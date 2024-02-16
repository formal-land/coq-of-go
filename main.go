package main

import (
	"bytes"
	"fmt"
	"go/constant"
	"go/types"
	"log"
	"os"
	"sort"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

const coqHeader = `Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.

Parameter float : Set.

Module Val.
  Inductive t : Set :=
  | bool : bool -> t
  | int : Z -> t
  | float : float -> t
  | complex : float -> float -> t
  | string : string -> t
  .
End Val.

Parameter M : Set -> Set.

Module M.
	Parameter global : GlobalName.t -> M Val.t.
End M.

`

// TODO: this function should be injective
func escapeName(name string) string {
	var buffer bytes.Buffer
	for _, c := range name {
		if c == '$' {
			buffer.WriteString("_dollar_")
		} else {
			buffer.WriteRune(c)
		}
	}
	return buffer.String()
}

func constToCoq(c *ssa.Const) string {
	switch c.Value.Kind() {
	case constant.Bool:
		if constant.BoolVal(c.Value) {
			return "Val.bool true"
		} else {
			return "Val.bool false"
		}
	case constant.Int:
		return fmt.Sprintf("Val.int %v", c.Value.ExactString())
	case constant.Float:
		return fmt.Sprintf("Val.float %v", c.Value.ExactString())
	case constant.Complex:
		return fmt.Sprintf("Val.complex %v", c.Value.ExactString())
	case constant.String:
		return fmt.Sprintf("Val.string %v", c.Value.ExactString())
	case constant.Unknown:
		fallthrough
	default:
		return "unknown"
	}
}

func namedConstToCoq(c *ssa.NamedConst) string {
	var buffer bytes.Buffer

	buffer.WriteString("Definition ")
	buffer.WriteString(c.Name())
	buffer.WriteString(" : Val.t :=\n")

	buffer.WriteString("  ")
	buffer.WriteString(constToCoq(c.Value))
	buffer.WriteString(".\n")

	return buffer.String()
}

func globalToCoq(global *ssa.Global) string {
	var buffer bytes.Buffer

	buffer.WriteString("Definition ")
	buffer.WriteString(escapeName(global.Name()))
	buffer.WriteString(" : M Val.t :=\n")

	buffer.WriteString("  ")
	buffer.WriteString("M.global GlobalName.")
	buffer.WriteString(escapeName(global.Name()))
	buffer.WriteString(".\n")

	return buffer.String()
}

func instructionToCoq(instr ssa.Instruction) string {
	var buffer bytes.Buffer

	if value, ok := instr.(ssa.Value); ok {
		buffer.WriteString(value.Name())
		buffer.WriteString(" := ")
	}

	switch instr := instr.(type) {
	case *ssa.Alloc:
		buffer.WriteString("Alloc")
		buffer.WriteString(" ")
		buffer.WriteString("(*")
		buffer.WriteString(instr.Comment)
		buffer.WriteString("*)")
		buffer.WriteString(" ")
		if instr.Heap {
			buffer.WriteString("Heap")
		} else {
			buffer.WriteString("Local")
		}
		buffer.WriteString(" ")
		buffer.WriteString(instr.Type().String())
	case *ssa.BinOp:
		buffer.WriteString("BinOp")
		buffer.WriteString(" ")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString("\"")
		buffer.WriteString(instr.Op.String())
		buffer.WriteString("\"")
		buffer.WriteString(" ")
		buffer.WriteString(instr.Y.Name())
		buffer.WriteString(")")
	case *ssa.Call:
		buffer.WriteString("Call")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Call.Value.Name())
		buffer.WriteString(" ")
		for i, arg := range instr.Call.Args {
			if i != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString(arg.Name())
		}
		buffer.WriteString(")")
	case *ssa.ChangeInterface:
		buffer.WriteString("ChangeInterface")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	case *ssa.ChangeType:
		buffer.WriteString("ChangeType")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	case *ssa.Convert:
		buffer.WriteString("Convert")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	case *ssa.Extract:
		buffer.WriteString("Extract")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Tuple.Name())
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Index))
		buffer.WriteString(")")
	case *ssa.Field:
		buffer.WriteString("Field")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Field))
		buffer.WriteString(")")
	case *ssa.FieldAddr:
		buffer.WriteString("FieldAddr")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Field))
		buffer.WriteString(")")
	case *ssa.Go:
		buffer.WriteString("Go")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Call.Value.Name())
		buffer.WriteString(" ")
		for i, arg := range instr.Call.Args {
			if i != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString(arg.Name())
		}
		buffer.WriteString(")")
	case *ssa.If:
		buffer.WriteString("If")
		buffer.WriteString(" ")
		buffer.WriteString(instr.Cond.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[0].String())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[1].String())
	case *ssa.Index:
		buffer.WriteString("Index")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Index.Name())
		buffer.WriteString(")")
	case *ssa.IndexAddr:
		buffer.WriteString("IndexAddr")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Index.Name())
		buffer.WriteString(")")
	case *ssa.Jump:
		buffer.WriteString("Jump")
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[0].String())
	case *ssa.Lookup:
		buffer.WriteString("Lookup")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Index.Name())
		buffer.WriteString(")")
	case *ssa.MakeChan:
		buffer.WriteString("MakeChan")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Size.Name())
		buffer.WriteString(")")
	case *ssa.MakeClosure:
		buffer.WriteString("MakeClosure")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Fn.Name())
		buffer.WriteString(" ")
		for i, freeVar := range instr.Bindings {
			if i != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString(freeVar.Name())
		}
		buffer.WriteString(")")
	case *ssa.MakeInterface:
		// INFO: Program.MethodValue(m): find the implementation of a method
		buffer.WriteString("MakeInterface")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		operands := instr.Operands(nil)
		for i_operand, operand := range operands {
			if i_operand != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString((*operand).Name())
		}
		buffer.WriteString(")")
	case *ssa.MakeMap:
		buffer.WriteString("MakeMap")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Reserve.Name())
		buffer.WriteString(")")
	case *ssa.MakeSlice:
		buffer.WriteString("MakeSlice")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Len.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Cap.Name())
		buffer.WriteString(")")
	case *ssa.MapUpdate:
		buffer.WriteString("MapUpdate")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Map.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Key.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Value.Name())
		buffer.WriteString(")")
	case *ssa.Next:
		buffer.WriteString("Next")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Iter.Name())
		buffer.WriteString(")")
	case *ssa.Panic:
		buffer.WriteString("Panic")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	case *ssa.Phi:
		buffer.WriteString("Phi")
		buffer.WriteString(" ")
		buffer.WriteString("(* ")
		buffer.WriteString(instr.Comment)
		buffer.WriteString(" *)")
		buffer.WriteString(" (")
		for i, edge := range instr.Edges {
			if i != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString(edge.Name())
		}
		buffer.WriteString(")")
	case *ssa.Range:
		buffer.WriteString("Range")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	case *ssa.Return:
		buffer.WriteString("Return")
		buffer.WriteString(" (")
		for i, result := range instr.Results {
			if i != 0 {
				buffer.WriteString(" ")
			}
			buffer.WriteString(result.Name())
		}
		buffer.WriteString(")")
	case *ssa.RunDefers:
		buffer.WriteString("RunDefers")
	case *ssa.Select:
		buffer.WriteString("Select")
		buffer.WriteString(" (")
		if instr.Blocking {
			buffer.WriteString("Blocking")
		} else {
			buffer.WriteString("NonBlocking")
		}
		buffer.WriteString(fmt.Sprintf("%b", instr.Blocking))
		for _, state := range instr.States {
			buffer.WriteString(state.Chan.Name())
			buffer.WriteString(" ")
			switch state.Dir {
			case types.RecvOnly:
				buffer.WriteString("RecvOnly")
			case types.SendOnly:
				buffer.WriteString("SendOnly")
			case types.SendRecv:
				buffer.WriteString("SendRecv")
			}
			buffer.WriteString(" ")
			buffer.WriteString(state.Send.Name())
		}
		buffer.WriteString(")")
	case *ssa.Slice:
		buffer.WriteString("Slice")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		if instr.Low != nil {
			buffer.WriteString(" ")
			buffer.WriteString(instr.Low.Name())
		}
		if instr.High != nil {
			buffer.WriteString(" ")
			buffer.WriteString(instr.High.Name())
		}
		buffer.WriteString(")")
	case *ssa.Store:
		buffer.WriteString("Store")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Addr.Name())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Val.Name())
		buffer.WriteString(")")
	case *ssa.TypeAssert:
		buffer.WriteString("TypeAssert")
		buffer.WriteString(" (")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(" ")
		if instr.CommaOk {
			buffer.WriteString("CommaOk")
		} else {
			buffer.WriteString("NoCommaOk")
		}
		buffer.WriteString(" ")
		buffer.WriteString(instr.AssertedType.String())
		buffer.WriteString(")")
	case *ssa.UnOp:
		buffer.WriteString("UnOp")
		buffer.WriteString(" (")
		buffer.WriteString(instr.Op.String())
		buffer.WriteString(" ")
		buffer.WriteString(instr.X.Name())
		buffer.WriteString(")")
	default:
		buffer.WriteString("Unknown: ")
		buffer.WriteString(instr.String())
	}

	return buffer.String()
}

func functionToCoq(f *ssa.Function) string {
	var buffer bytes.Buffer

	buffer.WriteString("Definition ")
	buffer.WriteString(f.Name())

	buffer.WriteString(" (")
	for i_param, param := range f.Params {
		if i_param != 0 {
			buffer.WriteString(" ")
		}
		buffer.WriteString(param.Name())
	}
	buffer.WriteString(" : Val.t)")

	buffer.WriteString(" : FunctionBody.t := [\n")
	for i_block, block := range f.Blocks {
		buffer.WriteString(fmt.Sprintf("  (%d, [\n", i_block))
		for i_instr, instr := range block.Instrs {
			buffer.WriteString("    ")
			buffer.WriteString(instructionToCoq(instr))
			if i_instr < len(block.Instrs)-1 {
				buffer.WriteString(";")
			}
			buffer.WriteString("\n")
		}
		buffer.WriteString("  ])")
		if i_block < len(f.Blocks)-1 {
			buffer.WriteString(";")
		}
		buffer.WriteString("\n")
	}
	buffer.WriteString("].\n")

	return buffer.String()
}

func main() {
	// Load, parse, and type-check the initial packages.
	cfg := &packages.Config{Mode: packages.LoadSyntax}
	initial, err := packages.Load(cfg,
		os.Args[1],
	)
	if err != nil {
		log.Fatal(err)
	}

	// Stop if any package had errors.
	// This step is optional; without it, the next step
	// will create SSA for only a subset of packages.
	if packages.PrintErrors(initial) > 0 {
		log.Fatalf("packages contain errors")
	}

	// Create SSA packages for all well-typed packages.
	prog, pkgs := ssautil.Packages(initial, 0)
	_ = prog

	// Build SSA code for the well-typed initial package.
	pkgs[0].Build()

	members := pkgs[0].Members
	functionNames := make([]string, 0)
	globalNames := make([]string, 0)
	namedConstNames := make([]string, 0)
	typeNames := make([]string, 0)

	for _, member := range members {
		switch member := member.(type) {
		case *ssa.Global:
			globalNames = append(globalNames, member.Name())
		case *ssa.Function:
			functionNames = append(functionNames, member.Name())
		case *ssa.NamedConst:
			namedConstNames = append(namedConstNames, member.Name())
		case *ssa.Type:
			typeNames = append(typeNames, member.Name())
		}
	}

	sort.Strings(namedConstNames)
	sort.Strings(functionNames)
	sort.Strings(globalNames)
	sort.Strings(typeNames)

	fmt.Print(coqHeader)

	fmt.Print("(** ** Constants *)\n\n")
	for _, constantName := range namedConstNames {
		constant := members[constantName].(*ssa.NamedConst)
		fmt.Println(namedConstToCoq(constant))
	}

	fmt.Print("(** ** Globals *)\n\n")

	// Create the inductive of global names
	fmt.Println("Module GlobalName.")
	fmt.Println("  Inductive t : Set :=")
	for _, globalName := range globalNames {
		fmt.Println("  |", escapeName(globalName), ": t")
	}
	fmt.Println("  .")
	fmt.Println("End GlobalName.")
	fmt.Println()

	for _, globalName := range globalNames {
		global := members[globalName].(*ssa.Global)
		fmt.Println(globalToCoq(global))
	}

	fmt.Print("(** ** Functions *)\n\n")
	for _, functionName := range functionNames {
		function := members[functionName].(*ssa.Function)
		fmt.Println(functionToCoq(function))
	}

	fmt.Print("(** ** Types *)\n\n")
	for _, typeName := range typeNames {
		fmt.Println("Parameter", typeName, ": Set.")
		fmt.Println()
	}
}
