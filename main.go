package main

import (
	"bytes"
	"fmt"
	"go/constant"
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

Module GoValue.
  Inductive t : Set :=
  | bool : bool -> t
  | int : Z -> t
  | float : float -> t
  | complex : float -> float -> t
  | string : string -> t
  .
End GoValue.
Definition GoValue : Set := GoValue.t.

Parameter M : Set -> Set.

Module M.
	Parameter global : GlobalName.t -> M GoValue.
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
			return "GoValue.bool true"
		} else {
			return "GoValue.bool false"
		}
	case constant.Int:
		return fmt.Sprintf("GoValue.int %v", c.Value.ExactString())
	case constant.Float:
		return fmt.Sprintf("GoValue.float %v", c.Value.ExactString())
	case constant.Complex:
		return fmt.Sprintf("GoValue.complex %v", c.Value.ExactString())
	case constant.String:
		return fmt.Sprintf("GoValue.string %v", c.Value.ExactString())
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
	buffer.WriteString(" : GoValue :=\n")

	buffer.WriteString("  ")
	buffer.WriteString(constToCoq(c.Value))
	buffer.WriteString(".\n")

	return buffer.String()
}

func globalToCoq(global *ssa.Global) string {
	var buffer bytes.Buffer

	buffer.WriteString("Definition ")
	buffer.WriteString(escapeName(global.Name()))
	buffer.WriteString(" : M GoValue :=\n")

	buffer.WriteString("  ")
	buffer.WriteString("M.global GlobalName.")
	buffer.WriteString(escapeName(global.Name()))
	buffer.WriteString(".\n")

	return buffer.String()
}

func functionToCoq(f *ssa.Function) string {
	var buffer bytes.Buffer

	buffer.WriteString("Definition ")
	buffer.WriteString(f.Name())
	for _, param := range f.Params {
		buffer.WriteString(" ")
		buffer.WriteString(param.Name())
	}
	buffer.WriteString(" : FunctionBody.t := [\n")
	for i_block, block := range f.Blocks {
		buffer.WriteString(fmt.Sprintf("  (%d, [\n", i_block))
		for i_instr, instr := range block.Instrs {
			buffer.WriteString("    ")
			if value, ok := instr.(ssa.Value); ok {
				buffer.WriteString(value.Name())
				buffer.WriteString(" := ")
			}
			buffer.WriteString(instr.String())
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
		// "internal/goarch",
		// ".",
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
	prog, pkgs := ssautil.Packages(initial,
		0,
		// ssa.PrintPackages,
	)
	_ = prog

	// Build SSA code for the well-typed initial package.
	pkgs[0].Build()

	// println("done")
	// var print_description = pkgs[0].Func("Println")
	// _ = print_description
	// println(pkgs[0].String())

	members := pkgs[0].Members
	constantNames := make([]string, 0)
	functionNames := make([]string, 0)
	globalNames := make([]string, 0)
	typeNames := make([]string, 0)
	for _, member := range members {
		switch member := member.(type) {
		case *ssa.Global:
			globalNames = append(globalNames, member.Name())
		case *ssa.Function:
			functionNames = append(functionNames, member.Name())
		case *ssa.NamedConst:
			constantNames = append(constantNames, member.Name())
		case *ssa.Type:
			typeNames = append(typeNames, member.Name())
		}
	}
	sort.Strings(constantNames)
	sort.Strings(functionNames)
	sort.Strings(globalNames)
	sort.Strings(typeNames)

	fmt.Print(coqHeader)

	fmt.Print("(** ** Constants *)\n\n")
	for _, constantName := range constantNames {
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
		fmt.Println("Type:", typeName)
		fmt.Println()
	}

	// for _, memberName := range memberNames {
	// 	switch member := pkgs[0].Members[memberName].(type) {
	// 	case *ssa.Global:
	// 		fmt.Println("Global:", member.Name(), member.Type())
	// 		fmt.Println()
	// 	case *ssa.Function:
	// 		fmt.Print(functionToCoq(member))
	// 		// fmt.Println("Function:", member.Name())
	// 		// for i, block := range member.Blocks {
	// 		// 	fmt.Println("Block:", i)
	// 		// 	for instr_index, instr := range block.Instrs {
	// 		// 		fmt.Println(instr_index, instr.String())
	// 		// 		// If the instruction is a bin op, print the operands
	// 		// 		if binop, ok := instr.(*ssa.BinOp); ok {
	// 		// 			fmt.Println(">>>>>>>>>> BinOp: <<<<<<<<<<<<<", binop.Op, binop.X, binop.Y)
	// 		// 		}
	// 		// 		if value, ok := instr.(ssa.Value); ok {
	// 		// 			fmt.Println(">>>>>>>>>> Value: <<<<<<<<<<<<<", value.Name(), value.String())
	// 		// 		}
	// 		// 		fmt.Println("====================================")
	// 		// 	}
	// 		// }
	// 		fmt.Println()
	// 	case *ssa.NamedConst:
	// 		fmt.Println("(*", member.Type(), "*)")
	// 		fmt.Println("Definition", member.Name(), ":=", constToCoq(member.Value), ".")
	// 		fmt.Println()
	// 	case *ssa.Type:
	// 		fmt.Println("Type:", member.Name())
	// 		fmt.Println()
	// 	}
	// }
}
