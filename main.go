package main

import (
	"bytes"
	"fmt"
	"go/constant"
	"go/types"
	"log"
	"math/big"
	"os"
	"sort"
	"strings"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

const coqHeader = `Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import List.ListNotations.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Parameter Rational : Set.

Module Lit.
  Inductive t : Set :=
  | Bool (_ : bool)
  | Int (_ : Z)
  | Float (_ : Rational)
  | Complex (_ _ : Rational)
  | String (_ : string)
  | Nil.
End Lit.

Module Val.
  Inductive t : Set :=
  | Lit (_ : Lit.t)
  | Tuple (_ : list t).
End Val.

Module M.
  CoInductive t (A : Set) : Set :=
  | Return (_ : A)
  | Bind {B : Set} (_ : t B) (_ : B -> t A)
  | Thunk (_ : t A)
  | EvalBody (_ : list (Z * t A)).
  Arguments Return {A}.
  Arguments Bind {A B}.
  Arguments Thunk {A}.
  Arguments EvalBody {A}.
End M.
Definition M : Set -> Set := M.t.

Module Register.
  Parameter read : string -> Val.t.

  Parameter write : string -> Val.t -> M unit.
End Register.

(* Notation "'let*' a := b 'in' c" :=
  (M.Bind b (fun a => c))
  (at level 200, b at level 100, a name). *)

Notation "'let*' a := b 'in' c" :=
  (M.Bind b (fun v_b => M.Bind (Register.write a v_b) (fun '_ => c)))
  (at level 200).

Notation "'do*' b 'in' c" :=
  (M.Bind b (fun '_ => c))
  (at level 200).

Module Function.
  Definition t : Set := list Val.t -> M (list Val.t).
End Function.

Module Alloc.
  Inductive t : Set :=
  | Heap
  | Local.
End Alloc.

Module CallKind.
  Inductive t : Set :=
  | Function (_ : M (list Val.t))
  | Method (_ : Val.t) (_ : string) (_ : list Val.t).
End CallKind.

Module TypeAssert.
  Inductive t : Set :=
  | CommaOk
  | NoCommaOk.
End TypeAssert.

Module Instr.
  Parameter Alloc : Alloc.t -> string -> M Val.t.

  Parameter BinOp : Val.t -> string -> Val.t -> M Val.t.

  Parameter Call : CallKind.t -> M Val.t.

  Parameter ChangeInterface : Val.t -> M Val.t.

  Parameter ChangeType : Val.t -> M Val.t.

  Parameter Convert : Val.t -> M Val.t.

  Parameter Extract : Val.t -> Z -> M Val.t.

	Parameter Field : Val.t -> Z -> M Val.t.

	Parameter FieldAddr : Val.t -> Z -> M Val.t.

  Parameter If : Val.t -> Z -> Z -> M (list Val.t).

  Parameter Index : Val.t -> Val.t -> M Val.t.

  Parameter IndexAddr : Val.t -> Val.t -> M Val.t.

  Parameter Jump : Z -> M (list Val.t).

  Parameter MakeInterface : Val.t -> M Val.t.

  Parameter MakeSlice : Val.t -> Val.t -> M Val.t.

	Parameter Panic : Val.t -> M (list Val.t).

  Parameter Phi : list Val.t -> M Val.t.

  Parameter Slice : Val.t -> option Val.t -> option Val.t -> M Val.t.

  Parameter Store : Val.t -> Val.t -> M Val.t.

  Parameter TypeAssert : Val.t -> TypeAssert.t -> string -> M Val.t.

	Parameter UnOp : string -> Val.t -> M Val.t.
End Instr.

Parameter TODO_method : Function.t.

(** ** Builtins *)

Parameter append : Function.t.

Parameter len : Function.t.

(** ** Go standard library *)

Module fmt.
  Parameter init : Function.t.

  Parameter Println : Function.t.

  Parameter Sprintf : Function.t.
End fmt.

Module go.
  Module token.
    Parameter init : Function.t.
  End token.
End go.

Module math.
  Parameter init : Function.t.

  Parameter Frexp : Function.t.

  Parameter IsInf : Function.t.

  Parameter IsNaN : Function.t.

  Module big.
    Parameter init : Function.t.

    Parameter NewInt : Function.t.

    Parameter NewRat : Function.t.
  End big.

  Module bits.
    Parameter init : Function.t.

    Parameter LeadingZeros64 : Function.t.
  End bits.
End math.

Module strconv.
  Parameter init : Function.t.

  Parameter ParseInt : Function.t.

  Parameter Unquote : Function.t.

  Parameter UnquoteChar : Function.t.
End strconv.

Module strings.
  Parameter init : Function.t.
End strings.

Module sync.
  Parameter init : Function.t.
End sync.

Module unicode.
  Module utf8.
    Parameter init : Function.t.
  End utf8.
End unicode.

Local Unset Guard Checking.
`

func escapeSpecialChars(name string) string {
	var buffer bytes.Buffer

	for _, c := range name {
		switch c {
		case '$':
			buffer.WriteString("_'dollar")
		case '\'':
			buffer.WriteString("_'prime_")
		default:
			buffer.WriteRune(c)
		}
	}

	return buffer.String()
}

func escapeName(name string) string {
	nameWithEscapedChars := escapeSpecialChars(name)

	reseredNames := []string{
		"and",
		"as",
		"else",
		"end",
		"exists",
		"fix",
		"forall",
		"fun",
		"if",
		"in",
		"let",
		"match",
		"Prop",
		"return",
		"Set",
		"then",
		"Type",
		"with",
	}

	for _, reservedName := range reseredNames {
		if nameWithEscapedChars == reservedName {
			return "_'" + nameWithEscapedChars
		}
	}

	return nameWithEscapedChars
}

func constToCoq(c *ssa.Const) string {
	if c.Value == nil {
		return "Val.Lit Lit.Nil"
	}

	switch value := constant.Val(c.Value).(type) {
	case bool:
		if value {
			return "Val.Lit (Lit.Bool true)"
		} else {
			return "Val.Lit (Lit.Bool false)"
		}
	case int64:
		var cString string
		if value < 0 {
			cString = fmt.Sprintf("(-%d)", -value)
		} else {
			cString = fmt.Sprintf("%d", value)
		}
		return "Val.Lit (Lit.Int " + cString + ")"
	case *big.Int:
		var cString string
		if value.Cmp(big.NewInt(0)) == -1 {
			cString = fmt.Sprintf("(-%d)", new(big.Int).Neg(value))
		} else {
			cString = fmt.Sprintf("%d", value)
		}
		return "Val.Lit (Lit.Int " + cString + ")"
	case *big.Float:
		return "Val.Lit (Lit.Float " + value.String() + ")"
	case *big.Rat:
		return "Val.Lit (Lit.Float " + value.String() + ")"
	case string:
		return "Val.Lit (Lit.String \"" + value + "\")"
	default:
		return "TODO-unknown-constant"
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
	buffer.WriteString("global GlobalName.")
	buffer.WriteString(escapeName(global.Name()))
	buffer.WriteString(".\n")

	return buffer.String()
}

// The name of a function, fully qualified with its package path.
func functionNameToCoq(packageToTranslate string, function *ssa.Function) string {
	// TODO: Handle the case where the function is a method.
	if function.Signature.Recv() != nil {
		return "TODO_method"
	}

	// Split the function name into its package path and the function name.
	pathAndName := strings.Split(function.String(), ".")
	path := pathAndName[0]
	name := escapeName(pathAndName[1])

	if path == packageToTranslate {
		return name
	}

	pathParts := strings.Split(path, "/")

	for pathPart := range pathParts {
		pathParts[pathPart] = escapeName(pathParts[pathPart])
	}

	return strings.Join(pathParts, ".") + "." + name
}

func valueToCoq(packageToTranslate string, value ssa.Value) string {
	// fmt.Println("-= String =-")
	// fmt.Println(value.String())
	// fmt.Println("-= Name =-")
	// fmt.Println(value.Name())
	// fmt.Println("-= TypeOf =-")
	// fmt.Println(reflect.TypeOf(value))
	// fmt.Println()

	switch value := value.(type) {
	case *ssa.Const:
		return "(" + constToCoq(value) + ")"
	case *ssa.Function:
		return functionNameToCoq(packageToTranslate, value)
	case *ssa.Builtin, *ssa.Parameter:
		return escapeName(value.Name())
	default:
		return "(Register.read \"" + value.Name() + "\")"
	}
}

func instructionToCoq(
	packageToTranslate string,
	isLast bool,
	instr ssa.Instruction,
) string {
	var buffer bytes.Buffer

	if !isLast {
		if value, ok := instr.(ssa.Value); ok {
			buffer.WriteString("let* ")
			buffer.WriteString("\"" + value.Name() + "\"")
			buffer.WriteString(" := ")
		} else {
			buffer.WriteString("do* ")
		}
	}

	switch instr := instr.(type) {
	case *ssa.Alloc:
		buffer.WriteString("Instr.Alloc")
		buffer.WriteString(" ")
		buffer.WriteString("(* ")
		buffer.WriteString(instr.Comment)
		buffer.WriteString(" *)")
		buffer.WriteString(" ")
		if instr.Heap {
			buffer.WriteString("Alloc.Heap")
		} else {
			buffer.WriteString("Alloc.Local")
		}
		buffer.WriteString(" ")
		buffer.WriteString("\"" + instr.Type().String() + "\"")
	case *ssa.BinOp:
		buffer.WriteString("Instr.BinOp")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString("\"")
		buffer.WriteString(instr.Op.String())
		buffer.WriteString("\"")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Y))
	case *ssa.Call:
		buffer.WriteString("Instr.Call")
		buffer.WriteString(" (")
		if instr.Call.Method != nil {
			buffer.WriteString("CallKind.Method")
			buffer.WriteString(" ")
			buffer.WriteString(valueToCoq(packageToTranslate, instr.Call.Value))
			buffer.WriteString(" ")
			buffer.WriteString("\"" + escapeName(instr.Call.Method.Name()) + "\"")
		} else {
			buffer.WriteString("CallKind.Function")
			buffer.WriteString(" (")
			buffer.WriteString(valueToCoq(packageToTranslate, instr.Call.Value))
		}
		buffer.WriteString(" [")
		for i, arg := range instr.Call.Args {
			if i != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString(valueToCoq(packageToTranslate, arg))
		}
		buffer.WriteString("])")
		if instr.Call.Method == nil {
			buffer.WriteString(")")
		}
	case *ssa.ChangeInterface:
		buffer.WriteString("Instr.ChangeInterface")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.ChangeType:
		buffer.WriteString("Instr.ChangeType")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.Convert:
		buffer.WriteString("Instr.Convert")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.Extract:
		buffer.WriteString("Instr.Extract")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Tuple))
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Index))
	case *ssa.Field:
		buffer.WriteString("Instr.Field")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Field))
	case *ssa.FieldAddr:
		buffer.WriteString("Instr.FieldAddr")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString(fmt.Sprintf("%d", instr.Field))
	case *ssa.Go:
		buffer.WriteString("Instr.Go")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Call.Value))
		buffer.WriteString(" [")
		for i, arg := range instr.Call.Args {
			if i != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString(valueToCoq(packageToTranslate, arg))
		}
		buffer.WriteString("]")
	case *ssa.If:
		buffer.WriteString("Instr.If")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Cond))
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[0].String())
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[1].String())
	case *ssa.Index:
		buffer.WriteString("Instr.Index")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Index))
	case *ssa.IndexAddr:
		buffer.WriteString("Instr.IndexAddr")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Index))
	case *ssa.Jump:
		buffer.WriteString("Instr.Jump")
		buffer.WriteString(" ")
		buffer.WriteString(instr.Block().Succs[0].String())
	case *ssa.Lookup:
		buffer.WriteString("Instr.Lookup")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Index))
	case *ssa.MakeChan:
		buffer.WriteString("Instr.MakeChan")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Size))
	case *ssa.MakeClosure:
		buffer.WriteString("Instr.MakeClosure")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Fn))
		buffer.WriteString(" [")
		for i, freeVar := range instr.Bindings {
			if i != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString(valueToCoq(packageToTranslate, freeVar))
		}
		buffer.WriteString("]")
	case *ssa.MakeInterface:
		// INFO: Program.MethodValue(m): find the implementation of a method
		buffer.WriteString("Instr.MakeInterface")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.MakeMap:
		buffer.WriteString("Instr.MakeMap")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Reserve))
	case *ssa.MakeSlice:
		buffer.WriteString("Instr.MakeSlice")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Len))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Cap))
	case *ssa.MapUpdate:
		buffer.WriteString("Instr.MapUpdate")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Map))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Key))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Value))
	case *ssa.Next:
		buffer.WriteString("Instr.Next")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Iter))
	case *ssa.Panic:
		buffer.WriteString("Instr.Panic")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.Phi:
		buffer.WriteString("Instr.Phi")
		buffer.WriteString(" ")
		buffer.WriteString("(* ")
		buffer.WriteString(instr.Comment)
		buffer.WriteString(" *) [")
		for i, edge := range instr.Edges {
			if i != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString(valueToCoq(packageToTranslate, edge))
		}
		buffer.WriteString("]")
	case *ssa.Range:
		buffer.WriteString("Instr.Range")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	case *ssa.Return:
		buffer.WriteString("M.Return")
		buffer.WriteString(" [")
		for i, result := range instr.Results {
			if i != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString(valueToCoq(packageToTranslate, result))
		}
		buffer.WriteString("]")
	case *ssa.RunDefers:
		buffer.WriteString("Instr.RunDefers")
	case *ssa.Select:
		buffer.WriteString("Instr.Select")
		buffer.WriteString(" ")
		if instr.Blocking {
			buffer.WriteString("Blocking")
		} else {
			buffer.WriteString("NonBlocking")
		}
		buffer.WriteString(" [")
		for i_state, state := range instr.States {
			if i_state != 0 {
				buffer.WriteString("; ")
			}
			buffer.WriteString("(")
			buffer.WriteString(valueToCoq(packageToTranslate, state.Chan))
			buffer.WriteString(", ")
			switch state.Dir {
			case types.RecvOnly:
				buffer.WriteString("ChannelDir.RecvOnly")
			case types.SendOnly:
				buffer.WriteString("ChannelDir.SendOnly")
			case types.SendRecv:
				buffer.WriteString("ChannelDir.SendRecv")
			}
			buffer.WriteString(", ")
			buffer.WriteString(valueToCoq(packageToTranslate, state.Send))
			buffer.WriteString(")")
		}
		buffer.WriteString("]")
	case *ssa.Slice:
		buffer.WriteString("Instr.Slice")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		if instr.Low != nil {
			buffer.WriteString("(Some ")
			buffer.WriteString(valueToCoq(packageToTranslate, instr.Low))
			buffer.WriteString(")")
		} else {
			buffer.WriteString("None")
		}
		buffer.WriteString(" ")
		if instr.High != nil {
			buffer.WriteString("(Some ")
			buffer.WriteString(valueToCoq(packageToTranslate, instr.High))
			buffer.WriteString(")")
		} else {
			buffer.WriteString("None")
		}
	case *ssa.Store:
		buffer.WriteString("Instr.Store")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Addr))
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.Val))
	case *ssa.TypeAssert:
		buffer.WriteString("Instr.TypeAssert")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
		buffer.WriteString(" ")
		if instr.CommaOk {
			buffer.WriteString("TypeAssert.CommaOk")
		} else {
			buffer.WriteString("TypeAssert.NoCommaOk")
		}
		buffer.WriteString(" ")
		buffer.WriteString("\"")
		buffer.WriteString(instr.AssertedType.String())
		buffer.WriteString("\"")
	case *ssa.UnOp:
		buffer.WriteString("Instr.UnOp")
		buffer.WriteString(" ")
		buffer.WriteString("\"")
		buffer.WriteString(instr.Op.String())
		buffer.WriteString("\"")
		buffer.WriteString(" ")
		buffer.WriteString(valueToCoq(packageToTranslate, instr.X))
	default:
		buffer.WriteString("Unknown: ")
		buffer.WriteString(instr.String())
	}

	if !isLast {
		buffer.WriteString(" in")
	}

	return buffer.String()
}

func functionToCoq(
	packageToTranslate string,
	isFirst bool,
	isLast bool,
	f *ssa.Function,
) string {
	var buffer bytes.Buffer

	if isFirst {
		buffer.WriteString("CoFixpoint ")
	} else {
		buffer.WriteString("with ")
	}
	buffer.WriteString(escapeName(f.Name()))
	buffer.WriteString(" (α : list Val.t) : M (list Val.t) :=\n")

	buffer.WriteString("  M.Thunk (\n")
	buffer.WriteString("  match α with\n")
	buffer.WriteString("  | [")
	for i_param, param := range f.Params {
		if i_param != 0 {
			buffer.WriteString("; ")
		}
		buffer.WriteString(escapeName(param.Name()))
	}
	buffer.WriteString("] =>\n")

	for i_block, block := range f.Blocks {
		buffer.WriteString("    ")
		if i_block == 0 {
			buffer.WriteString("M.Thunk (M.EvalBody [")
		}
		buffer.WriteString(fmt.Sprintf("(%d,\n", i_block))
		for i_instr, instr := range block.Instrs {
			buffer.WriteString("      ")
			buffer.WriteString(instructionToCoq(packageToTranslate, i_instr == len(block.Instrs)-1, instr))
			buffer.WriteString("\n")
		}
		buffer.WriteString("    )")
		if i_block == len(f.Blocks)-1 {
			buffer.WriteString("])")
		} else {
			buffer.WriteString(";")
		}
		buffer.WriteString("\n")
	}
	buffer.WriteString("  | _ => M.Thunk (M.EvalBody [])\n")
	buffer.WriteString("  end)")

	if isLast {
		buffer.WriteString(".")
	}

	buffer.WriteString("\n")

	return buffer.String()
}

func main() {
	packageToTranslate := os.Args[1]

	// Load, parse, and type-check the input package.
	cfg := &packages.Config{Mode: packages.LoadSyntax}
	initial, err := packages.Load(cfg, packageToTranslate)
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
	_, pkgs := ssautil.Packages(initial, 0)

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
	fmt.Println("Parameter global : GlobalName.t -> M Val.t.")
	fmt.Println()

	for _, globalName := range globalNames {
		global := members[globalName].(*ssa.Global)
		fmt.Println(globalToCoq(global))
	}

	fmt.Print("(** ** Functions *)\n\n")
	for i, functionName := range functionNames {
		function := members[functionName].(*ssa.Function)
		fmt.Println(functionToCoq(
			packageToTranslate,
			i == 0,
			i == len(functionNames)-1,
			function,
		))
	}

	fmt.Print("(** ** Types *)\n\n")
	for _, typeName := range typeNames {
		fmt.Println("Parameter", typeName, ": Set.")
		fmt.Println()
	}
}
