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

func constToCoq(c *ssa.Const) string {
	switch c.Value.Kind() {
	case constant.Bool:
		if constant.BoolVal(c.Value) {
			return "true"
		} else {
			return "false"
		}
	case constant.Int:
		return c.Value.ExactString()
	case constant.Float:
		return c.Value.ExactString()
	case constant.Complex:
		return c.Value.ExactString()
	case constant.String:
		return c.Value.ExactString()
	case constant.Unknown:
		fallthrough
	default:
		return "unknown"
	}
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

	fmt.Print("(** ** Constants *)\n\n")
	for _, constantName := range constantNames {
		constant := members[constantName].(*ssa.NamedConst)
		fmt.Println("(*", constant.Type(), "*)")
		fmt.Println("Definition", constant.Name(), ":=", constToCoq(constant.Value), ".")
		fmt.Println()
	}

	fmt.Print("(** ** Globals *)\n\n")
	for _, globalName := range globalNames {
		global := members[globalName].(*ssa.Global)
		fmt.Println("Global:", global.Name(), global.Type())
		fmt.Println()
	}

	fmt.Print("(** ** Functions *)\n\n")
	for _, functionName := range functionNames {
		function := members[functionName].(*ssa.Function)
		fmt.Print(functionToCoq(function))
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
