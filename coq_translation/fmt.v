Require Import Coq.ZArith.ZArith.
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
(** ** Constants *)

Definition badIndexString : Val.t :=
  Val.Lit (Lit.String "(BADINDEX)").

Definition badPrecString : Val.t :=
  Val.Lit (Lit.String "%!(BADPREC)").

Definition badWidthString : Val.t :=
  Val.Lit (Lit.String "%!(BADWIDTH)").

Definition binaryDigits : Val.t :=
  Val.Lit (Lit.String "01").

Definition commaSpaceString : Val.t :=
  Val.Lit (Lit.String ", ").

Definition decimalDigits : Val.t :=
  Val.Lit (Lit.String "0123456789").

Definition eof : Val.t :=
  Val.Lit (Lit.Int (-1)).

Definition exponent : Val.t :=
  Val.Lit (Lit.String "eEpP").

Definition extraString : Val.t :=
  Val.Lit (Lit.String "%!(EXTRA ").

Definition floatVerbs : Val.t :=
  Val.Lit (Lit.String "beEfFgGv").

Definition hexadecimalDigits : Val.t :=
  Val.Lit (Lit.String "0123456789aAbBcCdDeEfF").

Definition hugeWid : Val.t :=
  Val.Lit (Lit.Int 1073741824).

Definition intBits : Val.t :=
  Val.Lit (Lit.Int 64).

Definition invReflectString : Val.t :=
  Val.Lit (Lit.String "<invalid reflect.Value>").

Definition ldigits : Val.t :=
  Val.Lit (Lit.String "0123456789abcdefx").

Definition mapString : Val.t :=
  Val.Lit (Lit.String "map[").

Definition missingString : Val.t :=
  Val.Lit (Lit.String "(MISSING)").

Definition nilAngleString : Val.t :=
  Val.Lit (Lit.String "<nil>").

Definition nilParenString : Val.t :=
  Val.Lit (Lit.String "(nil)").

Definition nilString : Val.t :=
  Val.Lit (Lit.String "nil").

Definition noVerbString : Val.t :=
  Val.Lit (Lit.String "%!(NOVERB)").

Definition octalDigits : Val.t :=
  Val.Lit (Lit.String "01234567").

Definition panicString : Val.t :=
  Val.Lit (Lit.String "(PANIC=").

Definition percentBangString : Val.t :=
  Val.Lit (Lit.String "%!").

Definition period : Val.t :=
  Val.Lit (Lit.String ".").

Definition sign : Val.t :=
  Val.Lit (Lit.String "+-").

Definition signed : Val.t :=
  Val.Lit (Lit.Bool true).

Definition udigits : Val.t :=
  Val.Lit (Lit.String "0123456789ABCDEFX").

Definition uintptrBits : Val.t :=
  Val.Lit (Lit.Int 64).

Definition unsigned : Val.t :=
  Val.Lit (Lit.Bool false).

(** ** Globals *)

Module GlobalName.
  Inductive t : Set :=
  | errBool : t
  | errComplex : t
  | init_'dollarguard : t
  | ppFree : t
  | space : t
  | ssFree : t
  .
End GlobalName.

Parameter global : GlobalName.t -> M Val.t.

Definition errBool : M Val.t :=
  global GlobalName.errBool.

Definition errComplex : M Val.t :=
  global GlobalName.errComplex.

Definition init_'dollarguard : M Val.t :=
  global GlobalName.init_'dollarguard.

Definition ppFree : M Val.t :=
  global GlobalName.ppFree.

Definition space : M Val.t :=
  global GlobalName.space.

Definition ssFree : M Val.t :=
  global GlobalName.ssFree.

(** ** Functions *)

CoFixpoint Append (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [b; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (append [b; (Register.read "t4")])) in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Appendf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [b; format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); format; a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (append [b; (Register.read "t4")])) in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Appendln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [b; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (append [b; (Register.read "t4")])) in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Errorf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.FieldAddr (Register.read "t0") 8 in
      do* Instr.Store (Register.read "t1") (Val.Lit (Lit.Bool true)) in
      let* "t2" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); format; a])) in
      let* "t3" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t4" := Instr.UnOp "*" (Register.read "t3") in
      let* "t5" := Instr.Convert (Register.read "t4") in
      let* "t6" := Instr.FieldAddr (Register.read "t0") 9 in
      let* "t7" := Instr.UnOp "*" (Register.read "t6") in
      let* "t8" := Instr.Call (CallKind.Function (len [(Register.read "t7")])) in
      let* "t9" := Instr.BinOp (Register.read "t8") "==" (Val.Lit (Lit.Int 0)) in
      Instr.If (Register.read "t9") 2 4
    );
    (1,
      let* "t10" := Instr.Phi (* err *) [(Register.read "t12"); (Register.read "t25"); (Register.read "t45")] in
      let* "t11" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t10")]
    );
    (2,
      let* "t12" := Instr.Call (CallKind.Function (errors.New [(Register.read "t5")])) in
      Instr.Jump 1
    );
    (3,
      let* "t13" := Instr.Alloc (* complit *) Alloc.Heap "*fmt.wrapError" in
      let* "t14" := Instr.FieldAddr (Register.read "t13") 0 in
      do* Instr.Store (Register.read "t14") (Register.read "t5") in
      let* "t15" := Instr.FieldAddr (Register.read "t0") 9 in
      let* "t16" := Instr.UnOp "*" (Register.read "t15") in
      let* "t17" := Instr.IndexAddr (Register.read "t16") (Val.Lit (Lit.Int 0)) in
      let* "t18" := Instr.UnOp "*" (Register.read "t17") in
      let* "t19" := Instr.IndexAddr a (Register.read "t18") in
      let* "t20" := Instr.UnOp "*" (Register.read "t19") in
      let* "t21" := Instr.TypeAssert (Register.read "t20") TypeAssert.CommaOk "error" in
      let* "t22" := Instr.Extract (Register.read "t21") 0 in
      let* "t23" := Instr.FieldAddr (Register.read "t13") 1 in
      do* Instr.Store (Register.read "t23") (Register.read "t22") in
      let* "t24" := Instr.Extract (Register.read "t21") 1 in
      let* "t25" := Instr.MakeInterface (Register.read "t13") in
      Instr.Jump 1
    );
    (4,
      let* "t26" := Instr.BinOp (Register.read "t8") "==" (Val.Lit (Lit.Int 1)) in
      Instr.If (Register.read "t26") 3 5
    );
    (5,
      let* "t27" := Instr.FieldAddr (Register.read "t0") 4 in
      let* "t28" := Instr.UnOp "*" (Register.read "t27") in
      Instr.If (Register.read "t28") 6 7
    );
    (6,
      let* "t29" := Instr.FieldAddr (Register.read "t0") 9 in
      let* "t30" := Instr.UnOp "*" (Register.read "t29") in
      let* "t31" := Instr.Call (CallKind.Function (sort.Ints [(Register.read "t30")])) in
      Instr.Jump 7
    );
    (7,
      let* "t32" := Instr.FieldAddr (Register.read "t0") 9 in
      let* "t33" := Instr.UnOp "*" (Register.read "t32") in
      let* "t34" := Instr.Call (CallKind.Function (len [(Register.read "t33")])) in
      Instr.Jump 8
    );
    (8,
      let* "t35" := Instr.Phi (* errs *) [(Val.Lit Lit.Nil); (Register.read "t35"); (Register.read "t35"); (Register.read "t60")] in
      let* "t36" := Instr.Phi (* rangeindex *) [(Val.Lit (Lit.Int (-1))); (Register.read "t37"); (Register.read "t37"); (Register.read "t37")] in
      let* "t37" := Instr.BinOp (Register.read "t36") "+" (Val.Lit (Lit.Int 1)) in
      let* "t38" := Instr.BinOp (Register.read "t37") "<" (Register.read "t34") in
      Instr.If (Register.read "t38") 9 10
    );
    (9,
      let* "t39" := Instr.IndexAddr (Register.read "t33") (Register.read "t37") in
      let* "t40" := Instr.UnOp "*" (Register.read "t39") in
      let* "t41" := Instr.BinOp (Register.read "t37") ">" (Val.Lit (Lit.Int 0)) in
      Instr.If (Register.read "t41") 12 11
    );
    (10,
      let* "t42" := Instr.Alloc (* complit *) Alloc.Heap "*fmt.wrapErrors" in
      let* "t43" := Instr.FieldAddr (Register.read "t42") 0 in
      let* "t44" := Instr.FieldAddr (Register.read "t42") 1 in
      do* Instr.Store (Register.read "t43") (Register.read "t5") in
      do* Instr.Store (Register.read "t44") (Register.read "t35") in
      let* "t45" := Instr.MakeInterface (Register.read "t42") in
      Instr.Jump 1
    );
    (11,
      let* "t46" := Instr.IndexAddr a (Register.read "t40") in
      let* "t47" := Instr.UnOp "*" (Register.read "t46") in
      let* "t48" := Instr.TypeAssert (Register.read "t47") TypeAssert.CommaOk "error" in
      let* "t49" := Instr.Extract (Register.read "t48") 0 in
      let* "t50" := Instr.Extract (Register.read "t48") 1 in
      Instr.If (Register.read "t50") 13 8
    );
    (12,
      let* "t51" := Instr.FieldAddr (Register.read "t0") 9 in
      let* "t52" := Instr.UnOp "*" (Register.read "t51") in
      let* "t53" := Instr.BinOp (Register.read "t37") "-" (Val.Lit (Lit.Int 1)) in
      let* "t54" := Instr.IndexAddr (Register.read "t52") (Register.read "t53") in
      let* "t55" := Instr.UnOp "*" (Register.read "t54") in
      let* "t56" := Instr.BinOp (Register.read "t55") "==" (Register.read "t40") in
      Instr.If (Register.read "t56") 8 11
    );
    (13,
      let* "t57" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]error" in
      let* "t58" := Instr.IndexAddr (Register.read "t57") (Val.Lit (Lit.Int 0)) in
      do* Instr.Store (Register.read "t58") (Register.read "t49") in
      let* "t59" := Instr.Slice (Register.read "t57") None None in
      let* "t60" := Instr.Call (CallKind.Function (append [(Register.read "t35"); (Register.read "t59")])) in
      Instr.Jump 8
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with FormatString (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [state; verb] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Alloc (* tmp *) Alloc.Heap "*[16]byte" in
      let* "t1" := Instr.Slice (Register.read "t0") None (Some (Val.Lit (Lit.Int 0))) in
      let* "t2" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]byte" in
      let* "t3" := Instr.IndexAddr (Register.read "t2") (Val.Lit (Lit.Int 0)) in
      do* Instr.Store (Register.read "t3") (Val.Lit (Lit.Int 37)) in
      let* "t4" := Instr.Slice (Register.read "t2") None None in
      let* "t5" := Instr.Call (CallKind.Function (append [(Register.read "t1"); (Register.read "t4")])) in
      let* "t6" := Instr.Range (Val.Lit (Lit.String " +-#0")) in
      Instr.Jump 1
    );
    (1,
      let* "t7" := Instr.Phi (* b *) [(Register.read "t5"); (Register.read "t7"); (Register.read "t20")] in
      let* "t8" := Instr.Next (Register.read "t6") in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      Instr.If (Register.read "t9") 2 3
    );
    (2,
      let* "t10" := Instr.Extract (Register.read "t8") 2 in
      let* "t11" := Instr.Convert (Register.read "t10") in
      let* "t12" := Instr.Call (CallKind.Method state "Flag" [(Register.read "t11")]) in
      Instr.If (Register.read "t12") 4 1
    );
    (3,
      let* "t13" := Instr.Call (CallKind.Method state "Width" []) in
      let* "t14" := Instr.Extract (Register.read "t13") 0 in
      let* "t15" := Instr.Extract (Register.read "t13") 1 in
      Instr.If (Register.read "t15") 5 6
    );
    (4,
      let* "t16" := Instr.Convert (Register.read "t10") in
      let* "t17" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]byte" in
      let* "t18" := Instr.IndexAddr (Register.read "t17") (Val.Lit (Lit.Int 0)) in
      do* Instr.Store (Register.read "t18") (Register.read "t16") in
      let* "t19" := Instr.Slice (Register.read "t17") None None in
      let* "t20" := Instr.Call (CallKind.Function (append [(Register.read "t7"); (Register.read "t19")])) in
      Instr.Jump 1
    );
    (5,
      let* "t21" := Instr.Convert (Register.read "t14") in
      let* "t22" := Instr.Call (CallKind.Function (strconv.AppendInt [(Register.read "t7"); (Register.read "t21"); (Val.Lit (Lit.Int 10))])) in
      Instr.Jump 6
    );
    (6,
      let* "t23" := Instr.Phi (* b *) [(Register.read "t7"); (Register.read "t22")] in
      let* "t24" := Instr.Call (CallKind.Method state "Precision" []) in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      Instr.If (Register.read "t26") 7 8
    );
    (7,
      let* "t27" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]byte" in
      let* "t28" := Instr.IndexAddr (Register.read "t27") (Val.Lit (Lit.Int 0)) in
      do* Instr.Store (Register.read "t28") (Val.Lit (Lit.Int 46)) in
      let* "t29" := Instr.Slice (Register.read "t27") None None in
      let* "t30" := Instr.Call (CallKind.Function (append [(Register.read "t23"); (Register.read "t29")])) in
      let* "t31" := Instr.Convert (Register.read "t25") in
      let* "t32" := Instr.Call (CallKind.Function (strconv.AppendInt [(Register.read "t30"); (Register.read "t31"); (Val.Lit (Lit.Int 10))])) in
      Instr.Jump 8
    );
    (8,
      let* "t33" := Instr.Phi (* b *) [(Register.read "t23"); (Register.read "t32")] in
      let* "t34" := Instr.Call (CallKind.Function (unicode.utf8.AppendRune [(Register.read "t33"); verb])) in
      let* "t35" := Instr.Convert (Register.read "t34") in
      M.Return [(Register.read "t35")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fprint (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [w; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Method w "Write" [(Register.read "t4")]) in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      let* "t8" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t6"); (Register.read "t7")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fprintf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [w; format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); format; a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Method w "Write" [(Register.read "t4")]) in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      let* "t8" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t6"); (Register.read "t7")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fprintln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [w; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.ChangeType (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Method w "Write" [(Register.read "t4")]) in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      let* "t8" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t6"); (Register.read "t7")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fscan (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newScanState [r; (Val.Lit (Lit.Bool true)); (Val.Lit (Lit.Bool false))])) in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      let* "t3" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); (Register.read "t2")])) in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fscanf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r; format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newScanState [r; (Val.Lit (Lit.Bool false)); (Val.Lit (Lit.Bool false))])) in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      let* "t3" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); format; a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); (Register.read "t2")])) in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Fscanln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newScanState [r; (Val.Lit (Lit.Bool false)); (Val.Lit (Lit.Bool true))])) in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      let* "t3" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      let* "t6" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t1"); (Register.read "t2")])) in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Print (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdout") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fprint [(Register.read "t1"); a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Printf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdout") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fprintf [(Register.read "t1"); format; a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Println (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdout") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fprintln [(Register.read "t1"); a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Scan (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdin") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fscan [(Register.read "t1"); a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Scanf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdin") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fscanf [(Register.read "t1"); format; a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Scanln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "Stdin") in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      let* "t2" := Instr.Call (CallKind.Function (Fscanln [(Register.read "t1"); a])) in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sprint (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.Convert (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sprintf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); format; a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.Convert (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sprintln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (newPrinter [])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0"); a])) in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.Convert (Register.read "t3") in
      let* "t5" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      M.Return [(Register.read "t4")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sscan (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [str; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Alloc (* str *) Alloc.Heap "*string" in
      do* Instr.Store (Register.read "t0") str in
      let* "t1" := Instr.ChangeType (Register.read "t0") in
      let* "t2" := Instr.MakeInterface (Register.read "t1") in
      let* "t3" := Instr.Call (CallKind.Function (Fscan [(Register.read "t2"); a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sscanf (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [str; format; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Alloc (* str *) Alloc.Heap "*string" in
      do* Instr.Store (Register.read "t0") str in
      let* "t1" := Instr.ChangeType (Register.read "t0") in
      let* "t2" := Instr.MakeInterface (Register.read "t1") in
      let* "t3" := Instr.Call (CallKind.Function (Fscanf [(Register.read "t2"); format; a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with Sscanln (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [str; a] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Alloc (* str *) Alloc.Heap "*string" in
      do* Instr.Store (Register.read "t0") str in
      let* "t1" := Instr.ChangeType (Register.read "t0") in
      let* "t2" := Instr.MakeInterface (Register.read "t1") in
      let* "t3" := Instr.Call (CallKind.Function (Fscanln [(Register.read "t2"); a])) in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      M.Return [(Register.read "t4"); (Register.read "t5")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with errorHandler (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [errp] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (recover [])) in
      let* "t1" := Instr.BinOp (Register.read "t0") "!=" (Val.Lit Lit.Nil) in
      Instr.If (Register.read "t1") 1 2
    );
    (1,
      let* "t2" := Instr.Alloc (* se *) Alloc.Local "*fmt.scanError" in
      let* "t3" := Instr.TypeAssert (Register.read "t0") TypeAssert.CommaOk "fmt.scanError" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      do* Instr.Store (Register.read "t2") (Register.read "t4") in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 3 4
    );
    (2,
      M.Return []
    );
    (3,
      let* "t6" := Instr.FieldAddr (Register.read "t2") 0 in
      let* "t7" := Instr.UnOp "*" (Register.read "t6") in
      do* Instr.Store errp (Register.read "t7") in
      Instr.Jump 2
    );
    (4,
      let* "t8" := Instr.TypeAssert (Register.read "t0") TypeAssert.CommaOk "error" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 7 6
    );
    (5,
      do* Instr.Store errp (Register.read "t9") in
      Instr.Jump 2
    );
    (6,
      Instr.Panic (Register.read "t0")
    );
    (7,
      let* "t11" := Instr.UnOp "*" (Register.read "EOF") in
      let* "t12" := Instr.BinOp (Register.read "t9") "==" (Register.read "t11") in
      Instr.If (Register.read "t12") 5 6
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with getField (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [v; i] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (TODO_method [v; i])) in
      let* "t1" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      let* "t2" := Instr.BinOp (Register.read "t1") "==" (Val.Lit (Lit.Int 20)) in
      Instr.If (Register.read "t2") 3 2
    );
    (1,
      let* "t3" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      Instr.Jump 2
    );
    (2,
      let* "t4" := Instr.Phi (* val *) [(Register.read "t0"); (Register.read "t0"); (Register.read "t3")] in
      M.Return [(Register.read "t4")]
    );
    (3,
      let* "t5" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t0")])) in
      Instr.If (Register.read "t5") 2 1
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with hasX (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [s] =>
    M.Thunk (M.EvalBody [(0,
      Instr.Jump 3
    );
    (1,
      let* "t0" := Instr.Index s (Register.read "t2") in
      let* "t1" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 120)) in
      Instr.If (Register.read "t1") 4 6
    );
    (2,
      M.Return [(Val.Lit (Lit.Bool false))]
    );
    (3,
      let* "t2" := Instr.Phi (* i *) [(Val.Lit (Lit.Int 0)); (Register.read "t5")] in
      let* "t3" := Instr.Call (CallKind.Function (len [s])) in
      let* "t4" := Instr.BinOp (Register.read "t2") "<" (Register.read "t3") in
      Instr.If (Register.read "t4") 1 2
    );
    (4,
      M.Return [(Val.Lit (Lit.Bool true))]
    );
    (5,
      let* "t5" := Instr.BinOp (Register.read "t2") "+" (Val.Lit (Lit.Int 1)) in
      Instr.Jump 3
    );
    (6,
      let* "t6" := Instr.Index s (Register.read "t2") in
      let* "t7" := Instr.BinOp (Register.read "t6") "==" (Val.Lit (Lit.Int 88)) in
      Instr.If (Register.read "t7") 4 5
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with hexDigit (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [d] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Convert d in
      let* "t1" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 48)) in
      Instr.If (Register.read "t1") 1 3
    );
    (1,
      let* "t2" := Instr.BinOp (Register.read "t0") "-" (Val.Lit (Lit.Int 48)) in
      M.Return [(Register.read "t2"); (Val.Lit (Lit.Bool true))]
    );
    (2,
      let* "t3" := Instr.BinOp (Val.Lit (Lit.Int 10)) "+" (Register.read "t0") in
      let* "t4" := Instr.BinOp (Register.read "t3") "-" (Val.Lit (Lit.Int 97)) in
      M.Return [(Register.read "t4"); (Val.Lit (Lit.Bool true))]
    );
    (3,
      let* "t5" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 49)) in
      Instr.If (Register.read "t5") 1 4
    );
    (4,
      let* "t6" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 50)) in
      Instr.If (Register.read "t6") 1 5
    );
    (5,
      let* "t7" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 51)) in
      Instr.If (Register.read "t7") 1 6
    );
    (6,
      let* "t8" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 52)) in
      Instr.If (Register.read "t8") 1 7
    );
    (7,
      let* "t9" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 53)) in
      Instr.If (Register.read "t9") 1 8
    );
    (8,
      let* "t10" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 54)) in
      Instr.If (Register.read "t10") 1 9
    );
    (9,
      let* "t11" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 55)) in
      Instr.If (Register.read "t11") 1 10
    );
    (10,
      let* "t12" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 56)) in
      Instr.If (Register.read "t12") 1 11
    );
    (11,
      let* "t13" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 57)) in
      Instr.If (Register.read "t13") 1 12
    );
    (12,
      let* "t14" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 97)) in
      Instr.If (Register.read "t14") 2 14
    );
    (13,
      let* "t15" := Instr.BinOp (Val.Lit (Lit.Int 10)) "+" (Register.read "t0") in
      let* "t16" := Instr.BinOp (Register.read "t15") "-" (Val.Lit (Lit.Int 65)) in
      M.Return [(Register.read "t16"); (Val.Lit (Lit.Bool true))]
    );
    (14,
      let* "t17" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 98)) in
      Instr.If (Register.read "t17") 2 15
    );
    (15,
      let* "t18" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 99)) in
      Instr.If (Register.read "t18") 2 16
    );
    (16,
      let* "t19" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 100)) in
      Instr.If (Register.read "t19") 2 17
    );
    (17,
      let* "t20" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 101)) in
      Instr.If (Register.read "t20") 2 18
    );
    (18,
      let* "t21" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 102)) in
      Instr.If (Register.read "t21") 2 19
    );
    (19,
      let* "t22" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 65)) in
      Instr.If (Register.read "t22") 13 20
    );
    (20,
      let* "t23" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 66)) in
      Instr.If (Register.read "t23") 13 21
    );
    (21,
      let* "t24" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 67)) in
      Instr.If (Register.read "t24") 13 22
    );
    (22,
      let* "t25" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 68)) in
      Instr.If (Register.read "t25") 13 23
    );
    (23,
      let* "t26" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 69)) in
      Instr.If (Register.read "t26") 13 24
    );
    (24,
      let* "t27" := Instr.BinOp (Register.read "t0") "==" (Val.Lit (Lit.Int 70)) in
      Instr.If (Register.read "t27") 13 25
    );
    (25,
      M.Return [(Val.Lit (Lit.Int (-1))); (Val.Lit (Lit.Bool false))]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with indexRune (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [s; r] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Range s in
      Instr.Jump 1
    );
    (1,
      let* "t1" := Instr.Next (Register.read "t0") in
      let* "t2" := Instr.Extract (Register.read "t1") 0 in
      Instr.If (Register.read "t2") 2 3
    );
    (2,
      let* "t3" := Instr.Extract (Register.read "t1") 1 in
      let* "t4" := Instr.Extract (Register.read "t1") 2 in
      let* "t5" := Instr.BinOp (Register.read "t4") "==" r in
      Instr.If (Register.read "t5") 4 1
    );
    (3,
      M.Return [(Val.Lit (Lit.Int (-1)))]
    );
    (4,
      M.Return [(Register.read "t3")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with init (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "init$guard") in
      Instr.If (Register.read "t0") 2 1
    );
    (1,
      do* Instr.Store (Register.read "init$guard") (Val.Lit (Lit.Bool true)) in
      let* "t1" := Instr.Call (CallKind.Function (errors.init [])) in
      let* "t2" := Instr.Call (CallKind.Function (sort.init [])) in
      let* "t3" := Instr.Call (CallKind.Function (strconv.init [])) in
      let* "t4" := Instr.Call (CallKind.Function (unicode.utf8.init [])) in
      let* "t5" := Instr.Call (CallKind.Function (internal.fmtsort.init [])) in
      let* "t6" := Instr.Call (CallKind.Function (io.init [])) in
      let* "t7" := Instr.Call (CallKind.Function (os.init [])) in
      let* "t8" := Instr.Call (CallKind.Function (reflect.init [])) in
      let* "t9" := Instr.Call (CallKind.Function (sync.init [])) in
      let* "t10" := Instr.Call (CallKind.Function (math.init [])) in
      let* "t11" := Instr.FieldAddr (Register.read "ppFree") 5 in
      do* Instr.Store (Register.read "t11") init_'dollar1 in
      let* "t12" := Instr.Alloc (* slicelit *) Alloc.Heap "*[10][2]uint16" in
      let* "t13" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 0)) in
      let* "t14" := Instr.IndexAddr (Register.read "t13") (Val.Lit (Lit.Int 0)) in
      let* "t15" := Instr.IndexAddr (Register.read "t13") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t14") (Val.Lit (Lit.Int 9)) in
      do* Instr.Store (Register.read "t15") (Val.Lit (Lit.Int 13)) in
      let* "t16" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 1)) in
      let* "t17" := Instr.IndexAddr (Register.read "t16") (Val.Lit (Lit.Int 0)) in
      let* "t18" := Instr.IndexAddr (Register.read "t16") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t17") (Val.Lit (Lit.Int 32)) in
      do* Instr.Store (Register.read "t18") (Val.Lit (Lit.Int 32)) in
      let* "t19" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 2)) in
      let* "t20" := Instr.IndexAddr (Register.read "t19") (Val.Lit (Lit.Int 0)) in
      let* "t21" := Instr.IndexAddr (Register.read "t19") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t20") (Val.Lit (Lit.Int 133)) in
      do* Instr.Store (Register.read "t21") (Val.Lit (Lit.Int 133)) in
      let* "t22" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 3)) in
      let* "t23" := Instr.IndexAddr (Register.read "t22") (Val.Lit (Lit.Int 0)) in
      let* "t24" := Instr.IndexAddr (Register.read "t22") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t23") (Val.Lit (Lit.Int 160)) in
      do* Instr.Store (Register.read "t24") (Val.Lit (Lit.Int 160)) in
      let* "t25" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 4)) in
      let* "t26" := Instr.IndexAddr (Register.read "t25") (Val.Lit (Lit.Int 0)) in
      let* "t27" := Instr.IndexAddr (Register.read "t25") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t26") (Val.Lit (Lit.Int 5760)) in
      do* Instr.Store (Register.read "t27") (Val.Lit (Lit.Int 5760)) in
      let* "t28" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 5)) in
      let* "t29" := Instr.IndexAddr (Register.read "t28") (Val.Lit (Lit.Int 0)) in
      let* "t30" := Instr.IndexAddr (Register.read "t28") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t29") (Val.Lit (Lit.Int 8192)) in
      do* Instr.Store (Register.read "t30") (Val.Lit (Lit.Int 8202)) in
      let* "t31" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 6)) in
      let* "t32" := Instr.IndexAddr (Register.read "t31") (Val.Lit (Lit.Int 0)) in
      let* "t33" := Instr.IndexAddr (Register.read "t31") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t32") (Val.Lit (Lit.Int 8232)) in
      do* Instr.Store (Register.read "t33") (Val.Lit (Lit.Int 8233)) in
      let* "t34" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 7)) in
      let* "t35" := Instr.IndexAddr (Register.read "t34") (Val.Lit (Lit.Int 0)) in
      let* "t36" := Instr.IndexAddr (Register.read "t34") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t35") (Val.Lit (Lit.Int 8239)) in
      do* Instr.Store (Register.read "t36") (Val.Lit (Lit.Int 8239)) in
      let* "t37" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 8)) in
      let* "t38" := Instr.IndexAddr (Register.read "t37") (Val.Lit (Lit.Int 0)) in
      let* "t39" := Instr.IndexAddr (Register.read "t37") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t38") (Val.Lit (Lit.Int 8287)) in
      do* Instr.Store (Register.read "t39") (Val.Lit (Lit.Int 8287)) in
      let* "t40" := Instr.IndexAddr (Register.read "t12") (Val.Lit (Lit.Int 9)) in
      let* "t41" := Instr.IndexAddr (Register.read "t40") (Val.Lit (Lit.Int 0)) in
      let* "t42" := Instr.IndexAddr (Register.read "t40") (Val.Lit (Lit.Int 1)) in
      do* Instr.Store (Register.read "t41") (Val.Lit (Lit.Int 12288)) in
      do* Instr.Store (Register.read "t42") (Val.Lit (Lit.Int 12288)) in
      let* "t43" := Instr.Slice (Register.read "t12") None None in
      do* Instr.Store (Register.read "space") (Register.read "t43") in
      let* "t44" := Instr.FieldAddr (Register.read "ssFree") 5 in
      do* Instr.Store (Register.read "t44") init_'dollar2 in
      let* "t45" := Instr.Call (CallKind.Function (errors.New [(Val.Lit (Lit.String "syntax error scanning complex number"))])) in
      do* Instr.Store (Register.read "errComplex") (Register.read "t45") in
      let* "t46" := Instr.Call (CallKind.Function (errors.New [(Val.Lit (Lit.String "syntax error scanning boolean"))])) in
      do* Instr.Store (Register.read "errBool") (Register.read "t46") in
      Instr.Jump 2
    );
    (2,
      M.Return []
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with intFromArg (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [a; argNum] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (len [a])) in
      let* "t1" := Instr.BinOp argNum "<" (Register.read "t0") in
      Instr.If (Register.read "t1") 1 2
    );
    (1,
      let* "t2" := Instr.IndexAddr a argNum in
      let* "t3" := Instr.UnOp "*" (Register.read "t2") in
      let* "t4" := Instr.TypeAssert (Register.read "t3") TypeAssert.CommaOk "int" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 4 3
    );
    (2,
      let* "t7" := Instr.Phi (* num *) [(Val.Lit (Lit.Int 0)); (Register.read "t15"); (Val.Lit (Lit.Int 0))] in
      let* "t8" := Instr.Phi (* isInt *) [(Val.Lit (Lit.Bool false)); (Register.read "t16"); (Val.Lit (Lit.Bool false))] in
      let* "t9" := Instr.Phi (* newArgNum *) [argNum; (Register.read "t17"); (Register.read "t17")] in
      M.Return [(Register.read "t7"); (Register.read "t8"); (Register.read "t9")]
    );
    (3,
      let* "t10" := Instr.IndexAddr a argNum in
      let* "t11" := Instr.UnOp "*" (Register.read "t10") in
      let* "t12" := Instr.Call (CallKind.Function (reflect.ValueOf [(Register.read "t11")])) in
      let* "t13" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t12")])) in
      let* "t14" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 2)) in
      Instr.If (Register.read "t14") 5 7
    );
    (4,
      let* "t15" := Instr.Phi (* num *) [(Register.read "t5"); (Register.read "t5"); (Register.read "t5"); (Register.read "t5"); (Register.read "t31"); (Register.read "t5"); (Register.read "t37")] in
      let* "t16" := Instr.Phi (* isInt *) [(Register.read "t6"); (Register.read "t6"); (Register.read "t6"); (Register.read "t6"); (Val.Lit (Lit.Bool true)); (Register.read "t6"); (Val.Lit (Lit.Bool true))] in
      let* "t17" := Instr.BinOp argNum "+" (Val.Lit (Lit.Int 1)) in
      let* "t18" := Instr.Call (CallKind.Function (tooLarge [(Register.read "t15")])) in
      Instr.If (Register.read "t18") 20 2
    );
    (5,
      let* "t19" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t12")])) in
      let* "t20" := Instr.Convert (Register.read "t19") in
      let* "t21" := Instr.Convert (Register.read "t20") in
      let* "t22" := Instr.BinOp (Register.read "t21") "==" (Register.read "t19") in
      Instr.If (Register.read "t22") 12 4
    );
    (6,
      let* "t23" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t12")])) in
      let* "t24" := Instr.Convert (Register.read "t23") in
      let* "t25" := Instr.BinOp (Register.read "t24") ">=" (Val.Lit (Lit.Int 0)) in
      Instr.If (Register.read "t25") 19 4
    );
    (7,
      let* "t26" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 3)) in
      Instr.If (Register.read "t26") 5 8
    );
    (8,
      let* "t27" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 4)) in
      Instr.If (Register.read "t27") 5 9
    );
    (9,
      let* "t28" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 5)) in
      Instr.If (Register.read "t28") 5 10
    );
    (10,
      let* "t29" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 6)) in
      Instr.If (Register.read "t29") 5 11
    );
    (11,
      let* "t30" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 7)) in
      Instr.If (Register.read "t30") 6 13
    );
    (12,
      let* "t31" := Instr.Convert (Register.read "t19") in
      Instr.Jump 4
    );
    (13,
      let* "t32" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 8)) in
      Instr.If (Register.read "t32") 6 14
    );
    (14,
      let* "t33" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 9)) in
      Instr.If (Register.read "t33") 6 15
    );
    (15,
      let* "t34" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 10)) in
      Instr.If (Register.read "t34") 6 16
    );
    (16,
      let* "t35" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 11)) in
      Instr.If (Register.read "t35") 6 17
    );
    (17,
      let* "t36" := Instr.BinOp (Register.read "t13") "==" (Val.Lit (Lit.Int 12)) in
      Instr.If (Register.read "t36") 6 4
    );
    (18,
      let* "t37" := Instr.Convert (Register.read "t23") in
      Instr.Jump 4
    );
    (19,
      let* "t38" := Instr.Convert (Register.read "t23") in
      let* "t39" := Instr.Convert (Register.read "t38") in
      let* "t40" := Instr.BinOp (Register.read "t39") "==" (Register.read "t23") in
      Instr.If (Register.read "t40") 18 4
    );
    (20,
      Instr.Jump 2
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with isSpace (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.BinOp r ">=" (Val.Lit (Lit.Int 65536)) in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      M.Return [(Val.Lit (Lit.Bool false))]
    );
    (2,
      let* "t1" := Instr.Convert r in
      let* "t2" := Instr.Alloc (* rng *) Alloc.Local "*[2]uint16" in
      let* "t3" := Instr.UnOp "*" (Register.read "space") in
      let* "t4" := Instr.Call (CallKind.Function (len [(Register.read "t3")])) in
      Instr.Jump 3
    );
    (3,
      let* "t5" := Instr.Phi (* rangeindex *) [(Val.Lit (Lit.Int (-1))); (Register.read "t6")] in
      let* "t6" := Instr.BinOp (Register.read "t5") "+" (Val.Lit (Lit.Int 1)) in
      let* "t7" := Instr.BinOp (Register.read "t6") "<" (Register.read "t4") in
      Instr.If (Register.read "t7") 4 5
    );
    (4,
      let* "t8" := Instr.IndexAddr (Register.read "t3") (Register.read "t6") in
      let* "t9" := Instr.UnOp "*" (Register.read "t8") in
      do* Instr.Store (Register.read "t2") (Register.read "t9") in
      let* "t10" := Instr.IndexAddr (Register.read "t2") (Val.Lit (Lit.Int 0)) in
      let* "t11" := Instr.UnOp "*" (Register.read "t10") in
      let* "t12" := Instr.BinOp (Register.read "t1") "<" (Register.read "t11") in
      Instr.If (Register.read "t12") 6 7
    );
    (5,
      M.Return [(Val.Lit (Lit.Bool false))]
    );
    (6,
      M.Return [(Val.Lit (Lit.Bool false))]
    );
    (7,
      let* "t13" := Instr.IndexAddr (Register.read "t2") (Val.Lit (Lit.Int 1)) in
      let* "t14" := Instr.UnOp "*" (Register.read "t13") in
      let* "t15" := Instr.BinOp (Register.read "t1") "<=" (Register.read "t14") in
      Instr.If (Register.read "t15") 8 3
    );
    (8,
      M.Return [(Val.Lit (Lit.Bool true))]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with newPrinter (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (TODO_method [(Register.read "ppFree")])) in
      let* "t1" := Instr.TypeAssert (Register.read "t0") TypeAssert.NoCommaOk "*fmt.pp" in
      let* "t2" := Instr.FieldAddr (Register.read "t1") 6 in
      do* Instr.Store (Register.read "t2") (Val.Lit (Lit.Bool false)) in
      let* "t3" := Instr.FieldAddr (Register.read "t1") 7 in
      do* Instr.Store (Register.read "t3") (Val.Lit (Lit.Bool false)) in
      let* "t4" := Instr.FieldAddr (Register.read "t1") 8 in
      do* Instr.Store (Register.read "t4") (Val.Lit (Lit.Bool false)) in
      let* "t5" := Instr.FieldAddr (Register.read "t1") 3 in
      let* "t6" := Instr.FieldAddr (Register.read "t1") 0 in
      let* "t7" := Instr.Call (CallKind.Function (TODO_method [(Register.read "t5"); (Register.read "t6")])) in
      M.Return [(Register.read "t1")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with newScanState (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r; nlIsSpace; nlIsEnd] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (TODO_method [(Register.read "ssFree")])) in
      let* "t1" := Instr.TypeAssert (Register.read "t0") TypeAssert.NoCommaOk "*fmt.ss" in
      let* "t2" := Instr.TypeAssert r TypeAssert.CommaOk "io.RuneScanner" in
      let* "t3" := Instr.Extract (Register.read "t2") 0 in
      let* "t4" := Instr.Extract (Register.read "t2") 1 in
      Instr.If (Register.read "t4") 1 3
    );
    (1,
      let* "t5" := Instr.FieldAddr (Register.read "t1") 0 in
      do* Instr.Store (Register.read "t5") (Register.read "t3") in
      Instr.Jump 2
    );
    (2,
      let* "t6" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t7" := Instr.FieldAddr (Register.read "t6") 2 in
      do* Instr.Store (Register.read "t7") nlIsSpace in
      let* "t8" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t9" := Instr.FieldAddr (Register.read "t8") 1 in
      do* Instr.Store (Register.read "t9") nlIsEnd in
      let* "t10" := Instr.FieldAddr (Register.read "t1") 3 in
      do* Instr.Store (Register.read "t10") (Val.Lit (Lit.Bool false)) in
      let* "t11" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t12" := Instr.FieldAddr (Register.read "t11") 4 in
      do* Instr.Store (Register.read "t12") (Val.Lit (Lit.Int 1073741824)) in
      let* "t13" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t14" := Instr.FieldAddr (Register.read "t13") 3 in
      do* Instr.Store (Register.read "t14") (Val.Lit (Lit.Int 1073741824)) in
      let* "t15" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t16" := Instr.FieldAddr (Register.read "t15") 5 in
      do* Instr.Store (Register.read "t16") (Val.Lit (Lit.Int 1073741824)) in
      let* "t17" := Instr.FieldAddr (Register.read "t1") 4 in
      let* "t18" := Instr.FieldAddr (Register.read "t17") 0 in
      do* Instr.Store (Register.read "t18") (Val.Lit (Lit.Bool true)) in
      let* "t19" := Instr.FieldAddr (Register.read "t1") 2 in
      do* Instr.Store (Register.read "t19") (Val.Lit (Lit.Int 0)) in
      M.Return [(Register.read "t1"); (Val.Lit Lit.Nil)]
    );
    (3,
      let* "t20" := Instr.Alloc (* complit *) Alloc.Heap "*fmt.readRune" in
      let* "t21" := Instr.FieldAddr (Register.read "t20") 0 in
      let* "t22" := Instr.FieldAddr (Register.read "t20") 4 in
      do* Instr.Store (Register.read "t21") r in
      do* Instr.Store (Register.read "t22") (Val.Lit (Lit.Int (-1))) in
      let* "t23" := Instr.FieldAddr (Register.read "t1") 0 in
      let* "t24" := Instr.MakeInterface (Register.read "t20") in
      do* Instr.Store (Register.read "t23") (Register.read "t24") in
      Instr.Jump 2
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with notSpace (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [r] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (isSpace [r])) in
      let* "t1" := Instr.UnOp "!" (Register.read "t0") in
      M.Return [(Register.read "t1")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with parseArgNumber (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [format] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Call (CallKind.Function (len [format])) in
      let* "t1" := Instr.BinOp (Register.read "t0") "<" (Val.Lit (Lit.Int 3)) in
      Instr.If (Register.read "t1") 1 2
    );
    (1,
      M.Return [(Val.Lit (Lit.Int 0)); (Val.Lit (Lit.Int 1)); (Val.Lit (Lit.Bool false))]
    );
    (2,
      Instr.Jump 5
    );
    (3,
      let* "t2" := Instr.Index format (Register.read "t4") in
      let* "t3" := Instr.BinOp (Register.read "t2") "==" (Val.Lit (Lit.Int 93)) in
      Instr.If (Register.read "t3") 6 7
    );
    (4,
      M.Return [(Val.Lit (Lit.Int 0)); (Val.Lit (Lit.Int 1)); (Val.Lit (Lit.Bool false))]
    );
    (5,
      let* "t4" := Instr.Phi (* i *) [(Val.Lit (Lit.Int 1)); (Register.read "t11")] in
      let* "t5" := Instr.Call (CallKind.Function (len [format])) in
      let* "t6" := Instr.BinOp (Register.read "t4") "<" (Register.read "t5") in
      Instr.If (Register.read "t6") 3 4
    );
    (6,
      let* "t7" := Instr.Call (CallKind.Function (parsenum [format; (Val.Lit (Lit.Int 1)); (Register.read "t4")])) in
      let* "t8" := Instr.Extract (Register.read "t7") 0 in
      let* "t9" := Instr.Extract (Register.read "t7") 1 in
      let* "t10" := Instr.Extract (Register.read "t7") 2 in
      Instr.If (Register.read "t9") 10 8
    );
    (7,
      let* "t11" := Instr.BinOp (Register.read "t4") "+" (Val.Lit (Lit.Int 1)) in
      Instr.Jump 5
    );
    (8,
      let* "t12" := Instr.BinOp (Register.read "t4") "+" (Val.Lit (Lit.Int 1)) in
      M.Return [(Val.Lit (Lit.Int 0)); (Register.read "t12"); (Val.Lit (Lit.Bool false))]
    );
    (9,
      let* "t13" := Instr.BinOp (Register.read "t8") "-" (Val.Lit (Lit.Int 1)) in
      let* "t14" := Instr.BinOp (Register.read "t4") "+" (Val.Lit (Lit.Int 1)) in
      M.Return [(Register.read "t13"); (Register.read "t14"); (Val.Lit (Lit.Bool true))]
    );
    (10,
      let* "t15" := Instr.BinOp (Register.read "t10") "!=" (Register.read "t4") in
      Instr.If (Register.read "t15") 8 9
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with parsenum (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [s; start; _'end] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.BinOp start ">=" _'end in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      M.Return [(Val.Lit (Lit.Int 0)); (Val.Lit (Lit.Bool false)); _'end]
    );
    (2,
      Instr.Jump 5
    );
    (3,
      let* "t1" := Instr.Call (CallKind.Function (tooLarge [(Register.read "t2")])) in
      Instr.If (Register.read "t1") 8 9
    );
    (4,
      M.Return [(Register.read "t2"); (Register.read "t3"); (Register.read "t4")]
    );
    (5,
      let* "t2" := Instr.Phi (* num *) [(Val.Lit (Lit.Int 0)); (Register.read "t14")] in
      let* "t3" := Instr.Phi (* isnum *) [(Val.Lit (Lit.Bool false)); (Val.Lit (Lit.Bool true))] in
      let* "t4" := Instr.Phi (* newi *) [start; (Register.read "t15")] in
      let* "t5" := Instr.BinOp (Register.read "t4") "<" _'end in
      Instr.If (Register.read "t5") 7 4
    );
    (6,
      let* "t6" := Instr.Index s (Register.read "t4") in
      let* "t7" := Instr.BinOp (Register.read "t6") "<=" (Val.Lit (Lit.Int 57)) in
      Instr.If (Register.read "t7") 3 4
    );
    (7,
      let* "t8" := Instr.Index s (Register.read "t4") in
      let* "t9" := Instr.BinOp (Val.Lit (Lit.Int 48)) "<=" (Register.read "t8") in
      Instr.If (Register.read "t9") 6 4
    );
    (8,
      M.Return [(Val.Lit (Lit.Int 0)); (Val.Lit (Lit.Bool false)); _'end]
    );
    (9,
      let* "t10" := Instr.BinOp (Register.read "t2") "*" (Val.Lit (Lit.Int 10)) in
      let* "t11" := Instr.Index s (Register.read "t4") in
      let* "t12" := Instr.BinOp (Register.read "t11") "-" (Val.Lit (Lit.Int 48)) in
      let* "t13" := Instr.Convert (Register.read "t12") in
      let* "t14" := Instr.BinOp (Register.read "t10") "+" (Register.read "t13") in
      let* "t15" := Instr.BinOp (Register.read "t4") "+" (Val.Lit (Lit.Int 1)) in
      Instr.Jump 5
    )])
  | _ => M.Thunk (M.EvalBody [])
  end)

with tooLarge (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [x] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.BinOp x ">" (Val.Lit (Lit.Int 1000000)) in
      Instr.If (Register.read "t0") 2 1
    );
    (1,
      let* "t1" := Instr.BinOp x "<" (Val.Lit (Lit.Int (-1000000))) in
      Instr.Jump 2
    );
    (2,
      let* "t2" := Instr.Phi (* || *) [(Val.Lit (Lit.Bool true)); (Register.read "t1")] in
      M.Return [(Register.read "t2")]
    )])
  | _ => M.Thunk (M.EvalBody [])
  end).

(** ** Types *)

Parameter Formatter : Set.

Parameter GoStringer : Set.

Parameter ScanState : Set.

Parameter Scanner : Set.

Parameter State : Set.

Parameter Stringer : Set.

Parameter buffer : Set.

Parameter fmt : Set.

Parameter fmtFlags : Set.

Parameter pp : Set.

Parameter readRune : Set.

Parameter scanError : Set.

Parameter ss : Set.

Parameter ssave : Set.

Parameter stringReader : Set.

Parameter wrapError : Set.

Parameter wrapErrors : Set.

