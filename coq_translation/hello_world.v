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
  | String (_ : string).
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

(* Parameter TODO_constant : Val.t.

Parameter TODO_method : Function.t. *)

(* Parameter len : Function.t.

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
End unicode. *)

Local Unset Guard Checking.
(** ** Constants *)

(** ** Globals *)

Module GlobalName.
  Inductive t : Set :=
  | init_'dollarguard : t
  .
End GlobalName.

Parameter global : GlobalName.t -> M Val.t.

Definition init_'dollarguard : M Val.t :=
  global GlobalName.init_'dollarguard.

(** ** Functions *)

CoFixpoint Main (α : list Val.t) : M (list Val.t) :=
  M.Thunk (
  match α with
  | [] =>
    M.Thunk (M.EvalBody [(0,
      let* "t0" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t1" := Instr.IndexAddr (Register.read "t0") (Val.Lit (Lit.Int 0)) in
      let* "t2" := Instr.MakeInterface (Val.Lit (Lit.String "Hello, World!")) in
      do* Instr.Store (Register.read "t1") (Register.read "t2") in
      let* "t3" := Instr.Slice (Register.read "t0") None None in
      let* "t4" := Instr.Call (CallKind.Function (fmt.Println [(Register.read "t3")])) in
      M.Return []
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
      let* "t1" := Instr.Call (CallKind.Function (fmt.init [])) in
      Instr.Jump 2
    );
    (2,
      M.Return []
    )])
  | _ => M.Thunk (M.EvalBody [])
  end).

(** ** Types *)

