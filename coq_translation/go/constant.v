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
  Inductive t (A : Set) : Set :=
  | Return (_ : A)
  | Bind {B : Set} (_ : t B) (_ : B -> t A).
  Arguments Return {A}.
  Arguments Bind {A B}.
End M.
Definition M : Set -> Set := M.t.

Module Register.
  Parameter read : string -> Val.t.

  Parameter write : string -> M Val.t -> M (list Val.t) -> M (list Val.t).
End Register.

(* Notation "'let*' a := b 'in' c" :=
  (M.Bind b (fun a => c))
  (at level 200, b at level 100, a name). *)

Notation "'let*' a := b 'in' c" :=
  (Register.write a b c)
  (at level 200).

Module Function.
  CoInductive t : Set :=
  | Body (_ : Val.t -> list (Z * M (list Val.t))).
End Function.

Module Alloc.
  Inductive t : Set :=
  | Heap
  | Local.
End Alloc.

Module CallKind.
  Inductive t : Set :=
  | Function (_ : Function.t)
  | Method (_ : Val.t) (_ : string).
End CallKind.

Module TypeAssert.
  Inductive t : Set :=
  | CommaOk
  | NoCommaOk.
End TypeAssert.

Module Instr.
  Parameter Alloc : Alloc.t -> string -> M Val.t.

  Parameter BinOp : Val.t -> string -> Val.t -> M Val.t.

  Parameter Call : CallKind.t -> list Val.t -> M Val.t.

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

Parameter TODO_constant : Val.t.

Parameter TODO_method : Function.t.

Parameter len : Function.t.

Module fmt.
  Parameter init : Function.t.

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
(** ** Constants *)

Definition Bool : Val.t :=
  Val.Lit (Lit.Int 1).

Definition Complex : Val.t :=
  Val.Lit (Lit.Int 5).

Definition Float : Val.t :=
  Val.Lit (Lit.Int 4).

Definition Int : Val.t :=
  Val.Lit (Lit.Int 3).

Definition String : Val.t :=
  Val.Lit (Lit.Int 2).

Definition Unknown : Val.t :=
  Val.Lit (Lit.Int 0).

Definition _Kind_name : Val.t :=
  Val.Lit (Lit.String "UnknownBoolStringIntFloatComplex").

Definition _log : Val.t :=
  Val.Lit (Lit.Int 3).

Definition _m : Val.t :=
  Val.Lit (Lit.Int 18446744073709551615).

Definition maxExp : Val.t :=
  Val.Lit (Lit.Int 4096).

Definition prec : Val.t :=
  Val.Lit (Lit.Int 512).

Definition wordSize : Val.t :=
  Val.Lit (Lit.Int 8).

(** ** Globals *)

Module GlobalName.
  Inductive t : Set :=
  | _Kind_index : t
  | emptyString : t
  | floatVal0 : t
  | init_'dollarguard : t
  .
End GlobalName.

Parameter global : GlobalName.t -> M Val.t.

Definition _Kind_index : M Val.t :=
  global GlobalName._Kind_index.

Definition emptyString : M Val.t :=
  global GlobalName.emptyString.

Definition floatVal0 : M Val.t :=
  global GlobalName.floatVal0.

Definition init_'dollarguard : M Val.t :=
  global GlobalName.init_'dollarguard.

(** ** Functions *)

CoFixpoint BinaryOp : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x_; op; y_] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function _'match) [x_; y_] in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      let* "t3" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 1 2
    );
    (1,
      let* "t6" := Instr.MakeInterface (Register.read "t4") in
      M.Return [(Register.read "t6")]
    );
    (2,
      let* "t7" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t8" := Instr.Extract (Register.read "t7") 0 in
      let* "t9" := Instr.Extract (Register.read "t7") 1 in
      Instr.If (Register.read "t9") 3 4
    );
    (3,
      let* "t10" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.boolVal" in
      let* "t11" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t11") 5 7
    );
    (4,
      let* "t12" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t13" := Instr.Extract (Register.read "t12") 0 in
      let* "t14" := Instr.Extract (Register.read "t12") 1 in
      Instr.If (Register.read "t14") 12 13
    );
    (5,
      Instr.If (Register.read "t8") 8 9
    );
    (6,
      Instr.If (Register.read "t8") 11 10
    );
    (7,
      let* "t15" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t15") 6 43
    );
    (8,
      Instr.Jump 9
    );
    (9,
      let* "t16" := Instr.Phi (* && *) [TODO_constant; (Register.read "t10")] in
      let* "t17" := Instr.MakeInterface (Register.read "t16") in
      M.Return [(Register.read "t17")]
    );
    (10,
      Instr.Jump 11
    );
    (11,
      let* "t18" := Instr.Phi (* || *) [TODO_constant; (Register.read "t10")] in
      let* "t19" := Instr.MakeInterface (Register.read "t18") in
      M.Return [(Register.read "t19")]
    );
    (12,
      let* "t20" := Instr.ChangeType (Register.read "t13") in
      let* "t21" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.int64Val" in
      let* "t22" := Instr.ChangeType (Register.read "t21") in
      let* "t23" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t23") 15 17
    );
    (13,
      let* "t24" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.intVal" in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      Instr.If (Register.read "t26") 44 45
    );
    (14,
      let* "t27" := Instr.Phi (* c *) [(Register.read "t38"); (Register.read "t47"); (Register.read "t57"); (Register.read "t59"); (Register.read "t61"); (Register.read "t63"); (Register.read "t65"); (Register.read "t67"); (Register.read "t69")] in
      let* "t28" := Instr.ChangeType (Register.read "t27") in
      let* "t29" := Instr.MakeInterface (Register.read "t28") in
      M.Return [(Register.read "t29")]
    );
    (15,
      let* "t30" := Instr.Call (CallKind.Function is63bit) [(Register.read "t20")] in
      Instr.If (Register.read "t30") 20 18
    );
    (16,
      let* "t31" := Instr.Call (CallKind.Function is63bit) [(Register.read "t20")] in
      Instr.If (Register.read "t31") 25 23
    );
    (17,
      let* "t32" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t32") 16 22
    );
    (18,
      let* "t33" := Instr.Call (CallKind.Function newInt) [] in
      let* "t34" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t20")] in
      let* "t35" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t22")] in
      let* "t36" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t33"); (Register.read "t34"); (Register.read "t35")] in
      let* "t37" := Instr.Call (CallKind.Function makeInt) [(Register.read "t36")] in
      M.Return [(Register.read "t37")]
    );
    (19,
      let* "t38" := Instr.BinOp (Register.read "t20") "+" (Register.read "t22") in
      Instr.Jump 14
    );
    (20,
      let* "t39" := Instr.Call (CallKind.Function is63bit) [(Register.read "t22")] in
      Instr.If (Register.read "t39") 19 18
    );
    (21,
      let* "t40" := Instr.Call (CallKind.Function is32bit) [(Register.read "t20")] in
      Instr.If (Register.read "t40") 30 28
    );
    (22,
      let* "t41" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t41") 21 27
    );
    (23,
      let* "t42" := Instr.Call (CallKind.Function newInt) [] in
      let* "t43" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t20")] in
      let* "t44" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t22")] in
      let* "t45" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t42"); (Register.read "t43"); (Register.read "t44")] in
      let* "t46" := Instr.Call (CallKind.Function makeInt) [(Register.read "t45")] in
      M.Return [(Register.read "t46")]
    );
    (24,
      let* "t47" := Instr.BinOp (Register.read "t20") "-" (Register.read "t22") in
      Instr.Jump 14
    );
    (25,
      let* "t48" := Instr.Call (CallKind.Function is63bit) [(Register.read "t22")] in
      Instr.If (Register.read "t48") 24 23
    );
    (26,
      let* "t49" := Instr.Call (CallKind.Function math.big.NewRat) [(Register.read "t20"); (Register.read "t22")] in
      let* "t50" := Instr.Call (CallKind.Function makeRat) [(Register.read "t49")] in
      M.Return [(Register.read "t50")]
    );
    (27,
      let* "t51" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t51") 26 32
    );
    (28,
      let* "t52" := Instr.Call (CallKind.Function newInt) [] in
      let* "t53" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t20")] in
      let* "t54" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t22")] in
      let* "t55" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t52"); (Register.read "t53"); (Register.read "t54")] in
      let* "t56" := Instr.Call (CallKind.Function makeInt) [(Register.read "t55")] in
      M.Return [(Register.read "t56")]
    );
    (29,
      let* "t57" := Instr.BinOp (Register.read "t20") "*" (Register.read "t22") in
      Instr.Jump 14
    );
    (30,
      let* "t58" := Instr.Call (CallKind.Function is32bit) [(Register.read "t22")] in
      Instr.If (Register.read "t58") 29 28
    );
    (31,
      let* "t59" := Instr.BinOp (Register.read "t20") "/" (Register.read "t22") in
      Instr.Jump 14
    );
    (32,
      let* "t60" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t60") 31 34
    );
    (33,
      let* "t61" := Instr.BinOp (Register.read "t20") "%" (Register.read "t22") in
      Instr.Jump 14
    );
    (34,
      let* "t62" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t62") 33 36
    );
    (35,
      let* "t63" := Instr.BinOp (Register.read "t20") "&" (Register.read "t22") in
      Instr.Jump 14
    );
    (36,
      let* "t64" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t64") 35 38
    );
    (37,
      let* "t65" := Instr.BinOp (Register.read "t20") "|" (Register.read "t22") in
      Instr.Jump 14
    );
    (38,
      let* "t66" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t66") 37 40
    );
    (39,
      let* "t67" := Instr.BinOp (Register.read "t20") "^" (Register.read "t22") in
      Instr.Jump 14
    );
    (40,
      let* "t68" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t68") 39 42
    );
    (41,
      let* "t69" := Instr.BinOp (Register.read "t20") "&^" (Register.read "t22") in
      Instr.Jump 14
    );
    (42,
      let* "t70" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t70") 41 43
    );
    (43,
      let* "t71" := Instr.Alloc (* varargs *) Alloc.Heap "*[3]any" in
      let* "t72" := Instr.IndexAddr (Register.read "t71") TODO_constant in
      let* "t73" := Instr.ChangeInterface x_ in
      let* _ := Instr.Store (Register.read "t72") (Register.read "t73") in
      let* "t74" := Instr.IndexAddr (Register.read "t71") TODO_constant in
      let* "t75" := Instr.MakeInterface op in
      let* _ := Instr.Store (Register.read "t74") (Register.read "t75") in
      let* "t76" := Instr.IndexAddr (Register.read "t71") TODO_constant in
      let* "t77" := Instr.ChangeInterface y_ in
      let* _ := Instr.Store (Register.read "t76") (Register.read "t77") in
      let* "t78" := Instr.Slice (Register.read "t71") None None in
      let* "t79" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t78")] in
      let* "t80" := Instr.MakeInterface (Register.read "t79") in
      Instr.Panic (Register.read "t80")
    );
    (44,
      let* "t81" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t81") (Register.read "t25") in
      let* "t82" := Instr.FieldAddr (Register.read "t81") 0 in
      let* "t83" := Instr.UnOp "*" (Register.read "t82") in
      let* "t84" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.intVal" in
      let* "t85" := Instr.Field (Register.read "t84") 0 in
      let* "t86" := Instr.Call (CallKind.Function newInt) [] in
      let* "t87" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t87") 47 49
    );
    (45,
      let* "t88" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t89" := Instr.Extract (Register.read "t88") 0 in
      let* "t90" := Instr.Extract (Register.read "t88") 1 in
      Instr.If (Register.read "t90") 66 67
    );
    (46,
      let* "t91" := Instr.Call (CallKind.Function makeInt) [(Register.read "t86")] in
      M.Return [(Register.read "t91")]
    );
    (47,
      let* "t92" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (48,
      let* "t93" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (49,
      let* "t94" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t94") 48 51
    );
    (50,
      let* "t95" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (51,
      let* "t96" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t96") 50 53
    );
    (52,
      let* "t97" := Instr.Call (CallKind.Function newRat) [] in
      let* "t98" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t97"); (Register.read "t83"); (Register.read "t85")] in
      let* "t99" := Instr.Call (CallKind.Function makeRat) [(Register.read "t98")] in
      M.Return [(Register.read "t99")]
    );
    (53,
      let* "t100" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t100") 52 55
    );
    (54,
      let* "t101" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (55,
      let* "t102" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t102") 54 57
    );
    (56,
      let* "t103" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (57,
      let* "t104" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t104") 56 59
    );
    (58,
      let* "t105" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (59,
      let* "t106" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t106") 58 61
    );
    (60,
      let* "t107" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (61,
      let* "t108" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t108") 60 63
    );
    (62,
      let* "t109" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (63,
      let* "t110" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t110") 62 65
    );
    (64,
      let* "t111" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t86"); (Register.read "t83"); (Register.read "t85")] in
      Instr.Jump 46
    );
    (65,
      let* "t112" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t112") 64 43
    );
    (66,
      let* "t113" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t113") (Register.read "t89") in
      let* "t114" := Instr.FieldAddr (Register.read "t113") 0 in
      let* "t115" := Instr.UnOp "*" (Register.read "t114") in
      let* "t116" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.ratVal" in
      let* "t117" := Instr.Field (Register.read "t116") 0 in
      let* "t118" := Instr.Call (CallKind.Function newRat) [] in
      let* "t119" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t119") 69 71
    );
    (67,
      let* "t120" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t121" := Instr.Extract (Register.read "t120") 0 in
      let* "t122" := Instr.Extract (Register.read "t120") 1 in
      Instr.If (Register.read "t122") 76 77
    );
    (68,
      let* "t123" := Instr.Call (CallKind.Function makeRat) [(Register.read "t118")] in
      M.Return [(Register.read "t123")]
    );
    (69,
      let* "t124" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t118"); (Register.read "t115"); (Register.read "t117")] in
      Instr.Jump 68
    );
    (70,
      let* "t125" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t118"); (Register.read "t115"); (Register.read "t117")] in
      Instr.Jump 68
    );
    (71,
      let* "t126" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t126") 70 73
    );
    (72,
      let* "t127" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t118"); (Register.read "t115"); (Register.read "t117")] in
      Instr.Jump 68
    );
    (73,
      let* "t128" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t128") 72 75
    );
    (74,
      let* "t129" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t118"); (Register.read "t115"); (Register.read "t117")] in
      Instr.Jump 68
    );
    (75,
      let* "t130" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t130") 74 43
    );
    (76,
      let* "t131" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t131") (Register.read "t121") in
      let* "t132" := Instr.FieldAddr (Register.read "t131") 0 in
      let* "t133" := Instr.UnOp "*" (Register.read "t132") in
      let* "t134" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.floatVal" in
      let* "t135" := Instr.Field (Register.read "t134") 0 in
      let* "t136" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t137" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t137") 79 81
    );
    (77,
      let* "t138" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t139" := Instr.Extract (Register.read "t138") 0 in
      let* "t140" := Instr.Extract (Register.read "t138") 1 in
      Instr.If (Register.read "t140") 86 87
    );
    (78,
      let* "t141" := Instr.Call (CallKind.Function makeFloat) [(Register.read "t136")] in
      M.Return [(Register.read "t141")]
    );
    (79,
      let* "t142" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t136"); (Register.read "t133"); (Register.read "t135")] in
      Instr.Jump 78
    );
    (80,
      let* "t143" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t136"); (Register.read "t133"); (Register.read "t135")] in
      Instr.Jump 78
    );
    (81,
      let* "t144" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t144") 80 83
    );
    (82,
      let* "t145" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t136"); (Register.read "t133"); (Register.read "t135")] in
      Instr.Jump 78
    );
    (83,
      let* "t146" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t146") 82 85
    );
    (84,
      let* "t147" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t136"); (Register.read "t133"); (Register.read "t135")] in
      Instr.Jump 78
    );
    (85,
      let* "t148" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t148") 84 43
    );
    (86,
      let* "t149" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t149") (Register.read "t139") in
      let* "t150" := Instr.Alloc (* y *) Alloc.Local "*go/constant.complexVal" in
      let* "t151" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t150") (Register.read "t151") in
      let* "t152" := Instr.FieldAddr (Register.read "t149") 0 in
      let* "t153" := Instr.UnOp "*" (Register.read "t152") in
      let* "t154" := Instr.FieldAddr (Register.read "t149") 1 in
      let* "t155" := Instr.UnOp "*" (Register.read "t154") in
      let* "t156" := Instr.FieldAddr (Register.read "t150") 0 in
      let* "t157" := Instr.UnOp "*" (Register.read "t156") in
      let* "t158" := Instr.FieldAddr (Register.read "t150") 1 in
      let* "t159" := Instr.UnOp "*" (Register.read "t158") in
      let* "t160" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t160") 89 91
    );
    (87,
      let* "t161" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "*go/constant.stringVal" in
      let* "t162" := Instr.Extract (Register.read "t161") 0 in
      let* "t163" := Instr.Extract (Register.read "t161") 1 in
      Instr.If (Register.read "t163") 96 43
    );
    (88,
      let* "t164" := Instr.Phi (* re *) [(Register.read "t167"); (Register.read "t169"); (Register.read "t176"); (Register.read "t187")] in
      let* "t165" := Instr.Phi (* im *) [(Register.read "t168"); (Register.read "t170"); (Register.read "t177"); (Register.read "t189")] in
      let* "t166" := Instr.Call (CallKind.Function makeComplex) [(Register.read "t164"); (Register.read "t165")] in
      M.Return [(Register.read "t166")]
    );
    (89,
      let* "t167" := Instr.Call (CallKind.Function add) [(Register.read "t153"); (Register.read "t157")] in
      let* "t168" := Instr.Call (CallKind.Function add) [(Register.read "t155"); (Register.read "t159")] in
      Instr.Jump 88
    );
    (90,
      let* "t169" := Instr.Call (CallKind.Function sub) [(Register.read "t153"); (Register.read "t157")] in
      let* "t170" := Instr.Call (CallKind.Function sub) [(Register.read "t155"); (Register.read "t159")] in
      Instr.Jump 88
    );
    (91,
      let* "t171" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t171") 90 93
    );
    (92,
      let* "t172" := Instr.Call (CallKind.Function mul) [(Register.read "t153"); (Register.read "t157")] in
      let* "t173" := Instr.Call (CallKind.Function mul) [(Register.read "t155"); (Register.read "t159")] in
      let* "t174" := Instr.Call (CallKind.Function mul) [(Register.read "t155"); (Register.read "t157")] in
      let* "t175" := Instr.Call (CallKind.Function mul) [(Register.read "t153"); (Register.read "t159")] in
      let* "t176" := Instr.Call (CallKind.Function sub) [(Register.read "t172"); (Register.read "t173")] in
      let* "t177" := Instr.Call (CallKind.Function add) [(Register.read "t174"); (Register.read "t175")] in
      Instr.Jump 88
    );
    (93,
      let* "t178" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t178") 92 95
    );
    (94,
      let* "t179" := Instr.Call (CallKind.Function mul) [(Register.read "t153"); (Register.read "t157")] in
      let* "t180" := Instr.Call (CallKind.Function mul) [(Register.read "t155"); (Register.read "t159")] in
      let* "t181" := Instr.Call (CallKind.Function mul) [(Register.read "t155"); (Register.read "t157")] in
      let* "t182" := Instr.Call (CallKind.Function mul) [(Register.read "t153"); (Register.read "t159")] in
      let* "t183" := Instr.Call (CallKind.Function mul) [(Register.read "t157"); (Register.read "t157")] in
      let* "t184" := Instr.Call (CallKind.Function mul) [(Register.read "t159"); (Register.read "t159")] in
      let* "t185" := Instr.Call (CallKind.Function add) [(Register.read "t183"); (Register.read "t184")] in
      let* "t186" := Instr.Call (CallKind.Function add) [(Register.read "t179"); (Register.read "t180")] in
      let* "t187" := Instr.Call (CallKind.Function quo) [(Register.read "t186"); (Register.read "t185")] in
      let* "t188" := Instr.Call (CallKind.Function sub) [(Register.read "t181"); (Register.read "t182")] in
      let* "t189" := Instr.Call (CallKind.Function quo) [(Register.read "t188"); (Register.read "t185")] in
      Instr.Jump 88
    );
    (95,
      let* "t190" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t190") 94 43
    );
    (96,
      let* "t191" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t191") 97 43
    );
    (97,
      let* "t192" := Instr.Alloc (* complit *) Alloc.Heap "*go/constant.stringVal" in
      let* "t193" := Instr.FieldAddr (Register.read "t192") 2 in
      let* "t194" := Instr.FieldAddr (Register.read "t192") 3 in
      let* "t195" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "*go/constant.stringVal" in
      let* _ := Instr.Store (Register.read "t193") (Register.read "t162") in
      let* _ := Instr.Store (Register.read "t194") (Register.read "t195") in
      let* "t196" := Instr.MakeInterface (Register.read "t192") in
      M.Return [(Register.read "t196")]
    )]
  | _ => []
  end)

with BitLen : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.Convert (Register.read "t1") in
      let* "t4" := Instr.BinOp (Register.read "t1") "<" TODO_constant in
      Instr.If (Register.read "t4") 3 4
    );
    (2,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 5 6
    );
    (3,
      let* "t8" := Instr.UnOp "-" (Register.read "t1") in
      let* "t9" := Instr.Convert (Register.read "t8") in
      Instr.Jump 4
    );
    (4,
      let* "t10" := Instr.Phi (* u *) [(Register.read "t3"); (Register.read "t9")] in
      let* "t11" := Instr.Call (CallKind.Function math.bits.LeadingZeros64) [(Register.read "t10")] in
      let* "t12" := Instr.BinOp TODO_constant "-" (Register.read "t11") in
      M.Return [(Register.read "t12")]
    );
    (5,
      let* "t13" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t13") (Register.read "t6") in
      let* "t14" := Instr.FieldAddr (Register.read "t13") 0 in
      let* "t15" := Instr.UnOp "*" (Register.read "t14") in
      let* "t16" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t15")] in
      M.Return [(Register.read "t16")]
    );
    (6,
      let* "t17" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t18" := Instr.Extract (Register.read "t17") 0 in
      let* "t19" := Instr.Extract (Register.read "t17") 1 in
      Instr.If (Register.read "t19") 7 8
    );
    (7,
      M.Return [TODO_constant]
    );
    (8,
      let* "t20" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t21" := Instr.IndexAddr (Register.read "t20") TODO_constant in
      let* "t22" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t21") (Register.read "t22") in
      let* "t23" := Instr.Slice (Register.read "t20") None None in
      let* "t24" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t23")] in
      let* "t25" := Instr.MakeInterface (Register.read "t24") in
      Instr.Panic (Register.read "t25")
    )]
  | _ => []
  end)

with BoolVal : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.ChangeType (Register.read "t1") in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 3 4
    );
    (3,
      M.Return [TODO_constant]
    );
    (4,
      let* "t7" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t8" := Instr.IndexAddr (Register.read "t7") TODO_constant in
      let* "t9" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t9") in
      let* "t10" := Instr.Slice (Register.read "t7") None None in
      let* "t11" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t10")] in
      let* "t12" := Instr.MakeInterface (Register.read "t11") in
      Instr.Panic (Register.read "t12")
    )]
  | _ => []
  end)

with Bytes : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* t *) Alloc.Local "*go/constant.intVal" in
      let* "t1" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t2" := Instr.Extract (Register.read "t1") 0 in
      let* "t3" := Instr.Extract (Register.read "t1") 1 in
      Instr.If (Register.read "t3") 2 3
    );
    (1,
      let* "t4" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t5" := Instr.UnOp "*" (Register.read "t4") in
      let* "t6" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t5")] in
      let* "t7" := Instr.Call (CallKind.Function len) [(Register.read "t6")] in
      let* "t8" := Instr.BinOp (Register.read "t7") "*" TODO_constant in
      let* "t9" := Instr.MakeSlice (Register.read "t8") (Register.read "t8") in
      let* "t10" := Instr.Call (CallKind.Function len) [(Register.read "t6")] in
      Instr.Jump 6
    );
    (2,
      let* "t11" := Instr.Call (CallKind.Function i64toi) [(Register.read "t2")] in
      let* _ := Instr.Store (Register.read "t0") (Register.read "t11") in
      Instr.Jump 1
    );
    (3,
      let* "t12" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t13" := Instr.Extract (Register.read "t12") 0 in
      let* "t14" := Instr.Extract (Register.read "t12") 1 in
      Instr.If (Register.read "t14") 4 5
    );
    (4,
      let* _ := Instr.Store (Register.read "t0") (Register.read "t13") in
      Instr.Jump 1
    );
    (5,
      let* "t15" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t16" := Instr.IndexAddr (Register.read "t15") TODO_constant in
      let* "t17" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t16") (Register.read "t17") in
      let* "t18" := Instr.Slice (Register.read "t15") None None in
      let* "t19" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t18")] in
      let* "t20" := Instr.MakeInterface (Register.read "t19") in
      Instr.Panic (Register.read "t20")
    );
    (6,
      let* "t21" := Instr.Phi (* i *) [TODO_constant; (Register.read "t32")] in
      let* "t22" := Instr.Phi (* rangeindex *) [TODO_constant; (Register.read "t23")] in
      let* "t23" := Instr.BinOp (Register.read "t22") "+" TODO_constant in
      let* "t24" := Instr.BinOp (Register.read "t23") "<" (Register.read "t10") in
      Instr.If (Register.read "t24") 7 12
    );
    (7,
      let* "t25" := Instr.IndexAddr (Register.read "t6") (Register.read "t23") in
      let* "t26" := Instr.UnOp "*" (Register.read "t25") in
      Instr.Jump 9
    );
    (8,
      let* "t27" := Instr.Convert (Register.read "t33") in
      let* "t28" := Instr.IndexAddr (Register.read "t9") (Register.read "t32") in
      let* _ := Instr.Store (Register.read "t28") (Register.read "t27") in
      let* "t29" := Instr.BinOp (Register.read "t33") ">>" TODO_constant in
      let* "t30" := Instr.BinOp (Register.read "t32") "+" TODO_constant in
      let* "t31" := Instr.BinOp (Register.read "t34") "+" TODO_constant in
      Instr.Jump 9
    );
    (9,
      let* "t32" := Instr.Phi (* i *) [(Register.read "t21"); (Register.read "t30")] in
      let* "t33" := Instr.Phi (* w *) [(Register.read "t26"); (Register.read "t29")] in
      let* "t34" := Instr.Phi (* j *) [TODO_constant; (Register.read "t31")] in
      let* "t35" := Instr.BinOp (Register.read "t34") "<" TODO_constant in
      Instr.If (Register.read "t35") 8 6
    );
    (10,
      let* "t36" := Instr.BinOp (Register.read "t38") "-" TODO_constant in
      Instr.Jump 12
    );
    (11,
      let* "t37" := Instr.Slice (Register.read "t9") None (Some (Register.read "t38")) in
      M.Return [(Register.read "t37")]
    );
    (12,
      let* "t38" := Instr.Phi (* i *) [(Register.read "t21"); (Register.read "t36")] in
      let* "t39" := Instr.BinOp (Register.read "t38") ">" TODO_constant in
      Instr.If (Register.read "t39") 13 11
    );
    (13,
      let* "t40" := Instr.BinOp (Register.read "t38") "-" TODO_constant in
      let* "t41" := Instr.IndexAddr (Register.read "t9") (Register.read "t40") in
      let* "t42" := Instr.UnOp "*" (Register.read "t41") in
      let* "t43" := Instr.BinOp (Register.read "t42") "==" TODO_constant in
      Instr.If (Register.read "t43") 10 11
    )]
  | _ => []
  end)

with Compare : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x_; op; y_] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function _'match) [x_; y_] in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      let* "t3" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 2 3
    );
    (1,
      let* "t6" := Instr.Alloc (* varargs *) Alloc.Heap "*[3]any" in
      let* "t7" := Instr.IndexAddr (Register.read "t6") TODO_constant in
      let* "t8" := Instr.ChangeInterface x_ in
      let* _ := Instr.Store (Register.read "t7") (Register.read "t8") in
      let* "t9" := Instr.IndexAddr (Register.read "t6") TODO_constant in
      let* "t10" := Instr.MakeInterface op in
      let* _ := Instr.Store (Register.read "t9") (Register.read "t10") in
      let* "t11" := Instr.IndexAddr (Register.read "t6") TODO_constant in
      let* "t12" := Instr.ChangeInterface y_ in
      let* _ := Instr.Store (Register.read "t11") (Register.read "t12") in
      let* "t13" := Instr.Slice (Register.read "t6") None None in
      let* "t14" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t13")] in
      let* "t15" := Instr.MakeInterface (Register.read "t14") in
      Instr.Panic (Register.read "t15")
    );
    (2,
      M.Return [TODO_constant]
    );
    (3,
      let* "t16" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t17" := Instr.Extract (Register.read "t16") 0 in
      let* "t18" := Instr.Extract (Register.read "t16") 1 in
      Instr.If (Register.read "t18") 4 5
    );
    (4,
      let* "t19" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.boolVal" in
      let* "t20" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t20") 6 8
    );
    (5,
      let* "t21" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t22" := Instr.Extract (Register.read "t21") 0 in
      let* "t23" := Instr.Extract (Register.read "t21") 1 in
      Instr.If (Register.read "t23") 9 10
    );
    (6,
      let* "t24" := Instr.BinOp (Register.read "t17") "==" (Register.read "t19") in
      M.Return [(Register.read "t24")]
    );
    (7,
      let* "t25" := Instr.BinOp (Register.read "t17") "!=" (Register.read "t19") in
      M.Return [(Register.read "t25")]
    );
    (8,
      let* "t26" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t26") 7 1
    );
    (9,
      let* "t27" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.int64Val" in
      let* "t28" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t28") 11 13
    );
    (10,
      let* "t29" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.intVal" in
      let* "t30" := Instr.Extract (Register.read "t29") 0 in
      let* "t31" := Instr.Extract (Register.read "t29") 1 in
      Instr.If (Register.read "t31") 22 23
    );
    (11,
      let* "t32" := Instr.BinOp (Register.read "t22") "==" (Register.read "t27") in
      M.Return [(Register.read "t32")]
    );
    (12,
      let* "t33" := Instr.BinOp (Register.read "t22") "!=" (Register.read "t27") in
      M.Return [(Register.read "t33")]
    );
    (13,
      let* "t34" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t34") 12 15
    );
    (14,
      let* "t35" := Instr.BinOp (Register.read "t22") "<" (Register.read "t27") in
      M.Return [(Register.read "t35")]
    );
    (15,
      let* "t36" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t36") 14 17
    );
    (16,
      let* "t37" := Instr.BinOp (Register.read "t22") "<=" (Register.read "t27") in
      M.Return [(Register.read "t37")]
    );
    (17,
      let* "t38" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t38") 16 19
    );
    (18,
      let* "t39" := Instr.BinOp (Register.read "t22") ">" (Register.read "t27") in
      M.Return [(Register.read "t39")]
    );
    (19,
      let* "t40" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t40") 18 21
    );
    (20,
      let* "t41" := Instr.BinOp (Register.read "t22") ">=" (Register.read "t27") in
      M.Return [(Register.read "t41")]
    );
    (21,
      let* "t42" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t42") 20 1
    );
    (22,
      let* "t43" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t43") (Register.read "t30") in
      let* "t44" := Instr.FieldAddr (Register.read "t43") 0 in
      let* "t45" := Instr.UnOp "*" (Register.read "t44") in
      let* "t46" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.intVal" in
      let* "t47" := Instr.Field (Register.read "t46") 0 in
      let* "t48" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t45"); (Register.read "t47")] in
      let* "t49" := Instr.Call (CallKind.Function cmpZero) [(Register.read "t48"); op] in
      M.Return [(Register.read "t49")]
    );
    (23,
      let* "t50" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t51" := Instr.Extract (Register.read "t50") 0 in
      let* "t52" := Instr.Extract (Register.read "t50") 1 in
      Instr.If (Register.read "t52") 24 25
    );
    (24,
      let* "t53" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t53") (Register.read "t51") in
      let* "t54" := Instr.FieldAddr (Register.read "t53") 0 in
      let* "t55" := Instr.UnOp "*" (Register.read "t54") in
      let* "t56" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.ratVal" in
      let* "t57" := Instr.Field (Register.read "t56") 0 in
      let* "t58" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t55"); (Register.read "t57")] in
      let* "t59" := Instr.Call (CallKind.Function cmpZero) [(Register.read "t58"); op] in
      M.Return [(Register.read "t59")]
    );
    (25,
      let* "t60" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t61" := Instr.Extract (Register.read "t60") 0 in
      let* "t62" := Instr.Extract (Register.read "t60") 1 in
      Instr.If (Register.read "t62") 26 27
    );
    (26,
      let* "t63" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t63") (Register.read "t61") in
      let* "t64" := Instr.FieldAddr (Register.read "t63") 0 in
      let* "t65" := Instr.UnOp "*" (Register.read "t64") in
      let* "t66" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.floatVal" in
      let* "t67" := Instr.Field (Register.read "t66") 0 in
      let* "t68" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t65"); (Register.read "t67")] in
      let* "t69" := Instr.Call (CallKind.Function cmpZero) [(Register.read "t68"); op] in
      M.Return [(Register.read "t69")]
    );
    (27,
      let* "t70" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t71" := Instr.Extract (Register.read "t70") 0 in
      let* "t72" := Instr.Extract (Register.read "t70") 1 in
      Instr.If (Register.read "t72") 28 29
    );
    (28,
      let* "t73" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t73") (Register.read "t71") in
      let* "t74" := Instr.Alloc (* y *) Alloc.Local "*go/constant.complexVal" in
      let* "t75" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t74") (Register.read "t75") in
      let* "t76" := Instr.FieldAddr (Register.read "t73") 0 in
      let* "t77" := Instr.UnOp "*" (Register.read "t76") in
      let* "t78" := Instr.FieldAddr (Register.read "t74") 0 in
      let* "t79" := Instr.UnOp "*" (Register.read "t78") in
      let* "t80" := Instr.Call (CallKind.Function Compare) [(Register.read "t77"); TODO_constant; (Register.read "t79")] in
      let* "t81" := Instr.FieldAddr (Register.read "t73") 1 in
      let* "t82" := Instr.UnOp "*" (Register.read "t81") in
      let* "t83" := Instr.FieldAddr (Register.read "t74") 1 in
      let* "t84" := Instr.UnOp "*" (Register.read "t83") in
      let* "t85" := Instr.Call (CallKind.Function Compare) [(Register.read "t82"); TODO_constant; (Register.read "t84")] in
      let* "t86" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t86") 30 32
    );
    (29,
      let* "t87" := Instr.TypeAssert (Register.read "t1") TypeAssert.CommaOk "*go/constant.stringVal" in
      let* "t88" := Instr.Extract (Register.read "t87") 0 in
      let* "t89" := Instr.Extract (Register.read "t87") 1 in
      Instr.If (Register.read "t89") 37 1
    );
    (30,
      Instr.If (Register.read "t80") 33 34
    );
    (31,
      Instr.If (Register.read "t80") 35 36
    );
    (32,
      let* "t90" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t90") 31 1
    );
    (33,
      Instr.Jump 34
    );
    (34,
      let* "t91" := Instr.Phi (* && *) [TODO_constant; (Register.read "t85")] in
      M.Return [(Register.read "t91")]
    );
    (35,
      let* "t92" := Instr.UnOp "!" (Register.read "t85") in
      Instr.Jump 36
    );
    (36,
      let* "t93" := Instr.Phi (* || *) [TODO_constant; (Register.read "t92")] in
      M.Return [(Register.read "t93")]
    );
    (37,
      let* "t94" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t88")] in
      let* "t95" := Instr.TypeAssert (Register.read "t2") TypeAssert.NoCommaOk "*go/constant.stringVal" in
      let* "t96" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t95")] in
      let* "t97" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t97") 38 40
    );
    (38,
      let* "t98" := Instr.BinOp (Register.read "t94") "==" (Register.read "t96") in
      M.Return [(Register.read "t98")]
    );
    (39,
      let* "t99" := Instr.BinOp (Register.read "t94") "!=" (Register.read "t96") in
      M.Return [(Register.read "t99")]
    );
    (40,
      let* "t100" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t100") 39 42
    );
    (41,
      let* "t101" := Instr.BinOp (Register.read "t94") "<" (Register.read "t96") in
      M.Return [(Register.read "t101")]
    );
    (42,
      let* "t102" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t102") 41 44
    );
    (43,
      let* "t103" := Instr.BinOp (Register.read "t94") "<=" (Register.read "t96") in
      M.Return [(Register.read "t103")]
    );
    (44,
      let* "t104" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t104") 43 46
    );
    (45,
      let* "t105" := Instr.BinOp (Register.read "t94") ">" (Register.read "t96") in
      M.Return [(Register.read "t105")]
    );
    (46,
      let* "t106" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t106") 45 48
    );
    (47,
      let* "t107" := Instr.BinOp (Register.read "t94") ">=" (Register.read "t96") in
      M.Return [(Register.read "t107")]
    );
    (48,
      let* "t108" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t108") 47 1
    )]
  | _ => []
  end)

with Denom : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      let* "t3" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t4")]
    );
    (3,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 2 4
    );
    (4,
      let* "t8" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 5 6
    );
    (5,
      let* "t11" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t11") (Register.read "t9") in
      let* "t12" := Instr.FieldAddr (Register.read "t11") 0 in
      let* "t13" := Instr.UnOp "*" (Register.read "t12") in
      let* "t14" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t13")] in
      let* "t15" := Instr.Call (CallKind.Function makeInt) [(Register.read "t14")] in
      M.Return [(Register.read "t15")]
    );
    (6,
      let* "t16" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t17" := Instr.Extract (Register.read "t16") 0 in
      let* "t18" := Instr.Extract (Register.read "t16") 1 in
      Instr.If (Register.read "t18") 7 8
    );
    (7,
      let* "t19" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t19") (Register.read "t17") in
      let* "t20" := Instr.FieldAddr (Register.read "t19") 0 in
      let* "t21" := Instr.UnOp "*" (Register.read "t20") in
      let* "t22" := Instr.Call (CallKind.Function smallFloat) [(Register.read "t21")] in
      Instr.If (Register.read "t22") 9 1
    );
    (8,
      let* "t23" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t24" := Instr.Extract (Register.read "t23") 0 in
      let* "t25" := Instr.Extract (Register.read "t23") 1 in
      Instr.If (Register.read "t25") 10 11
    );
    (9,
      let* "t26" := Instr.FieldAddr (Register.read "t19") 0 in
      let* "t27" := Instr.UnOp "*" (Register.read "t26") in
      let* "t28" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t27"); TODO_constant] in
      let* "t29" := Instr.Extract (Register.read "t28") 0 in
      let* "t30" := Instr.Extract (Register.read "t28") 1 in
      let* "t31" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t29")] in
      let* "t32" := Instr.Call (CallKind.Function makeInt) [(Register.read "t31")] in
      M.Return [(Register.read "t32")]
    );
    (10,
      Instr.Jump 1
    );
    (11,
      let* "t33" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t34" := Instr.IndexAddr (Register.read "t33") TODO_constant in
      let* "t35" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t34") (Register.read "t35") in
      let* "t36" := Instr.Slice (Register.read "t33") None None in
      let* "t37" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t36")] in
      let* "t38" := Instr.MakeInterface (Register.read "t37") in
      Instr.Panic (Register.read "t38")
    )]
  | _ => []
  end)

with Float32Val : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.Convert (Register.read "t1") in
      let* "t4" := Instr.Convert (Register.read "t3") in
      let* "t5" := Instr.BinOp (Register.read "t4") "==" (Register.read "t1") in
      M.Return [(Register.read "t3"); (Register.read "t5")]
    );
    (2,
      let* "t6" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t7" := Instr.Extract (Register.read "t6") 0 in
      let* "t8" := Instr.Extract (Register.read "t6") 1 in
      Instr.If (Register.read "t8") 3 4
    );
    (3,
      let* "t9" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t9") (Register.read "t7") in
      let* "t10" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t11" := Instr.FieldAddr (Register.read "t9") 0 in
      let* "t12" := Instr.UnOp "*" (Register.read "t11") in
      let* "t13" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t10"); (Register.read "t12")] in
      let* "t14" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t13")] in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      let* "t17" := Instr.BinOp (Register.read "t16") "==" TODO_constant in
      M.Return [(Register.read "t15"); (Register.read "t17")]
    );
    (4,
      let* "t18" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t19" := Instr.Extract (Register.read "t18") 0 in
      let* "t20" := Instr.Extract (Register.read "t18") 1 in
      Instr.If (Register.read "t20") 5 6
    );
    (5,
      let* "t21" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t21") (Register.read "t19") in
      let* "t22" := Instr.FieldAddr (Register.read "t21") 0 in
      let* "t23" := Instr.UnOp "*" (Register.read "t22") in
      let* "t24" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t23")] in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      M.Return [(Register.read "t25"); (Register.read "t26")]
    );
    (6,
      let* "t27" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t28" := Instr.Extract (Register.read "t27") 0 in
      let* "t29" := Instr.Extract (Register.read "t27") 1 in
      Instr.If (Register.read "t29") 7 8
    );
    (7,
      let* "t30" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t30") (Register.read "t28") in
      let* "t31" := Instr.FieldAddr (Register.read "t30") 0 in
      let* "t32" := Instr.UnOp "*" (Register.read "t31") in
      let* "t33" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t32")] in
      let* "t34" := Instr.Extract (Register.read "t33") 0 in
      let* "t35" := Instr.Extract (Register.read "t33") 1 in
      let* "t36" := Instr.BinOp (Register.read "t35") "==" TODO_constant in
      M.Return [(Register.read "t34"); (Register.read "t36")]
    );
    (8,
      let* "t37" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t38" := Instr.Extract (Register.read "t37") 0 in
      let* "t39" := Instr.Extract (Register.read "t37") 1 in
      Instr.If (Register.read "t39") 9 10
    );
    (9,
      M.Return [TODO_constant; TODO_constant]
    );
    (10,
      let* "t40" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t41" := Instr.IndexAddr (Register.read "t40") TODO_constant in
      let* "t42" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t41") (Register.read "t42") in
      let* "t43" := Instr.Slice (Register.read "t40") None None in
      let* "t44" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t43")] in
      let* "t45" := Instr.MakeInterface (Register.read "t44") in
      Instr.Panic (Register.read "t45")
    )]
  | _ => []
  end)

with Float64Val : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.ChangeType (Register.read "t1") in
      let* "t4" := Instr.Convert (Register.read "t3") in
      let* "t5" := Instr.Convert (Register.read "t4") in
      let* "t6" := Instr.BinOp (Register.read "t5") "==" (Register.read "t1") in
      M.Return [(Register.read "t4"); (Register.read "t6")]
    );
    (2,
      let* "t7" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t8" := Instr.Extract (Register.read "t7") 0 in
      let* "t9" := Instr.Extract (Register.read "t7") 1 in
      Instr.If (Register.read "t9") 3 4
    );
    (3,
      let* "t10" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t10") (Register.read "t8") in
      let* "t11" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t12" := Instr.FieldAddr (Register.read "t10") 0 in
      let* "t13" := Instr.UnOp "*" (Register.read "t12") in
      let* "t14" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t11"); (Register.read "t13")] in
      let* "t15" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t14")] in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      let* "t18" := Instr.BinOp (Register.read "t17") "==" TODO_constant in
      M.Return [(Register.read "t16"); (Register.read "t18")]
    );
    (4,
      let* "t19" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t20" := Instr.Extract (Register.read "t19") 0 in
      let* "t21" := Instr.Extract (Register.read "t19") 1 in
      Instr.If (Register.read "t21") 5 6
    );
    (5,
      let* "t22" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t22") (Register.read "t20") in
      let* "t23" := Instr.FieldAddr (Register.read "t22") 0 in
      let* "t24" := Instr.UnOp "*" (Register.read "t23") in
      let* "t25" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t24")] in
      let* "t26" := Instr.Extract (Register.read "t25") 0 in
      let* "t27" := Instr.Extract (Register.read "t25") 1 in
      M.Return [(Register.read "t26"); (Register.read "t27")]
    );
    (6,
      let* "t28" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t29" := Instr.Extract (Register.read "t28") 0 in
      let* "t30" := Instr.Extract (Register.read "t28") 1 in
      Instr.If (Register.read "t30") 7 8
    );
    (7,
      let* "t31" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t31") (Register.read "t29") in
      let* "t32" := Instr.FieldAddr (Register.read "t31") 0 in
      let* "t33" := Instr.UnOp "*" (Register.read "t32") in
      let* "t34" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t33")] in
      let* "t35" := Instr.Extract (Register.read "t34") 0 in
      let* "t36" := Instr.Extract (Register.read "t34") 1 in
      let* "t37" := Instr.BinOp (Register.read "t36") "==" TODO_constant in
      M.Return [(Register.read "t35"); (Register.read "t37")]
    );
    (8,
      let* "t38" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t39" := Instr.Extract (Register.read "t38") 0 in
      let* "t40" := Instr.Extract (Register.read "t38") 1 in
      Instr.If (Register.read "t40") 9 10
    );
    (9,
      M.Return [TODO_constant; TODO_constant]
    );
    (10,
      let* "t41" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t42" := Instr.IndexAddr (Register.read "t41") TODO_constant in
      let* "t43" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t42") (Register.read "t43") in
      let* "t44" := Instr.Slice (Register.read "t41") None None in
      let* "t45" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t44")] in
      let* "t46" := Instr.MakeInterface (Register.read "t45") in
      Instr.Panic (Register.read "t46")
    )]
  | _ => []
  end)

with Imag : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.MakeInterface (Register.read "t1") in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 3 4
    );
    (3,
      let* "t7" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t7")]
    );
    (4,
      let* "t8" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 3 5
    );
    (5,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 3 6
    );
    (6,
      let* "t14" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 3 7
    );
    (7,
      let* "t17" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t18" := Instr.Extract (Register.read "t17") 0 in
      let* "t19" := Instr.Extract (Register.read "t17") 1 in
      Instr.If (Register.read "t19") 8 9
    );
    (8,
      let* "t20" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t20") (Register.read "t18") in
      let* "t21" := Instr.FieldAddr (Register.read "t20") 1 in
      let* "t22" := Instr.UnOp "*" (Register.read "t21") in
      M.Return [(Register.read "t22")]
    );
    (9,
      let* "t23" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t24" := Instr.IndexAddr (Register.read "t23") TODO_constant in
      let* "t25" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t24") (Register.read "t25") in
      let* "t26" := Instr.Slice (Register.read "t23") None None in
      let* "t27" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t26")] in
      let* "t28" := Instr.MakeInterface (Register.read "t27") in
      Instr.Panic (Register.read "t28")
    )]
  | _ => []
  end)

with Int64Val : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.ChangeType (Register.read "t1") in
      M.Return [(Register.read "t3"); TODO_constant]
    );
    (2,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 3 4
    );
    (3,
      let* "t7" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t7") (Register.read "t5") in
      let* "t8" := Instr.FieldAddr (Register.read "t7") 0 in
      let* "t9" := Instr.UnOp "*" (Register.read "t8") in
      let* "t10" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t9")] in
      M.Return [(Register.read "t10"); TODO_constant]
    );
    (4,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 5 6
    );
    (5,
      M.Return [TODO_constant; TODO_constant]
    );
    (6,
      let* "t14" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t15" := Instr.IndexAddr (Register.read "t14") TODO_constant in
      let* "t16" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t15") (Register.read "t16") in
      let* "t17" := Instr.Slice (Register.read "t14") None None in
      let* "t18" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t17")] in
      let* "t19" := Instr.MakeInterface (Register.read "t18") in
      Instr.Panic (Register.read "t19")
    )]
  | _ => []
  end)

with Make : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "bool" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.ChangeType (Register.read "t1") in
      let* "t4" := Instr.MakeInterface (Register.read "t3") in
      M.Return [(Register.read "t4")]
    );
    (2,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "string" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 3 4
    );
    (3,
      let* "t8" := Instr.Alloc (* complit *) Alloc.Heap "*go/constant.stringVal" in
      let* "t9" := Instr.FieldAddr (Register.read "t8") 1 in
      let* _ := Instr.Store (Register.read "t9") (Register.read "t6") in
      let* "t10" := Instr.MakeInterface (Register.read "t8") in
      M.Return [(Register.read "t10")]
    );
    (4,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "int64" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 5 6
    );
    (5,
      let* "t14" := Instr.ChangeType (Register.read "t12") in
      let* "t15" := Instr.MakeInterface (Register.read "t14") in
      M.Return [(Register.read "t15")]
    );
    (6,
      let* "t16" := Instr.TypeAssert x TypeAssert.CommaOk "*math/big.Int" in
      let* "t17" := Instr.Extract (Register.read "t16") 0 in
      let* "t18" := Instr.Extract (Register.read "t16") 1 in
      Instr.If (Register.read "t18") 7 8
    );
    (7,
      let* "t19" := Instr.Call (CallKind.Function makeInt) [(Register.read "t17")] in
      M.Return [(Register.read "t19")]
    );
    (8,
      let* "t20" := Instr.TypeAssert x TypeAssert.CommaOk "*math/big.Rat" in
      let* "t21" := Instr.Extract (Register.read "t20") 0 in
      let* "t22" := Instr.Extract (Register.read "t20") 1 in
      Instr.If (Register.read "t22") 9 10
    );
    (9,
      let* "t23" := Instr.Call (CallKind.Function makeRat) [(Register.read "t21")] in
      M.Return [(Register.read "t23")]
    );
    (10,
      let* "t24" := Instr.TypeAssert x TypeAssert.CommaOk "*math/big.Float" in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      Instr.If (Register.read "t26") 11 12
    );
    (11,
      let* "t27" := Instr.Call (CallKind.Function makeFloat) [(Register.read "t25")] in
      M.Return [(Register.read "t27")]
    );
    (12,
      let* "t28" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t28")]
    )]
  | _ => []
  end)

with MakeBool : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [b] =>
    [(0,
      let* "t0" := Instr.ChangeType b in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      M.Return [(Register.read "t1")]
    )]
  | _ => []
  end)

with MakeFloat64 : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function math.IsInf) [x; TODO_constant] in
      Instr.If (Register.read "t0") 1 3
    );
    (1,
      let* "t1" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t1")]
    );
    (2,
      let* "t2" := Instr.Call (CallKind.Function smallFloat64) [x] in
      Instr.If (Register.read "t2") 4 5
    );
    (3,
      let* "t3" := Instr.Call (CallKind.Function math.IsNaN) [x] in
      Instr.If (Register.read "t3") 1 2
    );
    (4,
      let* "t4" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.ratVal" in
      let* "t5" := Instr.FieldAddr (Register.read "t4") 0 in
      let* "t6" := Instr.Call (CallKind.Function newRat) [] in
      let* "t7" := Instr.BinOp x "+" TODO_constant in
      let* "t8" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t6"); (Register.read "t7")] in
      let* _ := Instr.Store (Register.read "t5") (Register.read "t8") in
      let* "t9" := Instr.UnOp "*" (Register.read "t4") in
      let* "t10" := Instr.MakeInterface (Register.read "t9") in
      M.Return [(Register.read "t10")]
    );
    (5,
      let* "t11" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t12" := Instr.FieldAddr (Register.read "t11") 0 in
      let* "t13" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t14" := Instr.BinOp x "+" TODO_constant in
      let* "t15" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t13"); (Register.read "t14")] in
      let* _ := Instr.Store (Register.read "t12") (Register.read "t15") in
      let* "t16" := Instr.UnOp "*" (Register.read "t11") in
      let* "t17" := Instr.MakeInterface (Register.read "t16") in
      M.Return [(Register.read "t17")]
    )]
  | _ => []
  end)

with MakeFromBytes : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [bytes] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function len) [bytes] in
      let* "t1" := Instr.BinOp (Register.read "t0") "+" TODO_constant in
      let* "t2" := Instr.BinOp (Register.read "t1") "/" TODO_constant in
      let* "t3" := Instr.MakeSlice (Register.read "t2") (Register.read "t2") in
      let* "t4" := Instr.Call (CallKind.Function len) [bytes] in
      Instr.Jump 1
    );
    (1,
      let* "t5" := Instr.Phi (* i *) [TODO_constant; (Register.read "t5"); (Register.read "t21")] in
      let* "t6" := Instr.Phi (* w *) [TODO_constant; (Register.read "t15"); TODO_constant] in
      let* "t7" := Instr.Phi (* s *) [TODO_constant; (Register.read "t16"); TODO_constant] in
      let* "t8" := Instr.Phi (* rangeindex *) [TODO_constant; (Register.read "t9"); (Register.read "t9")] in
      let* "t9" := Instr.BinOp (Register.read "t8") "+" TODO_constant in
      let* "t10" := Instr.BinOp (Register.read "t9") "<" (Register.read "t4") in
      Instr.If (Register.read "t10") 2 3
    );
    (2,
      let* "t11" := Instr.IndexAddr bytes (Register.read "t9") in
      let* "t12" := Instr.UnOp "*" (Register.read "t11") in
      let* "t13" := Instr.Convert (Register.read "t12") in
      let* "t14" := Instr.BinOp (Register.read "t13") "<<" (Register.read "t7") in
      let* "t15" := Instr.BinOp (Register.read "t6") "|" (Register.read "t14") in
      let* "t16" := Instr.BinOp (Register.read "t7") "+" TODO_constant in
      let* "t17" := Instr.BinOp (Register.read "t16") "==" TODO_constant in
      Instr.If (Register.read "t17") 4 1
    );
    (3,
      let* "t18" := Instr.Call (CallKind.Function len) [(Register.read "t3")] in
      let* "t19" := Instr.BinOp (Register.read "t5") "<" (Register.read "t18") in
      Instr.If (Register.read "t19") 5 8
    );
    (4,
      let* "t20" := Instr.IndexAddr (Register.read "t3") (Register.read "t5") in
      let* _ := Instr.Store (Register.read "t20") (Register.read "t15") in
      let* "t21" := Instr.BinOp (Register.read "t5") "+" TODO_constant in
      Instr.Jump 1
    );
    (5,
      let* "t22" := Instr.IndexAddr (Register.read "t3") (Register.read "t5") in
      let* _ := Instr.Store (Register.read "t22") (Register.read "t6") in
      let* "t23" := Instr.BinOp (Register.read "t5") "+" TODO_constant in
      Instr.Jump 8
    );
    (6,
      let* "t24" := Instr.BinOp (Register.read "t29") "-" TODO_constant in
      Instr.Jump 8
    );
    (7,
      let* "t25" := Instr.Call (CallKind.Function newInt) [] in
      let* "t26" := Instr.Slice (Register.read "t3") None (Some (Register.read "t29")) in
      let* "t27" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t25"); (Register.read "t26")] in
      let* "t28" := Instr.Call (CallKind.Function makeInt) [(Register.read "t27")] in
      M.Return [(Register.read "t28")]
    );
    (8,
      let* "t29" := Instr.Phi (* i *) [(Register.read "t5"); (Register.read "t24"); (Register.read "t23")] in
      let* "t30" := Instr.BinOp (Register.read "t29") ">" TODO_constant in
      Instr.If (Register.read "t30") 9 7
    );
    (9,
      let* "t31" := Instr.BinOp (Register.read "t29") "-" TODO_constant in
      let* "t32" := Instr.IndexAddr (Register.read "t3") (Register.read "t31") in
      let* "t33" := Instr.UnOp "*" (Register.read "t32") in
      let* "t34" := Instr.BinOp (Register.read "t33") "==" TODO_constant in
      Instr.If (Register.read "t34") 6 7
    )]
  | _ => []
  end)

with MakeFromLiteral : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [lit; tok; zero] =>
    [(0,
      let* "t0" := Instr.BinOp zero "!=" TODO_constant in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.MakeInterface TODO_constant in
      Instr.Panic (Register.read "t1")
    );
    (2,
      let* "t2" := Instr.BinOp tok "==" TODO_constant in
      Instr.If (Register.read "t2") 4 6
    );
    (3,
      let* "t3" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t3")]
    );
    (4,
      let* "t4" := Instr.Call (CallKind.Function strconv.ParseInt) [lit; TODO_constant; TODO_constant] in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      let* "t7" := Instr.BinOp (Register.read "t6") "==" TODO_constant in
      Instr.If (Register.read "t7") 7 8
    );
    (5,
      let* "t8" := Instr.Call (CallKind.Function makeFloatFromLiteral) [lit] in
      let* "t9" := Instr.BinOp (Register.read "t8") "!=" TODO_constant in
      Instr.If (Register.read "t9") 12 3
    );
    (6,
      let* "t10" := Instr.BinOp tok "==" TODO_constant in
      Instr.If (Register.read "t10") 5 11
    );
    (7,
      let* "t11" := Instr.ChangeType (Register.read "t5") in
      let* "t12" := Instr.MakeInterface (Register.read "t11") in
      M.Return [(Register.read "t12")]
    );
    (8,
      let* "t13" := Instr.Call (CallKind.Function newInt) [] in
      let* "t14" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t13"); lit; TODO_constant] in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 9 3
    );
    (9,
      let* "t17" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.intVal" in
      let* "t18" := Instr.FieldAddr (Register.read "t17") 0 in
      let* _ := Instr.Store (Register.read "t18") (Register.read "t15") in
      let* "t19" := Instr.UnOp "*" (Register.read "t17") in
      let* "t20" := Instr.MakeInterface (Register.read "t19") in
      M.Return [(Register.read "t20")]
    );
    (10,
      let* "t21" := Instr.Call (CallKind.Function len) [lit] in
      let* "t22" := Instr.BinOp (Register.read "t21") ">" TODO_constant in
      Instr.If (Register.read "t22") 16 3
    );
    (11,
      let* "t23" := Instr.BinOp tok "==" TODO_constant in
      Instr.If (Register.read "t23") 10 14
    );
    (12,
      M.Return [(Register.read "t8")]
    );
    (13,
      let* "t24" := Instr.Call (CallKind.Function len) [lit] in
      let* "t25" := Instr.BinOp (Register.read "t24") ">=" TODO_constant in
      Instr.If (Register.read "t25") 20 3
    );
    (14,
      let* "t26" := Instr.BinOp tok "==" TODO_constant in
      Instr.If (Register.read "t26") 13 19
    );
    (15,
      let* "t27" := Instr.BinOp (Register.read "t21") "-" TODO_constant in
      let* "t28" := Instr.Slice lit None (Some (Register.read "t27")) in
      let* "t29" := Instr.Call (CallKind.Function makeFloatFromLiteral) [(Register.read "t28")] in
      let* "t30" := Instr.BinOp (Register.read "t29") "!=" TODO_constant in
      Instr.If (Register.read "t30") 17 3
    );
    (16,
      let* "t31" := Instr.BinOp (Register.read "t21") "-" TODO_constant in
      let* "t32" := Instr.Index lit (Register.read "t31") in
      let* "t33" := Instr.BinOp (Register.read "t32") "==" TODO_constant in
      Instr.If (Register.read "t33") 15 3
    );
    (17,
      let* "t34" := Instr.MakeInterface TODO_constant in
      let* "t35" := Instr.Call (CallKind.Function makeComplex) [(Register.read "t34"); (Register.read "t29")] in
      M.Return [(Register.read "t35")]
    );
    (18,
      let* "t36" := Instr.Call (CallKind.Function strconv.Unquote) [lit] in
      let* "t37" := Instr.Extract (Register.read "t36") 0 in
      let* "t38" := Instr.Extract (Register.read "t36") 1 in
      let* "t39" := Instr.BinOp (Register.read "t38") "==" TODO_constant in
      Instr.If (Register.read "t39") 23 3
    );
    (19,
      let* "t40" := Instr.BinOp tok "==" TODO_constant in
      Instr.If (Register.read "t40") 18 22
    );
    (20,
      let* "t41" := Instr.BinOp (Register.read "t24") "-" TODO_constant in
      let* "t42" := Instr.Slice lit (Some TODO_constant) (Some (Register.read "t41")) in
      let* "t43" := Instr.Call (CallKind.Function strconv.UnquoteChar) [(Register.read "t42"); TODO_constant] in
      let* "t44" := Instr.Extract (Register.read "t43") 0 in
      let* "t45" := Instr.Extract (Register.read "t43") 1 in
      let* "t46" := Instr.Extract (Register.read "t43") 2 in
      let* "t47" := Instr.Extract (Register.read "t43") 3 in
      let* "t48" := Instr.BinOp (Register.read "t47") "==" TODO_constant in
      Instr.If (Register.read "t48") 21 3
    );
    (21,
      let* "t49" := Instr.Convert (Register.read "t44") in
      let* "t50" := Instr.Call (CallKind.Function MakeInt64) [(Register.read "t49")] in
      M.Return [(Register.read "t50")]
    );
    (22,
      let* "t51" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t52" := Instr.IndexAddr (Register.read "t51") TODO_constant in
      let* "t53" := Instr.MakeInterface tok in
      let* _ := Instr.Store (Register.read "t52") (Register.read "t53") in
      let* "t54" := Instr.Slice (Register.read "t51") None None in
      let* "t55" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t54")] in
      let* "t56" := Instr.MakeInterface (Register.read "t55") in
      Instr.Panic (Register.read "t56")
    );
    (23,
      let* "t57" := Instr.Call (CallKind.Function MakeString) [(Register.read "t37")] in
      M.Return [(Register.read "t57")]
    )]
  | _ => []
  end)

with MakeImag : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      M.Return [x]
    );
    (2,
      let* "t3" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 3 4
    );
    (3,
      let* "t6" := Instr.MakeInterface TODO_constant in
      let* "t7" := Instr.Call (CallKind.Function makeComplex) [(Register.read "t6"); x] in
      M.Return [(Register.read "t7")]
    );
    (4,
      let* "t8" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 3 5
    );
    (5,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 3 6
    );
    (6,
      let* "t14" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 3 7
    );
    (7,
      let* "t17" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t18" := Instr.IndexAddr (Register.read "t17") TODO_constant in
      let* "t19" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t18") (Register.read "t19") in
      let* "t20" := Instr.Slice (Register.read "t17") None None in
      let* "t21" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t20")] in
      let* "t22" := Instr.MakeInterface (Register.read "t21") in
      Instr.Panic (Register.read "t22")
    )]
  | _ => []
  end)

with MakeInt64 : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.ChangeType x in
      let* "t1" := Instr.MakeInterface (Register.read "t0") in
      M.Return [(Register.read "t1")]
    )]
  | _ => []
  end)

with MakeString : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [s] =>
    [(0,
      let* "t0" := Instr.BinOp s "==" TODO_constant in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.MakeInterface (Register.read "emptyString") in
      M.Return [(Register.read "t1")]
    );
    (2,
      let* "t2" := Instr.Alloc (* complit *) Alloc.Heap "*go/constant.stringVal" in
      let* "t3" := Instr.FieldAddr (Register.read "t2") 1 in
      let* _ := Instr.Store (Register.read "t3") s in
      let* "t4" := Instr.MakeInterface (Register.read "t2") in
      M.Return [(Register.read "t4")]
    )]
  | _ => []
  end)

with MakeUint64 : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.BinOp x "<" TODO_constant in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.Convert x in
      let* "t2" := Instr.ChangeType (Register.read "t1") in
      let* "t3" := Instr.MakeInterface (Register.read "t2") in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.intVal" in
      let* "t5" := Instr.FieldAddr (Register.read "t4") 0 in
      let* "t6" := Instr.Call (CallKind.Function newInt) [] in
      let* "t7" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t6"); x] in
      let* _ := Instr.Store (Register.read "t5") (Register.read "t7") in
      let* "t8" := Instr.UnOp "*" (Register.read "t4") in
      let* "t9" := Instr.MakeInterface (Register.read "t8") in
      M.Return [(Register.read "t9")]
    )]
  | _ => []
  end)

with MakeUnknown : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [] =>
    [(0,
      let* "t0" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with Num : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      let* "t3" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t3")]
    );
    (2,
      M.Return [x]
    );
    (3,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 2 4
    );
    (4,
      let* "t7" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t8" := Instr.Extract (Register.read "t7") 0 in
      let* "t9" := Instr.Extract (Register.read "t7") 1 in
      Instr.If (Register.read "t9") 5 6
    );
    (5,
      let* "t10" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t10") (Register.read "t8") in
      let* "t11" := Instr.FieldAddr (Register.read "t10") 0 in
      let* "t12" := Instr.UnOp "*" (Register.read "t11") in
      let* "t13" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t12")] in
      let* "t14" := Instr.Call (CallKind.Function makeInt) [(Register.read "t13")] in
      M.Return [(Register.read "t14")]
    );
    (6,
      let* "t15" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      Instr.If (Register.read "t17") 7 8
    );
    (7,
      let* "t18" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t18") (Register.read "t16") in
      let* "t19" := Instr.FieldAddr (Register.read "t18") 0 in
      let* "t20" := Instr.UnOp "*" (Register.read "t19") in
      let* "t21" := Instr.Call (CallKind.Function smallFloat) [(Register.read "t20")] in
      Instr.If (Register.read "t21") 9 1
    );
    (8,
      let* "t22" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t23" := Instr.Extract (Register.read "t22") 0 in
      let* "t24" := Instr.Extract (Register.read "t22") 1 in
      Instr.If (Register.read "t24") 10 11
    );
    (9,
      let* "t25" := Instr.FieldAddr (Register.read "t18") 0 in
      let* "t26" := Instr.UnOp "*" (Register.read "t25") in
      let* "t27" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t26"); TODO_constant] in
      let* "t28" := Instr.Extract (Register.read "t27") 0 in
      let* "t29" := Instr.Extract (Register.read "t27") 1 in
      let* "t30" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t28")] in
      let* "t31" := Instr.Call (CallKind.Function makeInt) [(Register.read "t30")] in
      M.Return [(Register.read "t31")]
    );
    (10,
      Instr.Jump 1
    );
    (11,
      let* "t32" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t33" := Instr.IndexAddr (Register.read "t32") TODO_constant in
      let* "t34" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t33") (Register.read "t34") in
      let* "t35" := Instr.Slice (Register.read "t32") None None in
      let* "t36" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t35")] in
      let* "t37" := Instr.MakeInterface (Register.read "t36") in
      Instr.Panic (Register.read "t37")
    )]
  | _ => []
  end)

with Real : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      M.Return [x]
    );
    (2,
      let* "t3" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 1 3
    );
    (3,
      let* "t6" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t7" := Instr.Extract (Register.read "t6") 0 in
      let* "t8" := Instr.Extract (Register.read "t6") 1 in
      Instr.If (Register.read "t8") 1 4
    );
    (4,
      let* "t9" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t10" := Instr.Extract (Register.read "t9") 0 in
      let* "t11" := Instr.Extract (Register.read "t9") 1 in
      Instr.If (Register.read "t11") 1 5
    );
    (5,
      let* "t12" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t13" := Instr.Extract (Register.read "t12") 0 in
      let* "t14" := Instr.Extract (Register.read "t12") 1 in
      Instr.If (Register.read "t14") 1 6
    );
    (6,
      let* "t15" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      Instr.If (Register.read "t17") 7 8
    );
    (7,
      let* "t18" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t18") (Register.read "t16") in
      let* "t19" := Instr.FieldAddr (Register.read "t18") 0 in
      let* "t20" := Instr.UnOp "*" (Register.read "t19") in
      M.Return [(Register.read "t20")]
    );
    (8,
      let* "t21" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t22" := Instr.IndexAddr (Register.read "t21") TODO_constant in
      let* "t23" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t22") (Register.read "t23") in
      let* "t24" := Instr.Slice (Register.read "t21") None None in
      let* "t25" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t24")] in
      let* "t26" := Instr.MakeInterface (Register.read "t25") in
      Instr.Panic (Register.read "t26")
    )]
  | _ => []
  end)

with Shift : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; op; s] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      let* "t3" := Instr.Alloc (* varargs *) Alloc.Heap "*[3]any" in
      let* "t4" := Instr.IndexAddr (Register.read "t3") TODO_constant in
      let* "t5" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t4") (Register.read "t5") in
      let* "t6" := Instr.IndexAddr (Register.read "t3") TODO_constant in
      let* "t7" := Instr.MakeInterface op in
      let* _ := Instr.Store (Register.read "t6") (Register.read "t7") in
      let* "t8" := Instr.IndexAddr (Register.read "t3") TODO_constant in
      let* "t9" := Instr.MakeInterface s in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t9") in
      let* "t10" := Instr.Slice (Register.read "t3") None None in
      let* "t11" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t10")] in
      let* "t12" := Instr.MakeInterface (Register.read "t11") in
      Instr.Panic (Register.read "t12")
    );
    (2,
      let* "t13" := Instr.MakeInterface (Register.read "t1") in
      M.Return [(Register.read "t13")]
    );
    (3,
      let* "t14" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 4 5
    );
    (4,
      let* "t17" := Instr.BinOp s "==" TODO_constant in
      Instr.If (Register.read "t17") 6 7
    );
    (5,
      let* "t18" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t19" := Instr.Extract (Register.read "t18") 0 in
      let* "t20" := Instr.Extract (Register.read "t18") 1 in
      Instr.If (Register.read "t20") 11 1
    );
    (6,
      let* "t21" := Instr.MakeInterface (Register.read "t15") in
      M.Return [(Register.read "t21")]
    );
    (7,
      let* "t22" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t22") 8 10
    );
    (8,
      let* "t23" := Instr.Call (CallKind.Function i64toi) [(Register.read "t15")] in
      let* "t24" := Instr.Field (Register.read "t23") 0 in
      let* "t25" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t24"); (Register.read "t24"); s] in
      let* "t26" := Instr.Call (CallKind.Function makeInt) [(Register.read "t25")] in
      M.Return [(Register.read "t26")]
    );
    (9,
      let* "t27" := Instr.BinOp (Register.read "t15") ">>" s in
      let* "t28" := Instr.MakeInterface (Register.read "t27") in
      M.Return [(Register.read "t28")]
    );
    (10,
      let* "t29" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t29") 9 1
    );
    (11,
      let* "t30" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t30") (Register.read "t19") in
      let* "t31" := Instr.BinOp s "==" TODO_constant in
      Instr.If (Register.read "t31") 12 13
    );
    (12,
      let* "t32" := Instr.UnOp "*" (Register.read "t30") in
      let* "t33" := Instr.MakeInterface (Register.read "t32") in
      M.Return [(Register.read "t33")]
    );
    (13,
      let* "t34" := Instr.Call (CallKind.Function newInt) [] in
      let* "t35" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t35") 14 16
    );
    (14,
      let* "t36" := Instr.FieldAddr (Register.read "t30") 0 in
      let* "t37" := Instr.UnOp "*" (Register.read "t36") in
      let* "t38" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t34"); (Register.read "t37"); s] in
      let* "t39" := Instr.Call (CallKind.Function makeInt) [(Register.read "t38")] in
      M.Return [(Register.read "t39")]
    );
    (15,
      let* "t40" := Instr.FieldAddr (Register.read "t30") 0 in
      let* "t41" := Instr.UnOp "*" (Register.read "t40") in
      let* "t42" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t34"); (Register.read "t41"); s] in
      let* "t43" := Instr.Call (CallKind.Function makeInt) [(Register.read "t42")] in
      M.Return [(Register.read "t43")]
    );
    (16,
      let* "t44" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t44") 15 1
    )]
  | _ => []
  end)

with Sign : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.BinOp (Register.read "t1") "<" TODO_constant in
      Instr.If (Register.read "t3") 3 5
    );
    (2,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 7 8
    );
    (3,
      M.Return [TODO_constant]
    );
    (4,
      M.Return [TODO_constant]
    );
    (5,
      let* "t7" := Instr.BinOp (Register.read "t1") ">" TODO_constant in
      Instr.If (Register.read "t7") 4 6
    );
    (6,
      M.Return [TODO_constant]
    );
    (7,
      let* "t8" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t5") in
      let* "t9" := Instr.FieldAddr (Register.read "t8") 0 in
      let* "t10" := Instr.UnOp "*" (Register.read "t9") in
      let* "t11" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t10")] in
      M.Return [(Register.read "t11")]
    );
    (8,
      let* "t12" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t13" := Instr.Extract (Register.read "t12") 0 in
      let* "t14" := Instr.Extract (Register.read "t12") 1 in
      Instr.If (Register.read "t14") 9 10
    );
    (9,
      let* "t15" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t15") (Register.read "t13") in
      let* "t16" := Instr.FieldAddr (Register.read "t15") 0 in
      let* "t17" := Instr.UnOp "*" (Register.read "t16") in
      let* "t18" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t17")] in
      M.Return [(Register.read "t18")]
    );
    (10,
      let* "t19" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t20" := Instr.Extract (Register.read "t19") 0 in
      let* "t21" := Instr.Extract (Register.read "t19") 1 in
      Instr.If (Register.read "t21") 11 12
    );
    (11,
      let* "t22" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t22") (Register.read "t20") in
      let* "t23" := Instr.FieldAddr (Register.read "t22") 0 in
      let* "t24" := Instr.UnOp "*" (Register.read "t23") in
      let* "t25" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t24")] in
      M.Return [(Register.read "t25")]
    );
    (12,
      let* "t26" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t27" := Instr.Extract (Register.read "t26") 0 in
      let* "t28" := Instr.Extract (Register.read "t26") 1 in
      Instr.If (Register.read "t28") 13 14
    );
    (13,
      let* "t29" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t29") (Register.read "t27") in
      let* "t30" := Instr.FieldAddr (Register.read "t29") 0 in
      let* "t31" := Instr.UnOp "*" (Register.read "t30") in
      let* "t32" := Instr.Call (CallKind.Function Sign) [(Register.read "t31")] in
      let* "t33" := Instr.FieldAddr (Register.read "t29") 1 in
      let* "t34" := Instr.UnOp "*" (Register.read "t33") in
      let* "t35" := Instr.Call (CallKind.Function Sign) [(Register.read "t34")] in
      let* "t36" := Instr.BinOp (Register.read "t32") "|" (Register.read "t35") in
      M.Return [(Register.read "t36")]
    );
    (14,
      let* "t37" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t38" := Instr.Extract (Register.read "t37") 0 in
      let* "t39" := Instr.Extract (Register.read "t37") 1 in
      Instr.If (Register.read "t39") 15 16
    );
    (15,
      M.Return [TODO_constant]
    );
    (16,
      let* "t40" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t41" := Instr.IndexAddr (Register.read "t40") TODO_constant in
      let* "t42" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t41") (Register.read "t42") in
      let* "t43" := Instr.Slice (Register.read "t40") None None in
      let* "t44" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t43")] in
      let* "t45" := Instr.MakeInterface (Register.read "t44") in
      Instr.Panic (Register.read "t45")
    )]
  | _ => []
  end)

with StringVal : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "*go/constant.stringVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t1")] in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 3 4
    );
    (3,
      M.Return [TODO_constant]
    );
    (4,
      let* "t7" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t8" := Instr.IndexAddr (Register.read "t7") TODO_constant in
      let* "t9" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t9") in
      let* "t10" := Instr.Slice (Register.read "t7") None None in
      let* "t11" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t10")] in
      let* "t12" := Instr.MakeInterface (Register.read "t11") in
      Instr.Panic (Register.read "t12")
    )]
  | _ => []
  end)

with ToComplex : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.Call (CallKind.Function vtoc) [x] in
      let* "t4" := Instr.MakeInterface (Register.read "t3") in
      M.Return [(Register.read "t4")]
    );
    (2,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 1 3
    );
    (3,
      let* "t8" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 1 4
    );
    (4,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 1 5
    );
    (5,
      let* "t14" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 6 7
    );
    (6,
      let* "t17" := Instr.MakeInterface (Register.read "t15") in
      M.Return [(Register.read "t17")]
    );
    (7,
      let* "t18" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t18")]
    )]
  | _ => []
  end)

with ToFloat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      let* "t3" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.Call (CallKind.Function i64tor) [(Register.read "t1")] in
      let* "t5" := Instr.MakeInterface (Register.read "t4") in
      M.Return [(Register.read "t5")]
    );
    (3,
      let* "t6" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t7" := Instr.Extract (Register.read "t6") 0 in
      let* "t8" := Instr.Extract (Register.read "t6") 1 in
      Instr.If (Register.read "t8") 4 5
    );
    (4,
      let* "t9" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t9") (Register.read "t7") in
      let* "t10" := Instr.FieldAddr (Register.read "t9") 0 in
      let* "t11" := Instr.UnOp "*" (Register.read "t10") in
      let* "t12" := Instr.Call (CallKind.Function smallInt) [(Register.read "t11")] in
      Instr.If (Register.read "t12") 6 7
    );
    (5,
      let* "t13" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t14" := Instr.Extract (Register.read "t13") 0 in
      let* "t15" := Instr.Extract (Register.read "t13") 1 in
      Instr.If (Register.read "t15") 8 9
    );
    (6,
      let* "t16" := Instr.UnOp "*" (Register.read "t9") in
      let* "t17" := Instr.Call (CallKind.Function itor) [(Register.read "t16")] in
      let* "t18" := Instr.MakeInterface (Register.read "t17") in
      M.Return [(Register.read "t18")]
    );
    (7,
      let* "t19" := Instr.UnOp "*" (Register.read "t9") in
      let* "t20" := Instr.Call (CallKind.Function itof) [(Register.read "t19")] in
      let* "t21" := Instr.MakeInterface (Register.read "t20") in
      M.Return [(Register.read "t21")]
    );
    (8,
      M.Return [x]
    );
    (9,
      let* "t22" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t23" := Instr.Extract (Register.read "t22") 0 in
      let* "t24" := Instr.Extract (Register.read "t22") 1 in
      Instr.If (Register.read "t24") 8 10
    );
    (10,
      let* "t25" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t26" := Instr.Extract (Register.read "t25") 0 in
      let* "t27" := Instr.Extract (Register.read "t25") 1 in
      Instr.If (Register.read "t27") 11 1
    );
    (11,
      let* "t28" := Instr.Alloc (* x *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t28") (Register.read "t26") in
      let* "t29" := Instr.FieldAddr (Register.read "t28") 1 in
      let* "t30" := Instr.UnOp "*" (Register.read "t29") in
      let* "t31" := Instr.Call (CallKind.Function Sign) [(Register.read "t30")] in
      let* "t32" := Instr.BinOp (Register.read "t31") "==" TODO_constant in
      Instr.If (Register.read "t32") 12 1
    );
    (12,
      let* "t33" := Instr.FieldAddr (Register.read "t28") 0 in
      let* "t34" := Instr.UnOp "*" (Register.read "t33") in
      let* "t35" := Instr.Call (CallKind.Function ToFloat) [(Register.read "t34")] in
      M.Return [(Register.read "t35")]
    )]
  | _ => []
  end)

with ToInt : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      let* "t3" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t3")]
    );
    (2,
      M.Return [x]
    );
    (3,
      let* "t4" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 2 4
    );
    (4,
      let* "t7" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t8" := Instr.Extract (Register.read "t7") 0 in
      let* "t9" := Instr.Extract (Register.read "t7") 1 in
      Instr.If (Register.read "t9") 5 6
    );
    (5,
      let* "t10" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t10") (Register.read "t8") in
      let* "t11" := Instr.FieldAddr (Register.read "t10") 0 in
      let* "t12" := Instr.UnOp "*" (Register.read "t11") in
      let* "t13" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t12")] in
      Instr.If (Register.read "t13") 7 1
    );
    (6,
      let* "t14" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 8 9
    );
    (7,
      let* "t17" := Instr.FieldAddr (Register.read "t10") 0 in
      let* "t18" := Instr.UnOp "*" (Register.read "t17") in
      let* "t19" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t18")] in
      let* "t20" := Instr.Call (CallKind.Function makeInt) [(Register.read "t19")] in
      M.Return [(Register.read "t20")]
    );
    (8,
      let* "t21" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t21") (Register.read "t15") in
      let* "t22" := Instr.FieldAddr (Register.read "t21") 0 in
      let* "t23" := Instr.UnOp "*" (Register.read "t22") in
      let* "t24" := Instr.Call (CallKind.Function smallFloat) [(Register.read "t23")] in
      Instr.If (Register.read "t24") 10 1
    );
    (9,
      let* "t25" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t26" := Instr.Extract (Register.read "t25") 0 in
      let* "t27" := Instr.Extract (Register.read "t25") 1 in
      Instr.If (Register.read "t27") 16 1
    );
    (10,
      let* "t28" := Instr.Call (CallKind.Function newInt) [] in
      let* "t29" := Instr.FieldAddr (Register.read "t21") 0 in
      let* "t30" := Instr.UnOp "*" (Register.read "t29") in
      let* "t31" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t30"); (Register.read "t28")] in
      let* "t32" := Instr.Extract (Register.read "t31") 0 in
      let* "t33" := Instr.Extract (Register.read "t31") 1 in
      let* "t34" := Instr.BinOp (Register.read "t33") "==" TODO_constant in
      Instr.If (Register.read "t34") 11 12
    );
    (11,
      let* "t35" := Instr.Call (CallKind.Function makeInt) [(Register.read "t28")] in
      M.Return [(Register.read "t35")]
    );
    (12,
      let* "t36" := Instr.Alloc (* t *) Alloc.Heap "*math/big.Float" in
      let* "t37" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); TODO_constant] in
      let* "t38" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); TODO_constant] in
      let* "t39" := Instr.FieldAddr (Register.read "t21") 0 in
      let* "t40" := Instr.UnOp "*" (Register.read "t39") in
      let* "t41" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); (Register.read "t40")] in
      let* "t42" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); (Register.read "t28")] in
      let* "t43" := Instr.Extract (Register.read "t42") 0 in
      let* "t44" := Instr.Extract (Register.read "t42") 1 in
      let* "t45" := Instr.BinOp (Register.read "t44") "==" TODO_constant in
      Instr.If (Register.read "t45") 13 14
    );
    (13,
      let* "t46" := Instr.Call (CallKind.Function makeInt) [(Register.read "t28")] in
      M.Return [(Register.read "t46")]
    );
    (14,
      let* "t47" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); TODO_constant] in
      let* "t48" := Instr.FieldAddr (Register.read "t21") 0 in
      let* "t49" := Instr.UnOp "*" (Register.read "t48") in
      let* "t50" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); (Register.read "t49")] in
      let* "t51" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t36"); (Register.read "t28")] in
      let* "t52" := Instr.Extract (Register.read "t51") 0 in
      let* "t53" := Instr.Extract (Register.read "t51") 1 in
      let* "t54" := Instr.BinOp (Register.read "t53") "==" TODO_constant in
      Instr.If (Register.read "t54") 15 1
    );
    (15,
      let* "t55" := Instr.Call (CallKind.Function makeInt) [(Register.read "t28")] in
      M.Return [(Register.read "t55")]
    );
    (16,
      let* "t56" := Instr.MakeInterface (Register.read "t26") in
      let* "t57" := Instr.Call (CallKind.Function ToFloat) [(Register.read "t56")] in
      let* "t58" := Instr.Call (CallKind.Method (Register.read "t57") "Kind") [] in
      let* "t59" := Instr.BinOp (Register.read "t58") "==" TODO_constant in
      Instr.If (Register.read "t59") 17 1
    );
    (17,
      let* "t60" := Instr.Call (CallKind.Function ToInt) [(Register.read "t57")] in
      M.Return [(Register.read "t60")]
    )]
  | _ => []
  end)

with Uint64Val : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.Convert (Register.read "t1") in
      let* "t4" := Instr.BinOp (Register.read "t1") ">=" TODO_constant in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    );
    (2,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 3 4
    );
    (3,
      let* "t8" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t6") in
      let* "t9" := Instr.FieldAddr (Register.read "t8") 0 in
      let* "t10" := Instr.UnOp "*" (Register.read "t9") in
      let* "t11" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t10")] in
      let* "t12" := Instr.FieldAddr (Register.read "t8") 0 in
      let* "t13" := Instr.UnOp "*" (Register.read "t12") in
      let* "t14" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t13")] in
      M.Return [(Register.read "t11"); (Register.read "t14")]
    );
    (4,
      let* "t15" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      Instr.If (Register.read "t17") 5 6
    );
    (5,
      M.Return [TODO_constant; TODO_constant]
    );
    (6,
      let* "t18" := Instr.Alloc (* varargs *) Alloc.Heap "*[1]any" in
      let* "t19" := Instr.IndexAddr (Register.read "t18") TODO_constant in
      let* "t20" := Instr.ChangeInterface x in
      let* _ := Instr.Store (Register.read "t19") (Register.read "t20") in
      let* "t21" := Instr.Slice (Register.read "t18") None None in
      let* "t22" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t21")] in
      let* "t23" := Instr.MakeInterface (Register.read "t22") in
      Instr.Panic (Register.read "t23")
    )]
  | _ => []
  end)

with UnaryOp : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [op; y; prec] =>
    [(0,
      let* "t0" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t0") 1 3
    );
    (1,
      let* "t1" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t2" := Instr.Extract (Register.read "t1") 0 in
      let* "t3" := Instr.Extract (Register.read "t1") 1 in
      Instr.If (Register.read "t3") 4 5
    );
    (2,
      let* "t4" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t5" := Instr.Extract (Register.read "t4") 0 in
      let* "t6" := Instr.Extract (Register.read "t4") 1 in
      Instr.If (Register.read "t6") 12 13
    );
    (3,
      let* "t7" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t7") 2 11
    );
    (4,
      M.Return [y]
    );
    (5,
      let* "t8" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.If (Register.read "t10") 4 6
    );
    (6,
      let* "t11" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.intVal" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 4 7
    );
    (7,
      let* "t14" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 4 8
    );
    (8,
      let* "t17" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t18" := Instr.Extract (Register.read "t17") 0 in
      let* "t19" := Instr.Extract (Register.read "t17") 1 in
      Instr.If (Register.read "t19") 4 9
    );
    (9,
      let* "t20" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t21" := Instr.Extract (Register.read "t20") 0 in
      let* "t22" := Instr.Extract (Register.read "t20") 1 in
      Instr.If (Register.read "t22") 4 34
    );
    (10,
      let* "t23" := Instr.Call (CallKind.Function newInt) [] in
      let* "t24" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      Instr.If (Register.read "t26") 28 29
    );
    (11,
      let* "t27" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t27") 10 26
    );
    (12,
      let* "t28" := Instr.MakeInterface (Register.read "t5") in
      M.Return [(Register.read "t28")]
    );
    (13,
      let* "t29" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t30" := Instr.Extract (Register.read "t29") 0 in
      let* "t31" := Instr.Extract (Register.read "t29") 1 in
      Instr.If (Register.read "t31") 14 15
    );
    (14,
      let* "t32" := Instr.UnOp "-" (Register.read "t30") in
      let* "t33" := Instr.BinOp (Register.read "t32") "!=" (Register.read "t30") in
      Instr.If (Register.read "t33") 16 17
    );
    (15,
      let* "t34" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.intVal" in
      let* "t35" := Instr.Extract (Register.read "t34") 0 in
      let* "t36" := Instr.Extract (Register.read "t34") 1 in
      Instr.If (Register.read "t36") 18 19
    );
    (16,
      let* "t37" := Instr.MakeInterface (Register.read "t32") in
      M.Return [(Register.read "t37")]
    );
    (17,
      let* "t38" := Instr.Call (CallKind.Function newInt) [] in
      let* "t39" := Instr.ChangeType (Register.read "t30") in
      let* "t40" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t39")] in
      let* "t41" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t38"); (Register.read "t40")] in
      let* "t42" := Instr.Call (CallKind.Function makeInt) [(Register.read "t41")] in
      M.Return [(Register.read "t42")]
    );
    (18,
      let* "t43" := Instr.Alloc (* y *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t43") (Register.read "t35") in
      let* "t44" := Instr.Call (CallKind.Function newInt) [] in
      let* "t45" := Instr.FieldAddr (Register.read "t43") 0 in
      let* "t46" := Instr.UnOp "*" (Register.read "t45") in
      let* "t47" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t44"); (Register.read "t46")] in
      let* "t48" := Instr.Call (CallKind.Function makeInt) [(Register.read "t47")] in
      M.Return [(Register.read "t48")]
    );
    (19,
      let* "t49" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t50" := Instr.Extract (Register.read "t49") 0 in
      let* "t51" := Instr.Extract (Register.read "t49") 1 in
      Instr.If (Register.read "t51") 20 21
    );
    (20,
      let* "t52" := Instr.Alloc (* y *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t52") (Register.read "t50") in
      let* "t53" := Instr.Call (CallKind.Function newRat) [] in
      let* "t54" := Instr.FieldAddr (Register.read "t52") 0 in
      let* "t55" := Instr.UnOp "*" (Register.read "t54") in
      let* "t56" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t53"); (Register.read "t55")] in
      let* "t57" := Instr.Call (CallKind.Function makeRat) [(Register.read "t56")] in
      M.Return [(Register.read "t57")]
    );
    (21,
      let* "t58" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t59" := Instr.Extract (Register.read "t58") 0 in
      let* "t60" := Instr.Extract (Register.read "t58") 1 in
      Instr.If (Register.read "t60") 22 23
    );
    (22,
      let* "t61" := Instr.Alloc (* y *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t61") (Register.read "t59") in
      let* "t62" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t63" := Instr.FieldAddr (Register.read "t61") 0 in
      let* "t64" := Instr.UnOp "*" (Register.read "t63") in
      let* "t65" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t62"); (Register.read "t64")] in
      let* "t66" := Instr.Call (CallKind.Function makeFloat) [(Register.read "t65")] in
      M.Return [(Register.read "t66")]
    );
    (23,
      let* "t67" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t68" := Instr.Extract (Register.read "t67") 0 in
      let* "t69" := Instr.Extract (Register.read "t67") 1 in
      Instr.If (Register.read "t69") 24 34
    );
    (24,
      let* "t70" := Instr.Alloc (* y *) Alloc.Local "*go/constant.complexVal" in
      let* _ := Instr.Store (Register.read "t70") (Register.read "t68") in
      let* "t71" := Instr.FieldAddr (Register.read "t70") 0 in
      let* "t72" := Instr.UnOp "*" (Register.read "t71") in
      let* "t73" := Instr.Call (CallKind.Function UnaryOp) [TODO_constant; (Register.read "t72"); TODO_constant] in
      let* "t74" := Instr.FieldAddr (Register.read "t70") 1 in
      let* "t75" := Instr.UnOp "*" (Register.read "t74") in
      let* "t76" := Instr.Call (CallKind.Function UnaryOp) [TODO_constant; (Register.read "t75"); TODO_constant] in
      let* "t77" := Instr.Call (CallKind.Function makeComplex) [(Register.read "t73"); (Register.read "t76")] in
      M.Return [(Register.read "t77")]
    );
    (25,
      let* "t78" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t79" := Instr.Extract (Register.read "t78") 0 in
      let* "t80" := Instr.Extract (Register.read "t78") 1 in
      Instr.If (Register.read "t80") 37 38
    );
    (26,
      let* "t81" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t81") 25 34
    );
    (27,
      let* "t82" := Instr.BinOp prec ">" TODO_constant in
      Instr.If (Register.read "t82") 35 36
    );
    (28,
      let* "t83" := Instr.MakeInterface (Register.read "t25") in
      M.Return [(Register.read "t83")]
    );
    (29,
      let* "t84" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t85" := Instr.Extract (Register.read "t84") 0 in
      let* "t86" := Instr.Extract (Register.read "t84") 1 in
      Instr.If (Register.read "t86") 30 31
    );
    (30,
      let* "t87" := Instr.ChangeType (Register.read "t85") in
      let* "t88" := Instr.Call (CallKind.Function math.big.NewInt) [(Register.read "t87")] in
      let* "t89" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t23"); (Register.read "t88")] in
      Instr.Jump 27
    );
    (31,
      let* "t90" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.intVal" in
      let* "t91" := Instr.Extract (Register.read "t90") 0 in
      let* "t92" := Instr.Extract (Register.read "t90") 1 in
      Instr.If (Register.read "t92") 32 33
    );
    (32,
      let* "t93" := Instr.Alloc (* y *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t93") (Register.read "t91") in
      let* "t94" := Instr.FieldAddr (Register.read "t93") 0 in
      let* "t95" := Instr.UnOp "*" (Register.read "t94") in
      let* "t96" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t23"); (Register.read "t95")] in
      Instr.Jump 27
    );
    (33,
      Instr.Jump 34
    );
    (34,
      let* "t97" := Instr.Alloc (* varargs *) Alloc.Heap "*[2]any" in
      let* "t98" := Instr.IndexAddr (Register.read "t97") TODO_constant in
      let* "t99" := Instr.MakeInterface op in
      let* _ := Instr.Store (Register.read "t98") (Register.read "t99") in
      let* "t100" := Instr.IndexAddr (Register.read "t97") TODO_constant in
      let* "t101" := Instr.ChangeInterface y in
      let* _ := Instr.Store (Register.read "t100") (Register.read "t101") in
      let* "t102" := Instr.Slice (Register.read "t97") None None in
      let* "t103" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t102")] in
      let* "t104" := Instr.MakeInterface (Register.read "t103") in
      Instr.Panic (Register.read "t104")
    );
    (35,
      let* "t105" := Instr.Call (CallKind.Function newInt) [] in
      let* "t106" := Instr.Call (CallKind.Function math.big.NewInt) [TODO_constant] in
      let* "t107" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t105"); (Register.read "t106"); prec] in
      let* "t108" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t23"); (Register.read "t23"); (Register.read "t107")] in
      Instr.Jump 36
    );
    (36,
      let* "t109" := Instr.Call (CallKind.Function makeInt) [(Register.read "t23")] in
      M.Return [(Register.read "t109")]
    );
    (37,
      let* "t110" := Instr.MakeInterface (Register.read "t79") in
      M.Return [(Register.read "t110")]
    );
    (38,
      let* "t111" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t112" := Instr.Extract (Register.read "t111") 0 in
      let* "t113" := Instr.Extract (Register.read "t111") 1 in
      Instr.If (Register.read "t113") 39 34
    );
    (39,
      let* "t114" := Instr.UnOp "!" (Register.read "t112") in
      let* "t115" := Instr.MakeInterface (Register.read "t114") in
      M.Return [(Register.read "t115")]
    )]
  | _ => []
  end)

with Val : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      let* "t3" := Instr.ChangeType (Register.read "t1") in
      let* "t4" := Instr.MakeInterface (Register.read "t3") in
      M.Return [(Register.read "t4")]
    );
    (2,
      let* "t5" := Instr.TypeAssert x TypeAssert.CommaOk "*go/constant.stringVal" in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.If (Register.read "t7") 3 4
    );
    (3,
      let* "t8" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t6")] in
      let* "t9" := Instr.MakeInterface (Register.read "t8") in
      M.Return [(Register.read "t9")]
    );
    (4,
      let* "t10" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t11" := Instr.Extract (Register.read "t10") 0 in
      let* "t12" := Instr.Extract (Register.read "t10") 1 in
      Instr.If (Register.read "t12") 5 6
    );
    (5,
      let* "t13" := Instr.ChangeType (Register.read "t11") in
      let* "t14" := Instr.MakeInterface (Register.read "t13") in
      M.Return [(Register.read "t14")]
    );
    (6,
      let* "t15" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      Instr.If (Register.read "t17") 7 8
    );
    (7,
      let* "t18" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t18") (Register.read "t16") in
      let* "t19" := Instr.FieldAddr (Register.read "t18") 0 in
      let* "t20" := Instr.UnOp "*" (Register.read "t19") in
      let* "t21" := Instr.MakeInterface (Register.read "t20") in
      M.Return [(Register.read "t21")]
    );
    (8,
      let* "t22" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t23" := Instr.Extract (Register.read "t22") 0 in
      let* "t24" := Instr.Extract (Register.read "t22") 1 in
      Instr.If (Register.read "t24") 9 10
    );
    (9,
      let* "t25" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t25") (Register.read "t23") in
      let* "t26" := Instr.FieldAddr (Register.read "t25") 0 in
      let* "t27" := Instr.UnOp "*" (Register.read "t26") in
      let* "t28" := Instr.MakeInterface (Register.read "t27") in
      M.Return [(Register.read "t28")]
    );
    (10,
      let* "t29" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t30" := Instr.Extract (Register.read "t29") 0 in
      let* "t31" := Instr.Extract (Register.read "t29") 1 in
      Instr.If (Register.read "t31") 11 12
    );
    (11,
      let* "t32" := Instr.Alloc (* x *) Alloc.Local "*go/constant.floatVal" in
      let* _ := Instr.Store (Register.read "t32") (Register.read "t30") in
      let* "t33" := Instr.FieldAddr (Register.read "t32") 0 in
      let* "t34" := Instr.UnOp "*" (Register.read "t33") in
      let* "t35" := Instr.MakeInterface (Register.read "t34") in
      M.Return [(Register.read "t35")]
    );
    (12,
      M.Return [TODO_constant]
    )]
  | _ => []
  end)

with add : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function BinaryOp) [x; TODO_constant; y] in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with cmpZero : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; op] =>
    [(0,
      let* "t0" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t0") 1 3
    );
    (1,
      let* "t1" := Instr.BinOp x "==" TODO_constant in
      M.Return [(Register.read "t1")]
    );
    (2,
      let* "t2" := Instr.BinOp x "!=" TODO_constant in
      M.Return [(Register.read "t2")]
    );
    (3,
      let* "t3" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t3") 2 5
    );
    (4,
      let* "t4" := Instr.BinOp x "<" TODO_constant in
      M.Return [(Register.read "t4")]
    );
    (5,
      let* "t5" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t5") 4 7
    );
    (6,
      let* "t6" := Instr.BinOp x "<=" TODO_constant in
      M.Return [(Register.read "t6")]
    );
    (7,
      let* "t7" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t7") 6 9
    );
    (8,
      let* "t8" := Instr.BinOp x ">" TODO_constant in
      M.Return [(Register.read "t8")]
    );
    (9,
      let* "t9" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t9") 8 11
    );
    (10,
      let* "t10" := Instr.BinOp x ">=" TODO_constant in
      M.Return [(Register.read "t10")]
    );
    (11,
      let* "t11" := Instr.BinOp op "==" TODO_constant in
      Instr.If (Register.read "t11") 10 12
    );
    (12,
      let* "t12" := Instr.Alloc (* varargs *) Alloc.Heap "*[2]any" in
      let* "t13" := Instr.IndexAddr (Register.read "t12") TODO_constant in
      let* "t14" := Instr.MakeInterface x in
      let* _ := Instr.Store (Register.read "t13") (Register.read "t14") in
      let* "t15" := Instr.IndexAddr (Register.read "t12") TODO_constant in
      let* "t16" := Instr.MakeInterface op in
      let* _ := Instr.Store (Register.read "t15") (Register.read "t16") in
      let* "t17" := Instr.Slice (Register.read "t12") None None in
      let* "t18" := Instr.Call (CallKind.Function fmt.Sprintf) [TODO_constant; (Register.read "t17")] in
      let* "t19" := Instr.MakeInterface (Register.read "t18") in
      Instr.Panic (Register.read "t19")
    )]
  | _ => []
  end)

with i64tof : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t1" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t2" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t3" := Instr.ChangeType x in
      let* "t4" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t2"); (Register.read "t3")] in
      let* _ := Instr.Store (Register.read "t1") (Register.read "t4") in
      let* "t5" := Instr.UnOp "*" (Register.read "t0") in
      M.Return [(Register.read "t5")]
    )]
  | _ => []
  end)

with i64toi : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.intVal" in
      let* "t1" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t2" := Instr.Call (CallKind.Function newInt) [] in
      let* "t3" := Instr.ChangeType x in
      let* "t4" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t2"); (Register.read "t3")] in
      let* _ := Instr.Store (Register.read "t1") (Register.read "t4") in
      let* "t5" := Instr.UnOp "*" (Register.read "t0") in
      M.Return [(Register.read "t5")]
    )]
  | _ => []
  end)

with i64tor : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.ratVal" in
      let* "t1" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t2" := Instr.Call (CallKind.Function newRat) [] in
      let* "t3" := Instr.ChangeType x in
      let* "t4" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t2"); (Register.read "t3")] in
      let* _ := Instr.Store (Register.read "t1") (Register.read "t4") in
      let* "t5" := Instr.UnOp "*" (Register.read "t0") in
      M.Return [(Register.read "t5")]
    )]
  | _ => []
  end)

with init : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [] =>
    [(0,
      let* "t0" := Instr.UnOp "*" (Register.read "init$guard") in
      Instr.If (Register.read "t0") 2 1
    );
    (1,
      let* _ := Instr.Store (Register.read "init$guard") TODO_constant in
      let* "t1" := Instr.Call (CallKind.Function strconv.init) [] in
      let* "t2" := Instr.Call (CallKind.Function fmt.init) [] in
      let* "t3" := Instr.Call (CallKind.Function go.token.init) [] in
      let* "t4" := Instr.Call (CallKind.Function math.init) [] in
      let* "t5" := Instr.Call (CallKind.Function math.big.init) [] in
      let* "t6" := Instr.Call (CallKind.Function math.bits.init) [] in
      let* "t7" := Instr.Call (CallKind.Function strings.init) [] in
      let* "t8" := Instr.Call (CallKind.Function sync.init) [] in
      let* "t9" := Instr.Call (CallKind.Function unicode.utf8.init) [] in
      let* "t10" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t11" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t12" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t13" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t14" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t15" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* "t16" := Instr.IndexAddr (Register.read "_Kind_index") TODO_constant in
      let* _ := Instr.Store (Register.read "t10") TODO_constant in
      let* _ := Instr.Store (Register.read "t11") TODO_constant in
      let* _ := Instr.Store (Register.read "t12") TODO_constant in
      let* _ := Instr.Store (Register.read "t13") TODO_constant in
      let* _ := Instr.Store (Register.read "t14") TODO_constant in
      let* _ := Instr.Store (Register.read "t15") TODO_constant in
      let* _ := Instr.Store (Register.read "t16") TODO_constant in
      let* "t17" := Instr.FieldAddr (Register.read "floatVal0") 0 in
      let* "t18" := Instr.Call (CallKind.Function newFloat) [] in
      let* _ := Instr.Store (Register.read "t17") (Register.read "t18") in
      Instr.Jump 2
    );
    (2,
      M.Return []
    )]
  | _ => []
  end)

with is32bit : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.BinOp TODO_constant "<=" x in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.BinOp x "<=" TODO_constant in
      Instr.Jump 2
    );
    (2,
      let* "t2" := Instr.Phi (* && *) [TODO_constant; (Register.read "t1")] in
      M.Return [(Register.read "t2")]
    )]
  | _ => []
  end)

with is63bit : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.BinOp TODO_constant "<=" x in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.BinOp x "<=" TODO_constant in
      Instr.Jump 2
    );
    (2,
      let* "t2" := Instr.Phi (* && *) [TODO_constant; (Register.read "t1")] in
      M.Return [(Register.read "t2")]
    )]
  | _ => []
  end)

with itof : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t0") x in
      let* "t1" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t2" := Instr.FieldAddr (Register.read "t1") 0 in
      let* "t3" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t4" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t5" := Instr.UnOp "*" (Register.read "t4") in
      let* "t6" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t3"); (Register.read "t5")] in
      let* _ := Instr.Store (Register.read "t2") (Register.read "t6") in
      let* "t7" := Instr.UnOp "*" (Register.read "t1") in
      M.Return [(Register.read "t7")]
    )]
  | _ => []
  end)

with itor : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* x *) Alloc.Local "*go/constant.intVal" in
      let* _ := Instr.Store (Register.read "t0") x in
      let* "t1" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.ratVal" in
      let* "t2" := Instr.FieldAddr (Register.read "t1") 0 in
      let* "t3" := Instr.Call (CallKind.Function newRat) [] in
      let* "t4" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t5" := Instr.UnOp "*" (Register.read "t4") in
      let* "t6" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t3"); (Register.read "t5")] in
      let* _ := Instr.Store (Register.read "t2") (Register.read "t6") in
      let* "t7" := Instr.UnOp "*" (Register.read "t1") in
      M.Return [(Register.read "t7")]
    )]
  | _ => []
  end)

with makeComplex : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [re; im] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Method re "Kind") [] in
      let* "t1" := Instr.BinOp (Register.read "t0") "==" TODO_constant in
      Instr.If (Register.read "t1") 1 3
    );
    (1,
      let* "t2" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t2")]
    );
    (2,
      let* "t3" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.complexVal" in
      let* "t4" := Instr.FieldAddr (Register.read "t3") 0 in
      let* "t5" := Instr.FieldAddr (Register.read "t3") 1 in
      let* _ := Instr.Store (Register.read "t4") re in
      let* _ := Instr.Store (Register.read "t5") im in
      let* "t6" := Instr.UnOp "*" (Register.read "t3") in
      let* "t7" := Instr.MakeInterface (Register.read "t6") in
      M.Return [(Register.read "t7")]
    );
    (3,
      let* "t8" := Instr.Call (CallKind.Method im "Kind") [] in
      let* "t9" := Instr.BinOp (Register.read "t8") "==" TODO_constant in
      Instr.If (Register.read "t9") 1 2
    )]
  | _ => []
  end)

with makeFloat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function TODO_method) [x] in
      let* "t1" := Instr.BinOp (Register.read "t0") "==" TODO_constant in
      Instr.If (Register.read "t1") 1 2
    );
    (1,
      let* "t2" := Instr.UnOp "*" (Register.read "floatVal0") in
      let* "t3" := Instr.MakeInterface (Register.read "t2") in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.Call (CallKind.Function TODO_method) [x] in
      Instr.If (Register.read "t4") 3 4
    );
    (3,
      let* "t5" := Instr.MakeInterface TODO_constant in
      M.Return [(Register.read "t5")]
    );
    (4,
      let* "t6" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t7" := Instr.FieldAddr (Register.read "t6") 0 in
      let* _ := Instr.Store (Register.read "t7") x in
      let* "t8" := Instr.UnOp "*" (Register.read "t6") in
      let* "t9" := Instr.MakeInterface (Register.read "t8") in
      M.Return [(Register.read "t9")]
    )]
  | _ => []
  end)

with makeFloatFromLiteral : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [lit] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t1" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t0"); lit] in
      let* "t2" := Instr.Extract (Register.read "t1") 0 in
      let* "t3" := Instr.Extract (Register.read "t1") 1 in
      Instr.If (Register.read "t3") 1 2
    );
    (1,
      let* "t4" := Instr.Call (CallKind.Function smallFloat) [(Register.read "t2")] in
      Instr.If (Register.read "t4") 3 4
    );
    (2,
      M.Return [TODO_constant]
    );
    (3,
      let* "t5" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t2")] in
      let* "t6" := Instr.BinOp (Register.read "t5") "==" TODO_constant in
      Instr.If (Register.read "t6") 5 6
    );
    (4,
      let* "t7" := Instr.Call (CallKind.Function makeFloat) [(Register.read "t2")] in
      M.Return [(Register.read "t7")]
    );
    (5,
      Instr.Jump 6
    );
    (6,
      let* "t8" := Instr.Phi (* lit *) [lit; TODO_constant] in
      let* "t9" := Instr.Call (CallKind.Function newRat) [] in
      let* "t10" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t9"); (Register.read "t8")] in
      let* "t11" := Instr.Extract (Register.read "t10") 0 in
      let* "t12" := Instr.Extract (Register.read "t10") 1 in
      Instr.If (Register.read "t12") 7 4
    );
    (7,
      let* "t13" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.ratVal" in
      let* "t14" := Instr.FieldAddr (Register.read "t13") 0 in
      let* _ := Instr.Store (Register.read "t14") (Register.read "t11") in
      let* "t15" := Instr.UnOp "*" (Register.read "t13") in
      let* "t16" := Instr.MakeInterface (Register.read "t15") in
      M.Return [(Register.read "t16")]
    )]
  | _ => []
  end)

with makeInt : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function TODO_method) [x] in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      let* "t1" := Instr.Call (CallKind.Function TODO_method) [x] in
      let* "t2" := Instr.ChangeType (Register.read "t1") in
      let* "t3" := Instr.MakeInterface (Register.read "t2") in
      M.Return [(Register.read "t3")]
    );
    (2,
      let* "t4" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.intVal" in
      let* "t5" := Instr.FieldAddr (Register.read "t4") 0 in
      let* _ := Instr.Store (Register.read "t5") x in
      let* "t6" := Instr.UnOp "*" (Register.read "t4") in
      let* "t7" := Instr.MakeInterface (Register.read "t6") in
      M.Return [(Register.read "t7")]
    )]
  | _ => []
  end)

with makeRat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function TODO_method) [x] in
      let* "t1" := Instr.Call (CallKind.Function TODO_method) [x] in
      let* "t2" := Instr.Call (CallKind.Function smallInt) [(Register.read "t0")] in
      Instr.If (Register.read "t2") 3 2
    );
    (1,
      let* "t3" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.ratVal" in
      let* "t4" := Instr.FieldAddr (Register.read "t3") 0 in
      let* _ := Instr.Store (Register.read "t4") x in
      let* "t5" := Instr.UnOp "*" (Register.read "t3") in
      let* "t6" := Instr.MakeInterface (Register.read "t5") in
      M.Return [(Register.read "t6")]
    );
    (2,
      let* "t7" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t8" := Instr.FieldAddr (Register.read "t7") 0 in
      let* "t9" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t10" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t9"); x] in
      let* _ := Instr.Store (Register.read "t8") (Register.read "t10") in
      let* "t11" := Instr.UnOp "*" (Register.read "t7") in
      let* "t12" := Instr.MakeInterface (Register.read "t11") in
      M.Return [(Register.read "t12")]
    );
    (3,
      let* "t13" := Instr.Call (CallKind.Function smallInt) [(Register.read "t1")] in
      Instr.If (Register.read "t13") 1 2
    )]
  | _ => []
  end)

with _'match : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function ord) [x] in
      let* "t1" := Instr.Call (CallKind.Function ord) [y] in
      let* "t2" := Instr.BinOp (Register.read "t0") "<" (Register.read "t1") in
      Instr.If (Register.read "t2") 2 4
    );
    (1,
      let* "t3" := Instr.Phi (* x *) [(Register.read "t6"); (Register.read "t10"); x] in
      let* "t4" := Instr.Phi (* y *) [(Register.read "t7"); (Register.read "t9"); y] in
      M.Return [(Register.read "t3"); (Register.read "t4")]
    );
    (2,
      let* "t5" := Instr.Call (CallKind.Function match0) [x; y] in
      let* "t6" := Instr.Extract (Register.read "t5") 0 in
      let* "t7" := Instr.Extract (Register.read "t5") 1 in
      Instr.Jump 1
    );
    (3,
      let* "t8" := Instr.Call (CallKind.Function match0) [y; x] in
      let* "t9" := Instr.Extract (Register.read "t8") 0 in
      let* "t10" := Instr.Extract (Register.read "t8") 1 in
      Instr.Jump 1
    );
    (4,
      let* "t11" := Instr.BinOp (Register.read "t0") ">" (Register.read "t1") in
      Instr.If (Register.read "t11") 3 1
    )]
  | _ => []
  end)

with match0 : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.intVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 2 3
    );
    (1,
      M.Return [x; x]
    );
    (2,
      let* "t3" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 4 1
    );
    (3,
      let* "t6" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t7" := Instr.Extract (Register.read "t6") 0 in
      let* "t8" := Instr.Extract (Register.read "t6") 1 in
      Instr.If (Register.read "t8") 5 6
    );
    (4,
      let* "t9" := Instr.Call (CallKind.Function i64toi) [(Register.read "t4")] in
      let* "t10" := Instr.MakeInterface (Register.read "t9") in
      M.Return [(Register.read "t10"); y]
    );
    (5,
      let* "t11" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t12" := Instr.Extract (Register.read "t11") 0 in
      let* "t13" := Instr.Extract (Register.read "t11") 1 in
      Instr.If (Register.read "t13") 7 8
    );
    (6,
      let* "t14" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t15" := Instr.Extract (Register.read "t14") 0 in
      let* "t16" := Instr.Extract (Register.read "t14") 1 in
      Instr.If (Register.read "t16") 10 11
    );
    (7,
      let* "t17" := Instr.Call (CallKind.Function i64tor) [(Register.read "t12")] in
      let* "t18" := Instr.MakeInterface (Register.read "t17") in
      M.Return [(Register.read "t18"); y]
    );
    (8,
      let* "t19" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t20" := Instr.Extract (Register.read "t19") 0 in
      let* "t21" := Instr.Extract (Register.read "t19") 1 in
      Instr.If (Register.read "t21") 9 1
    );
    (9,
      let* "t22" := Instr.Call (CallKind.Function itor) [(Register.read "t20")] in
      let* "t23" := Instr.MakeInterface (Register.read "t22") in
      M.Return [(Register.read "t23"); y]
    );
    (10,
      let* "t24" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t25" := Instr.Extract (Register.read "t24") 0 in
      let* "t26" := Instr.Extract (Register.read "t24") 1 in
      Instr.If (Register.read "t26") 12 13
    );
    (11,
      let* "t27" := Instr.TypeAssert y TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t28" := Instr.Extract (Register.read "t27") 0 in
      let* "t29" := Instr.Extract (Register.read "t27") 1 in
      Instr.If (Register.read "t29") 17 1
    );
    (12,
      let* "t30" := Instr.Call (CallKind.Function i64tof) [(Register.read "t25")] in
      let* "t31" := Instr.MakeInterface (Register.read "t30") in
      M.Return [(Register.read "t31"); y]
    );
    (13,
      let* "t32" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t33" := Instr.Extract (Register.read "t32") 0 in
      let* "t34" := Instr.Extract (Register.read "t32") 1 in
      Instr.If (Register.read "t34") 14 15
    );
    (14,
      let* "t35" := Instr.Call (CallKind.Function itof) [(Register.read "t33")] in
      let* "t36" := Instr.MakeInterface (Register.read "t35") in
      M.Return [(Register.read "t36"); y]
    );
    (15,
      let* "t37" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t38" := Instr.Extract (Register.read "t37") 0 in
      let* "t39" := Instr.Extract (Register.read "t37") 1 in
      Instr.If (Register.read "t39") 16 1
    );
    (16,
      let* "t40" := Instr.Call (CallKind.Function rtof) [(Register.read "t38")] in
      let* "t41" := Instr.MakeInterface (Register.read "t40") in
      M.Return [(Register.read "t41"); y]
    );
    (17,
      let* "t42" := Instr.Call (CallKind.Function vtoc) [x] in
      let* "t43" := Instr.MakeInterface (Register.read "t42") in
      M.Return [(Register.read "t43"); y]
    )]
  | _ => []
  end)

with mul : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function BinaryOp) [x; TODO_constant; y] in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with newFloat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [] =>
    [(0,
      let* "t0" := Instr.Alloc (* new *) Alloc.Heap "*math/big.Float" in
      let* "t1" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t0"); TODO_constant] in
      M.Return [(Register.read "t1")]
    )]
  | _ => []
  end)

with newInt : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [] =>
    [(0,
      let* "t0" := Instr.Alloc (* new *) Alloc.Heap "*math/big.Int" in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with newRat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [] =>
    [(0,
      let* "t0" := Instr.Alloc (* new *) Alloc.Heap "*math/big.Rat" in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with ord : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.unknownVal" in
      let* "t1" := Instr.Extract (Register.read "t0") 0 in
      let* "t2" := Instr.Extract (Register.read "t0") 1 in
      Instr.If (Register.read "t2") 1 2
    );
    (1,
      M.Return [TODO_constant]
    );
    (2,
      let* "t3" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.boolVal" in
      let* "t4" := Instr.Extract (Register.read "t3") 0 in
      let* "t5" := Instr.Extract (Register.read "t3") 1 in
      Instr.If (Register.read "t5") 3 4
    );
    (3,
      M.Return [TODO_constant]
    );
    (4,
      let* "t6" := Instr.TypeAssert x TypeAssert.CommaOk "*go/constant.stringVal" in
      let* "t7" := Instr.Extract (Register.read "t6") 0 in
      let* "t8" := Instr.Extract (Register.read "t6") 1 in
      Instr.If (Register.read "t8") 3 5
    );
    (5,
      let* "t9" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.int64Val" in
      let* "t10" := Instr.Extract (Register.read "t9") 0 in
      let* "t11" := Instr.Extract (Register.read "t9") 1 in
      Instr.If (Register.read "t11") 6 7
    );
    (6,
      M.Return [TODO_constant]
    );
    (7,
      let* "t12" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.intVal" in
      let* "t13" := Instr.Extract (Register.read "t12") 0 in
      let* "t14" := Instr.Extract (Register.read "t12") 1 in
      Instr.If (Register.read "t14") 8 9
    );
    (8,
      M.Return [TODO_constant]
    );
    (9,
      let* "t15" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.ratVal" in
      let* "t16" := Instr.Extract (Register.read "t15") 0 in
      let* "t17" := Instr.Extract (Register.read "t15") 1 in
      Instr.If (Register.read "t17") 10 11
    );
    (10,
      M.Return [TODO_constant]
    );
    (11,
      let* "t18" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.floatVal" in
      let* "t19" := Instr.Extract (Register.read "t18") 0 in
      let* "t20" := Instr.Extract (Register.read "t18") 1 in
      Instr.If (Register.read "t20") 12 13
    );
    (12,
      M.Return [TODO_constant]
    );
    (13,
      let* "t21" := Instr.TypeAssert x TypeAssert.CommaOk "go/constant.complexVal" in
      let* "t22" := Instr.Extract (Register.read "t21") 0 in
      let* "t23" := Instr.Extract (Register.read "t21") 1 in
      Instr.If (Register.read "t23") 14 15
    );
    (14,
      M.Return [TODO_constant]
    );
    (15,
      M.Return [TODO_constant]
    )]
  | _ => []
  end)

with quo : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function BinaryOp) [x; TODO_constant; y] in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with reverse : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function len) [x] in
      Instr.Jump 3
    );
    (1,
      let* "t1" := Instr.BinOp (Register.read "t0") "-" TODO_constant in
      let* "t2" := Instr.BinOp (Register.read "t1") "-" (Register.read "t12") in
      let* "t3" := Instr.BinOp (Register.read "t0") "-" TODO_constant in
      let* "t4" := Instr.BinOp (Register.read "t3") "-" (Register.read "t12") in
      let* "t5" := Instr.IndexAddr x (Register.read "t4") in
      let* "t6" := Instr.UnOp "*" (Register.read "t5") in
      let* "t7" := Instr.IndexAddr x (Register.read "t12") in
      let* "t8" := Instr.UnOp "*" (Register.read "t7") in
      let* "t9" := Instr.IndexAddr x (Register.read "t12") in
      let* _ := Instr.Store (Register.read "t9") (Register.read "t6") in
      let* "t10" := Instr.IndexAddr x (Register.read "t2") in
      let* _ := Instr.Store (Register.read "t10") (Register.read "t8") in
      let* "t11" := Instr.BinOp (Register.read "t12") "+" TODO_constant in
      Instr.Jump 3
    );
    (2,
      M.Return [x]
    );
    (3,
      let* "t12" := Instr.Phi (* i *) [TODO_constant; (Register.read "t11")] in
      let* "t13" := Instr.BinOp (Register.read "t12") "+" (Register.read "t12") in
      let* "t14" := Instr.BinOp (Register.read "t13") "<" (Register.read "t0") in
      Instr.If (Register.read "t14") 1 2
    )]
  | _ => []
  end)

with rtof : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* x *) Alloc.Local "*go/constant.ratVal" in
      let* _ := Instr.Store (Register.read "t0") x in
      let* "t1" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.floatVal" in
      let* "t2" := Instr.FieldAddr (Register.read "t1") 0 in
      let* "t3" := Instr.Call (CallKind.Function newFloat) [] in
      let* "t4" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t5" := Instr.UnOp "*" (Register.read "t4") in
      let* "t6" := Instr.Call (CallKind.Function TODO_method) [(Register.read "t3"); (Register.read "t5")] in
      let* _ := Instr.Store (Register.read "t2") (Register.read "t6") in
      let* "t7" := Instr.UnOp "*" (Register.read "t1") in
      M.Return [(Register.read "t7")]
    )]
  | _ => []
  end)

with smallFloat : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function TODO_method) [x] in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      M.Return [TODO_constant]
    );
    (2,
      let* "t1" := Instr.Call (CallKind.Function TODO_method) [x; TODO_constant] in
      let* "t2" := Instr.BinOp TODO_constant "<" (Register.read "t1") in
      Instr.If (Register.read "t2") 3 4
    );
    (3,
      let* "t3" := Instr.BinOp (Register.read "t1") "<" TODO_constant in
      Instr.Jump 4
    );
    (4,
      let* "t4" := Instr.Phi (* && *) [TODO_constant; (Register.read "t3")] in
      M.Return [(Register.read "t4")]
    )]
  | _ => []
  end)

with smallFloat64 : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function math.IsInf) [x; TODO_constant] in
      Instr.If (Register.read "t0") 1 2
    );
    (1,
      M.Return [TODO_constant]
    );
    (2,
      let* "t1" := Instr.Call (CallKind.Function math.Frexp) [x] in
      let* "t2" := Instr.Extract (Register.read "t1") 0 in
      let* "t3" := Instr.Extract (Register.read "t1") 1 in
      let* "t4" := Instr.BinOp TODO_constant "<" (Register.read "t3") in
      Instr.If (Register.read "t4") 3 4
    );
    (3,
      let* "t5" := Instr.BinOp (Register.read "t3") "<" TODO_constant in
      Instr.Jump 4
    );
    (4,
      let* "t6" := Instr.Phi (* && *) [TODO_constant; (Register.read "t5")] in
      M.Return [(Register.read "t6")]
    )]
  | _ => []
  end)

with smallInt : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function TODO_method) [x] in
      let* "t1" := Instr.BinOp (Register.read "t0") "<" TODO_constant in
      M.Return [(Register.read "t1")]
    )]
  | _ => []
  end)

with sub : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x; y] =>
    [(0,
      let* "t0" := Instr.Call (CallKind.Function BinaryOp) [x; TODO_constant; y] in
      M.Return [(Register.read "t0")]
    )]
  | _ => []
  end)

with vtoc : Function.t :=
  Function.Body (fun α =>
  match α with
  | Val.Tuple [x] =>
    [(0,
      let* "t0" := Instr.Alloc (* complit *) Alloc.Local "*go/constant.complexVal" in
      let* "t1" := Instr.FieldAddr (Register.read "t0") 0 in
      let* "t2" := Instr.FieldAddr (Register.read "t0") 1 in
      let* _ := Instr.Store (Register.read "t1") x in
      let* "t3" := Instr.MakeInterface TODO_constant in
      let* _ := Instr.Store (Register.read "t2") (Register.read "t3") in
      let* "t4" := Instr.UnOp "*" (Register.read "t0") in
      M.Return [(Register.read "t4")]
    )]
  | _ => []
  end).

(** ** Types *)

Parameter Kind : Set.

Parameter Value : Set.

Parameter boolVal : Set.

Parameter complexVal : Set.

Parameter floatVal : Set.

Parameter int64Val : Set.

Parameter intVal : Set.

Parameter ratVal : Set.

Parameter stringVal : Set.

Parameter unknownVal : Set.

