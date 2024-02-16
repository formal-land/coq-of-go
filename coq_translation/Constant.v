Require Import Coq.ZArith.ZArith.
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

(** ** Constants *)

Definition Bool : Val.t :=
  Val.int 1.

Definition Complex : Val.t :=
  Val.int 5.

Definition Float : Val.t :=
  Val.int 4.

Definition Int : Val.t :=
  Val.int 3.

Definition String : Val.t :=
  Val.int 2.

Definition Unknown : Val.t :=
  Val.int 0.

Definition _Kind_name : Val.t :=
  Val.string "UnknownBoolStringIntFloatComplex".

Definition _log : Val.t :=
  Val.int 3.

Definition _m : Val.t :=
  Val.int 18446744073709551615.

Definition maxExp : Val.t :=
  Val.int 4096.

Definition prec : Val.t :=
  Val.int 512.

Definition wordSize : Val.t :=
  Val.int 8.

(** ** Globals *)

Module GlobalName.
  Inductive t : Set :=
  | _Kind_index : t
  | emptyString : t
  | floatVal0 : t
  | init_dollar_guard : t
  .
End GlobalName.

Definition _Kind_index : M Val.t :=
  M.global GlobalName._Kind_index.

Definition emptyString : M Val.t :=
  M.global GlobalName.emptyString.

Definition floatVal0 : M Val.t :=
  M.global GlobalName.floatVal0.

Definition init_dollar_guard : M Val.t :=
  M.global GlobalName.init_dollar_guard.

(** ** Functions *)

Definition BinaryOp (x_ op y_ : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (match x_ y_);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    t3 := TypeAssert (t1 CommaOk go/constant.unknownVal);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 1 2
  ]);
  (1, [
    t6 := MakeInterface (t4 t4);
    Return (t6)
  ]);
  (2, [
    t7 := TypeAssert (t1 CommaOk go/constant.boolVal);
    t8 := Extract (t7 0);
    t9 := Extract (t7 1);
    If t9 3 4
  ]);
  (3, [
    t10 := TypeAssert (t2 NoCommaOk go/constant.boolVal);
    t11 := BinOp op "==" 34:go/token.Token);
    If t11 5 7
  ]);
  (4, [
    t12 := TypeAssert (t1 CommaOk go/constant.int64Val);
    t13 := Extract (t12 0);
    t14 := Extract (t12 1);
    If t14 12 13
  ]);
  (5, [
    If t8 8 9
  ]);
  (6, [
    If t8 11 10
  ]);
  (7, [
    t15 := BinOp op "==" 35:go/token.Token);
    If t15 6 43
  ]);
  (8, [
    Jump 9
  ]);
  (9, [
    t16 := Phi (* && *) (false:go/constant.boolVal t10);
    t17 := MakeInterface (t16 t16);
    Return (t17)
  ]);
  (10, [
    Jump 11
  ]);
  (11, [
    t18 := Phi (* || *) (true:go/constant.boolVal t10);
    t19 := MakeInterface (t18 t18);
    Return (t19)
  ]);
  (12, [
    t20 := ChangeType (t13);
    t21 := TypeAssert (t2 NoCommaOk go/constant.int64Val);
    t22 := ChangeType (t21);
    t23 := BinOp op "==" 12:go/token.Token);
    If t23 15 17
  ]);
  (13, [
    t24 := TypeAssert (t1 CommaOk go/constant.intVal);
    t25 := Extract (t24 0);
    t26 := Extract (t24 1);
    If t26 44 45
  ]);
  (14, [
    t27 := Phi (* c *) (t38 t47 t57 t59 t61 t63 t65 t67 t69);
    t28 := ChangeType (t27);
    t29 := MakeInterface (t28 t28);
    Return (t29)
  ]);
  (15, [
    t30 := Call (is63bit t20);
    If t30 20 18
  ]);
  (16, [
    t31 := Call (is63bit t20);
    If t31 25 23
  ]);
  (17, [
    t32 := BinOp op "==" 13:go/token.Token);
    If t32 16 22
  ]);
  (18, [
    t33 := Call (newInt );
    t34 := Call (NewInt t20);
    t35 := Call (NewInt t22);
    t36 := Call (Add t33 t34 t35);
    t37 := Call (makeInt t36);
    Return (t37)
  ]);
  (19, [
    t38 := BinOp t20 "+" t22);
    Jump 14
  ]);
  (20, [
    t39 := Call (is63bit t22);
    If t39 19 18
  ]);
  (21, [
    t40 := Call (is32bit t20);
    If t40 30 28
  ]);
  (22, [
    t41 := BinOp op "==" 14:go/token.Token);
    If t41 21 27
  ]);
  (23, [
    t42 := Call (newInt );
    t43 := Call (NewInt t20);
    t44 := Call (NewInt t22);
    t45 := Call (Sub t42 t43 t44);
    t46 := Call (makeInt t45);
    Return (t46)
  ]);
  (24, [
    t47 := BinOp t20 "-" t22);
    Jump 14
  ]);
  (25, [
    t48 := Call (is63bit t22);
    If t48 24 23
  ]);
  (26, [
    t49 := Call (NewRat t20 t22);
    t50 := Call (makeRat t49);
    Return (t50)
  ]);
  (27, [
    t51 := BinOp op "==" 15:go/token.Token);
    If t51 26 32
  ]);
  (28, [
    t52 := Call (newInt );
    t53 := Call (NewInt t20);
    t54 := Call (NewInt t22);
    t55 := Call (Mul t52 t53 t54);
    t56 := Call (makeInt t55);
    Return (t56)
  ]);
  (29, [
    t57 := BinOp t20 "*" t22);
    Jump 14
  ]);
  (30, [
    t58 := Call (is32bit t22);
    If t58 29 28
  ]);
  (31, [
    t59 := BinOp t20 "/" t22);
    Jump 14
  ]);
  (32, [
    t60 := BinOp op "==" 26:go/token.Token);
    If t60 31 34
  ]);
  (33, [
    t61 := BinOp t20 "%" t22);
    Jump 14
  ]);
  (34, [
    t62 := BinOp op "==" 16:go/token.Token);
    If t62 33 36
  ]);
  (35, [
    t63 := BinOp t20 "&" t22);
    Jump 14
  ]);
  (36, [
    t64 := BinOp op "==" 17:go/token.Token);
    If t64 35 38
  ]);
  (37, [
    t65 := BinOp t20 "|" t22);
    Jump 14
  ]);
  (38, [
    t66 := BinOp op "==" 18:go/token.Token);
    If t66 37 40
  ]);
  (39, [
    t67 := BinOp t20 "^" t22);
    Jump 14
  ]);
  (40, [
    t68 := BinOp op "==" 19:go/token.Token);
    If t68 39 42
  ]);
  (41, [
    t69 := BinOp t20 "&^" t22);
    Jump 14
  ]);
  (42, [
    t70 := BinOp op "==" 22:go/token.Token);
    If t70 41 43
  ]);
  (43, [
    t71 := Alloc (*varargs*) Heap *[3]any;
    t72 := IndexAddr (t71 0:int);
    t73 := ChangeInterface (x_);
    Store (t72 t73);
    t74 := IndexAddr (t71 1:int);
    t75 := MakeInterface (op op);
    Store (t74 t75);
    t76 := IndexAddr (t71 2:int);
    t77 := ChangeInterface (y_);
    Store (t76 t77);
    t78 := Slice (t71);
    t79 := Call (Sprintf "invalid binary op...":string t78);
    t80 := MakeInterface (t79 t79);
    Panic (t80)
  ]);
  (44, [
    t81 := Alloc (*x*) Local *go/constant.intVal;
    Store (t81 t25);
    t82 := FieldAddr (t81 0);
    t83 := UnOp (* t82);
    t84 := TypeAssert (t2 NoCommaOk go/constant.intVal);
    t85 := Field (t84 0);
    t86 := Call (newInt );
    t87 := BinOp op "==" 12:go/token.Token);
    If t87 47 49
  ]);
  (45, [
    t88 := TypeAssert (t1 CommaOk go/constant.ratVal);
    t89 := Extract (t88 0);
    t90 := Extract (t88 1);
    If t90 66 67
  ]);
  (46, [
    t91 := Call (makeInt t86);
    Return (t91)
  ]);
  (47, [
    t92 := Call (Add t86 t83 t85);
    Jump 46
  ]);
  (48, [
    t93 := Call (Sub t86 t83 t85);
    Jump 46
  ]);
  (49, [
    t94 := BinOp op "==" 13:go/token.Token);
    If t94 48 51
  ]);
  (50, [
    t95 := Call (Mul t86 t83 t85);
    Jump 46
  ]);
  (51, [
    t96 := BinOp op "==" 14:go/token.Token);
    If t96 50 53
  ]);
  (52, [
    t97 := Call (newRat );
    t98 := Call (SetFrac t97 t83 t85);
    t99 := Call (makeRat t98);
    Return (t99)
  ]);
  (53, [
    t100 := BinOp op "==" 15:go/token.Token);
    If t100 52 55
  ]);
  (54, [
    t101 := Call (Quo t86 t83 t85);
    Jump 46
  ]);
  (55, [
    t102 := BinOp op "==" 26:go/token.Token);
    If t102 54 57
  ]);
  (56, [
    t103 := Call (Rem t86 t83 t85);
    Jump 46
  ]);
  (57, [
    t104 := BinOp op "==" 16:go/token.Token);
    If t104 56 59
  ]);
  (58, [
    t105 := Call (And t86 t83 t85);
    Jump 46
  ]);
  (59, [
    t106 := BinOp op "==" 17:go/token.Token);
    If t106 58 61
  ]);
  (60, [
    t107 := Call (Or t86 t83 t85);
    Jump 46
  ]);
  (61, [
    t108 := BinOp op "==" 18:go/token.Token);
    If t108 60 63
  ]);
  (62, [
    t109 := Call (Xor t86 t83 t85);
    Jump 46
  ]);
  (63, [
    t110 := BinOp op "==" 19:go/token.Token);
    If t110 62 65
  ]);
  (64, [
    t111 := Call (AndNot t86 t83 t85);
    Jump 46
  ]);
  (65, [
    t112 := BinOp op "==" 22:go/token.Token);
    If t112 64 43
  ]);
  (66, [
    t113 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t113 t89);
    t114 := FieldAddr (t113 0);
    t115 := UnOp (* t114);
    t116 := TypeAssert (t2 NoCommaOk go/constant.ratVal);
    t117 := Field (t116 0);
    t118 := Call (newRat );
    t119 := BinOp op "==" 12:go/token.Token);
    If t119 69 71
  ]);
  (67, [
    t120 := TypeAssert (t1 CommaOk go/constant.floatVal);
    t121 := Extract (t120 0);
    t122 := Extract (t120 1);
    If t122 76 77
  ]);
  (68, [
    t123 := Call (makeRat t118);
    Return (t123)
  ]);
  (69, [
    t124 := Call (Add t118 t115 t117);
    Jump 68
  ]);
  (70, [
    t125 := Call (Sub t118 t115 t117);
    Jump 68
  ]);
  (71, [
    t126 := BinOp op "==" 13:go/token.Token);
    If t126 70 73
  ]);
  (72, [
    t127 := Call (Mul t118 t115 t117);
    Jump 68
  ]);
  (73, [
    t128 := BinOp op "==" 14:go/token.Token);
    If t128 72 75
  ]);
  (74, [
    t129 := Call (Quo t118 t115 t117);
    Jump 68
  ]);
  (75, [
    t130 := BinOp op "==" 15:go/token.Token);
    If t130 74 43
  ]);
  (76, [
    t131 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t131 t121);
    t132 := FieldAddr (t131 0);
    t133 := UnOp (* t132);
    t134 := TypeAssert (t2 NoCommaOk go/constant.floatVal);
    t135 := Field (t134 0);
    t136 := Call (newFloat );
    t137 := BinOp op "==" 12:go/token.Token);
    If t137 79 81
  ]);
  (77, [
    t138 := TypeAssert (t1 CommaOk go/constant.complexVal);
    t139 := Extract (t138 0);
    t140 := Extract (t138 1);
    If t140 86 87
  ]);
  (78, [
    t141 := Call (makeFloat t136);
    Return (t141)
  ]);
  (79, [
    t142 := Call (Add t136 t133 t135);
    Jump 78
  ]);
  (80, [
    t143 := Call (Sub t136 t133 t135);
    Jump 78
  ]);
  (81, [
    t144 := BinOp op "==" 13:go/token.Token);
    If t144 80 83
  ]);
  (82, [
    t145 := Call (Mul t136 t133 t135);
    Jump 78
  ]);
  (83, [
    t146 := BinOp op "==" 14:go/token.Token);
    If t146 82 85
  ]);
  (84, [
    t147 := Call (Quo t136 t133 t135);
    Jump 78
  ]);
  (85, [
    t148 := BinOp op "==" 15:go/token.Token);
    If t148 84 43
  ]);
  (86, [
    t149 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t149 t139);
    t150 := Alloc (*y*) Local *go/constant.complexVal;
    t151 := TypeAssert (t2 NoCommaOk go/constant.complexVal);
    Store (t150 t151);
    t152 := FieldAddr (t149 0);
    t153 := UnOp (* t152);
    t154 := FieldAddr (t149 1);
    t155 := UnOp (* t154);
    t156 := FieldAddr (t150 0);
    t157 := UnOp (* t156);
    t158 := FieldAddr (t150 1);
    t159 := UnOp (* t158);
    t160 := BinOp op "==" 12:go/token.Token);
    If t160 89 91
  ]);
  (87, [
    t161 := TypeAssert (t1 CommaOk *go/constant.stringVal);
    t162 := Extract (t161 0);
    t163 := Extract (t161 1);
    If t163 96 43
  ]);
  (88, [
    t164 := Phi (* re *) (t167 t169 t176 t187);
    t165 := Phi (* im *) (t168 t170 t177 t189);
    t166 := Call (makeComplex t164 t165);
    Return (t166)
  ]);
  (89, [
    t167 := Call (add t153 t157);
    t168 := Call (add t155 t159);
    Jump 88
  ]);
  (90, [
    t169 := Call (sub t153 t157);
    t170 := Call (sub t155 t159);
    Jump 88
  ]);
  (91, [
    t171 := BinOp op "==" 13:go/token.Token);
    If t171 90 93
  ]);
  (92, [
    t172 := Call (mul t153 t157);
    t173 := Call (mul t155 t159);
    t174 := Call (mul t155 t157);
    t175 := Call (mul t153 t159);
    t176 := Call (sub t172 t173);
    t177 := Call (add t174 t175);
    Jump 88
  ]);
  (93, [
    t178 := BinOp op "==" 14:go/token.Token);
    If t178 92 95
  ]);
  (94, [
    t179 := Call (mul t153 t157);
    t180 := Call (mul t155 t159);
    t181 := Call (mul t155 t157);
    t182 := Call (mul t153 t159);
    t183 := Call (mul t157 t157);
    t184 := Call (mul t159 t159);
    t185 := Call (add t183 t184);
    t186 := Call (add t179 t180);
    t187 := Call (quo t186 t185);
    t188 := Call (sub t181 t182);
    t189 := Call (quo t188 t185);
    Jump 88
  ]);
  (95, [
    t190 := BinOp op "==" 15:go/token.Token);
    If t190 94 43
  ]);
  (96, [
    t191 := BinOp op "==" 12:go/token.Token);
    If t191 97 43
  ]);
  (97, [
    t192 := Alloc (*complit*) Heap *go/constant.stringVal;
    t193 := FieldAddr (t192 2);
    t194 := FieldAddr (t192 3);
    t195 := TypeAssert (t2 NoCommaOk *go/constant.stringVal);
    Store (t193 t162);
    Store (t194 t195);
    t196 := MakeInterface (t192 t192);
    Return (t196)
  ])
].

Definition BitLen (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := Convert (t1);
    t4 := BinOp t1 "<" 0:go/constant.int64Val);
    If t4 3 4
  ]);
  (2, [
    t5 := TypeAssert (x CommaOk go/constant.intVal);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 5 6
  ]);
  (3, [
    t8 := UnOp (- t1);
    t9 := Convert (t8);
    Jump 4
  ]);
  (4, [
    t10 := Phi (* u *) (t3 t9);
    t11 := Call (LeadingZeros64 t10);
    t12 := BinOp 64:int "-" t11);
    Return (t12)
  ]);
  (5, [
    t13 := Alloc (*x*) Local *go/constant.intVal;
    Store (t13 t6);
    t14 := FieldAddr (t13 0);
    t15 := UnOp (* t14);
    t16 := Call (BitLen t15);
    Return (t16)
  ]);
  (6, [
    t17 := TypeAssert (x CommaOk go/constant.unknownVal);
    t18 := Extract (t17 0);
    t19 := Extract (t17 1);
    If t19 7 8
  ]);
  (7, [
    Return (0:int)
  ]);
  (8, [
    t20 := Alloc (*varargs*) Heap *[1]any;
    t21 := IndexAddr (t20 0:int);
    t22 := ChangeInterface (x);
    Store (t21 t22);
    t23 := Slice (t20);
    t24 := Call (Sprintf "%v not an Int":string t23);
    t25 := MakeInterface (t24 t24);
    Panic (t25)
  ])
].

Definition BoolVal (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.boolVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := ChangeType (t1);
    Return (t3)
  ]);
  (2, [
    t4 := TypeAssert (x CommaOk go/constant.unknownVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 3 4
  ]);
  (3, [
    Return (false:bool)
  ]);
  (4, [
    t7 := Alloc (*varargs*) Heap *[1]any;
    t8 := IndexAddr (t7 0:int);
    t9 := ChangeInterface (x);
    Store (t8 t9);
    t10 := Slice (t7);
    t11 := Call (Sprintf "%v not a Bool":string t10);
    t12 := MakeInterface (t11 t11);
    Panic (t12)
  ])
].

Definition Bytes (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*t*) Local *go/constant.intVal;
    t1 := TypeAssert (x CommaOk go/constant.int64Val);
    t2 := Extract (t1 0);
    t3 := Extract (t1 1);
    If t3 2 3
  ]);
  (1, [
    t4 := FieldAddr (t0 0);
    t5 := UnOp (* t4);
    t6 := Call (Bits t5);
    t7 := Call (len t6);
    t8 := BinOp t7 "*" 8:int);
    t9 := MakeSlice (t8 t8);
    t10 := Call (len t6);
    Jump 6
  ]);
  (2, [
    t11 := Call (i64toi t2);
    Store (t0 t11);
    Jump 1
  ]);
  (3, [
    t12 := TypeAssert (x CommaOk go/constant.intVal);
    t13 := Extract (t12 0);
    t14 := Extract (t12 1);
    If t14 4 5
  ]);
  (4, [
    Store (t0 t13);
    Jump 1
  ]);
  (5, [
    t15 := Alloc (*varargs*) Heap *[1]any;
    t16 := IndexAddr (t15 0:int);
    t17 := ChangeInterface (x);
    Store (t16 t17);
    t18 := Slice (t15);
    t19 := Call (Sprintf "%v not an Int":string t18);
    t20 := MakeInterface (t19 t19);
    Panic (t20)
  ]);
  (6, [
    t21 := Phi (* i *) (0:int t32);
    t22 := Phi (* rangeindex *) (-1:int t23);
    t23 := BinOp t22 "+" 1:int);
    t24 := BinOp t23 "<" t10);
    If t24 7 12
  ]);
  (7, [
    t25 := IndexAddr (t6 t23);
    t26 := UnOp (* t25);
    Jump 9
  ]);
  (8, [
    t27 := Convert (t33);
    t28 := IndexAddr (t9 t32);
    Store (t28 t27);
    t29 := BinOp t33 ">>" 8:uint);
    t30 := BinOp t32 "+" 1:int);
    t31 := BinOp t34 "+" 1:int);
    Jump 9
  ]);
  (9, [
    t32 := Phi (* i *) (t21 t30);
    t33 := Phi (* w *) (t26 t29);
    t34 := Phi (* j *) (0:int t31);
    t35 := BinOp t34 "<" 8:int);
    If t35 8 6
  ]);
  (10, [
    t36 := BinOp t38 "-" 1:int);
    Jump 12
  ]);
  (11, [
    t37 := Slice (t9 t38);
    Return (t37)
  ]);
  (12, [
    t38 := Phi (* i *) (t21 t36);
    t39 := BinOp t38 ">" 0:int);
    If t39 13 11
  ]);
  (13, [
    t40 := BinOp t38 "-" 1:int);
    t41 := IndexAddr (t9 t40);
    t42 := UnOp (* t41);
    t43 := BinOp t42 "==" 0:byte);
    If t43 10 11
  ])
].

Definition Compare (x_ op y_ : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (match x_ y_);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    t3 := TypeAssert (t1 CommaOk go/constant.unknownVal);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 2 3
  ]);
  (1, [
    t6 := Alloc (*varargs*) Heap *[3]any;
    t7 := IndexAddr (t6 0:int);
    t8 := ChangeInterface (x_);
    Store (t7 t8);
    t9 := IndexAddr (t6 1:int);
    t10 := MakeInterface (op op);
    Store (t9 t10);
    t11 := IndexAddr (t6 2:int);
    t12 := ChangeInterface (y_);
    Store (t11 t12);
    t13 := Slice (t6);
    t14 := Call (Sprintf "invalid compariso...":string t13);
    t15 := MakeInterface (t14 t14);
    Panic (t15)
  ]);
  (2, [
    Return (false:bool)
  ]);
  (3, [
    t16 := TypeAssert (t1 CommaOk go/constant.boolVal);
    t17 := Extract (t16 0);
    t18 := Extract (t16 1);
    If t18 4 5
  ]);
  (4, [
    t19 := TypeAssert (t2 NoCommaOk go/constant.boolVal);
    t20 := BinOp op "==" 39:go/token.Token);
    If t20 6 8
  ]);
  (5, [
    t21 := TypeAssert (t1 CommaOk go/constant.int64Val);
    t22 := Extract (t21 0);
    t23 := Extract (t21 1);
    If t23 9 10
  ]);
  (6, [
    t24 := BinOp t17 "==" t19);
    Return (t24)
  ]);
  (7, [
    t25 := BinOp t17 "!=" t19);
    Return (t25)
  ]);
  (8, [
    t26 := BinOp op "==" 44:go/token.Token);
    If t26 7 1
  ]);
  (9, [
    t27 := TypeAssert (t2 NoCommaOk go/constant.int64Val);
    t28 := BinOp op "==" 39:go/token.Token);
    If t28 11 13
  ]);
  (10, [
    t29 := TypeAssert (t1 CommaOk go/constant.intVal);
    t30 := Extract (t29 0);
    t31 := Extract (t29 1);
    If t31 22 23
  ]);
  (11, [
    t32 := BinOp t22 "==" t27);
    Return (t32)
  ]);
  (12, [
    t33 := BinOp t22 "!=" t27);
    Return (t33)
  ]);
  (13, [
    t34 := BinOp op "==" 44:go/token.Token);
    If t34 12 15
  ]);
  (14, [
    t35 := BinOp t22 "<" t27);
    Return (t35)
  ]);
  (15, [
    t36 := BinOp op "==" 40:go/token.Token);
    If t36 14 17
  ]);
  (16, [
    t37 := BinOp t22 "<=" t27);
    Return (t37)
  ]);
  (17, [
    t38 := BinOp op "==" 45:go/token.Token);
    If t38 16 19
  ]);
  (18, [
    t39 := BinOp t22 ">" t27);
    Return (t39)
  ]);
  (19, [
    t40 := BinOp op "==" 41:go/token.Token);
    If t40 18 21
  ]);
  (20, [
    t41 := BinOp t22 ">=" t27);
    Return (t41)
  ]);
  (21, [
    t42 := BinOp op "==" 46:go/token.Token);
    If t42 20 1
  ]);
  (22, [
    t43 := Alloc (*x*) Local *go/constant.intVal;
    Store (t43 t30);
    t44 := FieldAddr (t43 0);
    t45 := UnOp (* t44);
    t46 := TypeAssert (t2 NoCommaOk go/constant.intVal);
    t47 := Field (t46 0);
    t48 := Call (Cmp t45 t47);
    t49 := Call (cmpZero t48 op);
    Return (t49)
  ]);
  (23, [
    t50 := TypeAssert (t1 CommaOk go/constant.ratVal);
    t51 := Extract (t50 0);
    t52 := Extract (t50 1);
    If t52 24 25
  ]);
  (24, [
    t53 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t53 t51);
    t54 := FieldAddr (t53 0);
    t55 := UnOp (* t54);
    t56 := TypeAssert (t2 NoCommaOk go/constant.ratVal);
    t57 := Field (t56 0);
    t58 := Call (Cmp t55 t57);
    t59 := Call (cmpZero t58 op);
    Return (t59)
  ]);
  (25, [
    t60 := TypeAssert (t1 CommaOk go/constant.floatVal);
    t61 := Extract (t60 0);
    t62 := Extract (t60 1);
    If t62 26 27
  ]);
  (26, [
    t63 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t63 t61);
    t64 := FieldAddr (t63 0);
    t65 := UnOp (* t64);
    t66 := TypeAssert (t2 NoCommaOk go/constant.floatVal);
    t67 := Field (t66 0);
    t68 := Call (Cmp t65 t67);
    t69 := Call (cmpZero t68 op);
    Return (t69)
  ]);
  (27, [
    t70 := TypeAssert (t1 CommaOk go/constant.complexVal);
    t71 := Extract (t70 0);
    t72 := Extract (t70 1);
    If t72 28 29
  ]);
  (28, [
    t73 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t73 t71);
    t74 := Alloc (*y*) Local *go/constant.complexVal;
    t75 := TypeAssert (t2 NoCommaOk go/constant.complexVal);
    Store (t74 t75);
    t76 := FieldAddr (t73 0);
    t77 := UnOp (* t76);
    t78 := FieldAddr (t74 0);
    t79 := UnOp (* t78);
    t80 := Call (Compare t77 39:go/token.Token t79);
    t81 := FieldAddr (t73 1);
    t82 := UnOp (* t81);
    t83 := FieldAddr (t74 1);
    t84 := UnOp (* t83);
    t85 := Call (Compare t82 39:go/token.Token t84);
    t86 := BinOp op "==" 39:go/token.Token);
    If t86 30 32
  ]);
  (29, [
    t87 := TypeAssert (t1 CommaOk *go/constant.stringVal);
    t88 := Extract (t87 0);
    t89 := Extract (t87 1);
    If t89 37 1
  ]);
  (30, [
    If t80 33 34
  ]);
  (31, [
    If t80 35 36
  ]);
  (32, [
    t90 := BinOp op "==" 44:go/token.Token);
    If t90 31 1
  ]);
  (33, [
    Jump 34
  ]);
  (34, [
    t91 := Phi (* && *) (false:bool t85);
    Return (t91)
  ]);
  (35, [
    t92 := UnOp (! t85);
    Jump 36
  ]);
  (36, [
    t93 := Phi (* || *) (true:bool t92);
    Return (t93)
  ]);
  (37, [
    t94 := Call (string t88);
    t95 := TypeAssert (t2 NoCommaOk *go/constant.stringVal);
    t96 := Call (string t95);
    t97 := BinOp op "==" 39:go/token.Token);
    If t97 38 40
  ]);
  (38, [
    t98 := BinOp t94 "==" t96);
    Return (t98)
  ]);
  (39, [
    t99 := BinOp t94 "!=" t96);
    Return (t99)
  ]);
  (40, [
    t100 := BinOp op "==" 44:go/token.Token);
    If t100 39 42
  ]);
  (41, [
    t101 := BinOp t94 "<" t96);
    Return (t101)
  ]);
  (42, [
    t102 := BinOp op "==" 40:go/token.Token);
    If t102 41 44
  ]);
  (43, [
    t103 := BinOp t94 "<=" t96);
    Return (t103)
  ]);
  (44, [
    t104 := BinOp op "==" 45:go/token.Token);
    If t104 43 46
  ]);
  (45, [
    t105 := BinOp t94 ">" t96);
    Return (t105)
  ]);
  (46, [
    t106 := BinOp op "==" 41:go/token.Token);
    If t106 45 48
  ]);
  (47, [
    t107 := BinOp t94 ">=" t96);
    Return (t107)
  ]);
  (48, [
    t108 := BinOp op "==" 46:go/token.Token);
    If t108 47 1
  ])
].

Definition Denom (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    t3 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t3)
  ]);
  (2, [
    t4 := MakeInterface (1:go/constant.int64Val 1:go/constant.int64Val);
    Return (t4)
  ]);
  (3, [
    t5 := TypeAssert (x CommaOk go/constant.intVal);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 2 4
  ]);
  (4, [
    t8 := TypeAssert (x CommaOk go/constant.ratVal);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    If t10 5 6
  ]);
  (5, [
    t11 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t11 t9);
    t12 := FieldAddr (t11 0);
    t13 := UnOp (* t12);
    t14 := Call (Denom t13);
    t15 := Call (makeInt t14);
    Return (t15)
  ]);
  (6, [
    t16 := TypeAssert (x CommaOk go/constant.floatVal);
    t17 := Extract (t16 0);
    t18 := Extract (t16 1);
    If t18 7 8
  ]);
  (7, [
    t19 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t19 t17);
    t20 := FieldAddr (t19 0);
    t21 := UnOp (* t20);
    t22 := Call (smallFloat t21);
    If t22 9 1
  ]);
  (8, [
    t23 := TypeAssert (x CommaOk go/constant.unknownVal);
    t24 := Extract (t23 0);
    t25 := Extract (t23 1);
    If t25 10 11
  ]);
  (9, [
    t26 := FieldAddr (t19 0);
    t27 := UnOp (* t26);
    t28 := Call (Rat t27 nil:*math/big.Rat);
    t29 := Extract (t28 0);
    t30 := Extract (t28 1);
    t31 := Call (Denom t29);
    t32 := Call (makeInt t31);
    Return (t32)
  ]);
  (10, [
    Jump 1
  ]);
  (11, [
    t33 := Alloc (*varargs*) Heap *[1]any;
    t34 := IndexAddr (t33 0:int);
    t35 := ChangeInterface (x);
    Store (t34 t35);
    t36 := Slice (t33);
    t37 := Call (Sprintf "%v not Int or Float":string t36);
    t38 := MakeInterface (t37 t37);
    Panic (t38)
  ])
].

Definition Float32Val (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := Convert (t1);
    t4 := Convert (t3);
    t5 := BinOp t4 "==" t1);
    Return (t3 t5)
  ]);
  (2, [
    t6 := TypeAssert (x CommaOk go/constant.intVal);
    t7 := Extract (t6 0);
    t8 := Extract (t6 1);
    If t8 3 4
  ]);
  (3, [
    t9 := Alloc (*x*) Local *go/constant.intVal;
    Store (t9 t7);
    t10 := Call (newFloat );
    t11 := FieldAddr (t9 0);
    t12 := UnOp (* t11);
    t13 := Call (SetInt t10 t12);
    t14 := Call (Float32 t13);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    t17 := BinOp t16 "==" 0:math/big.Accuracy);
    Return (t15 t17)
  ]);
  (4, [
    t18 := TypeAssert (x CommaOk go/constant.ratVal);
    t19 := Extract (t18 0);
    t20 := Extract (t18 1);
    If t20 5 6
  ]);
  (5, [
    t21 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t21 t19);
    t22 := FieldAddr (t21 0);
    t23 := UnOp (* t22);
    t24 := Call (Float32 t23);
    t25 := Extract (t24 0);
    t26 := Extract (t24 1);
    Return (t25 t26)
  ]);
  (6, [
    t27 := TypeAssert (x CommaOk go/constant.floatVal);
    t28 := Extract (t27 0);
    t29 := Extract (t27 1);
    If t29 7 8
  ]);
  (7, [
    t30 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t30 t28);
    t31 := FieldAddr (t30 0);
    t32 := UnOp (* t31);
    t33 := Call (Float32 t32);
    t34 := Extract (t33 0);
    t35 := Extract (t33 1);
    t36 := BinOp t35 "==" 0:math/big.Accuracy);
    Return (t34 t36)
  ]);
  (8, [
    t37 := TypeAssert (x CommaOk go/constant.unknownVal);
    t38 := Extract (t37 0);
    t39 := Extract (t37 1);
    If t39 9 10
  ]);
  (9, [
    Return (0:float32 false:bool)
  ]);
  (10, [
    t40 := Alloc (*varargs*) Heap *[1]any;
    t41 := IndexAddr (t40 0:int);
    t42 := ChangeInterface (x);
    Store (t41 t42);
    t43 := Slice (t40);
    t44 := Call (Sprintf "%v not a Float":string t43);
    t45 := MakeInterface (t44 t44);
    Panic (t45)
  ])
].

Definition Float64Val (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := ChangeType (t1);
    t4 := Convert (t3);
    t5 := Convert (t4);
    t6 := BinOp t5 "==" t1);
    Return (t4 t6)
  ]);
  (2, [
    t7 := TypeAssert (x CommaOk go/constant.intVal);
    t8 := Extract (t7 0);
    t9 := Extract (t7 1);
    If t9 3 4
  ]);
  (3, [
    t10 := Alloc (*x*) Local *go/constant.intVal;
    Store (t10 t8);
    t11 := Call (newFloat );
    t12 := FieldAddr (t10 0);
    t13 := UnOp (* t12);
    t14 := Call (SetInt t11 t13);
    t15 := Call (Float64 t14);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    t18 := BinOp t17 "==" 0:math/big.Accuracy);
    Return (t16 t18)
  ]);
  (4, [
    t19 := TypeAssert (x CommaOk go/constant.ratVal);
    t20 := Extract (t19 0);
    t21 := Extract (t19 1);
    If t21 5 6
  ]);
  (5, [
    t22 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t22 t20);
    t23 := FieldAddr (t22 0);
    t24 := UnOp (* t23);
    t25 := Call (Float64 t24);
    t26 := Extract (t25 0);
    t27 := Extract (t25 1);
    Return (t26 t27)
  ]);
  (6, [
    t28 := TypeAssert (x CommaOk go/constant.floatVal);
    t29 := Extract (t28 0);
    t30 := Extract (t28 1);
    If t30 7 8
  ]);
  (7, [
    t31 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t31 t29);
    t32 := FieldAddr (t31 0);
    t33 := UnOp (* t32);
    t34 := Call (Float64 t33);
    t35 := Extract (t34 0);
    t36 := Extract (t34 1);
    t37 := BinOp t36 "==" 0:math/big.Accuracy);
    Return (t35 t37)
  ]);
  (8, [
    t38 := TypeAssert (x CommaOk go/constant.unknownVal);
    t39 := Extract (t38 0);
    t40 := Extract (t38 1);
    If t40 9 10
  ]);
  (9, [
    Return (0:float64 false:bool)
  ]);
  (10, [
    t41 := Alloc (*varargs*) Heap *[1]any;
    t42 := IndexAddr (t41 0:int);
    t43 := ChangeInterface (x);
    Store (t42 t43);
    t44 := Slice (t41);
    t45 := Call (Sprintf "%v not a Float":string t44);
    t46 := MakeInterface (t45 t45);
    Panic (t46)
  ])
].

Definition Imag (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.unknownVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := MakeInterface (t1 t1);
    Return (t3)
  ]);
  (2, [
    t4 := TypeAssert (x CommaOk go/constant.int64Val);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 3 4
  ]);
  (3, [
    t7 := MakeInterface (0:go/constant.int64Val 0:go/constant.int64Val);
    Return (t7)
  ]);
  (4, [
    t8 := TypeAssert (x CommaOk go/constant.intVal);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    If t10 3 5
  ]);
  (5, [
    t11 := TypeAssert (x CommaOk go/constant.ratVal);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 3 6
  ]);
  (6, [
    t14 := TypeAssert (x CommaOk go/constant.floatVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 3 7
  ]);
  (7, [
    t17 := TypeAssert (x CommaOk go/constant.complexVal);
    t18 := Extract (t17 0);
    t19 := Extract (t17 1);
    If t19 8 9
  ]);
  (8, [
    t20 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t20 t18);
    t21 := FieldAddr (t20 1);
    t22 := UnOp (* t21);
    Return (t22)
  ]);
  (9, [
    t23 := Alloc (*varargs*) Heap *[1]any;
    t24 := IndexAddr (t23 0:int);
    t25 := ChangeInterface (x);
    Store (t24 t25);
    t26 := Slice (t23);
    t27 := Call (Sprintf "%v not numeric":string t26);
    t28 := MakeInterface (t27 t27);
    Panic (t28)
  ])
].

Definition Int64Val (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := ChangeType (t1);
    Return (t3 true:bool)
  ]);
  (2, [
    t4 := TypeAssert (x CommaOk go/constant.intVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 3 4
  ]);
  (3, [
    t7 := Alloc (*x*) Local *go/constant.intVal;
    Store (t7 t5);
    t8 := FieldAddr (t7 0);
    t9 := UnOp (* t8);
    t10 := Call (Int64 t9);
    Return (t10 false:bool)
  ]);
  (4, [
    t11 := TypeAssert (x CommaOk go/constant.unknownVal);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 5 6
  ]);
  (5, [
    Return (0:int64 false:bool)
  ]);
  (6, [
    t14 := Alloc (*varargs*) Heap *[1]any;
    t15 := IndexAddr (t14 0:int);
    t16 := ChangeInterface (x);
    Store (t15 t16);
    t17 := Slice (t14);
    t18 := Call (Sprintf "%v not an Int":string t17);
    t19 := MakeInterface (t18 t18);
    Panic (t19)
  ])
].

Definition Make (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk bool);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := ChangeType (t1);
    t4 := MakeInterface (t3 t3);
    Return (t4)
  ]);
  (2, [
    t5 := TypeAssert (x CommaOk string);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 3 4
  ]);
  (3, [
    t8 := Alloc (*complit*) Heap *go/constant.stringVal;
    t9 := FieldAddr (t8 1);
    Store (t9 t6);
    t10 := MakeInterface (t8 t8);
    Return (t10)
  ]);
  (4, [
    t11 := TypeAssert (x CommaOk int64);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 5 6
  ]);
  (5, [
    t14 := ChangeType (t12);
    t15 := MakeInterface (t14 t14);
    Return (t15)
  ]);
  (6, [
    t16 := TypeAssert (x CommaOk *math/big.Int);
    t17 := Extract (t16 0);
    t18 := Extract (t16 1);
    If t18 7 8
  ]);
  (7, [
    t19 := Call (makeInt t17);
    Return (t19)
  ]);
  (8, [
    t20 := TypeAssert (x CommaOk *math/big.Rat);
    t21 := Extract (t20 0);
    t22 := Extract (t20 1);
    If t22 9 10
  ]);
  (9, [
    t23 := Call (makeRat t21);
    Return (t23)
  ]);
  (10, [
    t24 := TypeAssert (x CommaOk *math/big.Float);
    t25 := Extract (t24 0);
    t26 := Extract (t24 1);
    If t26 11 12
  ]);
  (11, [
    t27 := Call (makeFloat t25);
    Return (t27)
  ]);
  (12, [
    t28 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t28)
  ])
].

Definition MakeBool (b : Val.t) : FunctionBody.t := [
  (0, [
    t0 := ChangeType (b);
    t1 := MakeInterface (t0 t0);
    Return (t1)
  ])
].

Definition MakeFloat64 (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (IsInf x 0:int);
    If t0 1 3
  ]);
  (1, [
    t1 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t1)
  ]);
  (2, [
    t2 := Call (smallFloat64 x);
    If t2 4 5
  ]);
  (3, [
    t3 := Call (IsNaN x);
    If t3 1 2
  ]);
  (4, [
    t4 := Alloc (*complit*) Local *go/constant.ratVal;
    t5 := FieldAddr (t4 0);
    t6 := Call (newRat );
    t7 := BinOp x "+" 0:float64);
    t8 := Call (SetFloat64 t6 t7);
    Store (t5 t8);
    t9 := UnOp (* t4);
    t10 := MakeInterface (t9 t9);
    Return (t10)
  ]);
  (5, [
    t11 := Alloc (*complit*) Local *go/constant.floatVal;
    t12 := FieldAddr (t11 0);
    t13 := Call (newFloat );
    t14 := BinOp x "+" 0:float64);
    t15 := Call (SetFloat64 t13 t14);
    Store (t12 t15);
    t16 := UnOp (* t11);
    t17 := MakeInterface (t16 t16);
    Return (t17)
  ])
].

Definition MakeFromBytes (bytes : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (len bytes);
    t1 := BinOp t0 "+" 7:int);
    t2 := BinOp t1 "/" 8:int);
    t3 := MakeSlice (t2 t2);
    t4 := Call (len bytes);
    Jump 1
  ]);
  (1, [
    t5 := Phi (* i *) (0:int t5 t21);
    t6 := Phi (* w *) (0:math/big.Word t15 0:math/big.Word);
    t7 := Phi (* s *) (0:uint t16 0:uint);
    t8 := Phi (* rangeindex *) (-1:int t9 t9);
    t9 := BinOp t8 "+" 1:int);
    t10 := BinOp t9 "<" t4);
    If t10 2 3
  ]);
  (2, [
    t11 := IndexAddr (bytes t9);
    t12 := UnOp (* t11);
    t13 := Convert (t12);
    t14 := BinOp t13 "<<" t7);
    t15 := BinOp t6 "|" t14);
    t16 := BinOp t7 "+" 8:uint);
    t17 := BinOp t16 "==" 64:uint);
    If t17 4 1
  ]);
  (3, [
    t18 := Call (len t3);
    t19 := BinOp t5 "<" t18);
    If t19 5 8
  ]);
  (4, [
    t20 := IndexAddr (t3 t5);
    Store (t20 t15);
    t21 := BinOp t5 "+" 1:int);
    Jump 1
  ]);
  (5, [
    t22 := IndexAddr (t3 t5);
    Store (t22 t6);
    t23 := BinOp t5 "+" 1:int);
    Jump 8
  ]);
  (6, [
    t24 := BinOp t29 "-" 1:int);
    Jump 8
  ]);
  (7, [
    t25 := Call (newInt );
    t26 := Slice (t3 t29);
    t27 := Call (SetBits t25 t26);
    t28 := Call (makeInt t27);
    Return (t28)
  ]);
  (8, [
    t29 := Phi (* i *) (t5 t24 t23);
    t30 := BinOp t29 ">" 0:int);
    If t30 9 7
  ]);
  (9, [
    t31 := BinOp t29 "-" 1:int);
    t32 := IndexAddr (t3 t31);
    t33 := UnOp (* t32);
    t34 := BinOp t33 "==" 0:math/big.Word);
    If t34 6 7
  ])
].

Definition MakeFromLiteral (lit tok zero : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp zero "!=" 0:uint);
    If t0 1 2
  ]);
  (1, [
    t1 := MakeInterface ("MakeFromLiteral c...":string "MakeFromLiteral c...":string);
    Panic (t1)
  ]);
  (2, [
    t2 := BinOp tok "==" 5:go/token.Token);
    If t2 4 6
  ]);
  (3, [
    t3 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t3)
  ]);
  (4, [
    t4 := Call (ParseInt lit 0:int 64:int);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    t7 := BinOp t6 "==" nil:error);
    If t7 7 8
  ]);
  (5, [
    t8 := Call (makeFloatFromLiteral lit);
    t9 := BinOp t8 "!=" nil:go/constant.Value);
    If t9 12 3
  ]);
  (6, [
    t10 := BinOp tok "==" 6:go/token.Token);
    If t10 5 11
  ]);
  (7, [
    t11 := ChangeType (t5);
    t12 := MakeInterface (t11 t11);
    Return (t12)
  ]);
  (8, [
    t13 := Call (newInt );
    t14 := Call (SetString t13 lit 0:int);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 9 3
  ]);
  (9, [
    t17 := Alloc (*complit*) Local *go/constant.intVal;
    t18 := FieldAddr (t17 0);
    Store (t18 t15);
    t19 := UnOp (* t17);
    t20 := MakeInterface (t19 t19);
    Return (t20)
  ]);
  (10, [
    t21 := Call (len lit);
    t22 := BinOp t21 ">" 0:int);
    If t22 16 3
  ]);
  (11, [
    t23 := BinOp tok "==" 7:go/token.Token);
    If t23 10 14
  ]);
  (12, [
    Return (t8)
  ]);
  (13, [
    t24 := Call (len lit);
    t25 := BinOp t24 ">=" 2:int);
    If t25 20 3
  ]);
  (14, [
    t26 := BinOp tok "==" 8:go/token.Token);
    If t26 13 19
  ]);
  (15, [
    t27 := BinOp t21 "-" 1:int);
    t28 := Slice (lit t27);
    t29 := Call (makeFloatFromLiteral t28);
    t30 := BinOp t29 "!=" nil:go/constant.Value);
    If t30 17 3
  ]);
  (16, [
    t31 := BinOp t21 "-" 1:int);
    t32 := Index (lit t31);
    t33 := BinOp t32 "==" 105:byte);
    If t33 15 3
  ]);
  (17, [
    t34 := MakeInterface (0:go/constant.int64Val 0:go/constant.int64Val);
    t35 := Call (makeComplex t34 t29);
    Return (t35)
  ]);
  (18, [
    t36 := Call (Unquote lit);
    t37 := Extract (t36 0);
    t38 := Extract (t36 1);
    t39 := BinOp t38 "==" nil:error);
    If t39 23 3
  ]);
  (19, [
    t40 := BinOp tok "==" 9:go/token.Token);
    If t40 18 22
  ]);
  (20, [
    t41 := BinOp t24 "-" 1:int);
    t42 := Slice (lit 1:int t41);
    t43 := Call (UnquoteChar t42 39:byte);
    t44 := Extract (t43 0);
    t45 := Extract (t43 1);
    t46 := Extract (t43 2);
    t47 := Extract (t43 3);
    t48 := BinOp t47 "==" nil:error);
    If t48 21 3
  ]);
  (21, [
    t49 := Convert (t44);
    t50 := Call (MakeInt64 t49);
    Return (t50)
  ]);
  (22, [
    t51 := Alloc (*varargs*) Heap *[1]any;
    t52 := IndexAddr (t51 0:int);
    t53 := MakeInterface (tok tok);
    Store (t52 t53);
    t54 := Slice (t51);
    t55 := Call (Sprintf "%v is not a valid...":string t54);
    t56 := MakeInterface (t55 t55);
    Panic (t56)
  ]);
  (23, [
    t57 := Call (MakeString t37);
    Return (t57)
  ])
].

Definition MakeImag (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.unknownVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    Return (x)
  ]);
  (2, [
    t3 := TypeAssert (x CommaOk go/constant.int64Val);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 3 4
  ]);
  (3, [
    t6 := MakeInterface (0:go/constant.int64Val 0:go/constant.int64Val);
    t7 := Call (makeComplex t6 x);
    Return (t7)
  ]);
  (4, [
    t8 := TypeAssert (x CommaOk go/constant.intVal);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    If t10 3 5
  ]);
  (5, [
    t11 := TypeAssert (x CommaOk go/constant.ratVal);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 3 6
  ]);
  (6, [
    t14 := TypeAssert (x CommaOk go/constant.floatVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 3 7
  ]);
  (7, [
    t17 := Alloc (*varargs*) Heap *[1]any;
    t18 := IndexAddr (t17 0:int);
    t19 := ChangeInterface (x);
    Store (t18 t19);
    t20 := Slice (t17);
    t21 := Call (Sprintf "%v not Int or Float":string t20);
    t22 := MakeInterface (t21 t21);
    Panic (t22)
  ])
].

Definition MakeInt64 (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := ChangeType (x);
    t1 := MakeInterface (t0 t0);
    Return (t1)
  ])
].

Definition MakeString (s : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp s "==" "":string);
    If t0 1 2
  ]);
  (1, [
    t1 := MakeInterface (emptyString emptyString);
    Return (t1)
  ]);
  (2, [
    t2 := Alloc (*complit*) Heap *go/constant.stringVal;
    t3 := FieldAddr (t2 1);
    Store (t3 s);
    t4 := MakeInterface (t2 t2);
    Return (t4)
  ])
].

Definition MakeUint64 (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp x "<" 9223372036854775808:uint64);
    If t0 1 2
  ]);
  (1, [
    t1 := Convert (x);
    t2 := ChangeType (t1);
    t3 := MakeInterface (t2 t2);
    Return (t3)
  ]);
  (2, [
    t4 := Alloc (*complit*) Local *go/constant.intVal;
    t5 := FieldAddr (t4 0);
    t6 := Call (newInt );
    t7 := Call (SetUint64 t6 x);
    Store (t5 t7);
    t8 := UnOp (* t4);
    t9 := MakeInterface (t8 t8);
    Return (t9)
  ])
].

Definition MakeUnknown ( : Val.t) : FunctionBody.t := [
  (0, [
    t0 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t0)
  ])
].

Definition Num (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    t3 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t3)
  ]);
  (2, [
    Return (x)
  ]);
  (3, [
    t4 := TypeAssert (x CommaOk go/constant.intVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 2 4
  ]);
  (4, [
    t7 := TypeAssert (x CommaOk go/constant.ratVal);
    t8 := Extract (t7 0);
    t9 := Extract (t7 1);
    If t9 5 6
  ]);
  (5, [
    t10 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t10 t8);
    t11 := FieldAddr (t10 0);
    t12 := UnOp (* t11);
    t13 := Call (Num t12);
    t14 := Call (makeInt t13);
    Return (t14)
  ]);
  (6, [
    t15 := TypeAssert (x CommaOk go/constant.floatVal);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    If t17 7 8
  ]);
  (7, [
    t18 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t18 t16);
    t19 := FieldAddr (t18 0);
    t20 := UnOp (* t19);
    t21 := Call (smallFloat t20);
    If t21 9 1
  ]);
  (8, [
    t22 := TypeAssert (x CommaOk go/constant.unknownVal);
    t23 := Extract (t22 0);
    t24 := Extract (t22 1);
    If t24 10 11
  ]);
  (9, [
    t25 := FieldAddr (t18 0);
    t26 := UnOp (* t25);
    t27 := Call (Rat t26 nil:*math/big.Rat);
    t28 := Extract (t27 0);
    t29 := Extract (t27 1);
    t30 := Call (Num t28);
    t31 := Call (makeInt t30);
    Return (t31)
  ]);
  (10, [
    Jump 1
  ]);
  (11, [
    t32 := Alloc (*varargs*) Heap *[1]any;
    t33 := IndexAddr (t32 0:int);
    t34 := ChangeInterface (x);
    Store (t33 t34);
    t35 := Slice (t32);
    t36 := Call (Sprintf "%v not Int or Float":string t35);
    t37 := MakeInterface (t36 t36);
    Panic (t37)
  ])
].

Definition Real (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.unknownVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    Return (x)
  ]);
  (2, [
    t3 := TypeAssert (x CommaOk go/constant.int64Val);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 1 3
  ]);
  (3, [
    t6 := TypeAssert (x CommaOk go/constant.intVal);
    t7 := Extract (t6 0);
    t8 := Extract (t6 1);
    If t8 1 4
  ]);
  (4, [
    t9 := TypeAssert (x CommaOk go/constant.ratVal);
    t10 := Extract (t9 0);
    t11 := Extract (t9 1);
    If t11 1 5
  ]);
  (5, [
    t12 := TypeAssert (x CommaOk go/constant.floatVal);
    t13 := Extract (t12 0);
    t14 := Extract (t12 1);
    If t14 1 6
  ]);
  (6, [
    t15 := TypeAssert (x CommaOk go/constant.complexVal);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    If t17 7 8
  ]);
  (7, [
    t18 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t18 t16);
    t19 := FieldAddr (t18 0);
    t20 := UnOp (* t19);
    Return (t20)
  ]);
  (8, [
    t21 := Alloc (*varargs*) Heap *[1]any;
    t22 := IndexAddr (t21 0:int);
    t23 := ChangeInterface (x);
    Store (t22 t23);
    t24 := Slice (t21);
    t25 := Call (Sprintf "%v not numeric":string t24);
    t26 := MakeInterface (t25 t25);
    Panic (t26)
  ])
].

Definition Shift (x op s : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.unknownVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    t3 := Alloc (*varargs*) Heap *[3]any;
    t4 := IndexAddr (t3 0:int);
    t5 := ChangeInterface (x);
    Store (t4 t5);
    t6 := IndexAddr (t3 1:int);
    t7 := MakeInterface (op op);
    Store (t6 t7);
    t8 := IndexAddr (t3 2:int);
    t9 := MakeInterface (s s);
    Store (t8 t9);
    t10 := Slice (t3);
    t11 := Call (Sprintf "invalid shift %v ...":string t10);
    t12 := MakeInterface (t11 t11);
    Panic (t12)
  ]);
  (2, [
    t13 := MakeInterface (t1 t1);
    Return (t13)
  ]);
  (3, [
    t14 := TypeAssert (x CommaOk go/constant.int64Val);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 4 5
  ]);
  (4, [
    t17 := BinOp s "==" 0:uint);
    If t17 6 7
  ]);
  (5, [
    t18 := TypeAssert (x CommaOk go/constant.intVal);
    t19 := Extract (t18 0);
    t20 := Extract (t18 1);
    If t20 11 1
  ]);
  (6, [
    t21 := MakeInterface (t15 t15);
    Return (t21)
  ]);
  (7, [
    t22 := BinOp op "==" 20:go/token.Token);
    If t22 8 10
  ]);
  (8, [
    t23 := Call (i64toi t15);
    t24 := Field (t23 0);
    t25 := Call (Lsh t24 t24 s);
    t26 := Call (makeInt t25);
    Return (t26)
  ]);
  (9, [
    t27 := BinOp t15 ">>" s);
    t28 := MakeInterface (t27 t27);
    Return (t28)
  ]);
  (10, [
    t29 := BinOp op "==" 21:go/token.Token);
    If t29 9 1
  ]);
  (11, [
    t30 := Alloc (*x*) Local *go/constant.intVal;
    Store (t30 t19);
    t31 := BinOp s "==" 0:uint);
    If t31 12 13
  ]);
  (12, [
    t32 := UnOp (* t30);
    t33 := MakeInterface (t32 t32);
    Return (t33)
  ]);
  (13, [
    t34 := Call (newInt );
    t35 := BinOp op "==" 20:go/token.Token);
    If t35 14 16
  ]);
  (14, [
    t36 := FieldAddr (t30 0);
    t37 := UnOp (* t36);
    t38 := Call (Lsh t34 t37 s);
    t39 := Call (makeInt t38);
    Return (t39)
  ]);
  (15, [
    t40 := FieldAddr (t30 0);
    t41 := UnOp (* t40);
    t42 := Call (Rsh t34 t41 s);
    t43 := Call (makeInt t42);
    Return (t43)
  ]);
  (16, [
    t44 := BinOp op "==" 21:go/token.Token);
    If t44 15 1
  ])
].

Definition Sign (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := BinOp t1 "<" 0:go/constant.int64Val);
    If t3 3 5
  ]);
  (2, [
    t4 := TypeAssert (x CommaOk go/constant.intVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 7 8
  ]);
  (3, [
    Return (-1:int)
  ]);
  (4, [
    Return (1:int)
  ]);
  (5, [
    t7 := BinOp t1 ">" 0:go/constant.int64Val);
    If t7 4 6
  ]);
  (6, [
    Return (0:int)
  ]);
  (7, [
    t8 := Alloc (*x*) Local *go/constant.intVal;
    Store (t8 t5);
    t9 := FieldAddr (t8 0);
    t10 := UnOp (* t9);
    t11 := Call (Sign t10);
    Return (t11)
  ]);
  (8, [
    t12 := TypeAssert (x CommaOk go/constant.ratVal);
    t13 := Extract (t12 0);
    t14 := Extract (t12 1);
    If t14 9 10
  ]);
  (9, [
    t15 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t15 t13);
    t16 := FieldAddr (t15 0);
    t17 := UnOp (* t16);
    t18 := Call (Sign t17);
    Return (t18)
  ]);
  (10, [
    t19 := TypeAssert (x CommaOk go/constant.floatVal);
    t20 := Extract (t19 0);
    t21 := Extract (t19 1);
    If t21 11 12
  ]);
  (11, [
    t22 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t22 t20);
    t23 := FieldAddr (t22 0);
    t24 := UnOp (* t23);
    t25 := Call (Sign t24);
    Return (t25)
  ]);
  (12, [
    t26 := TypeAssert (x CommaOk go/constant.complexVal);
    t27 := Extract (t26 0);
    t28 := Extract (t26 1);
    If t28 13 14
  ]);
  (13, [
    t29 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t29 t27);
    t30 := FieldAddr (t29 0);
    t31 := UnOp (* t30);
    t32 := Call (Sign t31);
    t33 := FieldAddr (t29 1);
    t34 := UnOp (* t33);
    t35 := Call (Sign t34);
    t36 := BinOp t32 "|" t35);
    Return (t36)
  ]);
  (14, [
    t37 := TypeAssert (x CommaOk go/constant.unknownVal);
    t38 := Extract (t37 0);
    t39 := Extract (t37 1);
    If t39 15 16
  ]);
  (15, [
    Return (1:int)
  ]);
  (16, [
    t40 := Alloc (*varargs*) Heap *[1]any;
    t41 := IndexAddr (t40 0:int);
    t42 := ChangeInterface (x);
    Store (t41 t42);
    t43 := Slice (t40);
    t44 := Call (Sprintf "%v not numeric":string t43);
    t45 := MakeInterface (t44 t44);
    Panic (t45)
  ])
].

Definition StringVal (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk *go/constant.stringVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := Call (string t1);
    Return (t3)
  ]);
  (2, [
    t4 := TypeAssert (x CommaOk go/constant.unknownVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 3 4
  ]);
  (3, [
    Return ("":string)
  ]);
  (4, [
    t7 := Alloc (*varargs*) Heap *[1]any;
    t8 := IndexAddr (t7 0:int);
    t9 := ChangeInterface (x);
    Store (t8 t9);
    t10 := Slice (t7);
    t11 := Call (Sprintf "%v not a String":string t10);
    t12 := MakeInterface (t11 t11);
    Panic (t12)
  ])
].

Definition ToComplex (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := Call (vtoc x);
    t4 := MakeInterface (t3 t3);
    Return (t4)
  ]);
  (2, [
    t5 := TypeAssert (x CommaOk go/constant.intVal);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 1 3
  ]);
  (3, [
    t8 := TypeAssert (x CommaOk go/constant.ratVal);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    If t10 1 4
  ]);
  (4, [
    t11 := TypeAssert (x CommaOk go/constant.floatVal);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 1 5
  ]);
  (5, [
    t14 := TypeAssert (x CommaOk go/constant.complexVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 6 7
  ]);
  (6, [
    t17 := MakeInterface (t15 t15);
    Return (t17)
  ]);
  (7, [
    t18 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t18)
  ])
].

Definition ToFloat (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    t3 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t3)
  ]);
  (2, [
    t4 := Call (i64tor t1);
    t5 := MakeInterface (t4 t4);
    Return (t5)
  ]);
  (3, [
    t6 := TypeAssert (x CommaOk go/constant.intVal);
    t7 := Extract (t6 0);
    t8 := Extract (t6 1);
    If t8 4 5
  ]);
  (4, [
    t9 := Alloc (*x*) Local *go/constant.intVal;
    Store (t9 t7);
    t10 := FieldAddr (t9 0);
    t11 := UnOp (* t10);
    t12 := Call (smallInt t11);
    If t12 6 7
  ]);
  (5, [
    t13 := TypeAssert (x CommaOk go/constant.ratVal);
    t14 := Extract (t13 0);
    t15 := Extract (t13 1);
    If t15 8 9
  ]);
  (6, [
    t16 := UnOp (* t9);
    t17 := Call (itor t16);
    t18 := MakeInterface (t17 t17);
    Return (t18)
  ]);
  (7, [
    t19 := UnOp (* t9);
    t20 := Call (itof t19);
    t21 := MakeInterface (t20 t20);
    Return (t21)
  ]);
  (8, [
    Return (x)
  ]);
  (9, [
    t22 := TypeAssert (x CommaOk go/constant.floatVal);
    t23 := Extract (t22 0);
    t24 := Extract (t22 1);
    If t24 8 10
  ]);
  (10, [
    t25 := TypeAssert (x CommaOk go/constant.complexVal);
    t26 := Extract (t25 0);
    t27 := Extract (t25 1);
    If t27 11 1
  ]);
  (11, [
    t28 := Alloc (*x*) Local *go/constant.complexVal;
    Store (t28 t26);
    t29 := FieldAddr (t28 1);
    t30 := UnOp (* t29);
    t31 := Call (Sign t30);
    t32 := BinOp t31 "==" 0:int);
    If t32 12 1
  ]);
  (12, [
    t33 := FieldAddr (t28 0);
    t34 := UnOp (* t33);
    t35 := Call (ToFloat t34);
    Return (t35)
  ])
].

Definition ToInt (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    t3 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t3)
  ]);
  (2, [
    Return (x)
  ]);
  (3, [
    t4 := TypeAssert (x CommaOk go/constant.intVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 2 4
  ]);
  (4, [
    t7 := TypeAssert (x CommaOk go/constant.ratVal);
    t8 := Extract (t7 0);
    t9 := Extract (t7 1);
    If t9 5 6
  ]);
  (5, [
    t10 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t10 t8);
    t11 := FieldAddr (t10 0);
    t12 := UnOp (* t11);
    t13 := Call (IsInt t12);
    If t13 7 1
  ]);
  (6, [
    t14 := TypeAssert (x CommaOk go/constant.floatVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 8 9
  ]);
  (7, [
    t17 := FieldAddr (t10 0);
    t18 := UnOp (* t17);
    t19 := Call (Num t18);
    t20 := Call (makeInt t19);
    Return (t20)
  ]);
  (8, [
    t21 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t21 t15);
    t22 := FieldAddr (t21 0);
    t23 := UnOp (* t22);
    t24 := Call (smallFloat t23);
    If t24 10 1
  ]);
  (9, [
    t25 := TypeAssert (x CommaOk go/constant.complexVal);
    t26 := Extract (t25 0);
    t27 := Extract (t25 1);
    If t27 16 1
  ]);
  (10, [
    t28 := Call (newInt );
    t29 := FieldAddr (t21 0);
    t30 := UnOp (* t29);
    t31 := Call (Int t30 t28);
    t32 := Extract (t31 0);
    t33 := Extract (t31 1);
    t34 := BinOp t33 "==" 0:math/big.Accuracy);
    If t34 11 12
  ]);
  (11, [
    t35 := Call (makeInt t28);
    Return (t35)
  ]);
  (12, [
    t36 := Alloc (*t*) Heap *math/big.Float;
    t37 := Call (SetPrec t36 508:uint);
    t38 := Call (SetMode t36 2:math/big.RoundingMode);
    t39 := FieldAddr (t21 0);
    t40 := UnOp (* t39);
    t41 := Call (Set t36 t40);
    t42 := Call (Int t36 t28);
    t43 := Extract (t42 0);
    t44 := Extract (t42 1);
    t45 := BinOp t44 "==" 0:math/big.Accuracy);
    If t45 13 14
  ]);
  (13, [
    t46 := Call (makeInt t28);
    Return (t46)
  ]);
  (14, [
    t47 := Call (SetMode t36 3:math/big.RoundingMode);
    t48 := FieldAddr (t21 0);
    t49 := UnOp (* t48);
    t50 := Call (Set t36 t49);
    t51 := Call (Int t36 t28);
    t52 := Extract (t51 0);
    t53 := Extract (t51 1);
    t54 := BinOp t53 "==" 0:math/big.Accuracy);
    If t54 15 1
  ]);
  (15, [
    t55 := Call (makeInt t28);
    Return (t55)
  ]);
  (16, [
    t56 := MakeInterface (t26 t26);
    t57 := Call (ToFloat t56);
    t58 := Call (t57 );
    t59 := BinOp t58 "==" 4:go/constant.Kind);
    If t59 17 1
  ]);
  (17, [
    t60 := Call (ToInt t57);
    Return (t60)
  ])
].

Definition Uint64Val (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.int64Val);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := Convert (t1);
    t4 := BinOp t1 ">=" 0:go/constant.int64Val);
    Return (t3 t4)
  ]);
  (2, [
    t5 := TypeAssert (x CommaOk go/constant.intVal);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 3 4
  ]);
  (3, [
    t8 := Alloc (*x*) Local *go/constant.intVal;
    Store (t8 t6);
    t9 := FieldAddr (t8 0);
    t10 := UnOp (* t9);
    t11 := Call (Uint64 t10);
    t12 := FieldAddr (t8 0);
    t13 := UnOp (* t12);
    t14 := Call (IsUint64 t13);
    Return (t11 t14)
  ]);
  (4, [
    t15 := TypeAssert (x CommaOk go/constant.unknownVal);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    If t17 5 6
  ]);
  (5, [
    Return (0:uint64 false:bool)
  ]);
  (6, [
    t18 := Alloc (*varargs*) Heap *[1]any;
    t19 := IndexAddr (t18 0:int);
    t20 := ChangeInterface (x);
    Store (t19 t20);
    t21 := Slice (t18);
    t22 := Call (Sprintf "%v not an Int":string t21);
    t23 := MakeInterface (t22 t22);
    Panic (t23)
  ])
].

Definition UnaryOp (op y prec : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp op "==" 12:go/token.Token);
    If t0 1 3
  ]);
  (1, [
    t1 := TypeAssert (y CommaOk go/constant.unknownVal);
    t2 := Extract (t1 0);
    t3 := Extract (t1 1);
    If t3 4 5
  ]);
  (2, [
    t4 := TypeAssert (y CommaOk go/constant.unknownVal);
    t5 := Extract (t4 0);
    t6 := Extract (t4 1);
    If t6 12 13
  ]);
  (3, [
    t7 := BinOp op "==" 13:go/token.Token);
    If t7 2 11
  ]);
  (4, [
    Return (y)
  ]);
  (5, [
    t8 := TypeAssert (y CommaOk go/constant.int64Val);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    If t10 4 6
  ]);
  (6, [
    t11 := TypeAssert (y CommaOk go/constant.intVal);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 4 7
  ]);
  (7, [
    t14 := TypeAssert (y CommaOk go/constant.ratVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 4 8
  ]);
  (8, [
    t17 := TypeAssert (y CommaOk go/constant.floatVal);
    t18 := Extract (t17 0);
    t19 := Extract (t17 1);
    If t19 4 9
  ]);
  (9, [
    t20 := TypeAssert (y CommaOk go/constant.complexVal);
    t21 := Extract (t20 0);
    t22 := Extract (t20 1);
    If t22 4 34
  ]);
  (10, [
    t23 := Call (newInt );
    t24 := TypeAssert (y CommaOk go/constant.unknownVal);
    t25 := Extract (t24 0);
    t26 := Extract (t24 1);
    If t26 28 29
  ]);
  (11, [
    t27 := BinOp op "==" 19:go/token.Token);
    If t27 10 26
  ]);
  (12, [
    t28 := MakeInterface (t5 t5);
    Return (t28)
  ]);
  (13, [
    t29 := TypeAssert (y CommaOk go/constant.int64Val);
    t30 := Extract (t29 0);
    t31 := Extract (t29 1);
    If t31 14 15
  ]);
  (14, [
    t32 := UnOp (- t30);
    t33 := BinOp t32 "!=" t30);
    If t33 16 17
  ]);
  (15, [
    t34 := TypeAssert (y CommaOk go/constant.intVal);
    t35 := Extract (t34 0);
    t36 := Extract (t34 1);
    If t36 18 19
  ]);
  (16, [
    t37 := MakeInterface (t32 t32);
    Return (t37)
  ]);
  (17, [
    t38 := Call (newInt );
    t39 := ChangeType (t30);
    t40 := Call (NewInt t39);
    t41 := Call (Neg t38 t40);
    t42 := Call (makeInt t41);
    Return (t42)
  ]);
  (18, [
    t43 := Alloc (*y*) Local *go/constant.intVal;
    Store (t43 t35);
    t44 := Call (newInt );
    t45 := FieldAddr (t43 0);
    t46 := UnOp (* t45);
    t47 := Call (Neg t44 t46);
    t48 := Call (makeInt t47);
    Return (t48)
  ]);
  (19, [
    t49 := TypeAssert (y CommaOk go/constant.ratVal);
    t50 := Extract (t49 0);
    t51 := Extract (t49 1);
    If t51 20 21
  ]);
  (20, [
    t52 := Alloc (*y*) Local *go/constant.ratVal;
    Store (t52 t50);
    t53 := Call (newRat );
    t54 := FieldAddr (t52 0);
    t55 := UnOp (* t54);
    t56 := Call (Neg t53 t55);
    t57 := Call (makeRat t56);
    Return (t57)
  ]);
  (21, [
    t58 := TypeAssert (y CommaOk go/constant.floatVal);
    t59 := Extract (t58 0);
    t60 := Extract (t58 1);
    If t60 22 23
  ]);
  (22, [
    t61 := Alloc (*y*) Local *go/constant.floatVal;
    Store (t61 t59);
    t62 := Call (newFloat );
    t63 := FieldAddr (t61 0);
    t64 := UnOp (* t63);
    t65 := Call (Neg t62 t64);
    t66 := Call (makeFloat t65);
    Return (t66)
  ]);
  (23, [
    t67 := TypeAssert (y CommaOk go/constant.complexVal);
    t68 := Extract (t67 0);
    t69 := Extract (t67 1);
    If t69 24 34
  ]);
  (24, [
    t70 := Alloc (*y*) Local *go/constant.complexVal;
    Store (t70 t68);
    t71 := FieldAddr (t70 0);
    t72 := UnOp (* t71);
    t73 := Call (UnaryOp 13:go/token.Token t72 0:uint);
    t74 := FieldAddr (t70 1);
    t75 := UnOp (* t74);
    t76 := Call (UnaryOp 13:go/token.Token t75 0:uint);
    t77 := Call (makeComplex t73 t76);
    Return (t77)
  ]);
  (25, [
    t78 := TypeAssert (y CommaOk go/constant.unknownVal);
    t79 := Extract (t78 0);
    t80 := Extract (t78 1);
    If t80 37 38
  ]);
  (26, [
    t81 := BinOp op "==" 43:go/token.Token);
    If t81 25 34
  ]);
  (27, [
    t82 := BinOp prec ">" 0:uint);
    If t82 35 36
  ]);
  (28, [
    t83 := MakeInterface (t25 t25);
    Return (t83)
  ]);
  (29, [
    t84 := TypeAssert (y CommaOk go/constant.int64Val);
    t85 := Extract (t84 0);
    t86 := Extract (t84 1);
    If t86 30 31
  ]);
  (30, [
    t87 := ChangeType (t85);
    t88 := Call (NewInt t87);
    t89 := Call (Not t23 t88);
    Jump 27
  ]);
  (31, [
    t90 := TypeAssert (y CommaOk go/constant.intVal);
    t91 := Extract (t90 0);
    t92 := Extract (t90 1);
    If t92 32 33
  ]);
  (32, [
    t93 := Alloc (*y*) Local *go/constant.intVal;
    Store (t93 t91);
    t94 := FieldAddr (t93 0);
    t95 := UnOp (* t94);
    t96 := Call (Not t23 t95);
    Jump 27
  ]);
  (33, [
    Jump 34
  ]);
  (34, [
    t97 := Alloc (*varargs*) Heap *[2]any;
    t98 := IndexAddr (t97 0:int);
    t99 := MakeInterface (op op);
    Store (t98 t99);
    t100 := IndexAddr (t97 1:int);
    t101 := ChangeInterface (y);
    Store (t100 t101);
    t102 := Slice (t97);
    t103 := Call (Sprintf "invalid unary ope...":string t102);
    t104 := MakeInterface (t103 t103);
    Panic (t104)
  ]);
  (35, [
    t105 := Call (newInt );
    t106 := Call (NewInt -1:int64);
    t107 := Call (Lsh t105 t106 prec);
    t108 := Call (AndNot t23 t23 t107);
    Jump 36
  ]);
  (36, [
    t109 := Call (makeInt t23);
    Return (t109)
  ]);
  (37, [
    t110 := MakeInterface (t79 t79);
    Return (t110)
  ]);
  (38, [
    t111 := TypeAssert (y CommaOk go/constant.boolVal);
    t112 := Extract (t111 0);
    t113 := Extract (t111 1);
    If t113 39 34
  ]);
  (39, [
    t114 := UnOp (! t112);
    t115 := MakeInterface (t114 t114);
    Return (t115)
  ])
].

Definition Val (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.boolVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    t3 := ChangeType (t1);
    t4 := MakeInterface (t3 t3);
    Return (t4)
  ]);
  (2, [
    t5 := TypeAssert (x CommaOk *go/constant.stringVal);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    If t7 3 4
  ]);
  (3, [
    t8 := Call (string t6);
    t9 := MakeInterface (t8 t8);
    Return (t9)
  ]);
  (4, [
    t10 := TypeAssert (x CommaOk go/constant.int64Val);
    t11 := Extract (t10 0);
    t12 := Extract (t10 1);
    If t12 5 6
  ]);
  (5, [
    t13 := ChangeType (t11);
    t14 := MakeInterface (t13 t13);
    Return (t14)
  ]);
  (6, [
    t15 := TypeAssert (x CommaOk go/constant.intVal);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    If t17 7 8
  ]);
  (7, [
    t18 := Alloc (*x*) Local *go/constant.intVal;
    Store (t18 t16);
    t19 := FieldAddr (t18 0);
    t20 := UnOp (* t19);
    t21 := MakeInterface (t20 t20);
    Return (t21)
  ]);
  (8, [
    t22 := TypeAssert (x CommaOk go/constant.ratVal);
    t23 := Extract (t22 0);
    t24 := Extract (t22 1);
    If t24 9 10
  ]);
  (9, [
    t25 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t25 t23);
    t26 := FieldAddr (t25 0);
    t27 := UnOp (* t26);
    t28 := MakeInterface (t27 t27);
    Return (t28)
  ]);
  (10, [
    t29 := TypeAssert (x CommaOk go/constant.floatVal);
    t30 := Extract (t29 0);
    t31 := Extract (t29 1);
    If t31 11 12
  ]);
  (11, [
    t32 := Alloc (*x*) Local *go/constant.floatVal;
    Store (t32 t30);
    t33 := FieldAddr (t32 0);
    t34 := UnOp (* t33);
    t35 := MakeInterface (t34 t34);
    Return (t35)
  ]);
  (12, [
    Return (nil:any)
  ])
].

Definition add (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (BinaryOp x 12:go/token.Token y);
    Return (t0)
  ])
].

Definition cmpZero (x op : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp op "==" 39:go/token.Token);
    If t0 1 3
  ]);
  (1, [
    t1 := BinOp x "==" 0:int);
    Return (t1)
  ]);
  (2, [
    t2 := BinOp x "!=" 0:int);
    Return (t2)
  ]);
  (3, [
    t3 := BinOp op "==" 44:go/token.Token);
    If t3 2 5
  ]);
  (4, [
    t4 := BinOp x "<" 0:int);
    Return (t4)
  ]);
  (5, [
    t5 := BinOp op "==" 40:go/token.Token);
    If t5 4 7
  ]);
  (6, [
    t6 := BinOp x "<=" 0:int);
    Return (t6)
  ]);
  (7, [
    t7 := BinOp op "==" 45:go/token.Token);
    If t7 6 9
  ]);
  (8, [
    t8 := BinOp x ">" 0:int);
    Return (t8)
  ]);
  (9, [
    t9 := BinOp op "==" 41:go/token.Token);
    If t9 8 11
  ]);
  (10, [
    t10 := BinOp x ">=" 0:int);
    Return (t10)
  ]);
  (11, [
    t11 := BinOp op "==" 46:go/token.Token);
    If t11 10 12
  ]);
  (12, [
    t12 := Alloc (*varargs*) Heap *[2]any;
    t13 := IndexAddr (t12 0:int);
    t14 := MakeInterface (x x);
    Store (t13 t14);
    t15 := IndexAddr (t12 1:int);
    t16 := MakeInterface (op op);
    Store (t15 t16);
    t17 := Slice (t12);
    t18 := Call (Sprintf "invalid compariso...":string t17);
    t19 := MakeInterface (t18 t18);
    Panic (t19)
  ])
].

Definition i64tof (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*complit*) Local *go/constant.floatVal;
    t1 := FieldAddr (t0 0);
    t2 := Call (newFloat );
    t3 := ChangeType (x);
    t4 := Call (SetInt64 t2 t3);
    Store (t1 t4);
    t5 := UnOp (* t0);
    Return (t5)
  ])
].

Definition i64toi (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*complit*) Local *go/constant.intVal;
    t1 := FieldAddr (t0 0);
    t2 := Call (newInt );
    t3 := ChangeType (x);
    t4 := Call (SetInt64 t2 t3);
    Store (t1 t4);
    t5 := UnOp (* t0);
    Return (t5)
  ])
].

Definition i64tor (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*complit*) Local *go/constant.ratVal;
    t1 := FieldAddr (t0 0);
    t2 := Call (newRat );
    t3 := ChangeType (x);
    t4 := Call (SetInt64 t2 t3);
    Store (t1 t4);
    t5 := UnOp (* t0);
    Return (t5)
  ])
].

Definition init ( : Val.t) : FunctionBody.t := [
  (0, [
    t0 := UnOp (* init$guard);
    If t0 2 1
  ]);
  (1, [
    Store (init$guard true:bool);
    t1 := Call (init );
    t2 := Call (init );
    t3 := Call (init );
    t4 := Call (init );
    t5 := Call (init );
    t6 := Call (init );
    t7 := Call (init );
    t8 := Call (init );
    t9 := Call (init );
    t10 := IndexAddr (_Kind_index 0:int);
    t11 := IndexAddr (_Kind_index 1:int);
    t12 := IndexAddr (_Kind_index 2:int);
    t13 := IndexAddr (_Kind_index 3:int);
    t14 := IndexAddr (_Kind_index 4:int);
    t15 := IndexAddr (_Kind_index 5:int);
    t16 := IndexAddr (_Kind_index 6:int);
    Store (t10 0:uint8);
    Store (t11 7:uint8);
    Store (t12 11:uint8);
    Store (t13 17:uint8);
    Store (t14 20:uint8);
    Store (t15 25:uint8);
    Store (t16 32:uint8);
    t17 := FieldAddr (floatVal0 0);
    t18 := Call (newFloat );
    Store (t17 t18);
    Jump 2
  ]);
  (2, [
    Return ()
  ])
].

Definition is32bit (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp -2147483648:int64 "<=" x);
    If t0 1 2
  ]);
  (1, [
    t1 := BinOp x "<=" 2147483647:int64);
    Jump 2
  ]);
  (2, [
    t2 := Phi (* && *) (false:bool t1);
    Return (t2)
  ])
].

Definition is63bit (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := BinOp -4611686018427387904:int64 "<=" x);
    If t0 1 2
  ]);
  (1, [
    t1 := BinOp x "<=" 4611686018427387903:int64);
    Jump 2
  ]);
  (2, [
    t2 := Phi (* && *) (false:bool t1);
    Return (t2)
  ])
].

Definition itof (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*x*) Local *go/constant.intVal;
    Store (t0 x);
    t1 := Alloc (*complit*) Local *go/constant.floatVal;
    t2 := FieldAddr (t1 0);
    t3 := Call (newFloat );
    t4 := FieldAddr (t0 0);
    t5 := UnOp (* t4);
    t6 := Call (SetInt t3 t5);
    Store (t2 t6);
    t7 := UnOp (* t1);
    Return (t7)
  ])
].

Definition itor (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*x*) Local *go/constant.intVal;
    Store (t0 x);
    t1 := Alloc (*complit*) Local *go/constant.ratVal;
    t2 := FieldAddr (t1 0);
    t3 := Call (newRat );
    t4 := FieldAddr (t0 0);
    t5 := UnOp (* t4);
    t6 := Call (SetInt t3 t5);
    Store (t2 t6);
    t7 := UnOp (* t1);
    Return (t7)
  ])
].

Definition makeComplex (re im : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (re );
    t1 := BinOp t0 "==" 0:go/constant.Kind);
    If t1 1 3
  ]);
  (1, [
    t2 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t2)
  ]);
  (2, [
    t3 := Alloc (*complit*) Local *go/constant.complexVal;
    t4 := FieldAddr (t3 0);
    t5 := FieldAddr (t3 1);
    Store (t4 re);
    Store (t5 im);
    t6 := UnOp (* t3);
    t7 := MakeInterface (t6 t6);
    Return (t7)
  ]);
  (3, [
    t8 := Call (im );
    t9 := BinOp t8 "==" 0:go/constant.Kind);
    If t9 1 2
  ])
].

Definition makeFloat (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (Sign x);
    t1 := BinOp t0 "==" 0:int);
    If t1 1 2
  ]);
  (1, [
    t2 := UnOp (* floatVal0);
    t3 := MakeInterface (t2 t2);
    Return (t3)
  ]);
  (2, [
    t4 := Call (IsInf x);
    If t4 3 4
  ]);
  (3, [
    t5 := MakeInterface (struct{}{}:go/constant.unknownVal struct{}{}:go/constant.unknownVal);
    Return (t5)
  ]);
  (4, [
    t6 := Alloc (*complit*) Local *go/constant.floatVal;
    t7 := FieldAddr (t6 0);
    Store (t7 x);
    t8 := UnOp (* t6);
    t9 := MakeInterface (t8 t8);
    Return (t9)
  ])
].

Definition makeFloatFromLiteral (lit : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (newFloat );
    t1 := Call (SetString t0 lit);
    t2 := Extract (t1 0);
    t3 := Extract (t1 1);
    If t3 1 2
  ]);
  (1, [
    t4 := Call (smallFloat t2);
    If t4 3 4
  ]);
  (2, [
    Return (nil:go/constant.Value)
  ]);
  (3, [
    t5 := Call (Sign t2);
    t6 := BinOp t5 "==" 0:int);
    If t6 5 6
  ]);
  (4, [
    t7 := Call (makeFloat t2);
    Return (t7)
  ]);
  (5, [
    Jump 6
  ]);
  (6, [
    t8 := Phi (* lit *) (lit "0":string);
    t9 := Call (newRat );
    t10 := Call (SetString t9 t8);
    t11 := Extract (t10 0);
    t12 := Extract (t10 1);
    If t12 7 4
  ]);
  (7, [
    t13 := Alloc (*complit*) Local *go/constant.ratVal;
    t14 := FieldAddr (t13 0);
    Store (t14 t11);
    t15 := UnOp (* t13);
    t16 := MakeInterface (t15 t15);
    Return (t16)
  ])
].

Definition makeInt (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (IsInt64 x);
    If t0 1 2
  ]);
  (1, [
    t1 := Call (Int64 x);
    t2 := ChangeType (t1);
    t3 := MakeInterface (t2 t2);
    Return (t3)
  ]);
  (2, [
    t4 := Alloc (*complit*) Local *go/constant.intVal;
    t5 := FieldAddr (t4 0);
    Store (t5 x);
    t6 := UnOp (* t4);
    t7 := MakeInterface (t6 t6);
    Return (t7)
  ])
].

Definition makeRat (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (Num x);
    t1 := Call (Denom x);
    t2 := Call (smallInt t0);
    If t2 3 2
  ]);
  (1, [
    t3 := Alloc (*complit*) Local *go/constant.ratVal;
    t4 := FieldAddr (t3 0);
    Store (t4 x);
    t5 := UnOp (* t3);
    t6 := MakeInterface (t5 t5);
    Return (t6)
  ]);
  (2, [
    t7 := Alloc (*complit*) Local *go/constant.floatVal;
    t8 := FieldAddr (t7 0);
    t9 := Call (newFloat );
    t10 := Call (SetRat t9 x);
    Store (t8 t10);
    t11 := UnOp (* t7);
    t12 := MakeInterface (t11 t11);
    Return (t12)
  ]);
  (3, [
    t13 := Call (smallInt t1);
    If t13 1 2
  ])
].

Definition match (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (ord x);
    t1 := Call (ord y);
    t2 := BinOp t0 "<" t1);
    If t2 2 4
  ]);
  (1, [
    t3 := Phi (* x *) (t6 t10 x);
    t4 := Phi (* y *) (t7 t9 y);
    Return (t3 t4)
  ]);
  (2, [
    t5 := Call (match0 x y);
    t6 := Extract (t5 0);
    t7 := Extract (t5 1);
    Jump 1
  ]);
  (3, [
    t8 := Call (match0 y x);
    t9 := Extract (t8 0);
    t10 := Extract (t8 1);
    Jump 1
  ]);
  (4, [
    t11 := BinOp t0 ">" t1);
    If t11 3 1
  ])
].

Definition match0 (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (y CommaOk go/constant.intVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 2 3
  ]);
  (1, [
    Return (x x)
  ]);
  (2, [
    t3 := TypeAssert (x CommaOk go/constant.int64Val);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 4 1
  ]);
  (3, [
    t6 := TypeAssert (y CommaOk go/constant.ratVal);
    t7 := Extract (t6 0);
    t8 := Extract (t6 1);
    If t8 5 6
  ]);
  (4, [
    t9 := Call (i64toi t4);
    t10 := MakeInterface (t9 t9);
    Return (t10 y)
  ]);
  (5, [
    t11 := TypeAssert (x CommaOk go/constant.int64Val);
    t12 := Extract (t11 0);
    t13 := Extract (t11 1);
    If t13 7 8
  ]);
  (6, [
    t14 := TypeAssert (y CommaOk go/constant.floatVal);
    t15 := Extract (t14 0);
    t16 := Extract (t14 1);
    If t16 10 11
  ]);
  (7, [
    t17 := Call (i64tor t12);
    t18 := MakeInterface (t17 t17);
    Return (t18 y)
  ]);
  (8, [
    t19 := TypeAssert (x CommaOk go/constant.intVal);
    t20 := Extract (t19 0);
    t21 := Extract (t19 1);
    If t21 9 1
  ]);
  (9, [
    t22 := Call (itor t20);
    t23 := MakeInterface (t22 t22);
    Return (t23 y)
  ]);
  (10, [
    t24 := TypeAssert (x CommaOk go/constant.int64Val);
    t25 := Extract (t24 0);
    t26 := Extract (t24 1);
    If t26 12 13
  ]);
  (11, [
    t27 := TypeAssert (y CommaOk go/constant.complexVal);
    t28 := Extract (t27 0);
    t29 := Extract (t27 1);
    If t29 17 1
  ]);
  (12, [
    t30 := Call (i64tof t25);
    t31 := MakeInterface (t30 t30);
    Return (t31 y)
  ]);
  (13, [
    t32 := TypeAssert (x CommaOk go/constant.intVal);
    t33 := Extract (t32 0);
    t34 := Extract (t32 1);
    If t34 14 15
  ]);
  (14, [
    t35 := Call (itof t33);
    t36 := MakeInterface (t35 t35);
    Return (t36 y)
  ]);
  (15, [
    t37 := TypeAssert (x CommaOk go/constant.ratVal);
    t38 := Extract (t37 0);
    t39 := Extract (t37 1);
    If t39 16 1
  ]);
  (16, [
    t40 := Call (rtof t38);
    t41 := MakeInterface (t40 t40);
    Return (t41 y)
  ]);
  (17, [
    t42 := Call (vtoc x);
    t43 := MakeInterface (t42 t42);
    Return (t43 y)
  ])
].

Definition mul (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (BinaryOp x 14:go/token.Token y);
    Return (t0)
  ])
].

Definition newFloat ( : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*new*) Heap *math/big.Float;
    t1 := Call (SetPrec t0 512:uint);
    Return (t1)
  ])
].

Definition newInt ( : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*new*) Heap *math/big.Int;
    Return (t0)
  ])
].

Definition newRat ( : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*new*) Heap *math/big.Rat;
    Return (t0)
  ])
].

Definition ord (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := TypeAssert (x CommaOk go/constant.unknownVal);
    t1 := Extract (t0 0);
    t2 := Extract (t0 1);
    If t2 1 2
  ]);
  (1, [
    Return (0:int)
  ]);
  (2, [
    t3 := TypeAssert (x CommaOk go/constant.boolVal);
    t4 := Extract (t3 0);
    t5 := Extract (t3 1);
    If t5 3 4
  ]);
  (3, [
    Return (1:int)
  ]);
  (4, [
    t6 := TypeAssert (x CommaOk *go/constant.stringVal);
    t7 := Extract (t6 0);
    t8 := Extract (t6 1);
    If t8 3 5
  ]);
  (5, [
    t9 := TypeAssert (x CommaOk go/constant.int64Val);
    t10 := Extract (t9 0);
    t11 := Extract (t9 1);
    If t11 6 7
  ]);
  (6, [
    Return (2:int)
  ]);
  (7, [
    t12 := TypeAssert (x CommaOk go/constant.intVal);
    t13 := Extract (t12 0);
    t14 := Extract (t12 1);
    If t14 8 9
  ]);
  (8, [
    Return (3:int)
  ]);
  (9, [
    t15 := TypeAssert (x CommaOk go/constant.ratVal);
    t16 := Extract (t15 0);
    t17 := Extract (t15 1);
    If t17 10 11
  ]);
  (10, [
    Return (4:int)
  ]);
  (11, [
    t18 := TypeAssert (x CommaOk go/constant.floatVal);
    t19 := Extract (t18 0);
    t20 := Extract (t18 1);
    If t20 12 13
  ]);
  (12, [
    Return (5:int)
  ]);
  (13, [
    t21 := TypeAssert (x CommaOk go/constant.complexVal);
    t22 := Extract (t21 0);
    t23 := Extract (t21 1);
    If t23 14 15
  ]);
  (14, [
    Return (6:int)
  ]);
  (15, [
    Return (-1:int)
  ])
].

Definition quo (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (BinaryOp x 15:go/token.Token y);
    Return (t0)
  ])
].

Definition reverse (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (len x);
    Jump 3
  ]);
  (1, [
    t1 := BinOp t0 "-" 1:int);
    t2 := BinOp t1 "-" t12);
    t3 := BinOp t0 "-" 1:int);
    t4 := BinOp t3 "-" t12);
    t5 := IndexAddr (x t4);
    t6 := UnOp (* t5);
    t7 := IndexAddr (x t12);
    t8 := UnOp (* t7);
    t9 := IndexAddr (x t12);
    Store (t9 t6);
    t10 := IndexAddr (x t2);
    Store (t10 t8);
    t11 := BinOp t12 "+" 1:int);
    Jump 3
  ]);
  (2, [
    Return (x)
  ]);
  (3, [
    t12 := Phi (* i *) (0:int t11);
    t13 := BinOp t12 "+" t12);
    t14 := BinOp t13 "<" t0);
    If t14 1 2
  ])
].

Definition rtof (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*x*) Local *go/constant.ratVal;
    Store (t0 x);
    t1 := Alloc (*complit*) Local *go/constant.floatVal;
    t2 := FieldAddr (t1 0);
    t3 := Call (newFloat );
    t4 := FieldAddr (t0 0);
    t5 := UnOp (* t4);
    t6 := Call (SetRat t3 t5);
    Store (t2 t6);
    t7 := UnOp (* t1);
    Return (t7)
  ])
].

Definition smallFloat (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (IsInf x);
    If t0 1 2
  ]);
  (1, [
    Return (false:bool)
  ]);
  (2, [
    t1 := Call (MantExp x nil:*math/big.Float);
    t2 := BinOp -4096:int "<" t1);
    If t2 3 4
  ]);
  (3, [
    t3 := BinOp t1 "<" 4096:int);
    Jump 4
  ]);
  (4, [
    t4 := Phi (* && *) (false:bool t3);
    Return (t4)
  ])
].

Definition smallFloat64 (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (IsInf x 0:int);
    If t0 1 2
  ]);
  (1, [
    Return (false:bool)
  ]);
  (2, [
    t1 := Call (Frexp x);
    t2 := Extract (t1 0);
    t3 := Extract (t1 1);
    t4 := BinOp -4096:int "<" t3);
    If t4 3 4
  ]);
  (3, [
    t5 := BinOp t3 "<" 4096:int);
    Jump 4
  ]);
  (4, [
    t6 := Phi (* && *) (false:bool t5);
    Return (t6)
  ])
].

Definition smallInt (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (BitLen x);
    t1 := BinOp t0 "<" 4096:int);
    Return (t1)
  ])
].

Definition sub (x y : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Call (BinaryOp x 13:go/token.Token y);
    Return (t0)
  ])
].

Definition vtoc (x : Val.t) : FunctionBody.t := [
  (0, [
    t0 := Alloc (*complit*) Local *go/constant.complexVal;
    t1 := FieldAddr (t0 0);
    t2 := FieldAddr (t0 1);
    Store (t1 x);
    t3 := MakeInterface (0:go/constant.int64Val 0:go/constant.int64Val);
    Store (t2 t3);
    t4 := UnOp (* t0);
    Return (t4)
  ])
].

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

