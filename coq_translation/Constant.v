Require Import Coq.ZArith.ZArith.
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

(** ** Constants *)

Definition Bool : GoValue :=
  GoValue.int 1.

Definition Complex : GoValue :=
  GoValue.int 5.

Definition Float : GoValue :=
  GoValue.int 4.

Definition Int : GoValue :=
  GoValue.int 3.

Definition String : GoValue :=
  GoValue.int 2.

Definition Unknown : GoValue :=
  GoValue.int 0.

Definition _Kind_name : GoValue :=
  GoValue.string "UnknownBoolStringIntFloatComplex".

Definition _log : GoValue :=
  GoValue.int 3.

Definition _m : GoValue :=
  GoValue.int 18446744073709551615.

Definition maxExp : GoValue :=
  GoValue.int 4096.

Definition prec : GoValue :=
  GoValue.int 512.

Definition wordSize : GoValue :=
  GoValue.int 8.

(** ** Globals *)

Module GlobalName.
  Inductive t : Set :=
  | _Kind_index : t
  | emptyString : t
  | floatVal0 : t
  | init_dollar_guard : t
  .
End GlobalName.

Definition _Kind_index : M GoValue :=
  M.global GlobalName._Kind_index.

Definition emptyString : M GoValue :=
  M.global GlobalName.emptyString.

Definition floatVal0 : M GoValue :=
  M.global GlobalName.floatVal0.

Definition init_dollar_guard : M GoValue :=
  M.global GlobalName.init_dollar_guard.

(** ** Functions *)

Definition BinaryOp x_ op y_ : FunctionBody.t := [
  (0, [
    t0 := match(x_, y_);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    t3 := typeassert,ok t1.(unknownVal);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 1 else 2
  ]);
  (1, [
    t6 := make Value <- unknownVal (t4);
    return t6
  ]);
  (2, [
    t7 := typeassert,ok t1.(boolVal);
    t8 := extract t7 #0;
    t9 := extract t7 #1;
    if t9 goto 3 else 4
  ]);
  (3, [
    t10 := typeassert t2.(boolVal);
    t11 := op == 34:go/token.Token;
    if t11 goto 5 else 7
  ]);
  (4, [
    t12 := typeassert,ok t1.(int64Val);
    t13 := extract t12 #0;
    t14 := extract t12 #1;
    if t14 goto 12 else 13
  ]);
  (5, [
    if t8 goto 8 else 9
  ]);
  (6, [
    if t8 goto 11 else 10
  ]);
  (7, [
    t15 := op == 35:go/token.Token;
    if t15 goto 6 else 43
  ]);
  (8, [
    jump 9
  ]);
  (9, [
    t16 := phi [5: false:boolVal, 8: t10] #&&;
    t17 := make Value <- boolVal (t16);
    return t17
  ]);
  (10, [
    jump 11
  ]);
  (11, [
    t18 := phi [6: true:boolVal, 10: t10] #||;
    t19 := make Value <- boolVal (t18);
    return t19
  ]);
  (12, [
    t20 := changetype int64 <- int64Val (t13);
    t21 := typeassert t2.(int64Val);
    t22 := changetype int64 <- int64Val (t21);
    t23 := op == 12:go/token.Token;
    if t23 goto 15 else 17
  ]);
  (13, [
    t24 := typeassert,ok t1.(intVal);
    t25 := extract t24 #0;
    t26 := extract t24 #1;
    if t26 goto 44 else 45
  ]);
  (14, [
    t27 := phi [19: t38, 24: t47, 29: t57, 31: t59, 33: t61, 35: t63, 37: t65, 39: t67, 41: t69] #c;
    t28 := changetype int64Val <- int64 (t27);
    t29 := make Value <- int64Val (t28);
    return t29
  ]);
  (15, [
    t30 := is63bit(t20);
    if t30 goto 20 else 18
  ]);
  (16, [
    t31 := is63bit(t20);
    if t31 goto 25 else 23
  ]);
  (17, [
    t32 := op == 13:go/token.Token;
    if t32 goto 16 else 22
  ]);
  (18, [
    t33 := newInt();
    t34 := math/big.NewInt(t20);
    t35 := math/big.NewInt(t22);
    t36 := (*math/big.Int).Add(t33, t34, t35);
    t37 := makeInt(t36);
    return t37
  ]);
  (19, [
    t38 := t20 + t22;
    jump 14
  ]);
  (20, [
    t39 := is63bit(t22);
    if t39 goto 19 else 18
  ]);
  (21, [
    t40 := is32bit(t20);
    if t40 goto 30 else 28
  ]);
  (22, [
    t41 := op == 14:go/token.Token;
    if t41 goto 21 else 27
  ]);
  (23, [
    t42 := newInt();
    t43 := math/big.NewInt(t20);
    t44 := math/big.NewInt(t22);
    t45 := (*math/big.Int).Sub(t42, t43, t44);
    t46 := makeInt(t45);
    return t46
  ]);
  (24, [
    t47 := t20 - t22;
    jump 14
  ]);
  (25, [
    t48 := is63bit(t22);
    if t48 goto 24 else 23
  ]);
  (26, [
    t49 := math/big.NewRat(t20, t22);
    t50 := makeRat(t49);
    return t50
  ]);
  (27, [
    t51 := op == 15:go/token.Token;
    if t51 goto 26 else 32
  ]);
  (28, [
    t52 := newInt();
    t53 := math/big.NewInt(t20);
    t54 := math/big.NewInt(t22);
    t55 := (*math/big.Int).Mul(t52, t53, t54);
    t56 := makeInt(t55);
    return t56
  ]);
  (29, [
    t57 := t20 * t22;
    jump 14
  ]);
  (30, [
    t58 := is32bit(t22);
    if t58 goto 29 else 28
  ]);
  (31, [
    t59 := t20 / t22;
    jump 14
  ]);
  (32, [
    t60 := op == 26:go/token.Token;
    if t60 goto 31 else 34
  ]);
  (33, [
    t61 := t20 % t22;
    jump 14
  ]);
  (34, [
    t62 := op == 16:go/token.Token;
    if t62 goto 33 else 36
  ]);
  (35, [
    t63 := t20 & t22;
    jump 14
  ]);
  (36, [
    t64 := op == 17:go/token.Token;
    if t64 goto 35 else 38
  ]);
  (37, [
    t65 := t20 | t22;
    jump 14
  ]);
  (38, [
    t66 := op == 18:go/token.Token;
    if t66 goto 37 else 40
  ]);
  (39, [
    t67 := t20 ^ t22;
    jump 14
  ]);
  (40, [
    t68 := op == 19:go/token.Token;
    if t68 goto 39 else 42
  ]);
  (41, [
    t69 := t20 &^ t22;
    jump 14
  ]);
  (42, [
    t70 := op == 22:go/token.Token;
    if t70 goto 41 else 43
  ]);
  (43, [
    t71 := new [3]any (varargs);
    t72 := &t71[0:int];
    t73 := change interface any <- Value (x_);
    *t72 = t73;
    t74 := &t71[1:int];
    t75 := make any <- go/token.Token (op);
    *t74 = t75;
    t76 := &t71[2:int];
    t77 := change interface any <- Value (y_);
    *t76 = t77;
    t78 := slice t71[:];
    t79 := fmt.Sprintf("invalid binary op...":string, t78...);
    t80 := make interface{} <- string (t79);
    panic t80
  ]);
  (44, [
    t81 := local intVal (x);
    *t81 = t25;
    t82 := &t81.val [#0];
    t83 := *t82;
    t84 := typeassert t2.(intVal);
    t85 := t84.val [#0];
    t86 := newInt();
    t87 := op == 12:go/token.Token;
    if t87 goto 47 else 49
  ]);
  (45, [
    t88 := typeassert,ok t1.(ratVal);
    t89 := extract t88 #0;
    t90 := extract t88 #1;
    if t90 goto 66 else 67
  ]);
  (46, [
    t91 := makeInt(t86);
    return t91
  ]);
  (47, [
    t92 := (*math/big.Int).Add(t86, t83, t85);
    jump 46
  ]);
  (48, [
    t93 := (*math/big.Int).Sub(t86, t83, t85);
    jump 46
  ]);
  (49, [
    t94 := op == 13:go/token.Token;
    if t94 goto 48 else 51
  ]);
  (50, [
    t95 := (*math/big.Int).Mul(t86, t83, t85);
    jump 46
  ]);
  (51, [
    t96 := op == 14:go/token.Token;
    if t96 goto 50 else 53
  ]);
  (52, [
    t97 := newRat();
    t98 := (*math/big.Rat).SetFrac(t97, t83, t85);
    t99 := makeRat(t98);
    return t99
  ]);
  (53, [
    t100 := op == 15:go/token.Token;
    if t100 goto 52 else 55
  ]);
  (54, [
    t101 := (*math/big.Int).Quo(t86, t83, t85);
    jump 46
  ]);
  (55, [
    t102 := op == 26:go/token.Token;
    if t102 goto 54 else 57
  ]);
  (56, [
    t103 := (*math/big.Int).Rem(t86, t83, t85);
    jump 46
  ]);
  (57, [
    t104 := op == 16:go/token.Token;
    if t104 goto 56 else 59
  ]);
  (58, [
    t105 := (*math/big.Int).And(t86, t83, t85);
    jump 46
  ]);
  (59, [
    t106 := op == 17:go/token.Token;
    if t106 goto 58 else 61
  ]);
  (60, [
    t107 := (*math/big.Int).Or(t86, t83, t85);
    jump 46
  ]);
  (61, [
    t108 := op == 18:go/token.Token;
    if t108 goto 60 else 63
  ]);
  (62, [
    t109 := (*math/big.Int).Xor(t86, t83, t85);
    jump 46
  ]);
  (63, [
    t110 := op == 19:go/token.Token;
    if t110 goto 62 else 65
  ]);
  (64, [
    t111 := (*math/big.Int).AndNot(t86, t83, t85);
    jump 46
  ]);
  (65, [
    t112 := op == 22:go/token.Token;
    if t112 goto 64 else 43
  ]);
  (66, [
    t113 := local ratVal (x);
    *t113 = t89;
    t114 := &t113.val [#0];
    t115 := *t114;
    t116 := typeassert t2.(ratVal);
    t117 := t116.val [#0];
    t118 := newRat();
    t119 := op == 12:go/token.Token;
    if t119 goto 69 else 71
  ]);
  (67, [
    t120 := typeassert,ok t1.(floatVal);
    t121 := extract t120 #0;
    t122 := extract t120 #1;
    if t122 goto 76 else 77
  ]);
  (68, [
    t123 := makeRat(t118);
    return t123
  ]);
  (69, [
    t124 := (*math/big.Rat).Add(t118, t115, t117);
    jump 68
  ]);
  (70, [
    t125 := (*math/big.Rat).Sub(t118, t115, t117);
    jump 68
  ]);
  (71, [
    t126 := op == 13:go/token.Token;
    if t126 goto 70 else 73
  ]);
  (72, [
    t127 := (*math/big.Rat).Mul(t118, t115, t117);
    jump 68
  ]);
  (73, [
    t128 := op == 14:go/token.Token;
    if t128 goto 72 else 75
  ]);
  (74, [
    t129 := (*math/big.Rat).Quo(t118, t115, t117);
    jump 68
  ]);
  (75, [
    t130 := op == 15:go/token.Token;
    if t130 goto 74 else 43
  ]);
  (76, [
    t131 := local floatVal (x);
    *t131 = t121;
    t132 := &t131.val [#0];
    t133 := *t132;
    t134 := typeassert t2.(floatVal);
    t135 := t134.val [#0];
    t136 := newFloat();
    t137 := op == 12:go/token.Token;
    if t137 goto 79 else 81
  ]);
  (77, [
    t138 := typeassert,ok t1.(complexVal);
    t139 := extract t138 #0;
    t140 := extract t138 #1;
    if t140 goto 86 else 87
  ]);
  (78, [
    t141 := makeFloat(t136);
    return t141
  ]);
  (79, [
    t142 := (*math/big.Float).Add(t136, t133, t135);
    jump 78
  ]);
  (80, [
    t143 := (*math/big.Float).Sub(t136, t133, t135);
    jump 78
  ]);
  (81, [
    t144 := op == 13:go/token.Token;
    if t144 goto 80 else 83
  ]);
  (82, [
    t145 := (*math/big.Float).Mul(t136, t133, t135);
    jump 78
  ]);
  (83, [
    t146 := op == 14:go/token.Token;
    if t146 goto 82 else 85
  ]);
  (84, [
    t147 := (*math/big.Float).Quo(t136, t133, t135);
    jump 78
  ]);
  (85, [
    t148 := op == 15:go/token.Token;
    if t148 goto 84 else 43
  ]);
  (86, [
    t149 := local complexVal (x);
    *t149 = t139;
    t150 := local complexVal (y);
    t151 := typeassert t2.(complexVal);
    *t150 = t151;
    t152 := &t149.re [#0];
    t153 := *t152;
    t154 := &t149.im [#1];
    t155 := *t154;
    t156 := &t150.re [#0];
    t157 := *t156;
    t158 := &t150.im [#1];
    t159 := *t158;
    t160 := op == 12:go/token.Token;
    if t160 goto 89 else 91
  ]);
  (87, [
    t161 := typeassert,ok t1.(*stringVal);
    t162 := extract t161 #0;
    t163 := extract t161 #1;
    if t163 goto 96 else 43
  ]);
  (88, [
    t164 := phi [89: t167, 90: t169, 92: t176, 94: t187] #re;
    t165 := phi [89: t168, 90: t170, 92: t177, 94: t189] #im;
    t166 := makeComplex(t164, t165);
    return t166
  ]);
  (89, [
    t167 := add(t153, t157);
    t168 := add(t155, t159);
    jump 88
  ]);
  (90, [
    t169 := sub(t153, t157);
    t170 := sub(t155, t159);
    jump 88
  ]);
  (91, [
    t171 := op == 13:go/token.Token;
    if t171 goto 90 else 93
  ]);
  (92, [
    t172 := mul(t153, t157);
    t173 := mul(t155, t159);
    t174 := mul(t155, t157);
    t175 := mul(t153, t159);
    t176 := sub(t172, t173);
    t177 := add(t174, t175);
    jump 88
  ]);
  (93, [
    t178 := op == 14:go/token.Token;
    if t178 goto 92 else 95
  ]);
  (94, [
    t179 := mul(t153, t157);
    t180 := mul(t155, t159);
    t181 := mul(t155, t157);
    t182 := mul(t153, t159);
    t183 := mul(t157, t157);
    t184 := mul(t159, t159);
    t185 := add(t183, t184);
    t186 := add(t179, t180);
    t187 := quo(t186, t185);
    t188 := sub(t181, t182);
    t189 := quo(t188, t185);
    jump 88
  ]);
  (95, [
    t190 := op == 15:go/token.Token;
    if t190 goto 94 else 43
  ]);
  (96, [
    t191 := op == 12:go/token.Token;
    if t191 goto 97 else 43
  ]);
  (97, [
    t192 := new stringVal (complit);
    t193 := &t192.l [#2];
    t194 := &t192.r [#3];
    t195 := typeassert t2.(*stringVal);
    *t193 = t162;
    *t194 = t195;
    t196 := make Value <- *stringVal (t192);
    return t196
  ])
].

Definition BitLen x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := convert uint64 <- int64Val (t1);
    t4 := t1 < 0:int64Val;
    if t4 goto 3 else 4
  ]);
  (2, [
    t5 := typeassert,ok x.(intVal);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 5 else 6
  ]);
  (3, [
    t8 := -t1;
    t9 := convert uint64 <- int64Val (t8);
    jump 4
  ]);
  (4, [
    t10 := phi [1: t3, 3: t9] #u;
    t11 := math/bits.LeadingZeros64(t10);
    t12 := 64:int - t11;
    return t12
  ]);
  (5, [
    t13 := local intVal (x);
    *t13 = t6;
    t14 := &t13.val [#0];
    t15 := *t14;
    t16 := (*math/big.Int).BitLen(t15);
    return t16
  ]);
  (6, [
    t17 := typeassert,ok x.(unknownVal);
    t18 := extract t17 #0;
    t19 := extract t17 #1;
    if t19 goto 7 else 8
  ]);
  (7, [
    return 0:int
  ]);
  (8, [
    t20 := new [1]any (varargs);
    t21 := &t20[0:int];
    t22 := change interface any <- Value (x);
    *t21 = t22;
    t23 := slice t20[:];
    t24 := fmt.Sprintf("%v not an Int":string, t23...);
    t25 := make interface{} <- string (t24);
    panic t25
  ])
].

Definition BoolVal x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(boolVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := changetype bool <- boolVal (t1);
    return t3
  ]);
  (2, [
    t4 := typeassert,ok x.(unknownVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 3 else 4
  ]);
  (3, [
    return false:bool
  ]);
  (4, [
    t7 := new [1]any (varargs);
    t8 := &t7[0:int];
    t9 := change interface any <- Value (x);
    *t8 = t9;
    t10 := slice t7[:];
    t11 := fmt.Sprintf("%v not a Bool":string, t10...);
    t12 := make interface{} <- string (t11);
    panic t12
  ])
].

Definition Bytes x : FunctionBody.t := [
  (0, [
    t0 := local intVal (t);
    t1 := typeassert,ok x.(int64Val);
    t2 := extract t1 #0;
    t3 := extract t1 #1;
    if t3 goto 2 else 3
  ]);
  (1, [
    t4 := &t0.val [#0];
    t5 := *t4;
    t6 := (*math/big.Int).Bits(t5);
    t7 := len(t6);
    t8 := t7 * 8:int;
    t9 := make []byte t8 t8;
    t10 := len(t6);
    jump 6
  ]);
  (2, [
    t11 := i64toi(t2);
    *t0 = t11;
    jump 1
  ]);
  (3, [
    t12 := typeassert,ok x.(intVal);
    t13 := extract t12 #0;
    t14 := extract t12 #1;
    if t14 goto 4 else 5
  ]);
  (4, [
    *t0 = t13;
    jump 1
  ]);
  (5, [
    t15 := new [1]any (varargs);
    t16 := &t15[0:int];
    t17 := change interface any <- Value (x);
    *t16 = t17;
    t18 := slice t15[:];
    t19 := fmt.Sprintf("%v not an Int":string, t18...);
    t20 := make interface{} <- string (t19);
    panic t20
  ]);
  (6, [
    t21 := phi [1: 0:int, 9: t32] #i;
    t22 := phi [1: -1:int, 9: t23] #rangeindex;
    t23 := t22 + 1:int;
    t24 := t23 < t10;
    if t24 goto 7 else 12
  ]);
  (7, [
    t25 := &t6[t23];
    t26 := *t25;
    jump 9
  ]);
  (8, [
    t27 := convert byte <- math/big.Word (t33);
    t28 := &t9[t32];
    *t28 = t27;
    t29 := t33 >> 8:uint;
    t30 := t32 + 1:int;
    t31 := t34 + 1:int;
    jump 9
  ]);
  (9, [
    t32 := phi [7: t21, 8: t30] #i;
    t33 := phi [7: t26, 8: t29] #w;
    t34 := phi [7: 0:int, 8: t31] #j;
    t35 := t34 < 8:int;
    if t35 goto 8 else 6
  ]);
  (10, [
    t36 := t38 - 1:int;
    jump 12
  ]);
  (11, [
    t37 := slice t9[:t38];
    return t37
  ]);
  (12, [
    t38 := phi [6: t21, 10: t36] #i;
    t39 := t38 > 0:int;
    if t39 goto 13 else 11
  ]);
  (13, [
    t40 := t38 - 1:int;
    t41 := &t9[t40];
    t42 := *t41;
    t43 := t42 == 0:byte;
    if t43 goto 10 else 11
  ])
].

Definition Compare x_ op y_ : FunctionBody.t := [
  (0, [
    t0 := match(x_, y_);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    t3 := typeassert,ok t1.(unknownVal);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 2 else 3
  ]);
  (1, [
    t6 := new [3]any (varargs);
    t7 := &t6[0:int];
    t8 := change interface any <- Value (x_);
    *t7 = t8;
    t9 := &t6[1:int];
    t10 := make any <- go/token.Token (op);
    *t9 = t10;
    t11 := &t6[2:int];
    t12 := change interface any <- Value (y_);
    *t11 = t12;
    t13 := slice t6[:];
    t14 := fmt.Sprintf("invalid compariso...":string, t13...);
    t15 := make interface{} <- string (t14);
    panic t15
  ]);
  (2, [
    return false:bool
  ]);
  (3, [
    t16 := typeassert,ok t1.(boolVal);
    t17 := extract t16 #0;
    t18 := extract t16 #1;
    if t18 goto 4 else 5
  ]);
  (4, [
    t19 := typeassert t2.(boolVal);
    t20 := op == 39:go/token.Token;
    if t20 goto 6 else 8
  ]);
  (5, [
    t21 := typeassert,ok t1.(int64Val);
    t22 := extract t21 #0;
    t23 := extract t21 #1;
    if t23 goto 9 else 10
  ]);
  (6, [
    t24 := t17 == t19;
    return t24
  ]);
  (7, [
    t25 := t17 != t19;
    return t25
  ]);
  (8, [
    t26 := op == 44:go/token.Token;
    if t26 goto 7 else 1
  ]);
  (9, [
    t27 := typeassert t2.(int64Val);
    t28 := op == 39:go/token.Token;
    if t28 goto 11 else 13
  ]);
  (10, [
    t29 := typeassert,ok t1.(intVal);
    t30 := extract t29 #0;
    t31 := extract t29 #1;
    if t31 goto 22 else 23
  ]);
  (11, [
    t32 := t22 == t27;
    return t32
  ]);
  (12, [
    t33 := t22 != t27;
    return t33
  ]);
  (13, [
    t34 := op == 44:go/token.Token;
    if t34 goto 12 else 15
  ]);
  (14, [
    t35 := t22 < t27;
    return t35
  ]);
  (15, [
    t36 := op == 40:go/token.Token;
    if t36 goto 14 else 17
  ]);
  (16, [
    t37 := t22 <= t27;
    return t37
  ]);
  (17, [
    t38 := op == 45:go/token.Token;
    if t38 goto 16 else 19
  ]);
  (18, [
    t39 := t22 > t27;
    return t39
  ]);
  (19, [
    t40 := op == 41:go/token.Token;
    if t40 goto 18 else 21
  ]);
  (20, [
    t41 := t22 >= t27;
    return t41
  ]);
  (21, [
    t42 := op == 46:go/token.Token;
    if t42 goto 20 else 1
  ]);
  (22, [
    t43 := local intVal (x);
    *t43 = t30;
    t44 := &t43.val [#0];
    t45 := *t44;
    t46 := typeassert t2.(intVal);
    t47 := t46.val [#0];
    t48 := (*math/big.Int).Cmp(t45, t47);
    t49 := cmpZero(t48, op);
    return t49
  ]);
  (23, [
    t50 := typeassert,ok t1.(ratVal);
    t51 := extract t50 #0;
    t52 := extract t50 #1;
    if t52 goto 24 else 25
  ]);
  (24, [
    t53 := local ratVal (x);
    *t53 = t51;
    t54 := &t53.val [#0];
    t55 := *t54;
    t56 := typeassert t2.(ratVal);
    t57 := t56.val [#0];
    t58 := (*math/big.Rat).Cmp(t55, t57);
    t59 := cmpZero(t58, op);
    return t59
  ]);
  (25, [
    t60 := typeassert,ok t1.(floatVal);
    t61 := extract t60 #0;
    t62 := extract t60 #1;
    if t62 goto 26 else 27
  ]);
  (26, [
    t63 := local floatVal (x);
    *t63 = t61;
    t64 := &t63.val [#0];
    t65 := *t64;
    t66 := typeassert t2.(floatVal);
    t67 := t66.val [#0];
    t68 := (*math/big.Float).Cmp(t65, t67);
    t69 := cmpZero(t68, op);
    return t69
  ]);
  (27, [
    t70 := typeassert,ok t1.(complexVal);
    t71 := extract t70 #0;
    t72 := extract t70 #1;
    if t72 goto 28 else 29
  ]);
  (28, [
    t73 := local complexVal (x);
    *t73 = t71;
    t74 := local complexVal (y);
    t75 := typeassert t2.(complexVal);
    *t74 = t75;
    t76 := &t73.re [#0];
    t77 := *t76;
    t78 := &t74.re [#0];
    t79 := *t78;
    t80 := Compare(t77, 39:go/token.Token, t79);
    t81 := &t73.im [#1];
    t82 := *t81;
    t83 := &t74.im [#1];
    t84 := *t83;
    t85 := Compare(t82, 39:go/token.Token, t84);
    t86 := op == 39:go/token.Token;
    if t86 goto 30 else 32
  ]);
  (29, [
    t87 := typeassert,ok t1.(*stringVal);
    t88 := extract t87 #0;
    t89 := extract t87 #1;
    if t89 goto 37 else 1
  ]);
  (30, [
    if t80 goto 33 else 34
  ]);
  (31, [
    if t80 goto 35 else 36
  ]);
  (32, [
    t90 := op == 44:go/token.Token;
    if t90 goto 31 else 1
  ]);
  (33, [
    jump 34
  ]);
  (34, [
    t91 := phi [30: false:bool, 33: t85] #&&;
    return t91
  ]);
  (35, [
    t92 := !t85;
    jump 36
  ]);
  (36, [
    t93 := phi [31: true:bool, 35: t92] #||;
    return t93
  ]);
  (37, [
    t94 := (*stringVal).string(t88);
    t95 := typeassert t2.(*stringVal);
    t96 := (*stringVal).string(t95);
    t97 := op == 39:go/token.Token;
    if t97 goto 38 else 40
  ]);
  (38, [
    t98 := t94 == t96;
    return t98
  ]);
  (39, [
    t99 := t94 != t96;
    return t99
  ]);
  (40, [
    t100 := op == 44:go/token.Token;
    if t100 goto 39 else 42
  ]);
  (41, [
    t101 := t94 < t96;
    return t101
  ]);
  (42, [
    t102 := op == 40:go/token.Token;
    if t102 goto 41 else 44
  ]);
  (43, [
    t103 := t94 <= t96;
    return t103
  ]);
  (44, [
    t104 := op == 45:go/token.Token;
    if t104 goto 43 else 46
  ]);
  (45, [
    t105 := t94 > t96;
    return t105
  ]);
  (46, [
    t106 := op == 41:go/token.Token;
    if t106 goto 45 else 48
  ]);
  (47, [
    t107 := t94 >= t96;
    return t107
  ]);
  (48, [
    t108 := op == 46:go/token.Token;
    if t108 goto 47 else 1
  ])
].

Definition Denom x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    t3 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t3
  ]);
  (2, [
    t4 := make Value <- int64Val (1:int64Val);
    return t4
  ]);
  (3, [
    t5 := typeassert,ok x.(intVal);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 2 else 4
  ]);
  (4, [
    t8 := typeassert,ok x.(ratVal);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    if t10 goto 5 else 6
  ]);
  (5, [
    t11 := local ratVal (x);
    *t11 = t9;
    t12 := &t11.val [#0];
    t13 := *t12;
    t14 := (*math/big.Rat).Denom(t13);
    t15 := makeInt(t14);
    return t15
  ]);
  (6, [
    t16 := typeassert,ok x.(floatVal);
    t17 := extract t16 #0;
    t18 := extract t16 #1;
    if t18 goto 7 else 8
  ]);
  (7, [
    t19 := local floatVal (x);
    *t19 = t17;
    t20 := &t19.val [#0];
    t21 := *t20;
    t22 := smallFloat(t21);
    if t22 goto 9 else 1
  ]);
  (8, [
    t23 := typeassert,ok x.(unknownVal);
    t24 := extract t23 #0;
    t25 := extract t23 #1;
    if t25 goto 10 else 11
  ]);
  (9, [
    t26 := &t19.val [#0];
    t27 := *t26;
    t28 := (*math/big.Float).Rat(t27, nil:*math/big.Rat);
    t29 := extract t28 #0;
    t30 := extract t28 #1;
    t31 := (*math/big.Rat).Denom(t29);
    t32 := makeInt(t31);
    return t32
  ]);
  (10, [
    jump 1
  ]);
  (11, [
    t33 := new [1]any (varargs);
    t34 := &t33[0:int];
    t35 := change interface any <- Value (x);
    *t34 = t35;
    t36 := slice t33[:];
    t37 := fmt.Sprintf("%v not Int or Float":string, t36...);
    t38 := make interface{} <- string (t37);
    panic t38
  ])
].

Definition Float32Val x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := convert float32 <- int64Val (t1);
    t4 := convert int64Val <- float32 (t3);
    t5 := t4 == t1;
    return t3, t5
  ]);
  (2, [
    t6 := typeassert,ok x.(intVal);
    t7 := extract t6 #0;
    t8 := extract t6 #1;
    if t8 goto 3 else 4
  ]);
  (3, [
    t9 := local intVal (x);
    *t9 = t7;
    t10 := newFloat();
    t11 := &t9.val [#0];
    t12 := *t11;
    t13 := (*math/big.Float).SetInt(t10, t12);
    t14 := (*math/big.Float).Float32(t13);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    t17 := t16 == 0:math/big.Accuracy;
    return t15, t17
  ]);
  (4, [
    t18 := typeassert,ok x.(ratVal);
    t19 := extract t18 #0;
    t20 := extract t18 #1;
    if t20 goto 5 else 6
  ]);
  (5, [
    t21 := local ratVal (x);
    *t21 = t19;
    t22 := &t21.val [#0];
    t23 := *t22;
    t24 := (*math/big.Rat).Float32(t23);
    t25 := extract t24 #0;
    t26 := extract t24 #1;
    return t25, t26
  ]);
  (6, [
    t27 := typeassert,ok x.(floatVal);
    t28 := extract t27 #0;
    t29 := extract t27 #1;
    if t29 goto 7 else 8
  ]);
  (7, [
    t30 := local floatVal (x);
    *t30 = t28;
    t31 := &t30.val [#0];
    t32 := *t31;
    t33 := (*math/big.Float).Float32(t32);
    t34 := extract t33 #0;
    t35 := extract t33 #1;
    t36 := t35 == 0:math/big.Accuracy;
    return t34, t36
  ]);
  (8, [
    t37 := typeassert,ok x.(unknownVal);
    t38 := extract t37 #0;
    t39 := extract t37 #1;
    if t39 goto 9 else 10
  ]);
  (9, [
    return 0:float32, false:bool
  ]);
  (10, [
    t40 := new [1]any (varargs);
    t41 := &t40[0:int];
    t42 := change interface any <- Value (x);
    *t41 = t42;
    t43 := slice t40[:];
    t44 := fmt.Sprintf("%v not a Float":string, t43...);
    t45 := make interface{} <- string (t44);
    panic t45
  ])
].

Definition Float64Val x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := changetype int64 <- int64Val (t1);
    t4 := convert float64 <- int64 (t3);
    t5 := convert int64Val <- float64 (t4);
    t6 := t5 == t1;
    return t4, t6
  ]);
  (2, [
    t7 := typeassert,ok x.(intVal);
    t8 := extract t7 #0;
    t9 := extract t7 #1;
    if t9 goto 3 else 4
  ]);
  (3, [
    t10 := local intVal (x);
    *t10 = t8;
    t11 := newFloat();
    t12 := &t10.val [#0];
    t13 := *t12;
    t14 := (*math/big.Float).SetInt(t11, t13);
    t15 := (*math/big.Float).Float64(t14);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    t18 := t17 == 0:math/big.Accuracy;
    return t16, t18
  ]);
  (4, [
    t19 := typeassert,ok x.(ratVal);
    t20 := extract t19 #0;
    t21 := extract t19 #1;
    if t21 goto 5 else 6
  ]);
  (5, [
    t22 := local ratVal (x);
    *t22 = t20;
    t23 := &t22.val [#0];
    t24 := *t23;
    t25 := (*math/big.Rat).Float64(t24);
    t26 := extract t25 #0;
    t27 := extract t25 #1;
    return t26, t27
  ]);
  (6, [
    t28 := typeassert,ok x.(floatVal);
    t29 := extract t28 #0;
    t30 := extract t28 #1;
    if t30 goto 7 else 8
  ]);
  (7, [
    t31 := local floatVal (x);
    *t31 = t29;
    t32 := &t31.val [#0];
    t33 := *t32;
    t34 := (*math/big.Float).Float64(t33);
    t35 := extract t34 #0;
    t36 := extract t34 #1;
    t37 := t36 == 0:math/big.Accuracy;
    return t35, t37
  ]);
  (8, [
    t38 := typeassert,ok x.(unknownVal);
    t39 := extract t38 #0;
    t40 := extract t38 #1;
    if t40 goto 9 else 10
  ]);
  (9, [
    return 0:float64, false:bool
  ]);
  (10, [
    t41 := new [1]any (varargs);
    t42 := &t41[0:int];
    t43 := change interface any <- Value (x);
    *t42 = t43;
    t44 := slice t41[:];
    t45 := fmt.Sprintf("%v not a Float":string, t44...);
    t46 := make interface{} <- string (t45);
    panic t46
  ])
].

Definition Imag x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(unknownVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := make Value <- unknownVal (t1);
    return t3
  ]);
  (2, [
    t4 := typeassert,ok x.(int64Val);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 3 else 4
  ]);
  (3, [
    t7 := make Value <- int64Val (0:int64Val);
    return t7
  ]);
  (4, [
    t8 := typeassert,ok x.(intVal);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    if t10 goto 3 else 5
  ]);
  (5, [
    t11 := typeassert,ok x.(ratVal);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 3 else 6
  ]);
  (6, [
    t14 := typeassert,ok x.(floatVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 3 else 7
  ]);
  (7, [
    t17 := typeassert,ok x.(complexVal);
    t18 := extract t17 #0;
    t19 := extract t17 #1;
    if t19 goto 8 else 9
  ]);
  (8, [
    t20 := local complexVal (x);
    *t20 = t18;
    t21 := &t20.im [#1];
    t22 := *t21;
    return t22
  ]);
  (9, [
    t23 := new [1]any (varargs);
    t24 := &t23[0:int];
    t25 := change interface any <- Value (x);
    *t24 = t25;
    t26 := slice t23[:];
    t27 := fmt.Sprintf("%v not numeric":string, t26...);
    t28 := make interface{} <- string (t27);
    panic t28
  ])
].

Definition Int64Val x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := changetype int64 <- int64Val (t1);
    return t3, true:bool
  ]);
  (2, [
    t4 := typeassert,ok x.(intVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 3 else 4
  ]);
  (3, [
    t7 := local intVal (x);
    *t7 = t5;
    t8 := &t7.val [#0];
    t9 := *t8;
    t10 := (*math/big.Int).Int64(t9);
    return t10, false:bool
  ]);
  (4, [
    t11 := typeassert,ok x.(unknownVal);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 5 else 6
  ]);
  (5, [
    return 0:int64, false:bool
  ]);
  (6, [
    t14 := new [1]any (varargs);
    t15 := &t14[0:int];
    t16 := change interface any <- Value (x);
    *t15 = t16;
    t17 := slice t14[:];
    t18 := fmt.Sprintf("%v not an Int":string, t17...);
    t19 := make interface{} <- string (t18);
    panic t19
  ])
].

Definition Make x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(bool);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := changetype boolVal <- bool (t1);
    t4 := make Value <- boolVal (t3);
    return t4
  ]);
  (2, [
    t5 := typeassert,ok x.(string);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 3 else 4
  ]);
  (3, [
    t8 := new stringVal (complit);
    t9 := &t8.s [#1];
    *t9 = t6;
    t10 := make Value <- *stringVal (t8);
    return t10
  ]);
  (4, [
    t11 := typeassert,ok x.(int64);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 5 else 6
  ]);
  (5, [
    t14 := changetype int64Val <- int64 (t12);
    t15 := make Value <- int64Val (t14);
    return t15
  ]);
  (6, [
    t16 := typeassert,ok x.(*math/big.Int);
    t17 := extract t16 #0;
    t18 := extract t16 #1;
    if t18 goto 7 else 8
  ]);
  (7, [
    t19 := makeInt(t17);
    return t19
  ]);
  (8, [
    t20 := typeassert,ok x.(*math/big.Rat);
    t21 := extract t20 #0;
    t22 := extract t20 #1;
    if t22 goto 9 else 10
  ]);
  (9, [
    t23 := makeRat(t21);
    return t23
  ]);
  (10, [
    t24 := typeassert,ok x.(*math/big.Float);
    t25 := extract t24 #0;
    t26 := extract t24 #1;
    if t26 goto 11 else 12
  ]);
  (11, [
    t27 := makeFloat(t25);
    return t27
  ]);
  (12, [
    t28 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t28
  ])
].

Definition MakeBool b : FunctionBody.t := [
  (0, [
    t0 := changetype boolVal <- bool (b);
    t1 := make Value <- boolVal (t0);
    return t1
  ])
].

Definition MakeFloat64 x : FunctionBody.t := [
  (0, [
    t0 := math.IsInf(x, 0:int);
    if t0 goto 1 else 3
  ]);
  (1, [
    t1 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t1
  ]);
  (2, [
    t2 := smallFloat64(x);
    if t2 goto 4 else 5
  ]);
  (3, [
    t3 := math.IsNaN(x);
    if t3 goto 1 else 2
  ]);
  (4, [
    t4 := local ratVal (complit);
    t5 := &t4.val [#0];
    t6 := newRat();
    t7 := x + 0:float64;
    t8 := (*math/big.Rat).SetFloat64(t6, t7);
    *t5 = t8;
    t9 := *t4;
    t10 := make Value <- ratVal (t9);
    return t10
  ]);
  (5, [
    t11 := local floatVal (complit);
    t12 := &t11.val [#0];
    t13 := newFloat();
    t14 := x + 0:float64;
    t15 := (*math/big.Float).SetFloat64(t13, t14);
    *t12 = t15;
    t16 := *t11;
    t17 := make Value <- floatVal (t16);
    return t17
  ])
].

Definition MakeFromBytes bytes : FunctionBody.t := [
  (0, [
    t0 := len(bytes);
    t1 := t0 + 7:int;
    t2 := t1 / 8:int;
    t3 := make []math/big.Word t2 t2;
    t4 := len(bytes);
    jump 1
  ]);
  (1, [
    t5 := phi [0: 0:int, 2: t5, 4: t21] #i;
    t6 := phi [0: 0:math/big.Word, 2: t15, 4: 0:math/big.Word] #w;
    t7 := phi [0: 0:uint, 2: t16, 4: 0:uint] #s;
    t8 := phi [0: -1:int, 2: t9, 4: t9] #rangeindex;
    t9 := t8 + 1:int;
    t10 := t9 < t4;
    if t10 goto 2 else 3
  ]);
  (2, [
    t11 := &bytes[t9];
    t12 := *t11;
    t13 := convert math/big.Word <- byte (t12);
    t14 := t13 << t7;
    t15 := t6 | t14;
    t16 := t7 + 8:uint;
    t17 := t16 == 64:uint;
    if t17 goto 4 else 1
  ]);
  (3, [
    t18 := len(t3);
    t19 := t5 < t18;
    if t19 goto 5 else 8
  ]);
  (4, [
    t20 := &t3[t5];
    *t20 = t15;
    t21 := t5 + 1:int;
    jump 1
  ]);
  (5, [
    t22 := &t3[t5];
    *t22 = t6;
    t23 := t5 + 1:int;
    jump 8
  ]);
  (6, [
    t24 := t29 - 1:int;
    jump 8
  ]);
  (7, [
    t25 := newInt();
    t26 := slice t3[:t29];
    t27 := (*math/big.Int).SetBits(t25, t26);
    t28 := makeInt(t27);
    return t28
  ]);
  (8, [
    t29 := phi [3: t5, 6: t24, 5: t23] #i;
    t30 := t29 > 0:int;
    if t30 goto 9 else 7
  ]);
  (9, [
    t31 := t29 - 1:int;
    t32 := &t3[t31];
    t33 := *t32;
    t34 := t33 == 0:math/big.Word;
    if t34 goto 6 else 7
  ])
].

Definition MakeFromLiteral lit tok zero : FunctionBody.t := [
  (0, [
    t0 := zero != 0:uint;
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := make interface{} <- string ("MakeFromLiteral c...":string);
    panic t1
  ]);
  (2, [
    t2 := tok == 5:go/token.Token;
    if t2 goto 4 else 6
  ]);
  (3, [
    t3 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t3
  ]);
  (4, [
    t4 := strconv.ParseInt(lit, 0:int, 64:int);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    t7 := t6 == nil:error;
    if t7 goto 7 else 8
  ]);
  (5, [
    t8 := makeFloatFromLiteral(lit);
    t9 := t8 != nil:Value;
    if t9 goto 12 else 3
  ]);
  (6, [
    t10 := tok == 6:go/token.Token;
    if t10 goto 5 else 11
  ]);
  (7, [
    t11 := changetype int64Val <- int64 (t5);
    t12 := make Value <- int64Val (t11);
    return t12
  ]);
  (8, [
    t13 := newInt();
    t14 := (*math/big.Int).SetString(t13, lit, 0:int);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 9 else 3
  ]);
  (9, [
    t17 := local intVal (complit);
    t18 := &t17.val [#0];
    *t18 = t15;
    t19 := *t17;
    t20 := make Value <- intVal (t19);
    return t20
  ]);
  (10, [
    t21 := len(lit);
    t22 := t21 > 0:int;
    if t22 goto 16 else 3
  ]);
  (11, [
    t23 := tok == 7:go/token.Token;
    if t23 goto 10 else 14
  ]);
  (12, [
    return t8
  ]);
  (13, [
    t24 := len(lit);
    t25 := t24 >= 2:int;
    if t25 goto 20 else 3
  ]);
  (14, [
    t26 := tok == 8:go/token.Token;
    if t26 goto 13 else 19
  ]);
  (15, [
    t27 := t21 - 1:int;
    t28 := slice lit[:t27];
    t29 := makeFloatFromLiteral(t28);
    t30 := t29 != nil:Value;
    if t30 goto 17 else 3
  ]);
  (16, [
    t31 := t21 - 1:int;
    t32 := lit[t31];
    t33 := t32 == 105:byte;
    if t33 goto 15 else 3
  ]);
  (17, [
    t34 := make Value <- int64Val (0:int64Val);
    t35 := makeComplex(t34, t29);
    return t35
  ]);
  (18, [
    t36 := strconv.Unquote(lit);
    t37 := extract t36 #0;
    t38 := extract t36 #1;
    t39 := t38 == nil:error;
    if t39 goto 23 else 3
  ]);
  (19, [
    t40 := tok == 9:go/token.Token;
    if t40 goto 18 else 22
  ]);
  (20, [
    t41 := t24 - 1:int;
    t42 := slice lit[1:int:t41];
    t43 := strconv.UnquoteChar(t42, 39:byte);
    t44 := extract t43 #0;
    t45 := extract t43 #1;
    t46 := extract t43 #2;
    t47 := extract t43 #3;
    t48 := t47 == nil:error;
    if t48 goto 21 else 3
  ]);
  (21, [
    t49 := convert int64 <- rune (t44);
    t50 := MakeInt64(t49);
    return t50
  ]);
  (22, [
    t51 := new [1]any (varargs);
    t52 := &t51[0:int];
    t53 := make any <- go/token.Token (tok);
    *t52 = t53;
    t54 := slice t51[:];
    t55 := fmt.Sprintf("%v is not a valid...":string, t54...);
    t56 := make interface{} <- string (t55);
    panic t56
  ]);
  (23, [
    t57 := MakeString(t37);
    return t57
  ])
].

Definition MakeImag x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(unknownVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    return x
  ]);
  (2, [
    t3 := typeassert,ok x.(int64Val);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 3 else 4
  ]);
  (3, [
    t6 := make Value <- int64Val (0:int64Val);
    t7 := makeComplex(t6, x);
    return t7
  ]);
  (4, [
    t8 := typeassert,ok x.(intVal);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    if t10 goto 3 else 5
  ]);
  (5, [
    t11 := typeassert,ok x.(ratVal);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 3 else 6
  ]);
  (6, [
    t14 := typeassert,ok x.(floatVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 3 else 7
  ]);
  (7, [
    t17 := new [1]any (varargs);
    t18 := &t17[0:int];
    t19 := change interface any <- Value (x);
    *t18 = t19;
    t20 := slice t17[:];
    t21 := fmt.Sprintf("%v not Int or Float":string, t20...);
    t22 := make interface{} <- string (t21);
    panic t22
  ])
].

Definition MakeInt64 x : FunctionBody.t := [
  (0, [
    t0 := changetype int64Val <- int64 (x);
    t1 := make Value <- int64Val (t0);
    return t1
  ])
].

Definition MakeString s : FunctionBody.t := [
  (0, [
    t0 := s == "":string;
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := make Value <- *stringVal (emptyString);
    return t1
  ]);
  (2, [
    t2 := new stringVal (complit);
    t3 := &t2.s [#1];
    *t3 = s;
    t4 := make Value <- *stringVal (t2);
    return t4
  ])
].

Definition MakeUint64 x : FunctionBody.t := [
  (0, [
    t0 := x < 9223372036854775808:uint64;
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := convert int64 <- uint64 (x);
    t2 := changetype int64Val <- int64 (t1);
    t3 := make Value <- int64Val (t2);
    return t3
  ]);
  (2, [
    t4 := local intVal (complit);
    t5 := &t4.val [#0];
    t6 := newInt();
    t7 := (*math/big.Int).SetUint64(t6, x);
    *t5 = t7;
    t8 := *t4;
    t9 := make Value <- intVal (t8);
    return t9
  ])
].

Definition MakeUnknown : FunctionBody.t := [
  (0, [
    t0 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t0
  ])
].

Definition Num x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    t3 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t3
  ]);
  (2, [
    return x
  ]);
  (3, [
    t4 := typeassert,ok x.(intVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 2 else 4
  ]);
  (4, [
    t7 := typeassert,ok x.(ratVal);
    t8 := extract t7 #0;
    t9 := extract t7 #1;
    if t9 goto 5 else 6
  ]);
  (5, [
    t10 := local ratVal (x);
    *t10 = t8;
    t11 := &t10.val [#0];
    t12 := *t11;
    t13 := (*math/big.Rat).Num(t12);
    t14 := makeInt(t13);
    return t14
  ]);
  (6, [
    t15 := typeassert,ok x.(floatVal);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    if t17 goto 7 else 8
  ]);
  (7, [
    t18 := local floatVal (x);
    *t18 = t16;
    t19 := &t18.val [#0];
    t20 := *t19;
    t21 := smallFloat(t20);
    if t21 goto 9 else 1
  ]);
  (8, [
    t22 := typeassert,ok x.(unknownVal);
    t23 := extract t22 #0;
    t24 := extract t22 #1;
    if t24 goto 10 else 11
  ]);
  (9, [
    t25 := &t18.val [#0];
    t26 := *t25;
    t27 := (*math/big.Float).Rat(t26, nil:*math/big.Rat);
    t28 := extract t27 #0;
    t29 := extract t27 #1;
    t30 := (*math/big.Rat).Num(t28);
    t31 := makeInt(t30);
    return t31
  ]);
  (10, [
    jump 1
  ]);
  (11, [
    t32 := new [1]any (varargs);
    t33 := &t32[0:int];
    t34 := change interface any <- Value (x);
    *t33 = t34;
    t35 := slice t32[:];
    t36 := fmt.Sprintf("%v not Int or Float":string, t35...);
    t37 := make interface{} <- string (t36);
    panic t37
  ])
].

Definition Real x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(unknownVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    return x
  ]);
  (2, [
    t3 := typeassert,ok x.(int64Val);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 1 else 3
  ]);
  (3, [
    t6 := typeassert,ok x.(intVal);
    t7 := extract t6 #0;
    t8 := extract t6 #1;
    if t8 goto 1 else 4
  ]);
  (4, [
    t9 := typeassert,ok x.(ratVal);
    t10 := extract t9 #0;
    t11 := extract t9 #1;
    if t11 goto 1 else 5
  ]);
  (5, [
    t12 := typeassert,ok x.(floatVal);
    t13 := extract t12 #0;
    t14 := extract t12 #1;
    if t14 goto 1 else 6
  ]);
  (6, [
    t15 := typeassert,ok x.(complexVal);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    if t17 goto 7 else 8
  ]);
  (7, [
    t18 := local complexVal (x);
    *t18 = t16;
    t19 := &t18.re [#0];
    t20 := *t19;
    return t20
  ]);
  (8, [
    t21 := new [1]any (varargs);
    t22 := &t21[0:int];
    t23 := change interface any <- Value (x);
    *t22 = t23;
    t24 := slice t21[:];
    t25 := fmt.Sprintf("%v not numeric":string, t24...);
    t26 := make interface{} <- string (t25);
    panic t26
  ])
].

Definition Shift x op s : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(unknownVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    t3 := new [3]any (varargs);
    t4 := &t3[0:int];
    t5 := change interface any <- Value (x);
    *t4 = t5;
    t6 := &t3[1:int];
    t7 := make any <- go/token.Token (op);
    *t6 = t7;
    t8 := &t3[2:int];
    t9 := make any <- uint (s);
    *t8 = t9;
    t10 := slice t3[:];
    t11 := fmt.Sprintf("invalid shift %v ...":string, t10...);
    t12 := make interface{} <- string (t11);
    panic t12
  ]);
  (2, [
    t13 := make Value <- unknownVal (t1);
    return t13
  ]);
  (3, [
    t14 := typeassert,ok x.(int64Val);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 4 else 5
  ]);
  (4, [
    t17 := s == 0:uint;
    if t17 goto 6 else 7
  ]);
  (5, [
    t18 := typeassert,ok x.(intVal);
    t19 := extract t18 #0;
    t20 := extract t18 #1;
    if t20 goto 11 else 1
  ]);
  (6, [
    t21 := make Value <- int64Val (t15);
    return t21
  ]);
  (7, [
    t22 := op == 20:go/token.Token;
    if t22 goto 8 else 10
  ]);
  (8, [
    t23 := i64toi(t15);
    t24 := t23.val [#0];
    t25 := (*math/big.Int).Lsh(t24, t24, s);
    t26 := makeInt(t25);
    return t26
  ]);
  (9, [
    t27 := t15 >> s;
    t28 := make Value <- int64Val (t27);
    return t28
  ]);
  (10, [
    t29 := op == 21:go/token.Token;
    if t29 goto 9 else 1
  ]);
  (11, [
    t30 := local intVal (x);
    *t30 = t19;
    t31 := s == 0:uint;
    if t31 goto 12 else 13
  ]);
  (12, [
    t32 := *t30;
    t33 := make Value <- intVal (t32);
    return t33
  ]);
  (13, [
    t34 := newInt();
    t35 := op == 20:go/token.Token;
    if t35 goto 14 else 16
  ]);
  (14, [
    t36 := &t30.val [#0];
    t37 := *t36;
    t38 := (*math/big.Int).Lsh(t34, t37, s);
    t39 := makeInt(t38);
    return t39
  ]);
  (15, [
    t40 := &t30.val [#0];
    t41 := *t40;
    t42 := (*math/big.Int).Rsh(t34, t41, s);
    t43 := makeInt(t42);
    return t43
  ]);
  (16, [
    t44 := op == 21:go/token.Token;
    if t44 goto 15 else 1
  ])
].

Definition Sign x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := t1 < 0:int64Val;
    if t3 goto 3 else 5
  ]);
  (2, [
    t4 := typeassert,ok x.(intVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 7 else 8
  ]);
  (3, [
    return -1:int
  ]);
  (4, [
    return 1:int
  ]);
  (5, [
    t7 := t1 > 0:int64Val;
    if t7 goto 4 else 6
  ]);
  (6, [
    return 0:int
  ]);
  (7, [
    t8 := local intVal (x);
    *t8 = t5;
    t9 := &t8.val [#0];
    t10 := *t9;
    t11 := (*math/big.Int).Sign(t10);
    return t11
  ]);
  (8, [
    t12 := typeassert,ok x.(ratVal);
    t13 := extract t12 #0;
    t14 := extract t12 #1;
    if t14 goto 9 else 10
  ]);
  (9, [
    t15 := local ratVal (x);
    *t15 = t13;
    t16 := &t15.val [#0];
    t17 := *t16;
    t18 := (*math/big.Rat).Sign(t17);
    return t18
  ]);
  (10, [
    t19 := typeassert,ok x.(floatVal);
    t20 := extract t19 #0;
    t21 := extract t19 #1;
    if t21 goto 11 else 12
  ]);
  (11, [
    t22 := local floatVal (x);
    *t22 = t20;
    t23 := &t22.val [#0];
    t24 := *t23;
    t25 := (*math/big.Float).Sign(t24);
    return t25
  ]);
  (12, [
    t26 := typeassert,ok x.(complexVal);
    t27 := extract t26 #0;
    t28 := extract t26 #1;
    if t28 goto 13 else 14
  ]);
  (13, [
    t29 := local complexVal (x);
    *t29 = t27;
    t30 := &t29.re [#0];
    t31 := *t30;
    t32 := Sign(t31);
    t33 := &t29.im [#1];
    t34 := *t33;
    t35 := Sign(t34);
    t36 := t32 | t35;
    return t36
  ]);
  (14, [
    t37 := typeassert,ok x.(unknownVal);
    t38 := extract t37 #0;
    t39 := extract t37 #1;
    if t39 goto 15 else 16
  ]);
  (15, [
    return 1:int
  ]);
  (16, [
    t40 := new [1]any (varargs);
    t41 := &t40[0:int];
    t42 := change interface any <- Value (x);
    *t41 = t42;
    t43 := slice t40[:];
    t44 := fmt.Sprintf("%v not numeric":string, t43...);
    t45 := make interface{} <- string (t44);
    panic t45
  ])
].

Definition StringVal x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(*stringVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := (*stringVal).string(t1);
    return t3
  ]);
  (2, [
    t4 := typeassert,ok x.(unknownVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 3 else 4
  ]);
  (3, [
    return "":string
  ]);
  (4, [
    t7 := new [1]any (varargs);
    t8 := &t7[0:int];
    t9 := change interface any <- Value (x);
    *t8 = t9;
    t10 := slice t7[:];
    t11 := fmt.Sprintf("%v not a String":string, t10...);
    t12 := make interface{} <- string (t11);
    panic t12
  ])
].

Definition ToComplex x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := vtoc(x);
    t4 := make Value <- complexVal (t3);
    return t4
  ]);
  (2, [
    t5 := typeassert,ok x.(intVal);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 1 else 3
  ]);
  (3, [
    t8 := typeassert,ok x.(ratVal);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    if t10 goto 1 else 4
  ]);
  (4, [
    t11 := typeassert,ok x.(floatVal);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 1 else 5
  ]);
  (5, [
    t14 := typeassert,ok x.(complexVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 6 else 7
  ]);
  (6, [
    t17 := make Value <- complexVal (t15);
    return t17
  ]);
  (7, [
    t18 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t18
  ])
].

Definition ToFloat x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    t3 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t3
  ]);
  (2, [
    t4 := i64tor(t1);
    t5 := make Value <- ratVal (t4);
    return t5
  ]);
  (3, [
    t6 := typeassert,ok x.(intVal);
    t7 := extract t6 #0;
    t8 := extract t6 #1;
    if t8 goto 4 else 5
  ]);
  (4, [
    t9 := local intVal (x);
    *t9 = t7;
    t10 := &t9.val [#0];
    t11 := *t10;
    t12 := smallInt(t11);
    if t12 goto 6 else 7
  ]);
  (5, [
    t13 := typeassert,ok x.(ratVal);
    t14 := extract t13 #0;
    t15 := extract t13 #1;
    if t15 goto 8 else 9
  ]);
  (6, [
    t16 := *t9;
    t17 := itor(t16);
    t18 := make Value <- ratVal (t17);
    return t18
  ]);
  (7, [
    t19 := *t9;
    t20 := itof(t19);
    t21 := make Value <- floatVal (t20);
    return t21
  ]);
  (8, [
    return x
  ]);
  (9, [
    t22 := typeassert,ok x.(floatVal);
    t23 := extract t22 #0;
    t24 := extract t22 #1;
    if t24 goto 8 else 10
  ]);
  (10, [
    t25 := typeassert,ok x.(complexVal);
    t26 := extract t25 #0;
    t27 := extract t25 #1;
    if t27 goto 11 else 1
  ]);
  (11, [
    t28 := local complexVal (x);
    *t28 = t26;
    t29 := &t28.im [#1];
    t30 := *t29;
    t31 := Sign(t30);
    t32 := t31 == 0:int;
    if t32 goto 12 else 1
  ]);
  (12, [
    t33 := &t28.re [#0];
    t34 := *t33;
    t35 := ToFloat(t34);
    return t35
  ])
].

Definition ToInt x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    t3 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t3
  ]);
  (2, [
    return x
  ]);
  (3, [
    t4 := typeassert,ok x.(intVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 2 else 4
  ]);
  (4, [
    t7 := typeassert,ok x.(ratVal);
    t8 := extract t7 #0;
    t9 := extract t7 #1;
    if t9 goto 5 else 6
  ]);
  (5, [
    t10 := local ratVal (x);
    *t10 = t8;
    t11 := &t10.val [#0];
    t12 := *t11;
    t13 := (*math/big.Rat).IsInt(t12);
    if t13 goto 7 else 1
  ]);
  (6, [
    t14 := typeassert,ok x.(floatVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 8 else 9
  ]);
  (7, [
    t17 := &t10.val [#0];
    t18 := *t17;
    t19 := (*math/big.Rat).Num(t18);
    t20 := makeInt(t19);
    return t20
  ]);
  (8, [
    t21 := local floatVal (x);
    *t21 = t15;
    t22 := &t21.val [#0];
    t23 := *t22;
    t24 := smallFloat(t23);
    if t24 goto 10 else 1
  ]);
  (9, [
    t25 := typeassert,ok x.(complexVal);
    t26 := extract t25 #0;
    t27 := extract t25 #1;
    if t27 goto 16 else 1
  ]);
  (10, [
    t28 := newInt();
    t29 := &t21.val [#0];
    t30 := *t29;
    t31 := (*math/big.Float).Int(t30, t28);
    t32 := extract t31 #0;
    t33 := extract t31 #1;
    t34 := t33 == 0:math/big.Accuracy;
    if t34 goto 11 else 12
  ]);
  (11, [
    t35 := makeInt(t28);
    return t35
  ]);
  (12, [
    t36 := new math/big.Float (t);
    t37 := (*math/big.Float).SetPrec(t36, 508:uint);
    t38 := (*math/big.Float).SetMode(t36, 2:math/big.RoundingMode);
    t39 := &t21.val [#0];
    t40 := *t39;
    t41 := (*math/big.Float).Set(t36, t40);
    t42 := (*math/big.Float).Int(t36, t28);
    t43 := extract t42 #0;
    t44 := extract t42 #1;
    t45 := t44 == 0:math/big.Accuracy;
    if t45 goto 13 else 14
  ]);
  (13, [
    t46 := makeInt(t28);
    return t46
  ]);
  (14, [
    t47 := (*math/big.Float).SetMode(t36, 3:math/big.RoundingMode);
    t48 := &t21.val [#0];
    t49 := *t48;
    t50 := (*math/big.Float).Set(t36, t49);
    t51 := (*math/big.Float).Int(t36, t28);
    t52 := extract t51 #0;
    t53 := extract t51 #1;
    t54 := t53 == 0:math/big.Accuracy;
    if t54 goto 15 else 1
  ]);
  (15, [
    t55 := makeInt(t28);
    return t55
  ]);
  (16, [
    t56 := make Value <- complexVal (t26);
    t57 := ToFloat(t56);
    t58 := invoke t57.Kind();
    t59 := t58 == 4:Kind;
    if t59 goto 17 else 1
  ]);
  (17, [
    t60 := ToInt(t57);
    return t60
  ])
].

Definition Uint64Val x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(int64Val);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := convert uint64 <- int64Val (t1);
    t4 := t1 >= 0:int64Val;
    return t3, t4
  ]);
  (2, [
    t5 := typeassert,ok x.(intVal);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 3 else 4
  ]);
  (3, [
    t8 := local intVal (x);
    *t8 = t6;
    t9 := &t8.val [#0];
    t10 := *t9;
    t11 := (*math/big.Int).Uint64(t10);
    t12 := &t8.val [#0];
    t13 := *t12;
    t14 := (*math/big.Int).IsUint64(t13);
    return t11, t14
  ]);
  (4, [
    t15 := typeassert,ok x.(unknownVal);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    if t17 goto 5 else 6
  ]);
  (5, [
    return 0:uint64, false:bool
  ]);
  (6, [
    t18 := new [1]any (varargs);
    t19 := &t18[0:int];
    t20 := change interface any <- Value (x);
    *t19 = t20;
    t21 := slice t18[:];
    t22 := fmt.Sprintf("%v not an Int":string, t21...);
    t23 := make interface{} <- string (t22);
    panic t23
  ])
].

Definition UnaryOp op y prec : FunctionBody.t := [
  (0, [
    t0 := op == 12:go/token.Token;
    if t0 goto 1 else 3
  ]);
  (1, [
    t1 := typeassert,ok y.(unknownVal);
    t2 := extract t1 #0;
    t3 := extract t1 #1;
    if t3 goto 4 else 5
  ]);
  (2, [
    t4 := typeassert,ok y.(unknownVal);
    t5 := extract t4 #0;
    t6 := extract t4 #1;
    if t6 goto 12 else 13
  ]);
  (3, [
    t7 := op == 13:go/token.Token;
    if t7 goto 2 else 11
  ]);
  (4, [
    return y
  ]);
  (5, [
    t8 := typeassert,ok y.(int64Val);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    if t10 goto 4 else 6
  ]);
  (6, [
    t11 := typeassert,ok y.(intVal);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 4 else 7
  ]);
  (7, [
    t14 := typeassert,ok y.(ratVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 4 else 8
  ]);
  (8, [
    t17 := typeassert,ok y.(floatVal);
    t18 := extract t17 #0;
    t19 := extract t17 #1;
    if t19 goto 4 else 9
  ]);
  (9, [
    t20 := typeassert,ok y.(complexVal);
    t21 := extract t20 #0;
    t22 := extract t20 #1;
    if t22 goto 4 else 34
  ]);
  (10, [
    t23 := newInt();
    t24 := typeassert,ok y.(unknownVal);
    t25 := extract t24 #0;
    t26 := extract t24 #1;
    if t26 goto 28 else 29
  ]);
  (11, [
    t27 := op == 19:go/token.Token;
    if t27 goto 10 else 26
  ]);
  (12, [
    t28 := make Value <- unknownVal (t5);
    return t28
  ]);
  (13, [
    t29 := typeassert,ok y.(int64Val);
    t30 := extract t29 #0;
    t31 := extract t29 #1;
    if t31 goto 14 else 15
  ]);
  (14, [
    t32 := -t30;
    t33 := t32 != t30;
    if t33 goto 16 else 17
  ]);
  (15, [
    t34 := typeassert,ok y.(intVal);
    t35 := extract t34 #0;
    t36 := extract t34 #1;
    if t36 goto 18 else 19
  ]);
  (16, [
    t37 := make Value <- int64Val (t32);
    return t37
  ]);
  (17, [
    t38 := newInt();
    t39 := changetype int64 <- int64Val (t30);
    t40 := math/big.NewInt(t39);
    t41 := (*math/big.Int).Neg(t38, t40);
    t42 := makeInt(t41);
    return t42
  ]);
  (18, [
    t43 := local intVal (y);
    *t43 = t35;
    t44 := newInt();
    t45 := &t43.val [#0];
    t46 := *t45;
    t47 := (*math/big.Int).Neg(t44, t46);
    t48 := makeInt(t47);
    return t48
  ]);
  (19, [
    t49 := typeassert,ok y.(ratVal);
    t50 := extract t49 #0;
    t51 := extract t49 #1;
    if t51 goto 20 else 21
  ]);
  (20, [
    t52 := local ratVal (y);
    *t52 = t50;
    t53 := newRat();
    t54 := &t52.val [#0];
    t55 := *t54;
    t56 := (*math/big.Rat).Neg(t53, t55);
    t57 := makeRat(t56);
    return t57
  ]);
  (21, [
    t58 := typeassert,ok y.(floatVal);
    t59 := extract t58 #0;
    t60 := extract t58 #1;
    if t60 goto 22 else 23
  ]);
  (22, [
    t61 := local floatVal (y);
    *t61 = t59;
    t62 := newFloat();
    t63 := &t61.val [#0];
    t64 := *t63;
    t65 := (*math/big.Float).Neg(t62, t64);
    t66 := makeFloat(t65);
    return t66
  ]);
  (23, [
    t67 := typeassert,ok y.(complexVal);
    t68 := extract t67 #0;
    t69 := extract t67 #1;
    if t69 goto 24 else 34
  ]);
  (24, [
    t70 := local complexVal (y);
    *t70 = t68;
    t71 := &t70.re [#0];
    t72 := *t71;
    t73 := UnaryOp(13:go/token.Token, t72, 0:uint);
    t74 := &t70.im [#1];
    t75 := *t74;
    t76 := UnaryOp(13:go/token.Token, t75, 0:uint);
    t77 := makeComplex(t73, t76);
    return t77
  ]);
  (25, [
    t78 := typeassert,ok y.(unknownVal);
    t79 := extract t78 #0;
    t80 := extract t78 #1;
    if t80 goto 37 else 38
  ]);
  (26, [
    t81 := op == 43:go/token.Token;
    if t81 goto 25 else 34
  ]);
  (27, [
    t82 := prec > 0:uint;
    if t82 goto 35 else 36
  ]);
  (28, [
    t83 := make Value <- unknownVal (t25);
    return t83
  ]);
  (29, [
    t84 := typeassert,ok y.(int64Val);
    t85 := extract t84 #0;
    t86 := extract t84 #1;
    if t86 goto 30 else 31
  ]);
  (30, [
    t87 := changetype int64 <- int64Val (t85);
    t88 := math/big.NewInt(t87);
    t89 := (*math/big.Int).Not(t23, t88);
    jump 27
  ]);
  (31, [
    t90 := typeassert,ok y.(intVal);
    t91 := extract t90 #0;
    t92 := extract t90 #1;
    if t92 goto 32 else 33
  ]);
  (32, [
    t93 := local intVal (y);
    *t93 = t91;
    t94 := &t93.val [#0];
    t95 := *t94;
    t96 := (*math/big.Int).Not(t23, t95);
    jump 27
  ]);
  (33, [
    jump 34
  ]);
  (34, [
    t97 := new [2]any (varargs);
    t98 := &t97[0:int];
    t99 := make any <- go/token.Token (op);
    *t98 = t99;
    t100 := &t97[1:int];
    t101 := change interface any <- Value (y);
    *t100 = t101;
    t102 := slice t97[:];
    t103 := fmt.Sprintf("invalid unary ope...":string, t102...);
    t104 := make interface{} <- string (t103);
    panic t104
  ]);
  (35, [
    t105 := newInt();
    t106 := math/big.NewInt(-1:int64);
    t107 := (*math/big.Int).Lsh(t105, t106, prec);
    t108 := (*math/big.Int).AndNot(t23, t23, t107);
    jump 36
  ]);
  (36, [
    t109 := makeInt(t23);
    return t109
  ]);
  (37, [
    t110 := make Value <- unknownVal (t79);
    return t110
  ]);
  (38, [
    t111 := typeassert,ok y.(boolVal);
    t112 := extract t111 #0;
    t113 := extract t111 #1;
    if t113 goto 39 else 34
  ]);
  (39, [
    t114 := !t112;
    t115 := make Value <- boolVal (t114);
    return t115
  ])
].

Definition Val x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(boolVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    t3 := changetype bool <- boolVal (t1);
    t4 := make any <- bool (t3);
    return t4
  ]);
  (2, [
    t5 := typeassert,ok x.(*stringVal);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    if t7 goto 3 else 4
  ]);
  (3, [
    t8 := (*stringVal).string(t6);
    t9 := make any <- string (t8);
    return t9
  ]);
  (4, [
    t10 := typeassert,ok x.(int64Val);
    t11 := extract t10 #0;
    t12 := extract t10 #1;
    if t12 goto 5 else 6
  ]);
  (5, [
    t13 := changetype int64 <- int64Val (t11);
    t14 := make any <- int64 (t13);
    return t14
  ]);
  (6, [
    t15 := typeassert,ok x.(intVal);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    if t17 goto 7 else 8
  ]);
  (7, [
    t18 := local intVal (x);
    *t18 = t16;
    t19 := &t18.val [#0];
    t20 := *t19;
    t21 := make any <- *math/big.Int (t20);
    return t21
  ]);
  (8, [
    t22 := typeassert,ok x.(ratVal);
    t23 := extract t22 #0;
    t24 := extract t22 #1;
    if t24 goto 9 else 10
  ]);
  (9, [
    t25 := local ratVal (x);
    *t25 = t23;
    t26 := &t25.val [#0];
    t27 := *t26;
    t28 := make any <- *math/big.Rat (t27);
    return t28
  ]);
  (10, [
    t29 := typeassert,ok x.(floatVal);
    t30 := extract t29 #0;
    t31 := extract t29 #1;
    if t31 goto 11 else 12
  ]);
  (11, [
    t32 := local floatVal (x);
    *t32 = t30;
    t33 := &t32.val [#0];
    t34 := *t33;
    t35 := make any <- *math/big.Float (t34);
    return t35
  ]);
  (12, [
    return nil:any
  ])
].

Definition add x y : FunctionBody.t := [
  (0, [
    t0 := BinaryOp(x, 12:go/token.Token, y);
    return t0
  ])
].

Definition cmpZero x op : FunctionBody.t := [
  (0, [
    t0 := op == 39:go/token.Token;
    if t0 goto 1 else 3
  ]);
  (1, [
    t1 := x == 0:int;
    return t1
  ]);
  (2, [
    t2 := x != 0:int;
    return t2
  ]);
  (3, [
    t3 := op == 44:go/token.Token;
    if t3 goto 2 else 5
  ]);
  (4, [
    t4 := x < 0:int;
    return t4
  ]);
  (5, [
    t5 := op == 40:go/token.Token;
    if t5 goto 4 else 7
  ]);
  (6, [
    t6 := x <= 0:int;
    return t6
  ]);
  (7, [
    t7 := op == 45:go/token.Token;
    if t7 goto 6 else 9
  ]);
  (8, [
    t8 := x > 0:int;
    return t8
  ]);
  (9, [
    t9 := op == 41:go/token.Token;
    if t9 goto 8 else 11
  ]);
  (10, [
    t10 := x >= 0:int;
    return t10
  ]);
  (11, [
    t11 := op == 46:go/token.Token;
    if t11 goto 10 else 12
  ]);
  (12, [
    t12 := new [2]any (varargs);
    t13 := &t12[0:int];
    t14 := make any <- int (x);
    *t13 = t14;
    t15 := &t12[1:int];
    t16 := make any <- go/token.Token (op);
    *t15 = t16;
    t17 := slice t12[:];
    t18 := fmt.Sprintf("invalid compariso...":string, t17...);
    t19 := make interface{} <- string (t18);
    panic t19
  ])
].

Definition i64tof x : FunctionBody.t := [
  (0, [
    t0 := local floatVal (complit);
    t1 := &t0.val [#0];
    t2 := newFloat();
    t3 := changetype int64 <- int64Val (x);
    t4 := (*math/big.Float).SetInt64(t2, t3);
    *t1 = t4;
    t5 := *t0;
    return t5
  ])
].

Definition i64toi x : FunctionBody.t := [
  (0, [
    t0 := local intVal (complit);
    t1 := &t0.val [#0];
    t2 := newInt();
    t3 := changetype int64 <- int64Val (x);
    t4 := (*math/big.Int).SetInt64(t2, t3);
    *t1 = t4;
    t5 := *t0;
    return t5
  ])
].

Definition i64tor x : FunctionBody.t := [
  (0, [
    t0 := local ratVal (complit);
    t1 := &t0.val [#0];
    t2 := newRat();
    t3 := changetype int64 <- int64Val (x);
    t4 := (*math/big.Rat).SetInt64(t2, t3);
    *t1 = t4;
    t5 := *t0;
    return t5
  ])
].

Definition init : FunctionBody.t := [
  (0, [
    t0 := *init$guard;
    if t0 goto 2 else 1
  ]);
  (1, [
    *init$guard = true:bool;
    t1 := strconv.init();
    t2 := fmt.init();
    t3 := go/token.init();
    t4 := math.init();
    t5 := math/big.init();
    t6 := math/bits.init();
    t7 := strings.init();
    t8 := sync.init();
    t9 := unicode/utf8.init();
    t10 := &_Kind_index[0:int];
    t11 := &_Kind_index[1:int];
    t12 := &_Kind_index[2:int];
    t13 := &_Kind_index[3:int];
    t14 := &_Kind_index[4:int];
    t15 := &_Kind_index[5:int];
    t16 := &_Kind_index[6:int];
    *t10 = 0:uint8;
    *t11 = 7:uint8;
    *t12 = 11:uint8;
    *t13 = 17:uint8;
    *t14 = 20:uint8;
    *t15 = 25:uint8;
    *t16 = 32:uint8;
    t17 := &floatVal0.val [#0];
    t18 := newFloat();
    *t17 = t18;
    jump 2
  ]);
  (2, [
    return
  ])
].

Definition is32bit x : FunctionBody.t := [
  (0, [
    t0 := -2147483648:int64 <= x;
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := x <= 2147483647:int64;
    jump 2
  ]);
  (2, [
    t2 := phi [0: false:bool, 1: t1] #&&;
    return t2
  ])
].

Definition is63bit x : FunctionBody.t := [
  (0, [
    t0 := -4611686018427387904:int64 <= x;
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := x <= 4611686018427387903:int64;
    jump 2
  ]);
  (2, [
    t2 := phi [0: false:bool, 1: t1] #&&;
    return t2
  ])
].

Definition itof x : FunctionBody.t := [
  (0, [
    t0 := local intVal (x);
    *t0 = x;
    t1 := local floatVal (complit);
    t2 := &t1.val [#0];
    t3 := newFloat();
    t4 := &t0.val [#0];
    t5 := *t4;
    t6 := (*math/big.Float).SetInt(t3, t5);
    *t2 = t6;
    t7 := *t1;
    return t7
  ])
].

Definition itor x : FunctionBody.t := [
  (0, [
    t0 := local intVal (x);
    *t0 = x;
    t1 := local ratVal (complit);
    t2 := &t1.val [#0];
    t3 := newRat();
    t4 := &t0.val [#0];
    t5 := *t4;
    t6 := (*math/big.Rat).SetInt(t3, t5);
    *t2 = t6;
    t7 := *t1;
    return t7
  ])
].

Definition makeComplex re im : FunctionBody.t := [
  (0, [
    t0 := invoke re.Kind();
    t1 := t0 == 0:Kind;
    if t1 goto 1 else 3
  ]);
  (1, [
    t2 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t2
  ]);
  (2, [
    t3 := local complexVal (complit);
    t4 := &t3.re [#0];
    t5 := &t3.im [#1];
    *t4 = re;
    *t5 = im;
    t6 := *t3;
    t7 := make Value <- complexVal (t6);
    return t7
  ]);
  (3, [
    t8 := invoke im.Kind();
    t9 := t8 == 0:Kind;
    if t9 goto 1 else 2
  ])
].

Definition makeFloat x : FunctionBody.t := [
  (0, [
    t0 := (*math/big.Float).Sign(x);
    t1 := t0 == 0:int;
    if t1 goto 1 else 2
  ]);
  (1, [
    t2 := *floatVal0;
    t3 := make Value <- floatVal (t2);
    return t3
  ]);
  (2, [
    t4 := (*math/big.Float).IsInf(x);
    if t4 goto 3 else 4
  ]);
  (3, [
    t5 := make Value <- unknownVal (struct{}{}:unknownVal);
    return t5
  ]);
  (4, [
    t6 := local floatVal (complit);
    t7 := &t6.val [#0];
    *t7 = x;
    t8 := *t6;
    t9 := make Value <- floatVal (t8);
    return t9
  ])
].

Definition makeFloatFromLiteral lit : FunctionBody.t := [
  (0, [
    t0 := newFloat();
    t1 := (*math/big.Float).SetString(t0, lit);
    t2 := extract t1 #0;
    t3 := extract t1 #1;
    if t3 goto 1 else 2
  ]);
  (1, [
    t4 := smallFloat(t2);
    if t4 goto 3 else 4
  ]);
  (2, [
    return nil:Value
  ]);
  (3, [
    t5 := (*math/big.Float).Sign(t2);
    t6 := t5 == 0:int;
    if t6 goto 5 else 6
  ]);
  (4, [
    t7 := makeFloat(t2);
    return t7
  ]);
  (5, [
    jump 6
  ]);
  (6, [
    t8 := phi [3: lit, 5: "0":string] #lit;
    t9 := newRat();
    t10 := (*math/big.Rat).SetString(t9, t8);
    t11 := extract t10 #0;
    t12 := extract t10 #1;
    if t12 goto 7 else 4
  ]);
  (7, [
    t13 := local ratVal (complit);
    t14 := &t13.val [#0];
    *t14 = t11;
    t15 := *t13;
    t16 := make Value <- ratVal (t15);
    return t16
  ])
].

Definition makeInt x : FunctionBody.t := [
  (0, [
    t0 := (*math/big.Int).IsInt64(x);
    if t0 goto 1 else 2
  ]);
  (1, [
    t1 := (*math/big.Int).Int64(x);
    t2 := changetype int64Val <- int64 (t1);
    t3 := make Value <- int64Val (t2);
    return t3
  ]);
  (2, [
    t4 := local intVal (complit);
    t5 := &t4.val [#0];
    *t5 = x;
    t6 := *t4;
    t7 := make Value <- intVal (t6);
    return t7
  ])
].

Definition makeRat x : FunctionBody.t := [
  (0, [
    t0 := (*math/big.Rat).Num(x);
    t1 := (*math/big.Rat).Denom(x);
    t2 := smallInt(t0);
    if t2 goto 3 else 2
  ]);
  (1, [
    t3 := local ratVal (complit);
    t4 := &t3.val [#0];
    *t4 = x;
    t5 := *t3;
    t6 := make Value <- ratVal (t5);
    return t6
  ]);
  (2, [
    t7 := local floatVal (complit);
    t8 := &t7.val [#0];
    t9 := newFloat();
    t10 := (*math/big.Float).SetRat(t9, x);
    *t8 = t10;
    t11 := *t7;
    t12 := make Value <- floatVal (t11);
    return t12
  ]);
  (3, [
    t13 := smallInt(t1);
    if t13 goto 1 else 2
  ])
].

Definition match x y : FunctionBody.t := [
  (0, [
    t0 := ord(x);
    t1 := ord(y);
    t2 := t0 < t1;
    if t2 goto 2 else 4
  ]);
  (1, [
    t3 := phi [2: t6, 3: t10, 4: x] #x;
    t4 := phi [2: t7, 3: t9, 4: y] #y;
    return t3, t4
  ]);
  (2, [
    t5 := match0(x, y);
    t6 := extract t5 #0;
    t7 := extract t5 #1;
    jump 1
  ]);
  (3, [
    t8 := match0(y, x);
    t9 := extract t8 #0;
    t10 := extract t8 #1;
    jump 1
  ]);
  (4, [
    t11 := t0 > t1;
    if t11 goto 3 else 1
  ])
].

Definition match0 x y : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok y.(intVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 2 else 3
  ]);
  (1, [
    return x, x
  ]);
  (2, [
    t3 := typeassert,ok x.(int64Val);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 4 else 1
  ]);
  (3, [
    t6 := typeassert,ok y.(ratVal);
    t7 := extract t6 #0;
    t8 := extract t6 #1;
    if t8 goto 5 else 6
  ]);
  (4, [
    t9 := i64toi(t4);
    t10 := make Value <- intVal (t9);
    return t10, y
  ]);
  (5, [
    t11 := typeassert,ok x.(int64Val);
    t12 := extract t11 #0;
    t13 := extract t11 #1;
    if t13 goto 7 else 8
  ]);
  (6, [
    t14 := typeassert,ok y.(floatVal);
    t15 := extract t14 #0;
    t16 := extract t14 #1;
    if t16 goto 10 else 11
  ]);
  (7, [
    t17 := i64tor(t12);
    t18 := make Value <- ratVal (t17);
    return t18, y
  ]);
  (8, [
    t19 := typeassert,ok x.(intVal);
    t20 := extract t19 #0;
    t21 := extract t19 #1;
    if t21 goto 9 else 1
  ]);
  (9, [
    t22 := itor(t20);
    t23 := make Value <- ratVal (t22);
    return t23, y
  ]);
  (10, [
    t24 := typeassert,ok x.(int64Val);
    t25 := extract t24 #0;
    t26 := extract t24 #1;
    if t26 goto 12 else 13
  ]);
  (11, [
    t27 := typeassert,ok y.(complexVal);
    t28 := extract t27 #0;
    t29 := extract t27 #1;
    if t29 goto 17 else 1
  ]);
  (12, [
    t30 := i64tof(t25);
    t31 := make Value <- floatVal (t30);
    return t31, y
  ]);
  (13, [
    t32 := typeassert,ok x.(intVal);
    t33 := extract t32 #0;
    t34 := extract t32 #1;
    if t34 goto 14 else 15
  ]);
  (14, [
    t35 := itof(t33);
    t36 := make Value <- floatVal (t35);
    return t36, y
  ]);
  (15, [
    t37 := typeassert,ok x.(ratVal);
    t38 := extract t37 #0;
    t39 := extract t37 #1;
    if t39 goto 16 else 1
  ]);
  (16, [
    t40 := rtof(t38);
    t41 := make Value <- floatVal (t40);
    return t41, y
  ]);
  (17, [
    t42 := vtoc(x);
    t43 := make Value <- complexVal (t42);
    return t43, y
  ])
].

Definition mul x y : FunctionBody.t := [
  (0, [
    t0 := BinaryOp(x, 14:go/token.Token, y);
    return t0
  ])
].

Definition newFloat : FunctionBody.t := [
  (0, [
    t0 := new math/big.Float (new);
    t1 := (*math/big.Float).SetPrec(t0, 512:uint);
    return t1
  ])
].

Definition newInt : FunctionBody.t := [
  (0, [
    t0 := new math/big.Int (new);
    return t0
  ])
].

Definition newRat : FunctionBody.t := [
  (0, [
    t0 := new math/big.Rat (new);
    return t0
  ])
].

Definition ord x : FunctionBody.t := [
  (0, [
    t0 := typeassert,ok x.(unknownVal);
    t1 := extract t0 #0;
    t2 := extract t0 #1;
    if t2 goto 1 else 2
  ]);
  (1, [
    return 0:int
  ]);
  (2, [
    t3 := typeassert,ok x.(boolVal);
    t4 := extract t3 #0;
    t5 := extract t3 #1;
    if t5 goto 3 else 4
  ]);
  (3, [
    return 1:int
  ]);
  (4, [
    t6 := typeassert,ok x.(*stringVal);
    t7 := extract t6 #0;
    t8 := extract t6 #1;
    if t8 goto 3 else 5
  ]);
  (5, [
    t9 := typeassert,ok x.(int64Val);
    t10 := extract t9 #0;
    t11 := extract t9 #1;
    if t11 goto 6 else 7
  ]);
  (6, [
    return 2:int
  ]);
  (7, [
    t12 := typeassert,ok x.(intVal);
    t13 := extract t12 #0;
    t14 := extract t12 #1;
    if t14 goto 8 else 9
  ]);
  (8, [
    return 3:int
  ]);
  (9, [
    t15 := typeassert,ok x.(ratVal);
    t16 := extract t15 #0;
    t17 := extract t15 #1;
    if t17 goto 10 else 11
  ]);
  (10, [
    return 4:int
  ]);
  (11, [
    t18 := typeassert,ok x.(floatVal);
    t19 := extract t18 #0;
    t20 := extract t18 #1;
    if t20 goto 12 else 13
  ]);
  (12, [
    return 5:int
  ]);
  (13, [
    t21 := typeassert,ok x.(complexVal);
    t22 := extract t21 #0;
    t23 := extract t21 #1;
    if t23 goto 14 else 15
  ]);
  (14, [
    return 6:int
  ]);
  (15, [
    return -1:int
  ])
].

Definition quo x y : FunctionBody.t := [
  (0, [
    t0 := BinaryOp(x, 15:go/token.Token, y);
    return t0
  ])
].

Definition reverse x : FunctionBody.t := [
  (0, [
    t0 := len(x);
    jump 3
  ]);
  (1, [
    t1 := t0 - 1:int;
    t2 := t1 - t12;
    t3 := t0 - 1:int;
    t4 := t3 - t12;
    t5 := &x[t4];
    t6 := *t5;
    t7 := &x[t12];
    t8 := *t7;
    t9 := &x[t12];
    *t9 = t6;
    t10 := &x[t2];
    *t10 = t8;
    t11 := t12 + 1:int;
    jump 3
  ]);
  (2, [
    return x
  ]);
  (3, [
    t12 := phi [0: 0:int, 1: t11] #i;
    t13 := t12 + t12;
    t14 := t13 < t0;
    if t14 goto 1 else 2
  ])
].

Definition rtof x : FunctionBody.t := [
  (0, [
    t0 := local ratVal (x);
    *t0 = x;
    t1 := local floatVal (complit);
    t2 := &t1.val [#0];
    t3 := newFloat();
    t4 := &t0.val [#0];
    t5 := *t4;
    t6 := (*math/big.Float).SetRat(t3, t5);
    *t2 = t6;
    t7 := *t1;
    return t7
  ])
].

Definition smallFloat x : FunctionBody.t := [
  (0, [
    t0 := (*math/big.Float).IsInf(x);
    if t0 goto 1 else 2
  ]);
  (1, [
    return false:bool
  ]);
  (2, [
    t1 := (*math/big.Float).MantExp(x, nil:*math/big.Float);
    t2 := -4096:int < t1;
    if t2 goto 3 else 4
  ]);
  (3, [
    t3 := t1 < 4096:int;
    jump 4
  ]);
  (4, [
    t4 := phi [2: false:bool, 3: t3] #&&;
    return t4
  ])
].

Definition smallFloat64 x : FunctionBody.t := [
  (0, [
    t0 := math.IsInf(x, 0:int);
    if t0 goto 1 else 2
  ]);
  (1, [
    return false:bool
  ]);
  (2, [
    t1 := math.Frexp(x);
    t2 := extract t1 #0;
    t3 := extract t1 #1;
    t4 := -4096:int < t3;
    if t4 goto 3 else 4
  ]);
  (3, [
    t5 := t3 < 4096:int;
    jump 4
  ]);
  (4, [
    t6 := phi [2: false:bool, 3: t5] #&&;
    return t6
  ])
].

Definition smallInt x : FunctionBody.t := [
  (0, [
    t0 := (*math/big.Int).BitLen(x);
    t1 := t0 < 4096:int;
    return t1
  ])
].

Definition sub x y : FunctionBody.t := [
  (0, [
    t0 := BinaryOp(x, 13:go/token.Token, y);
    return t0
  ])
].

Definition vtoc x : FunctionBody.t := [
  (0, [
    t0 := local complexVal (complit);
    t1 := &t0.re [#0];
    t2 := &t0.im [#1];
    *t1 = x;
    t3 := make Value <- int64Val (0:int64Val);
    *t2 = t3;
    t4 := *t0;
    return t4
  ])
].

(** ** Types *)

Type: Kind

Type: Value

Type: boolVal

Type: complexVal

Type: floatVal

Type: int64Val

Type: intVal

Type: ratVal

Type: stringVal

Type: unknownVal

