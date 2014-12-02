Require Import String.
Require Import ZArith.
Require Import List.
Import BinIntDef.



Section lang.


Inductive mname := mod_name : string -> mname.
Inductive vname := var_name : string -> vname.
Inductive pname := fun_name : string -> pname.
Inductive tname := type_name : string -> tname.
Inductive cname := constr_name : string -> cname.
Inductive constr := constr_def : cname -> list tname -> constr.



(* 比較演算子がない *)
Inductive binop :=
| b_and
| b_or
| b_plus
| b_minus
| b_time
| b_div
| b_mod
| b_append.


(* あと整数とかboolとか *)
Inductive exp : Set :=
| var : vname -> exp
| con : cname -> exp
| boolean : bool -> exp
| num : Z -> exp
| str : string -> exp
| binary : binop -> exp -> exp -> exp
| application : exp -> exp -> exp.



Inductive val : Set :=
| con_val : con_values -> val (* induction schemeが怪しいので注意 *)
| boolean_val : bool -> val
| num_val : Z -> val
| str_val : string -> val


with con_values : Set :=
| con_name : cname -> con_values
| con_args : con_values -> val -> con_values
.



(* functionというより手続き？ *)
Inductive proc : Set :=
(*| Pblock  : list vname -> proc -> proc*)
| Pseq    : proc -> proc -> proc (* 左結合などを意識した方がいいか *)
| Pwhile  : exp -> proc -> proc
| Pmatch  : exp -> list proc -> proc
| Passign : vname -> exp -> proc
| Pcall   : pname -> proc (* 引数あったけどやめた。面倒くさい *)
.


Inductive declaration :=
| type_decl : tname -> list constr -> declaration
| proc_decl : pname -> proc -> declaration.


Record module := { Mname : mname; Mdecls : list declaration }.

Record program := { Pmods : list mname; Pdecls : list declaration; Pmain : proc }.

Record in_program := { Idecls : list declaration; current : proc }.


Axiom var_val : vname -> val -> Prop.
Axiom var_val_eq :forall v v1 v2, var_val v v1 -> var_val v v2 -> v1 = v2.
Axiom var_val_neq : forall v v1 v2, ~ var_val v v1 -> var_val v v2 -> v1 <> v2.

(*
Inductive list_forall {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
| nil_forall : list_forall P nil nil
| cons_forall : forall a b la lb, P a b -> list_forall P la lb -> list_forall P (cons a la) (cons b lb).
*)


(** semantics of exp **)
Inductive binop_apply : binop -> val -> val -> val -> Prop :=
| binop_and  : forall b1 b2, binop_apply b_and (boolean_val b1) (boolean_val b2) (boolean_val (andb b1 b2))
| binop_or   : forall b1 b2, binop_apply b_or  (boolean_val b1) (boolean_val b2) (boolean_val (orb  b1 b2))
| binop_plus  : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 + z2)%Z)
| binop_minus : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 - z2)%Z)
| binop_time  : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 * z2)%Z)
| binop_div   : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 / z2)%Z)
| binop_mod   : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 mod z2)%Z)
| binop_append : forall s1 s2, binop_apply b_plus (str_val s1) (str_val s2) (str_val (append s1 s2))
.

Inductive exp_val : exp -> val -> Prop :=
| val_var : forall v e, var_val v e -> exp_val (var v) e
| val_constructor : forall c v, exp_val_constructor c v -> exp_val c (con_val v)
| val_boolean : forall b, exp_val (boolean b) (boolean_val b)
| val_num : forall z, exp_val (num z) (num_val z)
| val_str : forall s, exp_val (str s) (str_val s)
| val_binop : forall op e1 e2 v1 v2 v, exp_val e1 v1 -> exp_val e2 v2 -> binop_apply op v1 v2 v -> exp_val (binary op e1 e2) v

with exp_val_constructor : exp -> con_values -> Prop :=
| val_con_name : forall c, exp_val_constructor (con c) (con_name c)
| val_con_args : forall c e cv v, exp_val_constructor c cv -> exp_val e v -> exp_val_constructor (application c e) (con_args cv v)
.



Axiom pname_decl : list declaration -> pname -> proc -> Prop.

(* no type checking. If a program is not well-typed, the semantics of it may not be defined. *)

Inductive verify (decls : list declaration) : proc -> Prop -> Prop -> Prop :=
| Vseq    : forall p1 p2 P1 P P2, verify decls p1 P1 P -> verify decls p2 P P2 -> verify decls (Pseq p1 p2) P1 P2
| Vwhile  : forall e p P, verify decls p (P /\ exp_val e (boolean_val true)) P -> verify decls (Pwhile e p) P (P /\ exp_val e (boolean_val false))
(* | Pmatch  : exp -> list proc -> proc *)
| Vassign : forall v e (P : exp -> Prop), verify decls (Passign v e) (P e) (P (var v))
| Vcall   : forall pn p P1 P2, pname_decl decls pn p -> verify decls p P1 P2 -> verify decls (Pcall pn) P1 P2
| Vweaken : forall p P1 P2 (P : Prop), verify decls p P1 P2 -> (P -> P1) -> verify decls p P P2
.

(*
Goal verify nil (Passign (var_name "a") (var (var_name "b"))) (exp_val (var (var_name "b")) (num_val 1%Z)) (exp_val (var (var_name "a")) (num_val 1%Z)).
apply Vassign with (P := fun v => exp_val v (num_val 1%Z)).
Qed.
*)

(* lazy verification system (unsound if you do not care about assignment) *)

End lang.
