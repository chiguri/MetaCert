Require Import String.
Require Import ZArith.
Require Import List.
Import BinIntDef.



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
| b_eq
| b_lt
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


Coercion num : Z >-> exp.
Coercion boolean : bool >-> exp.

Open Scope string.
Open Scope Z.

Notation "'V' @ x" := (var (var_name x)) (at level 10).
Notation "'C' @ x" := (con (constr_name x)) (at level 10).
Notation "x +' y" := (binary b_plus x y) (at level 15).
Notation "'S' @ x" := (str x) (at level 10).
Notation "x $ y" := (application x y) (at level 14, left associativity).



Inductive val : Set :=
| con_val : con_values -> val (* induction schemeが怪しいので注意 *)
| boolean_val : bool -> val
| num_val : Z -> val
| str_val : string -> val


with con_values : Set :=
| con_name : cname -> con_values
| con_args : con_values -> val -> con_values
.

Coercion num_val : Z >-> val.
Coercion boolean_val : bool >-> val.

Notation "'C' # s" := (con_name (constr_name s)) (at level 10).
Notation "'S' # x" := (str_val x) (at level 10).
Notation "x #$ y" := (con_args x y) (at level 14, left associativity).
Notation "[[ x ]]" := (con_val x) (at level 15).

Inductive proc : Set :=
| Pseq    : proc -> proc -> proc
| Pwhile  : exp -> proc -> proc
| Pmatch  : exp -> list proc -> proc
| Passign : vname -> exp -> proc
| Pcall   : pname -> proc
.


Notation "x :== y" := (Passign (var_name x) y) (at level 20).
Notation "P1 ;; P2" := (Pseq P1 P2) (at level 22).



Inductive declaration :=
| type_decl : tname -> list constr -> declaration
| proc_decl : pname -> proc -> declaration.


Record module := { Mname : mname; Mdecls : list declaration }.

Record program := { Pmods : list mname; Pdecls : list declaration; Pmain : proc }.

Record in_program := { Idecls : list declaration; current : proc }.


Axiom var_val : vname -> val -> Prop.
Axiom var_val_eq :forall v v1 v2, var_val v v1 -> var_val v v2 -> v1 = v2.
Definition var_val_neq : forall v v1 v2, ~ var_val v v1 -> var_val v v2 -> v1 <> v2.
intros.
intro.
apply H; rewrite H1; apply H0.
Qed.
(*
Inductive list_forall {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
| nil_forall : list_forall P nil nil
| cons_forall : forall a b la lb, P a b -> list_forall P la lb -> list_forall P (cons a la) (cons b lb).
*)

Definition Zlt_bool x y :=
match (x ?= y) with
| Lt => true
| _ => false
end.

(** semantics of exp **)
Inductive binop_apply : binop -> val -> val -> val -> Prop :=
| binop_and  : forall b1 b2, binop_apply b_and (boolean_val b1) (boolean_val b2) (boolean_val (andb b1 b2))
| binop_or   : forall b1 b2, binop_apply b_or  (boolean_val b1) (boolean_val b2) (boolean_val (orb  b1 b2))
| binop_plus  : forall z1 z2, binop_apply b_plus (num_val z1) (num_val z2) (num_val (z1 + z2))
| binop_minus : forall z1 z2, binop_apply b_minus (num_val z1) (num_val z2) (num_val (z1 - z2))
| binop_time  : forall z1 z2, binop_apply b_time (num_val z1) (num_val z2) (num_val (z1 * z2))
| binop_div   : forall z1 z2, binop_apply b_div (num_val z1) (num_val z2) (num_val (z1 / z2))
| binop_mod   : forall z1 z2, binop_apply b_mod (num_val z1) (num_val z2) (num_val (z1 mod z2))
| binop_eq   : forall z1 z2, binop_apply b_eq (num_val z1) (num_val z2) (boolean_val (Zeq_bool z1 z2))
| binop_lt   : forall z1 z2, binop_apply b_lt (num_val z1) (num_val z2) (boolean_val (Zlt_bool z1 z2))
| binop_append : forall s1 s2, binop_apply b_append (str_val s1) (str_val s2) (str_val (append s1 s2))
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


Notation "x #~> y" := (exp_val x y) (at level 25).



Axiom pname_decl : list declaration -> pname -> proc -> Prop.

(* no type checking. If a program is not well-typed, the semantics of it may not be defined. *)

Inductive verify (decls : list declaration) : proc -> Prop -> Prop -> Prop :=
| Vseq    : forall p1 p2 P1 P P2, verify decls p1 P1 P -> verify decls p2 P P2 -> verify decls (Pseq p1 p2) P1 P2
| Vwhile  : forall e p P, verify decls p (P /\ exp_val e (boolean_val true)) P -> verify decls (Pwhile e p) P (P /\ exp_val e (boolean_val false))
(* | Pmatch  : exp -> list proc -> proc *)
| Vassign : forall v e (P : exp -> Prop), verify decls (Passign v e) (P e) (P (var v))
| Vcall   : forall pn p P1 P2, pname_decl decls pn p -> verify decls p P1 P2 -> verify decls (Pcall pn) P1 P2
| Vweaken : forall p (P1 P2 P : Prop), verify decls p P P2 -> (P1 -> P) -> verify decls p P1 P2
.


Notation "D ||- {- P -} p {- Q -}" := (verify D p P Q) (at level 26).



Goal nil ||- {- V @ "b" #~> 0 -} "a":== V @ "b" +' 1 {- V @ "a" #~> 1 -}.
apply Vweaken with (P := V @ "b" +' 1 #~> 1).
apply Vassign with (P := fun v => v #~> 1).
intro.
inversion H; subst.
apply val_binop with 0 1.
 auto.
 constructor.
 constructor.
Qed.

(* lazy verification system (unsound if you do not care about assignment) *)



