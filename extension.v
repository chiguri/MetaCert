Require Import List.
Require Import ZArith.
Require Import String.
Import ListNotations.


Require Import lang.


Section meta_syntax.


(* for expression *)
Definition exp_var_constr := constr_def (constr_name "var") [type_name "string"].
Definition exp_num_constr := constr_def (constr_name "num") [type_name "num"].
Definition exp_plus_constr := constr_def (constr_name "plus") [type_name "num"; type_name "num"].
(*
Inductive exp : Set :=
| var : vname -> exp
| con : cname -> exp
| boolean : bool -> exp
| num : Z -> exp
| str : string -> exp
| binary : binop -> exp -> exp -> exp
| application : exp -> exp -> exp.
*)

Definition syntax_exp_decl := type_decl (type_name "exp") [exp_var_constr; exp_num_constr; exp_plus_constr].


Inductive exp_meta_base : val -> exp -> Prop :=
| exp_mb_var : forall v, exp_meta_base (con_val (con_args (con_name (constr_name "var")) (str_val v))) (var (var_name v))
| exp_mb_num : forall z, exp_meta_base (con_val (con_args (con_name (constr_name "num")) (num_val z))) (num z)
| exp_mb_plus : forall z1 z2,
   exp_meta_base
    (con_val
     (con_args
      (con_args
       (con_name (constr_name "plus"))
       (con_val
        (con_args (con_name (constr_name "num"))
                  (num_val z1))))
      (con_val
       (con_args
        (con_name (constr_name "num"))
                  (num_val z2)))))
     (binary b_plus (num z1) (num z2))
.


(* for procedure *)
Definition proc_assign_constr := constr_def (constr_name "assign") [type_name "string"; type_name "exp"].
Definition proc_seq_constr := constr_def (constr_name "seq") [type_name "proc"; type_name "proc"].

(*
Inductive proc : Set :=
(*| Pblock  : list vname -> proc -> proc*)
| Pseq    : proc -> proc -> proc (* 左結合などを意識した方がいいか *)
| Pwhile  : exp -> proc -> proc
| Pmatch  : exp -> list proc -> proc
| Passign : vname -> exp -> proc
| Pcall   : pname -> proc (* 引数あったけどやめた。面倒くさい *)
.
*)

Definition syntax_proc_decl := type_decl (type_name "proc") [proc_assign_constr; proc_seq_constr].

Inductive proc_meta_base : val -> proc -> Prop :=
| proc_mb_assign : forall vn v e, exp_meta_base v e ->
    proc_meta_base (con_val (con_args (con_args (con_name (constr_name "assign")) (str_val vn)) v)) (Passign (var_name vn) e)
| proc_mb_seq : forall v1 v2 p1 p2,
   proc_meta_base v1 p1 -> proc_meta_base v2 p2 ->
    proc_meta_base (con_val (con_args (con_args (con_name (constr_name "seq")) v1) v2)) (Pseq p1 p2)
.







(*
Variable syntax_type_decl : declaration.


Definition meta_module := ("meta_syntax", [syntax_proc_decl; syntax_func_decl; syntax_type_decl]).
*)

(* a := 10 という文vを作るプログラム *)
Definition test_program := Passign (var_name "v") (application (application (con (constr_name "assign")) (str "a")) (application (con (constr_name "num")) (num 10%Z))).

(* 書いて気づいたけど、変数の環境をmetaとbaseで切り分けないと100%死ぬよこれ *)
Goal verify [] test_program True (forall v p, exp_val (var (var_name "v")) v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 10%Z))).
unfold test_program.
apply Vweaken with
 (P1 := forall (v : val) (p : proc), exp_val (application (application (con (constr_name "assign")) (str "a")) (application (con (constr_name "num")) (num 10))) v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 10%Z))).
apply Vassign with (P := fun e => forall (v : val) (p : proc), exp_val e v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 10%Z))).
intro.
intros.
inversion H0; clear H0; subst.
inversion H2; clear H2; subst.
inversion H4; clear H4; subst.
inversion H3; clear H3; subst.
inversion H6; clear H6; subst.
inversion H7; clear H7; subst.
inversion H2.
inversion H0; clear H0; subst.
inversion H4; clear H4; subst.
inversion H6; clear H6; subst.
inversion H0.
inversion H1; clear H1; subst.
inversion H4; clear H4; subst.
eapply Vweaken.
eapply Vassign with (P := fun v => exp_val v (num_val 10%Z)).
intro.
constructor.
Qed.



(* a := 10; a := a + 10 *)
Definition test_program2 :=
 Passign
  (var_name "v")
  (application
   (application
    (con
     (constr_name "assign")) (str "a")) (application (con (constr_name "num")) (num 10%Z))).




End meta_syntax.
