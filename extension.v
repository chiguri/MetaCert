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
| exp_mb_plus : forall e1 e2 v1 v2,
   exp_meta_base e1 v1 -> exp_meta_base e2 v2 ->
   exp_meta_base
    (con_val
     (con_args
      (con_args
       (con_name (constr_name "plus"))
       e1)
      e2))
    (binary b_plus v1 v2)
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

Definition test_program_data :=
 application
  (application
   (con
    (constr_name "assign"))
   (str "a"))
  (application
   (con
    (constr_name "num"))
   (num 10%Z)).

(* a := 10 という文vを作るプログラム *)
Definition test_program := Passign (var_name "v") test_program_data.

(* 書いて気づいたけど、変数の環境をmetaとbaseで切り分けないと100%死ぬよこれ *)
Goal verify [] test_program True (forall v p, exp_val (var (var_name "v")) v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 10%Z))).
unfold test_program.
apply Vweaken with
 (P1 := forall (v : val) (p : proc), exp_val test_program_data v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 10%Z))); unfold test_program_data.
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



(* v = "a := 10; a := a + 10" *)
Definition test_program2_data :=
 application
  (application
   (con
    (constr_name "seq"))
   (application
    (application
     (con
      (constr_name "assign"))
     (str "a"))
    (application
     (con (constr_name "num"))
     (num 10%Z))))
 (application
  (application
   (con
    (constr_name "assign")) (str "a"))
  (application
   (application
    (con (constr_name "plus"))
    (application
     (con (constr_name "var"))
     (str "a")))
   (application
    (con (constr_name "num"))
    (num 10%Z)))).

Definition test_program2 :=
 Passign (var_name "v") test_program2_data.




Goal verify [] test_program2 True (forall v p, exp_val (var (var_name "v")) v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 20%Z))).
unfold test_program2.
apply Vweaken with
 (P1 := forall (v : val) (p : proc), exp_val test_program2_data v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 20%Z))).
apply Vassign with (P := fun e => forall (v : val) (p : proc), exp_val e v -> proc_meta_base v p -> verify [] p True (exp_val (var (var_name "a")) (num_val 20%Z))).
intro H; clear H.
intros.
unfold test_program2_data in H.
(* evaluation of expression *)
inversion H; clear H; subst.
inversion H1; clear H1; subst.
inversion H3; clear H3; subst.
inversion H2; clear H2; subst.
inversion H5; clear H5; subst.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H2; clear H2; subst.
inversion H5; clear H5; subst.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H2; clear H2; subst.
inversion H5; clear H5; subst.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H5; clear H5; subst.
inversion H.
inversion H6; clear H6; subst.
inversion H7; clear H7; subst.
inversion H1.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H2; clear H2; subst.
inversion H5; clear H5; subst.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H5; clear H5; subst.
inversion H.
inversion H6; clear H6; subst.
inversion H.
inversion H8; clear H8; subst.
inversion H; clear H; subst.
inversion H3; clear H3; subst.
inversion H5; clear H5; subst.
inversion H.
(* meta-to-base *)
inversion H0; clear H0; subst.
inversion H2; clear H2; subst.
inversion H3; clear H3; subst.
inversion H4; clear H4; subst.
inversion H2; clear H2; subst.
inversion H1; clear H1; subst.
inversion H4; clear H4; subst.
(* generated program verification *)
apply Vweaken with (P1 := (exp_val (binary b_plus (num 10%Z) (num 10%Z)) (num_val 20%Z))).
eapply Vseq.
apply Vassign with (P := fun e => exp_val (binary b_plus e (num 10)) (num_val 20)).
apply Vassign with (P := fun e => exp_val e (num_val 20)). (* なんでapplyだけじゃうまく行かないのかよく分からない *)
intro H; clear H.
eapply val_binop.
apply val_num.
apply val_num.
constructor.
Qed.




End meta_syntax.
