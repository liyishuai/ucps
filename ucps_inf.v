Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export FTop.ucps_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme e_ind' := Induction for e Sort Prop.

Definition e_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  e_ind' H1 H2 H3 H4 H5 H6.

Scheme e_rec' := Induction for e Sort Set.

Definition e_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  e_rec' H1 H2 H3 H4 H5 H6.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_e_wrt_e_rec (n1 : nat) (x1 : x) (e1 : e) {struct e1} : e :=
  match e1 with
    | e_var_f x2 => if (x1 == x2) then (e_var_b n1) else (e_var_f x2)
    | e_var_b n2 => if (lt_ge_dec n2 n1) then (e_var_b n2) else (e_var_b (S n2))
    | e_lam e2 => e_lam (close_e_wrt_e_rec (S n1) x1 e2)
    | e_app e2 e3 => e_app (close_e_wrt_e_rec n1 x1 e2) (close_e_wrt_e_rec n1 x1 e3)
    | e_halt e2 => e_halt (close_e_wrt_e_rec n1 x1 e2)
  end.

Definition close_e_wrt_e x1 e1 := close_e_wrt_e_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_e (e1 : e) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lam e2 => 1 + (size_e e2)
    | e_app e2 e3 => 1 + (size_e e2) + (size_e e3)
    | e_halt e2 => 1 + (size_e e2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_e_wrt_e : nat -> e -> Prop :=
  | degree_wrt_e_e_var_f : forall n1 x1,
    degree_e_wrt_e n1 (e_var_f x1)
  | degree_wrt_e_e_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_e_wrt_e n1 (e_var_b n2)
  | degree_wrt_e_e_lam : forall n1 e1,
    degree_e_wrt_e (S n1) e1 ->
    degree_e_wrt_e n1 (e_lam e1)
  | degree_wrt_e_e_app : forall n1 e1 e2,
    degree_e_wrt_e n1 e1 ->
    degree_e_wrt_e n1 e2 ->
    degree_e_wrt_e n1 (e_app e1 e2)
  | degree_wrt_e_e_halt : forall n1 e1,
    degree_e_wrt_e n1 e1 ->
    degree_e_wrt_e n1 (e_halt e1).

Scheme degree_e_wrt_e_ind' := Induction for degree_e_wrt_e Sort Prop.

Definition degree_e_wrt_e_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  degree_e_wrt_e_ind' H1 H2 H3 H4 H5 H6.

Hint Constructors degree_e_wrt_e : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_e : e -> Set :=
  | lc_set_e_var_f : forall x1,
    lc_set_e (e_var_f x1)
  | lc_set_e_lam : forall e1,
    (forall x1 : x, lc_set_e (open_e_wrt_e e1 (e_var_f x1))) ->
    lc_set_e (e_lam e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_e e1 ->
    lc_set_e e2 ->
    lc_set_e (e_app e1 e2)
  | lc_set_e_halt : forall e1,
    lc_set_e e1 ->
    lc_set_e (e_halt e1).

Scheme lc_e_ind' := Induction for lc_e Sort Prop.

Definition lc_e_mutind :=
  fun H1 H2 H3 H4 H5 =>
  lc_e_ind' H1 H2 H3 H4 H5.

Scheme lc_set_e_ind' := Induction for lc_set_e Sort Prop.

Definition lc_set_e_mutind :=
  fun H1 H2 H3 H4 H5 =>
  lc_set_e_ind' H1 H2 H3 H4 H5.

Scheme lc_set_e_rec' := Induction for lc_set_e Sort Set.

Definition lc_set_e_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  lc_set_e_rec' H1 H2 H3 H4 H5.

Hint Constructors lc_e : core lngen.

Hint Constructors lc_set_e : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_e_wrt_e e1 := forall x1, lc_e (open_e_wrt_e e1 (e_var_f x1)).

Hint Unfold body_e_wrt_e.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_e_min_mutual :
(forall e1, 1 <= size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_e_min :
forall e1, 1 <= size_e e1.
Proof.
pose proof size_e_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_e_min : lngen.

(* begin hide *)

Lemma size_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  size_e (close_e_wrt_e_rec n1 x1 e1) = size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  size_e (close_e_wrt_e_rec n1 x1 e1) = size_e e1.
Proof.
pose proof size_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_e_close_e_wrt_e_rec : lngen.
Hint Rewrite size_e_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_e_close_e_wrt_e :
forall e1 x1,
  size_e (close_e_wrt_e x1 e1) = size_e e1.
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

Hint Resolve size_e_close_e_wrt_e : lngen.
Hint Rewrite size_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_mutual :
(forall e1 e2 n1,
  size_e e1 <= size_e (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec :
forall e1 e2 n1,
  size_e e1 <= size_e (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof size_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma size_e_open_e_wrt_e :
forall e1 e2,
  size_e e1 <= size_e (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve size_e_open_e_wrt_e : lngen.

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_var_mutual :
(forall e1 x1 n1,
  size_e (open_e_wrt_e_rec n1 (e_var_f x1) e1) = size_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_e_open_e_wrt_e_rec_var :
forall e1 x1 n1,
  size_e (open_e_wrt_e_rec n1 (e_var_f x1) e1) = size_e e1.
Proof.
pose proof size_e_open_e_wrt_e_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_e_open_e_wrt_e_rec_var : lngen.
Hint Rewrite size_e_open_e_wrt_e_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_e_open_e_wrt_e_var :
forall e1 x1,
  size_e (open_e_wrt_e e1 (e_var_f x1)) = size_e e1.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve size_e_open_e_wrt_e_var : lngen.
Hint Rewrite size_e_open_e_wrt_e_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_e_wrt_e_S_mutual :
(forall n1 e1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) e1).
Proof.
apply_mutual_ind degree_e_wrt_e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_e_wrt_e_S :
forall n1 e1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) e1.
Proof.
pose proof degree_e_wrt_e_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_e_wrt_e_S : lngen.

Lemma degree_e_wrt_e_O :
forall n1 e1,
  degree_e_wrt_e O e1 ->
  degree_e_wrt_e n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_e_wrt_e_O : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1).
Proof.
pose proof degree_e_wrt_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_e_wrt_e_close_e_wrt_e_rec : lngen.

(* end hide *)

Lemma degree_e_wrt_e_close_e_wrt_e :
forall e1 x1,
  degree_e_wrt_e 0 e1 ->
  degree_e_wrt_e 1 (close_e_wrt_e x1 e1).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

Hint Resolve degree_e_wrt_e_close_e_wrt_e : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_inv_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1) ->
  degree_e_wrt_e n1 e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_rec_inv :
forall e1 x1 n1,
  degree_e_wrt_e (S n1) (close_e_wrt_e_rec n1 x1 e1) ->
  degree_e_wrt_e n1 e1.
Proof.
pose proof degree_e_wrt_e_close_e_wrt_e_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_e_wrt_e_close_e_wrt_e_rec_inv : lngen.

(* end hide *)

Lemma degree_e_wrt_e_close_e_wrt_e_inv :
forall e1 x1,
  degree_e_wrt_e 1 (close_e_wrt_e x1 e1) ->
  degree_e_wrt_e 0 e1.
Proof.
unfold close_e_wrt_e; eauto with lngen.
Qed.

Hint Immediate degree_e_wrt_e_close_e_wrt_e_inv : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_mutual :
(forall e1 e2 n1,
  degree_e_wrt_e (S n1) e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec :
forall e1 e2 n1,
  degree_e_wrt_e (S n1) e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof degree_e_wrt_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_e_wrt_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma degree_e_wrt_e_open_e_wrt_e :
forall e1 e2,
  degree_e_wrt_e 1 e1 ->
  degree_e_wrt_e 0 e2 ->
  degree_e_wrt_e 0 (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve degree_e_wrt_e_open_e_wrt_e : lngen.

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_inv_mutual :
(forall e1 e2 n1,
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1) ->
  degree_e_wrt_e (S n1) e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_rec_inv :
forall e1 e2 n1,
  degree_e_wrt_e n1 (open_e_wrt_e_rec n1 e2 e1) ->
  degree_e_wrt_e (S n1) e1.
Proof.
pose proof degree_e_wrt_e_open_e_wrt_e_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_e_wrt_e_open_e_wrt_e_rec_inv : lngen.

(* end hide *)

Lemma degree_e_wrt_e_open_e_wrt_e_inv :
forall e1 e2,
  degree_e_wrt_e 0 (open_e_wrt_e e1 e2) ->
  degree_e_wrt_e 1 e1.
Proof.
unfold open_e_wrt_e; eauto with lngen.
Qed.

Hint Immediate degree_e_wrt_e_open_e_wrt_e_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_e_wrt_e_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_e_wrt_e_rec n1 x1 e1 = close_e_wrt_e_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind e_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_inj :
forall e1 e2 x1 n1,
  close_e_wrt_e_rec n1 x1 e1 = close_e_wrt_e_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_e_wrt_e_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_e_wrt_e_rec_inj : lngen.

(* end hide *)

Lemma close_e_wrt_e_inj :
forall e1 e2 x1,
  close_e_wrt_e x1 e1 = close_e_wrt_e x1 e2 ->
  e1 = e2.
Proof.
unfold close_e_wrt_e; eauto with lngen.
Qed.

Hint Immediate close_e_wrt_e_inj : lngen.

(* begin hide *)

Lemma close_e_wrt_e_rec_open_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_e e1 ->
  close_e_wrt_e_rec n1 x1 (open_e_wrt_e_rec n1 (e_var_f x1) e1) = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_open_e_wrt_e_rec :
forall e1 x1 n1,
  x1 `notin` fv_e e1 ->
  close_e_wrt_e_rec n1 x1 (open_e_wrt_e_rec n1 (e_var_f x1) e1) = e1.
Proof.
pose proof close_e_wrt_e_rec_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_e_wrt_e_rec_open_e_wrt_e_rec : lngen.
Hint Rewrite close_e_wrt_e_rec_open_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_e_wrt_e_open_e_wrt_e :
forall e1 x1,
  x1 `notin` fv_e e1 ->
  close_e_wrt_e x1 (open_e_wrt_e e1 (e_var_f x1)) = e1.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve close_e_wrt_e_open_e_wrt_e : lngen.
Hint Rewrite close_e_wrt_e_open_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_e_wrt_e_rec_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  open_e_wrt_e_rec n1 (e_var_f x1) (close_e_wrt_e_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_close_e_wrt_e_rec :
forall e1 x1 n1,
  open_e_wrt_e_rec n1 (e_var_f x1) (close_e_wrt_e_rec n1 x1 e1) = e1.
Proof.
pose proof open_e_wrt_e_rec_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_e_wrt_e_rec_close_e_wrt_e_rec : lngen.
Hint Rewrite open_e_wrt_e_rec_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_e_wrt_e_close_e_wrt_e :
forall e1 x1,
  open_e_wrt_e (close_e_wrt_e x1 e1) (e_var_f x1) = e1.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve open_e_wrt_e_close_e_wrt_e : lngen.
Hint Rewrite open_e_wrt_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_e_wrt_e_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_e e2 ->
  x1 `notin` fv_e e1 ->
  open_e_wrt_e_rec n1 (e_var_f x1) e2 = open_e_wrt_e_rec n1 (e_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind e_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_e e2 ->
  x1 `notin` fv_e e1 ->
  open_e_wrt_e_rec n1 (e_var_f x1) e2 = open_e_wrt_e_rec n1 (e_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_e_wrt_e_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_e_wrt_e_rec_inj : lngen.

(* end hide *)

Lemma open_e_wrt_e_inj :
forall e2 e1 x1,
  x1 `notin` fv_e e2 ->
  x1 `notin` fv_e e1 ->
  open_e_wrt_e e2 (e_var_f x1) = open_e_wrt_e e1 (e_var_f x1) ->
  e2 = e1.
Proof.
unfold open_e_wrt_e; eauto with lngen.
Qed.

Hint Immediate open_e_wrt_e_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_e_wrt_e_of_lc_e_mutual :
(forall e1,
  lc_e e1 ->
  degree_e_wrt_e 0 e1).
Proof.
apply_mutual_ind lc_e_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_e_wrt_e_of_lc_e :
forall e1,
  lc_e e1 ->
  degree_e_wrt_e 0 e1.
Proof.
pose proof degree_e_wrt_e_of_lc_e_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_e_wrt_e_of_lc_e : lngen.

(* begin hide *)

Lemma lc_e_of_degree_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  degree_e_wrt_e 0 e1 ->
  lc_e e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind e_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_e_of_degree :
forall e1,
  degree_e_wrt_e 0 e1 ->
  lc_e e1.
Proof.
intros e1; intros;
pose proof (lc_e_of_degree_size_mutual (size_e e1));
intuition eauto.
Qed.

Hint Resolve lc_e_of_degree : lngen.

Ltac e_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_e_wrt_e_of_lc_e in J1; clear H
          end).

Lemma lc_e_lam_exists :
forall x1 e1,
  lc_e (open_e_wrt_e e1 (e_var_f x1)) ->
  lc_e (e_lam e1).
Proof.
intros; e_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_e (e_lam _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_lam_exists x1).

Lemma lc_body_e_wrt_e :
forall e1 e2,
  body_e_wrt_e e1 ->
  lc_e e2 ->
  lc_e (open_e_wrt_e e1 e2).
Proof.
unfold body_e_wrt_e;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
e_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_e_wrt_e : lngen.

Lemma lc_body_e_lam_1 :
forall e1,
  lc_e (e_lam e1) ->
  body_e_wrt_e e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_lam_1 : lngen.

(* begin hide *)

Lemma lc_e_unique_mutual :
(forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_e_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_e_unique :
forall e1 (proof2 proof3 : lc_e e1), proof2 = proof3.
Proof.
pose proof lc_e_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_e_unique : lngen.

(* begin hide *)

Lemma lc_e_of_lc_set_e_mutual :
(forall e1, lc_set_e e1 -> lc_e e1).
Proof.
apply_mutual_ind lc_set_e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_e_of_lc_set_e :
forall e1, lc_set_e e1 -> lc_e e1.
Proof.
pose proof lc_e_of_lc_set_e_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_e_of_lc_set_e : lngen.

(* begin hide *)

Lemma lc_set_e_of_lc_e_size_mutual :
forall i1,
(forall e1,
  size_e e1 = i1 ->
  lc_e e1 ->
  lc_set_e e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind e_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_e_of_lc_e];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_e_of_lc_e :
forall e1,
  lc_e e1 ->
  lc_set_e e1.
Proof.
intros e1; intros;
pose proof (lc_set_e_of_lc_e_size_mutual (size_e e1));
intuition eauto.
Qed.

Hint Resolve lc_set_e_of_lc_e : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_e_wrt_e_rec_degree_e_wrt_e_mutual :
(forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  x1 `notin` fv_e e1 ->
  close_e_wrt_e_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_e_wrt_e_rec_degree_e_wrt_e :
forall e1 x1 n1,
  degree_e_wrt_e n1 e1 ->
  x1 `notin` fv_e e1 ->
  close_e_wrt_e_rec n1 x1 e1 = e1.
Proof.
pose proof close_e_wrt_e_rec_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

Hint Resolve close_e_wrt_e_rec_degree_e_wrt_e : lngen.
Hint Rewrite close_e_wrt_e_rec_degree_e_wrt_e using solve [auto] : lngen.

(* end hide *)

Lemma close_e_wrt_e_lc_e :
forall e1 x1,
  lc_e e1 ->
  x1 `notin` fv_e e1 ->
  close_e_wrt_e x1 e1 = e1.
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

Hint Resolve close_e_wrt_e_lc_e : lngen.
Hint Rewrite close_e_wrt_e_lc_e using solve [auto] : lngen.

(* begin hide *)

Lemma open_e_wrt_e_rec_degree_e_wrt_e_mutual :
(forall e2 e1 n1,
  degree_e_wrt_e n1 e2 ->
  open_e_wrt_e_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_e_wrt_e_rec_degree_e_wrt_e :
forall e2 e1 n1,
  degree_e_wrt_e n1 e2 ->
  open_e_wrt_e_rec n1 e1 e2 = e2.
Proof.
pose proof open_e_wrt_e_rec_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

Hint Resolve open_e_wrt_e_rec_degree_e_wrt_e : lngen.
Hint Rewrite open_e_wrt_e_rec_degree_e_wrt_e using solve [auto] : lngen.

(* end hide *)

Lemma open_e_wrt_e_lc_e :
forall e2 e1,
  lc_e e2 ->
  open_e_wrt_e e2 e1 = e2.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve open_e_wrt_e_lc_e : lngen.
Hint Rewrite open_e_wrt_e_lc_e using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_e_close_e_wrt_e_rec_mutual :
(forall e1 x1 n1,
  fv_e (close_e_wrt_e_rec n1 x1 e1) [=] remove x1 (fv_e e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_e_close_e_wrt_e_rec :
forall e1 x1 n1,
  fv_e (close_e_wrt_e_rec n1 x1 e1) [=] remove x1 (fv_e e1).
Proof.
pose proof fv_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_close_e_wrt_e_rec : lngen.
Hint Rewrite fv_e_close_e_wrt_e_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_e_close_e_wrt_e :
forall e1 x1,
  fv_e (close_e_wrt_e x1 e1) [=] remove x1 (fv_e e1).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

Hint Resolve fv_e_close_e_wrt_e : lngen.
Hint Rewrite fv_e_close_e_wrt_e using solve [auto] : lngen.

(* begin hide *)

Lemma fv_e_open_e_wrt_e_rec_lower_mutual :
(forall e1 e2 n1,
  fv_e e1 [<=] fv_e (open_e_wrt_e_rec n1 e2 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_e_open_e_wrt_e_rec_lower :
forall e1 e2 n1,
  fv_e e1 [<=] fv_e (open_e_wrt_e_rec n1 e2 e1).
Proof.
pose proof fv_e_open_e_wrt_e_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_open_e_wrt_e_rec_lower : lngen.

(* end hide *)

Lemma fv_e_open_e_wrt_e_lower :
forall e1 e2,
  fv_e e1 [<=] fv_e (open_e_wrt_e e1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve fv_e_open_e_wrt_e_lower : lngen.

(* begin hide *)

Lemma fv_e_open_e_wrt_e_rec_upper_mutual :
(forall e1 e2 n1,
  fv_e (open_e_wrt_e_rec n1 e2 e1) [<=] fv_e e2 `union` fv_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_e_open_e_wrt_e_rec_upper :
forall e1 e2 n1,
  fv_e (open_e_wrt_e_rec n1 e2 e1) [<=] fv_e e2 `union` fv_e e1.
Proof.
pose proof fv_e_open_e_wrt_e_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_open_e_wrt_e_rec_upper : lngen.

(* end hide *)

Lemma fv_e_open_e_wrt_e_upper :
forall e1 e2,
  fv_e (open_e_wrt_e e1 e2) [<=] fv_e e2 `union` fv_e e1.
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve fv_e_open_e_wrt_e_upper : lngen.

(* begin hide *)

Lemma fv_e_subst_e_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_e e1 ->
  fv_e (subst_e e2 x1 e1) [=] fv_e e1).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_e_subst_e_fresh :
forall e1 e2 x1,
  x1 `notin` fv_e e1 ->
  fv_e (subst_e e2 x1 e1) [=] fv_e e1.
Proof.
pose proof fv_e_subst_e_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_subst_e_fresh : lngen.
Hint Rewrite fv_e_subst_e_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_e_subst_e_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_e e1) [<=] fv_e (subst_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_e_subst_e_lower :
forall e1 e2 x1,
  remove x1 (fv_e e1) [<=] fv_e (subst_e e2 x1 e1).
Proof.
pose proof fv_e_subst_e_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_subst_e_lower : lngen.

(* begin hide *)

Lemma fv_e_subst_e_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_e e1 ->
  x2 `notin` fv_e e2 ->
  x2 `notin` fv_e (subst_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_e_subst_e_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_e e1 ->
  x2 `notin` fv_e e2 ->
  x2 `notin` fv_e (subst_e e2 x1 e1).
Proof.
pose proof fv_e_subst_e_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_subst_e_notin : lngen.

(* begin hide *)

Lemma fv_e_subst_e_upper_mutual :
(forall e1 e2 x1,
  fv_e (subst_e e2 x1 e1) [<=] fv_e e2 `union` remove x1 (fv_e e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_e_subst_e_upper :
forall e1 e2 x1,
  fv_e (subst_e e2 x1 e1) [<=] fv_e e2 `union` remove x1 (fv_e e1).
Proof.
pose proof fv_e_subst_e_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_e_subst_e_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_e_close_e_wrt_e_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_e_wrt_e n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_e e1 ->
  subst_e e1 x1 (close_e_wrt_e_rec n1 x2 e2) = close_e_wrt_e_rec n1 x2 (subst_e e1 x1 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_close_e_wrt_e_rec :
forall e2 e1 x1 x2 n1,
  degree_e_wrt_e n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_e e1 ->
  subst_e e1 x1 (close_e_wrt_e_rec n1 x2 e2) = close_e_wrt_e_rec n1 x2 (subst_e e1 x1 e2).
Proof.
pose proof subst_e_close_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_close_e_wrt_e_rec : lngen.

Lemma subst_e_close_e_wrt_e :
forall e2 e1 x1 x2,
  lc_e e1 ->  x1 <> x2 ->
  x2 `notin` fv_e e1 ->
  subst_e e1 x1 (close_e_wrt_e x2 e2) = close_e_wrt_e x2 (subst_e e1 x1 e2).
Proof.
unfold close_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_close_e_wrt_e : lngen.

(* begin hide *)

Lemma subst_e_degree_e_wrt_e_mutual :
(forall e1 e2 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (subst_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_degree_e_wrt_e :
forall e1 e2 x1 n1,
  degree_e_wrt_e n1 e1 ->
  degree_e_wrt_e n1 e2 ->
  degree_e_wrt_e n1 (subst_e e2 x1 e1).
Proof.
pose proof subst_e_degree_e_wrt_e_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_degree_e_wrt_e : lngen.

(* begin hide *)

Lemma subst_e_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_e e2 ->
  subst_e e1 x1 e2 = e2).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_e e2 ->
  subst_e e1 x1 e2 = e2.
Proof.
pose proof subst_e_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_fresh_eq : lngen.
Hint Rewrite subst_e_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_e_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_e e1 ->
  x1 `notin` fv_e (subst_e e1 x1 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_e e1 ->
  x1 `notin` fv_e (subst_e e1 x1 e2).
Proof.
pose proof subst_e_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_fresh_same : lngen.

(* begin hide *)

Lemma subst_e_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_e e2 ->
  x1 `notin` fv_e e1 ->
  x1 `notin` fv_e (subst_e e1 x2 e2)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_e e2 ->
  x1 `notin` fv_e e1 ->
  x1 `notin` fv_e (subst_e e1 x2 e2).
Proof.
pose proof subst_e_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_fresh : lngen.

Lemma subst_e_lc_e :
forall e1 e2 x1,
  lc_e e1 ->
  lc_e e2 ->
  lc_e (subst_e e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_e_lc_e : lngen.

(* begin hide *)

Lemma subst_e_open_e_wrt_e_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_e e1 ->
  subst_e e1 x1 (open_e_wrt_e_rec n1 e2 e3) = open_e_wrt_e_rec n1 (subst_e e1 x1 e2) (subst_e e1 x1 e3)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_e_open_e_wrt_e_rec :
forall e3 e1 e2 x1 n1,
  lc_e e1 ->
  subst_e e1 x1 (open_e_wrt_e_rec n1 e2 e3) = open_e_wrt_e_rec n1 (subst_e e1 x1 e2) (subst_e e1 x1 e3).
Proof.
pose proof subst_e_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma subst_e_open_e_wrt_e :
forall e3 e1 e2 x1,
  lc_e e1 ->
  subst_e e1 x1 (open_e_wrt_e e3 e2) = open_e_wrt_e (subst_e e1 x1 e3) (subst_e e1 x1 e2).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_open_e_wrt_e : lngen.

Lemma subst_e_open_e_wrt_e_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_e e1 ->
  open_e_wrt_e (subst_e e1 x1 e2) (e_var_f x2) = subst_e e1 x1 (open_e_wrt_e e2 (e_var_f x2)).
Proof.
intros; rewrite subst_e_open_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_open_e_wrt_e_var : lngen.

(* begin hide *)

Lemma subst_e_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_e e2 x1 e1 = open_e_wrt_e_rec n1 e2 (close_e_wrt_e_rec n1 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_e_spec_rec :
forall e1 e2 x1 n1,
  subst_e e2 x1 e1 = open_e_wrt_e_rec n1 e2 (close_e_wrt_e_rec n1 x1 e1).
Proof.
pose proof subst_e_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_spec_rec : lngen.

(* end hide *)

Lemma subst_e_spec :
forall e1 e2 x1,
  subst_e e2 x1 e1 = open_e_wrt_e (close_e_wrt_e x1 e1) e2.
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_spec : lngen.

(* begin hide *)

Lemma subst_e_subst_e_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_e e2 ->
  x2 <> x1 ->
  subst_e e2 x1 (subst_e e3 x2 e1) = subst_e (subst_e e2 x1 e3) x2 (subst_e e2 x1 e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_subst_e :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_e e2 ->
  x2 <> x1 ->
  subst_e e2 x1 (subst_e e3 x2 e1) = subst_e (subst_e e2 x1 e3) x2 (subst_e e2 x1 e1).
Proof.
pose proof subst_e_subst_e_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_subst_e : lngen.

(* begin hide *)

Lemma subst_e_close_e_wrt_e_rec_open_e_wrt_e_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_e e2 ->
  x2 `notin` fv_e e1 ->
  x2 <> x1 ->
  degree_e_wrt_e n1 e1 ->
  subst_e e1 x1 e2 = close_e_wrt_e_rec n1 x2 (subst_e e1 x1 (open_e_wrt_e_rec n1 (e_var_f x2) e2))).
Proof.
apply_mutual_ind e_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_e_close_e_wrt_e_rec_open_e_wrt_e_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_e e2 ->
  x2 `notin` fv_e e1 ->
  x2 <> x1 ->
  degree_e_wrt_e n1 e1 ->
  subst_e e1 x1 e2 = close_e_wrt_e_rec n1 x2 (subst_e e1 x1 (open_e_wrt_e_rec n1 (e_var_f x2) e2)).
Proof.
pose proof subst_e_close_e_wrt_e_rec_open_e_wrt_e_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_close_e_wrt_e_rec_open_e_wrt_e_rec : lngen.

(* end hide *)

Lemma subst_e_close_e_wrt_e_open_e_wrt_e :
forall e2 e1 x1 x2,
  x2 `notin` fv_e e2 ->
  x2 `notin` fv_e e1 ->
  x2 <> x1 ->
  lc_e e1 ->
  subst_e e1 x1 e2 = close_e_wrt_e x2 (subst_e e1 x1 (open_e_wrt_e e2 (e_var_f x2))).
Proof.
unfold close_e_wrt_e; unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_close_e_wrt_e_open_e_wrt_e : lngen.

Lemma subst_e_e_lam :
forall x2 e2 e1 x1,
  lc_e e1 ->
  x2 `notin` fv_e e1 `union` fv_e e2 `union` singleton x1 ->
  subst_e e1 x1 (e_lam e2) = e_lam (close_e_wrt_e x2 (subst_e e1 x1 (open_e_wrt_e e2 (e_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_e_e_lam : lngen.

(* begin hide *)

Lemma subst_e_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_e e1 ->
  open_e_wrt_e_rec n1 e2 e1 = subst_e e2 x1 (open_e_wrt_e_rec n1 (e_var_f x1) e1)).
Proof.
apply_mutual_ind e_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_e_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_e e1 ->
  open_e_wrt_e_rec n1 e2 e1 = subst_e e2 x1 (open_e_wrt_e_rec n1 (e_var_f x1) e1).
Proof.
pose proof subst_e_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_e_intro_rec : lngen.
Hint Rewrite subst_e_intro_rec using solve [auto] : lngen.

Lemma subst_e_intro :
forall x1 e1 e2,
  x1 `notin` fv_e e1 ->
  open_e_wrt_e e1 e2 = subst_e e2 x1 (open_e_wrt_e e1 (e_var_f x1)).
Proof.
unfold open_e_wrt_e; default_simp.
Qed.

Hint Resolve subst_e_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
