(** * Example: Generalized parameterized coinduction

We show how to use the companion to deal with the example motivating 
generalized parameterized coinduction in the following paper:

An equational theory for weak bisimulation via generalized parameterized coinduction. 
Yannick Zakowski, Paul He, Chung-Kil Hur, Steve Zdancewic, In Proc. CPP 2020
https://doi.org/10.1145/3372885.3373813
https://arxiv.org/abs/2001.02659

 *)

Set Implicit Arguments.
Set Primitive Projections.
From Coinduction Require Import coinduction rel tactics.

(** streams with internal actions *)
Variant streamF streamF :=
| TauF(s: streamF)
| VisF(n: nat)(s: streamF).
CoInductive stream := inj {obs: streamF stream}.
Notation stream' := (streamF stream).

Definition Tau s := {|obs := TauF s|}.
Definition Vis n s := {|obs := VisF n s|}.

(** two streams corresponding to s'0 and t'0 in Figure 1 *)
CoFixpoint x := Vis 0 (Vis 2 (Tau x)). 
CoFixpoint y := Vis 0 (Vis 2 y). 

Notation rel' := (stream' -> stream' -> Prop).
Notation rel := (stream -> stream -> Prop).

(** monotone function whose greatest fixpoint is desired notion of equivalence on streams:
    internal actions are ignored, as long as we eventually get a value
  *)
Inductive b' (R: rel): rel' :=
| bTau: forall s t, R s t -> b' R (TauF s) (TauF t)
| bTauL: forall s t, b' R (obs s) t -> b' R (TauF s) t
| bTauR: forall s t, b' R s (obs t) -> b' R s (TauF t)
| bVis: forall s t, R s t -> forall n, b' R (VisF n s) (VisF n t).

Program Definition b: mon rel := {| body R x y := b' R (obs x) (obs y) |}.
Next Obligation.
  cbv. intros R S H.
  induction 1; constructor; auto.
Qed.

Infix "~" := (gfp b) (at level 70). 
Notation t := (t b).
Notation T := (T b).
Notation bt := (bt b).
Notation bT := (bT b).
Notation "x ≃[ R ] y" := (t R x y) (at level 79).
Notation "x ≃ y" := (t _ x y) (at level 79). 
Notation "x [≃] y" := (bt _ x y) (at level 79).

(** converse is compatible *)
Lemma converse_t: converse <= t.
Proof.
  apply leq_t. cbv. intros S x y.
  cut (forall x y, b' S y x -> b' (converse S) x y). now auto.
  induction 1; constructor; auto.
Qed.
#[export] Instance Symmetric_t R: Symmetric (t R).
Proof. intros x y. apply (ft_t converse_t). Qed.

(** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
#[export] Instance Reflexive_b'eq {R} {HR: Reflexive R}: Reflexive (b' R).
Proof. now intros [s|n s]; constructor. Qed.
Lemma eq_t: const eq <= t.
Proof.
  apply leq_t. intro R. change (eq <= b eq). 
  intros p ? <-. cbv. reflexivity. 
Qed.
#[export] Instance Reflexive_t R: Reflexive (t R).
Proof. intro. now apply eq_t. Qed.

Lemma unfold x: x ~ inj (obs x).
Proof. now step. Qed.

(** the unsatisfactory proof (Figure 2) *)
Goal x ~ y.
  coinduction R H. cbn.
  constructor.
  (** not satisfactory to have to anticipate the next step *)
  accumulate H'.
  constructor.
  (** not satisfactory to use step here (and repeat the above argument) *)
  step.                         
  constructor. cbn.
  constructor.
  assumption.
Qed.

Goal x ~ y.
  coinduction R H. cbn.
  constructor.
  step.
  constructor.
  (** here, we would like to just remove the tau and conclude *)
Abort.

(** we solve the issue by using an up-to technique: "up-to tau steps on the left"  *)
Variant tauL' (R: rel): _ -> _ -> Prop :=
| tauL_: forall s t, R s t -> tauL' R (TauF s) t.

Program Definition tauL: mon rel := {| body R x y := tauL' R (obs x) y |}.
Next Obligation.
  cbv. intros R S H. destruct 1; constructor; auto.
Qed.

(** this technique is safe (below the companion)  *)
Lemma tauL_t: tauL <= t.
Proof.
  apply Coinduction. intros R x' y.
  cut (forall x, tauL' (b R) x y -> b' (T tauL R) x (obs y)).
   intro H. exact (H (obs x')).
  clear x'. intro x. 
  destruct 1. constructor.
  revert H. apply b. apply id_T. 
Qed.

(** so that we get the following deduction rule about the companion: *)
Corollary tau_l R x y: t R x y ->  t R (Tau x) y.
Proof.
  intro H. apply (ft_t tauL_t). constructor. assumption.
Qed.

(** and we get a satisfactory proof *)
Goal x ~ y.
  coinduction R H. cbn.
  constructor.
  step.
  constructor.
  apply tau_l.
  assumption.
Qed.
