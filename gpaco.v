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
From Coinduction Require Import all. Import CoindNotations.

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
Notation "x ≃[ R ] y" := (`R x y) (at level 79).
Notation "x ≃ y" := (`_ x y) (at level 79). 
Notation "x [≃] y" := (b `_ x y) (at level 79).



(** elements of the final chain are reflexive *)
#[export] Instance Reflexive_b' {R} {HR: Reflexive R}: Reflexive (b' R).
Proof. now intros [s|n s]; constructor. Qed.
#[export] Instance Reflexive_t: forall {R: Chain b}, Reflexive `R.
Proof. apply Reflexive_chain. now cbn. Qed.

(** elements of the final chain are symmetric *)
#[export] Instance Symmetric_t: forall {R: Chain b}, Symmetric `R.
Proof.
  apply Symmetric_chain. 
  intros R HR. 
  assert (H: forall x y, b' `R y x -> b' `R x y)
    by (induction 1; constructor; auto).
  intros x y xy. now apply H.  
Qed.

Lemma unfold x: x ~ inj (obs x).
Proof. now step; cbn. Qed.

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
Proposition tau_l: forall {R: Chain b} x y, `R x y ->  `R (Tau x) y.
Proof.
  (* TODO: improve the need to specify the predicate *)
  apply (tower (P:=fun R: _ -> _ -> Prop => forall x y, R x y ->  R (Tau x) y)). 
  - intros P HP x y xy R PR. apply HP; auto. 
  - intros. now apply bTauL. 
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
