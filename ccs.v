(** * Example: Milner's CCS 
    
    references point to the following paper 
    Coinduction All the Way Up. Damien Pous. In Proc. LICS, 2016.

 *)

(* TODO: merge common bits from Coinduction and RelationAlgebra (operations on relations) *)
(* TOTHINK: algebraic definition of generating functions? *)

From RelationAlgebra Require Import kat prop rel comparisons kat_tac rewriting.
From Coinduction Require Import lattice tower rel tactics.
From AAC_tactics Require Import AAC.
Set Implicit Arguments.

Module Type N.
 Parameter N: Set.           (* channels names *)
End N.

Module CCS(Export M: N).

 (** CCS labels (or prefixes, they are the same) *)
 Variant label := tau | out(a: N) | inp(a: N).
  
 (** CCS processes. Instead of using process constants, as in the paper, 
   we use a coinductive definition. In other words, we use Coq's corecursive 
   definitions to encode CCS recursion *)
 CoInductive S :=
 | nil
 | prf(l: label)(p: S)
 | pls(p q: S)
 | par(p q: S)
 | new(a: N)(p: S)
 | rep(p: S).

 Declare Scope ccs_scope.
 Bind Scope ccs_scope with S.
 Delimit Scope ccs_scope with ccs.
 Open Scope ccs_scope.
 
 Notation "0" := nil: ccs_scope.
 Infix "∥" := par (at level 40, left associativity): ccs_scope. 
 Infix "+" := pls (at level 50, left associativity): ccs_scope.
 Notation "! p" := (rep p): ccs_scope.

 (** when a name [a] does not appear in a label [l] *)
 Definition fresh a (l: label) :=
   match l with tau => True | out b | inp b => a<>b end.

 (** the (standard) LTS  *)
 Inductive trans: label -> S -> S -> Prop :=
 | t_prf: forall l p, trans l (prf l p) p
 | t_pls_l: forall p q l p', trans l p p' -> trans l (p+q) p'
 | t_pls_r: forall p q l q', trans l q q' -> trans l (p+q) q'
 | t_par_l: forall p l p' q, trans l p p' -> trans l (p ∥ q) (p' ∥ q)
 | t_par_r: forall p l p' q, trans l p p' -> trans l (q ∥ p) (q ∥ p')
 | t_par_lr: forall a p p' q q', trans (out a) p p' -> trans (inp a) q q' -> trans tau (p ∥ q) (p' ∥ q')
 | t_par_rl: forall a p p' q q', trans (inp a) p p' -> trans (out a) q q' -> trans tau (p ∥ q) (p' ∥ q')
 | t_new: forall a p l p', trans l p p' -> fresh a l -> trans l (new a p) (new a p')
 | t_rep: forall p l p', trans l (!p ∥ p) p' -> trans l (!p) p'
 .
 Global Hint Resolve t_prf t_par_l t_par_r t_par_lr t_par_rl t_new t_pls_l t_pls_r: ccs.
 
 Lemma t_rep': forall p l p', trans l p p' -> trans l (!p) (!p ∥ p').
 Proof. intros. apply t_rep; eauto with ccs. Qed.
 Global Hint Resolve t_rep': ccs.

 Lemma t_rep'': forall p a po pi, trans (out a) p po -> trans (inp a) p pi -> trans tau (!p) (!p ∥ po ∥ pi).
 Proof. intros. apply t_rep; eauto with ccs. Qed.
 Global Hint Resolve t_rep'': ccs.
 
 (** dumb utilities for corecursion *)
 Definition id_S(p: S): S :=
   match p with
   | nil => nil
   | prf l p => prf l p
   | new a' p => new a' p
   | par p q => par p q
   | pls p q => pls p q
   | rep p => rep p 
   end.
 Lemma Sd p: p = id_S p.
 Proof. now case p. Qed.

 Ltac inverse_trans :=
   match goal with
   | H: trans _ ?p _ |- _ =>
     tryif is_var p then fail else
       inversion H; subst; clear H; (* try congruence; *) inverse_trans
   | _ => idtac
   end.

 (** the function defining (strong) simulations and similarity *)
 Program Definition s: mon (S -> S -> Prop) :=
   {| body R p q :=
        forall l p', trans l p p' -> exists2 q', trans l q q' & R p' q' |}.
 Next Obligation. cbv. firstorder. Qed.
 
 (** the symmetrised version, defining (strong) bisimulations and bisimilarity *)
 Notation b := (cap s (comp converse (comp s converse))).

 Notation "p ~ q" := (gfp b p%ccs q%ccs) (at level 70).
 (** notations  for easing readability in proofs by enhanced coinduction *)
 Infix "[~]" := (`_) (at level 79). 
 Infix "{~}" := (b `_) (at level 79).

 
 (** Some valid laws  *)
 Lemma parC: forall p q, p ∥ q ~ q ∥ p.
 Proof.
   (** the tactic [coinduction R H] makes it possible to start a proof by enhanced coinduction.
       the goal is transformed into a bisimulation candidate [R], and we get to analyse the transitions, information about pairs in [R] is stored in [H]. *)
   coinduction R H.
   (** the tactic [symmetric] makes it possible to play the bisimulation only from left-to-right here, since the candidate is symmetric*)
   symmetric.
   (** we finally analyse the transitions *)
   intros p q l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 Lemma parA: forall p q r, p ∥ (q ∥ r) ~ (p ∥ q) ∥ r.
 Proof.
   coinduction R H.
   intros p q r; split; intros l p' pp'; cbn; inverse_trans; eauto with ccs.
 Qed.
 
 Lemma par0p: forall p, 0 ∥ p ~ p.
 Proof.
   coinduction R H.
   intros p; split; intros l p' pp'; cbn; inverse_trans; eauto with ccs.
 Qed.

 (** we prove more laws below, but first we need to establish the validity of up-to congruence, i.e., with the companion, that for all R, [t R] is a congruence w.r.t. CCS operators.
  *)
 
 (** * Equivalence closure *)
 
 (** elements of the final chain are equivalence relations *)
 #[export] Instance Equivalence_t {R: Chain b}: Equivalence `R.
 Proof.
   constructor; revert R.
   - apply Reflexive_symchain. intros R HR x l x' xx'. now exists x'. 
   - apply Symmetric_symchain. 
   - apply Transitive_symchain. intros R HR x y z xy yz l x' xx'.
     destruct (xy _ _ xx') as [y' yy' x'y']. 
     destruct (yz _ _ yy') as [z' zz' y'z'].     
     exists z'; trivial. now transitivity y'.
 Qed.

 (** * Context closure *)

 (** ** prefix *)
 #[export] Instance prf_chain {a}: forall {R: Chain b}, Proper (`R ==> `R) (prf a).
 Proof.
   apply (Proper_symchain 1).
   intros R HR p q Hpq l p' pp'.
   inverse_trans.
   eexists. eauto with ccs.
   now step. 
 Qed.

 (** ** name restriction *)
 #[export] Instance new_chain {a}: forall {R: Chain b}, Proper (`R ==> `R) (new a).
 Proof.
   apply (Proper_symchain 1).
   intros R HR p q Hpq l p' pp'.
   inverse_trans. destruct (proj1 Hpq _ _ H2) as [???].
   eexists. eauto with ccs. now apply HR. 
 Qed.

 (** ** choice *)
 #[export] Instance pls_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) pls.
 Proof.
   apply (Proper_symchain 2).
   intros R HR p q Hpq r s Hrs l p0 Hp0.
   inverse_trans.
   destruct (proj1 Hpq _ _ H3). eauto with ccs. 
   destruct (proj1 Hrs _ _ H3). eauto with ccs.
 Qed.
 
 (** ** parallel composition *)
 (** Lemma 8.1 *)
 #[export] Instance par_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) par.
 Proof.
   apply (Proper_symchain 2).
   intros R HR p q Hpq r s Hrs l p0 Hp0.
   inversion_clear Hp0.
    destruct (proj1 Hpq _ _ H). eexists. eauto with ccs. apply HR; auto. now step. 
    destruct (proj1 Hrs _ _ H). eexists. eauto with ccs. apply HR; auto. now step. 
    destruct (proj1 Hpq _ _ H).
    destruct (proj1 Hrs _ _ H0). eexists. eauto with ccs. now apply HR. 
    destruct (proj1 Hpq _ _ H).
    destruct (proj1 Hrs _ _ H0). eexists. eauto with ccs. now apply HR. 
 Qed.
 
 (** ** replication (the challenging operation) *)

 (** preliminary results *)
 Lemma unfold_rep p: !p ~ !p ∥ p.
 Proof.
   step. split; intros l p' pp'; cbn.
   inversion_clear pp'. eauto with ccs.
   eexists. constructor; eassumption. reflexivity.
 Qed.

 (** Proposition 8.2(i) *)
 Proposition rep_trans p l p0: trans l (rep p) p0 -> exists2 p1, trans l (p ∥ p) p1 & p0 ~ !p ∥ p1.
 Proof.
   remember (!p)%ccs as rp. intro H. revert rp l p0 H p Heqrp. fix rep_trans 4.
   intros rp l p0 H p E. destruct H; try discriminate.
   remember (!p0 ∥ p0)%ccs as rpp. destruct H; try discriminate. 
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto with ccs. 
    rewrite H1. now rewrite (parC (rep _)), <-parA, <-unfold_rep.
    
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto with ccs.
    now rewrite parA, <-unfold_rep.
    
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto with ccs|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, (parC q'), parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, (parC q'), parA.

    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto with ccs|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, parA.
 Qed.

 (** Proposition 8.2(ii) *)
 Proposition rep_trans' p l p1: trans l (p ∥ p) p1 -> exists2 p0, trans l (!p) p0 & p0 ~ !p ∥ p1.
 Proof.
   assert (E: !p ∥ (p∥p) ~ !p).
    now rewrite parA, <-2unfold_rep.
   intros H.
   assert (H': trans l (!p ∥ (p∥p)) (!p∥p1)) by auto with ccs.
   destruct (proj1 (gfp_pfp b _ _ E) _ _ H'). eexists. eauto with ccs. symmetry. assumption.
 Qed.

 (** Lemma 8.4 
     (note that we do not need Lemma 8.3 as in the paper: we
     use instead the more general fact that we can reason up to
     equivalence [Equivalence_t] and that [~ <= t R]) *)
 #[export] Instance rep_chain: forall {R: Chain b}, Proper (`R ==> `R) rep.
 Proof.
   apply (Proper_symchain 1).
   intros R HR p q Hpq l p0 Hp0.
   apply rep_trans in Hp0 as [p1 ppp1 p0p1]. 
   assert (H: b `R (par p p) (par q q)) by now apply par_chain.
   destruct (proj1 H _ _ ppp1) as [q1 qqq1 p1q1].
   apply rep_trans' in qqq1 as [q0 Hq0 q0q1].
   eexists. eassumption.
   now rewrite p0p1, q0q1, Hpq, p1q1.
 Qed.

 (** more laws  *)
 
 Lemma parp0 p: p ∥ 0 ~ p.
 Proof. now rewrite parC, par0p. Qed.

 Section s.
 Context {R: Chain b}.
 #[export] Instance par_Associative: Associative `R par.
 Proof. intros ???. now rewrite parA. Qed.
 #[export] Instance par_Commutative: Commutative `R par.
 Proof. intros ??. now rewrite parC. Qed.
 #[export] Instance par_Unit: Unit `R par 0%ccs.
 Proof. split; intro; now rewrite ?par0p, ?parp0. Qed.
 End s.

 Lemma plsC: forall p q, p+q ~ q+p.
 Proof.
   (* coinduction not necessary, just used here to exploit symmetry argument *)
   coinduction R _. symmetric.
   intros p q l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 Lemma plsA p q r: p+(q+r) ~ (p+q)+r.
 Proof.
   step.
   split; intros l p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.
 
 Lemma plsI p: p+p ~ p.
 Proof.
   step.
   split; intros l p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.

 Lemma pls0p p: 0 + p ~ p.
 Proof.
   step.
   split; intros l p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.
   
 Lemma plsp0 p: p + 0 ~ p.
 Proof. now rewrite plsC, pls0p. Qed.   

 Section s.
 Context {R: Chain b}.
 #[export] Instance pls_Associative: Associative `R pls.
 Proof. intros ???. now rewrite plsA. Qed.
 #[export] Instance pls_Commutative: Commutative `R pls.
 Proof. intros ??. now rewrite plsC. Qed.
 #[export] Instance pls_Idempotent: Idempotent `R pls%ccs.
 Proof. repeat intro; now rewrite plsI. Qed.
 #[export] Instance pls_Unit: Unit `R pls 0%ccs.
 Proof. split; intro; now rewrite ?pls0p, ?plsp0. Qed.
 End s.

 Lemma new_new: forall a b p, new a (new b p) ~ new b (new a p).
 Proof.
   coinduction R H. symmetric.
   intros a b p l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 (* special case of [new_gc] below *)
 Lemma new_zer: forall a, new a 0 ~ 0.
 Proof.
   intro. step. 
   split; intros l' p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.

 Lemma new_prf: forall a l p, fresh a l -> new a (prf l p) ~ prf l (new a p).
 Proof.
   intros. step. 
   split; intros l' p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.

 Lemma new_prf': forall a l p, ~ fresh a l -> new a (prf l p) ~ 0.
 Proof.
   intros. step. 
   split; intros l' p' pp'; cbn; inverse_trans; eauto with ccs; tauto.
 Qed.
 
 Lemma new_sum: forall a p q, new a (p + q) ~ new a p + new a q.
 Proof.
   intros. step.
   split; intros l' p' pp'; cbn; inverse_trans; eauto with ccs. 
 Qed.

 Lemma prf_tau_new c p q: prf tau (new c (p ∥ q)) ~ new c (prf (out c) p ∥ prf (inp c) q).
 Proof.
   step.
   split; intros l p' pp'; cbn; inverse_trans; eauto with ccs; congruence.
 Qed.

 Lemma prf_prf_tau_new_o l c p q:
   fresh c l ->
   prf l (prf tau (new c (p ∥ q))) ~ new c (prf l (prf (out c) p) ∥ prf (inp c) q).
 Proof.
   intro H. step.
   split; intros l' p' pp'; cbn; inverse_trans; try congruence;
     eexists; eauto with ccs; apply prf_tau_new.
 Qed.

 Lemma prf_prf_tau_new_i l c p q:
   fresh c l ->
   prf l (prf tau (new c (p ∥ q))) ~ new c (prf (out c) p ∥ prf l (prf (inp c) q)).
 Proof.
   intro H. step.
   split; intros l' p' pp'; cbn; inverse_trans; try congruence;
     eexists; eauto with ccs; apply prf_tau_new.
 Qed.

 (* is a name [a] fresh in a process *)
 CoInductive freshp (a: N): S -> Prop :=
 | f_nil: freshp a 0
 | f_prf: forall l p, fresh a l -> freshp a p -> freshp a (prf l p) 
 | f_pls: forall p q, freshp a p -> freshp a q -> freshp a (p+q)
 | f_par: forall p q, freshp a p -> freshp a q -> freshp a (p∥q)
 | f_new: forall b p, a=b \/ freshp a p -> freshp a (new b p)
 | f_rep: forall p, freshp a p -> freshp a (!p).

 Lemma freshp_trans a p: freshp a p -> forall l p', trans l p p' -> fresh a l /\ freshp a p'.
 Proof.
   intros F l p' T. revert F.
   induction T; intro F; inversion F; subst; clear F;
     try (split; [cbn; tauto|firstorder; constructor; trivial]).
   - intuition subst; trivial; constructor; tauto.
   - apply IHT. now repeat constructor.
 Qed.

 Lemma new_gc: forall a p, freshp a p -> new a p ~ p.
 Proof.
   intro a. coinduction R HR; intros p Hp.
   pose proof (freshp_trans Hp) as H.
   split; intros l p' pp'; cbn. 
   - inverse_trans. eexists. eauto with ccs. apply HR. eapply H; eauto with ccs. 
   - specialize (H _ _ pp') as [? ?]. eauto with ccs. 
 Qed.

 Lemma prf_tau_new_i c p: freshp c p -> prf tau p ~ new c (prf (out c) 0 ∥ prf (inp c) p).
 Proof.
   intro. rewrite <- prf_tau_new.
   rewrite new_gc. aac_reflexivity.
   now repeat constructor.
 Qed.
 
 Lemma prf_tau_new_o c p: freshp c p -> prf tau p ~ new c (prf (out c) p ∥ prf (inp c) 0).
 Proof.
   intro. rewrite <- prf_tau_new.
   rewrite new_gc. aac_reflexivity.
   now repeat constructor.
 Qed.

 Lemma new_par: forall a p q, freshp a q -> new a (p∥q) ~ (new a p) ∥ q.
 Proof.
   intro a. coinduction R HR. intros p q Hq.
   split; intros l p' pp'; cbn; inverse_trans;
     (match goal with
      | H: trans _ q _ |- _ => destruct (freshp_trans Hq H) as [??]
      | _ => idtac end);
     eauto 10 with ccs.
 Qed.
  
 Proposition rep_trans2 p l p0:
   trans l (!p) p0 ->
   (exists p', trans l p p' /\ p0 ~ !p ∥ p')
   \/ (l=tau /\ exists a po pi, trans (out a) p po /\ trans (inp a) p pi /\ p0 ~ rep p ∥ po ∥ pi).
 Proof.
   intro T. apply rep_trans in T as [p1 T E].
   inversion T; subst; clear T.
   - left. eexists. split. eauto with ccs. rewrite E. now aac_rewrite <-unfold_rep.
   - left. eexists. split. eauto with ccs. rewrite E. now aac_rewrite <-unfold_rep.
   - right. split; trivial. do 4 eexists. eauto with ccs. split. eauto with ccs. rewrite E. aac_reflexivity.
   - right. split; trivial. do 4 eexists. eauto with ccs. split. eauto with ccs. rewrite E. aac_reflexivity.
 Qed.

 Ltac inverse_trans' :=
   match goal with
   | H: trans _ ?p _ |- _ =>
     lazymatch p with
     | rep _ =>
       apply rep_trans2 in H as [(?&?&?)|(?&?&?&?&?&?&?)];
       [|subst || (exfalso; congruence)]; inverse_trans'
     | _ => tryif is_var p then fail else inversion H; subst; clear H; inverse_trans'
     end
   | _ => idtac
   end.
 
 Lemma rep_pls p q: !(p+q) ~ !p ∥ !q.
 Proof.
   coinduction R H.
   split; intros a p' T; cbn; inverse_trans';
     (eexists; [eauto with ccs|rewrite ?H1, ?H3, H; aac_reflexivity]).
 Qed.

 Lemma rep_invol p: !(!p) ~ !p.
 Proof.
   coinduction R H.
   split; intros l p' T; cbn.
   - inverse_trans'.
     eexists. eauto with ccs. rewrite H1, H2. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity.
     eexists. eauto with ccs. rewrite H1, H4. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity. 
     eexists. eauto with ccs. rewrite H3, H2, H4. do 2 aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity.     
   - destruct (rep_trans T) as [? _ E].
     eexists. eauto with ccs. rewrite E. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity. 
 Qed.

 Lemma rep_idem p: !p ~ !p ∥ !p.
 Proof. now rewrite <-rep_pls, plsI. Qed.

 Lemma rep_par p q: !(p ∥ q) ~ !p ∥ !q.
 Proof.
   coinduction R H.
   split; intros a p' T; cbn; inverse_trans';
     (eexists; [eauto with ccs|rewrite ?H1, ?H3, H; repeat aac_rewrite <-unfold_rep; aac_reflexivity]).
 Qed.

 Lemma rep_prf_trans a p b p': trans b (!prf a p) p' -> a=b /\ p' ~ p ∥ !prf a p.
 Proof.
   intro T. apply rep_trans in T as [p'' T E].
   inverse_trans; split; trivial;
     rewrite E; rewrite unfold_rep at 2.
   aac_reflexivity. aac_reflexivity. 
 Qed.
 
 Lemma rep_prf a p: !prf a p ~ prf a (p ∥ !prf a p).
 Proof.
   coinduction R H. split; intros b p' T.
   - apply rep_prf_trans in T as [<- E]. eexists. eauto with ccs. now rewrite E.
   - inverse_trans. eexists. eauto with ccs. cbn. aac_reflexivity. 
 Qed.

 Goal forall a p q, !prf a (p ∥ prf a q) ∥ !prf a (prf a p ∥ q) ~ !prf a p ∥ !prf a q.
 Proof.
   intros. coinduction R H.
   split; intros b p' T; cbn; inverse_trans'.
   - eexists. apply t_par_l; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_r; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_l; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_r; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
 Qed.

 Infix ">>" := (prf) (at level 30, right associativity): ccs_scope. 

 (* NOTE: while the freshness assumptions about b are merely bureaucratic,
    x<>y is crucial in the equality below:
    this equation fails otherwise, thus proving that bisimularity is not closed under substitutions, (even in the absence of sum).
 *)
 Goal forall x y b p,
     b<>x -> b<>y -> freshp b p ->
     x<>y -> 
     !(out y >> inp x >> tau >> p) ∥ !(inp x >> out y >> tau >> p)
     ~ 
     !new b (out y >> out b >> 0 ∥ inp x >> inp b >> p).
 Proof.
   intros x y b p BX BY BP XY.
   assert (BX': fresh b (inp x)) by congruence. 
   assert (BY': fresh b (out y)) by congruence.
   assert (BP': freshp b (0 ∥ p)) by now repeat constructor. 
   coinduction R H.
   split; intros l p' pp'; cbn; inverse_trans'; try congruence; 
     eexists; eauto with ccs; rewrite H1; clear H1; aac_rewrite H; apply par_chain; trivial;
       (* last step just to improve setoid_rewriting performances *)
       apply sub_gfp_Chain.
   - rewrite <-prf_prf_tau_new_i by assumption.
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_o by assumption. 
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_i by assumption.
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_o by assumption. 
     rewrite new_gc by assumption.
     aac_reflexivity.
 Qed.

 (** weak transition system *)
 (** we use an algebraic presentation of this LTS so that we can exploit the tactics from RelationAlgebra in order to reason about reflexive transitive closure *)
 Definition wtrans (l: label): hrel S S :=  
   match l with
   | tau => (trans tau: hrel S S)^*
   | _ => (trans tau: hrel S S)^* ⋅ trans l ⋅ (trans tau: hrel S S)^*
   end.
 
 Lemma trans_wtrans l: forall p p', trans l p p' -> wtrans l p p'.
 Proof.
   change (trans l ≦ wtrans l).
   unfold wtrans; case l; ka.
 Qed.
 Global Hint Resolve trans_wtrans: ccs.
 
 Lemma wnil: forall p, wtrans tau p p.
 Proof. intro. now exists O. Qed.
 Global Hint Resolve wnil: ccs.
 
 Lemma wcons l: forall p p' p'', wtrans tau p p' -> wtrans l p' p'' -> wtrans l p p''.
 Proof.
   assert (wtrans tau ⋅ wtrans l ≦ wtrans l) as H
       by (unfold wtrans; case l; ka).
   intros. apply H. eexists; eassumption.
 Qed.
 Lemma wsnoc l: forall p p' p'', wtrans l p p' -> wtrans tau p' p'' -> wtrans l p p''.
 Proof.
   assert (wtrans l ⋅ wtrans tau ≦ wtrans l) as H
       by (unfold wtrans; case l; ka).
   intros. apply H. eexists; eassumption.
 Qed.

 (** the function defining weak simulations and similarity *)
 Program Definition w: mon (S -> S -> Prop) :=
   {| body R p q :=
        forall l p', trans l p p' -> exists2 q', wtrans l q q' & R p' q' |}.
 Next Obligation. cbv. firstorder. Qed.
 
 (** the symmetrised version, defining weak bisimulations and bisimilarity *)
 Notation wb := (cap w (comp converse (comp w converse))).

 Notation "p ≈ q" := (gfp wb p%ccs q%ccs) (at level 70).
 (** notations  for easing readability in proofs by enhanced coinduction *)
 Infix "[≊]" := (elem (b:=wb) _) (at level 80). 
 Infix "{≊}" := (wb (elem (b:=wb) _)) (at level 80).

 (** elements of the final chain are reflexive and symmetric *)
 #[export] Instance Reflexive_wt: forall {R: Chain wb}, Reflexive `R.
 Proof.
   apply Reflexive_symchain. 
   intros R HR x l x' xx'. exists x'; eauto with ccs. 
 Qed.
 #[export] Instance Symmetric_wt: forall {R: Chain wb}, Symmetric `R.
 Proof. apply Symmetric_symchain. Qed.

 
 (** we get the following law as a basic consequence *)
 Lemma weak_tau p: p ≈ prf tau p.
 Proof.
   step. split.
   - intros l p' H. exists p'. apply wcons with p; auto with ccs. reflexivity.
   - intros l p' H. inverse_trans. exists p'; eauto with ccs. cbn. reflexivity. 
 Qed.


 (** but squaring is not compatible and [t R] is not always transitive, 
     as soon as there is at least one channel name *)
 Lemma not_Transitive_wt: N -> ~ forall R: Chain wb, Transitive `R.
 Proof.
   intros a H.
   cut (prf (out a) nil ≈ nil).
    intro E. apply (gfp_pfp wb) in E as [E _].
    destruct (E (out a) nil) as [?[?[n [k N] N']_]_]. auto with ccs.
    replace n with 0 in N'. inversion N'.
    clear N'. destruct k. assumption.
    destruct N as [? N' ?]. inversion N'.
   rewrite weak_tau. coinduction R CIH. split.
    intros l p' pp'. inverse_trans. exists 0; auto with ccs.
    rewrite weak_tau. assumption. 
    intros l q' qq'. inverse_trans. 
 Qed.

 (** weak bisimilarity is nevertheless transitive, which we prove below *)
 
 (** algebraic refomulation of the right-to-left part of the game *)
 Lemma game_rl l: (gfp wb: hrel _ _) ⋅ trans l ≦ wtrans l ⋅ gfp wb.
 Proof.
   intros p q' [q pq qq']. apply (gfp_pfp wb) in pq as [_ pq]. now apply pq.
 Qed.

 (** (algebraic) extension to weak transitions *)
 Lemma weak_game_rl l: (gfp wb: hrel _ _) ⋅ wtrans l ≦ wtrans l ⋅ gfp wb.
 Proof.
   assert (Htau: (gfp wb: hrel _ _) ⋅ wtrans tau ≦ wtrans tau ⋅ gfp wb).
    unfold wtrans. apply str_ind_r'. ka. mrewrite game_rl. unfold wtrans. ka.
   destruct l.
   - apply Htau. 
   - unfold wtrans at 1. mrewrite Htau. mrewrite game_rl. mrewrite Htau.
     unfold wtrans; ka. 
   - unfold wtrans at 1. mrewrite Htau. mrewrite game_rl. mrewrite Htau.
     unfold wtrans; ka. 
 Qed.

 (* TODO: better interaction with RelationAlgebra *)
 Lemma cnv_wt (R: Chain wb): RelationAlgebra.lattice.weq ((`R: hrel _ _)°) (`R).
 Proof.
   apply RelationAlgebra.lattice.antisym; intros ???.
   now eapply Symmetric_wt.
   now eapply Symmetric_wt in H.
 Qed.
 Lemma cnv_gfp: RelationAlgebra.lattice.weq ((gfp wb: hrel _ _)°) (gfp wb).
 Proof. apply cnv_wt. Qed.
 
 (** by symmetry, similar result for left-to-right game *)
 Lemma weak_game_lr l: cnv _ _ (wtrans l: hrel _ _) ⋅ gfp wb ≦ (gfp wb: hrel _ _) ⋅ cnv _ _ (wtrans l).
 Proof. cnv_switch. rewrite 2cnvdot, cnv_invol, cnv_gfp. apply weak_game_rl. Qed.

 (** left-to-right game on weak transitions *)
 Lemma weak_game p q l p': wtrans l p p' -> p ≈ q -> exists2 q', p' ≈ q' & wtrans l q q'.
 Proof. intros pp' pq. apply weak_game_lr. now exists p. Qed.

 #[export] Instance Equivalence_wbisim: Equivalence (gfp wb).
 Proof.
   split. apply Reflexive_wt. apply Symmetric_wt.
   assert (square (gfp wb) <= gfp wb) as H.
    apply leq_gfp. apply symmetric_pfp.
     rewrite converse_square. apply square. simpl. apply cnv_gfp. (* TODO: rework, coinduction.rel vs relationalgebra.rel *)
    intros x z [y xy yz] l x' xx'. 
    apply (gfp_pfp wb) in xy as [xy _].
    destruct (xy _ _ xx') as [y' yy' x'y'].
    destruct (weak_game _ _ yy' yz) as [z' y'z' zz'].
    exists z'. assumption. now exists y'.  
   intros x y z xy yz. apply H. now exists y.
 Qed.

 (* TODO: up to context for weak bisimulations, expansion, up to expansion 
    TOTHINK: is there a nice way to factorise work so that we study contexts mostly wrt [s] and [w], and then combine for [b] [wb] [e] ? 
  *)
 
End CCS.

(** * A proof by enhanced coinduction  *)

Module acd.
 CoInductive N': Type := a | c | d.
 Definition N := N'.
End acd.
Module Import CCSacd := CCS acd.

(** The four processes from Section 4 *)
CoFixpoint A := inp a >> inp c >> D
      with B := inp a >> inp c >> C
      with C := out a >> (A ∥ C)
      with D := out a >> (B ∥ D).

Lemma dA: A = inp a >> inp c >> D.
Proof. apply Sd. Qed.
Lemma dB: B = inp a >> inp c >> C.
Proof. apply Sd. Qed.
Lemma dC: C = out a >> (A ∥ C).
Proof. apply Sd. Qed.
Lemma dD: D = out a >> (B ∥ D).
Proof. apply Sd. Qed.

(** Utilities to factor code thanks to the (relative) determinism of the considered processes *)
Lemma bAB (R: S -> S -> Prop): R (inp c >> D) (inp c >> C) -> b R A B.
Proof. intro. rewrite dA, dB. split; intros ? ? T; inversion_clear T; eauto with ccs. Qed.
Lemma bCD (R: S -> S -> Prop): R (A ∥ C) (B ∥ D) -> b R C D.
Proof. intro. rewrite dC, dD. split; intros ? ? T; inversion_clear T; eauto with ccs. Qed.

(** the proof by enhanced bisimulation *)
Goal A ~ B /\ C ~ D.
  coinduction R [AB CD]. split.
  apply bAB. now rewrite CD.     (* apply prf_t. now symmetry.  *)
  apply bCD. now rewrite AB, CD. (* now apply par_t.  *)
Qed.

(** refining the candidate on-the-fly, using the [accumulate] tactic *)
Goal A ~ B.
  coinduction R AB.
  apply bAB. apply prf_chain.
  symmetry. accumulate CD. 
  apply bCD. now rewrite AB, CD. 
Qed.
