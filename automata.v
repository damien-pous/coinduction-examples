(** * Example: Automata equivalence *)

Require Import Nat List. Import ListNotations.
From Coinduction Require Import lattice coinduction rel tactics.
From AAC_tactics Require Import AAC.

Set Implicit Arguments.

Section s.
 Notation A := nat.               (* the alphabet is fixed to consist of natural numbers *)
 Notation word := (list A).
 Notation language := (word -> Prop). (* Prop so that star on languages is easier to define *)
 
 Record DA := {
   states:> Set;
   out: states -> bool;              (* bool so that first examples look nicer *)
   next: states -> A -> states;
 }.

 Definition DA0: DA :=
   {|
   states := unit;
   out x := true;
   next x a := x;
   |}.

 Definition DA1: DA :=
   {|
   states := bool;
   out x := x;
   next x a := negb x;
   |}.

 Inductive four := x0|x1|x2|x3.
 Definition DA1': DA :=
   {|
   states := four;
   out x := match x with x1 | x3 => true | _ => false end;
   next x a := match x with x0=>x1 | x1=>x2 | x2=>x3 | x3=>x0 end;
   |}.

 Definition DA2: DA :=
   {|
   states := option nat;
   out x := match x with None => false | _ => true end;
   next x a := match x with None => None | Some b => if leb b a then Some a else None end
   |}.

 Fixpoint L (X: DA) (x: X) (w: word): Prop :=
   match w with
   | [] => out X x = true
   | a::w => L X (next X x a) w
   end.

 (* Compute L DA0 tt       [0;1;2;3]. *)
 (* Compute L DA1 false    [0;1;2;3]. *)
 (* Compute L DA2 (Some 0) [0;1;2;3]. *)
 (* Compute L DA2 (Some 0) [0;1;3;2;4]. *)
 
 Lemma L0: forall w, L DA0 tt w.
 Proof. now induction w; cbn. Qed.

 Lemma L1_false: forall w, L DA1 false w <-> odd (length w) = true.
 Proof.
   cut (forall w b, L DA1 b w <-> (if b then even else odd) (length w) = true).
    intros H w. apply H. 
   induction w; cbn; intro b.
   - now destruct b.
   - rewrite IHw. destruct b.
     now rewrite PeanoNat.Nat.even_succ.
     now rewrite PeanoNat.Nat.odd_succ.
 Qed.

 Lemma L1'_0_L1_false: forall w, L DA1' x0 w <-> L DA1 false w.
 Proof.
   cut (forall w x, L DA1' x w <-> L DA1 (match x with x1 | x3 => true | _ => false end) w).
    intros H w. apply H. 
   induction w; cbn; intro x.
   - reflexivity. 
   - destruct x; apply IHw.
 Qed.

 Lemma L1'_0_2: forall w, L DA1' x0 w <-> L DA1' x2 w.
 Proof.
   cut (forall w, (L DA1' x0 w <-> L DA1' x2 w) /\ (L DA1' x1 w <-> L DA1' x3 w)).
    intros H w. apply H. 
   induction w; cbn; split. 
   - reflexivity. 
   - reflexivity. 
   - apply IHw.
   - symmetry. apply IHw.
 Qed.
 

 Section bisim.
  Variable X: DA.
 
  Definition equiv x y := L X x == L X y.
  Infix "≡" := equiv (at level 70).
  
  Program Definition b: mon (X -> X -> Prop) :=
    {| body R x y := out X x = out X y /\ forall a, R (next X x a) (next X y a) |}.
  Next Obligation. firstorder. Qed.
 
  Infix "~" := (gfp b) (at level 70).

  Lemma bool_eq (b c: bool): b=c <-> (b=true <-> c=true).
  Proof. destruct b; destruct c; intuition congruence. Qed.
  
  Theorem bisimilarity_is_language_equivalence x y: x ~ y <-> x ≡ y.
  (* equivalently, [gfp b == equiv] *)
  Proof.
    split.
    - intros H w. revert x y H. induction w; intros x y H.
      -- apply (gfp_fp b) in H as [H _]. apply bool_eq, H.
      -- apply (gfp_fp b) in H as [_ H]. apply IHw, H.
    - revert x y. apply (leq_gfp b). intros x y xy. split.
      -- apply bool_eq, (xy []).
      -- intros a w. apply (xy (a::w)).
  Qed.
 
  (** notations  for easing readability in proofs by enhanced coinduction *)
  Notation t := (t b).
  Notation T := (T b).
  Notation bt := (bt b).
  Notation bT := (bT b).
  Notation "x ≃[ R ] y" := (t R x y) (at level 79).
  Notation "x ≃ y" := (t _ x y) (at level 79). 
  Notation "x [≃] y" := (bt _ x y) (at level 79).
 
  (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
  Lemma eq_t: const eq <= t.
  Proof.
    apply leq_t. intro R. change (eq <= b eq). 
    intros p ? <-. now split.
  Qed.
  
  (** converse is compatible *)
  Lemma converse_t: converse <= t.
  Proof.
    apply leq_t. intros S x y [xy xy']. split.
    congruence. assumption.
  Qed.
  
  (** so is squaring *)
  Lemma square_t: square <= t.
  Proof.
    apply leq_t. intros S x z [y [xy xy'] [yz yz']]. split.
    congruence. eexists; eauto.
  Qed.
  
  (** thus [t R] and [T f R] are always equivalence relations *)
  Global Instance Equivalence_t R: Equivalence (t R).
  Proof.
    apply Equivalence_t.
    apply eq_t. apply square_t. apply converse_t. 
  Qed.
  Global Instance Equivalence_T f R: Equivalence (T f R).
  Proof.
    apply Equivalence_T.
    apply eq_t. apply square_t. apply converse_t. 
  Qed.
 
 End bisim.

 (** notations  for easing readability in proofs by enhanced coinduction *)
 Notation t := (t (b _)).
 Notation T := (T (b _)).
 Notation bt := (bt (b _)).
 Notation bT := (bT (b _)).
 Infix "~" := (gfp (b _)) (at level 70).
 Notation "x ≃[ R ] y" := (t R x y) (at level 79).
 Notation "x ≃ y" := (t _ x y) (at level 79). 
 Notation "x [≃] y" := (bt _ x y) (at level 79).

 (* so that elements of four are implicitely recognised as states of DA1' *)
 Canonical Structure DA1'.
 
 Goal x0 ~ x2. 
 Proof.
   cut (x0 ~ x2 /\ x1 ~ x3). tauto. 
   coinduction R [H02 H13]. split.
    split. reflexivity. intro; assumption. 
    split. reflexivity. intro; symmetry; assumption. (* note the use of up-to-symmetry *)

   (* discovering the candidate on-the-fly *)
   Restart.
   coinduction R H02. split. reflexivity. cbn; intros _.
   accumulate H13. split. reflexivity. cbn; intros _. now symmetry.
 Qed.

 Inductive four_five := y0|y1|y2|y3 | z0|z1|z2|z3|z4.
 Canonical Structure F45: DA := {|
   states := four_five;
   out _ := true;               (* this example is a bit silly, because all states are accepting *)
   next s a := match s with
               | y0=>y1 | y1=>y2 | y2=>y3 | y3=>y0
               | z0=>z1 | z1=>z2 | z2=>z3 | z3=>z4 | z4=>z0 
               end;
 |}. 
 Goal y0 ~ z0.
 Proof.
   (* naive bisimulation *)
   coinduction R H00. split. reflexivity. cbn; intros _.
   accumulate    H11. split. reflexivity. cbn; intros _.
   accumulate    H22. split. reflexivity. cbn; intros _.
   accumulate    H33. split. reflexivity. cbn; intros _.
   accumulate    H04. split. reflexivity. cbn; intros _.
   accumulate    H10. split. reflexivity. cbn; intros _.
   accumulate    H21. split. reflexivity. cbn; intros _.
   accumulate    H32. split. reflexivity. cbn; intros _.
   accumulate    H03. split. reflexivity. cbn; intros _.
   accumulate    H14. split. reflexivity. cbn; intros _.
   accumulate    H20. split. reflexivity. cbn; intros _.
   accumulate    H31. split. reflexivity. cbn; intros _.
   accumulate    H02. split. reflexivity. cbn; intros _.
   accumulate    H13. split. reflexivity. cbn; intros _.
   accumulate    H24. split. reflexivity. cbn; intros _.
   accumulate    H30. split. reflexivity. cbn; intros _.
   accumulate    H01. split. reflexivity. cbn; intros _.
   accumulate    H12. split. reflexivity. cbn; intros _.
   accumulate    H23. split. reflexivity. cbn; intros _.
   accumulate    H34. split. reflexivity. cbn; intros _.
   apply H00.

   Restart.
   (* using up-to equivalence *)
   coinduction R H00. split. reflexivity. cbn; intros _.
   accumulate    H11. split. reflexivity. cbn; intros _.
   accumulate    H22. split. reflexivity. cbn; intros _.
   accumulate    H33. split. reflexivity. cbn; intros _.
   accumulate    H04. split. reflexivity. cbn; intros _.
   accumulate    H10. split. reflexivity. cbn; intros _.
   accumulate    H21. split. reflexivity. cbn; intros _.
   accumulate    H32. split. reflexivity. cbn; intros _.
   accumulate    H03. split. reflexivity. cbn; intros _.
   (* here we use the fact that ≃[R] is an equivalence relation *)
   now rewrite H11, <-H21, H22, <-H32, H33, <-H03. 

   Restart.
   (* using a smarter candidate (possible here because the example is rather contrived) *)
   generalize y0 z0. 
   coinduction R CIH. now split. 
 Qed.

 (* TODO: regular expressions and derivatives *)
 Inductive regex :=
 | zer
 | one
 | var(a: A)
 | pls(e f: regex)
 | dot(e f: regex)
 | str(e: regex).
 Notation "0" := zer. 
 Notation "1" := one. 
 Infix "+" := pls.
 Infix "·" := dot (at level 40).
 Notation "e ^*" := (str e) (at level 20).

 Definition lang_zer: language := bot. 
 Definition lang_one: language := eq []. 
 Definition lang_var a: language := eq [a].
 Definition lang_pls L K: language := cup L K.
 Definition lang_dot L K: language := fun w => exists u v, L u /\ K v /\ w = u ++ v.
 Fixpoint lang_itr L n: language :=
   match n with
   | O => lang_one
   | S n => lang_dot L (lang_itr L n)
   end.
 Definition lang_str L: language := sup_all (lang_itr L).
 Fixpoint lang (e: regex): language :=
   match e with
   | 0 => lang_zer
   | 1 => lang_one
   | var a => lang_var a
   | e+f => lang_pls (lang e) (lang f)
   | e·f => lang_dot (lang e) (lang f)
   | e^* => lang_str (lang e)
   end.

 Instance lang_pls_weq: Proper (weq ==> weq ==> weq) lang_pls.
 Proof. apply cup_weq. Qed.
 Instance lang_dot_weq: Proper (weq ==> weq ==> weq) lang_dot.
 Proof.
   intros L L' HL K K' HK w.
   unfold lang_dot. setoid_rewrite HL. setoid_rewrite HK.
   reflexivity.
 Qed.
 
 Definition eps (L: language): Prop := L [].
 Definition der (L: language) (a: A): language := fun w => L (a::w).

 Lemma eps_zer: eps lang_zer <-> False.
 Proof. reflexivity. Qed.
 Lemma eps_one: eps lang_one <-> True.
 Proof. intuition reflexivity. Qed.
 Lemma eps_var a: eps (lang_var a) <-> False.
 Proof. intuition congruence. Qed.
 Lemma eps_pls L K: eps (lang_pls L K) <-> eps L \/ eps K.
 Proof. vm_compute. tauto. Qed.
 Lemma eps_dot L K: eps (lang_dot L K) <-> eps L /\ eps K.
 Proof.
   split.
   - intros (u&v&Lu&Kv&uv).
     symmetry in uv. apply app_eq_nil in uv as [-> ->]. now split.
   - intros [eL eK]. now exists [], [].
 Qed.
 Lemma eps_str L: eps (lang_str L) <-> True.
 Proof.
   split; trivial; intros _.
   now exists O. 
 Qed.

 Lemma der_zer a: der lang_zer a == lang_zer.
 Proof. reflexivity. Qed.
 Lemma der_one a: der lang_one a == lang_zer.
 Proof. firstorder congruence. Qed.
 Lemma der_var_same a: der (lang_var a) a == lang_one.
 Proof. cbv. intuition congruence. Qed.
 Lemma der_var_diff a b: a<>b -> der (lang_var a) b == lang_zer.
 Proof. vm_compute. intuition congruence. Qed.
 Lemma der_pls L K a: der (lang_pls L K) a == lang_pls (der L a) (der K a).
 Proof. cbv. tauto. Qed.
 Lemma der_dot_0 L K a: ~eps L -> der (lang_dot L K) a == lang_dot (der L a) K.
 Proof.
   intros H w. split.
   - intros (u&v&Hu&Hv&uv). destruct u as [|b u].
     -- elim (H Hu).
     -- injection uv. intros uv' <-. exists u, v. now split.
   - intros (u&v&Hu&Hv&uv).
     exists (a::u), v. cbn. intuition congruence.
 Qed.
 Lemma der_dot_1 L K a: eps L -> der (lang_dot L K) a == lang_pls (lang_dot (der L a) K) (der K a).
 Proof.
   intros H w. split.
   - intros (u&v&Hu&Hv&uv). destruct u as [|b u].
     -- right. unfold der. now rewrite uv. 
     -- left. injection uv. intros uv' <-. exists u, v. now split.
   - intros [(u&v&Hu&Hv&uv)|Kaw].
     exists (a::u), v. cbn. intuition congruence.
     now exists [], (a::w). 
 Qed.
 Lemma der_str L a: der (lang_str L) a == lang_dot (der L a) (lang_str L).
 Admitted.
 
 Fixpoint reps (e: regex): bool :=
   match e with
   | 0 | var _ => false
   | 1 | _^* => true
   | e+f => reps e || reps f
   | e·f => reps e && reps f
   end.
 Fixpoint rder (e: regex) (a: A): regex :=
   match e with
   | 0 | 1 => 0
   | var b => if eqb a b then 1 else 0
   | e+f => rder e a + rder f a
   (* TOTHINK: if-then-else operation to factorise code? *)
   | e·f => if reps e then rder e a · f + rder f a else rder e a · f
   | e^* => rder e a · e ^*
   end.
 Canonical Structure RX := {| states := regex; out := reps; next := rder |}.

 Lemma eps_lang e: eps (lang e) <-> reps e = true.
 Proof.
   induction e; simpl. 
   - rewrite eps_zer. intuition discriminate. 
   - rewrite eps_one. intuition reflexivity.
   - rewrite eps_var. intuition discriminate.
   - rewrite eps_pls.
     rewrite Bool.orb_true_iff.
     now rewrite IHe1, IHe2. 
   - rewrite eps_dot.
     rewrite Bool.andb_true_iff.
     now rewrite IHe1, IHe2. 
   - rewrite eps_str. intuition reflexivity. 
 Qed.

 Lemma der_lang e a: der (lang e) a == lang (rder e a).
 Proof. 
   induction e; simpl lang. 
   - apply der_zer. 
   - apply der_one.
   - case PeanoNat.Nat.eqb_spec.
     -- intros <-. apply der_var_same. 
     -- intro. apply der_var_diff. congruence.
   - now rewrite der_pls, IHe1, IHe2. 
   - case_eq (reps e1).
     -- intro. rewrite der_dot_1. now rewrite IHe1, IHe2.
        now apply eps_lang.
     -- intro. rewrite der_dot_0. now rewrite IHe1.
        rewrite eps_lang. congruence. 
   - now rewrite der_str, IHe.
 Qed.
     
 Theorem Lang: forall e, lang e == L RX e.
 Proof.
   (* in fact, we have just proven that lang is a coalgebra homomorphism, so that it must coincide with L by finality *)
   intros e w. revert e. induction w; intro e.
   - apply eps_lang.
   - simpl L. rewrite <-IHw. apply der_lang.
 Qed.
 
 Corollary bisim_lang e f: e ~ f <-> lang e == lang f.
 Proof.
   rewrite 2Lang.
   rewrite bisimilarity_is_language_equivalence.
   reflexivity.
 Qed.

 Lemma plsA: forall e f g, e+(f+g) ~ (e+f)+g.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.orb_assoc.
   - intro. apply H.

   Restart.
   intros. rewrite bisim_lang. apply cupA. 
 Qed.
 
 Lemma plsC: forall e f, e+f ~ f+e.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.orb_comm.
   - intro. apply H.

   Restart.
   intros. rewrite bisim_lang. apply cupC. 
 Qed.

 Lemma plsI: forall e, e+e ~ e.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.orb_diag.
   - intro. apply H.

   Restart.
   intros. rewrite bisim_lang. apply cupI. 
 Qed.

 Lemma pls0x: forall x, 0 + x ~ x.
 Proof. now coinduction R H; cbn. Qed.
   
 Lemma plsx0 x: x + 0 ~ x.
 Proof. now rewrite plsC, pls0x. Qed.   

 (** addition corresponds to a compatible function *)
 Lemma ctx_pls_t: binary_ctx pls <= t.
 Proof.
   apply leq_t. intro R. apply (leq_binary_ctx pls).
   intros x x' [Hx Hx'] y y' [Hy Hy'].
   split; cbn.
   - cbn in Hx, Hy. congruence.
   - intro. now apply in_binary_ctx. 
 Qed.
 Instance pls_t: forall R, Proper (t R ==> t R ==> t R) pls := binary_proper_t ctx_pls_t.
 Instance pls_T f: forall R, Proper (T f R ==> T f R ==> T f R) pls := binary_proper_T ctx_pls_t.

 Instance pls_Associative R: Associative (t R) pls.
 Proof. intros ???. apply (gfp_t (b _)), plsA. Qed.
 Instance pls_Commutative R: Commutative (t R) pls.
 Proof. intros ??. apply (gfp_t (b _)), plsC. Qed.
 Instance pls_Unit R: Unit (t R) pls 0.
 Proof. split; intro; apply (gfp_t (b _)). apply pls0x. apply plsx0. Qed.

 Lemma dotplsx: forall e f g, (e+f)·g ~ e·g + f·g.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.andb_orb_distrib_l.
   - intro. case reps; case reps; cbn; rewrite H.
     -- aac_rewrite plsI in_right. aac_reflexivity. 
     -- aac_reflexivity. 
     -- aac_reflexivity. 
     -- reflexivity.
 Qed.

 Lemma dotxpls: forall e f g, g·(e+f) ~ g·e + g·f.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.andb_orb_distrib_r.
   - intro. case reps; cbn; rewrite H.
     -- aac_reflexivity. 
     -- reflexivity. 
 Qed.
 
 Lemma dotA: forall e f g, e·(f·g) ~ (e·f)·g.
 Proof.
   coinduction R H; split; cbn.
   - apply Bool.andb_assoc.
   - intro. case reps; case reps; cbn; trivial.
     -- rewrite dotplsx, H. aac_reflexivity.
     -- rewrite dotplsx, H. reflexivity. 
 Qed.

 Lemma dot0x: forall g, 0·g ~ 0.
 Proof. now coinduction R H; cbn. Qed.

 Lemma dotx0: forall g, g·0 ~ 0.
 Proof.
   coinduction R H; split; cbn.
   - now rewrite Bool.andb_comm. 
   - intro. now case reps; cbn; rewrite H, ?plsI. 
 Qed.

 Lemma dot1p: forall p, 1 · p ~ p.
 Proof.
   coinduction R H; split; cbn.
   - reflexivity.
   - intro. now rewrite dot0x, pls0x. 
 Qed.
   
 Lemma dotp1: forall p, p · 1 ~ p.
 Proof.
   coinduction R H; split; cbn.
   - now rewrite Bool.andb_comm. 
   - intro. case reps; now rewrite H, ?plsx0.
 Qed.   

 (** concatenation corresponds to a compatible function *)
 Lemma ctx_dot_t: binary_ctx dot <= t.
 Proof.
   apply Coinduction. intro R. apply (leq_binary_ctx dot).
   intros x x' [Hx Hx'] y y' Hy.
   split.
   - destruct Hy as [Hy _]; cbn in *; congruence.
   - intro. cbn in Hx. cbn. rewrite Hx; case reps.
     apply pls_T. 
     1,3: apply binary_proper_Tctx. 
     1,3: apply (id_T (b _)), Hx'.
     1,2: apply (b_T (b _)), Hy.
     1:   apply (id_T (b _)), Hy.
 Qed.
 Instance dot_t: forall R, Proper (t R ==> t R ==> t R) dot := binary_proper_t ctx_dot_t.

 Instance dot_Associative R: Associative (t R) dot.
 Proof. intros ???. apply (gfp_t (b _)), dotA. Qed.
 Instance dot_Unit R: Unit (t R) dot 1.
 Proof. split; intro; apply (gfp_t (b _)). apply dot1p. apply dotp1. Qed.
 
 Goal forall e f, (e+f)^* ~ f^*·(e·f^*)^*.
 Proof.
   intros; coinduction R H; split; cbn.
   - reflexivity. 
   - intro. case reps; rewrite H, !dotplsx.
     -- aac_rewrite plsI in_right. aac_reflexivity.
     -- aac_reflexivity.
 Qed.

 Lemma str_unfold e: e^* ~ 1 + e·e^*.
 Proof.
   coinduction R H. split. reflexivity.
   intro; cbn; rewrite pls0x.
   case reps; trivial. now rewrite plsI.
 Qed.
 
 Goal forall e f, (e·f)^*·e ~ e·(f·e)^*.
 Proof.
   intros; coinduction R H; split; cbn.
   - now rewrite Bool.andb_comm. 
   - intro. case reps. case reps.
     all: aac_rewrite H.
     (* need more lemmas *)
     -- rewrite 2dotplsx. aac_rewrite plsI in_right.
        rewrite str_unfold at 3.
        rewrite dotxpls. aac_reflexivity. 
     -- rewrite dotplsx. 
        rewrite str_unfold at 3.
        rewrite dotxpls. aac_reflexivity. 
     -- rewrite str_unfold at 2.
        rewrite dotxpls. aac_reflexivity. 
 Qed.
 
 (* TODO: non-determinism *)

End s.

