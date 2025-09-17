(** * Automata, regular expressions, language equivalence *)

From Stdlib Require Import PeanoNat List. Import ListNotations.
From Coinduction Require Import all. Import CoindNotations.
From AAC_tactics Require Import AAC.
Transparent cup bot.

Set Implicit Arguments.

(** we take natural numbers as alphabet (letters) *)
Notation A := nat.
(** words are lists of letters *)
Notation word := (list A).
(** languages are predicates on words *)
Notation language := (word -> Prop). 

(** * Deterministic automata *)
Module Import DA.

 (** our automata do not have initial states: 
     we shall look at the languages some states in an automaton *)
 Class DA := {
  states: Set;                  (* states *)
  out: states -> bool;          (* which states are accepting *)
  next: states -> A -> states;  (* transition function *)
 }.
 Coercion states: DA >-> Sortclass.

 (** language of a state in an automaton *)
 Fixpoint L (X: DA) (x: X) (w: word): Prop :=
  match w with
  | [] => out x = true
  | a::w => L X (next x a) w
  end.
End DA.

(** an automaton with a single state *)
Definition DA0: DA :=
  {|
  states := unit;
  out x := true;
  next x a := x;
  |}.

(** an automaton with two states *)
Definition DA1: DA :=
  {|
  states := bool;
  out x := x;
  next x a := negb x;
  |}.

(** an automaton with four states *)
Inductive four := x0|x1|x2|x3.
Definition DA1': DA :=
  {|
  states := four;
  out x := match x with x1 | x3 => true | _ => false end;
  next x a := match x with x0=>x1 | x1=>x2 | x2=>x3 | x3=>x0 end;
  |}.

(** an automaton with infinitely many states *)
Definition DA2: DA :=
  {|
  states := option nat;
  out x := match x with None => false | _ => true end;
  next x a := match x with None => None | Some b => if Nat.leb b a then Some a else None end
  |}.

(*
Compute L DA0 tt       [0;1;2;3].
Compute L DA1 false    [0;1;2;3].
Compute L DA2 (Some 0) [0;1;2;3].
Compute L DA2 (Some 0) [0;1;3;2;4].
*)

(** explicit characterisations of the languages recognised by some states in the above automata *)
Lemma L0: forall w, L DA0 tt w.
Proof. now induction w; cbn. Qed.

Lemma L1_false: forall w, L DA1 false w <-> Nat.odd (length w) = true.
Proof.
  cut (forall w b, L DA1 b w <-> (if b then Nat.even else Nat.odd) (length w) = true).
   intros H w. apply H. 
  induction w; cbn; intro b.
  - now destruct b.
  - rewrite IHw. destruct b.
    now rewrite Nat.even_succ.
    now rewrite Nat.odd_succ.
Qed.

(** direct proofs of language equivalence of some states in the above automata *)
Lemma L1'_0_L1_false: L DA1' x0 == L DA1 false.
Proof.
  cut (forall x, L DA1' x == L DA1 (match x with x1 | x3 => true | _ => false end)).
   intros H w. apply H. 
  intros x w; revert x; induction w; cbn; intro x.
  - reflexivity. 
  - destruct x; apply IHw.
Qed.

Lemma L1'_0_2: L DA1' x0 == L DA1' x2.
Proof.
  cut (forall w, (L DA1' x0 w <-> L DA1' x2 w) /\ (L DA1' x1 w <-> L DA1' x3 w)).
   intros H w. apply H. 
  induction w; cbn; split. 
  - reflexivity. 
  - reflexivity. 
  - apply IHw.
  - symmetry. apply IHw.
Qed.

(** * Coinductive approach to language equivalence in automata *)

Section bisim.
 (** we fix an automaton X *)
 Variable X: DA.

 (** language equivalence be tween the states of X *)
 Definition equiv x y := L X x == L X y.
 Infix "≡" := equiv (at level 70).

 (** a montone function on relations on X *)
 Program Definition b: mon (X -> X -> Prop) :=
   {| body R x y := out x = out y /\ forall a, R (next x a) (next y a) |}.
 Next Obligation. firstorder. Qed.

 (** whose greatest fixpoint coincides with language equivalence *)
 Infix "~" := (gfp b) (at level 70).

 Lemma bool_eq (b c: bool): b=c <-> (b=true <-> c=true).
 Proof. destruct b; destruct c; intuition congruence. Qed.
 
 Theorem bisimilarity_is_language_equivalence x y: x ~ y <-> x ≡ y.
 (* equivalently, [gfp b == equiv] *)
 Proof.
   split.
   - intros H w. revert x y H. induction w; intros x y H.
     -- apply (gfp_pfp b) in H as [H _]. apply bool_eq, H.
     -- apply (gfp_pfp b) in H as [_ H]. apply IHw, H.
   - revert x y. apply (leq_gfp b). intros x y xy. split.
     -- apply bool_eq, (xy []).
     -- intros a w. apply (xy (a::w)).
 Qed.

 (** notations  for easing readability in proofs by enhanced coinduction *)
 Notation "x [~] y" := (`_ x y) (at level 79). 
 Notation "x {~} y" := (b `_ x y) (at level 79).

 (** elements of the final chain are all equivalence relations *)
 #[export] Instance Equivalence_chain {R: Chain b}: Equivalence `R.
 Proof.
   constructor; revert R.
   - apply Reflexive_chain. intros R HR x. now split.
   - apply Symmetric_chain. intros R HR x y []. now split; symmetry.
   - apply Transitive_chain. intros R HR x y z [] []. split. congruence. etransitivity; auto. 
 Qed.

End bisim.

(** reexporting notations *)
Infix "~" := (gfp (b _)) (at level 70).
Notation "x [~] y" := (`_ x y) (at level 79). 
Notation "x {~} y" := (b _ `_ x y) (at level 79).


(** make sure that elements of four are implicitely recognised as states of DA1' *)
Canonical Structure DA1'.

Ltac next := split; [reflexivity||fail "different outputs" | cbn; (intros _ || intro)].

Goal x0 ~ x2.                   (* here, implicitely, we play the bisimulation game in DA1' *)
Proof.
  coinduction R H. next.
  (* coinductive hypothesis is not strong enough *)
  
  Restart.
  (* we restart the proof by strengthening the invariant *)
  cut (x0 ~ x2 /\ x1 ~ x3). tauto. 
  coinduction R [H02 H13]. split; next.
   assumption. 
   symmetry; assumption. (* note the use of up-to-symmetry *)

  (* discovering the candidate on-the-fly, using the [accumulate] tactic 
     this tactic is based on the 'accumulation rule': x <= bt(x+y) implies x <= ty *)
  Restart.
  coinduction R H02. next. 
  accumulate H13. next. now symmetry.
Qed.

(** an automaton with 4+5 states, actually the disjoint union of two automata with 4 and 5 states 
    (hint: draw it)
*)
Inductive four_five := y0|y1|y2|y3 | z0|z1|z2|z3|z4.
Canonical Structure F45: DA := {|
  states := four_five;
  out _ := true;               (* this example is a bit silly, because all states are accepting *)
  next s a := match s with
              | y0=>y1 | y1=>y2 | y2=>y3 | y3=>y0
              | z0=>z1 | z1=>z2 | z2=>z3 | z3=>z4 | z4=>z0 
              end;
|}. 

(** brute-force exploration tactic *)
Ltac explore := next; assumption || (accumulate ?; explore).

Goal y0 ~ z0.
Proof.
  (* naive bisimulation: 20 pairs *)
  coinduction R H00. next.
  accumulate    H11. next.
  accumulate    H22. next.
  accumulate    H33. next.
  accumulate    H04. next.
  accumulate    H10. next.
  accumulate    H21. next.
  accumulate    H32. next.
  accumulate    H03. next.
  accumulate    H14. next.
  accumulate    H20. next.
  accumulate    H31. next.
  accumulate    H02. next.
  accumulate    H13. next.
  accumulate    H24. next.
  accumulate    H30. next.
  accumulate    H01. next.
  accumulate    H12. next.
  accumulate    H23. next.
  accumulate    H34. next.
  apply H00.

  Restart.
  (* same naive bisimulation, but automatised *)
  coinduction R ?. explore.

  Restart.
  (* bisimulation up-to equivalence: 8 pairs, but harder to automatise (feasible though) *)
  coinduction R H00. next.
  accumulate    H11. next.
  accumulate    H22. next.
  accumulate    H33. next.
  accumulate    H04. next.
  accumulate    H10. next.
  accumulate    H21. next.
  accumulate    H32. next.
  accumulate    H03. next.
  (* here we use the fact that ≃[R] is an equivalence relation *)
  now rewrite H11, <-H21, H22, <-H32, H33, <-H03. 

  Restart.
  (* using a smarter candidate (possible here because the example is rather contrived) *)
  generalize y0 z0. 
  coinduction R CIH. now split. 
Qed.


(** * Non-deterministic automata *)
Module NA.
 Class NA := {
  states: Set;
  out: states -> bool;
  next: states -> A -> list states; (* each state has a list of successors along each letter *)
 }.
End NA.
Notation NA := NA.NA.
Coercion NA.states: NA >-> Sortclass.

(** language of a state in a non-deterministic automaton *)
Fixpoint NL (X: NA) (x: X) (w: word) :=
  match w with
  | [] => NA.out x = true
  | a::w => exists y, In y (NA.next x a) /\ NL X y w
  end.

(** language of a list of states in a non-deterministic automaton *)
Definition nL (X: NA) (l: list X) (w: word) := exists x, In x l /\ NL X x w.

Lemma nL_single X x: NL X x == nL X [x].
Proof. firstorder congruence. Qed.

(** determinisation, via the powerset constructions,
    here we use lists as an approximation of finite sets, we shall see later that we need to remove duplicates in those lists in order to preserve finiteness 
    accordingly, list concatenation (app) approximates set-theoretic union
 *)
Canonical Structure det (X: NA): DA :=
 {|
  DA.states := list X;
  DA.out l := existsb NA.out l;
  DA.next l a := flat_map (fun x => NA.next x a) l;
 |}.

Lemma L_det_nil (X: NA): L (det X) [] == bot.
Proof.
  intro w. induction w.
  - now cbv. 
  - apply IHw. 
Qed.
Lemma L_det_app (X: NA) h k: L (det X) (h++k) == cup (L (det X) h) (L (det X) k).
Proof.
  intro w. revert h k; induction w; intros h k.
  - simpl. now rewrite existsb_app, Bool.orb_true_iff.
  - simpl. rewrite flat_map_app. apply IHw.
Qed.
  
Lemma L_det_flat_map (X: NA) A f (l: list A) w: L (det X) (flat_map f l) w <-> exists x, In x l /\ L (det X) (f x) w.
Proof.
  induction l; simpl.
  - rewrite (L_det_nil _ w). firstorder.
  - rewrite (L_det_app _ _ _ w). simpl. rewrite IHl.
    firstorder congruence. 
Qed.

(** main theorem for the powerset construction:
    the language of a set in the determinised automaton is the corresponding language in the non-deterministic automaton *)
Theorem L_det (X: NA) l: L (det X) l == nL X l.
Proof.
  intro w; revert l; induction w as [|a w IH]; intro l.
  - simpl. now rewrite existsb_exists.
  - simpl. rewrite L_det_flat_map. now setoid_rewrite IH.
Qed.
Corollary L_det_single (X: NA) x: L (det X) [x] == NL X x.
Proof. now rewrite L_det, nL_single. Qed.


(** up-to union technique in determinised automata *)
Section d.
 Variable X: NA. 
 Notation b := (b (det X)).
 
 (** list concatenation (i.e., union) seen as a context is compatible, 
     and hence below the companion, and hence preserves all elements of the final chain of b *)
 #[export] Instance app_chain: forall {R: Chain b}, Proper (`R ==> `R ==> `R) (@app _).
 Proof.
   apply (Proper_chain 2). 
   intros R HR x x' xx' y y' yy'. split.
   - simpl. rewrite 2existsb_app.
     f_equal. apply xx'. apply yy'.
   - intro a. simpl. rewrite 2flat_map_app.
     apply HR. apply xx'. apply yy'.
 Qed.

 (** moreover, list concatenation (which actually implements union), 
     is associative, commutative, idempotent *)
 Lemma appC: forall h k: list X, h++k ~ k++h.
 Proof.
   coinduction R H.
   intros h k. split; cbn.
   - now rewrite 2existsb_app, Bool.orb_comm.
   - intro a. rewrite 2flat_map_app. apply H.
 Qed.

 Lemma appI: forall h: list X, h++h ~ h.
 Proof.
   coinduction R H.
   intros h. split; cbn.
   - now rewrite existsb_app, Bool.orb_diag.
   - intro a. rewrite flat_map_app. apply H.
 Qed.

 Lemma appA: forall h k l: list X, h++(k++l) ~ (h++k)++l.
 Proof.
   intros. now rewrite app_assoc. 
 Qed.

 Section s.
 Context {R: Chain b}. 
 #[export] Instance aac_appA: Associative `R (@app _).
 Proof. repeat intro. now rewrite appA. Qed.
 #[export] Instance aac_appC: Commutative `R (@app _).
 Proof. repeat intro. now rewrite appC. Qed.
 #[export] Instance aac_appI: Idempotent `R (@app _).
 Proof. repeat intro. now rewrite appI. Qed.
 #[export] Instance aac_appU: Unit `R (@app _) [].
 Proof. split; intro. reflexivity. now rewrite app_nil_r. Qed.

 (* this lemma should not be useful with better aac_tactics *)
 Lemma appM {x y z k k' l l'}: `R (x++y++k) (z++k') -> `R (x++y++l) (z++l') -> `R (x++y++k++l) (z++k'++l').
 Proof. 
   intros K L.
 Admitted.
 (*   rewrite appA, K. *)
 (*   rewrite <-appA, (appC k' l), appA, L. *)
 (*   now rewrite <-appA, (appC l' k'), appA. *)
 (* Qed. *)
   
 End s.

 
 (** declaring the above instances makes it possible to use the [aac_reflexivity] tactic to solve equations modulo ACI *)
 Goal forall x y z: X, [x]++[y]++[x]++[z] ~ [y]++[x]++[z].
 Proof.
   intros. aac_reflexivity. 
 Qed.

End d.

(* a tactic to 'fold' concatenations:
   when the goal contains a list [x;y;z], it gets replaced by [x]++[y]++[z]
   this makes it possible to use tactics like [aac_reflexivity]
 *)
Ltac fold_app :=
  repeat match goal with
          | |- context[?a::?q] =>
            lazymatch q with [] => fail
                        | _ => change (a::q) with ([a]++q) end
          | H: context[?a::?q] |- _ =>
            lazymatch q with [] => fail
                        | _ => change (a::q) with ([a]++q) in H end
         end.

(** a non-deterministic automaton with four states 
    (hint: draw it)
 *)
Canonical Structure NA0: NA :=
 {|
  NA.states := four;
  NA.out x := match x with x2 => false | _ => true end;
  NA.next x a := match x with x0=>[x1;x2] | x1=>[x0] | x2=>[x1] | x3=>[x3] end;
 |}.
 
Goal [x0] ~ [x3].
Proof.
  (* first a bisimulation (four pairs) *)
  coinduction R H. next.
  accumulate H'. next.
  accumulate H''. next.
  accumulate H'''. next.
  rewrite <- H'''. 
  fold_app. aac_reflexivity.

  (* then a bisimulation up to congruence (two pairs) *)
  Restart.
  coinduction R H. next.
  accumulate H'. next.
  fold_app.
  rewrite H. rewrite <-H'. fold_app. aac_reflexivity. 
Qed.

Module EXP.
 (** an automaton with 3(n+1) states, here with n=3 *)
 Variant T := x | x1 | x2 | x3
            | y | y1 | y2 | y3
            | z | z1 | z2 | z3.
 Canonical Structure NAS: NA :=
   {|
   NA.states := T;
   NA.out s := match s with x3 | y3 | z3 => true | _ => false end;
   NA.next s a :=
     match a,s
     with
     | S(S _),_ => []
     | 0,x => [x;x1] | 1,x => [x] | _,x1 => [x2] | _,x2 =>[x3] | _,x3 =>[]
     | 1,y => [y;y1] | 0,y => [y] | _,y1 => [y2] | _,y2 =>[y3] | _,y3 =>[]
     | _,z => [z;z1]              | _,z1 => [z2] | _,z2 =>[z3] | _,z3 =>[]
     end;
   |}.

 (* there are only two letters of interest (0,1), so that we can use the following helper lemmas to analyse transitions *)
 Lemma next2 (x: list T) a: next x (S (S a)) = [].
 Proof. destruct x as [|x q]; cbn. reflexivity. now induction q. Qed.
 Lemma forall2 (R: Chain (b (det NAS))) (x y: list T):
   `R (next x 0) (next y 0) /\ `R (next x 1) (next y 1)
   -> (forall a, `R (next x a) (next y a)).
 Proof.
   intros [H0 H1].
   intros [|[|a]]; trivial.
   now rewrite 2next2. 
 Qed.

 (** a proof with an exponential bisimulation (here, 15 pairs)*)
 Goal [x;y] ~ [z].
 Proof.
   cut ([x;y] ~ [z]
   /\ [x; x1; y] ~ [z; z1]
   /\ [x; y; y1] ~ [z; z1]
   /\ [x; x1; x2; y] ~ [z; z1; z2]
   /\ [x; x2; y; y1] ~ [z; z1; z2]
   /\ [x; x1; y; y2] ~ [z; z1; z2]
   /\ [x; y; y1; y2] ~ [z; z1; z2]
   /\ [x; x1; x2; x3; y] ~ [z; z1; z2; z3]
   /\ [x; x2; x3; y; y1] ~ [z; z1; z2; z3]
   /\ [x; x1; x3; y; y2] ~ [z; z1; z2; z3]
   /\ [x; x3; y; y1; y2] ~ [z; z1; z2; z3]
   /\ [x; x1; x2; y; y3] ~ [z; z1; z2; z3]
   /\ [x; x2; y; y1; y3] ~ [z; z1; z2; z3]
   /\ [x; x1; y; y2; y3] ~ [z; z1; z2; z3]
   /\ [x; y; y1; y2; y3] ~ [z; z1; z2; z3])
   .
   tauto.
   coinduction R H. repeat split; trivial; apply forall2; cbn; tauto. 
 Qed.

 (** a proof with a linear bisimulation up to union (here 7 pairs) *)
 Goal [x;y] ~ [z].
 Proof.
   cut ([x;y] ~ [z]
   /\ [x; y; x1] ~ [z; z1]
   /\ [x; y; y1] ~ [z; z1]
   /\ [x; y; x2] ~ [z; z2]
   /\ [x; y; y2] ~ [z; z2]
   /\ [x; y; x3] ~ [z; z3]
   /\ [x; y; y3] ~ [z; z3])
   .
   tauto.
   coinduction R (H&Hx1&Hy1&Hx2&Hy2&Hx3&Hy3).
   repeat split; trivial; apply forall2; cbn; split; trivial; fold_app.
   1,10,11: now aac_rewrite Hx1.
   (* aac_tactics are painful here *)
   - rewrite <- (appM Hx1 Hx2); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hy1 Hx2); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hx1 Hy2); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hy1 Hy2); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hx1 Hx3); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hy1 Hx3); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hx1 Hy3); cbn; fold_app; aac_reflexivity. 
   - rewrite <- (appM Hy1 Hy3); cbn; fold_app; aac_reflexivity. 
 Qed.
 
End EXP.


(** * Regular expressions *)

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
Infix "·" := dot (at level 41, right associativity).
Notation "e ^*" := (str e) (at level 20).
Notation "e ^+" := (e·e^*) (at level 20).

(** ** regular operations on languages *)
Definition lang_zer: language := bot. 
Definition lang_one: language := eq []. 
Definition lang_var a: language := eq [a].
Definition lang_pls L K: language := cup L K.
Definition lang_dot L K: language := fun w => exists u v, L u /\ K v /\ w = u ++ v.
Arguments lang_zer _/.
Arguments lang_one _/.
Arguments lang_var _ _/.
Arguments lang_pls _ _ _/.
Arguments lang_dot _ _ _/.
Fixpoint lang_itr L n: language :=
  match n with
  | O => lang_one
  | S n => lang_dot L (lang_itr L n)
  end.
Definition lang_str L: language := sup' top (lang_itr L).

(** by recursion, language of a regular expression  *)
Fixpoint lang (e: regex): language :=
  match e with
  | 0 => lang_zer
  | 1 => lang_one
  | var a => lang_var a
  | e+f => lang_pls (lang e) (lang f)
  | e·f => lang_dot (lang e) (lang f)
  | e^* => lang_str (lang e)
  end.

(** notation for language equivalent expressions *)
Notation "e ≡ f" := (lang e == lang f) (at level 80).

#[export] Instance lang_pls_weq: Proper (weq ==> weq ==> weq) lang_pls.
Proof. apply cup_weq. Qed.
#[export] Instance lang_dot_weq: Proper (weq ==> weq ==> weq) lang_dot.
Proof.
  cbn. intros L L' HL K K' HK w.
  unfold lang_dot. setoid_rewrite HL. setoid_rewrite HK.
  reflexivity.
Qed.
Lemma lang_itr_weq: Proper (weq ==> eq ==> weq) lang_itr.
Proof.
  intros L L' HL i i' <-. induction i.
  reflexivity. now apply lang_dot_weq. 
Qed.
#[export] Instance lang_str_weq: Proper (weq ==> weq) lang_str.
Proof.
  intros L L' HL. unfold lang_str.
  apply sup_weq. reflexivity. intro. now apply lang_itr_weq.
Qed.

(** testing a language for the empty word *)
Definition lang_eps (L: language): Prop := L [].

(** derivative of a language (a^-1 L) *)
Definition lang_der (L: language) (a: A): language := fun w => L (a::w).

(** properties of [lang_eps]  *)
Lemma eps_zer: lang_eps lang_zer <-> False.
Proof. reflexivity. Qed.
Lemma eps_one: lang_eps lang_one <-> True.
Proof. intuition reflexivity. Qed.
Lemma eps_var a: lang_eps (lang_var a) <-> False.
Proof. intuition congruence. Qed.
Lemma eps_pls L K: lang_eps (lang_pls L K) <-> lang_eps L \/ lang_eps K.
Proof. cbv. tauto. Qed.
Lemma eps_dot L K: lang_eps (lang_dot L K) <-> lang_eps L /\ lang_eps K.
Proof.
  split.
  - intros (u&v&Lu&Kv&uv).
    symmetry in uv. apply app_eq_nil in uv as [-> ->]. now split.
  - intros [eL eK]. now exists [], [].
Qed.
Lemma eps_str L: lang_eps (lang_str L) <-> True.
Proof.
  split; trivial; intros _.
  now exists O. 
Qed.

(** injecting propositions into languages (empty language if False, 1={epsilon} otherwise) *)
Definition lang_tst (P: Prop): language := fun w => w=[] /\ P.
Coercion lang_tst: Sortclass >-> Funclass.

(** properties of [lang_der]  *)
Lemma der_zer a: lang_der lang_zer a == lang_zer.
Proof. reflexivity. Qed.
Lemma der_one a: lang_der lang_one a == lang_zer.
Proof. firstorder congruence. Qed.
Lemma der_var a b: lang_der (lang_var a) b == (b=a).
Proof. cbv. firstorder congruence. Qed.
Lemma der_pls L K a: lang_der (lang_pls L K) a == lang_pls (lang_der L a) (lang_der K a).
Proof. cbv. tauto. Qed.
Lemma der_dot L K a:
  lang_der (lang_dot L K) a ==
  lang_pls (lang_dot (lang_der L a) K) (lang_dot (lang_eps L) (lang_der K a)).
Proof.
  intros w. split.
  - intros (u&v&Hu&Hv&uv). destruct u as [|b u].
    -- right. exists [], w. unfold lang_der. rewrite uv. now split.
    -- left. injection uv. intros uv' <-. exists u, v. now split.
  - intros [(u&v&Hu&Hv&uv)|Kaw].
    exists (a::u), v. cbn. intuition congruence.
    exists [], (a::w).
    now destruct Kaw as (u&w'&[-> eL]&Kaw&->).
Qed.   
Lemma der_str L a: lang_der (lang_str L) a == lang_dot (lang_der L a) (lang_str L).
Proof.
  intros w. split.
  - intros [i _ H]. induction i in w,H.
    -- discriminate.
    -- destruct H as (u&v&Hu&Hv&uv). destruct u as [|b u].
       --- apply IHi. now rewrite uv.
       --- injection uv; intros -> <-. clear uv.
           exists u, v. split. assumption. split. now exists i. reflexivity.
  - intros (u&v&Hu&Hv&->). 
    destruct Hv as [i _ Hv]. exists (S i). trivial. 
    now exists (a::u), v. 
Qed.


(** ** Brzozowski's derivatives 
    
    a standard way to obtain a deterministic automaton for regular expressions, syntactically

*)

(** epsilon test *)
Fixpoint eps (e: regex): bool :=
  match e with
  | 0 | var _ => false
  | 1 | _^* => true
  | e+f => eps e || eps f
  | e·f => eps e && eps f
  end.

(** seeing a Boolean value as a regular expression  *)
Definition tst (b: bool): regex := if b then 1 else 0.
Coercion tst: bool >-> regex.

(** Brzozowski's derivatives  *)
Fixpoint der (e: regex) (a: A): regex :=
  match e with
  | 0 | 1 => 0
  | var b => Nat.eqb a b
  | e+f => der e a + der f a
  | e·f => der e a · f + eps e · der f a
  | e^* => der e a · e ^*
  end.

(** deterministic automaton associated to Brzozowski's derivatives *)
Canonical Structure BRZ := {| states := regex; out := eps; next := der |}.

Lemma lang_eps_lang e: lang_eps (lang e) <-> eps e = true.
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
Lemma Lang_eps e: lang (eps e) == lang_tst (lang_eps (lang e)).
Proof.
  intros w. unfold lang_tst. rewrite lang_eps_lang. 
  now case eps.
Qed.

Lemma Lang_tst b P: Bool.reflect P b -> lang (tst b) == lang_tst P.
Proof. destruct 1; cbv; firstorder. Qed.

Lemma Lang_der e a: lang (der e a) == lang_der (lang e) a.
Proof.
  symmetry.
  induction e; simpl lang. 
  - apply der_zer. 
  - apply der_one.
  - rewrite der_var. symmetry. apply Lang_tst. apply PeanoNat.Nat.eqb_spec.
  - now rewrite der_pls, IHe1, IHe2. 
  - now rewrite der_dot, IHe1, IHe2, Lang_eps. 
  - now rewrite der_str, IHe.
Qed.

(** the language of an expression coincides with
    the language of this expression in Brzozowski's automaton *)
Theorem L_BRZ: forall e, lang e == L BRZ e.
Proof.
  (* in fact, we have just proven that lang is a coalgebra homomorphism, 
     so that it must coincide with L by finality *)
  intros e w. revert e. induction w; intro e.
  - apply lang_eps_lang.
  - simpl L. rewrite <-IHw. symmetry. apply Lang_der.
Qed.

Corollary Brzozowski e f: e ~ f <-> e ≡ f.
Proof.
  rewrite 2L_BRZ.
  apply bisimilarity_is_language_equivalence.
Qed.

(** ** Proving laws by coinduction
    
now that we have an automaton on regular expressions, we can prove laws by coinduction

  *)

(* TOTHINK:
   could be nicer to state the following lemmas with ≡
   + starting the proofs with [apply Brzozowski] make it clear that we choose to use coinduction and Brzozowski's derivatives
   - but then the lemmas are harder to use in other coinductive proofs
 *)
Lemma plsA: forall e f g, e+(f+g) ~ (e+f)+g.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.orb_assoc.
  - intro. apply H.

  (* for laws about +, this is not necessarily the shortest path... *)
  Restart.
  intros. rewrite Brzozowski. apply cupA. 
Qed.

Lemma plsC: forall e f, e+f ~ f+e.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.orb_comm.
  - intro. apply H.

  Restart.
  intros. rewrite Brzozowski. apply cupC. 
Qed.

Lemma plsI: forall e, e+e ~ e.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.orb_diag.
  - intro. apply H.

  Restart.
  intros. rewrite Brzozowski. apply cupI. 
Qed.

Lemma pls0x: forall x, 0 + x ~ x.
Proof. now coinduction R H; cbn. Qed.
  
Lemma plsx0 x: x + 0 ~ x.
Proof. now rewrite plsC, pls0x. Qed.   

(** addition corresponds to a compatible function 
    and preserves elements of the final chain of [b BRZ] *)
#[export] Instance pls_chain: forall {R: Chain (b _)}, Proper (`R ==> `R ==> `R) pls.
Proof.
  apply (Proper_chain 2). 
  intros R HR x x' [Hx Hx'] y y' [Hy Hy'].
  split; cbn.
  - cbn in Hx, Hy. congruence.
  - intro. now apply HR. 
Qed.

Section s.
Context {R: Chain (b BRZ)}. 
#[export] Instance pls_Associative: Associative `R pls.
Proof. intros ???. now rewrite plsA. Qed.
#[export] Instance pls_Commutative: Commutative `R pls.
Proof. intros ??. now rewrite plsC. Qed.
#[export] Instance pls_Idempotent: Idempotent `R pls.
Proof. intros ?. now rewrite plsI. Qed.
#[export] Instance pls_Unit: Unit `R pls 0.
Proof. split; intro; now rewrite ?pls0x, ?plsx0. Qed.
End s.

Lemma dot0x: forall x, 0 · x ~ 0.
Proof.
  coinduction R H; split; cbn.
  - reflexivity.
  - intro. now rewrite 2H, plsI. 
Qed.

Lemma dotx0: forall x, x · 0 ~ 0.
Proof.
  coinduction R H; split; cbn.
  - now rewrite Bool.andb_comm. 
  - intro. now rewrite 2H, plsI. 
Qed.

Lemma dot1x: forall x, 1 · x ~ x.
Proof.
  coinduction R H; split; cbn.
  - reflexivity.
  - intro. now rewrite dot0x, pls0x. 
Qed.
  
Lemma dotx1: forall x, x · 1 ~ x.
Proof.
  coinduction R H; split; cbn.
  - now rewrite Bool.andb_comm. 
  - intro. now rewrite dotx0, plsx0.
Qed.

Lemma dotorbx b c g: (orb b c)·g ~ b·g + c·g.
Proof.
  case b; case c; simpl; rewrite ?dot1x, ?dot0x.
  aac_reflexivity. 
  aac_reflexivity. 
  aac_reflexivity. 
  aac_reflexivity. 
Qed.

Lemma dotandbx b c g: (andb b c)·g ~ b·(c·g).
Proof.
  symmetry. case b; simpl.
  apply dot1x.
  now rewrite 2dot0x. 
Qed.

Lemma dotplsx: forall e f g, (e+f)·g ~ e·g + f·g.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.andb_orb_distrib_l.
  - intro. rewrite H, dotorbx. aac_reflexivity. 
Qed.

Lemma dotxpls: forall e f g, g·(e+f) ~ g·e + g·f.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.andb_orb_distrib_r.
  - intro. rewrite 2H. aac_reflexivity. 
Qed.

Lemma dotA: forall e f g, e·(f·g) ~ (e·f)·g.
Proof.
  coinduction R H; split; cbn.
  - apply Bool.andb_assoc.
  - intro.
    rewrite dotplsx, dotxpls, dotandbx.
    rewrite 2H. aac_reflexivity. 
Qed.

(** context function associated to concatenation is below the companion 
    and preserves elements of the final chain of [b BRZ] *)
#[export] Instance dot_chain: forall {R: Chain (b _)}, Proper (`R ==> `R ==> `R) dot.
Proof.
  apply (Proper_chain 2). 
  intros R HR x x' [Hx Hx'] y y' Hy.
  split.
  - destruct Hy as [Hy _]; cbn in *; congruence.
  - intro. cbn in Hx, Hx'. cbn.
    now rewrite Hx, (proj2 Hy), Hx', Hy.
Qed.  

Section s.
Context {R: Chain (b BRZ)}. 
#[export] Instance dot_Associative: Associative `R dot.
Proof. intros ???. now rewrite dotA. Qed.
#[export] Instance dot_Unit: Unit `R dot 1.
Proof. split; intro. now rewrite dot1x. now rewrite dotx1. Qed.
End s.

(** a helper lemma *)
Lemma kill_b (b: bool) e: e + b·e ~ e.
Proof.
  case b; cbn.
  rewrite dot1x. aac_reflexivity. 
  rewrite dot0x. aac_reflexivity. 
Qed.

(** more advanced laws, handled by coinduction + algebraic reasoning 
    unfortunately, not as convenient as one could hope
 *)
Goal forall e f, (e+f)^* ~ f^*·(e·f^*)^*.
Proof.
  intros; coinduction R H; split; cbn.
  - reflexivity. 
  - intro. rewrite H, !dotplsx.
    aac_rewrite (kill_b (eps e)) in_right.
    aac_reflexivity.
Qed.

Lemma str_unfold e: e^* ~ 1 + e·e^*.
Proof.
  coinduction R _. next.
  rewrite pls0x.
  aac_rewrite (kill_b (eps e)) in_right.
  reflexivity. 
Qed.

Goal forall e f, (e·f)^*·e ~ e·(f·e)^*.
Proof.
  intros; coinduction R H; split; cbn.
  - now rewrite Bool.andb_comm. 
  - intro. case eps. case eps.
    all: rewrite ?dot1x, ?dot0x.
    all: aac_rewrite H.
    (* need more lemmas *)
    -- rewrite 2dotplsx. aac_normalise. 
       rewrite str_unfold at 3.
       rewrite dotxpls. aac_reflexivity. 
    -- rewrite dotplsx. 
       rewrite str_unfold at 3.
       rewrite dotxpls. aac_reflexivity. 
    -- rewrite str_unfold at 2.
       rewrite dotxpls. aac_reflexivity. 
Qed.


(** proving `concrete' laws is slightly easier, but there is still quite a lot of bookkeeping *)
Module C0.
Notation a := (var 0).
Notation b := (var 1).
Notation c := (var 2).
Ltac letters :=
  repeat match goal with |- context[Nat.eqb ?a _] => is_var a; destruct a; cbn end.

Goal (a+b)^* ~ a^*·(b·a^*)^*.
Proof.
  coinduction R H. next. letters. 
  - aac_normalise. rewrite dot0x, H. aac_reflexivity.
  - aac_normalise. rewrite 2dot0x, H. aac_reflexivity.
  - aac_normalise. rewrite !dot0x. now aac_rewrite dot0x in_right.
Qed.

Goal (a·b)^*·a ~ a·(b·a)^*.
Proof.
  coinduction R H. next. letters; aac_normalise; rewrite !dot0x.
  - accumulate H'. next. letters; aac_normalise; rewrite !dot0x. 
    -- aac_reflexivity. 
    -- now aac_normalise.
    -- aac_normalise. now rewrite dot0x.
  - aac_reflexivity. 
  - clear a. aac_normalise. now rewrite dot0x.
Qed.
                
End C0.



(** ** Antimirov' partial derivatives 
    
    A definition of a non-deterministic automaton on regular expressions, 
    with finitely many reachable states from every state.

 *)

(** reversed product *)
Definition pdot f e := dot e f. 
Arguments pdot _ _/.

(** Antimirov' partial derivatives *)
Fixpoint pder (e: regex) (a: A): list regex :=
  match e with
  | 0 | 1 => []
  | var b => if Nat.eqb a b then [1] else []
  | e+f => pder e a ++ pder f a
  | e·f => (if eps e then pder f a else []) ++ map (pdot f) (pder e a)
  | e^* => map (pdot (e ^*)) (pder e a) 
  end.

(** non-deterministic automaton associated to Antimirov derivatives *)
Canonical Structure ANT := {| NA.states := regex; NA.out := eps; NA.next := pder |}.


(** summing a list of regular expressions *)
Definition sum := fold_right pls zer.

Lemma sum_app h k: sum (h++k) ~ sum h + sum k.
Proof.
  induction h; simpl. aac_reflexivity.
  rewrite IHh. aac_reflexivity.
Qed.
Lemma sum_mapdot e h: sum (map (pdot e) h) ~ sum h · e.
Proof.
  induction h; simpl. now rewrite dot0x.
  now rewrite IHh, dotplsx.
Qed.

(** key lemma about Antimirov' partial derivatives *)
Lemma pder_der e a: der e a ~ sum (pder e a).
Proof.
  induction e; simpl.
  - reflexivity.
  - reflexivity.
  - case Nat.eqb; simpl. aac_reflexivity. aac_reflexivity. 
  - now rewrite IHe1, IHe2, sum_app.
  - rewrite IHe1, IHe2. case eps; simpl.
    rewrite sum_app, sum_mapdot. aac_reflexivity.
    rewrite dot0x, sum_mapdot. aac_reflexivity.
  - now rewrite sum_mapdot, IHe. 
Qed.

(** language of a list of regular expressions  *)
Definition plang h w := exists x, In x h /\ lang x w.
Lemma plang_nil: plang [] == lang_zer.
Proof. firstorder. Qed.
Lemma plang_cons a q: plang (a::q) == lang_pls (lang a) (plang q).
Proof. firstorder congruence. Qed.
Lemma plang_lang h: plang h == lang (sum h). 
Proof.
  induction h.
  - apply plang_nil.
  - rewrite plang_cons. now apply cup_weq.
Qed.

(** counter-part of [Lang_der], for partial derivatives *)
Corollary Lang_pder e a: plang (pder e a) == lang_der (lang e) a.
Proof.
  rewrite plang_lang, <-Lang_der.
  apply Brzozowski. now rewrite pder_der.
Qed.

(** the language of an expression coincides with 
    the language of this expression in Antimirov' automaton *)
Theorem NL_ANT: forall e, lang e == NL ANT e.
Proof.
  (* in fact, we have just proven that lang is a coalgebra homomorphism, 
     so that it must coincide with L by finality *)
  intros e w. revert e. induction w; intro e.
  - apply lang_eps_lang.
  - simpl NL. setoid_rewrite <-IHw. symmetry. apply Lang_pder.
Qed.

Corollary Antimirov e f: [e] ~ [f] <-> e ≡ f.
Proof.
  rewrite 2NL_ANT, <-2L_det_single.
  apply bisimilarity_is_language_equivalence.
Qed.


(** at this point we can use Antimirov' automaton to prove laws by coinduction *)
Module C1.
Import C0.

Goal a^* ≡ 1+a·a^*.
Proof.
  apply Antimirov.
  coinduction R H. next. letters. 2: reflexivity. 
  accumulate H'. next. letters. assumption. reflexivity. 
Qed.

Goal (a·b)^*·a ≡ a·(b·a)^*.
Proof.
  apply Antimirov. 
  coinduction R ?. next. letters; trivial.
  accumulate ?. next. letters; trivial.
  accumulate ?. next. letters; trivial.
Qed.

(* a first attempt at automation *)
Ltac explore :=
  apply Antimirov;
  coinduction R ?;
  repeat (next; letters; trivial; accumulate ?).

Goal a^* ≡ 1+a·a^*.
Proof. explore. Qed.

Goal a^* ≡ 1+a^*·a.
Proof. explore. Qed.

Goal a^* ≡ a^*·a^*.
Proof.
  (* here [explore] loops forever... *)
  apply Antimirov.
  coinduction R ?; next; letters; trivial.
  accumulate ?; next; letters; trivial.
  accumulate ?; next; letters; trivial.
  accumulate ?; next; letters; trivial.
  (* we need to remove duplicates to get a finite automaton *)
Abort.  

End C1.



(** ** Sorting lists of regular expressions, removing duplicates

this will allow us to mimic finite sets with lists more faithfully
*)

(** comparing regular expressions, syntactically *)
Notation lex c d := match c with Eq => d | _ => c end.
Fixpoint compare e f :=
  match e,f with
  | 0,0 => Eq
  | 0,_ => Lt
  | _,0 => Gt
  | 1,1 => Eq
  | 1,_ => Lt
  | _,1 => Gt
  | var a,var b => Nat.compare a b
  | var _,_ => Lt
  | _,var _ => Gt
  | e+e',f+f' => lex (compare e f) (compare e' f')
  | _+_,_ => Lt
  | _,_+_ => Gt
  | e·e',f·f' => lex (compare e f) (compare e' f')
  | _·_,_ => Lt
  | _,_·_ => Gt
  | e^*,f^* => compare e f
  end.

(** weak specification: [compare] only equates equal values *)
Lemma lex_eq c d: lex c d = Eq -> c=Eq /\ d=Eq.
Proof. destruct c; auto; discriminate. Qed.
Lemma compare_eq: forall e f, compare e f = Eq -> e=f.
Proof.
  induction e; destruct f; cbn; try discriminate.
  - reflexivity.
  - reflexivity.
  - intro H. apply Nat.compare_eq in H. congruence.
  - intro H. apply lex_eq in H as [? ?]. f_equal; auto.
  - intro H. apply lex_eq in H as [? ?]. f_equal; auto.
  - intro. f_equal; auto.
Qed.

(** inserting in a sorted list *)
Fixpoint insert x l :=
  match l with
  | [] => [x]
  | y::q => match compare x y with
          | Lt => x::l
          | Eq => l
          | Gt => y::insert x q
          end
  end.
(** weak specification: we just preserve the semantics *)
Lemma Insert x l: insert x l ~ [x]++l.
Proof.
  induction l as [|y q IH]; cbn.
  - reflexivity.
  - case_eq (compare x y); intro E.
    -- apply compare_eq in E as <-. fold_app. aac_reflexivity.
    -- reflexivity.
    -- fold_app. rewrite IH. aac_reflexivity. 
Qed.

(** sorting a list *)
Fixpoint sort l :=
  match l with
  | [] => []
  | x::l => insert x (sort l)
  end.
(** weak specification: we just preserve the semantics *)
Lemma Sort (l: list regex): sort l ~ l.
Proof.
  induction l as [|y q IH]; cbn.
  - reflexivity.
  - now rewrite Insert, IH. 
Qed.

Corollary reduce (R: Chain (b _)) h k: `R (sort h) (sort k) -> `R h k.
Proof. now rewrite 2Sort. Qed.

  

Module C2.
Export C0.


Goal a^* ≡ a^*·a^*.
Proof.
  apply Antimirov.
  coinduction R ?; next; letters; trivial.
  accumulate ?; next; letters; trivial.
  (* by using lemma [reduce], we can sort or lists an remove duplicates *)
  apply reduce.
  cbn.
  assumption.
Qed.  


(** automation tactic, via Antimirov' automaton *)
Ltac explore :=
  apply Antimirov;
  coinduction R ?;
  repeat (next; letters; apply reduce; cbn; trivial; accumulate ?).

Goal (a·b)^*·a ≡ a·(b·a)^*.
Proof. explore. Qed.

Goal a·(b·c) ≡ (a·b)·c.
Proof. explore. Qed.

Goal a·(b+c) ≡ a·b + a·c.
Proof. explore. Qed.

Goal a^* ≡ 1+a·a^*.
Proof. explore. Qed.

Goal a^* ≡ 1+a^*·a.
Proof. explore. Qed.

Goal a^* ≡ a^*·a^*.
Proof. explore. Qed.

Goal a^* ≡ a^*^*.
Proof. explore. Qed.

Goal a^* ≡ (1+a)·(a·a)^*.
Proof. explore. Qed.

Goal a^* ≡ (1+a+a·a)·(a·a·a)^*.
Proof. explore. Qed.

Goal (a+b)^* ≡ b^*·(a·b^*)^*.
Proof. explore. Qed.

Goal (a^*·b·a^*)^+ ≡ (a+b)^*·b·(a+b)^*.
Proof. explore. Qed.

(** Note: we could do equally well with Brzozowski's derivatives if we were defining a normalisation function on regular expressions to take care of simplifying units (1x=x, 0x=0) and removing duplicate terms in sums
 *)

End C2.

(** * Closure of equations under substitutions

  we prove that forall expressions e,f and substitution \sigma, 
  e ≡ f   implies   e\sigma ≡ f\sigma

  this makes it possible to prove universally quantified laws by resorting to concrete laws.
  for instance, we deduce \forall e f, (e·f)^*·e ≡ e·(f·e)^*
  from the law (a·b)^*·a ≡ a·(b·a)^* and the substitution a->e, b->f
 *)
Section subst.
 Variable s: A -> regex.

 (** substituting expressions for variables in a given expression *)
 Fixpoint subst (e: regex) :=
   match e with
   | 0 => 0
   | 1 => 1
   | var a => s a
   | e+f => subst e + subst f
   | e·f => subst e · subst f
   | e^* => subst e^*
   end.
 (** in a given word *)
 Fixpoint wsubst (w: word) :=
   match w with
   | [] => 1
   | a::w => s a · wsubst w
   end.
 Lemma wsubst_app u v: wsubst (u++v) ≡ wsubst u · wsubst v.
 Proof.
   apply Brzozowski.
   induction u; cbn. aac_reflexivity.
   rewrite IHu. aac_reflexivity. 
 Qed.

 (** generic properties of supremums *)
 Lemma sup_sup_all I J (f: I -> language) (g: J -> I -> Prop):
   sup' (sup' top g) f == sup' top (fun j => sup' (g j) f).
 Proof.
   apply antisym. apply sup_spec.
   intros i [j gj]. apply eleq_xsup with j; trivial. eapply eleq_xsup; eauto.
   apply sup_spec. intros j _. apply sup_spec. intros i H. eapply eleq_xsup; eauto. 
   now exists j. 
 Qed.

 (** a function h which is a homomorphism (useful to prove Proposition [lang_subst] below) *)
 Let h L := sup' L (fun w => lang (wsubst w)).
 Lemma h_one: h lang_one == lang_one.
 Proof. unfold h. now setoid_rewrite sup_single. Qed.
 Lemma h_dot L K: h (lang_dot L K) == lang_dot (h L) (h K).
 Proof.
   intro w; split.
     -- intros [z (u&v&Hu&Hv&->) H]. rewrite (wsubst_app _ _ _) in H.
        destruct H as (u'&v'&Hu'&Hv'&->). exists u', v'. split; [|split]; trivial.
        eexists; eauto. 
        eexists; eauto.
     -- intros (u&v&Hu&Hv&->).
        destruct Hu as [u' Hu' uu']. 
        destruct Hv as [v' Hv' vv'].
        exists (u'++v'). now exists u', v'. rewrite (wsubst_app _ _ _). eexists; eauto.
 Qed.
 Lemma h_itr L i: h (lang_itr L i) == lang_itr (h L) i.
 Proof.
   induction i; simpl lang_itr. apply h_one.
   now rewrite h_dot, IHi.
 Qed.   
 Lemma h_str L: h (lang_str L) == lang_str (h L).
 Proof.
   unfold h, lang_str. rewrite sup_sup_all.
   apply sup_weq. reflexivity.
   intro. apply h_itr. 
 Qed.

 (** the language of a substituted expression can be expressed in terms of the language of the starting expressions *)
 Proposition lang_subst e: lang (subst e) == sup' (lang e) (fun w => lang (wsubst w)).
 Proof.
   induction e; simpl subst.
   - now rewrite sup_bot. 
   - symmetry. apply h_one. 
   - setoid_rewrite sup_single. simpl wsubst. apply Brzozowski. now rewrite dotx1.
   - simpl lang. unfold lang_pls. rewrite sup_cup. now apply cup_weq.
   - etransitivity. 2: symmetry; apply h_dot.
     now apply lang_dot_weq. 
   - etransitivity. 2: symmetry; apply h_str.
     now apply lang_str_weq. 
 Qed.
 (** closure under substitution follows *)
 Theorem subst_eq e f: e ≡ f -> subst e ≡ subst f.
 Proof. intro H. rewrite 2lang_subst. now rewrite H. Qed.
 
 (** open question: can we get the following stronger result? *)
 Conjecture subst_chain: forall {R: Chain (b _)}, Proper (`R ==> `R) subst.
 (*
 Proof.                         
   apply (Proper_chain 1).
   intros R HR e f H. split.
   (* not clear at all *)
 *)

 (** [subst_eq] follows from the conjecture: *)
 Corollary subst_eq' e f: e ≡ f -> subst e ≡ subst f.
 Proof. rewrite <-2Brzozowski. apply subst_chain. Qed.
End subst.


(* the above theorem [subst_eq] makes it possible to prove universally 
   quantified equations by resorting to concrete equations *)
Module C3.
Import C2.

Goal forall e f, (e^*·f·e^*)^+ ≡ (e+f)^*·f·(e+f)^*.
Proof.
 intros e f.
 (* 0 is for letter a, 1 for letter b *)
 set (s i := match i with O => e | _ => f end).
 change (subst s ((a^*·b·a^*)^+) ≡ subst s ((a+b)^*·b·(a+b)^*)).
 apply subst_eq.
 explore.                   
Qed.

End C3.
