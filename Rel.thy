theory Rel
imports Main Logic begin

(*
(** * Rel: Properties of Relations *)
(* Version of 3/26/2010 *)

(** This short chapter develops some basic definitions that will be
    needed when we come to working with small-step operational
    semantics in Smallstep.v.  It can be postponed until just before
    Smallstep.v, but it is also a good source of good exercises for
    developing facility with Coq's basic reasoning facilities, so it
    may also be useful to look at it just after Logic.v. *)

Require Export Logic.

(* ######################################################### *)
(** * Relations *)

(** A _relation_ is just a parameterized proposition.  As you know
    from your undergraduate discrete math course, there are a lot of
    ways of discussing and describing relations _in general_ -- ways
    of classifying relations (are they reflexive, transitive, etc.),
    theorems that can be proved generically about classes of
    relations, constructions that build one relation from another,
    etc.  Let us pause here to review a few that will be useful in
    what follows. *)

(** A relation _on_ a set [X] is a proposition parameterized by two
    [X]s -- i.e., it is a logical assertion involving two values from
    the set [X].  *)

Definition relation (X: Type) := X->X->Prop.
*)

type_synonym 'a rel = "'a \<Rightarrow> 'a \<Rightarrow> bool"

(* 
(** Somewhat confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance. To maintain
    consistency with the library, we will do the same.  So, henceforth
    the Coq identifier [relation] will always refer to a binary
    relation between some set and itself, while the English word
    "relation" can refer either to the specific Coq concept or the
    more general concept of a relation between any number of possibly
    different sets.  The context of the discussion should always make
    clear which is meant. *)

(* ######################################################### *)
(** * Properties *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., if [R x
    y1] and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 
*)

definition partialfunction :: "'a rel \<Rightarrow> bool" where
"partialfunction r = (\<forall> x y1 y2. r x y1 \<longrightarrow> r x y2 \<longrightarrow> y1 = y2)"

(* 
(** For example, the [next_nat] relation defined in Logic.v is a
    partial function. *)

Theorem next_nat_partial_function : 
   partial_function next_nat.
Proof. 
  unfold partial_function.
  intros x y1 y2 P Q. 
  inversion P. inversion Q.
  reflexivity.  Qed.
*)
inductive next_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
nn : "next_nat n (Suc n)"

theorem "partialfunction next_nat"
apply (unfold partialfunction_def, intro allI impI)
apply (erule next_nat.cases)
apply (erule next_nat.cases)
by simp

theorem "partialfunction next_nat"
by (auto simp: partialfunction_def elim: next_nat.cases)
  

theorem "\<not> (partialfunction le)"
unfolding partialfunction_def
by auto

theorem "\<not> (partialfunction le)"
unfolding partialfunction_def
apply clarsimp
apply (rule_tac x="(Suc 0)" in exI)
apply (rule_tac x="Suc (Suc 0)" in exI)
apply (rule conjI)
apply (rule le_S)
apply (rule le_n)
apply (rule_tac x="Suc 0" in exI)
apply (rule conjI)
apply (rule le_n)
by simp

(* we use clarsimp as a weaker auto, to do basic intros and simplifications of the proof and get it into an interesting state.  clarsimp works only on the 
current goal. *)

(* 
(** However, the [<=] relation on numbers is not a partial function.

    This can be shown by contradiction.  In short: Assume, for a
    contradiction, that [<=] is a partial function.  But then, since
    [0 <= 0] and [0 <= 1], it follows that [0 = 1].  This is nonsense,
    so our assumption was contradictory. *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply H with 0. 
     apply le_n. 
     apply le_S. apply le_n. 
  inversion Nonsense.   Qed.

(** **** Exercise: 2 stars, optional *)
(** Show that the [total_relation] defined in Logic.v is not a partial
    function. *)

*)


(* 

(* SOLUTION: *)
Theorem total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold partial_function. intros H. 
  assert (0 = 1) as Nonsense.
    apply H with 0. apply tot. apply tot.
  inversion Nonsense. Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Show that the [empty_relation] defined in Logic.v is a partial
    function. *)

(* SOLUTION: *)
Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof. 
  unfold partial_function. intros n y1 y2 H1 H2. inversion H1.  Qed.
(** [] *)
*)

(* 
(** A _reflexive_ relation on a set [X] is one that holds for every
    element of [X]. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
*)

definition reflexive :: "'a rel \<Rightarrow> bool" where
"reflexive r \<equiv> (\<forall> a. r a a)"

declare reflexive_def [simp]

theorem "reflexive le"
by (auto intro: le.intros)

(* 
Theorem le_reflexive :
  reflexive le.
Proof. 
  unfold reflexive. intros n. apply le_n.  Qed.

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
*)

definition transitive :: "'a rel \<Rightarrow> bool" where
"transitive r \<equiv> (\<forall> a b c. r a b \<longrightarrow> r b c \<longrightarrow> r a c)"

lemma transitiveE : "transitive r \<Longrightarrow> r a b \<Longrightarrow> r b c \<Longrightarrow> r a c"
apply (unfold transitive_def)
by fast

lemma transitiveI : "(!! a b c. r a b \<Longrightarrow> r b c \<Longrightarrow> r a c) \<Longrightarrow> transitive r"
apply (unfold transitive_def)
by fast

(* 
Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.  Qed.
*)

theorem le_trans : "transitive le"
proof (rule transitiveI)
  fix a b c 
  assume H1 : "le a b"
  assume H2 : "le b c"

  show "le a c" using H2 H1 
           apply (induct b c rule: le.induct)
           by (auto intro: le.intros)
qed

lemma le_trans' : "\<lbrakk>le x y; le y z\<rbrakk> \<Longrightarrow> le x z"
apply (subgoal_tac "transitive le")
apply (erule transitiveE)
apply simp
apply simp
apply (rule le_trans)
done

(* 
Theorem lt_trans:
  transitive lt.
Proof. 
  unfold lt. unfold transitive. 
  intros n m o Hnm Hmo.
  apply le_S in Hnm. 
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, optional *)
(** We can also prove [lt_trans more] laboriously by induction,
    without using le_trans.  Do this.*)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* SOLUTION: *)
    Case "le_m". apply le_S in Hnm. apply Hnm.
    Case "le_S". apply le_S in IHHm'o. apply IHHm'o.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Prove the same thing again by induction on [o]. *)
*)

(* 
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* SOLUTION: *)
    Case "o = 0". inversion Hmo.
    Case "o = S o'". inversion Hmo.
      SCase "le_n". rewrite -> H0 in Hnm. apply le_S in Hnm. apply Hnm.
      SCase "le_S". apply IHo' in H0. apply le_S in H0. apply H0.  Qed.
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. 
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.
*)

theorem "le (Suc n) m \<Longrightarrow> le n m"
proof -
  fix n m
  assume H1: "le (Suc n) m"
  have L1: "le n (Suc n)" by (auto intro: le.intros)
  show "le n m" using transitiveE [OF le_trans, OF L1 H1] .
qed

(* 

(** **** Exercise: 1 star, optional *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* SOLUTION: *)
  intros n m H. inversion H.
  Case "le_n".
    apply le_n.
  Case "le_S".
    apply le_Sn_le. apply H1.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (le_Sn_n_inf) *)
(** Provide an informal proof of the following theorem:
 
    Theorem: For every [n], [~(S n <= n)]
 
    A formal proof of this is an optional exercise below, but try
    the informal proof without doing the formal proof first
 
    Proof:
    (* SOLUTION: *)
    By induction on [n].
 
    - Suppose first that [n = 0].  Then we must show [~(S 0 <=
      0)].  But this follows immediately from the definition of
      [<=], since neither [le_n] nor [le_S] can be used to prove
      [~(S 0 <= 0)].
 
    - Next, suppose [n = S n'] for some [n'] with [~(S n' <= n')].
      We must show [~(S n <= n)] -- that is, [~(S (S n') <= (S
      n'))].  Suppose, for a contradiction, that [S (S n') <= (S
      n')].  Then, by lemma [le_S_n], we have [S n' <= n'], which
      contradicts the IH.
        []
 *)

(** **** Exercise: 1 star, optional *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* SOLUTION: *)
  induction n as [| n'].
    Case "n = 0". intros H. inversion H.
    Case "n = S n'". intros H. unfold not in IHn'. apply IHn'.
      apply le_S_n. apply H.  Qed.
(** [] *)

(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)
*)

definition symmetric :: "'a rel \<Rightarrow> bool" where
"symmetric r \<equiv> (\<forall> a b. r a b \<longrightarrow> r b a)"



(* 
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
*)

lemma symmetricI : "(!! a b. r a b \<Longrightarrow> r b a) \<Longrightarrow> symmetric r"
apply (unfold symmetric_def)
by fast

lemma symmetricE : "symmetric r \<Longrightarrow> r a b \<Longrightarrow> r b a"
apply (unfold symmetric_def)
by fast

theorem le_not_symmetric : "\<not> (symmetric le)"
apply (rule notI)
apply (subgoal_tac "le 1 0")
apply (erule le.cases, auto)
by (erule symmetricE, rule le_S, rule le_n)

theorem "\<not> (symmetric le)"
apply (unfold symmetric_def, rule notI)
apply (drule spec [where x=0])
apply (drule spec [where x=1])
apply (drule mp)
apply (simp add: eval_nat_numeral, rule le_S, rule le_n)
apply (erule le.cases)
by (auto intro: le.intros)

theorem "\<not> (symmetric le)"
unfolding symmetric_def
proof
assume H: "\<forall>a b. le a b \<longrightarrow> le b a"
then have "le 0 (Suc 0)" and "le (Suc 0) 0" by auto
thus "False" by auto
qed

(* 
(** **** Exercise: 2 stars, optional *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* SOLUTION: *)
  unfold symmetric. intros H.
  assert (1 <= 0) as Nonsense. 
    Case "Proof of assertion.". apply H. apply le_S. apply le_n.
  inversion Nonsense.  Qed.
(** [] *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)
*)

definition antisymmetric :: "'a rel \<Rightarrow> bool" where
"antisymmetric r \<equiv> (\<forall> a b. r a b \<longrightarrow> r b a \<longrightarrow> a = b)"
(*
theorem "antisymmetric le"
apply (unfold antisymmetric_def, intro allI,
       induct_tac a, intro impI)
*)

(*
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, optional *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* SOLUTION: *)
  (* Here s a pretty proof due to Jianzhou Zhao: *)
  unfold antisymmetric. induction a as [| a'].
    Case "a = 0". intros b H1 H2. inversion H2. reflexivity.
    Case "a = S a'". intros b H1 H2. destruct b as [| b']. 
      SCase "b = 0". inversion H1.
      SCase "b = S b'". 
         apply le_S_n in H1.
         apply le_S_n in H2.
         apply IHa' in H1.
            rewrite H1. reflexivity.
            apply H2.  Qed.
  
(* An uglier way of getting there: *)
Theorem le_antisymmetric' : 
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a b Hab Hba.
  inversion Hab.
    Case "le_n". reflexivity.
    Case "le_S". inversion Hba.
      SCase "le_n". rewrite <- H1. symmetry. apply H0.
      SCase "le_S".
        rewrite <- H2 in H.
        rewrite <- H0 in H1.
        assert (S m0 <= m0) as bad.
          SSCase "Proof of assertion".
            apply le_trans with (b:=m).
              SSSCase "S m0 <= m". apply H.
              SSSCase "m <= m0". apply le_trans with (b:=S m).
                SSSSCase "m <= S m". apply le_S. apply le_n.
                SSSSCase "S m <= m0". apply H1.
        assert (~ (S m0 <= m0)) as L.
          SSCase "Proof of assertion". apply le_Sn_n.
        unfold not in L.
        apply L in bad. inversion bad.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof. 
  (* SOLUTION: *)
  intros.
  unfold lt in H.
  assert (S n <= S p).
    apply le_trans with m. apply  H. apply H0.
  apply le_S_n. assumption.  Qed.
  (** [] *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split. 
    Case "refl". apply le_reflexive.
    split. 
      Case "antisym". apply le_antisymmetric. 
      Case "transitive.". apply le_trans.  Qed.

(* ########################################################### *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

*)

inductive clos_refl_trans :: "'a rel \<Rightarrow> 'a rel" for R :: "'a rel" where
 rt_step [intro]: "R x y \<Longrightarrow> clos_refl_trans R x y" |
 rt_refl [intro]: "clos_refl_trans R x x" |
 rt_trans [trans]: "\<lbrakk>clos_refl_trans R x y; clos_refl_trans R y z\<rbrakk> \<Longrightarrow> clos_refl_trans R x z"

(* 

Tactic Notation "rt_cases" tactic(first) tactic(c) :=
  first;
  [ c "rt_step" | c "rt_refl" | c "rt_trans" ].

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)
*)
theorem next_nat_closure_is_le : "(le n m) = (clos_refl_trans next_nat n m)"
apply (rule iffI)
apply (induct n m rule: le.induct)
apply (rule rt_refl)
apply (rule rt_trans, assumption)
apply (rule rt_step)
apply (rule nn)
apply (induct n m rule: clos_refl_trans.induct)
apply (erule next_nat.cases, simp)
apply (rule le_S)
apply (rule le_n)
apply (rule le_n)
by (rule le_trans')



(* 
Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H. 
         apply rt_refl.
         apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H.  rt_cases (induction H) SCase.
        SCase "rt_step".  inversion H. apply le_S.  apply le_n. 
        SCase "rt_refl". apply le_n. 
        SCase "rt_trans". 
           apply le_trans with y.  
           apply IHclos_refl_trans1. 
           apply IHclos_refl_trans2.  Qed.

(** The above definition of reflexive, transitive closure is
    natural -- it says, explicitly, that the reflexive and transitive
    closure of [R] is the least relation that includes [R] and that is
    closed under rules of reflexivity and transitivity.  But it turns
    out that this definition is not very convenient for doing
    proofs -- the "nondeterminism" of the rt_trans rule can sometimes
    lead to tricky inductions.
 
    Here is a more useful definition... *)

Inductive refl_step_closure {X:Type} (R: relation X) 
                            : X -> X -> Prop :=
  | rsc_refl  : forall (x : X),
                 refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.
*)

inductive refl_step_closure :: "'a rel \<Rightarrow> 'a rel" for R :: "'a rel" where
rsc_refl [intro]: "refl_step_closure R x x" |
rsc_step [intro]: "\<lbrakk>R x y; refl_step_closure R y z\<rbrakk> \<Longrightarrow> refl_step_closure R x z" 

(* 
(** This new definition "bundles together" the [rtc_R] and [rtc_trans]
    rules into the single rule step.  The left-hand premise of this
    step is a single use of [R], leading to a much simpler induction
    principle.
 
    Before we go on, we should check that the two definitions do
    indeed define the same relation...
    
    First, we prove two lemmas showing that [rsc] mimics the behavior
    of the two "missing " [rtc] constructors.  *)

Tactic Notation "rsc_cases" tactic(first) tactic(c) :=
  first;
  [ c "rsc_refl" | c "rsc_step" ].
*)

lemma "r x y \<Longrightarrow> refl_step_closure r x y"
by auto

theorem rsc_R : "r x y \<Longrightarrow> refl_step_closure r x y"
apply (rule rsc_step)
apply assumption
apply (rule rsc_refl)
done

(* 
Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.   Qed.

*)

theorem rsc_trans : "\<lbrakk>refl_step_closure r x y; refl_step_closure r y z\<rbrakk> \<Longrightarrow>
                     refl_step_closure r x z"
apply (induct x y rule: refl_step_closure.induct)
apply assumption
by (rule rsc_step)

(* 

(** **** Exercise: 2 stars, optional (rsc_trans) *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* SOLUTION: *)
  intros X R x y z G H.
  rsc_cases (induction G) Case.
    Case "rsc_refl". assumption.
    Case "rsc_step". 
      apply rsc_step with y. assumption. 
      apply IHG. assumption.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide : 
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* SOLUTION: *)
  intros X R x y.
  unfold iff. apply conj.
    Case "->".
      intros H. rt_cases (induction H) SCase.
        SCase "rt_step".
          apply rsc_R.  assumption.
        SCase "rt_refl".
          apply rsc_refl.
        SCase "rt_trans".
          apply rsc_trans with y. assumption. assumption.
    Case "<-".
      intros H. rsc_cases (induction H) SCase.
        SCase "rsc_refl". apply rt_refl.
        SCase "rsc_step". apply rt_trans with y. apply rt_step. 
          assumption. apply IHrefl_step_closure.  Qed. 
(** [] *)
*)

end