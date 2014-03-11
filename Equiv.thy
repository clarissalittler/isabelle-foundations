theory Equiv 
imports Main Imp begin

(* (** * Equiv: Program Equivalence *)
(* Version of 4/29/2010 *)

Require Export Imp.

(** *** Some general advice for the homework

      - We've tried to make sure that most of the Coq proofs we ask
        you to do are similar to proofs that we've provided.  Before
        starting to work on the homework problems, take the time to
        work through our proofs (both informally, on paper, and in
        Coq) and make sure you understand them in detail.  This will
        save you a lot of time.

      - Here's another thing that will save a lot of time.  The Coq
        proofs we're doing now are sufficiently complicated that it is
        more or less impossible to complete them simply by "following
        your nose" or random hacking.  You need to start with an idea
        about why the property is true and how the proof is going to
        go.  The best way to do this is to write out at least a sketch
        of an informal proof on paper -- one that intuitively
        convinces you of the truth of the theorem -- before starting
        to work on the formal one.

      - Use automation to save work!  Some of the proofs in this
        chapter's exercises are pretty long if you try to write out
        all the cases explicitly.  *)

(* ####################################################### *)
(** * Behavioral equivalence *)

(** In the last chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    it was very easy to define what it _means_ for a program
    transformation to be correct: it should always yield a program
    that evaluates to the same number as the original.

    To talk about the correctness of program transformations in the
    full Imp language, we need to think about the role of variables
    and the state. *)

(* ####################################################### *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s, the definition we want is clear.  We say
    that two [aexp]s or [bexp]s are _behaviorally equivalent_ if they
    evaluate to the same result _in every state_. *)
 
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state), 
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state), 
    beval st b1 = beval st b2.
*)

definition aequiv :: "aexp' \<Rightarrow> aexp' \<Rightarrow> bool" where
"aequiv a a' \<equiv> \<forall> st. aeval' st a = aeval' st a'"

definition bequiv :: "bexp' \<Rightarrow> bexp' \<Rightarrow> bool" where
"bequiv b b' \<equiv> \<forall> st. beval' st b = beval' st b'"

(* 
(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are run in the
    same initial state," because some commands (in some starting
    states) don't terminate in any final state at all!  What we need
    instead is this: two commands are behaviorally equivalent if, for
    any given starting state, they either both diverge or both
    terminate in the same final state. *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st':state), 
    (c1 / st ==> st') <-> (c2 / st ==> st').
*)

definition cequiv :: "com \<Rightarrow> com \<Rightarrow> bool" where
"cequiv c c' \<equiv> \<forall> st st'. ceval c st st' \<longleftrightarrow> ceval c' st st'"

ML {* val setup_tac = (unfold_tac [@{thm cequiv_def},
                                   @{thm aequiv_def},
                                   @{thm bequiv_def}]
                                  @{simpset}) *}

(* 



(* ####################################################### *)
(** ** Examples *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  unfold aequiv. intros st. simpl.
  apply minus_diag.  
Qed.
*)

theorem "aequiv (AMinus' (AId' X) (AId' X)) (ANum' 0)"
by (simp add: aequiv_def)

(* 
Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue. 
Proof. 
  unfold bequiv. intros. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** Let's start by looking at some trivial command transformations involving SKIP *)

Theorem skip_left: forall c,
  cequiv 
     (SKIP; c) 
     c.
Proof. 
  unfold cequiv. intros c st st'.
  split; intros H.
  Case "->". 
    inversion H. subst. 
    inversion H2. subst. 
    assumption.
  Case "<-". 
    apply E_Seq with st.
    apply E_Skip. 
    assumption.  
Qed.
*)

lemma skip_ident1 : "ceval SKIP st st' \<Longrightarrow> st = st'"
apply (erule ceval.cases)
by auto


lemma skip_ident2 : "ceval SKIP st st' \<Longrightarrow> st' = st"
apply (erule ceval.cases)
by auto

lemma skip_left : "cequiv (SKIP ;; c) c"
apply (simp add: cequiv_def)
apply (intro allI iffI)
apply (erule ceval.cases)
  apply auto
  proof -
  fix sta st'a st''
  assume H1: "ceval SKIP sta st'a"
  assume H2: "ceval c st'a st''"
  have L1: "sta = st'a" using H1 by (simp add: skip_ident1)
  have L2: "ceval c sta st''" using H2 L1 by simp
  show "ceval c sta st''" using L2 by simp
 next
 fix st st'
 assume H1: "ceval c st st'"
 have L1: "ceval SKIP st st" by (rule ceval.intros)
 show "ceval (SKIP ;; c) st st'" using H1 L1 by (auto intro: ceval.intros)
qed

theorem skip_right : "cequiv (c ;; SKIP) c"
proof (unfold cequiv_def, intro allI iffI, erule ceval.cases, auto)
fix sta st'a st''
 assume H1 : "ceval c sta st'a"
 assume H2 : "ceval SKIP st'a st''"
 have L1 : "st'a = st''" using H2 by (simp add: skip_ident1)
 show "ceval c sta st''" using H1 L1 by simp
next
 fix st st'
 assume H1 : "ceval c st st'"
 have L1 : "ceval SKIP st' st'" by (rule ceval.intros)
 show "ceval (c ;; SKIP) st st'" using H1 L1 by (rule ceval.intros)
qed

(* CL:  Question!  So the above proofs are a little longer
        than their equivalents in Coq, but I think that's
        just because inversion in Coq automatically wipes
        out contradictory goals while I need to call auto
        in Isabelle to do the same.  Is there a way
        to make these shorter? *)

(* 
(** **** Exercise: 2 stars *)
Theorem skip_right: forall c,
  cequiv 
    (c; SKIP) 
    c.
Proof. 
  (* SOLUTION: *)
  unfold cequiv. intros c st st'.
  split; intros H.
  Case "->". 
    inversion H. subst. 
    inversion H5. subst.
    assumption.
  Case "<-". 
    apply E_Seq with st'.
    assumption. apply E_Skip.  Qed. 
(** [] *)
*)

theorem "cequiv (IF BTrue' THEN c1 ELSE c2) c1"
by (unfold cequiv_def, 
    intro allI iffI, 
    erule ceval.cases, auto intro: ceval.intros)

(* 
(** We can also explore transformations that simplify [IFB] commands *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv 
    (IFB BTrue THEN c1 ELSE c2 FI) 
    c1.
Proof. 
  intros c1 c2. 
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** Of course, few programmers would be tempted to write a while loop
    whose guard is literally [BTrue].  A more interesting case is when
    the guard is _equivalent_ to true...

   _Theorem_: forall [b] [c1] [c2], if [b] is equivalent to [BTrue],
   then [IFB b THEN c1 ELSE c2 FI] is equivalent to [c1].

   _Proof_: 

     - (--->) We must show, for all [st] and [st'], that if [IFB b
       THEN c1 ELSE c2 FI / st ==> st'] then [c1 / st ==> st'].

       There are two rules that could have been used to show [IFB b
       THEN c1 ELSE c2 FI / st ==> st']: [E_IfTrue] and [E_IfFalse].

       - Suppose the rule used to show [IFB b THEN c1 ELSE c2 FI /
         st ==> st'] was [E_IfTrue].  We then have, by the premises of
         [E_IfTrue], that [c1 / st ==> st'].  This is exactly what we
         set out to prove.

       - Suppose the rule used to show [IFB b THEN c1 ELSE c2 FI /
         st ==> st'] was [E_IfFalse].  We then know that [beval st b =
         false] and [c2 / st ==> st'].

         Recall that [b] is equivalent to [BTrue], i.e. forall
         [st], [beval st b = beval st BTrue].  In particular, this
         means that [beval st b = true], since [beval st BTrue =
         true].  But this is a contradiction, since [E_IfFalse]
         requires that [beval st b = false].  We therefore conclude
         that the final rule could not have been [E_IfFalse].

     - (<---) We must show, for all [st] and [st'], that if [c1 / st
       ==> st'] then [IFB b THEN c1 ELSE c2 FI / st ==> st'].

       Since [b] is equivalent to [BTrue], we know that [beval st b] =
       [beval st BTrue] = [true].  Together with the assumption that
       [c1 / st ==> st'], we can apply [E_IfTrue] to derive [IFB b
       THEN c1 ELSE c2 FI / st ==> st'].  [] 

   Here is the formal version of this proof: *)
*)

theorem "bequiv b BTrue' \<Longrightarrow> cequiv (IF b THEN c1 ELSE c2) c1"
apply (unfold cequiv_def bequiv_def, intro iffI allI)
apply (erule ceval.cases)
by (auto intro: ceval.intros)

(* 
Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv 
       (IFB b THEN c1 ELSE c2 FI) 
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity.  Qed.

(* Similarly: *)
*)

theorem "bequiv b BFalse' \<Longrightarrow> cequiv (IF b THEN c1 ELSE c2) c2"
apply (unfold bequiv_def cequiv_def, intro iffI allI)
apply (erule ceval.cases)
by (auto intro: ceval.intros)


(* 
(** **** Exercise: 2 stars *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  (* SOLUTION: *)
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true (contradiction)".
      rewrite Hb in H5.
      inversion H5.
    SCase "b evaluates to false".
      assumption.
  Case "<-".
    apply E_IfFalse; try assumption.
    rewrite Hb. reflexivity.  Qed.
(** [] *)

(** For while loops, there is a similar pair of theorems: a loop whose
    guard is equivalent to [BFalse] is equivalent to [SKIP], while a
    loop whose guard is equivalent to [BTrue] is equivalent to [WHILE
    BTrue DO SKIP END] (or any other non-terminating program).  The
    first of these facts is easy. *)
*)

theorem "bequiv b BFalse' \<Longrightarrow> cequiv (WHILE b DO c END) SKIP"
proof (unfold bequiv_def cequiv_def, intro allI iffI,
       erule ceval.cases, auto intro: ceval.intros)
fix st st'
 assume H1 : "\<forall>st. \<not> beval' st b"
 assume H2 : "ceval SKIP st st'"
 have L1 : "st = st'" using H2 apply -
                               apply (erule ceval.cases)
                               by auto
 show "ceval (WHILE b DO c END) st st'" using H1 L1 
   by (auto intro: ceval.intros)
qed

(* 
Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof. 
  intros b c Hb. 
  unfold cequiv. split; intros.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_WhileLoop".
      rewrite Hb in H2. inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(** To prove the second fact, we need an auxiliary lemma stating that
    while loops whose guards are equivalent to [BTrue] never
    terminate:

    _Lemma_: If [b] is equivalent to [BTrue], then it cannot be the
    case that [(WHILE b DO c END) / st ==> st'].

    _Proof_: Suppose that [(WHILE b DO c END) / st ==> st'].  We show,
    by induction on a derivation of [(WHILE b DO c END) / st ==> st'],
    that this assumption leads to a contradiction.  

      - Suppose [(WHILE b DO c END) / st ==> st'] is proved using rule
        [E_WhileEnd].  Then by assumption [beval st b = false].  But
        this contradicts the assumption that [b] is equivalent to
        [BTrue].

      - Suppose [(WHILE b DO c END) / st ==> st'] is proved using rule
        [E_WhileLoop].  Then we are given the induction hypothesis
        that [(WHILE b DO c END) / st ==> st'] is contradictory, which
        is exactly what we are trying to prove!

      - Since these are the only rules that could have been used to
        prove [(WHILE b DO c END) / st ==> st'], the other cases of
        the induction are immediately contradictory. [] *)
*)

lemma while_true_nonterm : "bequiv b BTrue' \<Longrightarrow> \<not> (ceval (WHILE b DO c END) st st')"
apply auto

done
(* 
Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st ==> st' ).
Proof. 
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  (ceval_cases (induction H) Case);
    (* most rules don't apply, and we can rule them out by inversion *)
    inversion Heqcw; subst; clear Heqcw.

  Case "E_WhileEnd". (* contradictory -- b is always true! *)
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop". (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, optional (WHILE_true_nonterm_informal) *)
(** Explain what the lemma [WHILE_true_nonterm] means in English.

(* SOLUTION: *) [WHILE_true_nonterm] claims that if a [bexp] [b] is
   equivalent to [BTrue] (i.e., if [forall st, beval st b = true]),
   then it is not possible to construct a derivation [(WHILE b DO c
   END) / st ==> st'] for any [st], [st'], or [c].
   
   We can understand this lack of a derivation as nontermination: the
   reason a derivation can't be constructed is because the
   [E_WhileLoop] rule would need to be applied infinitely many times,
   and derivations are finite.
*)
(** [] *)

(** **** Exercise: 2 stars *)
(** You'll want to use [WHILE_true_nonterm] here... *)

*)
theorem "bequiv b BTrue' \<Longrightarrow>
         cequiv (WHILE b DO c END)
                (WHILE BTrue' DO c END)"
proof (unfold cequiv_def, intro allI conjI iffI)
 fix st st'
 assume H1: "bequiv b BTrue'"
 assume H2: "ceval (WHILE b DO c END) st st'"
 have L1: "\<not> (ceval (WHILE b DO c END) st st')" using H1 by (simp add: while_true_nonterm)
 show "ceval (WHILE BTrue' DO c END) st st'" using H2 L1 by simp
next
 fix st st'
 assume H1: "ceval (WHILE BTrue' DO c END) st st'"
 have L1: "bequiv BTrue' BTrue'" by (simp add: bequiv_def)
 have L2: "\<not> (ceval (WHILE BTrue' DO c END) st st')"
    using L1 by (simp add: while_true_nonterm)
 show "ceval (WHILE b DO c END) st st'" using L2 H1 by simp
qed

(* 
Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  (* SOLUTION: *)
  intros b c Hb.
  split; intros H.
  Case "->".
    apply ex_falso_quodlibet.
    assert (~((WHILE b DO c END) / st ==> st')) as Hcontra.
      apply WHILE_true_nonterm; assumption.
    apply Hcontra. apply H.
  Case "<-".
    apply ex_falso_quodlibet.
    assert (~((WHILE BTrue DO SKIP END) / st ==> st')) as Hcontra.
      apply WHILE_true_nonterm.
      unfold bequiv. reflexivity.
    apply Hcontra. apply H.  Qed.
(** [] *)

(** **** Exercise: 2 stars (WHILE_false_inf) *)
(** Write an informal proof of WHILE_false.

(* SOLUTION: *)
   Theorem: forall [b] [c], if [b] is equivalent to [BFalse],
   then [WHILE b DO c END] is equivalent to [SKIP].
 
   Proof: 

   - (->) We know that [b] is equivalent to [BFalse].  We must
     show, for all [st] and [st'], that if [(WHILE b DO c END) /
     st ==> st'] then [SKIP / st ==> st'].
     
     There are only two ways we can have [(WHILE b DO c END) /
     st ==> st']: using [E_WhileEnd] and [E_WhileLoop].
     
     - Suppose the final rule used to show [(WHILE b DO c END) /
       st ==> st'] was [E_WhileEnd].  We then know that [st =
       st']; by [E_Skip], we know that [SKIP / st ==> st].
     
     - Suppose the final rule used to show [(WHILE b DO c END) / st
       ==> st'] was [E_WhileLoop].  But this rule only applies when
       [beval st b = true].  However, we are assuming that 
       that [b] is equivalent to [BFalse], i.e. forall
       [st], [beval st b = beval st BFalse = false]. So we have
       a contradiction, and the final rule could not have been
       [E_WhileLoop] after all.

   - (<-) We know that [b] is equivalent to [BFalse].  We must
     show, for all [st] and [st'], that if [SKIP / st ==> st']
     then [(WHILE b DO c END) / st ==> st'].
   
     [E_Skip] is the only rule that could have proven [SKIP / st
     ==> st'], so we know that [st' = st].  We must show
     that [(WHILE b DO c LOOP) / st ==> st].
   
     Since [b] is equivalent to [BFalse], we know that [beval st
     b = false].  By [E_WhileEnd], then, we can derive that
     [(WHILE b DO c END) / st ==> st], and we are done.
[]
*)
*)

theorem loop_unrolling : "cequiv (WHILE b DO c END)
                                 (IF b THEN (c ;; WHILE b DO c END) ELSE SKIP)"
apply (unfold cequiv_def, intro allI iffI conjI)
apply (erule ceval.cases, auto intro: ceval.intros)+
done

(* 
Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  unfold cequiv. intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.  
    SCase "loop doesn't run".
      apply E_IfFalse. assumption. apply E_Skip.
    SCase "loop runs".
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0). 
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.

(** Finally, let's look at simple equivalences involving assignments. 
    This turns out to be a little tricky.

    To start with, we might expect to be able to show that certain
    kinds of "useless" assignments can be removed. Most trivially: *)
*)

theorem identity_assignment : "cequiv (x ::= AId' x) SKIP"
apply (unfold cequiv_def, intro conjI iffI allI)
apply (erule ceval.cases, auto intro: ceval.intros)
proof -
  fix sta
  have L : "update sta x (sta x) = sta" 
      by (auto simp: update_def intro: ext) 
  show "ceval SKIP sta (update sta x (sta x))" using L
      by (auto intro: ceval.intros)
 next
  fix st st'
  assume H: "ceval SKIP st st'"
  have L1: "st = st'" using H apply -
                          apply (erule ceval.cases)
                          by auto
  have L2: "update st x (st x) = st" by (auto simp: update_def intro: ext)
  have L3: "update st x (st x) = st'" using L1 L2 by (simp)
  show "ceval (x ::= AId' x) st st'" using L3 by (auto intro: ceval.intros)
qed

(* CL:  TODO - clean this proof up, also we're totes being jerks here by using functional extensionality when Coq doesn't have it *)

(* 
Theorem identity_assignment_first_try : forall (x:id),
  cequiv
    (x ::= AId x)
    SKIP.
Proof. 
   unfold cequiv.  intros. split; intro H.
     Case "->". 
       inversion H; subst.  simpl.
       replace (update st x (st x)) with st.  
       constructor. 
(** But here we're stuck. The goal looks reasonable, but in fact it is
    not provable!  If we look back at the set of lemmas we proved
    about [update] in the last chapter, we can see that lemma
    [update_same] almost does the job, but not quite: it says that the
    original and updated states agree at all values, but this is not
    the same thing as saying that they are [eq] in Coq's sense! 
*)
Admitted.

(** What is going on here?  Recall that our states are just functions
    from identifiers to values.  For Coq, functions are only equal
    when their definitions are syntactically the same (after
    reduction). (Otherwise, attempts to apply the [eq] constructor
    will fail!) In practice, for functions built up out of [update]
    operations, this means that two functions are equal only if they
    were constructed using the _same_ [update] operations, applied in
    the same order.  In the theorem above, the sequence of updates on
    the first parameter [cequiv] is one longer than for the second
    parameter, so it is no wonder that the equality doesn't hold. 

    But the problem is quite general. If we try to prove other
    "trivial" facts, such as

    [cequiv (x ::= APlus (AId x ANum 1) ; x ::= APlus (AId x ANum 1))
            (x ::= APlus (AId x ANum 2))] 

    or

    [cequiv (x ::= ANum 1; y ::= ANum 2) 
            (y ::= ANum 2; x ::= ANum 1)]
  
    we'll get stuck in the same way: we'll have two functions that
    behave the same way on all inputs, but cannot be proven to be [eq]
    to each other.

    The principle we would like to use in these situations is called
    _functional extensionality_:

                        forall x, f x = g x
                       --------------------
                             f = g

    Although this principle is not derivable in Coq, it turns out
    to be safe to add it as an (unproven) _axiom_.  *)

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(** It has been proven that adding this axiom doesn't introduce any
    inconsistencies into Coq.  In this way, it is similar to adding
    one of the classical logic axioms, such as [excluded_middle]. 

    With the benefit of this axiom we can prove our theorem: *)

Theorem identity_assignment : forall (x:id),
  cequiv
    (x ::= AId x)
    SKIP.
Proof. 
   unfold cequiv.  intros. split; intro H.
     Case "->". 
       inversion H; subst. simpl.
       replace (update st x (st x)) with st.  
       constructor. 
       apply functional_extensionality. intro. rewrite update_same; reflexivity.  
     Case "<-".
       inversion H; subst. 
       assert (st' = (update st' x (st' x))).
          apply functional_extensionality. intro. rewrite update_same; reflexivity.
       rewrite H0 at 2. 
       constructor. reflexivity.
Qed.


(** A digression on equivalences.

    Purists might object to using [functional_extensionality].  In
    general, it can be quite dangerous to add axioms, particularly
    several at once (as they may be mutually inconsistent). In fact,
    [functional_extensionality] and [excluded_middle] can both be
    assumed without any problems, but some Coq users prefer to avoid
    such "heavyweight" general techniques, and instead craft solutions
    for specific problems that stay within Coq's standard logic.

    For our particular problem here, rather than extending the
    definition of equality to do what we want on functions
    representing states, we could instead give an explicit notion of
    _equivalence_ on states.  For example: *)

Definition stequiv (st1 st2 : state) : Prop :=
  forall (x:id), st1 x = st2 x. 

Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

(** It is easy to prove that [stequiv] is an _equivalence_ (i.e., it
   is reflexive, symmetric, and transitive), so it partitions the set
   of all states into equivalence classes. *)
(** **** Exercise: 1 star *)
Lemma stequiv_refl : forall (st : state), st ~ st.
Proof.
  (* SOLUTION: *)
  unfold stequiv. intros. reflexivity. Qed.
  
(** **** Exercise: 1 star *)
Lemma stequiv_sym : forall (st1 st2 : state), st1 ~ st2 -> st2 ~ st1.
Proof. 
  (* SOLUTION: *)
  unfold stequiv. intros. rewrite H. reflexivity. Qed.
     
(** **** Exercise: 1 star *)
Lemma stequiv_trans : forall (st1 st2 st3 : state), st1 ~ st2 -> st2 ~ st3 -> st1 ~ st3.
Proof.  
  (* SOLUTION: *)
  unfold stequiv. intros.  rewrite H. rewrite H0. reflexivity.  Qed.
  
(**  It is then straightforward to show that [aeval] and [beval] behave
     uniformly on all members of an equvalence class: *)

(** **** Exercise: 2 stars *)
Lemma stequiv_aeval : forall (st1 st2 : state), 
  st1 ~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a. 
Proof.
  (* SOLUTION: *)
  intros. induction a; simpl; try rewrite IHa1; try rewrite IHa2; try reflexivity.  
  apply H. Qed. 
(** **** Exercise: 2 stars *)
Lemma stequiv_beval : forall (st1 st2 : state), 
  st1 ~ st2 ->
  forall (b:bexp), beval st1 b = beval st2 b. 
Proof.
  (* SOLUTION: *)
  intros. 
  (bexp_cases (induction b) Case); simpl; try reflexivity. 
  Case "BEq".
   repeat rewrite (stequiv_aeval _ _ H). reflexivity. 
  Case "BLe". 
   repeat rewrite (stequiv_aeval _ _ H). reflexivity. 
  Case "BNot".
   rewrite IHb. reflexivity.
  Case "BAnd".
   rewrite IHb1. rewrite IHb2. reflexivity. Qed.
  
(** Now we need to redefine [cequal] to use [~] instead of [=].
    Unfortunately, it is not so easy to do this in a way that keeps
    the definition simple and symmetric.  But here is one approach.
    We first define a looser variant of [==>] that "folds in"
    the notion of equivalence. *)
    
Reserved Notation "c1 '/' st '==>'' st'" (at level 40, st at level 39).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    c / st ==> st' -> 
    st' ~ st'' ->
    c / st ==>' st''
  where   "c1 '/' st '==>'' st'" := (ceval' c1 st st').

(** Now the revised definition of [cequiv'] looks familiar: *)

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st ==>' st') <-> (c2 / st ==>' st').


(** A sanity check shows that the original notion of command equivalence is at least
   as strong as this new one.  (The converse is not true, naturally.) *)
Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof. 
  unfold cequiv, cequiv'; split; intros. 
       inversion H0 ; subst.  apply E_equiv with st'0.  apply (H st st'0); assumption. assumption. 
       inversion H0 ; subst.  apply E_equiv with st'0.  apply (H st st'0). assumption. assumption.
Qed.

(** **** Exercise: 2 stars *)
(** Finally, here is our example once more... (You can complete the proof) *)
Example identity_assign' :
  cequiv' SKIP (X ::= AId X).
Proof.
    unfold cequiv'.  intros.  split; intros. 
    Case "->".
      inversion H; subst; clear H. inversion H0; subst.   apply E_equiv with (update st'0 X (st'0 X)). 
      constructor. reflexivity.  apply stequiv_trans with st'0.  unfold stequiv. intro. apply update_same. reflexivity. assumption. 
    Case "<-".  
      (* SOLUTION: *)
      inversion H; subst; clear H. inversion H0; subst.  simpl in H1.  apply E_equiv with st. 
      constructor.  apply stequiv_trans with (update st X (st X)).  apply stequiv_sym.  unfold stequiv.  intro. rewrite update_same; reflexivity.
      assumption. Qed. 
(** On the whole, this explicit equivalence approach is considerably harder to work with than
    relying on functional extensionality. (Coq does have an advanced mechanism called "setoids" that 
    makes working with equivalences somewhat easier, by allowing them to be registered with the system
    so that standard rewriting tactics work for them almost as well as for equalities.)  
    But it is worth knowing about, because it applies even in situations where the equivalence in
    question is *not* over functions.  For example, if we chose to represent state mappings
    as binary search trees, we would need to use an explicit equivalence of this kind. *)

(** End of digression *)
*)

lemma [simp] : "ceval SKIP st st' \<Longrightarrow> st = st'"
by (erule ceval.cases, auto)

lemma [simp] : "update st x (st x) = st"
by (auto simp: update_def intro: ext)

theorem assign_equiv : "aequiv (AId' x) e \<Longrightarrow> cequiv SKIP (x ::= e)"
proof (unfold cequiv_def, intro conjI iffI allI)
 fix st st'
 assume H1: "aequiv (AId' x) e"
 assume H2: "ceval SKIP st st'"
 have L1 : "st = st'" using H2 by simp
 have L2 : "aeval' st' e = st' x" using H1 by (auto simp: aequiv_def)
 have L3 : "update st x (aeval' st e) = st'" using L1 H1 L2 by (auto)
 show "ceval (x ::= e) st st'" using L3 by (auto intro: ceval.intros)
next
 fix st st'
  assume H1: "aequiv (AId' x) e"
  assume H2: "ceval (x ::= e) st st'"
  have L1 : "st' = update st x (aeval' st e)" using H2 
          apply - apply (erule ceval.cases) by auto
  have L2 : "update st x (aeval' st e) = st" using H1 
    by (auto simp: aequiv_def)
  show "ceval SKIP st st'" using L1 L2 by (auto intro: ceval.intros) 
qed

(* CL:  I'll admit the the above is a bit more verbose than the Coq proof,
        but most of the text comes from the set up of the Isar proof
        which I think is worth it to get the more readable form and
        the forwards reasoning.  I can probably make it cuter,
        but my basic goal was simply to have something nice. *)

(* 

(** **** Exercise: 2 stars *)
Theorem assign_aequiv : forall x e,
  aequiv (AId x) e -> 
  cequiv SKIP (x ::= e).
Proof.
  (* SOLUTION: *)
  unfold cequiv.  intros. 
  split; intros; inversion H0; subst.  
  Case "->".
    assert (st' = update st' x (aeval st' e)). 
      apply functional_extensionality.  intros. unfold aequiv in H.  simpl in H. rewrite <- H.  rewrite update_same; reflexivity.
    rewrite H1 at 2.  constructor; reflexivity. 
  Case "<-".
    replace (update st x (aeval st e)) with st. constructor.
    apply functional_extensionality. intros. rewrite update_same.  reflexivity. apply H.   Qed.
  (** [] *)

(** **** Exercise: 2 stars *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  (* SOLUTION: *)
  unfold cequiv. intros c1 c2 c3 st st'.
  split; intros Hce.
  Case "->".
    inversion Hce. subst. inversion H1. subst.
    apply E_Seq with (st' := st'1); try assumption.
    apply E_Seq with (st' := st'0); try assumption.
  Case "<-".
    inversion Hce. subst. inversion H4. subst.
    apply E_Seq with (st' := st'1); try assumption.
    apply E_Seq with (st' := st'0); try assumption.  Qed.
(** [] *)
*)

theorem seq_assoc : "cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3))"
apply (unfold cequiv_def, intro allI iffI conjI)
by (erule ceval.cases, auto intro: ceval.intros)+

(* CL:  AUTO POWER!!1one 
        Enough proofs come up that look just like this that I'd, honestly, like
        to write a tactic to handle it.
*)

theorem swap_if_branches : "cequiv (IF b THEN e1 ELSE e2) (IF (BNot' b) THEN e2 ELSE e1)"
apply (unfold cequiv_def, intro allI iffI conjI)
by (erule ceval.cases, auto intro: ceval.intros)+

(* CL: I feel like I'm cheating, but I think the Isar examples above make it clear
       that if you want to go through the longer, forward reasoning, you can. 
       Please comment if you'd like to see things done more explicitly! *)

(* 
(** **** Exercise: 3 stars *)
Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  (* SOLUTION: *)
  unfold cequiv. intros b eq e2 st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "b is true".
      apply E_IfFalse; try assumption.
      simpl. rewrite H4. reflexivity.
    SCase "b is false".
      apply E_IfTrue; try assumption.
      simpl. rewrite H4. reflexivity.
  Case "<-".
    inversion Hce; subst.
    SCase "b is false".
      simpl in H4. symmetry in H4; apply negb_sym in H4. simpl in H4.
      apply E_IfFalse; assumption.
    SCase "b is true".
      simpl in H4. symmetry in H4; apply negb_sym in H4. simpl in H4.
      apply E_IfTrue; assumption.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Which of the following pairs of programs are equivalent? Write
    "yes" or "no" for each one.

(a)
[[
    WHILE (BLe (ANum 1) (AId X)) DO 
      X ::= APlus (AId X) (ANum 1) 
    END
]]
    and
[[
    WHILE (BLe (ANum 2) (AId X)) DO 
      X ::= APlus (AId X) (ANum 1) 
    END
]]
(* SOLUTION: *)
    No. (When started in a state where variable X has value 1, the
    first program diverges while the second one halts.)

(b) 
[[
    WHILE BTrue DO 
      WHILE BFalse DO X ::= APlus (AId X) (ANum 1) END 
    END
]]
and
[[
    WHILE BFalse DO 
      WHILE BTrue DO X ::= APlus (AId X) (ANum 1) END 
    END
]]

(* SOLUTION: *)
    No. (The first program always diverges; the second always halts.)

[] *)

(* ####################################################### *)
(** ** Program Equivalence is an Equivalence *)

(** The equivalences on [aexps], [bexps], and [com]s are
    reflexive, symmetric, and transitive *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  unfold aequiv. intros a st. reflexivity.  Qed.
*)

lemma refl_aequiv : "aequiv a a"
by (auto simp: aequiv_def)

(* 
Lemma sym_aequiv : forall (a1 a2 : aexp), 
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.
*)

lemma sym_aequiv : "aequiv a1 a2 \<Longrightarrow> aequiv a2 a1"
by (auto simp: aequiv_def)

(* 
Lemma trans_aequiv : forall (a1 a2 a3 : aexp), 
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3. 
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.
*)

lemma trans_aequiv : "aequiv a1 a2 \<Longrightarrow> aequiv a2 a3 \<Longrightarrow> aequiv a1 a3"
by (auto simp: aequiv_def)

(* 
Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.
*)

lemma refl_bequiv : "bequiv b b"
by (auto simp: bequiv_def)

(* 
Lemma sym_bequiv : forall (b1 b2 : bexp), 
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.
*)

lemma sym_bequiv : "bequiv b1 b2 \<Longrightarrow> bequiv b2 b2"
by (auto simp: bequiv_def)

(* 
Lemma trans_bequiv : forall (b1 b2 b3 : bexp), 
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3. 
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.
*)

lemma trans_bequiv : "bequiv b1 b2 \<Longrightarrow> bequiv b2 b3 \<Longrightarrow> bequiv b1 b3"
by (auto simp: bequiv_def)

(* 
Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.
*)

end

(* 
Lemma sym_cequiv : forall (c1 c2 : com), 
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st ==> st' <-> c2 / st ==> st') as H'. 
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop), 
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A. 
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), 
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3. 
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st ==> st'). apply H12. apply H23.  Qed.

(* ########################################################*)
(** ** Program Equivalence is a Congruence *)

(** Program equivalence is also a _congruence_.  That is, the
    equivalence of two subprograms implies the equivalence of the
    whole programs in which they are embedded:
[[[
              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')
 
              cequiv c1 c1'    
              cequiv c2 c2'
         ------------------------
         cequiv (c1;c2) (c1';c2')
]]]
    And so on.  Note that we are using the inference rule notation
    here not as part of a _definition_, but simply to write down some
    valid implications in a readable format. We prove these
    implications below.
 
    We will see why these congruence properties are important in the
    following section (in the proof of [fold_constants_com_sound]). *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  unfold aequiv,cequiv. intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass. 
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [WHILE b1 DO c1 END / st ==> st'] iff [WHILE b1' DO c1' END / st
    ==> st'].  We consider each direction in turn.

      - (---->) We show that [WHILE b1 DO c1 END / st ==> st'] implies
        [WHILE b1' DO c1' END / st ==> st'], by induction on a
        derivation of [WHILE b1 DO c1 END / st ==> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileEnd] or [E_WhileLoop].

          - [E_WhileEnd]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E-WhileEnd] applies, giving us [WHILE b1' DO
            c1' END / st ==> st'], as required.

          - [E_WhileLoop]: The form of the rule now gives us [beval st
            b1 = true], with [c1 / st ==> st'0] and [WHILE b1 DO c1
            END / st'0 ==> st'] for some state [st'0], with the
            induction hypothesis [WHILE b1' DO c1' END / st'0 ==>
            st'].  

            Since [c1] and [c1'] are equivalent, we know that [c1' /
            st ==> st'0].  And since [b1] and [b1'] are equivalent, we
            have [beval st b1' = true].  Now [E-WhileLoop] applies,
            giving us [WHILE b1' DO c1' END / st ==> st'], as
            required.

      - (<----) Similar. [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile.
    induction Hce; try (inversion Heqcwhile); subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution". 
        apply (Hc1e st st').  apply Hce1. 
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while.
    induction Hce; try (inversion Heqc'while); subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution". 
        apply (Hc1e st st').  apply Hce1. 
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.  Qed.

(** **** Exercise: 3 stars *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;c2) (c1';c2').
Proof. 
  (* SOLUTION: *)
  unfold cequiv. intros c1 c1' c2 c2' Hc1 Hc2 st st'.
  split; intros Hc; inversion Hc; subst.
  Case "->".
    apply E_Seq with (st' := st'0).
    SCase "c1".
      destruct (Hc1 st st'0) as [Hc1c1' _]. 
      apply Hc1c1'. apply H1.
    SCase "c2".
      destruct (Hc2 st'0 st') as [Hc2c2' _].
      apply Hc2c2'. apply H4.
  Case "<-".
    apply E_Seq with (st' := st'0).
    SCase "c1".
      destruct (Hc1 st st'0) as [_ Hc1'c1].
      apply Hc1'c1. apply H1.
    SCase "c2".
      destruct (Hc2 st'0 st') as [_ Hc2'c2].
      apply Hc2'c2. apply H4.  Qed.
(** [] *)

(** **** Exercise: 3 stars *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  (* SOLUTION: *)
  unfold bequiv,cequiv.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
  destruct (Hc1e st st') as [Hc1c1' Hc1'c1].
  destruct (Hc2e st st') as [Hc2c2' Hc2'c2]. clear Hc1e Hc2e.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "E_IfTrue".  
      rewrite -> Hbe in H4. apply Hc1c1' in H5. 
      apply E_IfTrue; assumption.
    SCase "E_IfFalse".
      rewrite -> Hbe in H4. apply Hc2c2' in H5.
      apply E_IfFalse; assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "E_IfTrue".
      rewrite <- Hbe in H4. apply Hc1'c1 in H5.
      apply E_IfTrue; assumption.
    SCase "E_IfFalse".
      rewrite <- Hbe in H4. apply Hc2'c2 in H5.
      apply E_IfFalse; assumption.  Qed.
(** [] *)


Example congruence_example:
  cequiv
    (X ::= ANum 0;
     IFB (BEq (AMinus (AId X) (AId X)) (ANum 0))
     THEN
       Y ::= AId X
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= AMinus (AId X) (AId X);
     IFB (BTrue)
     THEN
        Y ::= APlus (ANum 0) (AId X) 
     ELSE
        Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence. 
    apply CAss_congruence.
      apply sym_aequiv. apply aequiv_example.
    apply CIf_congruence.
      apply bequiv_example.
      apply CAss_congruence. unfold aequiv. simpl. reflexivity.
      apply refl_cequiv. 
Qed.
      

(* ####################################################### *)
(** * Case Study: Constant Folding *)

(** A _program transformation_ is a function that takes a program
    as input and produces some variant of the program as its
    output.  Compiler optimizations such as constant folding are
    a canonical example, but there are many others. *)

(* ####################################################### *)
(** ** Soundness of Program Transformations *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program.
 
    We can define a notion of soundness for translations of
    [aexp]s, [bexp]s, and [com]s. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ######################################################## *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.
 
    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (plus n1 n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (minus n1 n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (mult n1 n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp 
      (AMult (APlus (ANum 1) (ANum 2)) (AId X)) 
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions, but the
    definitions and proofs get longer. *)

Example fold_aexp_ex2 :
    fold_constants_aexp 
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases), we can also find constant _boolean_
    expressions and reduce them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2  => 
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1  => 
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  => 
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp 
      (BAnd (BEq (AId X) (AId Y)) 
            (BEq (ANum 0) 
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      => 
      SKIP
  | i ::= a  => 
      CAss i (fold_constants_aexp a)
  | c1 ; c2  => 
      (fold_constants_com c1) ; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI => 
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1 ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END => 
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com 
    (X ::= APlus (ANum 4) (ANum 5);
     Y ::= AMinus (AId X) (ANum 3);
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP 
     ELSE
       Y ::= ANum 0
     FI;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP 
     FI;
     WHILE BEq (AId Y) (ANum 0) DO 
       X ::= APlus (AId X) (ANum 1) 
     END) =
  (X ::= ANum 9;
   Y ::= AMinus (AId X) (ANum 3);
   IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
     SKIP 
   ELSE
     (Y ::= ANum 0) 
   FI;
   Y ::= ANum 0;
   WHILE BEq (AId Y) (ANum 0) DO 
     X ::= APlus (AId X) (ANum 1) 
   END).
Proof. reflexivity. Qed.


(* ################################################### *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

Theorem fold_constants_aexp_sound: 
  atrans_sound fold_constants_aexp.
Proof. 
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case.
  Case "ANum". reflexivity.
  Case "AId". reflexivity.
  Case "APlus".  simpl. 
    remember (fold_constants_aexp a1) as a1'. 
    remember (fold_constants_aexp a2) as a2'.
    rewrite IHa1. rewrite IHa2. 
    destruct a1' ; destruct a2'; reflexivity.
  Case "AMinus". simpl.
    remember (fold_constants_aexp a1) as a1'. 
    remember (fold_constants_aexp a2) as a2'.
    rewrite IHa1. rewrite IHa2.
    destruct a1'; destruct a2'; reflexivity.
  Case "AMult". simpl.
    remember (fold_constants_aexp a1) as a1'. 
    remember (fold_constants_aexp a2) as a2'.
    rewrite IHa1. rewrite IHa2.
    destruct a1'; destruct a2'; reflexivity.  Qed.

(** Here's a shorter proof... *)

Theorem fold_constants_aexp_sound' : 
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  (aexp_cases (induction a) Case); simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2) 
            = ANum (plus (aeval st a1) (aeval st a2)) 
            = aeval st (ANum (plus (aeval st a1) (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.
                                                      
(** **** Exercise: 3 stars *)
(** Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show 
[[
       beval st (BEq a1 a2) 
     = beval st (fold_constants_bexp (BEq a1 a2)).
]]
   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have
[[
           fold_constants_bexp (BEq a1 a2) 
         = if beq_nat n1 n2 then BTrue else BFalse
]]
       and
[[
           beval st (BEq a1 a2) 
         = beq_nat (aeval st a1) (aeval st a2).
]]
       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know
[[
           aeval st a1 
         = aeval st (fold_constants_aexp a1) 
         = aeval st (ANum n1) 
         = n1
]]
       and
[[
           aeval st a2 
         = aeval st (fold_constants_aexp a2) 
         = aeval st (ANum n2) 
         = n2,
]]
       so
[[
           beval st (BEq a1 a2) 
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.
]]
       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that
[[
           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.
]]
       So
[[
           beval st (BEq a1 a2) 
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
]]         
       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show
[[
           beval st (BEq a1 a2) 
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),
]]
       which, by the definition of [beval], is the same as showing
[[
           beq_nat (aeval st a1) (aeval st a2) 
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).
]]
       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us
[[
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
]]
       completing the case. *)

Theorem fold_constants_bexp_sound: 
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  (bexp_cases (induction b) Case); 
    (* BTrue and BFalse are immediate *)
    try reflexivity. 
  Case "BEq". 
    (* Doing induction when there are a lot of constructors makes
       specifying variable names a chore, but Coq doesn't always
       choose nice variable names.  You can rename entries in the
       context with the [rename] tactic: [rename a into a1] will
       change [a] to [a1] in the current goal and context. *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'. 
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      (* The only interesting case is when both a1 and a2 
         become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  Case "BLe". 
    (* SOLUTION: *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'. 
    remember (fold_constants_aexp a2) as a2'.
    (* a slightly alternative approach using asserts: *)
    assert (aeval st a1 = aeval st a1') as H1.
      SCase "Proof of assertion". subst a1'. apply fold_constants_aexp_sound.
    assert (aeval st a2 = aeval st a2') as H2.
      SCase "Proof of assertion". subst a2'. apply fold_constants_aexp_sound. 
    rewrite H1. rewrite H2.
    destruct a1'; destruct a2'; try reflexivity.
      (* Again, the only interesting case is when both a1 and a2 
         become constants after folding *)
      simpl. destruct (ble_nat n n0); reflexivity.
      Case "BNot". 
    simpl. remember (fold_constants_bexp b) as b'. 
    rewrite IHb.
    destruct b'; reflexivity. 
  Case "BAnd". 
    simpl. 
    remember (fold_constants_bexp b1) as b1'. 
    remember (fold_constants_bexp b2) as b2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  (com_cases (induction c) Case); simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    (* SOLUTION: *)
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      (* Again, the cases where fold_constants_com doesn't change
         the test or don't change the loop body follow from the
         IH and [fold_constants_bexp_sound] *)
      try (apply CWhile_congruence; assumption).
    SCase "b always true".
      apply WHILE_true; assumption.
    SCase "b always false".
      apply WHILE_false; assumption.  Qed.
(** [] *)

(* ########################################################## *)
(** ** Soundness of (0 + n) elimination *)

(** **** Exercise: 4 stars (optimize_0plus) *)
(** Recall the definition [optimize_0plus] from Imp.v:
[[
    Fixpoint optimize_0plus (e:aexp) : aexp := 
      match e with
      | ANum n => ANum n
      | APlus (ANum 0) e2 => optimize_0plus e2
      | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
      end.
]]
   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function, and analogous ones for bexps
   and commands:
[[
     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
]]
   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] (otherwise it will be _long_!).

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)
(* SOLUTION: *)

Fixpoint optimize_0plus_aexp (e:aexp) : aexp := 
  match e with
  | ANum n => ANum n
  | AId i => AId i
  | APlus (ANum 0) e2 => optimize_0plus_aexp e2
  | APlus e1 e2 => APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 => AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 => AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1     => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP       => SKIP
  | CAss i a    => CAss i (optimize_0plus_aexp a)
  | c1 ; c2  => (optimize_0plus_com c1) ; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI => IFB (optimize_0plus_bexp b) THEN (optimize_0plus_com c1) ELSE (optimize_0plus_com c2) FI
  | WHILE b DO c END  => WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.

Theorem optimize_0plus_aexp_sound: 
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound, aequiv.
  intros a st. 
  (aexp_cases (induction a) Case); 
    (* ANum and AId are immediate by definition *)
    try (reflexivity);
    (* AMinus and AMult are immediate by IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  Case "APlus".
    (aexp_cases (destruct a1) SCase); 
    (* everything but ANum and AId follow from the IH *)
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "ANum".
      simpl. rewrite IHa2.
      destruct n as [| n'].
      SSCase "n = 0".
        apply plus_0_l.
      SSCase "n = S n'".
        simpl. reflexivity.
    SCase "AId".
      simpl. rewrite IHa2. reflexivity.  Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound, bequiv.
  intros b st. (bexp_cases (induction b) Case); simpl;
               try reflexivity;
               try (rewrite IHb1; rewrite IHb2; reflexivity);
               try (rewrite <- optimize_0plus_aexp_sound;
                    rewrite <- optimize_0plus_aexp_sound;
                    reflexivity).
  Case "BNot".
    rewrite IHb. reflexivity.  Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound, cequiv.
  intros c.
  (com_cases (induction c) Case); 
  intros st st'; simpl.
  Case "SKIP".
    apply refl_cequiv.
  Case "::=".
    apply CAss_congruence.
    apply optimize_0plus_aexp_sound.
  Case ";".
    apply CSeq_congruence; unfold cequiv.
    apply IHc1. apply IHc2.
  Case "IFB".
    apply CIf_congruence; unfold cequiv.
    apply optimize_0plus_bexp_sound.
    apply IHc1. apply IHc2.
  Case "WHILE".
    apply CWhile_congruence; unfold cequiv.
    apply optimize_0plus_bexp_sound.
    apply IHc.  Qed.

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. unfold optimizer.
  intros c.
  apply trans_cequiv with (fold_constants_com c).
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound.  Qed.
(** [] *)

(* ####################################################### *)
(** * Proving That Programs Are _Not_ Equivalent *)

(** Suppose that [c1] is a command of the form [x ::= a1; y ::= a2]
    and [c2] is the command [x ::= a1; y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [x] in [a2].
    For example, [c1] and [c2] might be:
[[
       c1  =  (x ::= 42 + 53; 
               y ::= y + x)
       c2  =  (x ::= 42 + 53; 
               y ::= y + (42 + 53))
]]
    Clearly, this particular [c1] and [c2] are equivalent.  But is
    this true in general? *)

(** We will see that it is not, but it is worthwhile to pause,
    now, and see if you can find a counter-example on your own (or
    remember the one from the discussion from class). *)

(** Here, formally, is the function that substitutes an arithmetic
    expression for each occurrence of a given location in another
    expression *)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i'       => if beq_id i i' then u else AId i'
  | APlus a1 a2  => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

(** Sadly, the property does _not_ always hold.  First, a helper lemma:  *)

Lemma cequiv_state: forall c1 c2 st st' st'',
  cequiv c1 c2 ->
  c1 / st ==> st' ->
  c2 / st ==> st'' ->
  st' = st''.  
Proof. 
  intros c1 c2 st st' st'' Hcequiv Hc1 Hc2.
  unfold cequiv in Hcequiv. destruct (Hcequiv st st') as [Hc12 _].
   (* By equivalence c2 / st ==> st' *)
   apply Hc12 in Hc1. 
   (* By determinacy, st' = st'' *)
   apply (ceval_deterministic c2 st); assumption.  Qed.
 
(** Now a proof by counter-example. *)

Theorem subst_inequiv : 
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1); 
            Y ::= AId X) 
      as c1.
  remember (X ::= APlus (AId X) (ANum 1); 
            Y ::= APlus (AId X) (ANum 1)) 
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  
  (* This allows us to show that the command 
        [X ::= APlus (AId X) (ANum 1); Y ::= AId X] 
     can terminate in two different final states:
        st'  = {X |-> 1, Y |-> 1} 
        st'' = {X |-> 1, Y |-> 2}. *)
  remember (update (update empty_state X 1) Y 1) as st'.
  remember (update (update empty_state X 1) Y 2) as st''.
  assert (st' = st'') as Hcontra. 
  Case "Pf of Hcontra".     
  (* This can be shown by using [cequiv_state], 
     with appropriate "final" states for c1 and c2 *)
    assert (c1 / empty_state ==> st') as H1;
    assert (c2 / empty_state ==> st'') as H2;
    try (subst;
         apply E_Seq with (st' := (update empty_state X 1)); 
         apply E_Ass; reflexivity).
    apply (cequiv_state c1 c2 empty_state st' st''); try assumption.
  
  (* Finally, we use the "equality" of the different states 
     to obtain a contradiction. *)
  assert (st' Y = st'' Y) as Hcontra' 
    by (rewrite Hcontra; reflexivity).
  subst; inversion Hcontra'.  Qed.

       

(** **** Exercise: 4 stars (better_subst_equiv) *)
(** The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [x] occurs in the
    right-hand-side of the first assignment statement. *)
   

Inductive var_not_used_in_aexp (x:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp x (ANum n)
  | VNUId: forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus: forall a1 a2, 
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus: forall a1 a2, 
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult: forall a1 a2, 
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  (* SOLUTION: *)
  intros i st a.
  (aexp_cases (induction a) Case); intros ni Hi;
    (* the binary operators follow from the IH *)
    try (simpl; inversion Hi; subst; 
         rewrite IHa1; try assumption;
         rewrite IHa2; try assumption;
         reflexivity).
  Case "ANum".
    reflexivity.
  Case "AId".
    inversion Hi; subst. simpl.
    assert ((update st i ni) i0 = st i0).
    SCase "Pf of assertion".
      apply update_neq.
      apply not_eq_beq_id_false. assumption.
    assumption.  Qed.
  
  (* Using [var_not_used_in_aexp], formalize and prove 
     a correct verson of [subst_equiv_property]. *)
(* SOLUTION: *)
Lemma aeval_subst : forall i st a1 a2,
  var_not_used_in_aexp i a1 ->
  aeval (update st i (aeval st a1)) a2 =
  aeval (update st i (aeval st a1)) (subst_aexp i a1 a2).
Proof.
  intros i st a1 a2 Hi.
  generalize dependent st.
  (aexp_cases (induction a2) Case); intros st;
    (* operator cases follow from the IH *)
    try (simpl; rewrite -> IHa2_1; rewrite -> IHa2_2; reflexivity).
  Case "ANum".
    reflexivity.
  Case "AId".
    unfold subst_aexp.
    remember (beq_id i i0) as b.
    destruct b.
    SCase "i = i0".
      assert (aeval (update st i (aeval st a1)) a1 = aeval st a1).
      SSCase "Pf of assertion".
        apply aeval_weakening. assumption.
      rewrite -> H.
      apply beq_id_eq in Heqb. subst i0.
      unfold update. simpl. rewrite <- beq_id_refl. reflexivity.
    SCase "i <> i0".
      reflexivity.  Qed.

Theorem subst_equiv : forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).
Proof.
  unfold cequiv. intros i1 i2 a1 a2 Hi.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    apply E_Seq with st'0; try assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. symmetry. apply aeval_subst.
    assumption.
  Case "<-".
    inversion Hce; subst.
    apply E_Seq with st'0.
    assumption.
    inversion H4; subst. apply E_Ass.
    inversion H1; subst. apply aeval_subst.
    assumption.  Qed.
(** [] *)

(** **** Exercise: 3 stars *)
Theorem inequiv_exercise: 
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  (* SOLUTION: *)
  intros Contra. 
  assert (~((WHILE BTrue DO SKIP END) / empty_state ==> empty_state)) as H. 
    apply WHILE_true_nonterm. apply refl_bequiv.
  apply H. 
  apply (Contra empty_state empty_state). 
  apply E_Skip. Qed.
(** [] *)

(* ####################################################### *)
(** * Reasoning about Imp programs *)

(** Recall the factorial program: *)
(* Print fact_body. Print fact_loop. Print fact_com. *)

(** Here is an alternative "mathematical" definition of the factorial
    function: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (real_fact n')
  end.

(** We would like to show that they agree -- if we start [fact_com] in
    a state where variable [X] contains some number [x], then it will
    terminate in a state where variable [Y] contains the factorial of
    [x].

    To show this, we rely on the critical idea of a _loop
    invariant_. *)

Definition fact_invariant (x:nat) (st:state) :=
  mult (st Y) (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant: forall st st' x,
     fact_invariant x st ->
     st Z <> 0 ->
     fact_body / st ==> st' ->
     fact_invariant x st'.
Proof.
  intros st st' x Hm HZnz He.
  unfold fact_invariant in Hm.
  unfold fact_invariant.
  unfold fact_body in He.
  inversion He; subst.
  inversion H1; subst.
  inversion H4; subst.
  simpl. 
  rewrite (update_neq Z Y); [|reflexivity].
  rewrite (update_neq Y Z); [|reflexivity].
  rewrite update_eq. rewrite update_eq. 
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as [| z'].
    apply ex_falso_quodlibet. apply HZnz. reflexivity.
  simpl. rewrite <- Hm. rewrite <- mult_assoc. simpl.  
  replace (z' - 0) with z' by omega. 
  reflexivity.  Qed.



Theorem fact_loop_preserves_invariant : forall st st' x,
     fact_invariant x st ->
     fact_loop / st ==> st' ->
     fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  (ceval_cases (induction Hce) Case); inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    (* trivial when the loop doesn't run... *)
    assumption.
  Case "E_WhileLoop".
    (* if the loop does run, we know that fact_body preserves
       fact_invariant -- we just need to assemble the pieces *)
    apply IHHce2. 
      apply fact_body_preserves_invariant with st.  
        assumption.
        intros Contra. simpl in H0; subst. rewrite Contra in H0. inversion H0. 
      assumption.
      reflexivity.  Qed.

Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st ==> st' ->
     beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  (ceval_cases (induction Hce) Case); try (inversion Heqcloop; subst).
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.  Qed.

(** Patching it all together... *)
Theorem fact_com_correct : forall st st' x,
     st X = x ->
     fact_com / st ==> st' ->
     st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst.
  inversion H1; subst.
  inversion H4; subst.
  inversion H2; subst.
  rename st' into st''.
  (* we notice that the invariant is set up before the loop runs... *)
  remember (update (update st Z (aeval st (AId X))) Y
            (aeval (update st Z (aeval st (AId X))) (ANum 1))) as st'.
  assert (fact_invariant (st X) st').
    unfold fact_invariant. subst st'. 
    simpl.
    rewrite update_neq; try reflexivity.
    rewrite update_eq.
    omega.
  (* ...and that when the loop is done running, the invariant 
     is maintained *)
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  (* Finally, if the loop terminated, then Z is 0; so Y must be
     factorial of X *)
  assert (beval st'' (BNot (BEq (AId Z) (ANum 0))) = false).
      apply guard_false_after_loop with (st := st') (c := fact_body).
      apply H6.
  remember (st'' Z) as z''. destruct z''.
  Case "st'' Z = 0".
     simpl in H0. omega. 
  Case "st'' Z > 0 (impossible)".
    simpl in H3.  rewrite <- Heqz'' in H3. inversion H3. 
Qed.

(** One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the topic of next week's lectures! *)

(** **** Exercise: 3 stars (subtract_slowly_spec) *)
(** Prove a specification for subtract_slowly, using the above
    specification of [fact_com] and the invariant below as
    guides. *)

Definition ss_invariant (x:nat) (z:nat) (st:state) :=
  minus (st Z) (st X) = minus z x.

(* SOLUTION: *)
Theorem ss_body_preserves_invariant : forall st x z st',
     ss_invariant x z st ->
     st X <> 0 ->
     subtract_slowly_body / st ==> st' ->
     ss_invariant x z st'.
Proof.
  intros st x z st' H Hnz He.
  unfold ss_invariant in *.
  inversion He; subst. 
  inversion H2; subst.  
  inversion H5; subst. 
  simpl.
  rewrite update_neq; [|reflexivity].
  rewrite update_eq. 
  rewrite update_eq.
  rewrite update_neq; [|reflexivity].
  omega.   (* Interestingly, this all we need here  -- although only after a perceptible delay! *)
Qed.

Theorem ss_preserves_invariant : forall st x z st',
     ss_invariant x z st ->
     subtract_slowly / st ==> st'  ->
     ss_invariant x z st'.
Proof.
  intros st x z st' H He.
  remember subtract_slowly as c.
  (ceval_cases (induction He) Case); inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHe2; try reflexivity.
    apply ss_body_preserves_invariant with st; try assumption.
    intros Contra. simpl in H0. rewrite Contra in H0. inversion H0.  Qed.

Theorem ss_correct : forall st x z st',
     st X = x ->
     st Z = z ->
     subtract_slowly / st ==> st' ->
     st' Z = minus z x.
Proof.
  intros st x z st' HX HZ He.
  assert (ss_invariant x z st).
    unfold ss_invariant.
    subst.
    reflexivity.
  assert (ss_invariant x z st').
    apply ss_preserves_invariant with st; assumption.
  unfold ss_invariant in H0.
  assert (beval st' (BNot (BEq (AId X) (ANum 0))) = false).
    apply guard_false_after_loop with (st := st) (c := subtract_slowly_body).
    assumption.
  remember (st' X) as x''. destruct x''.
  Case "st' X = 0".
   omega. 
  Case "st' X > 0 (impossible)".
   simpl in H1. rewrite <- Heqx'' in H1. inversion H1. 
Qed.
(** [] *)

(* ####################################################### *)
(** * Additional exercises *)

(** **** Exercise: 3 stars, optional (update_eq_variant) *)
(** The way [update_eq] is stated (in the section on mappings
    in Imp.v) may have looked a bit surprising: wouldn't it be
    simpler just to say [lookup k (update f k x) = Some x]?
    Try changing the statement of the theorem to read like this;
    then work through some of this file and see how the proofs
    that use [update_eq] need to be changed to use the
    simplified version. *)
(** [] *)

(** **** Exercise: 4 stars, optional *)
(** This exercise extends an optional exercise from Imp.v, where you
    were asked to extend the language of commands with C-style [for]
    loops.  Prove that the command:
[[
      for (c1 ; b ; c2) {
          c3
      }
]]
    is equivalent to:
[[
       c1 ; 
       WHILE b DO
         c3 ;
         c2
       END
]]
*)
(* SOLUTION: *)
(** [] *)

(** **** Exercise: 3 stars *)
Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 -> 
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1; l2 ::= a2)
    (l2 ::= a2; l1 ::= a1).
Proof. 
(* Hint: You'll need [functional_extensionality] *)
(* SOLUTION: *)
intros l1 l2 a1 a2 NEQ VNU1 VNU2. 
  unfold cequiv. intros st st'. 
  remember (update st l1 (aeval st a1)) as st1. 
  remember (update st l2 (aeval st a2)) as st2. 
  assert (aeval st a1 = aeval st2 a1) as AE1. 
        subst st2. rewrite aeval_weakening; try reflexivity; try assumption.
  assert (aeval st a2 = aeval st1 a2) as AE2.
        subst st1. rewrite aeval_weakening; try reflexivity; try assumption.
  assert ((update st1 l2 (aeval st1 a2)) =
          (update st2 l1 (aeval st2 a1))) as EQST.
     rewrite <- AE1.  rewrite <- AE2. 
     apply functional_extensionality.  intros.  subst st1 st2. 
     apply update_permute. apply not_eq_beq_id_false. assumption.
  split; intro. 
  Case "->".
    inversion H. 
    inversion H2.
    inversion H5.
    apply E_Seq with st2; subst.
       apply E_Ass. reflexivity. 
       rewrite EQST. apply E_Ass. reflexivity. 
  Case "<-".
    inversion H.
    inversion H2.
    inversion H5.
    apply E_Seq with st1; subst. 
       apply E_Ass. reflexivity. 
       rewrite <- EQST. apply E_Ass. reflexivity.  Qed.

*)
