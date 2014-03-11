theory Hoare
imports Main Imp begin

(* 

(** * Hoare: Hoare Logic *)
(* Version of 5/5/2010 *)


Require Export Imp.

(** In the past two chapters, we've begun applying the mathematical
    tools developed in the first part of the course to studying the
    theory of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      If the course had ended at this point, we would still have
      gotten to something extremely useful: a set of tools for
      defining and discussing programming languages and language
      features that are mathematically precise, easy to work with, and
      very flexible.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinacy of evaluation

        - equivalence of some different ways of writing down the
          definition

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving behavioral
          equivalence) of a number of useful program transformations.

      All of these properties -- especially the behavioral
      equivalences -- are things that language designers, compiler
      writers, and users might care about knowing.  Indeed, many of
      them are so fundamental to our understanding of the programming
      languages we deal with that we might not consciously recognize
      them as "theorems."  (But, as the discussion of
      [subst_equiv_property] in Equiv.v showed, properties that seem
      intuitively obvious can sometimes be quite subtle or, in some
      cases, actually even wrong!)

      We'll return to this theme later in the course when we discuss
      _types_ and _type soundness_.

    - We saw a couple of examples of _program verification_ -- using
      the precise definition of Imp to prove formally that certain
      particular programs (factorial and slow subtraction) satisfied
      particular specifications of their behavior.
*)

(** In this chapter, we're going to take this idea further.  We'll
    develop a reasoning system called _Floyd-Hoare Logic_ -- usually,
    if somewhat unfairly, shortened to just _Hoare Logic_ -- in which
    each of the syntactic constructs of Imp is equipped with a single,
    generic "proof rule" that can be used to reason about programs
    involving this construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a huge variety of tools that are now being
    used to specify and verify real software systems.
*)

  
(* ####################################################### *)
(** * Hoare Logic *)

(* ####################################################### *)
(** ** Assertions *)

(** If we're going to talk about specifications of programs, the first
    thing we'll want is a way of making _assertions_ about properties
    that hold at particular points in time -- i.e., properties that
    may or may not be true of a given state. *)

Definition Assertion := state -> Prop.
*)

types assertion = "state \<Rightarrow> bool"

(* 
(** **** Exercise: 1 star (assertions) *)
(** Paraphrase the following assertions in English.
[[
      fun st =>  st X = 3
      fun st =>  st X = x
      fun st =>  st X <= st Y
      fun st =>  st X = 3 \/ st X <= st Y
      fun st =>  (st Z) * (st Z) <= x 
                 /\ ~ (((S (st Z)) * (S (st Z))) <= x)
      fun st =>  True
      fun st =>  False
]]
*)
(** (Remember that one-star exercises do not need to be handed in.) *)
(** [] *)

(** This way of writing assertions is formally correct -- it precisely
    captures what we mean, and it is exactly what we will use in Coq
    proofs -- but it is not very nice to look at: every single
    assertion that we ever write is going to begin with [fun st => ],
    and everyplace we refer to a variable in the current state it is
    written [st X].

    Moreover, this is the _only_ way we use states and the only way we
    refer to the values of variables in the current state: we never
    need to talk about two states at the same time, etc.  So when we
    are writing down assertions informally, we can make some
    simplifications: drop the initial [fun st =>] and write just [X]
    instead of [st X]. *)
(** Informally, instead of
[[
      fun st =>  (st Z) * (st Z) <= x 
                 /\ ~ ((S (st Z)) * (S (st Z)) <= x)
]]
    we'll write just
[[
         Z * Z <= x 
      /\ ~((S Z) * (S Z) <= x).
]]
*)

(* ####################################################### *)
(** ** Hoare Triples *)

(** Next, we need a way of specifying -- making general claims
    about -- the behavior of commands.  Since we've defined assertions
    as a way of making general claims about the properties of states,
    and since the behavior of a command is to transform one state to
    another, a general claim about a command takes the following form:

      - "If [c] is started in a state satisfying assertion [P], and if
        [c] eventually terminates, then the final state is guaranteed
        to satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called a _precondition_; [Q] is a _postcondition_.
 
    Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
[[
       {{P}}  c  {{Q}}.
]]
    Traditionally, Hoare triples are written [{P} c {Q}], but single
    braces are already used for other things in Coq.  *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st ==> st'  ->
       P st  ->
       Q st'.
*)

definition hoare_triple :: "assertion \<Rightarrow> com \<Rightarrow> assertion \<Rightarrow> bool" ("{{_}} _ {{_}}") where
"{{P}} c {{Q}} \<equiv> (\<forall> st st'. ceval c st st' \<longrightarrow> P st \<longrightarrow> Q st')"

(* 
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** **** Exercise: 1 star (triples) *)
(** Paraphrase the following Hoare triples in English.  
[[
      {{True}} c {{X = 5}}

      {{X = x}} c {{X = x + 5)}}

      {{X <= Y}} c {{Y <= X}}

      {{True}} c {{False}}

         {{X = x}} 
      c
         {{Y = real_fact x}}.

         {{True}} 
      c 
         {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}
]]
 *)
(** [] *)

(** **** Exercise: 1 star (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?  
[[
      {{True}} X ::= 5 {{X = 5}}

      {{X = 2}} X ::= X + 1 {{X = 3}}

      {{True}} X ::= 5; Y ::= 0 {{X = 5}}

      {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

      {{True}} SKIP {{False}}

      {{False}} SKIP {{True}}

      {{True}} WHILE True DO SKIP END {{False}}

         {{X = 0}} 
      WHILE X == 0 DO X ::= X + 1 END 
         {{X = 1}}

         {{X = 1}} 
      WHILE X <> 0 DO X ::= X + 1 END 
         {{X = 100}}
]]
   (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability.  We'll continue
   doing so throughout the chapter.) *)
(** [] *)

(** To get us warmed up, here are two simple facts about Hoare
   triples *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.
*)

theorem hoare_post_true : "(\<forall> st. Q st) \<Longrightarrow> {{P}} c {{Q}}"
  by (auto simp: hoare_triple_def)

theorem hoare_pre_false : "(\<forall> st. \<not>(P st)) \<Longrightarrow> {{P}} c {{Q}}"
  by (auto simp: hoare_triple_def)

(* 
Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  destruct HP.  Qed.

(* ####################################################### *) 
(** ** Weakest Preconditions *)

(** That is, [P] suffices to guarantee that [Q] holds after [c],
    and [P] is the weakest (easiest to satisfy) assertion that
    guarantees [Q] after [c]. *)

(** **** Exercise: 1 star (wp) *)
(** What are the weakest preconditions of the following commands
   for the following postconditions?
[[
     {{ ? }}  SKIP  {{ X = 5 }}

     {{ ? }}  X ::= Y + Z {{ X = 5 }}

     {{ ? }}  X ::= Y  {{ X = Y }}

        {{ ? }}  
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
        {{ Y = 5 }}

        {{ ? }}  
     X ::= 5
        {{ X = 0 }}

        {{ ? }}  
     WHILE True DO X ::= 0 END
        {{ X = 0 }}
]]
*)
(** [] *)

(* ####################################################### *) 
(** ** Proof Rules *)

(* ####################################################### *) 
(** *** Assignment *)

(** The rule for reasoning about assignment is the most basic of
    the Hoare rules... and probably the trickiest!  Here's how it
    works.

    Consider this (valid) Hoare triple:
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
]]
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
]]
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if a is *any* arithmetic expression, then
[[
       {{ a = 1 }}  X ::= a {{ X = 1 }}
]]
    is a valid Hoare triple. 

    Even more generally, if [Q] is *any* property of numbers and
    [a] is any arithmetic expression, then
[[
       {{ Q(a) }}  X ::= a {{ Q(X) }}
]]
    is a valid Hoare triple.

    Rephrasing this a bit leads us to the general Hoare rule for
    assignment:
[[
      {{ Q where a is substituted for X }}  X ::= a  {{ Q }}
]]
    This rule looks backwards to everyone at first -- what it's
    saying is that, if Q holds in an environment where X is
    replaced by the value of a, then Q still holds after
    executing [X ::= a].

    For example, these are valid applications of the assignment
    rule:
[[
      {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}

      {{ 3 = 3 }}  X ::= 3  {{ X = 3 }}

      {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
*)

(** We could try to formalize the assignment rule directly in Coq
    by treating [Q] as a family of assertions indexed by
    arithmetic expressions -- something like this:
[[
      Theorem hoare_asgn_firsttry : 
        forall (Q : aexp -> Assertion) V a,
        {{fun st => Q a st}} (V ::= a) {{fun st => Q (AId V) st}}.
]]
    But this formulation is not very nice, for two reasons.
    First, it is not clear how we'd prove it is valid (we'd need
    to somehow reason about all possible propositions).  And
    second, even if we could prove it, it would be awkward to
    use.

    A much smoother way of formalizing the rule arises from the
    following obervation:

    - For all states [st], "[Q] where a is substituted for [X]"
      holds in the state [st] if and only if [Q] holds in the
      state [update st X (aeval st a)]. *)
 
(** That is, asserting that a substituted variant of [Q] holds in
    some state is the same as asserting that [Q] itself holds in
    a substituted variant of the state.  *)

(** Substitution: *)

Definition assn_sub V a Q : Assertion :=
  fun (st : state) =>
    Q (update st V (aeval st a)).
*)

definition assn_sub :: "id \<Rightarrow> aexp' \<Rightarrow> assertion \<Rightarrow> assertion" where
"assn_sub V a Q \<equiv> (\<lambda> st. Q (update st V (aeval' st a)))"

(* 
(** The proof rule for assignment: 
[[[
      ------------------------------
      {{assn_sub V a Q}} V::=a {{Q}}
]]]
*)

Theorem hoare_asgn : forall Q V a,
  {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.
*)

theorem hoare_asgn : "{{assn_sub V a Q}} (V ::= a) {{Q}}"
by (auto simp: assn_sub_def hoare_triple_def elim: ceval.cases)

(* CL:  We don't actually need the full power of auto here.
        once we apply the cases, we just finish every goal by simplification *)

theorem "{{assn_sub V a Q}} (V ::= a) {{Q}}"
unfolding assn_sub_def hoare_triple_def
apply clarsimp
apply (erule ceval.cases, simp+)
done 
(* 
(** Here's a first formal proof using this rule: *)

Example assn_sub_example : 
  {{fun st => 3 = 3}} (X ::= (ANum 3)) {{fun st => st X = 3}}.
Proof.
  assert ((fun st => 3 = 3) = 
          (assn_sub X (ANum 3) (fun st => st X = 3))). 
  Case "Proof of assertion".
    unfold assn_sub. reflexivity.
  rewrite -> H. apply hoare_asgn.  Qed.
*)

(* CL:  here's a proof using hoare_asgn *)
lemma "{{\<lambda> st. (3 :: nat) = 3}} (X ::= (ANum' 3)) {{\<lambda> st. st X = 3}}"
apply (subgoal_tac "(\<lambda> st. (3 :: nat) = 3) = (assn_sub X (ANum' 3) (\<lambda> st. st X = 3))")
prefer 2
apply (simp add: assn_sub_def)
apply simp
apply (rule hoare_asgn)
done

(* 
(** Unfortunately, the [hoare_asgn] rule doesn't literally apply
    to the initial goal: it only works with triples whose
    precondition has precisely the form [assn_sub Q V a] for some
    [Q], [V], and [a].  So we start with asserting a little lemma
    to get the goal into this form. *)

(** Doing this kind of fiddling with the goal state every time we
    want to use [hoare_asgn] would get tiresome pretty quickly.
    Fortunately, there are easier alternatives.  One simple one is
    to state a slightly more general theorem that introduces an
    explicit equality hypothesis: *)

Theorem hoare_asgn_eq : forall Q Q' V a,
     Q' = assn_sub V a Q ->
     {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H. rewrite H. apply hoare_asgn.  Qed.
*)

theorem hoare_asgn_eq : "Q' = assn_sub V a Q \<Longrightarrow> {{Q'}} (V ::= a) {{Q}}"
by (simp add: hoare_asgn)

(* 
(** With this version of [hoare_asgn], we can do the proof much
    more smoothly. *)

Example assn_sub_example' : 
  {{fun st => 3 = 3}} (X ::= (ANum 3)) {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn_eq. reflexivity.  Qed.
*)

lemma "{{\<lambda> st. (3::nat)=3}} (X ::= (ANum' 3)) {{\<lambda> st. st X = 3}}"
by (rule hoare_asgn_eq, simp add: assn_sub_def)

(* 
(** **** Exercise: 2 stars (hoare_asgn_examples) *)
(** Translate these informal Hoare triples
[[
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}

       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
   into formal statements and use [hoare_asgn_eq] to prove
   them. *)
(* SOLUTION: *)
Example assn_sub_ex1 : 
  {{ fun st => st X + 1 <= 5 }}  
  (X ::= APlus (AId X) (ANum 1))
  {{ fun st => st X <= 5 }}.
Proof.
  apply hoare_asgn_eq. reflexivity.  Qed.

Example assn_sub_ex2 :
  {{ fun st => 0 <= 3 /\ 3 <= 5 }}  
  (X ::= (ANum 3))
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  apply hoare_asgn_eq. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars (hoarestate2) *)
(** If the assignment rule still seems "backward", it may help to
    think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
[[
      {{ True }} X ::= a {{ X = a }}
]]
    Explain what is wrong with this rule.

    (* SOLUTION: *)

    The underlying problem is that the state in which the
    postcondition will be checked is different than the state in which
    [a] was evaluated when it was assigned to [X].  If [a] itself
    mentions [X], then the value of [a] may be different in the final
    state because of this update.  (For example, if [Q] is [[a] is [X
    + 1], then setting [X] to [a] certainly does not achieve the
    postcondition [X = X + 1]!)  Another problem is that the rule
    achieves _only_ the postcondition [X = a].  It tells us nothing
    about any other facts that might have been true about the initial
    state and would still be true in the final state (because they had
    to do with different variables, for example).  So this rule would
    not be useful in reasoning about compound programs.
*)
(** [] *)
*)

theorem hoare_asgn_weakest : "{{P}} (V ::= a) {{Q}} \<Longrightarrow> (\<forall> st. P st \<longrightarrow> assn_sub V a Q st)"
by (auto simp: assn_sub_def hoare_triple_def)

theorem "{{P}} (V ::=a) {{Q}} \<Longrightarrow> (\<forall> st. P st \<longrightarrow> assn_sub V a Q st)"
unfolding hoare_triple_def assn_sub_def
apply clarsimp
apply (erule_tac x="st" in allE)
apply (erule_tac x="update st V (aeval' st a)" in allE) 
apply (subgoal_tac "ceval (V ::= a) st (update st V (aeval' st a))")
apply simp
apply (rule E_Ass, simp)
done

(* 
(** **** Exercise: 2 stars, optional (hoare_asgn_weakest) *)
(** The precondition in the rule hoare_asgn is in fact the weakest
    precondition.
*)
Theorem hoare_asgn_weakest : forall P V a Q,
  {{P}} (V ::= a) {{Q}} ->
  forall st, P st -> assn_sub V a Q st.
Proof.
(* SOLUTION: *)
  unfold hoare_triple.
  intros P V a Q HE st H1.
  unfold assn_sub.
  apply HE with (st:=st).
    apply E_Ass. reflexivity.
    assumption.
Qed.
(* [] *)


(* ####################################################### *) 
(** *** Consequence *)

(** The above discussion about the awkwardness of applying the
    assignment rule illustrates a more general point: sometimes
    the preconditions and postconditions we get from the Hoare
    rules won't quite be the ones we want -- they may (as in the
    above example) be logically equivalent but have a different
    syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker or
    stronger than the goal.

    For instance, while
[[
      {{3 = 3}} X ::= 3 {{X = 3}},
]]
    is a valid Hoare triple, what we probably have in mind when
    we think about the effect of this assignment is something
    more like this:
[[
      {{True}} X ::= 3 {{X = 3}}.
]]
    This triple is also valid, but we can't derive it from
    [hoare_asgn] (or [hoare_asgn_eq]) because [True] and [3 = 3]
    are not equal, even after simplification.

    In general, if we can derive [{{P}} c {{Q}}], it is valid to
    change [P] to [P'] as long as [P'] is still enough to show
    [P], and change [Q] to [Q'] as long as [Q] is enough to show
    [Q'].

    This observation is captured by the following _Rule of
    Consequence_.
[[[
                {{P'}} c {{Q'}}
         P implies P' (in every state)
         Q' implies Q (in every state)
         -----------------------------
                {{P}} c {{Q}}
]]]
   For convenience, here are two more consequence rules -- one
   for situations where we want to just strengthen the
   precondition, and one for when we want to just loosen the
   postcondition.
[[[
                {{P'}} c {{Q}}
         P implies P' (in every state)
         -----------------------------
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
         Q' implies Q (in every state)
         -----------------------------
                {{P}} c {{Q}}
]]]
 *)
*)

theorem hoare_consequence : "{{P'}} c {{Q'}} \<Longrightarrow> (\<forall> st. P st \<longrightarrow> P' st) 
                                             \<Longrightarrow> (\<forall> st. Q' st \<longrightarrow> Q st)
                                             \<Longrightarrow> {{P}} c {{Q}}"
by (auto simp: hoare_triple_def)

theorem "\<lbrakk>{{P'}} c {{Q'}}; (\<And> st. P st \<Longrightarrow> P' st); (\<And> st. Q' st \<Longrightarrow> Q st)\<rbrakk>
                                             \<Longrightarrow> {{P}} c {{Q}}"
unfolding hoare_triple_def
by simp

(* 
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q.  apply (Hht st st'). assumption. 
  apply HPP'. assumption.  Qed.
*)

theorem hoare_consequence_pre : "{{P'}} c {{Q}} \<Longrightarrow> (\<forall> st. P st \<longrightarrow> P' st)
                                                \<Longrightarrow> {{P}} c {{Q}}"
by (auto intro: hoare_consequence)

(* 
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  (forall st, P st -> P' st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  apply hoare_consequence with (P' := P') (Q' := Q);
    try assumption. 
  intros st H. apply H.  Qed.
*)

theorem hoare_consequence_post : "{{P}} c {{Q'}} \<Longrightarrow> (\<forall> st. Q' st \<longrightarrow> Q st)
                                                 \<Longrightarrow> {{P}} c {{Q}}"
by (auto intro: hoare_consequence)

(* 
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  apply hoare_consequence with (P' := P) (Q' := Q');
    try assumption.
  intros st H. apply H.  Qed.

(** For example, we might use (the "[_pre]" version of) the
    consequence rule like this:
[[
                {{ True }} =>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
]]
    Or, formally... 
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre 
    with (P' := (fun st => 1 = 1)).
  apply hoare_asgn_eq.  reflexivity.
  intros st H. reflexivity.
Qed.
*)
lemma "{{\<lambda> st. True}} (X ::= (ANum' 1)) {{\<lambda> st. st X = 1}}"
apply (rule hoare_consequence_pre [of "\<lambda> st. (1 :: nat) = 1"])
by (auto intro: hoare_asgn_eq simp: assn_sub_def)

lemma "{{\<lambda> st. True}} (X ::= (ANum' 1)) {{\<lambda> st. st X = 1}}"
apply (rule hoare_consequence_pre [of "\<lambda> st. (1 :: nat) = 1"])
apply (rule hoare_asgn_eq)
apply (simp add: assn_sub_def)
apply simp
done
(* 

(* ####################################################### *)
(** *** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature
    of Coq.  Having to write [P'] explicitly in the example above
    is a bit annoying because the very next thing we are going to
    do -- applying the [hoare_asgn] rule -- is going to determine
    exactly what it should be.  We can use [eapply] instead of
    [apply] to tell Coq, essentially, "The missing part is going
    to be filled in later." *)

Example hoare_asgn_example1' :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn. 
  intros st H. reflexivity.  Qed. 
*)

(* CL:  In general, applications of rule & drule can have free quantified variables that
        they will introduce.  These operate somewhat like the free variables introduced by eapply 
        Isabelle, by default, acts more like eapply than apply
*)

(* 
(** In general, [eapply H] tactic works just like [apply H]
    except that, instead of failing if unifying the goal with the
    conclusion of [H] does not determine how to instantiate all
    of the variables appearing in the premises of [H], [eapply H]
    will replace these variables with _existential variables_
    (written [?nnn]) as placeholders for expressions that will be
    determined (by further unification) later in the proof. 

    There is also an [eassumption] tactic that works similarly. *)

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
[[[
      --------------------
      {{ P }} SKIP {{ P }}
]]]
*)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple. intros P st st' H HP. inversion H. subst.
  assumption.  Qed.
*)

(* CL:  TODO - put the following theorem in Imp.thy as a default simp rule! *)
theorem skip_eq [simp]: "ceval SKIP st st' \<Longrightarrow> st = st'"
by (erule ceval.cases, auto)

theorem hoare_skip : "{{P}} SKIP {{P}}"
unfolding hoare_triple_def
apply (intro allI impI)
apply (drule skip_eq)
by simp

(* CL:  Find out why I had to do the two applies of auto instead of forcing
        st = st' by skip_eq right away *)

(* 
(* ####################################################### *) 
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
[[[
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------
       {{ P }} c1;c2 {{ R }}
]]]
*)
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.  
  apply (H2 st st'0); try assumption. Qed.
*)

theorem hoare_seq : "\<lbrakk>{{Q}} c2 {{R}};{{P}} c1 {{Q}}\<rbrakk> \<Longrightarrow> {{P}} (c1 ;; c2) {{R}}"
apply (auto simp: hoare_triple_def intro: ceval.intros)
apply (erule ceval.cases)
by auto

(* 
(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches
    the natural flow of information in many of the situations
    where we'll use the rule. *)

(** Informally, a nice way of recording a proof using this rule
    is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
[[
                   {{ a = n }}
    X ::= a;
                   {{ X = n }}        <---- Q
    SKIP
                   {{ X = n }}
]]
*)
Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.  subst.  reflexivity. Qed.

(** **** Exercise: 2 stars (hoare_asgn_example4) *)
(** Translate this decorated program into a formal proof:
[[
                   {{ True }} =>
                   {{ 1 = 1 }}
    X ::= 1;
                   {{ X = 1 }} =>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
]]
*)
*)

lemma "{{\<lambda> st. True}} (X ::= (ANum' 1) ;; Y ::= (ANum' 2))
       {{\<lambda> st. (st X =1) \<and> (st Y = 2)}}"
apply (rule hoare_seq [of "\<lambda> st. st X = 1"])
apply (rule hoare_consequence_pre [of "\<lambda> st. (st X = 1) \<and> ((2 :: nat) = 2)"])
apply (rule hoare_asgn_eq)
apply (simp add: assn_sub_def)
apply simp
apply (rule hoare_consequence_pre [of "\<lambda> st. (1::nat)=1"])
apply (rule hoare_asgn_eq)
apply (simp add: assn_sub_def)
apply simp
done

(*
Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* SOLUTION: *)
  apply hoare_seq with (Q := fun st => st X = 1).
  SCase "right part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.
    split.
      rewrite update_neq; auto.
      apply update_eq. 
  SCase "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H. unfold assn_sub. apply update_eq.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (swap_exercise) *)
(** Write an IMP program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
[[
      {{X <= Y}} c {{Y <= X}}
]]
*)

*)

(* 
(* SOLUTION: *)
Example swap_exercise : 
  {{fun st => st X <= st Y}} 
  (Z ::= (AId X); X ::= (AId Y); Y ::= (AId Z)) 
  {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq.
  eapply hoare_seq.
  apply hoare_asgn.
  apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assn_sub, update. simpl. 
  intros st H. assumption.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (hoarestate1) *)
(** Explain why the following proposition can't be proven:
[[
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}} (X ::= (ANum 3); Y ::= a) 
         {{fun st => st Y = n}}.
]]
*)
(* SOLUTION: *)
(* The problem is that [X] may occur inside (i.e. be read inside)
   the expression [a]. If this is the case, and if location [X]
   does not contain 3 in the state where the precondition is
   evaluated, then [a] will evaluate to a value other than [n]
   when it is assigned to [Y]. *)
(** [] *)

(* ####################################################### *) 
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
[[[
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
]]]
   However, this is rather weak. For example, using this rule,
   we cannot show that:
[[
                             {{True}} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
                             {{ X <= Y }}
]]
   since the rule tells us nothing about the state in which the
   assignments take place in the then- and else- branches.
   
   But, actually, we can say something more precise.  In the
   "then" branch, we know that the boolean expression [b]
   evaluates to [true], and in the "else" branch, we know it
   evaluates to [false].  Making this information available in
   the premises of the lemma gives us more information to work
   with when reasoning about the behavior of [c1] and [c2] (i.e.,
   the reasons why they establish the postcondtion [Q]).
[[[
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
]]]
*)

(** To interpret this rule formally, we need to do a little work.

    Strictly speaking, what we've written -- [P /\ b] -- is the
    conjunction of an assertion and a boolean expression, which
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn
    b] for the assertion "[b] evaluates to [true] in (a given
    state)." *)

Definition bassn b : Assertion :=
  fun st => beval st b = true.

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    (and prove it correct). *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  unfold hoare_triple.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example : 
  {{fun st => True}} 
  (IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
   FI) 
  {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update. simpl. intros. 
    inversion H.
       symmetry in H1; apply beq_nat_eq in H1. 
       rewrite H1.  omega. 
  Case "Else". 
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update; simpl; intros. omega. 
Qed.


(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops.  Suppose
    we have a loop
[[
      WHILE b DO c END
]]
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
[[
      {{P}} WHILE b DO c END {{Q}} 
]]
    is a valid triple.  

    First of all, let's think about the case where [b] is false
    at the beginning, so that the loop body never executes at
    all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write
[[
      {{P}} WHILE b DO c END {{P}}.
]]
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
[[
      {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
[[[
                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
    The proposition [P] is called an _invariant_.

    This is almost the rule we want, but again it can be improved
    a little: at the beginning of the loop body, we know not only
    that [P] holds, but also that the guard [b] is true in the
    current state.  This gives us a little more information to
    use in reasoning about [c].  Here is the final version of the
    rule:
[[[
               {{P /\ b}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} (WHILE b DO c END) {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  unfold hoare_triple.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction on He, 
     because in the loop case its hypotheses talk about the
     whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  (ceval_cases (induction He) Case); try (inversion Heqwcom); subst.
  
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    destruct IHHe2 as [HP' Hbfalse'].  reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_true. assumption.
    split; assumption.  Qed.

Example while_example : 
  {{fun st => st X <= 3}}
  (WHILE (BLe (AId X) (ANum 2))
   DO X ::= APlus (AId X) (ANum 1) END)
  {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn,  assn_sub. intros.  rewrite update_eq. simpl. 
     destruct H as [_ H0].  simpl in H0. apply ble_nat_true in H0.  omega. 
  unfold bassn. intros.  destruct H.  simpl in H0.  remember (ble_nat (st X) 2) as le.  destruct le. 
     apply ex_falso_quodlibet. apply H0; reflexivity.  
     symmetry in Heqle. apply ble_nat_false in Heqle. omega. 
Qed.


(** We can also use the WHILE rule to prove the following Hoare triple, 
which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} (WHILE BTrue DO SKIP END) {{Q}}.
Proof.
  intros P Q c.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. constructor. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    unfold bassn in Hguard. destruct Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Actually, this result shouldn't be surprising.  If we look back at
the definition of hoare_triple, we can see that it asserts something 
meaningful _only_ when the command terminates. *)

(* Print hoare_triple.  *)

(** If the command doesn't terminate, we can prove anything we like
about the post-condition.  Here's a more direct proof of the same
fact: *)

Theorem always_loop_hoare' : forall P Q,
  {{P}} (WHILE BTrue DO SKIP END) {{Q}}.
Proof.  
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra. 
Qed.

(** Hoare rules that only talk about terminating commands are often
said to describe a logic of "partial" correctness.  It is also possible
to give Hoare rules for "total" correctness, which build in the
fact that the commands terminate. *)

(* ####################################################### *)
(** ** Decorated Programs *)

(** There are only a few places where we actually need to _think_
    when performing a correctness proof in Hoare Logic:

    - the intermediate assertion for a sequential composition
      [c1;c2]

    - the "inner" assertions [P'] and [Q'] in the consequence rules 

    - the invariant of a while loop

    - the outermost pre- and post-conditions. *)

(** (In fact, the last two are the only places where any real
    creativity is required.) *)

(** We can completely remove the need for thinking by decorating
    programs with appropriate assertions in these situations (as
    we've already in several places above).  Such a _decorated
    program_ carries with it an (informal) proof of its own
    correctness.

    Concretely, a decorated program has one of the following forms:

    - null program:
[[
                         {{ P }} 
          SKIP
                         {{ P }} 
]]
    - sequential composition:
[[
                         {{ P }} 
          c1;
                         {{ Q }} 
          c2
                         {{ R }}
]]
      (where [c1] and [c2] are decorated programs such that the
      postcondition of [c1] is equal to the precondition of [c2])

    - assignment:
[[
                         {{ P where a is substituted for V }}  
          V ::= a  
                         {{ P }}
]]
    - conditional:
[[
                         {{ P }} 
          IFB b THEN
                         {{ P /\ b }} 
            c1 
          ELSE
                         {{ P /\ ~b }} 
            c2
          FI
                         {{ Q }}
      (where [c1] and [c2] are decorated programs with the
      same postcondition [Q] and such that the precondition of [c1] is
      [P/\b] and the precondition of [c2] is [P/\~b]) 
]]
    - loop:
[[
                         {{ P }} 
          WHILE b DO
                         {{ P /\ b }} 
            c1 
                         {{ P }}
          END
                         {{ P /\ ~b }} 
]]
      (where [c1] is a decorated program with precondition [P/\b] and
      postcondition [P])

    - consequence:
[[
                         {{ P }} =>
                         {{ P' }} 
          c
                         {{ Q }} 
]]
      (where [c] is a decorated program with precondition [P'] and
      postcondition [Q] and where [P st] implies [P' st] for all
      states [st]) or
[[
                         {{ P }} 
          c
                         {{ Q' }} =>
                         {{ Q }} 
]]
      (where [c] is a decorated program with precondition [P] and
      postcondition [Q'] and where [Q' st] implies [Q st] for all
      states [st]).
*)

(** For example, here is a complete decorated program:
[[
                                 {{ True }} =>
                                 {{ x = x }}
    X ::= x; 
                                 {{ X = x }} => 
                                 {{ X = x /\ z = z }}
    Z ::= z;              
                                 {{ X = x /\ Z = z }} =>
                                 {{ Z - X = z - x }}
    WHILE X <> 0 DO
                                 {{ Z - X = z - x /\ X <> 0 }} =>
                                 {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;               
                                 {{ Z - (X - 1) = z - x }}
      X ::= X - 1 
                                 {{ Z - X = z - x }} 
    END;
                                 {{ Z - X = z - x /\ ~ (X <> 0) }} =>
                                 {{ Z = z - x }} =>
                                 {{ Z + 1 = z - x + 1 }}
    Z ::= Z + 1
                                 {{ Z = z - x + 1 }}
]]
*)

(* ####################################################### *)
(** *** Exercise: Hoare Rules for [REPEAT] *)

Module RepeatExercise.

(** **** Exercise: 4 stars (hoare_repeat) *)
(** In this exercise, we'll add a new constructor to our language of
    commands: [CRepeat].  You will write the evaluation rule for
    [repeat] and add a new hoare logic theorem to the language for
    programs involving it.
 
    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once.
*)
Tactic Notation "com_cases" tactic(first) tactic(c) :=
  first;
  [ c "SKIP" | c "::=" | c ";" | c "IFB" | c "WHILE" | c "CRepeat"].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "V '::=' a" := 
  (CAss V a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n V,
      aeval st a1 = n ->
      ceval st (V ::= a1) (update st V n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* SOLUTION: *)
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''
.

Tactic Notation "ceval_cases" tactic(first) tactic(c) := first; [
    c "E_Skip" | c "E_Ass" | c "E_Seq" | c "E_IfTrue" | c "E_IfFalse" 
  | c "E_WhileEnd" | c "E_WhileLoop" 
(* SOLUTION: *)
  | c "E_RepeatEnd" | c "E_RepeatLoop" 
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '==>' st'" := (ceval st c1 st') (at level 40, st at level 39).
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', (c / st ==> st') -> P st -> Q st'.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90).

(** Now state and prove a theorem, [hoare_repeat], that expresses an
     appropriate proof rule for [repeat] commands.  Use [hoare_while]
     as a model. *)
(* SOLUTION: *)
Lemma hoare_repeat : forall P b c,
  {{P}} c {{P}} ->
  {{P}} (REPEAT c UNTIL b END) {{fun st => P st /\ bassn b st}}.
Proof.
  unfold hoare_triple. 
  intros P b c H st st' He HP.
  remember (REPEAT c UNTIL b END) as rcom.
  (ceval_cases (induction He) Case); try (inversion Heqrcom); subst.
  Case "E_RepeatEnd".
    split. apply H with st. assumption. assumption.
    unfold bassn. assumption.
  Case "E_RepeatLoop".
    assert (P st'' /\ bassn b st'') as C2.
      SCase "Proof of assertion". apply IHHe2. 
      (* the two [try]s here are for compatibility between Coq 8.1 and 8.2 *)
      try reflexivity.  
      apply H with st. assumption. assumption.
      try reflexivity.
    destruct C2. 
    split. assumption. assumption.  Qed.

End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** * Using Hoare Logic to Reason About Programs *)

(* ####################################################### *)
(** ** Miscellaneous Lemmas *)

(** Formal Hoare-logic proofs often require a bunch of small algebraic
    facts, most of which we wouldn't even bother writing down in an
    informal proof.  This is a bit clunky in Coq (though it can be
    improved quite a bit using some of the automation features we
    haven't discussed yet).  The best way to deal with it for now is
    to break them out as separate lemmas so that they don't clutter
    the main proofs.  Here we collect a bunch of properties that we'll
    use in the examples below. *)


(* ####################################################### *)
(** ** Example: Slow subtraction *)

(** Informally:
[[
                                  {{ X = x /\ Z = z }} =>
                                  {{ Z - X = z - x }}
    WHILE X <> 0 DO
                                  {{ Z - X = z - x /\ X <> 0 }} =>
                                  {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;
                                  {{ Z - (X - 1) = z - x }}
      X ::= X - 1
                                  {{ Z - X = z - x }} 
    END
                                  {{ Z - X = z - x /\ ~ (X <> 0) }} =>
                                  {{ Z = z - x }}
]]
*)

(** Formally: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= AMinus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition subtract_slowly_invariant x z := 
  fun st => minus (st Z) (st X) = minus z x.
  
Theorem subtract_slowly_correct : forall x z,
  {{fun st => st X = x /\ st Z = z}} 
  subtract_slowly 
  {{fun st => st Z = minus z x}}.
Proof.
  (* Note that we do NOT unfold the definition of hoare_triple
     anywhere in this proof!  The goal is to use only the hoare
     rules.  Your proofs should do the same. *)

  intros x z. unfold subtract_slowly.
  (* First we need to transform the pre and postconditions so
     that hoare_while will apply.  In particular, the
     precondition should be the loop invariant. *)
  eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
  apply hoare_while.

  Case "Loop body preserves invariant".
    (* Split up the two assignments with hoare_seq - using eapply 
       lets us solve the second one immediately with hoare_asgn *)
    eapply hoare_seq. apply hoare_asgn.
    (* Now for the first assignment, transform the precondition
       so we can use hoare_asgn *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Finally, we need to justify the implication generated by
       hoare_consequence_pre (this bit of reasoning is elided in the
       informal proof) *)
    unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
    intros st [Inv GuardTrue].
    (* There are several ways to do the case analysis here...this one is fairly general: *)
    remember (beq_nat (st X) 0) as Q; destruct Q. 
     inversion GuardTrue.
     symmetry in HeqQ.  apply beq_nat_false in HeqQ. omega. (* slow but effective! *)
  Case "Initial state satisfies invariant".
    (* This is the subgoal generated by the precondition part of our
       first use of hoare_consequence.  It's the first implication
       written in the decorated program (though we elided the actual
       proof there). *)
    unfold subtract_slowly_invariant.
    intros st [HX HZ]. omega.  
  Case "Invariant and negated guard imply postcondition".
   (* This is the subgoal generated by the postcondition part of
      out first use of hoare_consequence.  This implication is
      the one written after the while loop in the informal proof. *)
    intros st [Inv GuardFalse].
    unfold subtract_slowly_invariant in Inv.
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* Here's a slightly different alternative for the case analysis that
       works out well here (but is less general)... *)
    destruct (st X). 
      omega. 
      apply ex_falso_quodlibet.   apply GuardFalse. reflexivity. 
    Qed.

(* ####################################################### *)
(** ** Exercise: Reduce to zero *)

(** Here is a while loop that is so simple it needs no invariant: *)

(** 
[[
                                     {{ True }}
        WHILE X <> 0 DO
                                     {{ True /\ X <> 0 }} =>
                                     {{ True }}
          X ::= X - 1
                                     {{ True }}
        END
                                     {{ True /\ X = 0 }} =>
                                     {{ X = 0 }}
]]
   Your job is to translate this proof to Coq.  It may help to look
   at the [slow_subtraction] proof for ideas.
*)

(** **** Exercise: 2 stars (reduce_to_zero_correct) *)
Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct : 
  {{fun st => True}}
  reduce_to_zero
  {{fun st => st X = 0}}.
Proof.
  (* SOLUTION: *)
  unfold reduce_to_zero.
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    eapply hoare_consequence_pre.
    apply hoare_asgn. intros st [HT Hbp].
    unfold assn_sub. apply I.
  Case "Invariant and negated guard imply postcondition".
    intros st [PT Pnbp]. unfold bassn in Pnbp.
    simpl in Pnbp. destruct (st X). reflexivity. apply ex_falso_quodlibet. apply Pnbp. reflexivity. Qed. 
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow addition *)

(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z. *)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(** **** Exercise: 3 stars (add_slowly_decoration) *)
(** Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* SOLUTION: *)
(**
[[
                                 {{ X = x /\ Z = z }} =>
                                 {{ Z + X = z + x }}
  WHILE X <> 0 DO
                                 {{ Z + X = z + x /\ X <> 0 }} =>
                                 {{ (Z + 1) + (X - 1) = z + x }}
     Z ::= Z + 1;
                                 {{ Z + (X - 1) = z + x }}
     X ::= X - 1
                                 {{ Z + X = z + x }}
  END
                                 {{ Z + X = z + x /\ ~ (X <> 0) }} =>
                                 {{ Z = z + x }}
]]
*)
(** [] *)

(** **** Exercise: 3 stars (add_slowly_formal) *)
(** Now write down your specification of [add_slowly] formally, as a
    Coq [Hoare_triple], and prove it valid. *)
(* SOLUTION: *)
Definition add_slowly_invariant x z := 
  fun st => (st Z) + (st X) = z + x.
  
Theorem add_slowly_correct : forall x z,
  {{fun st => st X = x /\ st Z = z}} 
  add_slowly 
  {{fun st => st Z = z + x}}.
Proof.
  intros x z. unfold add_slowly. 
  eapply hoare_consequence.
  apply hoare_while with (P := add_slowly_invariant x z).
  Case "Loop body preserves invariant".    
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold add_slowly_invariant, assn_sub, update, bassn. simpl. 
    intros st [Inv GuardTrue]. 
    destruct (st X). 
      inversion GuardTrue. 
      omega. 
  Case "Initial state satisfies invariant".
    intros st [HX HZ]. unfold add_slowly_invariant.
    rewrite HX. rewrite HZ. reflexivity.
  Case "Invariant and negated guard imply postcondition".    
    unfold add_slowly_invariant, bassn. simpl.
    intros st [Inv GuardFalse].
    destruct (st X). 
      omega. 
      apply ex_falso_quodlibet; apply GuardFalse; reflexivity.  Qed. 
(** [] *)

(* ####################################################### *)
(** ** Example: Parity *)

(** Here's another, slightly trickier example.  Make sure you
    understand the decorated program completely.  Understanding
    all the details of the Coq proof is not required, though it
    is not actually very hard -- all the required ideas are
    already in the informal version, and all the required
    miscellaneous facts about arithmetic are recorded above. *)
(** 
[[
                               {{ X = x }} =>
                               {{ X = x /\ 0 = 0 }}
  Y ::= 0;
                               {{ X = x /\ Y = 0 }} =>
                               {{ (Y=0 <-> ev (x-X)) /\ X<=x }} 
  WHILE X <> 0 DO
                               {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
                               {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    Y ::= 1 - Y;
                               {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    X ::= X - 1
                               {{ Y=0 <-> ev (x-X) /\ X<=x }} 
  END
                               {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
                               {{ Y=0 <-> ev x }}
]]
*)

Lemma minus_pred : forall n m,
  (exists m', m = S m') ->
  m <= n ->
  minus n (pred m) = S (minus n m).
Proof.
  intros n m Hnot0.
  destruct Hnot0 as [m' Heq]. rewrite Heq in *.
  clear Heq m. revert n.
  induction m' as [| m'']; intros n Hle.
  Case "m' = 0".
    simpl. destruct n. inversion Hle. omega.
  Case "m' = S m''".
    simpl. simpl in IHm''.
    destruct n as [| n'].
    SCase "n = 0". inversion Hle.
    SCase "n = S n'".
      simpl. apply IHm''. apply le_S_n. assumption.
Qed.

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition find_parity_invariant x := 
  fun st => 
       st X <= x
    /\ (st Y = 0 /\ ev (x - st X) \/ st Y = 1 /\ ~ev (x - st X)). 

(* It turns out that we'll need the following lemma... *)
Lemma not_ev_ev_S_gen: forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      destruct H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    destruct IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra. 
      destruct H. apply ev_SS. apply contra.  Qed.

Lemma not_ev_ev_S : forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.



Theorem find_parity_correct : forall x,
  {{fun st => st X = x}} 
  find_parity
  {{fun st => st Y = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
  apply hoare_seq with (Q := find_parity_invariant x).
  eapply hoare_consequence.
  apply hoare_while with (P := find_parity_invariant x).
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *.
    rewrite update_eq.
    rewrite (update_neq Y X); auto.
    rewrite (update_neq X Y); auto.
    rewrite update_eq.
    simpl in GuardTrue. destruct (st X). 
      inversion GuardTrue.
    split. omega. 
    replace (S n - 1) with n by omega.
    destruct Inv2 as [[H1 H2] | [H1 H2]] ; [right|left]; (split; [omega |]).
    apply ev_not_ev_S in H2. 
    replace (S (x - S n)) with (x-n) in H2 by omega. 
    assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by omega.
    assumption.
  Case "Precondition implies invariant".
    intros st H. assumption.
  Case "Invariant implies postcondition".
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (st X).
      split; intro.   
        destruct Inv2.  
           destruct H0. replace (x-0) with x in H1 by omega. assumption.
           destruct H0.  rewrite H in H0. inversion H0. 
        destruct Inv2. 
           destruct H0. assumption. 
           destruct H0. replace (x-0) with x in H1 by omega. apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
  Case "invariant established before loop".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst. 
    split.
    omega. 
    replace (st X - st X) with 0 by omega. 
    left. split. reflexivity.
    apply ev_0.  Qed.

(** **** Exercise: 3 stars (wrong_find_parity_invariant) *)
(** A plausible first attempt at stating an invariant for [find_parity]
    is the following. *)

Definition find_parity_invariant' x := 
  fun st => 
    (st Y) = 0 <-> ev (x - st X). 

(** Why doesn't this work?  (Hint: Don't waste time trying to answer
    this exercise by attempting a formal proof and seeing where it
    goes wrong.  Just think about whether the loop body actually
    preserves the property.) *)
(* SOLUTION: *) 
(* If [x] is strictly less than [st X], then the loop body does
   _not_ necessarily preserve this property: it changes [Y] from
   [0] to [1] or vice versa but [minus x (st X)] remains
   constant.  *)
(** [] *)

(* ####################################################### *) 
(** ** Example: Finding square roots *)

Definition sqrt_loop : com :=
  WHILE BLe (AMult (APlus (ANum 1) (AId Z)) (APlus (ANum 1) (AId Z))) (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion := 
  fun st => 
       ((st Z) * (st Z)) <= x 
    /\ ~ (((S (st Z)) * (S (st Z))) <= x).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st => 
       st X = x
    /\ ((st Z) * (st Z)) <= x.

Theorem random_fact_1 : forall st,
     (S (st Z)) * (S (st Z)) <= st X ->
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) (APlus (ANum 1) (AId Z))) (AId X)) st.
Proof.
  intros st Hle.  unfold bassn. simpl.
  destruct (st X) as [|x'].
  Case "st X = 0".
    inversion Hle.
  Case "st X = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (ble_nat (plus (st Z) ((st Z) * (S (st Z)))) x')
      as ble.
    destruct ble. reflexivity. 
    symmetry in Heqble. apply ble_nat_false in Heqble.
    unfold not in Heqble. apply Heqble in Hle. destruct Hle.
Qed.

Theorem random_fact_2 : forall st,
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) (APlus (ANum 1) (AId Z))) (AId X)) st ->
     (aeval st (APlus (ANum 1) (AId Z))) * (aeval st (APlus (ANum 1) (AId Z))) <= st X.
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (st X) as [| x'].
  Case "st X = 0".
    inversion Hble.
  Case "st X = S x'".
    apply ble_nat_true in Hble. omega. Qed.

Theorem sqrt_com_correct : forall x,
  {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
Proof.
  intros x.
  apply hoare_seq with (Q := fun st => st X = x).
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (Q := fun st => st X = x /\ st Z = 0).

    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := sqrt_inv x).

      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
        apply hoare_asgn. intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        destruct H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; auto.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.

      SSCase "invariant is true initially".
        intros st H. destruct H as [HX HZ]. 
        unfold sqrt_inv. split. assumption. 
        rewrite HZ. simpl. omega.

      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        destruct H as [HX HP].
        unfold sqrt_inv in HX.  destruct HX as [HX Harith].
        split. assumption. 
        intros contra. apply HP. clear HP. 
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.

    SCase "Z set to 0".
      eapply hoare_consequence_pre. apply hoare_asgn. 
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq; auto.
      apply update_eq.

  Case "assignment of X".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.
    unfold assn_sub. apply update_eq.  Qed.

(** **** Exercise: 3 stars, optional (sqrt_informal) *)
(** Write a decorated program corresponding to the above
    correctness proof. *)

(* SOLUTION: *)
(**
[[ 
                               {{ X=x }} =>
                               {{ X=x /\ 0=0 }}
    Z ::= 0;
                               {{ X=x /\ Z=0 }} =>
                               {{ X=x /\ Z*Z <= x }}
    WHILE (1 + Z) * (1 + Z) <= X DO
                               {{ X=x /\ Z*Z<=x /\ ((1+Z)*(1+Z)<=X) }} =>
                               {{ X=x /\ (1+Z)*(1+Z)<=x }} 
      Z ::= 1 + Z
                               {{ X=x /\ Z*Z<=x }} 
    END
                               {{ X=x /\ Z*Z<=x /\ ~ ((1+Z)*(1+Z)<=X) }} =>
                               {{ Z*Z <= x /\ ~ ((Z+1)*(Z+1) <= x) }}
]]
*)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Factorial *)

Module Factorial.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Recall the factorial Imp program: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

(** **** Exercise: 3 stars, optional (fact_informal) *)
(** Decorate the [fact_com] program to show that it satisfies the
    specification given by the pre and postconditions below.  Just as
    we have done above, you may elide the algebraic reasoning about
    arithmetic, the less-than relation, etc., that is (formally)
    required by the rule of consequence:

(* SOLUTION: *)
[[
                               {{ X = x }} =>
                               {{ X = x /\ x = x }}
  Z ::= X;
                               {{ X = x /\ Z = x }} =>
                               {{ X = x /\ Z = x /\ 1 = 1 }}
  Y ::= 1;
                               {{ X = x /\ Z = x /\ Y = 1 }} =>
                               {{ Y * (real_fact Z) = real_fact x }}
  WHILE Z <> 0 DO
                               {{ Y * (real_fact Z) = real_fact x /\ 
                                  (Z <> 0) }} =>
                               {{ (Y * Z) * (real_fact (Z-1)) = real_fact x }}
    Y ::= Y * Z;
                               {{ Y * (real_fact (Z-1)) = real_fact x }}
    Z ::= Z - 1
                               {{ Y * (real_fact Z) = real_fact x }}
  END
                               {{ Y * (real_fact Z) = real_fact x /\
                                  ~ (Z <> 0) }} =>
                               {{ Y = real_fact x }}
]]
[[
                               {{ X = x }}
  Z ::= X;
  Y ::= 1;
  WHILE Z <> 0 DO
    Y ::= Y * Z;
    Z ::= Z - 1
  END
                               {{ Y = real_fact x }}
]]
*)
(** [] *)


Definition fact_invariant (x:nat) :=
  fun st => (st Y) * (real_fact (st Z)) = real_fact x.

(** **** Exercise: 4 stars, optional (fact_formal) *)
(** Prove formally that fact_com satisfies this specification,
    using your informal proof as a guide.  You may want to state
    the loop invariant separately (as we did in the examples). *)

Theorem fact_com_correct : forall x,
  {{fun st => st X = x}} fact_com
  {{fun st => st Y = real_fact x}}.
Proof.
  (* SOLUTION: *)
  intros x.
  unfold fact_com. 
  apply hoare_seq with (Q := fun st => st X = x /\ st Z = x).
  SCase "set Y and loop".
    apply hoare_seq with (Q := fact_invariant x).
    SSCase "loop".
      unfold fact_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := fact_invariant x).
      SSSCase "loop preserves invariant".
        unfold fact_body. eapply hoare_seq. apply hoare_asgn.
        eapply hoare_consequence_pre. apply hoare_asgn. 
        intros st [Hinv Harith].
        unfold assn_sub. unfold fact_invariant in *.
        remember (update st Y (aeval st (AMult (AId Y) (AId Z)))) as st'.
        simpl. rewrite update_neq; auto.
        rewrite update_eq. rewrite Heqst'. rewrite update_eq.
        rewrite update_neq; auto.
        simpl. unfold bassn in Harith. simpl in Harith. destruct (st Z).
        SSSSCase "z is 0 (contradiction)".
          inversion Harith.
        SSSSCase "z is not 0".
          simpl.
          assert (real_fact (S n) = (S n) * (real_fact n)).
            reflexivity.
          rewrite H in Hinv. rewrite <- Hinv.
          rewrite mult_assoc. rewrite <- minus_n_O.  reflexivity.
      SSSCase "invariant is true initially".
        intros st H. apply H.
      SSSCase "after loop, spec is satisfied".
        intros st [Hinv Harith]. unfold fact_invariant in Hinv.
        unfold bassn in Harith. simpl in Harith.
        destruct (st Z).
        SSSSCase "z is 0". 
          simpl in Hinv. rewrite mult_1_r in Hinv. apply Hinv.
        SSSSCase "z is not 0 (contradiction)".
          destruct Harith. reflexivity.
    SSCase "set Y".
      eapply hoare_consequence_pre. apply hoare_asgn. 
      intros st [HX HZ].
      unfold assn_sub. unfold fact_invariant.
      rewrite update_eq.
      rewrite update_neq; auto. 
      simpl. rewrite HZ. omega.
  SCase "Set Z".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st HX.
    unfold assn_sub. rewrite update_eq.
    rewrite update_neq; auto.  Qed.
(** [] *)
End Factorial.

*)

end