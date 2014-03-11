theory Logic 
imports Main Ind begin

(* (** * Logic: Logic in Coq *)
(* Version of 4/8/2010 *)

Require Export Ind. 

(** Like its built-in programming language, Coq's built-in logic
    is extremely small: universal quantification ([forall]) and
    implication ([->]) are primitive, but all the other familiar
    logical connectives -- conjunction, disjunction, negation,
    existential quantification, even equality -- can be defined using
    just these together with the [Inductive] definition facility. *)

(* ########################################################### *)
(** * Quantification and Implication *)

(** In fact, [->] and [forall] are the _same_ primitive! *)

(** Coq's [->] notation is actually just a shorthand for [forall].
    The [forall] notation is more general, because it allows us to
    _name_ the hypothesis. For example, consider this proposition: *)
*)

(* CL:  Okay, so this is totally not true in Isabelle.  Forall and the function
        space are different constructions.  Why?  Because Isabelle is,
        basically, interpreted in set theory.  *)

(*
Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

(** If we had a proof term inhabiting this proposition, it would be a
    function with two arguments: a number [n] and some evidence that
    [n] is even.  But the name [E] for this evidence is not used in
    the rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name.  We could write it like this instead: *)

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

(** Or we can write it in more familiar notation: *)

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

(** This illustrates that "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] is
    represented by the following inductively defined
    proposition. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 
*)

(* CL:  I believe this is, essentially, true in Isabelle given that the object
   level "Prop" is bool.  *)

(*
(** Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ====>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs, namely the propositions [P],[Q] and
    evidence of [P], [Q], and returns as output the evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
    (* Case "left". *) apply ev_0.
    (* Case "right". *) apply ev_SS. apply ev_SS. apply ev_0.  Qed.
*)

(* CL:  Isabelle's emphasis is on introduction and elimination rules. *)

theorem "(ev 0) \<and> (ev 4)"
apply (rule conjI)
apply (rule ev_0)
apply (simp del: refl)
by (rule ev_SS, rule ev_SS, rule ev_0)


theorem "(ev 0) \<and> (ev 4)"
proof (rule conjI)
  show "ev 0" by (rule ev_0)
next
  show "ev 4" by auto
qed

(*
(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ====>  conj (ev 0) (ev 4) ev_0 (ev_SS 2 (ev_SS 0 ev_0))
            : ev 0 /\ ev 4 *)

(** Note that the proof is of the form
[[
    conj (ev 0) (ev 4) (...pf of ev 0...) (...pf of ev 4...)
]]
    which is what you'd expect, given the type of [conj]. *)

(** **** Exercise: 1 star, optional *)
(** The [Case] tactics were commented out in the proof of
    [and_example] to avoid cluttering the proof object.  What would
    you guess the proof object will look like if we uncomment them?
    Try it and see. *)
(** [] *)

(** Just for convenience, we can also use [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.
*)

(* CL:  So there isn't anything quite like split in Isabelle, but you do
        have some fun options for automating the use of introduction rules!
        You can give auto the keyword intro: <list of intro rules>
        or you can specifically do apply (intro <list of intro rules>)
        to apply as many as possible *)



(* 
(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and put this evidence into the
    proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.
*)

(* CL: this use of inversion is, essentially, the application of elim rules
       in Isabelle.  Just as we could use intro for introduction rules, we 
       can use elim for elimination rules*)

theorem "P \<and> Q \<Longrightarrow> P"
apply (elim conjE)
by assumption

(* CL: Equivalently I think you can use the "cases" rule to take apart 
       a hypothesis as we saw in the previous section.  Inversion in Coq
       doesn't seem to exactly correspond to a construct in Isabelle. *)

(*
(** **** Exercise: 1 star, optional *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  split.  
    Case "left". apply proj2 with (P:=P). apply H.
    Case "right". apply proj1 with (Q:=Q). apply H.  Qed.

*)

theorem "P \<and> Q \<Longrightarrow> Q \<and> P"
apply (intro conjI)
by (elim conjE, simp)+

(* CL:  Also, for simple things involving this first order logic manipulation
 we can use a tactic called 'blast'.  Essentially everything in this file
 could be handled by blast outright. *)

theorem "P \<and> Q \<Longrightarrow> Q \<and> P"
by blast

(*
  
(** **** Exercise: 2 stars *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks [H : P /\ (Q /\ R)] down into [HP: P], [HQ : Q]
    and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
     split.  apply HP.  apply HQ.
  apply HR.
Qed.
(** [] *)
*)

theorem "P \<and> (Q \<and> R) \<Longrightarrow> (P \<and> Q) \<and> R"
apply (intro conjI)
apply (elim conjE,simp)+
done

theorem "P \<and> (Q \<and> R) \<Longrightarrow> (P \<and> Q) \<and> R"
by auto
(*


(** **** Exercise: 2 stars *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in the last chapter.  Notice that
   the left-hand conjunct here is the statement we are actually
   interested in; the right-hand conjunct is needed in order to make
   the induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  intros n.
  induction n.
     split.
     intros H.
     apply ev_0.
     intros H.
     inversion H.
     split.
     inversion IHn.
        apply H0.
     intros H.
         inversion H.
         apply ev_SS.
         inversion IHn.
         apply H0.
         unfold even.  apply H1.
Qed.
(** [] *)
*)

primrec even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc n) = (\<not> (even n))"

lemma ev_not_ev : "ev n \<Longrightarrow> \<not> (ev (Suc n))"
apply (induct n set: ev)
apply (rule notI)
apply (erule ev.cases)
apply simp+
apply (intro notI)
apply (erule notE)
apply (erule_tac a="(Suc (Suc (Suc n)))" in ev.cases)
by simp_all

lemma "ev n \<Longrightarrow> \<not> ev (Suc n)"
proof (induct n set: ev)
 case ev_0
  show ?case apply -
   apply (rule notI) 
   apply (erule ev.cases)
   by auto
 case (ev_SS i)
  assume H1 : "\<not> ev (Suc i)"
  have L1:"ev (Suc (Suc (Suc i))) \<Longrightarrow> ev (Suc i)" apply -
     apply (erule ev.cases)
     by (auto intro: ev.intros)
  show ?case using L1 H1 by (auto intro: ev.intros)
qed

(* CL:  I think the above is a lot more idiomatic than the
        apply script.  It's a little verbose, but I think
        the reasoning is pretty clear *)

thm contrapos_np [OF ev_not_ev]
(* 
lemma "(even n \<longrightarrow> ev n) \<and> (even (Suc n) \<longrightarrow> ev (Suc n))"
proof (induct n)
 case 0 
   show ?case proof (intro conjI impI)
               show "even 0 \<Longrightarrow> ev 0" by (rule ev_0)
              next
               show "even (Suc 0) \<Longrightarrow> ev (Suc 0)" by auto
              qed
next
 case (Suc i)
   show ?case using Suc(1) 
     proof (intro conjI impI)
       
qed
*)

theorem "(even n \<longrightarrow> ev n) \<and> (even (Suc n) \<longrightarrow> ev (Suc n))"
apply (induct_tac n)
apply (intro conjI impI)
apply (rule ev_0)
apply simp
apply (intro conjI impI)
apply simp
apply simp
apply (rule ev_SS)
apply simp
done

theorem "(even n \<longrightarrow> ev n) \<and> (even (Suc n) \<longrightarrow> ev (Suc n))"
apply (induct_tac n)
by auto

(*
(* ###################################################### *)
(** ** Iff *)

(** The familiar logical "if and only if" is just the
    conjunction of two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

*)

theorem "P\<longleftrightarrow>Q \<Longrightarrow> P \<longrightarrow> Q"
apply (elim iffE)
by assumption

(* CL:  IFF is a bit different in Isabelle as I don't believe it is fundamentally an inductive construction that is invertable the way it is in Coq *)


(*

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.
*)

theorem "(P \<longleftrightarrow> Q) \<Longrightarrow> (Q \<longleftrightarrow> P)"
apply (intro iffI)
by (erule iffE, erule mp, assumption)+


(*
(** **** Exercise: 1 star (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  intros P.
  split; intros H; apply H.
Qed.
*)
lemma "P \<longleftrightarrow> P"
apply (rule iffI)
by assumption+

(* 
(** Hint: If you have an iff hypothesis in the context, you
    can use [inversion] to break it into two separate
    implications.  (Think about why this works.) *)

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  split; inversion H1 as [PQ QP] ; inversion H2 as [QR RQ].
   intros HP.
      apply QR. apply PQ. apply HP.
   intros HR. 
      apply QP. apply RQ. apply HR.
Qed. 
*)
theorem "\<lbrakk>(P \<longleftrightarrow> Q);(Q \<longleftrightarrow> R)\<rbrakk> \<Longrightarrow> (P \<longleftrightarrow> R)"
by auto

theorem "\<lbrakk>(P \<longleftrightarrow> Q);(Q \<longleftrightarrow> R)\<rbrakk> \<Longrightarrow> (P \<longleftrightarrow> R)"
apply (rule iffI)
apply (erule iffE)+
apply (erule mp)
apply (erule mp)
apply assumption
apply (erule iffE)+
apply (erule mp)
apply (erule (1) mp)
done

(*          
(** [] *)

(** **** Exercise: 2 stars *)
(** We have seen that the families of propositions [MyProp] and [ev]
    actually characterize the same set of numbers (the even ones).
    Prove that [MyProp n <-> ev n] for all [n].  Just for fun, write
    your proof as an explicit proof object, rather than using
    tactics. (_Hint_: you should only need a single line!) *)

Check (fun n => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n)). 

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  (fun n => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n)).
(** [] *)

(** In traditional Coq, propositions phrased with [<->] were a bit
    inconvenient to use as hypotheses or lemmas, because they had to
    be deconstructed into their two directed components in order to be
    applied. Starting in Coq 8.2, using [apply] with an iff proposition 
    appears to do an implicit [inversion] first, so does the right thing
    if _either_ direction is relevant. Unfortunately, this feature isn't
    properly documented, though.  In the rest of the book, we'll just avoid 
    using [iff] very much. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 
*)

(* CL: In Isabelle, the equivalent is *)

(* 
Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P],[Q] and
    evidence of [P], and returns as output, the evidence of [P /\ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for! -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. 

    Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.
*)
theorem "P \<or> Q \<Longrightarrow> Q \<or> P"
apply (erule disjE)
apply (rule disjI2, assumption)
apply (rule disjI1, assumption)
done

(* 
(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [H1 H2]; inversion H1 as [HP1 | HQ]; inversion H2 as [HP2 | HR].
  left.  apply HP1.
  left.  apply HP1.
  left.  apply HP2.
  right.  split;  apply (HQ , HR).
Qed.
(** [] *)

(** **** Exercise: 1 star *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(** ** Digression: Induction Principles for [/\] and [\/] *)

(** The induction principles for conjunction and disjunction are a
    good illustration of Coq's way of generating simplified induction
    principles for [Inductive]ly defined propositions, which we
    discussed in the last chapter.  You try first: *)

(** **** Exercise: 1 star (and_ind_principle) *)
(** See if you can predict the induction principle for conjunction. *)
(* Check and_ind. *)
(** [] *)

(** **** Exercise: 1 star (or_ind_principle) *)
(** See if you can predict the induction principle for disjunction. *)
(* Check or_ind. *)
(** [] *)

Check and_ind.

(** From the inductive definition of the proposition [and P Q]
[[
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
    we might expect Coq to generate this induction principle
[[
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
]]
    but actually it generates this simpler and more useful one:
[[
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
]]
    In the same way, when given the inductive definition of [or P Q]
[[
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
]]
    instead of the "maximal induction principle"
[[
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
]]
    what Coq actually generates is this:
[[
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]] 
*)

(* ################################################### *)
(** ** Relating /\ and \/ with andb and orb *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are obviously analogs, in some sense, of the logical connectives
    [/\] and [\/].  This analogy can be made more precise by the
    following theorems, which show how to translate knowledge about
    [andb] and [orb]'s behaviors on certain inputs into propositional
    facts about those inputs. *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 1 star (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros b c H.
  destruct b; destruct c.
  inversion H.
  right ; reflexivity. left ; reflexivity. left ; reflexivity.
Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b; destruct c.
  left ; reflexivity.
  left ; reflexivity.
  right ; reflexivity.
  inversion H.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c H.
  destruct b ; destruct c.
  inversion H.
  inversion H.
  inversion H.
  split; reflexivity.
Qed.
(** [] *)

(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)

(** **** Exercise: 1 star (False_ind_principle) *)
(** Can you predict the induction principle for falsehood? *)
(* Check False_ind. *)
(** [] *)

(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> plus 2 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  plus 2 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)

(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, we might wonder whether it
    is possible to define truth in the same way.  Naturally, the
    answer is yes. *)

(** **** Exercise: 2 stars *)
(** Define [True] as another inductively defined proposition.  What
    induction principle will Coq generate for your definition?  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.  Alternatively, you may find it easiest
    to start with the induction principle and work backwards to the
    inductive definition.) *)

Inductive True : Prop := TT.
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ====> Prop -> Prop *)

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) should follow from assuming [P]. *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros QF HP.
  apply QF. apply H. apply HP.
Qed.
(** [] *)

(** **** Exercise: 1 star *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P.
  unfold not.
  intros H.  inversion H.
  apply H1; apply H0.
Qed.
(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  intros. inversion H.
  intros.
  apply IHev.
  inversion H0. apply H2.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
(** [] *)

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

(** **** Exercise: 2 stars *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
  intros n n' H.
  Admitted.
  
(** [] *)

(** **** Exercise: 2 stars, optional *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  Here is one way of defining it. *)

Module ExFirstTry.

Inductive ex : forall X:Type, (X->Prop) -> Prop :=
  ex_intro : forall (X:Type) (P: X->Prop),
             forall (witness:X),
             P witness -> 
             ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

    For example, consider this existentially quantified proposition: *)

Definition some_nat_is_even : Prop := 
  ex nat ev.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** However, this is not actually the best way to define [ex]: if we
    do it this way, Coq will generate the following rather complex
    induction axiom: *)

Check ex_ind.
(* ===>  forall Q : (forall X : Type, (X->Prop) -> Prop),
           (forall (X : Type) (P : X->Prop) (witness : X),
                   P witness -> Q X P) ->
           forall (X : Type) (P : X->Prop), ex X P -> Q X P 
   (modulo a little renaming...) *)

(** The reason this happened is that Coq uses the part of the
    [Inductive] declaration between the [:] and the [:=] as the
    argument type [T] for the proposition [P] in the induction
    principle "for all properties [P] over things of type [T], if
    ...(some clause for each constructor)... then [P] holds for
    everything of type [T]." *)

End ExFirstTry.

(** A much simpler induction axiom is generated if we rearrange the
    definition so that the parameters [X] and [P] are introduced at
    the very outside, rather than with the [ex_intro] constructor. *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** (Note that this is the version we saw in class.  The first version
    was added to the notes later.) *)

(** One way to state the effect of this change is to say that we are
    now defining a _parameterized inductively defined proposition_,
    rather than an _inductively defined parameterized proposition_.
    That is, the new [ex] can be thought of as a _function_ that takes
    [X] and [P] and returns an inductively defined proposition: the
    whole inductive definition is inside the body of the function,
    rather than the function being inside the constructor [ex_intro].

    The [ex_intro] constructor gets exactly the same type as
    before: *)

Check ex_intro.
(* ====>  forall (X : Type) (P : X -> Prop) (witness : X), 
          P witness -> ex X P *)

(** But the induction axiom is much simpler and easier to work with,
    because the parameters [X] and [P] are bound once at the beginning
    instead of appearing over and over: *)

Check ex_ind.
(* ===>  forall (X:Type) (P: X->Prop) (Q: Prop),
         (forall witness:X, P witness -> Q) -> 
         ex X P -> 
         Q *)

(** This principle can be understood as follows: If we have a
    function [f] that can construct evidence for [Q] given _any_
    witness of type [X] together with evidence that this witness has
    property [P], then from a proof of [ex X P] we can extract the
    witness and evidence that must have been supplied to the
    constructor, give these to [f], and thus obtain a proof of
    [Q]. *)

(** Next, Coq's notation definition facility can be used to
    introduce more familiar notation for writing existentially
    quantified propositions, exactly parallel to the built-in syntax
    for universally quantified propositions.  Instead of writing [ex
    nat ev] to express the proposition that there exists some number
    that is even, for example, we can write [exists x:nat, ev x].  (It
    is not necessary to understand the details of how the [Notation]
    definition works!) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the same set of tactics as always for
    manipulating existentials.  For example, if to prove an
    existential, we [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, plus n (mult n n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.
(** Note, again, that we have to explicitly give the witness. *)
*)

theorem "\<exists> n. n + (n*n) = (6::nat)"
apply (rule_tac ?x="2" in exI)
by simp

(*
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, 
     plus n (mult n n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
     (exists m, n = plus 4 m) ->
     (exists o, n = plus 2 o).
Proof.
  intros n H. 
  inversion H as [m Hm]. 
  exists (plus 2 m).  
  apply Hm.  Qed.
*)

theorem "(\<exists> m. n = (4::nat)+m) \<Longrightarrow> (\<exists> l. 2+l=n)"
apply (erule exE)
apply (rule_tac ?x="m+2" in exI)
apply simp
done

(*

(** **** Exercise: 1 star *)
(** In English, what does the proposition 
[[
      ex nat (fun n => ev (S n))
]] 
    mean? *)

(* FILL IN HERE *)
(** Complete the definition of the following proof object: *)
Definition p : ex nat (fun n => ev (S n)) := ex_intro nat (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(** [] *)

(** **** Exercise: 1 star *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P H.
  unfold not.  intros.
  inversion H0.
  apply H1.
  apply H.
Qed.
*)
theorem "(\<forall> x. P x) \<longrightarrow> \<not> (\<exists> x. \<not> (P x))"
apply (intro impI notI)
apply (elim exE notE)
apply (erule spec)
done

(*  
(** [] *)

(** **** Exercise: 3 stars, optional *)
(** The other direction requires the classical "law of the excluded
    middle": *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros X P Q.
   split; intros H.
   inversion H.
   inversion H0.
   left.
   exists witness. apply H1.
   right; exists witness; apply H1.
   inversion H.
   inversion H0.
   exists witness.
   left ; apply H1.
   inversion H0.
   exists witness.
   right ; apply H1.
Qed.
*)

theorem "(\<exists> x. (P x \<or> Q x)) \<longleftrightarrow> (\<exists> x. P x) \<or> (\<exists> x. Q x)"
apply (intro iffI)
apply (elim exE disjE)
apply (intro disjI1)
apply (rule_tac ?x="x" in exI)
apply assumption
apply (intro disjI2)
apply (rule_tac ?x="x" in exI)
apply assumption
apply (elim disjE exE)
apply (rule_tac ?x="x" in exI)
apply (rule disjI1, assumption)
apply (rule_tac ?x="x" in exI)
apply (rule disjI2, assumption)
done

(* CL:  I'm not sure whether the Coq or Isabelle version is uglier !! *)

theorem "(\<exists> x. (P x \<or> Q x)) \<longleftrightarrow> (\<exists> x. P x) \<or> (\<exists> x. Q x)"
by blast

(*

(** [] *)

(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (We enclose the definition in a
    module to avoid confusion with the standard library equality,
    which we have used extensively already). *)
*)

(* CL:  Equality in Isabelle is, really and truly, equality of sets. 
        So, yeah, it's a lot less complicated.  *)

(*
Module MyEquality.

Inductive eq (P:Type) : P -> P -> Prop :=
  refl_equal : forall x, eq P x x.

Notation "x = y" := (eq _ x y) (at level 70, no associativity) : type_scope.

(** This is a bit subtle.  The way to think about it is that,
    given a set [P], it defines a _family_ of propositions "[x] is
    equal to [y]," indexed by pairs of values ([x] and [y]) from [P].
    There is just one way of constructing evidence for members of this
    family: by applying the constructor [refl_equal] to two identical
    arguments. *)

(** Now we are down to the bedrock: The primitive feature of Coq that
    makes this definition work is the ability to make an [Inductive]
    declaration with a constructor whose type only permits it to be
    applied to three arguments where the second and third are the
    same.  (Strictly speaking, "the same _modulo simplification_.") *)

(** Here is an alternate definition -- the one that actually appears
    in the Coq standard library. *)

Inductive eq' (P:Type) (x:P) : P -> Prop :=
    refl_equal' : eq' P x x.

Notation "x =' y" := (eq' _ x y) (at level 70, no associativity) : type_scope.

(** **** Exercise: 3 stars, optional *)
(** Verify that the two definitions of equality are equivalent. *)

Theorem two_defs_of_eq_coincide : forall (P:Type) x y,
  eq P x y <-> eq' P x y.
Proof.
  intros P x y.
  split.
  intros H.
  inversion H.
  Admitted.
    
(** [] *)

(** The advantage of the second definition is that the induction
    principle that Coq derives for it is precisely the familiar
    principle of _Leibniz equality_: what we mean when we say "[x] and
    [y] are equal" is that every property on [P] that is true of [x]
    is also true of [y]. *)

Check eq'_ind.
(* ====>  forall (P : Type) (x : P) (P0 : P -> Prop),
             P0 x -> forall y : P, x =' y -> P0 y *)


End MyEquality.

(* ####################################################### *)
(** ** Inversion, Again *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses asserting inductively defined propositions.  Now
    that we've seen that these are actually the same thing, let's
    take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic 

    - takes a hypothesis [H] whose type is some inductively
      defined proposition [P]

    - for each constructor [C] in [P]'s definition

      - generates a new subgoal in which we assume [H] was
        built with [C]

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable
        
      - adds these equalities to the context of the subgoal

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O], immediately solves the subgoal.

   _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be equal!  The [inversion] tactic adds this to the
   context.  *)

(* ####################################################### *)
(** * Relations as Propositions *)

(** A proposition parameterized over a number (like [ev]) can be
    thought of as a _property_ -- i.e., it defines a subset of [nat],
    namely those numbers for which the proposition is provable.  In
    the same way, a two-argument proposition can be thought of as a
    _relation_ -- i.e., it defines a set of pairs for which the
    proposition is provable.  In the next few sections, we explore the
    consequences of this observation. *)

Module LeFirstTry.  

(** We've already seen an inductive definition of one
    fundamental relation: equality.  Another useful one is the "less
    than or equal to" relation on numbers: *)

(** This definition should be fairly intuitive.  It says that
    there are two ways to give evidence that one number is less than
    or equal to another: either observe that they are the same number,
    or give evidence that the first is less than or equal to the
    predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Check le_ind.
(* ===> forall P : nat -> nat -> Prop,
        (forall n : nat, P n n) ->
        (forall n m : nat, le n m -> P n m -> P n (S m)) ->
        forall n n0 : nat, le n n0 -> P n n0 *)
*)

inductive le :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
le_n [intro]: "le n n" |
le_S [intro]: "le n m \<Longrightarrow> le n (Suc m)"

(* CL:  In Coq, when you use inversion absurd cases are automatically tossed out
        but this isn't the case in Isabelle.  In some cases, it can help to use
        the command "inductive_cases" to generate relevant theorems once and
        for all.  In this case, we use it to make the elimination rule that
        if you have "le n 0" in the premise, and n isn't 0, then you can
        derive anything *)

inductive_cases le_0_n [elim]: "le n 0"

thm le_0_n

thm le.induct


(*
End LeFirstTry.

(** This is a fine definition of the [<=] relation, but we can
   streamline it a little by observing that the left-hand argument [n]
   is the same everywhere in the definition, so we can actually make
   it a "general parameter" to the whole definition, rather than an
   argument to each constructor. *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle. *)

Check le_ind.
(* ====>  forall (n : nat) (P : nat -> Prop),
          P n ->
          (forall m : nat, n <= m -> P m -> P (S m)) ->
          forall n0 : nat, n <= n0 -> P n0 *)

(** By contrast, the induction principle that Coq calculates for the
    first definition has a lot of extra quantifiers, which makes it
    messier to work with when proving things by induction.  Here is
    the induction principle for the first [le]: *)

(* Check le_ind.    (the first one above) *)
(* ===> le_ind
            : forall P : nat -> nat -> Prop,
              (forall n : nat, P n n) ->
              (forall n m : nat, LeFirstTry.le n m -> P n m -> P n (S m)) ->
              forall n n0 : nat, LeFirstTry.le n n0 -> P n n0 *)
*)

(*
(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in the previous chapter.  We can [apply] the constructors to
    prove [<=] goals (e.g., to show that [3<=3] or [3<=6]), and we can
    use tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations. *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.
*)

theorem "le 3 3"
by (rule le_n)


(*
Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H1.  Qed.

*)

theorem "le 3 6"
by auto

(*

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** A few more simple relations on numbers *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (mult n n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars *)
(** Define an inductive relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop := 
  totes : forall n m, total_relation n m.
*)

inductive total_relation :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
totes : "total_relation n m"

(* 
Check total_relation_ind.
(** [] *)

(** **** Exercise: 2 stars *)
(** Define an inductive relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop := .
*)

inductive empty_relation :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
totes_empty : "empty_relation x y \<Longrightarrow> empty_relation x y"

(* CL: You're totally not allowed to write an inductive definition with
       no elements.  Instead, you have to introduce a vacous rule for the
       induction that creates the empty set *)

inductive foo :: "nat \<Rightarrow> bool" where
foo : "foo x \<Longrightarrow> foo x"

thm foo.induct

(* CL:  The assumption that you can prove foo x for any x is false, thus
        you can derive anything from it. *)

theorem "foo x \<Longrightarrow> YourMotherNeverLovedYou x"
apply (induct x set: foo)
by assumption

(* CL:  TJC suggested I prove that your mother never loved you, btw *)

(*
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.
*)

inductive R :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 c1 [intro]: "R 0 0 0" |
 c2 [intro]: "R m n l \<Longrightarrow> R (Suc m) n (Suc l)" |
 c3 [intro]: "R m n l \<Longrightarrow> R m (Suc n) (Suc l)" |
 c4 [intro]: "R (Suc m) (Suc n) (Suc (Suc l)) \<Longrightarrow> R m n l" |
 c5 [intro]: "R m n l \<Longrightarrow> R n m l"


(*
(** - Which of the following propositions are provable?
      - [R 1 1 2] YES
      - [R 2 2 6] NOOOOO

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
      No, because c4 allows you to reverse c2 and c3 combined in order 
      to get back reflexivity.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
      c4 gives you reflexivity when combined with 2 and 3, so 
      it's not necessary if you keep c5

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Lemma R_sum1 : forall (o : nat), R o 0 o.
intros o.
induction o.
apply c1.
apply c2.
apply IHo.
Qed.

Lemma R_sum2 : forall (o : nat), R 0 o o.
intros o.
induction o.
apply c1.
apply c3.
apply IHo.
Qed.

Lemma R_sum3 : forall (o m : nat), R 0 m o <-> m=o.
Proof.
   intros o m.
   split.
      intro H.
      induction m.
      inversion H.
      reflexivity.
Admitted.
     

Theorem R_sum : forall (n m o : nat), n + m = o <-> R n m o.
Proof.
  intros n.
  induction n.
  split.
  intros sum.
  simpl in sum.
  rewrite sum.
  apply R_sum2.
  intros H.
  simpl.
    inversion H.
    reflexivity.
    simpl.
Admitted.  
  
*)

(* CL: It might be a good time to remind the reader to use C-c C-f intro
       to let Proof General search for possible intro rules to use here *)

lemma R_1 : "R 0 l l"
apply (induct l)
apply (rule c1)
apply (rule c3)
by assumption

lemma R_2 : "R l 0 l"
apply (induct l)
apply (rule c1)
apply (rule c2)
by assumption

theorem "\<forall> m l. R n m l \<longleftrightarrow> n + m = l"
apply (intro iffI allI)
apply (erule R.induct)
apply simp+
apply (induct n)
apply simp
apply (rule R_1)
apply (rule c4)
apply (rule c2)
apply (rule c2)
apply simp
done

(* CL: auto version! *)

theorem "\<forall> m l. R n m l \<longleftrightarrow> n + m = l"
apply (intro iffI allI)
apply (erule R.induct)
apply auto
apply (induct n)
apply (auto intro: R_1) 
done

(*
(** [] *)

End R.

(** **** Exercise: 4 stars (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
[[
    [1,4,6,2,3]
]]
    is an in-order merge of
[[
    [1,6,2]
]]
    and
[[
    [4,3].
]]

    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).
*)

inductive appears_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
ai_here : "appears_in a (a # t)" |
ai_later : "appears_in a l \<Longrightarrow> appears_in a (b # l)"

(* 
(** ...gives us a precise way of saying that a value [a] appears at
  least once as a member of a list [l]. 

   Here's a warm-up about [appears_in].
*)
*)

lemma appears_in_app : "appears_in x (xs @ ys) = (appears_in x xs \<or> appears_in x ys)"
apply (rule iffI)
apply (induct xs)
apply simp
apply (erule appears_in.cases)
apply (rule disjI1)
apply simp
apply (rule ai_here)
apply simp
apply (erule disjE)
apply (rule disjI1)
apply (erule ai_later)
apply (erule disjI2)
apply (erule disjE)
apply (erule appears_in.induct)
apply (simp)
apply (rule ai_here)
apply (simp)
apply (rule ai_later)
apply (simp)
apply (induct xs)
apply simp
apply simp
apply (erule ai_later)
done

(* CL: Okay, this wasn't the most instructive proof but it was really straight
       forward.  TODO:  Come up with some useful exposition about *why* 
       this kind of proof is really straightfoward and how to get intuition
       for what to do.  *)

(* 


Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) <-> appears_in x xs \/ appears_in x ys.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(**   Now use [appears_in] to define a proposition [disjoint X l1 l2], which 
  should be provable exactly when [l1] and [l2] are lists (with elements of type X) that 
  have no elements in common.
*)
*)

(* 
(* FILL IN HERE *)
(** [] *)

(** Next, use [appears_in] to define an inductive proposition
  [no_repeats X l], which should be provable exactly when [l] is a
  list (with elements of type [X]) where every member is different
  from every other.  For example, [no_repeats nat [1,2,3,4]] and
  [no_repeats bool []] should be provable, while [no_repeats nat
  [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)
(* FILL IN HERE *)
(** [] *)

(** Finally, state and prove one or more interesting theorems relating [disjoint], 
   [no_repeats] and [++] (list append).  *)
(* FILL IN HERE *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
(* FILL IN HERE *)
.

(** Recall the function [forallb], from the exercise
[forall_exists_challenge] in Poly.v: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

(* FILL IN HERE *)
(** [] *)

(* ######################################################### *)
(** ** Digression: More facts about [<=] and [<] *)

(** Let's pause briefly to record several facts about the [<=]
    and [<] relations that we are going to need later in the
    course.  The proofs make good practice exercises. *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
*)

lemma "le 0 n"
apply (induct n)
by (auto intro: le.intros)

(* 
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
Qed.
  

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  intros n m H.
  induction H.
   apply le_n.
   apply le_S.
   apply IHle.
Qed.
*)

lemma "le n m \<Longrightarrow> le (Suc n) (Suc m)"
apply (induct n m rule: le.induct)
by auto

(* 
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros a b.
  generalize dependent a.
  induction b.
  intros a.
     rewrite (plus_0_r).
     apply le_n.
  intros a.
     rewrite <- (plus_n_Sm).
     apply le_S.
     apply IHb.
Qed.
*)

lemma "le a (a+b)"
apply (induct b arbitrary: a)
by auto

(* 
Theorem plus_lt : forall n1 n2 m,
  plus n1 n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  intros n1 n2 m H.
  split.
  induction H.
     unfold lt.
     apply n_le_m__Sn_le_Sm.
     apply le_plus_l.
     unfold lt.
     apply le_S.
     unfold lt in IHle.
     apply IHle.
  induction H.
     unfold lt.
     apply n_le_m__Sn_le_Sm.
     rewrite plus_comm.
     apply le_plus_l.
     unfold lt.
     apply le_S.
     unfold lt in IHle.
     apply IHle.
Qed.
     
  

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof. 
  (* FILL IN HERE *) Admitted.

(** Hint: Do the right induction! *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** * Informal Proofs, Again *)

(** Q: What is the relation between a formal proof of a proposition
       [P] and an informal proof of the same proposition [P]?

    A: The latter should _teach_ the reader how to produce the
       former.

    Q: How much detail is needed?

    A: There is no single right answer; rather, there is a range
       of choices.  

      At one end of the spectrum, we can essentially give the
      reader the whole formal proof (i.e., the informal proof
      amounts to just transcribing the formal one into words).
      This gives the reader the _ability_ to reproduce the formal
      one for themselves, but it doesn't _teach_ them anything.

      At the other end of the spectrum, we can say "The theorem
      is true and you can figure out why for yourself if you
      think about it hard enough."  This is also not a good
      teaching strategy, because usually writing the proof
      requires some deep insights into the thing we're proving,
      and most readers will give up before they rediscover all
      the same insights as we did.

      In the middle is the golden mean -- a proof that includes
      all of the essential insights (saving the reader the hard
      part of work that we went through to find the proof in the
      first place) and clear high-level suggestions for the more
      routine parts to save the reader from spending too much
      time reconstructing these parts (e.g., what the IH says and
      what must be shown in each case of an inductive proof), but
      not so much detail that the main ideas are obscured. 

   Another key point: if we're talking about a formal proof of a
   proposition P and an informal proof of P, the proposition P
   doesn't change.  That is, formal and informal proofs are
   _talking about the same world_ and they must _play by the same
   rules_. *)
*)

end