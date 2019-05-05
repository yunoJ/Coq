(** * Induction: Proof by Induction *)

(** Before getting started, we need to import all of our
    definitions from the previous chapter: *)

From LF Require Export Basics.

(** For the [Require Export] to work, Coq needs to be able to
    find a compiled version of [Basics.v], called [Basics.vo], in a directory
    associated with the prefix [LF].  This file is analogous to the [.class]
    files compiled from [.java] source files and the [.o] files compiled from
    [.c] files.

    First create a file named [_CoqProject] containing the following line
    (if you obtained the whole volume "Logical Foundations" as a single
    archive, a [_CoqProject] should already exist and you can skip this step):

      [-Q . LF]

    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory") "[LF]".
    PG and CoqIDE read [_CoqProject] automatically, so they know to where to
    look for the file [Basics.vo] corresponding to the library [LF.Basics].

    Once [_CoqProject] is thus created, there are various ways to build
    [Basics.vo]:

     - In Proof General: The compilation can be made to happen automatically
       when you submit the [Require] line above to PG, by setting the emacs
       variable [coq-compile-before-require] to [t].

     - In CoqIDE: Open [Basics.v]; then, in the "Compile" menu, click
       on "Compile Buffer".

     - From the command line: Generate a [Makefile] using the [coq_makefile]
       utility, that comes installed with Coq (if you obtained the whole
       volume as a single archive, a [Makefile] should already exist
       and you can skip this step):

         [coq_makefile -f _CoqProject *.v -o Makefile]

       Note: You should rerun that command whenever you add or remove Coq files
       to the directory.

       Then you can compile [Basics.v] by running [make] with the corresponding
       [.vo] file as a target:

         [make Basics.vo]

       All files in the directory can be compiled by giving no arguments:

         [make]

       Under the hood, [make] uses the Coq compiler, [coqc].  You can also
       run [coqc] directly:

         [coqc -Q . LF Basics.v]

       But [make] also calculates dependencies between source files to compile
       them in the right order, so [make] should generally be prefered over
       explicit [coqc].

    If you have trouble (e.g., if you get complaints about missing
    identifiers later in the file), it may be because the "load path"
    for Coq is not set up correctly.  The [Print LoadPath.] command
    may be helpful in sorting out such issues.

    In particular, if you see a message like

        [Compiled library Foo makes inconsistent assumptions over
        library Bar]

    check whether you have multiple installations of Coq on your machine.
    It may be that commands (like [coqc]) that you execute in a terminal
    window are getting a different version of Coq than commands executed by
    Proof General or CoqIDE.

    - Another common reason is that the library [Bar] was modified and
      recompiled without also recompiling [Foo] which depends on it.  Recompile
      [Foo], or everything if too many files are affected.  (Using the third
      solution above: [make clean; make].)

    One more tip for CoqIDE users: If you see messages like [Error:
    Unable to locate library Basics], a likely reason is
    inconsistencies between compiling things _within CoqIDE_ vs _using
    [coqc] from the command line_.  This typically happens when there
    are two incompatible versions of [coqc] installed on your
    system (one associated with CoqIDE, and one associated with [coqc]
    from the terminal).  The workaround for this situation is
    compiling using CoqIDE only (i.e. choosing "make" from the menu),
    and avoiding using [coqc] directly at all. *)

(* ###################################################################### *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using a simple argument.  The fact that it is
    also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Admitted.

(** And reasoning by cases using [destruct n] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [destruct n'] to
   get one step further, but since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Admitted.

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.
    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for _all_ numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].
    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n']).  The goal in this case becomes [(S
    n') + 0 = S n'], which simplifies to [S (n' + 0) = S n'], which in
    turn follows from the induction hypothesis. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars (basic_induction) *)

(** Prove the following lemmas using induction. You might need
    previously proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* SOLUTION: *)
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* SOLUTION: *)
  intros n m. induction m as [| m'].
  Case "m = 0".
    simpl. rewrite -> plus_n_O. reflexivity.
  Case "m = S m'".
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* SOLUTION: *)
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.
(** [] *)

(** **** Exercise: 2 stars (double_plus) *)

(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  (* SOLUTION: *)
  intros n.  induction n as [|n']. 
  Case "n = 0".
   reflexivity.
  Case "n = S n'".
   simpl. rewrite plus_comm. simpl. rewrite IHn'.  reflexivity. Qed.
  (** [] *)
  
(** **** Exercise: 2 stars, standard, optional (evenb_S)  

One inconvenient aspect of our definition of [evenb n] is the
recursive call on [n - 2]. This makes proofs about [evenb n]
harder when done by induction on [n], since we may need an
induction hypothesis about [n - 2]. The following lemma gives an
alternative characterization of [evenb (S n)] that works better
with induction: *)

  
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 1 star (destruct_induction) *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].  
(* SOLUTION: *)
   Both are used to perform case analysis on an element of an
   inductively defined type; [induction] also generates an induction
   hypothesis, while [destruct] does not.
*)
(** [] *)


(* ###################################################################### *)
(** * Proofs Within Proofs *)


(** In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). 
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (0 + n = n) as H].  Also note that we mark the proof of
    this assertion with a [Case], both for readability and so that,
    when using Coq interactively, we can see when we're finished
    proving the assertion by observing when the ["Proof of assertion"]
    string disappears from the context.)  The second goal is the same
    as the one at the point where we invoke [assert], except that, in
    the context, we have the assumption [H] that [0 + n = n].  That
    is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** Actually, [assert] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to
    use the commutativity of addition ([plus_comm]) to rewrite one
    into the other.  However, the [rewrite] tactic is a little stupid
    about _where_ it applies the rewrite.  There are three uses of
    [+] here, and it turns out that doing [rewrite -> plus_comm]
    will affect only the _outer_ one. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Admitted.

(** To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Exercise: 4 stars (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* SOLUTION: *)
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite <- plus_comm. reflexivity.
  rewrite -> H. rewrite -> plus_assoc. reflexivity.  Qed.


Theorem mult_m_Sn : forall m n : nat,
 m * (S n) = m + (m * n).
Proof.
  induction m as [| m'].
  Case "m = 0".
    intros n. simpl. reflexivity.
  Case "m = S m'".
    intros n.
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_swap.
    reflexivity.  Qed.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* SOLUTION: *)
  induction m as [| m'].
  Case "m = 0".
    intros n. simpl. rewrite mult_0_r. reflexivity.
  Case "m = S m'".
    intros n.
    simpl.
    rewrite -> mult_m_Sn.
    rewrite -> IHm'.
    reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

(** Prove the following simple fact: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* SOLUTION: *)
  intros n.
  induction n as [| n'].
  Case "n = 0".  simpl. reflexivity.
  Case "n = S n'". 
    assert (H: evenb (S (S n')) = evenb n').
      simpl.  reflexivity.
    rewrite -> H. rewrite -> IHn'.  
    rewrite -> negb_involutive.  reflexivity.  Qed.
(** [] *)

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* SOLUTION: *)
  reflexivity.  Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* SOLUTION: *)
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* SOLUTION: *)
  intros n m p. induction p as [| p'].
  Case "p = 0".
    intros H.
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    intros H.
    simpl. rewrite -> IHp'. reflexivity.
    rewrite -> H. reflexivity.  Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* SOLUTION: *)
  reflexivity.  Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* SOLUTION: *)
  intros n. simpl. rewrite -> plus_0_r.
  reflexivity.  Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* SOLUTION: *)
  intros b c. destruct b.
    destruct c.
      reflexivity.
      reflexivity.
    destruct c.
      reflexivity.
      reflexivity.  Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* SOLUTION: *)
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'.
    rewrite -> plus_assoc.
    reflexivity.  Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* SOLUTION: *)
  intros n m p.  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> mult_plus_distr_r.  rewrite IHn'.  reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl) *)
Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  (* SOLUTION: *)
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap') *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  
   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* SOLUTION: *)
  intros n m p.
  rewrite -> plus_assoc.
  replace (n+m) with (m+n). 
  rewrite plus_assoc.
  reflexivity.  
  apply plus_comm.  Qed.
(** [] *)


(** **** Exercise: 3 stars (binary_commute) *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.
    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

(* SOLUTION: *)
Inductive bin : Type :=
  | BZ : bin
  | T2 : bin -> bin
  | T2P1 : bin -> bin.

Fixpoint incr (m:bin) : bin :=
  match m with
  | BZ      => T2P1 BZ
  | T2 m'   => T2P1 m'
  | T2P1 m' => T2 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | BZ      => O
  | T2   m' => 2 * bin_to_nat m'
  | T2P1 m' => 1 + 2 * bin_to_nat m'
  end.

Theorem bin_to_nat_pres_incr : forall b : bin, 
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [| b' | b'].
  Case "b = 0". 
    reflexivity. 
  Case "b = 2*b'".
    reflexivity.
  Case "b = 1 + 2*b'".
    simpl. rewrite -> IHb'. 
    simpl. rewrite <- plus_n_Sm.
    reflexivity.
Qed.
(** [] *)


(** **** Exercise: 5 stars, advanced (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.
    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.
    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.
    (c) Define a function [normalize] from binary numbers to binary
        numbers such that for any binary number b, converting to a
        natural and then back to binary yields [(normalize b)].  Prove
        it.
    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(* SOLUTION: *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O    => BZ
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.

Fixpoint double_bin (b:bin) : bin :=
  match b with 
  | BZ => BZ
  | _  => T2 b
  end.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | BZ      => BZ
  | T2   b' => double_bin (normalize b')
  | T2P1 b' => T2P1 (normalize b')
  end.

Lemma double_incr : forall b, double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  destruct b.
  Case "BZ". reflexivity.
  Case "T2". reflexivity.
  Case "T2P1". reflexivity.
Qed.

Lemma incr_double : forall b, incr (double_bin b) = T2P1 b.
Proof.
  destruct b.
  Case "BZ". reflexivity.
  Case "T2". reflexivity.
  Case "T2P1". reflexivity.
Qed.

Lemma nat_to_bin_double : forall n, nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite IHn'. rewrite <- double_incr. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b as [|b'|b'].
  Case "BZ". reflexivity.
  Case "T2". simpl.
    rewrite -> plus_0_r.
    rewrite <- double_plus.
    rewrite -> nat_to_bin_double.
    rewrite IHb'.
    reflexivity.
  Case "T2P1". simpl.
    rewrite -> plus_0_r.
    rewrite <- double_plus.
    rewrite -> nat_to_bin_double.
    rewrite IHb'.
    rewrite incr_double.
    reflexivity.
Qed.
(** [] *)

(* ###################################################################### *)
(** * Advanced Material *)

(** ** Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millenia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.
    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.
    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.
    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician might write it something like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].
    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].
    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [induction] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [reflexivity]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars, advanced (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    Proof: (* SOLUTION: *)
       Let natural numbers [n] and [m] be given.  We show [n + m = m +
       n] by induction on [m].
 
       - First, suppose [m = 0].  We must show [n + 0 = 0 + n].  By
         the definition of [+], we know [0 + n = 0], and we have
         already shown (lemma [plus_n_O]) that [n + 0 = 0].  Thus,
         showing [n + 0 = 0 + n] is equivalent to showing [0 = 0],
         which is true by reflexivity.
 
       - Next, suppose [m = S m'] for some [m'], where [n + m'] = [m'
         + n].  We must show that [n + (S m') = (S m') + n].  By the
         definition of [+] and the induction hypothesis, [(S m') + n =
         S (m' + n) = S (n + m')].  It remains to show [n + (S m') = S
         (n + m')], which is precisely lemma [plus_n_Sm].
[]
*)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* SOLUTION: *)
       By induction on [n].
 
       - First, suppose [n = 0].  We must show [true = beq_nat 0 0].  This
         follows directly from the definition of [beq_nat].
 
       - Next, suppose [n = S n'], where [true = beq_nat n' n'].  We
         must show [true = beq_nat (S n') (S n')]. This
         follows directly from the induction hypothesis and the
         definition of [beq_nat].
[]
 *)


(* Wed Jan 9 12:02:44 EST 2019 *)
