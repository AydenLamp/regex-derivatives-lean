import Mathlib

section RegexDecidableEq
namespace RegularExpression --I work in the same namespace that Mathlib's definitions are in

/-! This secition provides an instance of
`DecidableEq` on regexes (assuming their language is decidable).
To do this, I need to provide a boolean function that inputs two regexes
and (provably) returns true if they are equal, and false otherwise.

This relates to Constructivist mathmatics (a foundation of mathmatics
that does not use the law of the excluded middle). In non-constructive
(classical) mathmatics, we are allowed to assume that, for any
two objects of any type, those two objects are either equal or not equal.
However, in constructive mathmatics, one has to prove this on a case-by-case basis.
Languages like lean work well with the constructive philosophy, but
lean also provides a way to provide a `DecidableEq` instance for ANY type
automatically, so long as you use the law of the excluded middle by importing
`Classical`.
However, there are good reasons to go the constructive route. The
draw is that, in constructive mathmatics, a proof that something exists
requres that you actually have a function that RETURNS a specific object of that type.
In classical mathmatics, this is not always true becuase you could, say,
assume that the object does Not exist and then find a contradiction.

This project aims to CONSTRUCT the derivitives of regular expressions in such
a way that the derivitives can actually be printed to the user output, rather
than simply reasoning about derivitives without actually creating them,
and so natrually fits in the constructive framework.
-/
notation "star " P => RegularExpression.star P

open  Finset

variable {α} [DecidableEq α] [Fintype α]

/- This function computes the number of operators in a REGEX.-/
@[simp]
def size : RegularExpression α → Nat
| 0 => 0
| 1 => 0
| char _ => 0
| P + Q => P.size + Q.size + 1
| P * Q => P.size + Q.size + 1
| star P => P.size + 1

/-! Here is the boolean predicate defining (syntactic) equality of regexes.
This is effectivly a proof of the law of excluded middle on RegularExpressions.
That is, it proves that any pair of regexes are either equal or not equal.
TODO: move the below explination elseware
Lean functions corrospond to proofs that, ∀ objects of the input type, ∃ an object of the output type
This is not true for functions in all programming languages. It is only true when the language
requires that funcitons always terminate and always return an object of the output type.
Lean's type-checking system is complex enough to ensure that all function always return an output type,
but the proof of termination must be included explicitly.
For most functions, even recursive ones, lean can automatically synthesise a proof of termination
by structural induction for you, but when it cant, you have to add it in yourself,
as I had to do here. -/
set_option linter.unusedVariables false
in
@[simp]
def equal (P Q : RegularExpression α) : Bool :=
  match h : (P, Q) with
  | (0 , 0) => true
  | (1, 1) => true
  | (char a, char b) => if a = b then true else false
  | (star R, star S) =>R.equal S
  | (T * V, R * S) => T.equal R && V.equal S
  | (T + V, R + S) => T.equal R && V.equal S
  | ( _, _) => false

  termination_by (P.size + Q.size)  -- This function always terminates becuase (P.size + Q.size) decreases (invariant)
  decreasing_by  -- we procede by structural induction on the pair of regexes.
    · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]
      omega -- This is simple enough to prove by simplifying using a couple simple lemmas, then applying omega
    · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]
      omega -- Omega is an extremly usefull little proof writing tactic that can automitically prove almost any linear arithmatic statement
    · simp_all; omega
    · simp_all; omega
    · simp_all; omega

/-! I have to prove that the notion of propositional equality (P = Q) of type prop
is true iff my boolean predicate = true.
This allows us to move between the world of proposition, to the
more real, decidable, computable world of boolean equations.
Booleans are more constructive than propositions -/
set_option linter.unusedSectionVars false in
lemma equal_equal {P Q : RegularExpression α} (h : P.equal Q = true) : P = Q := by
  induction P using RegularExpression.recOn generalizing Q with  -- We procede by structural induction on the regex
  -- Case P = zero
  | zero => cases Q with  -- the `cases` tactic takes our goal and splits it into 6 different goals, one for each constructor of regexes.
     -- In the case Q also is zero,
    | zero => rfl -- the goal becomes zero=zero, which is true by reflexivity
    -- in all 5 other cases,
    | _ => simp [equal] at h
     -- We assume `zero.equal Q = true`, and aim to prove `zero = Q`
     -- In each produced goal, `Q` is replaced by our constructor, for example `zero = epsilon`. We now must prove each of these goals individually.
     -- Each of these subgoals can be proven by unfolding the definition of `equal` in our assumption `zero.equal Q = true`.
     -- Now, in every case except for the case where `Q = zero`, `zero.equal Q = true` simplifies to `false = true`, which is a contradiction.
     -- By the principal of logical explosion, a contradiction implies anything, so lean automicacally closes the goal.
  | epsilon => cases Q <;> simp [equal] at h; rfl
  | char a =>
    cases Q with
    | char b =>
        simp [equal] at h; subst h; rfl
    | _ => simp [equal] at h
  | plus P₁ P₂ ih₁ ih₂ => --In proofs by induction, lean automatically provides the inductive hypothesis as assumptions. Here, they are `ih₁` and `ìh₂`
    cases Q with
    | plus Q₁ Q₂ =>
      unfold equal at h
      have h₁ : P₁.equal Q₁ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_left h
      -- `have` statments are mini-proofs of the statement after the `:`.
      --  The proven statment then can be used as an assumption later in the proof
      have h₂ : P₂.equal Q₂ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_right h
      have eq₁ := ih₁ h₁ -- Use the inductive Hyp to get P1 = Q1
      have eq₂ := ih₂ h₂ -- use 2nd inductive Hyp to get P2 = Q2
      simp [eq₁, eq₂] -- subsiting with (P1 = Q1) and (P2 = Q2) is sufficient to prove the goal (reflexitivity is automatic)
    | _ => simp [equal] at h
  | comp P₁ P₂ ih₁ ih₂ =>
    cases Q with
    | comp Q₁ Q₂ =>
      unfold equal at h
      have h₁ : P₁.equal Q₁ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_left h
      have h₂ : P₂.equal Q₂ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_right h
      have eq₁ := ih₁ h₁
      have eq₂ := ih₂ h₂
      simp [eq₁, eq₂]
    | _ => simp [equal] at h
  | «star» P ih =>
    cases Q with
    | «star» Q =>
      unfold equal at h
      have eq' := ih h
      simp [eq']
    | _ => simp [equal] at h

/- A similar lemma -/
set_option linter.unusedSectionVars false in
lemma neq_neq {P Q : RegularExpression α} (h : P.equal Q = false) : P ≠ Q := by
  induction P using RegularExpression.recOn generalizing Q with
  | zero =>
    cases Q <;> (intro contra; try simp [equal] at h;) <;> contradiction
  | epsilon => cases Q <;> (intro contra; simp [equal] at h; try contradiction)
  | char a =>
    cases Q with
    | char b =>
      intro contra; rw [contra] at h; simp [equal] at h
    | _ => intro contra; try contradiction;
  | plus P₁ P₂ ih₁ ih₂ =>
    cases Q with
    | plus Q₁ Q₂ =>
      unfold equal at h
      cases h₁ : P₁.equal Q₁ with
      | false =>
        intro contra; injection contra with he₁ he₂
        exact ih₁ h₁ he₁
      | true =>
        have h₂ : P₂.equal Q₂ = false := by rw [h₁] at h; exact h
        intro contra; injection contra with he₁ he₂
        exact ih₂ h₂ he₂
    | _ => intro contra; contradiction
  | comp P₁ P₂ ih₁ ih₂ =>
    cases Q with
    | comp Q₁ Q₂ =>
      unfold equal at h
      cases h₁ : P₁.equal Q₁ with
      | false =>
        intro contra; injection contra with he₁ _;
        exact ih₁ h₁ he₁
      | true =>
        have h₂ : P₂.equal Q₂ = false := by rw [h₁] at h; exact h
        intro contra; injection contra with _ he₂;
        exact ih₂ h₂ he₂
    | _ =>
      intro contra; contradiction
  | «star» P' ih =>
    cases Q with
    | «star» Q' =>
      -- equal at star is just P'.equal Q'
      unfold equal at h
      -- so h = false gives P' ≠ Q'
      exact λ contra => ih h (by injection contra)
    | _ =>
      intro contra; contradiction

/-! The previous two lemmas can be used to provide lean with an instance of `DecidableEq` for the type RegularExpression.
Lean has a complicated typeclass system that is able to search for this very instance any time Decidable equality on a regularExpression
is required in a later proof. This, in effect, regesters to Lean that we have a function for deciding equality on Regexes.
TODO: show how this is an alternative to classical reasoning and highlight the relation to constructive mathatics. -/
instance decidableEq : DecidableEq (RegularExpression α) := by
  intros P Q
  cases heq : (P.equal Q)
  · apply isFalse; apply neq_neq; exact heq
  · apply isTrue; apply equal_equal; exact heq

end RegularExpression
end RegexDecidableEq

section REPR

/-
This section, like the previous, culmonates in defining an instance of some typeclass of Regexes.
This time, it is for the typeclass `Repr`, which regesters to lean that there is a function for
converting objects to the type Format (just a string with some printing information).
Every time lean tries to print some object to the infoview with an #eval command,
it searches your codebase to find an instance of `Repr` on that objects type, so that it knows how to format it.
Without this instance, #eval applied to a regular expression would give an error.
-/
open Std (Format)
open RegularExpression

variable {α} [alphabet_repr_instance: Repr α] -- We assume that the alphabet has a `Repr` instance already

def regex_reprPrec [H : Repr α] : RegularExpression α → ℕ → Format  -- The naural number `prec` is some printing metadata for presidence.
| 0 => fun _ => Format.text "0"
| 1      => fun _ => Format.text "1"
| char a => fun prec => Format.text "char " ++ (alphabet_repr_instance.reprPrec a prec)
| p + q  => fun prec =>
  let fp := regex_reprPrec p (prec+1)
  let fq := regex_reprPrec q (prec+1)
  Format.text "(" ++ fp ++ Format.text " + " ++ fq ++ Format.text ")"
| p * q  => fun prec =>
  let fp := regex_reprPrec p (prec+1)
  let fq := regex_reprPrec q (prec+1)
  Format.text "(" ++ fp ++ Format.text " * " ++ fq ++ Format.text ")"
| star p => fun prec => regex_reprPrec p prec ++ Format.text "*"

instance regex_repr [Repr α] : Repr (RegularExpression α) where
  reprPrec := regex_reprPrec

end REPR

section RegexDeriv
/-
This section Builds on the implementation of Regex Derivitives in Mathlib.
-/
namespace RegularExpression

open List

variable {α} [DecidableEq α] [HFA : Fintype α] [Repr α] -- Assume that the alphabet is a `Fintype`

/-!
A `Fintype` instance, here called `HFA`, is a structure that carries:
1. A Data structure: A finite list that contains every element of the type `α`. Implemented as a `Finset`
2. A proof that every element of the type `α` appears in this list.
This is a CONSTRUCTIVE structure. As opposed to the structure `set`, which is merely a type
and a predicate on that type, a `Fintype` and `Finset` actually contain a list of every element in the set.
In general, sets can NOT be prited by #eval commands becuase there is no general way of enumerating all elements of a set,
but with `Finset` or `Fintype`, this enumeration is encoded in structure.
-/

set_option linter.unusedSectionVars false

/- Another definition of `deriv` that outputs a `Finset` of `RegularExpression α` containing a single element,
rather than just the RegularExpression. This will make some of the functions later easier to implement.-/
@[simp]
def deriv_finset : RegularExpression α → α →  Finset (RegularExpression α)
  | 0, _ => {0}
  | 1, _ => {0}
  | char a₁, a₂ => if a₁ = a₂ then {1} else {0}
  | P + Q, a => {deriv P a + deriv Q a}
  | P * Q, a => if P.matchEpsilon then {deriv P a * Q + deriv Q a} else {deriv P a * Q}
  | star P, a => {deriv P a * star P}

/- This takes a regular expression `P` as input, and return the finset containing itself and
the `a` derivitive for every `a` in the alphabet -/
def deriv_step (P : RegularExpression α) : Finset (RegularExpression α) :=
  {P} ∪ Finset.biUnion (@Finset.univ α HFA) P.deriv_finset

/- This takes a Finset of regular expressions `S`, and returns a Finset of Regular expressions that is
the union of `deriv_step P` for every `P ∈ S` -/
def deriv_step_set (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  Finset.biUnion S deriv_step

/-! The rest of this section defines a function to Normalize Regexes.
The motivation is that, when iterating Deriv_step_set, the total amount of derivitivies
of any regular expression is finite ONLY when you consider Regexes as being equal
under certain conditions. (you could use the condition that they identify the same language,
but that is difficult to implement and is not necessary).
I will be normalizing by associativity, communitivity, and some identities for multiplying or
adding ones and zeros.-/

/-! To consider all regular expressions equal under associtivity and communitiity of addition,
we create a pipeline that pulls apart a regex of the form `P+Q+R+...` into a list of regular
expressions `[P, Q, R, ...]` using `flattenSum`.
Then, using `cleanSum`, we filter out all duplicates (becuase `P+P = P`)
and all zeros (becuase `0 + P = P`).
Then, using `rebuildSum`, we sort the list by a custom defined total-order.
This total order is defined as `regexLT` and is based on the string encoding of the Regex
given by the `Repr` instance. This way, every regex has a unique key and `rebuildSum`
will have a well-defined order to recombine the elements.-/

/-- Pull apart `P + Q` into a list of “atoms,” recursively. -/
@[simp]
def flattenSum : RegularExpression α → List (RegularExpression α)
| P + Q   => flattenSum P ++ flattenSum Q
| R       => [R]

/-- The language recognized by the list
is the same as the language of the original regex.
More specifically, this is a proof by structural induction that a regularExpression matches a word
iff some element of flattenSum P matches the word -/
@[simp]
lemma flattenSum_sound (P : RegularExpression α) (a : List α) :
    (flattenSum P).any (fun Q => Q.rmatch a) = P.rmatch a := by
  induction P generalizing a with
  | zero => simp only [flattenSum, zero_def, any_cons, zero_rmatch, any_nil, Bool.or_self]
  | epsilon => simp only [flattenSum, one_def, any_cons, any_nil, Bool.or_false]
  | char _ => simp only [flattenSum, any_cons, any_nil, Bool.or_false]
  | plus P Q IHP IHQ =>
    simp_all only [flattenSum, any_append, plus_def]
    have H := add_rmatch_iff P Q a
    rw [← Bool.coe_iff_coe]
    rw [H]
    simp only [Bool.or_eq_true, rmatch_iff_matches']
  | comp P Q IHP IHQ => simp_all only [flattenSum, comp_def, any_cons, any_nil, Bool.or_false]
  | «star» P IHP => simp only [flattenSum, any_cons, any_nil, Bool.or_false]

/-- Erase all `0`, keeping first occurrence. -/
def cleanSumZero (l : List (RegularExpression α)) : List (RegularExpression α) :=
  (l.filter (· ≠ 0))

/- Some element in  `cleanSumZero l` matches the word `a` iff some element of `l` matches `a` -/
@[simp]
theorem cleanSumZero_sound (l : List (RegularExpression α)) (a : List α) :
    (cleanSumZero l).any (fun Q => Q.rmatch a) = l.any (fun Q => Q.rmatch a) := by
  unfold cleanSumZero
  induction l with  -- induction on the length of input the list `l`
  | nil => simp_all
  | cons head tail ih =>
    simp_all only [bne_iff_ne, ne_eq, any_cons]
    by_cases H : head = 0
    · subst H; simp_all;
    · simp_all


/-- Erase all duplicates, keeping first occurrence. -/
def cleanSumDups (l : List (RegularExpression α)) : List (RegularExpression α) :=
  l.eraseDups


@[simp]
theorem cleanSumDups_sound (l : List (RegularExpression α)) (a : List α) :
    (cleanSumDups l).any (fun Q => Q.rmatch a) = l.any (fun Q => Q.rmatch a) := by
  unfold cleanSumDups
  induction l with
  | nil => simp_all only [any_nil, any_eq_false, rmatch_iff_matches', eraseDups]; sorry
  | cons head tail ih =>
    simp_all only [decide_not, any_filter, any_cons, duplicate_cons_self_iff, duplicate_cons_iff]
    rw [← ih]
    simp_all
    sorry

/-- Erase all duplicates, keeping first occurrence. -/
def cleanSum (l : List (RegularExpression α)) : List (RegularExpression α) :=
  cleanSumDups (cleanSumZero l) -- this merely combines the previous two functions

def cleanSum_sound (l : List (RegularExpression α)) (a : List α) :
    (cleanSum l).any (fun Q => Q.rmatch a) = l.any (fun Q => Q.rmatch a) := by
  simp_all only [cleanSum, cleanSumDups_sound, cleanSumZero_sound] --folows from the previous proofs

/-- Pair each regex with its unique “key” = (size, repr‐string). -/
@[simp]
private def regexKey (P : RegularExpression α) : Nat × String :=
  (P.size, toString (reprPrec P 0))

/-- A total order on regex—e.g. -/
def regexLT (P Q : RegularExpression α) : Prop :=
  let (nP, sP) := regexKey P
  let (nQ, sQ) := regexKey Q
  nP < nQ ∨ (nP = nQ ∧ sP < sQ)

/- Tells lean that `regexLT` is DECIDABLE  (i.e., a proof that, for all regexes P Q, P < Q or not)-/
instance decidable_regexLT : @DecidableRel (RegularExpression α) (RegularExpression α) regexLT := by
  intros P Q
  dsimp [regexLT]; infer_instance

/-- Sort, then fold into a single union. -/
def rebuildSum (l : List (RegularExpression α)) : RegularExpression α :=
  match l.mergeSort (fun P Q => decide (regexLT P Q)) with
  | []      => 0
  | x :: xs => xs.foldl (fun acc r => acc + r) x

@[simp]
lemma rebuildSum_sound (l : List (RegularExpression α)) (a : List α) :
  (rebuildSum l).rmatch a = l.any (fun Q => Q.rmatch a) := by
  induction l with
  | nil => simp only [rebuildSum, mergeSort_nil, zero_rmatch, any_nil]
  | cons head tail ih =>
    simp_all [any_cons, rebuildSum]
    rw [← ih]
    sorry

@[simp]
theorem full_rebuild_correct (P : RegularExpression α) (a : List α) :
  (rebuildSum (cleanSum (flattenSum P))).rmatch a = P.rmatch a := by
  simp only [rebuildSum_sound, cleanSum, cleanSumDups_sound, cleanSumZero_sound, flattenSum_sound]

/- TODO: handel mul associativity
NOTE: only the rules for and are necessary (without 0 + r = r)-/
def nf : RegularExpression α → RegularExpression α
| 0         => 0
| 1         => 1
| char a    => char a
| P + Q     => rebuildSum (cleanSum (flattenSum (nf P) ++ flattenSum (nf Q)))
| P * Q     =>
  match nf P, nf Q with
  | 0, _    => 0    -- 0·Q = 0
  | _, 0    => 0    -- P·0 = 0
  | 1, Q'   => Q'   -- 1·Q = Q
  | P', 1   => P'   -- P·1 = P
  | P', Q'  => P' * Q'
| star P    =>
  match nf P with
  | 0       => 1    -- 0* = 1
  | 1       => 1    -- 1* = 1
  | star R' => star R'  -- (R'*)* = R'*
  | R'      => star R'

theorem nf_sound (P : RegularExpression α) (a : List α):
    P.rmatch a = (nf P).rmatch a := by
  induction P generalizing a with
  | zero => simp [nf]
  | epsilon => simp [nf]
  | char _ => simp [nf]
  | plus P Q ihP ihQ =>
    simp_all only [plus_def, nf, rebuildSum_sound, cleanSum_sound, any_append, flattenSum_sound];
    have IHP := ihP a; have I := ihQ a
    have rmatchAdd := add_rmatch_iff P Q a
    refine Bool.coe_iff_coe.mp ?_
    simp_all only [Bool.or_eq_true]
  | comp P Q ihP ihQ =>
    simp_all only [comp_def, nf]
    sorry
  | «star» P ihP =>
    cases P with
    | zero => simp_all [nf]; sorry
    | epsilon => simp_all [nf]; sorry
    | char _ => simp_all [nf]
    | plus R S => simp_all [nf]; sorry
    | comp R S => simp_all [nf]; sorry
    | «star» R => simp_all [nf]; sorry

def normalize_P (P : RegularExpression α) : Finset (RegularExpression α) :=
  {nf P}

def normalize_set (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  Finset.biUnion S normalize_P

def deriv_step_set_nf (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  normalize_set (Finset.biUnion S deriv_step)

def iterate_one (P : RegularExpression α) : Finset (RegularExpression α) :=
  deriv_step_set_nf (normalize_P P)

def iterate_two (P : RegularExpression α) : Finset (RegularExpression α) :=
  deriv_step_set_nf (deriv_step_set_nf (normalize_P P))

def iterate_five (P : RegularExpression α) : Finset (RegularExpression α) :=
  deriv_step_set_nf (deriv_step_set_nf (deriv_step_set_nf (deriv_step_set_nf (deriv_step_set_nf (normalize_P P)))))


end RegularExpression
end RegexDeriv
