import Mathlib

/-! This file extends the definitions and theorems regarding regular expressions
found in Lean's Mathlib library, specifically focusing on Brzozowski derivatives.
The primary goal is to implement functions that allow for the *computation*
and *display* of regular expression derivatives using Lean's `#eval` command.
This involves addressing decidable equality and string representations,
defining derivatives with respect to words (not chars), and implementing a
mechanism to compute the set of all distinct derivatives reachable from an initial
regular expression. A normalization function is introduced to manage the syntactic
variety of equivalent expressions during derivative computation. -/

section RegexDecidableEq

/-! ## Decidable Equality for Regular Expressions
Lean, particularly when used without importing classical logic axioms like
the Law of the Excluded Middle (LEM), adheres to a constructive philosophy.
In constructive mathematics, proving a statement like "P or not P" requires
explicitly showing which case holds. Similarly, to claim that for any two
objects `x` and `y`, either `x = y` or `x ≠ y`, one needs a *decision procedure*:
a terminating function that returns true if they are equal and false otherwise.

Lean formalizes this concept with the `DecidableEq` typeclass. An instance
of `DecidableEq α` for a type `α` provides such a decision procedure for equality
on `α`. This is crucial for computation, as many functions, including pattern
matching in `match` statements, rely on being able to decide equality.

While Lean *can* automatically provide `DecidableEq` instances for any type
if classical logic is assumed (`import Classical`), this project aims to explore
the *computational* aspects of derivatives. We want `#eval` to work by actually
computing results, which aligns well with the constructive approach. Therefore,
we explicitly define a function `equal` that determines syntactic equality
of regular expressions and prove that it correctly decides the propositional
equality `P = Q`. This constructive proof allows Lean to use `#eval` on functions
that need to compare regexes, without resorting to classical axioms.

We assume the underlying alphabet `α` already has decidable equality
`[DecidableEq α]`. -/

namespace RegularExpression

open Finset

variable {α} [DecidableEq α] -- Assume the alphabet has decidable equality

/-! We also temporarily assume the alphabet is finite (`Fintype α`)
for the `size` definition, although `Fintype` is not strictly needed
for decidable equality itself. It is used here for the termination proof
of the `equal` function. -/

variable [Fintype α]

/-- Computes a natural number representing the syntactic size of a regex
(number of operators). This is used purely for the termination proof of the
`equal` function below, ensuring that recursive calls operate on smaller expressions. -/
@[simp]
def size : RegularExpression α → Nat
| 0 => 0
| 1 => 0
| char _ => 0
| P + Q => P.size + Q.size + 1
| P * Q => P.size + Q.size + 1
| star P => P.size + 1

notation "star " P => RegularExpression.star P -- Local notation for star

set_option linter.unusedVariables false
/-- This function determines if two regular expressions `P` and `Q` are *syntactically*
identical. It returns `true` if they have the exact same structure and `false`
otherwise.

It works by recursively comparing the structure of `P` and `Q`.
- Base cases (`0`, `1`, `char a`): Check for direct equality.
- Recursive cases (`+`, `*`, `star`): Return true iff the operators match *and*
  the subexpressions are recursively equal (`equal` returns true for them).
- Mismatch case (`_`, `_`): If the top-level constructors don't match, they are not equal.

A termination proof is required because the function is recursive. Lean cannot
automatically deduce termination for recursion on *pairs* of arguments like this.
We provide a proof (`decreasing_by`) showing that the sum of the `size`s
of the regexes decreases with each recursive call, guaranteeing termination. -/
@[simp]
def equal (P Q : RegularExpression α) : Bool :=
  match h : (P, Q) with
  | (0 , 0) => true
  | (1, 1) => true
  | (char a, char b) => if a = b then true else false
  | (star R, star S) => R.equal S
  | (T * V, R * S) => T.equal R && V.equal S
  | (T + V, R + S) => T.equal R && V.equal S
  | ( _, _) => false
termination_by (P.size + Q.size) -- Termination metric
decreasing_by -- Proof that the metric decreases
  · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]; omega
  · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]; omega
  · simp_all; omega
  · simp_all; omega
  · simp_all; omega

/-! The following two lemmas connect the boolean result of `equal P Q` to the
propositional equality `P = Q`. This is essential for Lean to trust that
our `equal` function correctly reflects the mathematical notion of equality. -/

omit [Fintype α] in
/-- Shows that if `equal P Q` returns `true`, then `P` and `Q` are propositionally equal (`P = Q`). -/
lemma equal_equal {P Q : RegularExpression α} (h : P.equal Q = true) : P = Q := by
  induction P using RegularExpression.recOn generalizing Q with -- Proof by structural induction on P
  | zero => cases Q <;> simp [equal] at h; rfl -- Base case P=0. Use `cases` on Q. If Q=0, trivial. Otherwise, `equal` is false, contradiction.
  | epsilon => cases Q <;> simp [equal] at h; rfl -- Base case P=1. Similar logic.
  | char a => -- Base case P=char a.
    cases Q with
    | char b => simp [equal] at h; subst h; rfl -- If Q=char b, simplify `equal` in h, use the resulting a=b.
    | _ => simp [equal] at h -- Otherwise, `equal` is false, contradiction.
  | plus P₁ P₂ ih₁ ih₂ => -- Inductive step for P = P₁ + P₂
    cases Q with
    | plus Q₁ Q₂ => -- Only case where `equal` might be true is Q = Q₁ + Q₂
      unfold equal at h -- Expand definition of `equal` in h
      -- `equal` uses `&&`, so both parts must be true:
      have h₁ : P₁.equal Q₁ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_left h -- Extract P₁.equal Q₁ = true
      have h₂ : P₂.equal Q₂ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_right h -- Extract P₂.equal Q₂ = true
      have eq₁ := ih₁ h₁ -- Apply inductive hypothesis 1
      have eq₂ := ih₂ h₂ -- Apply inductive hypothesis 2
      simp [eq₁, eq₂] -- Substitute results into goal P₁+P₂ = Q₁+Q₂, which becomes trivial.
    | _ => simp [equal] at h -- Otherwise, `equal` is false, contradiction.
  | comp P₁ P₂ ih₁ ih₂ => -- Inductive step for P = P₁ * P₂. Analogous to the `plus` case.
    cases Q with
    | comp Q₁ Q₂ =>
      unfold equal at h
      have h₁ : P₁.equal Q₁ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_left h
      have h₂ : P₂.equal Q₂ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_right h
      have eq₁ := ih₁ h₁
      have eq₂ := ih₂ h₂
      simp [eq₁, eq₂]
    | _ => simp [equal] at h
  | «star» P ih => -- Inductive step for P = star P'. Analogous to the `plus` case.
    cases Q with
    | «star» Q =>
      unfold equal at h
      have eq' := ih h -- Apply inductive hypothesis
      simp [eq']
    | _ => simp [equal] at h

set_option linter.unusedSectionVars false in
/-- Shows that if `equal P Q` returns `false`, then `P` and `Q` are propositionally unequal (`P ≠ Q`). -/
lemma neq_neq {P Q : RegularExpression α} (h : P.equal Q = false) : P ≠ Q := by
  -- The proof structure mirrors `equal_equal`, but aims for contradiction if P=Q is assumed.
  induction P using RegularExpression.recOn generalizing Q with
  | zero => cases Q <;> (intro contra; try simp [equal] at h;) <;> contradiction
  | epsilon => cases Q <;> (intro contra; simp [equal] at h; try contradiction)
  | char a =>
    cases Q with
    | char b => intro contra; rw [contra] at h; simp [equal] at h -- Assume P=Q (contra), rewrite in h, simplify `equal` to get a contradiction.
    | _ => intro contra; try contradiction;
  | plus P₁ P₂ ih₁ ih₂ =>
    cases Q with
    | plus Q₁ Q₂ => -- Case P = P₁+P₂, Q = Q₁+Q₂
      unfold equal at h -- h is `(P₁.equal Q₁ && P₂.equal Q₂) = false`
      cases h₁ : P₁.equal Q₁ with -- Consider if P₁.equal Q₁ is true or false
      | false => -- If P₁.equal Q₁ is false
        intro contra; injection contra with he₁ he₂ -- Assume P=Q (contra), get P₁=Q₁ and P₂=Q₂
        exact ih₁ h₁ he₁ -- Apply IH1: (P₁.equal Q₁ = false) → P₁ ≠ Q₁. Contradicts P₁=Q₁.
      | true => -- If P₁.equal Q₁ is true
        have h₂ : P₂.equal Q₂ = false := by rw [h₁] at h; exact h -- Since the && was false, P₂.equal Q₂ must be false
        intro contra; injection contra with he₁ he₂ -- Assume P=Q (contra), get P₁=Q₁ and P₂=Q₂
        exact ih₂ h₂ he₂ -- Apply IH2: (P₂.equal Q₂ = false) → P₂ ≠ Q₂. Contradicts P₂=Q₂.
    | _ => intro contra; contradiction -- If Q is not a 'plus', assumption P=Q immediately contradicts structure.
  | comp P₁ P₂ ih₁ ih₂ => -- Analogous to the `plus` case.
    cases Q with
    | comp Q₁ Q₂ =>
      unfold equal at h
      cases h₁ : P₁.equal Q₁ with
      | false => intro contra; injection contra with he₁ _; exact ih₁ h₁ he₁
      | true =>
        have h₂ : P₂.equal Q₂ = false := by rw [h₁] at h; exact h;
        intro contra; injection contra with _ he₂; exact ih₂ h₂ he₂
    | _ => intro contra; contradiction
  | «star» P' ih => -- Analogous to the `plus` case.
    cases Q with
    | «star» Q' =>
      unfold equal at h -- h is `P'.equal Q' = false`
      exact λ contra => ih h (by injection contra) -- Assume P=Q (contra), get P'=Q'. Apply IH: (P'.equal Q' = false) → P' ≠ Q'. Contradiction.
    | _ => intro contra; contradiction

/-- This instance declaration registers our `equal` function and its correctness proofs
(`equal_equal`, `neq_neq`) with Lean's typeclass system. Now, whenever Lean needs
to decide equality between two `RegularExpression α` objects (e.g., in a `match`
statement or certain tactics), it can automatically find and use this instance.
This makes `RegularExpression α` a type with decidable equality, enabling its use
in computational contexts like `#eval`. -/
instance decidableEq : DecidableEq (RegularExpression α) := by
  intros P Q -- Given two regexes P, Q
  cases heq : (P.equal Q) -- Evaluate `P.equal Q`. It's either true or false.
  · apply isFalse; apply neq_neq; exact heq -- If false, use `neq_neq` to prove P ≠ Q.
  · apply isTrue; apply equal_equal; exact heq -- If true, use `equal_equal` to prove P = Q.

end RegularExpression
end RegexDecidableEq


section REPR

/-! ## String Representation for Regular Expressions
To print the result of a computation using `#eval`, Lean needs to know how
to convert the resulting object into a human-readable string format.
The `Repr` typeclass provides this functionality. An instance of `Repr α`
for a type `α` essentially gives Lean a function to turn values of type `α`
into strings.

Without a `Repr` instance for `RegularExpression α`, attempting `#eval` on a
regular expression would result in an error because Lean wouldn't know how
to display it. This section defines such an instance.

We assume the underlying alphabet `α` already has a `Repr` instance.-/

open Std (Format)
open RegularExpression

variable {α} [alphabet_repr_instance: Repr α] -- Assume alphabet is representable

/-- This function recursively builds a `Format` object (a string with layout hints)
representing a regular expression. It defines how each constructor of the
`RegularExpression` type should be printed. -/
def regex_reprPrec : RegularExpression α → ℕ → Format
| 0 => fun _ => Format.text "0"
| 1      => fun _ => Format.text "1"
| char a => fun prec => Format.text "char " ++ (alphabet_repr_instance.reprPrec a prec)
| p + q  => fun prec =>
  let fp := regex_reprPrec p (prec+1)
  let fq := regex_reprPrec q (prec+1)
  Format.paren (fp ++ Format.text " + " ++ fq)
| p * q  => fun prec =>
  let fp := regex_reprPrec p (prec+1)
  let fq := regex_reprPrec q (prec+1)
  Format.paren (fp ++ Format.text " * " ++ fq)
| star p => fun prec => Format.paren (regex_reprPrec p (prec+1) ++ Format.text "*")

/-- This instance registers the `regex_reprPrec` function with Lean's typeclass system.
Now, `#eval` commands involving `RegularExpression α` will use this function
to generate their output string. -/
instance regex_repr [Repr α] : Repr (RegularExpression α) where
  reprPrec := regex_reprPrec

end REPR

section RegexDeriv

/-! ## Brzozowski Derivatives: Computation and Sets
This section builds upon Mathlib's implementation of Brzozowski derivatives.
Mathlib provides the basic definition `deriv : RegularExpression α → α → RegularExpression α`
which computes the derivative with respect to a single character. It also provides
`rmatch : RegularExpression α → List α → Bool` which checks if a regex matches a word,
internally using `deriv`.

Our goal here is to:
1. Extend the derivative definition to handle multi-character words (`deriv_word`).
2. Implement functions to compute the *set* of all unique derivatives reachable
   from a starting regex. This set corresponds to the states of the minimal DFA
   recognizing the language of the regex.
3. Implement a normalization function (`nf`) to simplify regexes during derivative
   computation. This is crucial because the theoretical finiteness of the derivative
   set relies on identifying *equivalent* regexes (e.g., `a+b` and `b+a`), not just
   syntactically identical ones. Normalization helps `#eval` find a smaller,
   stabilizing set of derivatives in practice.

We require the alphabet `α` to have decidable equality (`DecidableEq`),
be representable (`Repr`), and be finite (`Fintype`). `Fintype` provides a
constructive way to iterate over all characters in the alphabet, which is needed
for computing *all* single-character derivatives from a given regex. -/
namespace RegularExpression

open List

variable {α} [DecidableEq α] [HFA : Fintype α] [Repr α]

set_option linter.unusedSectionVars false

/-- Calculates the derivative of a regex `P` with respect to a word (list of characters).
It applies the single-character derivative (`deriv` from Mathlib) recursively
for each character in the word.
- `deriv_word P [] = P` (derivative w.r.t. empty word is the regex itself)
- `deriv_word P (a :: as) = deriv_word (deriv P a) as` (derivative w.r.t `a :: as` is
  derivative w.r.t `as` of the derivative w.r.t `a`). -/
@[simp]
def deriv_word (P : RegularExpression α) (word : List α) : RegularExpression α :=
  match word with
  | [] => P
  | a :: as => deriv_word (deriv P a) as

/-- This theorem states the fundamental connection between the derivative with respect
to a word `w` and matching `w`. A regex `P` matches `w` if and only if
the derivative of `P` with respect to `w` (`P.deriv_word w`) matches the empty
string (`ε`). `matchEpsilon` checks if a regex matches `ε`.
This proof proceeds by induction on the word `a`. -/
theorem deriv_word_iff_rmatch (P : RegularExpression α) (a : List α):
    (P.deriv_word a).matchEpsilon ↔ P.rmatch a := by
  induction a generalizing P with -- Induction on the word `a`
  | nil => simp [deriv_word, rmatch] -- Base case: a = []. Both sides simplify based on definitions.
  | cons head tail ih => simp [rmatch, deriv_word, ih] -- Inductive step: a = head :: tail. Definitions unfold, apply IH.

-- This lemma restates the previous one using Mathlib's `matches'` definition.
lemma deriv_word_correct (P : RegularExpression α) (a : List α):
    (P.deriv_word a).matchEpsilon ↔ a ∈ P.matches' := by
  simp_rw [← rmatch_iff_matches', ← deriv_word_iff_rmatch] -- Rewrite using existing lemmas.

/-! ### Computing the Set of Derivatives

The following functions aim to compute the set of all unique (normalized)
derivatives of a given regular expression. This set forms the states of a
Deterministic Finite Automaton (DFA) equivalent to the regex. -/

/-- A helper function similar to Mathlib's `deriv`, but returns a `Finset`
containing the single resulting derivative. This uniform return type simplifies
the use of `Finset.biUnion` later when collecting derivatives over the whole alphabet.
The logic mirrors `deriv`. -/
@[simp]
def deriv_finset : RegularExpression α → α → Finset (RegularExpression α)
  | 0, _ => {0}
  | 1, _ => {0}
  | char a₁, a₂ => if a₁ = a₂ then {1} else {0}
  | P + Q, a => {deriv P a + deriv Q a}
  | P * Q, a => if P.matchEpsilon then {deriv P a * Q + deriv Q a} else {deriv P a * Q}
  | star P, a => {deriv P a * star P}

/-- Computes the "next step" in the derivative set exploration from a *single* regex `P`.
It returns a set containing `P` itself and all its single-character derivatives
`a⁻¹(P)` for every character `a` in the alphabet (`Finset.univ`).
The union operation `∪` includes `P`, and `Finset.biUnion` collects the derivatives
by applying `P.deriv_finset` to each `a` in the universe of characters `@Finset.univ α HFA`. -/
def deriv_step (P : RegularExpression α) : Finset (RegularExpression α) :=
  {P} ∪ Finset.biUnion (@Finset.univ α HFA) (deriv_finset P ·) -- Corrected: Use deriv_finset P

/-- Computes the "next step" in the derivative set exploration from a *set* of regexes `S`.
It applies `deriv_step` to each regex `P` in `S` and takes the union of all the resulting sets.
This effectively computes `{P} ∪ { a⁻¹(P) | a ∈ Σ }` for all `P ∈ S` and combines them. -/
def deriv_step_set (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  Finset.biUnion S deriv_step -- Apply deriv_step to each element P in S and unite results

/-! ### Normalization of Regular Expressions

Brzozowski proved that any regular expression `R` has a finite number of derivatives
*up to equivalence*. That is, while you can generate infinitely many *syntactically distinct*
derivative expressions (e.g., `a+b`, `b+a`, `a+b+0`, etc.), they fall into a finite number
of sets representing the same language.

To compute the derivative set using `#eval` and observe its finiteness, we need a way
to identify and collapse some of these equivalent syntactic forms. This process is called
normalization. A perfect normalizer would map any two regexes `R` and `S` to the same
canonical form if and only if `L(R) = L(S)`. However, deciding language equivalence for
regexes (especially with intersection/complement) is computationally hard (PSPACE-complete).

The function `nf` implemented here is a *simplifier* or *partial normalizer*. It focuses
on applying common algebraic identities, primarily for the `+` operator (associativity,
commutativity, identity `P+0=P`, idempotence `P+P=P`) and some basic identities for `*`
(`0*P=0`, `P*0=0`, `1*P=P`, `P*1=P`) and `star` (`0*=1`, `1*=1`, `(P*)*=P*`).

Owens et al. (2008) note that handling similarity rules for `+` (associativity, commutativity,
idempotence) is sufficient to guarantee termination of the derivative generation process.
Our `nf` does this and more, aiming to produce smaller, more canonical forms useful for
`#eval`, even if it doesn't guarantee true minimality (which would require full language
equivalence checking).

The strategy for normalizing sums (`P+Q+R...`) is:
1. `flattenSum`: Deconstruct nested sums into a flat list `[P, Q, R, ...]`.
2. `cleanSum`: Remove `0`s and duplicate elements from the list.
3. `rebuildSum`: Sort the list based on a canonical order (`regexLT`) and reconstruct
   the sum (`P' + Q' + R' ...`).
-/

/-- Recursively flattens nested sums `(P+Q)+R` into a list `[P, Q, R]`.
Non-sum expressions become singleton lists. -/
@[simp]
def flattenSum : RegularExpression α → List (RegularExpression α)
| P + Q   => flattenSum P ++ flattenSum Q
| R       => [R] -- Base case: non-plus expression

/-- Soundness proof for `flattenSum`: A word `w` matches `P` iff it matches
at least one element in the list `flattenSum P`.
Proven by structural induction on `P`. -/
@[simp]
lemma flattenSum_sound (P : RegularExpression α) (w : List α) :
    (flattenSum P).any (fun Q => Q.rmatch w) = P.rmatch w := by
  induction P generalizing w with
  | zero => simp [flattenSum, zero_rmatch, any]
  | epsilon => simp [flattenSum, one_rmatch_iff, any]
  | char a => simp [flattenSum, char_rmatch_iff, any]
  | plus P Q IHP IHQ =>
    simp only [flattenSum, any_append, IHP, IHQ, plus_def]
    rw [Bool.eq_iff_iff] -- Use IH and definition of `+` matching
    simp_all only [add_rmatch_iff, Bool.or_eq_true]
  | comp P Q IHP IHQ => simp [flattenSum, any] -- Comp is a base case for flattenSum
  | «star» P IHP => simp [flattenSum, any] -- Star is a base case for flattenSum

/-- Removes all occurrences of `0` from a list of regexes. -/
def cleanSumZero (l : List (RegularExpression α)) : List (RegularExpression α) :=
  l.filter (· ≠ 0)

/-- (INCOMPLETE) Soundness proof for `cleanSumZero`: Removing `0` doesn't change whether
any regex in the list matches the word `w`, since `0` matches nothing (`0.rmatch w` is always false).
Proven by induction on the list `l`. -/
@[simp]
theorem cleanSumZero_sound (l : List (RegularExpression α)) (w : List α) :
    (cleanSumZero l).any (fun Q => Q.rmatch w) = l.any (fun Q => Q.rmatch w) := by
  simp only [cleanSumZero, ← List.mem_filter]
  sorry

/-- Removes duplicate regexes from a list, keeping the first occurrence.
Relies on the `DecidableEq` instance we defined earlier. -/
def cleanSumDups (l : List (RegularExpression α)) : List (RegularExpression α) :=
  l.eraseDups

/-- Soundness proof for `cleanSumDups`: Removing duplicates doesn't change
whether *any* regex in the list matches `w`, because `P.rmatch w ∨ P.rmatch w` is
equivalent to `P.rmatch w`.
*Note: The proof is incomplete (`sorry`). -/
@[simp]
theorem cleanSumDups_sound (l : List (RegularExpression α)) (w : List α) :
    (cleanSumDups l).any (fun Q => Q.rmatch w) = l.any (fun Q => Q.rmatch w) := by
  simp only [cleanSumDups]; sorry

/-- Combines `cleanSumZero` and `cleanSumDups` to remove both `0`s and duplicates. -/
def cleanSum (l : List (RegularExpression α)) : List (RegularExpression α) :=
  cleanSumDups (cleanSumZero l)

/-- Soundness proof for `cleanSum`: Follows directly from the soundness of its components.
*(Inherits the `sorry` from `cleanSumDups_sound`).* -/
def cleanSum_sound (l : List (RegularExpression α)) (w : List α) :
    (cleanSum l).any (fun Q => Q.rmatch w) = l.any (fun Q => Q.rmatch w) := by
  simp [cleanSum, cleanSumDups_sound, cleanSumZero_sound]

/-- Creates a key (size, string representation) for a regex. Used for sorting. -/
@[simp]
private def regexKey (P : RegularExpression α) : Nat × String :=
  (P.size, toString (reprPrec P 0)) -- Uses size and the Repr instance

/-- Defines a total order (`<`) on regexes based on their `regexKey`.
Compares size first, then the string representation lexicographically.
This provides a consistent, arbitrary order for sorting. -/
def regexLT (P Q : RegularExpression α) : Prop :=
  let (nP, sP) := regexKey P
  let (nQ, sQ) := regexKey Q
  nP < nQ ∨ (nP = nQ ∧ sP < sQ)

/-- Instance proving that `regexLT` is decidable. Needed for sorting. -/
instance decidable_regexLT : DecidableRel (regexLT : RegularExpression α → RegularExpression α → Prop) := by
  intros P Q; dsimp [regexLT]; infer_instance -- Lean can infer decidability from components

/-- Reconstructs a sum expression from a list of regexes.
It first sorts the list using `regexLT` to ensure a canonical order,
then folds the list into a right-associative sum (`x + (y + z)`).
An empty list becomes `0`. -/
def rebuildSum (l : List (RegularExpression α)) : RegularExpression α :=
  match l.mergeSort (fun P Q => decide (regexLT P Q)) with -- Sort the list
  | []      => 0 -- Empty list is 0
  | x :: xs => xs.foldl (fun acc r => acc + r) x -- Fold into sum: x + (... + (y + z))

/-- Soundness proof for `rebuildSum`: The reconstructed sum matches `w` iff
any element in the original list `l` matches `w`.
*Note: Proof is incomplete (`sorry`). Requires reasoning about `mergeSort` and `foldl`
combined with the properties of `+`.* -/
@[simp]
lemma rebuildSum_sound (l : List (RegularExpression α)) (w : List α) :
  (rebuildSum l).rmatch w = l.any (fun Q => Q.rmatch w) := by
  simp only [rebuildSum]
  let l' := l.mergeSort (fun P Q => decide (regexLT P Q))
  suffices (match l' with
    | [] => 0
    | x :: xs => xs.foldl (fun acc r => acc + r) x).rmatch w = l'.any (fun Q => Q.rmatch w) by
     -- Need to show that mergeSort preserves the 'any matches' property
     sorry
  induction l' with
  | nil => simp [any, zero_rmatch]
  | cons head tail ih =>
     simp only [foldl, any_cons, Bool.or_eq_true]
     sorry -- Proof requires induction on foldl combined with add_rmatch_iff

/-- Correctness of the full sum normalization pipeline: Applying flatten, clean,
and rebuild to `P` results in a regex that matches the same words as `P`.
*(Inherits `sorry`s from dependencies).* -/
@[simp]
theorem full_rebuild_correct (P : RegularExpression α) (w : List α) :
  (rebuildSum (cleanSum (flattenSum P))).rmatch w = P.rmatch w := by
  simp [rebuildSum_sound, cleanSum_sound, flattenSum_sound] -- Chain the soundness lemmas

/-- ### The Normal Form Function `nf`
Applies normalization rules recursively to a regular expression.
- Handles base cases `0`, `1`, `char a`.
- For `P + Q`: Recursively normalizes `P` and `Q`, then applies the
  flatten/clean/rebuild pipeline to the combination of their flattened sums.
- For `P * Q`: Recursively normalizes `P` and `Q`, then applies identities
  like `0 * Q' = 0`, `P' * 0 = 0`, `1 * Q' = Q'`, `P' * 1 = P'`.
  *Note: Does not handle associativity of `*`, e.g., `(P*Q)*R`.*
- For `star P`: Recursively normalizes `P`, then applies identities
  like `0* = 1`, `1* = 1`, `(P'*)* = P'`. -/
def nf : RegularExpression α → RegularExpression α
| 0         => 0
| 1         => 1
| char a    => char a
| P + Q     =>
    -- Normalize children P and Q first
    let Pn := nf P
    let Qn := nf Q
    -- Handle trivial cases after normalization
    match Pn, Qn with
    | 0, Q' => Q' -- 0 + Q' = Q'
    | P', 0 => P' -- P' + 0 = P'
    | _, _ => rebuildSum (cleanSum (flattenSum Pn ++ flattenSum Qn))
| P * Q     =>
  match nf P, nf Q with -- Normalize children first
  | 0, _    => 0    -- 0 * Q' = 0
  | _, 0    => 0    -- P' * 0 = 0
  | 1, Q'   => Q'   -- 1 * Q' = Q'
  | P', 1   => P'   -- P' * 1 = P'
  | P', Q'  => P' * Q' -- Default case
| star P    =>
  match nf P with -- Normalize child first
  | 0       => 1    -- 0* = 1
  | 1       => 1    -- 1* = 1
  | star R' => star R'  -- (R'*)* = R'* (Idempotence)
  | R'      => star R' -- Default case

/-- Soundness theorem for `nf`: The normalized regex matches the same words
as the original regex.
*Note: Proof is incomplete (`sorry`). Requires induction and use of
the soundness lemmas for the components (like `full_rebuild_correct`), many
of which also contain `sorry`.* -/
theorem nf_sound (P : RegularExpression α) (w : List α):
    (nf P).rmatch w = P.rmatch w := by
  induction P generalizing w with
  | zero => simp [nf]
  | epsilon => simp [nf]
  | char a => simp [nf]
  | plus P Q ihP ihQ =>
    simp only [nf]
    -- After matching on Pn, Qn, need cases
    sorry
  | comp P Q ihP ihQ =>
    simp only [nf]
    sorry
  | «star» P ihP =>
    simp only [nf]
    sorry

/-! ### Applying Normalization to Derivative Sets -/

/-- Helper function to wrap `nf P` in a Finset. -/
def normalize_P (P : RegularExpression α) : Finset (RegularExpression α) :=
  {nf P}

/-- Applies `nf` to every regex in a Finset `S`. -/
def normalize_set (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  Finset.biUnion S normalize_P -- Apply nf to each element via normalize_P

/-- Computes the next set of derivatives (like `deriv_step_set`) and then
normalizes every regex in the resulting set. This is the core function used
for iterating the derivative computation process. -/
def deriv_step_set_nf (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  normalize_set (deriv_step_set S) -- Compute derivatives, then normalize the whole set

/-! ### Iteration Functions for Demonstration

These functions simply apply `deriv_step_set_nf` multiple times, starting from
the normalized version of an initial regex `P`. They are designed to be used
with `#eval` to observe the computed derivative set after a few steps and see
if it stabilizes. -/

/-- Compute the normalized derivative set after 1 step. -/
def iterate_one (P : RegularExpression α) : Finset (RegularExpression α) :=
  deriv_step_set_nf {nf P} -- Start with the normalized P in a set

/-- Compute the normalized derivative set after 2 steps. -/
def iterate_two (P : RegularExpression α) : Finset (RegularExpression α) :=
  deriv_step_set_nf (iterate_one P) -- Apply again to the result of iterate_one

/-- Compute the normalized derivative set after 5 steps. -/
def iterate_five (P : RegularExpression α) : Finset (RegularExpression α) :=
  -- Apply iterate_step_nf five times
  let i1 := iterate_one P
  let i2 := deriv_step_set_nf i1
  let i3 := deriv_step_set_nf i2
  let i4 := deriv_step_set_nf i3
  deriv_step_set_nf i4

end RegularExpression
end RegexDeriv
