import Mathlib

section Examples
open RegularExpression Computability

variable {α β γ} [DecidableEq α] (P : RegularExpression α)

#print RegularExpression
#print matches'  -- regex to language

notation "star " P => RegularExpression.star P

def matches'_my : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
  | star P => P.matches'∗

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv_my : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon_my : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
def rmatch_my : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

example (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x ∈ P.matches' := by simp only [rmatch_iff_matches']

--already in Computability/RegularExpressions.lean
instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

@[simp]
def map_my (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)

example : ∀ P : RegularExpression α, P.map id = P := by
  simp only [map_id, implies_true]

example (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n := by
  simp only [RegularExpression.map_pow, implies_true]

example (g : β → γ) (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f) := by
  simp only [map_map, Function.const_apply, implies_true]

example (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches' := by
  simp only [matches'_map, implies_true]

end Examples

/-! ### Syntactic Monoid from Regular Expressions
In this section, we construct the syntactic monoid of the language defined by a regular expression.
We use the Brzozowski derivative operation from Mathlib to generate the finite set of distinct
derivatives (residual regex states) of a regular expression r.
By the Myhill–Nerode theorem, a regular language has finitely many distinct derivatives
(equivalently, finitely many Myhill–Nerode equivalence classes)​
​
Using these as states (with a Fintype instance),
we define the monoid of state transformations induced by input words.
Multiplication in this monoid corresponds to word concatenation
(implemented as function composition on states), and the identity is the empty word.
This construction is fully constructive, so the monoid’s elements and multiplication can be evaluated via #eval. -/

section SyntacticMonoidFromRegex

open RegularExpression Finset

variable {α} [DecidableEq α] [Fintype α]

@[simp]
def RegularExpression.size : RegularExpression α → Nat
| 0 => 1
| 1 => 1
| char _ => 1
| P + Q => P.size + Q.size + 1
| P * Q => P.size + Q.size + 1
| star P => P.size + 1

set_option linter.unusedVariables false in
@[simp]
def RegularExpression.equal (P Q : RegularExpression α) : Bool :=
  match h : (P, Q) with
  | (0 , 0) => true
  | (1, 1) => true
  | (char a, char b) => if a = b then true else false
  | (star R, star S) =>R.equal S
  | (T * V, R * S) => T.equal R && V.equal S
  | (T + V, R + S) => T.equal R && V.equal S
  | ( _, _) => false

  termination_by (P.size + Q.size)
  decreasing_by
    · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]
      omega
    · simp_all only [comp_def, Prod.mk.injEq, size, gt_iff_lt]
      omega
    · simp_all; omega
    · simp_all; omega
    · simp_all; omega

set_option linter.unusedSectionVars false in
lemma equal_equal {P Q : RegularExpression α} (h : P.equal Q = true) : P = Q := by
  induction P using RegularExpression.recOn generalizing Q with
  | zero => cases Q <;> simp [equal] at h; rfl
  | epsilon => cases Q <;> simp [equal] at h; rfl
  | char a =>
    cases Q with
    | char b =>
      simp [equal] at h; subst a; rfl
    | _ => simp [equal] at h
  | plus P₁ P₂ ih₁ ih₂ =>
    cases Q with
    | plus Q₁ Q₂ =>
      unfold equal at h
      have h₁ : P₁.equal Q₁ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_left h
      have h₂ : P₂.equal Q₂ = true := Lean.Grind.Bool.eq_true_of_and_eq_true_right h
      have eq₁ := ih₁ h₁
      have eq₂ := ih₂ h₂
      simp [eq₁, eq₂]
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


instance RegularExpression.decidableEq : DecidableEq (RegularExpression α) := by
  intros P Q
  cases heq : (P.equal Q)
  · apply isFalse; apply neq_neq; exact heq
  · apply isTrue; apply equal_equal; exact heq


#print Finset
#print Fintype
#print Multiset.Nodup
#print Finset.biUnion
#print Finset.image
#print Finset.sup

/-- Compute the one‐step derivative set of a single regex `P`:
  { P.deriv a | a ∈ univ }. -/
@[simp]
def derivSetOf (P : RegularExpression α) : Finset (RegularExpression α) :=
  Finset.image (P.deriv) (univ : Finset α)

/-- One‐step expansion of a set of regex‐states `S`:
  include the states themselves plus all their one‐symbol derivatives. -/
@[simp]
def stepOnce (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  S ∪ S.biUnion derivSetOf

/--
The full finite set of all Brzozowski derivatives of `r`,
obtained by iterating `stepOnce` up to `r.size + 1` times.
Since each derivative strictly reduces the size of the regex,
after `size + 1` steps we have collected every possible derivative.
-/
@[simp]
def derivatives_set (r : RegularExpression α) : Finset (RegularExpression α) :=
  (Nat.iterate stepOnce (2 ^ r.size)) {r}

def Language.toDFA (L : Language α) : DFA α (Set.range L.leftQuotient)

#eval derivatives_set (char 'a' + char 'b')
/-- Finite type of derivative states for regex `r` (each element is a regex in `derivatives_set r`). -/
def DerivState (r : RegularExpression α) :=
  {x // x ∈ derivatives_set r}

instance (r : RegularExpression α) : Fintype (DerivState r) :=
  Fintype.subtype (derivatives_set r) (by intros x; trivial)

/-- The initial state corresponding to regex `r` itself, as a member of `DerivState r`. -/
@[inline] def initial_state (r : RegularExpression α) : DerivState r :=
  ⟨r, Finset.mem_insert_self _ _⟩  -- `r` is in the initial `derivatives_set r`

/-- Transition function on derivative states: `step r s a` is the state reached by taking the Brzozowski derivative of state `s` on symbol `a`. -/
@[inline] def step (r : RegularExpression α) (s : DerivState r) (a : α) : DerivState r :=
  ⟨ (s.val).deriv a, Finset.mem_bind.mpr ⟨s.val, s.prop, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩ ⟩

@[simp] lemma step_val (r : RegularExpression α) (s : DerivState r) (a : α) : (step r s a).val = s.val.deriv a :=
  rfl

/-- Apply a whole list of input symbols (word) to a derivative state. -/
@[inline] def step_word (r : RegularExpression α) : DerivState r → List α → DerivState r
| s, []      => s
| s, (a::as) => step_word r (step r s a) as

@[simp] lemma step_word_nil (r : RegularExpression α) (s : DerivState r) : step_word r s [] = s := rfl
@[simp] lemma step_word_cons (r : RegularExpression α) (s : DerivState r) (a : α) (w : List α) :
  step_word r s (a :: w) = step_word r (step r s a) w :=
  rfl

/-- An element of the syntactic monoid of `r` is a function on `DerivState r` arising from some input word. -/
def SyntacticMonoidElem (r : RegularExpression α) :=
  { f : DerivState r → DerivState r // ∃ w : List α, ∀ (s : DerivState r), f s = step_word r s w }

instance (r : RegularExpression α) : Inhabited (SyntacticMonoidElem r) :=
  ⟨⟨id, ⟨[], λ s, rfl⟩⟩⟩  -- the empty word induces the identity transformation

/-- The monoid instance on `SyntacticMonoidElem r`, with multiplication as function composition (i.e. word concatenation). -/
instance (r : RegularExpression α) : Monoid (SyntacticMonoidElem r) :=
{ one := ⟨ id, ⟨[], λ s, rfl⟩ ⟩,
  mul := λ x y,
    ⟨ y.val ∘ x.val,
      let ⟨wx, hx⟩ := x.property in
      let ⟨wy, hy⟩ := y.property in
      ⟨ wx ++ wy, λ s, by
        { calc (y.val ∘ x.val) s
               = y.val (x.val s)         := rfl
           ... = step_word r (x.val s) wy := hy (x.val s)
           ... = step_word r (step_word r s wx) wy
                   := by rw [hx s]
           ... = step_word r s (wx ++ wy)
                   := by { induction wx generalizing s; simp [step_word, *] } } ⟩ ⟩,
  one_mul := λ x, subtype.ext (Function.comp.left_id x.val),
  mul_one := λ x, subtype.ext (Function.comp.right_id x.val),
  mul_assoc := λ x y z, subtype.ext (Function.comp.assoc _ _ _) }

instance (r : RegularExpression α) : Fintype (SyntacticMonoidElem r) :=
{ elems := ((@Finset.univ (List α) _).image $ λ w, ⟨λ s, step_word r s w, ⟨w, λ s, rfl⟩⟩),
  complete := λ ⟨f, ⟨w, hf⟩⟩, Finset.mem_image.mpr ⟨w, Finset.mem_univ w, subtype.ext $ funext (hf)⟩ }

end SyntacticMonoidFromRegex
