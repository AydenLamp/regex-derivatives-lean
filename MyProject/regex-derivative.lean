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


section RegexDecidableEq

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

end RegexDecidableEq


section REPR

open Std (Format)
open RegularExpression

variable {α} [H : Repr α]

def regex_reprPrec [H : Repr α] : RegularExpression α → ℕ → Format
| 0 => fun _ => Format.text "0"
| 1      => fun _ => Format.text "1"
| char a => fun prec => Format.text "char " ++ (H.reprPrec a prec)
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

namespace RegularExpression

variable {α} [HFA : Fintype α] [DecidableEq α] [Repr α]

#print Finset
#print Fintype
#print Multiset.Nodup
#print Finset.biUnion
#print Finset.image
#print Finset.sup

#print Set.Finite.toFinset_range
#print Set.toFinset
#print Fintype.ofFinset
#print Set.Finite.ofFinset
#print Finset.union_add

def deriv_finset : RegularExpression α → α →  Finset (RegularExpression α)
  | 0, _ => {0}
  | 1, _ => {0}
  | char a₁, a₂ => if a₁ = a₂ then {1} else {0}
  | P + Q, a => {deriv P a + deriv Q a}
  | P * Q, a => if P.matchEpsilon then {deriv P a * Q + deriv Q a} else {deriv P a * Q}
  | star P, a => {deriv P a * star P}

def deriv_step (P : RegularExpression α) : Finset (RegularExpression α) :=
  {P} ∪ Finset.biUnion (@Finset.univ α HFA) P.deriv_finset

def deriv_word (P : RegularExpression α) (word : List α) : RegularExpression α :=
  match word with
  | [] => P
  | a :: as => deriv_word (deriv P a) as

inductive Test
| a | b | c
deriving DecidableEq, Inhabited, Repr, Fintype

def P0 : RegularExpression Test := 0
def P1 : RegularExpression Test := 1
def Pa : RegularExpression Test := char Test.a
def Pb : RegularExpression Test := char Test.b
def Pc : RegularExpression Test := char Test.c

def Pabc : RegularExpression Test := Pa + Pb + Pc
def Pa_times_b : RegularExpression Test := Pa * Pb
def Pa_star : RegularExpression Test := star Pa
def P_sigma_star : RegularExpression Test := star Pabc

#eval Pabc
#eval Pabc.deriv_step
#eval (Pa_times_b.deriv Test.a).deriv Test.b
#eval Pa_times_b.deriv_word [Test.a, Test.b]
#eval P_sigma_star.deriv_step



/-- The left quotients of a language are the states of an automaton that accepts the language. -/
def toDFA (P : RegularExpression α): DFA α P.deriv_set where
  step := fun s a =>
    let r := (s : RegularExpression α).deriv a
    ⟨r, Finset.mem_derivatives_set_of_deriv s.2 a⟩ -- apply Finset.mem_derivatives_set_self P

  start := ⟨P, by  sorry⟩ --apply Finset.mem_derivatives_set_self P
  accept := { s | s.val.matchEpsilon }

theorem toDFA_correct (P : RegularExpression α) :
  (P.toDFA.accepts : Language α) = P.matches' := by
  -- extensionality on the input list `xs`
  funext xs
  induction xs with
  | nil =>
    -- On `[]`, `foldl step start [] = start = P`, so acceptance ⇔ `matchEpsilon_my P`
    show _ = _;
    -- by definition `DFA.accepts` at `[]` checks `accept start`
    dsimp [DFA.accepts, Language.accepts];
    -- `accept start` is `matchEpsilon_my P`, which matches `matches'` at `[]`
    simp [rmatch_iff_matches']

  | cons a xs ih =>
    -- For `a::xs`, DFA follows derivative then recurses
    dsimp [DFA.accepts, Language.accepts, DFA.step];
    -- `foldl step P (a::xs) = foldl step (deriv_my P a) xs`
    simp only [List.foldl_cons];
    -- Now apply the induction hypothesis on `xs` for the derivative
    simp [ih]

end RegularExpression
end RegexDeriv
