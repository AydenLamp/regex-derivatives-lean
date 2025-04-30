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
  | P + Q, a => P.deriv a + Q.deriv a
  | P * Q, a => if P.matchEpsilon then P.deriv a * Q + Q.deriv a else P.deriv a * Q
  | star P, a => P.deriv a * star P

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
| 0 => 0
| 1 => 0
| char _ => 0
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

open List

variable {α} [HFA : Fintype α] [DecidableEq α] [Repr α]

@[simp]
def deriv_word (P : RegularExpression α) (word : List α) : RegularExpression α :=
  match word with
  | [] => P
  | a :: as => deriv_word (deriv P a) as

omit HFA [Repr α] in
theorem deriv_word_correct (P : RegularExpression α) (a : List α):
  (P.deriv_word a).matchEpsilon ↔ P.rmatch (a)  := by
  induction a generalizing P with
  | nil => simp only [deriv_word, rmatch]
  | cons head tail ih => simp only [rmatch, deriv_word]; apply ih

/- Finset-based derivitives -/

@[simp]
def deriv_finset : RegularExpression α → α →  Finset (RegularExpression α)
  | 0, _ => {0}
  | 1, _ => {0}
  | char a₁, a₂ => if a₁ = a₂ then {1} else {0}
  | P + Q, a => {deriv P a + deriv Q a}
  | P * Q, a => if P.matchEpsilon then {deriv P a * Q + deriv Q a} else {deriv P a * Q}
  | star P, a => {deriv P a * star P}


def deriv_step (P : RegularExpression α) : Finset (RegularExpression α) :=
  {P} ∪ Finset.biUnion (@Finset.univ α HFA) P.deriv_finset


def deriv_step_set (S : Finset (RegularExpression α)) : Finset (RegularExpression α) :=
  Finset.biUnion S deriv_step

set_option linter.unusedSectionVars false


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

/-- Pull apart `P + Q` into a list of “atoms,” recursively. -/
@[simp]
def flattenSum : RegularExpression α → List (RegularExpression α)
| P + Q   => flattenSum P ++ flattenSum Q
| R       => [R]

/- todo- talk about the curry-howard corrospondence and its
significance in the proofs of correctness. -/

/-- The language recognized by the list
is the same as the language of the original regex. -/
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


@[simp]
theorem cleanSumZero_sound (l : List (RegularExpression α)) (a : List α) :
    (cleanSumZero l).any (fun Q => Q.rmatch a) = l.any (fun Q => Q.rmatch a) := by
  unfold cleanSumZero
  induction l with
  | nil => simp_all
  | cons head tail ih =>
    simp_all only [bne_iff_ne, ne_eq, any_cons]
    by_cases H : head = 0
    · subst H; simp_all;
    · simp_all


/-- Erase all duplicates, keeping first occurrence. -/
def cleanSumDups (l : List (RegularExpression α)) : List (RegularExpression α) :=
  l.filter (fun P => ¬Duplicate P l)

#check List.duplicate_cons_iff_of_ne
#check List.deci

instance DupsDecidable :
@[simp]
theorem cleanSumDups_sound (l : List (RegularExpression α)) (a : List α) :
    (cleanSumDups l).any (fun Q => Q.rmatch a) = l.any (fun Q => Q.rmatch a) := by
  unfold cleanSumDups
  induction l with
  | nil => simp_all only [not_duplicate_nil, not_false_eq_true, decide_true, filter_nil, any_nil]
  | cons head tail ih =>

    simp_all only [decide_not, any_filter, any_cons, duplicate_cons_self_iff, duplicate_cons_iff]
    rw [← ih]
    sorry





/-- Erase all duplicates, keeping first occurrence. -/
def cleanSum (l : List (RegularExpression α)) : List (RegularExpression α) :=
  cleanSumDups (cleanSumZero l)

@[simp]

/-- Pair each regex with its “key” = (size, repr‐string). -/
private def regexKey (P : RegularExpression α) : Nat × String :=
  (P.size, toString (reprPrec P 0))

/-- A total order on regex—e.g. -/
def regexLT (P Q : RegularExpression α) : Prop :=
  let (nP, sP) := regexKey P
  let (nQ, sQ) := regexKey Q
  nP < nQ ∨ (nP = nQ ∧ sP < sQ)

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
  simp_all [rebuildSum]
  split
  next x heq =>
    simp_all only [zero_rmatch, Bool.false_eq, any_eq_false, rmatch_iff_matches']
    intro x_1 a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
l : List (RegularExpression α)
a : List α
x : List (RegularExpression α)
heq : (l.mergeSort fun P Q ↦ decide (P.regexLT Q)) = []
x_1 : RegularExpression α
a_1 : x_1 ∈ l
a_2 : a ∈ x_1.matches'
⊢ False-/
  next x x_1 xs heq => sorry /-1 goal
α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
l : List (RegularExpression α)
a : List α
x : List (RegularExpression α)
x_1 : RegularExpression α
xs : List (RegularExpression α)
heq : (l.mergeSort fun P Q ↦ decide (P.regexLT Q)) = x_1 :: xs
⊢ (foldl (fun acc r ↦ acc + r) x_1 xs).rmatch a = l.any fun Q ↦ Q.rmatch a
-/


@[simp]
theorem rebuild_correct (P : RegularExpression α) (a : List α) :
  (rebuildSum (flattenSum P)).rmatch a = P.rmatch a := by
  calc
    (rebuildSum (flattenSum P)).rmatch a
    = (flattenSum P).any (fun Q => Q.rmatch a) := by
      apply rebuildSum_sound
    _ =  P.rmatch a := by
      apply flattenSum_sound



def nf : RegularExpression α → RegularExpression α
| 0         => 0
| 1         => 1
| char a    => char a
| P + Q     =>
  let atoms := cleanSum (flattenSum (nf P) ++ flattenSum (nf Q))
  rebuildSum atoms
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
  | R'      => R'


theorem nf_sound (P : RegularExpression α) (a : List α):
    P.rmatch a = (nf P).rmatch a := by
  unfold nf
  simp_all only
  split
  next x => simp_all only [zero_def, zero_rmatch]
  next x => simp_all only [one_def]
  next x a_1 => simp_all only
  next x P
    Q =>
    simp_all only [plus_def, rebuildSum_sound, cleanSum_sound, ne_eq, rmatch_iff_matches', Bool.decide_and,
      decide_not, any_append]
    sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q : RegularExpression α
⊢ (P + Q).rmatch a =
  ((P.nf.flattenSum.any fun Q ↦ !decide (Q = 0) && decide (a ∈ Q.matches')) ||
    Q.nf.flattenSum.any fun Q ↦ !decide (Q = 0) && decide (a ∈ Q.matches'))
-/
  next x P Q =>
    simp_all only [comp_def]
    split
    next x_1 x_2 heq =>
      simp_all only [zero_def, zero_rmatch]
      sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q x_1 x_2 : RegularExpression α
heq : P.nf = 0
⊢ (P * Q).rmatch a = false-/
    next x_1 x_2 heq x_3 =>
      simp_all only [zero_def, imp_false, zero_rmatch]
      sorry /- α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q x_1 x_2 : RegularExpression α
heq : Q.nf = 0
x_3 : ¬P.nf = 0
⊢ (P * Q).rmatch a = false-/
    next x_1 x_2 heq x_3 =>
      simp_all only [one_def, zero_def, imp_false]
      sorry
      /- α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q x_1 x_2 : RegularExpression α
heq : P.nf = 1
x_3 : ¬Q.nf = 0
⊢ (P * Q).rmatch a = Q.nf.rmatch a
-/
    next x_1 x_2 heq x_3 x_4 =>
      simp_all only [one_def, zero_def, imp_false]
      sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q x_1 x_2 : RegularExpression α
heq : Q.nf = 1
x_3 : ¬P.nf = 0
x_4 : ¬P.nf = 1
⊢ (P * Q).rmatch a = P.nf.rmatch a-/
    next x_1 x_2 x_3 x_4 x_5 x_6 =>
      simp_all only [zero_def, imp_false, one_def]
      sorry /- α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P Q x_1 x_2 : RegularExpression α
x_3 : ¬P.nf = 0
x_4 : ¬P.nf = 1
x_5 : ¬Q.nf = 0
x_6 : ¬Q.nf = 1
⊢ (P * Q).rmatch a = (P.nf * Q.nf).rmatch a-/
  next x P =>
    split
    next x_1 heq =>
      simp_all only [zero_def]
      sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P x_1 : RegularExpression α
heq : P.nf = 0
⊢ (star P).rmatch a = rmatch 1 a
-/
    next x_1 heq =>
      simp_all only [one_def]
      sorry /- α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P x_1 : RegularExpression α
heq : P.nf = 1
⊢ (star P).rmatch a = rmatch 1 a-/
    next x_1 R' heq => sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P x_1 R' : RegularExpression α
heq : P.nf = star R'
⊢ (star P).rmatch a = (star R').rmatch a-/
    next x_1 x_2 x_3 x_4 =>
      simp_all only [zero_def, imp_false, one_def]
      sorry /-α : Type u_1
HFA : Fintype α
inst✝¹ : DecidableEq α
inst✝ : Repr α
a : List α
x P x_1 : RegularExpression α
x_2 : ¬P.nf = 0
x_3 : ¬P.nf = 1
x_4 : ∀ (R' : RegularExpression α), ¬P.nf = star R'
⊢ (star P).rmatch a = P.nf.rmatch a
-/



inductive Lang
| A | B | C
deriving DecidableEq, Inhabited, Fintype

instance : Repr Lang where
  reprPrec
    | Lang.A, _ => "A"
    | Lang.B, _ => "B"
    | Lang.C, _ => "C"

def A := Lang.A
def B := Lang.B
def C := Lang.C

def R0 : RegularExpression Lang := 0
def R1 : RegularExpression Lang := 1
def a : RegularExpression Lang := char A
def b : RegularExpression Lang := char B
def c : RegularExpression Lang := char C

#eval R0.deriv A
#eval (a + b + c).deriv_word [A, ]
#eval (star (a * b)).deriv_word [A, B, A]
#eval ((star (a * b)).deriv_word [A]).matchEpsilon
#eval deriv_step_set (deriv_step_set (star (a * b)).deriv_step)


#eval Pabc.deriv_step
#eval (Pa_times_b.deriv Test.a).deriv Test.b
#eval Pa_times_b.deriv_word [Test.a]
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
