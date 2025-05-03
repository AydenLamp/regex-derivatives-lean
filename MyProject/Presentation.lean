import MyProject.EegexDerivative

open List Set Computability
universe u
namespace MathlibExamples'

/-! # Constructors:
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`  -/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α

end MathlibExamples'
namespace MathlibExamples

variable {α} {a b : α}

/- We can use `0`, `1`, `+`, and `*` to notate Regex Constructors-/
#check ((0 + 1) * (RegularExpression.char a + 1) : RegularExpression α)

/-! This is the assumption that, for all elements of `α` (characters),
we can DECIDE if those two elements are equal.
By decide, I mean that there is a BOOLEAN function returning equality
that is Guarenteed to terminate for any two inputs.
The variable declaration gives this assumtpion all the defs below -/
variable [DecidableEq α]

/-- `matchEpsilon P` is true if and only if `P` matches the empty string. FROM MATHLIB-/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | RegularExpression.char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | RegularExpression.star _P => true

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect to `a`. FROM MATHLIB -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | RegularExpression.char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | RegularExpression.star P, a => deriv P a * RegularExpression.star P

/- Mathlib also defines some simple lemmas that follow from the definition of deriv-/
theorem deriv_zero (a : α) : deriv 0 a = 0 := by simp only [deriv]

theorem deriv_one (a : α) : deriv 1 a = 0 := by simp only [deriv]

theorem deriv_char_self (a : α) : deriv (RegularExpression.char a) a = 1 := by
  simp only [deriv]; simp [↓reduceIte]

theorem deriv_char_of_ne (h : a ≠ b) : deriv (RegularExpression.char a) b = 0 := if_neg h

theorem deriv_add (P Q : RegularExpression α) (a : α) :
    deriv (P + Q) a = deriv P a + deriv Q a := by simp only [deriv]

theorem deriv_star (P : RegularExpression α) (a : α) :
    deriv P.star a = deriv P a * RegularExpression.star P := by simp only [deriv]


/-- `P.rmatch x` is true if and only if `P` matches `x`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x with --we procede by induction on the length of the word
  | nil =>  --Assume x = [] (length 0)
    -- the goal is `rmatch 0 [] = false`, which follows by the definition of `rmatch` and `matchEpsilon`
    simp [rmatch, matchEpsilon]
  | cons head tail ih => -- Assume length of x is greater than zero.
     -- x = head :: tail (where head is the first char and tail is the rest of the word
     -- The goal is `rmatch 0 (head :: tail) = false`
     -- We also have an inductive hypothesis `ih : rmatch 0 tail = false`
    simp [rmatch]
    -- Simplifying by the definition of `rmatch` gives us the goal `rmatch 0 tail = false`
    -- This is precisly our inductive hypothesis
    exact ih

end MathlibExamples

/-
This section Builds on the implementation of Regex Derivitives in Mathlib.
-/
namespace RegularExpression

open List

variable {α} [DecidableEq α]  -- Assume that the alphabet is a `Fintype`

/-- Deriv_word is defined recursivly on the length of the word, and uses mathlib's `deriv` for each character-/
@[simp]
def deriv_word (P : RegularExpression α) (word : List α) : RegularExpression α :=
  match word with
  | [] => P
  | a :: as => deriv_word (deriv P a) as

theorem deriv_word_iff_rmatch (P : RegularExpression α) (a : List α):
    (P.deriv_word a).matchEpsilon ↔ P.rmatch (a)  := by
  induction a generalizing P with
  | nil => simp only [deriv_word, rmatch]
  | cons head tail ih => simp only [rmatch, deriv_word]; apply ih

lemma deriv_word_correct (P : RegularExpression α) (a : List α):
    (P.deriv_word a).matchEpsilon ↔ a ∈ P.matches' := by
  simp_rw [← rmatch_iff_matches', ← deriv_word_iff_rmatch]

inductive Alphabet
| A | B | C
deriving DecidableEq, Inhabited, Fintype

instance : Repr Alphabet where
  reprPrec
    | Alphabet.A, _ => "A"
    | Alphabet.B, _ => "B"
    | Alphabet.C, _ => "C"

def A : Alphabet := Alphabet.A
def B := Alphabet.B
def C := Alphabet.C

def R0 : RegularExpression Alphabet := 0
def R1 : RegularExpression Alphabet := 1
def a : RegularExpression Alphabet := char A
def b : RegularExpression Alphabet := char B
def c : RegularExpression Alphabet := char C


#eval nf ((a + b).deriv_word [C])
#eval nf (((a * b)).deriv_word [A,B,C])

#eval nf ((c * (star (a + b)) * c).deriv_word [C, A])

#eval iterate_one  (c * (star (a + b)) * c)
#eval iterate_two  (c * (star (a + b)) * c)
#eval iterate_five  (c * (star (a + b)) * c)


#eval nf ((a + a + a + 0 + (0 * 1)) * 1)
