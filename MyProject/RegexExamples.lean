import MyProject.RegexDerivitives

/-! # Examples for Regular Expression Derivatives

This file demonstrates the functions defined in `RegexDerivative.lean` using
Lean's `#eval` command. It shows how to compute derivatives with respect
to words and how to compute the set of all reachable (normalized) derivatives.

We define a simple three-letter alphabet {A, B, C} and some basic regular expressions. -/

open RegularExpression

-- Define a simple Alphabet {A, B, C}
inductive Alphabet
| A | B | C
deriving DecidableEq, Inhabited, Fintype, Repr

-- Make instances easily available
def A : Alphabet := Alphabet.A
def B : Alphabet := Alphabet.B
def C : Alphabet := Alphabet.C

-- Define basic regular expressions for characters A, B, C
def a : RegularExpression Alphabet := char A
def b : RegularExpression Alphabet := char B
def c : RegularExpression Alphabet := char C

/-! ## Examples using `deriv_word`

`deriv_word P w` computes the derivative of `P` with respect to the word `w`.
The result is a single regular expression. We use `nf` to simplify the output. -/

-- Example 1: Derivative of `a+b` w.r.t `[C]`. Should be 0.
#eval nf ((a + b).deriv_word [C])
--  output: 0

-- Example 2: Derivative of `a*b` w.r.t `[A, B, C]`.
#eval nf ((a * b).deriv_word [A, B, C])
--  output: 0

-- Example 3: Derivative of `c * (star (a + b)) * c` w.r.t `[C, A]`.
#eval nf ((c * (star (a + b)) * c).deriv_word [C, A])
--  output: ((char A + char B)* * char C)


/-! ## Examples using `iterate_` functions

These functions compute the *set* of reachable, normalized derivatives.
`iterate_one P` computes the set after 1 step (P and its immediate derivatives).
`iterate_two P` computes the set after 2 steps, etc.
We expect the set size to stabilize after a finite number of steps, corresponding
to finding all states of the equivalent DFA. -/

-- R = c * (a+b)* * c
def R : RegularExpression Alphabet := c * (star (a + b)) * c

-- Compute the derivative set after 1 step
#eval iterate_one R
/-  output: A Finset containing nf(R) and nf(a⁻¹(R)) for a ∈ {A, B, C}.
{((char Alphabet.C * ((char Alphabet.A + char Alphabet.B)*)) * char Alphabet.C),
 0,
 (((char Alphabet.A + char Alphabet.B)*) * char Alphabet.C)} -/

-- Compute the derivative set after 2 steps
#eval iterate_two R
/- output:
{((char Alphabet.C * ((char Alphabet.A + char Alphabet.B)*)) * char Alphabet.C),
 0,
 (((char Alphabet.A + char Alphabet.B)*) * char Alphabet.C),
 1} -/

-- Compute the derivative set after 5 steps (it stabalizes after two steps)
#eval iterate_five R
/-  output:
{((char Alphabet.C * ((char Alphabet.A + char Alphabet.B)*)) * char Alphabet.C),
 (((char Alphabet.A + char Alphabet.B)*) * char Alphabet.C),
 1,
 0} -/

/-! ## Example demonstrating `nf` simplification -/

-- This expression simplifies significantly due to the rules in `nf`.
-- (a + a + a + 0 + (0 * 1)) * 1
-- = (a + a + a + 0 + 0) * 1  (0*1=0)
-- = (a + a + a) * 1          (X+0=X)
-- = a * 1                    (a+a=a, idempotence via cleanSumDups)
-- = a                        (X*1=X)
#eval nf ((a + a + a + 0 + (0 * 1)) * 1)
-- output: char Alphabet.A
