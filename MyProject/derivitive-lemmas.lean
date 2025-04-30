
/- lemmas for zero-/
@[simp]
lemma deriv_word_zero (a : List α) : (0 : RegularExpression α).deriv_word a = 0 := by
  induction a with
  | nil => simp
  | cons head tail ih => simpa

@[simp]
lemma deriv_word_zero_epsilon (a : List α) : ((0 : RegularExpression α).deriv_word a).matchEpsilon = false := by
  simp_all [matchEpsilon]

@[simp]
lemma deriv_word_zero_rmatch (a : List α) :
    (zero.deriv_word a).matchEpsilon = true ↔ zero.rmatch a = true := by simp [matchEpsilon]

/- lemmas for one-/
@[simp]
lemma deriv_word_one_char (a : α) : (1 : RegularExpression α).deriv_word [a] = 0 := by simp

@[simp]
lemma deriv_word_one_nil (a : List α): (1 : RegularExpression α).deriv_word a = 1  ↔ a = []:= by
  apply Iff.intro
  · intro H; induction a
    · rfl
    · simp at H;
  · intro H; subst H; simp only [deriv_word]

@[simp]
lemma deriv_word_one_epsilon (a : List α) :
    ((1 : RegularExpression α).deriv_word a).matchEpsilon = true ↔ a = [] := by
  cases a with
  | nil => simp [matchEpsilon]
  | cons head tail => simp_all [matchEpsilon]

@[simp]
lemma deriv_word_one_rmatch (a : List α) :
    ((1 : RegularExpression α).deriv_word a).matchEpsilon = true ↔ ((1 : RegularExpression α).rmatch a) := by
  simp only [deriv_word_one_epsilon, rmatch_iff_matches', matches'_epsilon, Language.mem_one]

/- Lemmas for char-/
@[simp]
lemma deriv_word_char_self (a : α) : (char a : RegularExpression α).deriv_word [a] = 1 := by simp

@[simp]
lemma deriv_word_char_of_ne {a b : α} (H : a ≠ b) : (char a : RegularExpression α).deriv_word [b] = 0 := by
  simp; unfold deriv; simp_all only [ne_eq, ↓reduceIte]

@[simp]
lemma deriv_word_char_iff_eq {a b : α} : (char a : RegularExpression α).deriv_word [b] = 1 ↔ a = b := by
  simp_all; apply Iff.intro
  · intro H; by_cases H2: (a = b)
    · assumption
    · have contra := deriv_word_char_of_ne H2; simp_all
  · intro H; subst H; simp

@[simp]
lemma deriv_word_char_epsilon {a : α} {b : List α} :
    ((char a : RegularExpression α).deriv_word b).matchEpsilon ↔ b = [a] := by
  cases b with
  | nil => simp_all [matchEpsilon]
  | cons head tail =>
    simp_all [deriv_word, deriv, matchEpsilon]; apply Iff.intro
    · intro H; by_cases Heq : (a = head)
      · subst Heq; simp_all;
      · simp_all; simp [matchEpsilon] at H
    · intro H; simp_all [matchEpsilon]

@[simp]
lemma deriv_word_char_rmatch {a : α} {b : List α} :
    ((char a : RegularExpression α).deriv_word b).matchEpsilon ↔ (char a : RegularExpression α).rmatch b := by
  simp_all only [deriv_word_char_epsilon, rmatch_iff_matches', matches'_char]; rfl

/- lemmas for add-/
@[simp]
theorem deriv_word_add (P Q : RegularExpression α) (a : List α) :
    deriv_word (P + Q) a = deriv_word P a + deriv_word Q a := by
  induction a generalizing P Q with
  | nil => simp only [deriv_word]
  | cons head tail ih => simp only [deriv_word, deriv_add]; apply ih

@[simp]
lemma deriv_word_add_epsilon {P Q : RegularExpression α} {a : List α} :
    ((P + Q).deriv_word a).matchEpsilon ↔ (P.deriv_word a + Q.deriv_word a).matchEpsilon := by
  simp only [deriv_word_add]
