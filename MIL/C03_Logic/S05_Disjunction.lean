import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg]
    exact h
  . rw [abs_of_neg]
    linarith
    linarith


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rw [← abs_neg]
  apply le_abs_self

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  . have := abs_of_nonneg h
    rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self _) (le_abs_self _)
  . have := abs_of_neg h
    rw [abs_of_neg h]
    ring_nf
    exact add_le_add (neg_le_abs_self _) (neg_le_abs_self _)


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      intro h; left; exact h
    · rw [abs_of_neg h]
      intro h; right; exact h
  . rintro (ha | hb)
    apply lt_of_lt_of_le ha (le_abs_self _)
    apply lt_of_lt_of_le hb (neg_le_abs_self _)



theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . intro h
    . rcases le_or_gt 0 x with h' | h'
      . rw [abs_of_nonneg h'] at h
        constructor <;> linarith
      . rw [abs_of_neg h'] at h
        constructor <;> linarith
  . intro h
    . rcases le_or_gt 0 x with h' | h'
      . rw [abs_of_nonneg h']
        linarith
      . rw [abs_of_neg h']
        linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h | h'⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by linarith
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h | h
  right; linarith
  left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by linarith
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h | h'
  . right; linarith
  . left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by
    ring_nf
    apply neg_add_eq_zero.mpr
    symm; assumption
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h | h
  right;
  rw [neg_eq_of_add_eq_zero_left]
  exact h
  left;
  rw [← sub_eq_zero]
  exact h

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by
    ring_nf
    rw [sub_eq_zero]
    exact h
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with h | h
  right; exact eq_neg_of_add_eq_zero_left h
  left; exact sub_eq_zero.mp h
end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  . contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h' : P
  . right; exact h h'
  . left; assumption
  rintro (_ | _)
  intro; contradiction
  intro; assumption
