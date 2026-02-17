import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

theorem min_comm : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left


example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  have h1 : ∀ x y z: ℝ, min (min x y) z ≤ x := by
    intro x y z
    apply le_trans
    apply min_le_left
    apply min_le_left

  have h2 : ∀ x y z : ℝ, min x (min y z) ≤ min (min x y) z := by
    intro x y z
    apply le_min
    apply le_min
    apply min_le_left
    rw [min_comm]
    apply h1
    rw [min_comm x, min_comm y]
    apply h1

  apply le_antisymm
  rw [min_comm, min_comm a b, min_comm a (min b c), min_comm b c]
  apply h2 c b a
  apply h2

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add
  apply min_le_left
  apply le_rfl
  apply add_le_add
  apply min_le_right
  apply le_rfl

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have foo := aux (a + c) ( b + c)  (-c)
  rw [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at foo
  have bar := add_le_add_right foo c
  rw [add_assoc, neg_add_cancel, add_zero] at bar
  exact bar

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)


example : |a| - |b| ≤ |a - b| := by
  have bar : |a| ≤ |b + -b + a| := by
    rw [add_neg_cancel b, zero_add]

  have baz : |b + -b + a| ≤ |b| + |a - b| := by
    rw [add_assoc]
    apply le_trans
    apply abs_add
    rw [add_comm (-b), sub_eq_add_neg]

  have thud := add_le_add_right (le_trans bar baz) (-|b|)
  ring_nf at thud
  exact thud
end


section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  repeat apply dvd_add
  rw [mul_comm x, ← mul_assoc]
  repeat apply dvd_mul_left
  apply dvd_mul_of_dvd_left
  norm_num
  exact h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply gcd_comm
end
