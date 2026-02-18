import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  -- I'm not sure how to use congr/convert here
  -- so this isn't the nicest looking thing
  have h := max_le_iff.mp hn
  have h' := add_lt_add_of_lt_of_lt (hs n h.1) (ht n h.2)
  norm_num at h'
  have : |s n + t n - (a + b)| = |s n - a + (t n - b)| := by ring_nf
  rw [this]
  apply lt_of_le_of_lt
  apply abs_add
  exact h'

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h

  intro ε εpos
  dsimp
  have : 0 < ε / |c| := div_pos εpos acpos
  rcases cs (ε / |c|) this with ⟨Nc, hNc⟩
  use Nc
  intro n hn
  calc
    |c * s n - c * a| = |c * (s n - a)| := by rw [mul_sub]
    _ = |c| * |s n - a| := by rw [abs_mul]
    _ < |c| * (ε / |c|) := by exact (mul_lt_mul_left acpos).mpr (hNc n hn)
    _ = ε := by field_simp

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  -- The solutions doesn't bother with all the rewriting I did.
  -- It just uses congr (on an equality!) then uses abs_add and linarith.
  -- So: manipulate equality first, then work on the inequalities instead of trying to
  -- do both at once like I did.
  calc
    |s n| ≤ |s n - a| + |a| := by
      nth_rw 1 [← add_zero (s n)]
      rw [← sub_self (a), sub_eq_add_neg, add_comm a, ← add_assoc, ← sub_eq_add_neg]
      apply abs_add
    _ < |a| + 1 := by
      rw [add_comm]
      apply add_lt_add_of_le_of_lt
      rfl
      apply h n hn

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  ring_nf
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  have h2 := le_of_max_le_left hn
  have h1 := le_of_max_le_right hn
  calc
    |s n * t n| = |s n| * |t n| := by apply abs_mul
    _ < B * (ε / B) := by
      apply mul_lt_mul_of_nonneg_of_pos' ?_ ?_ ?_ Bpos
      apply le_of_lt (h₀ n h2)
      norm_num at h₁
      apply h₁ _ h1
      apply abs_nonneg
    _ = ε := by
      apply mul_div_cancel₀ _
      symm
      apply ne_of_lt Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs _
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1
  · ext; ring
  . ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply abs_pos.mpr (sub_ne_zero_of_ne abne)
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa _ (le_max_left Na Nb)
  have absb : |s N - b| < ε := by
    apply hNb _ (le_max_right Na Nb)
  have : |a - b| < |a - b| :=
    calc
      |a - b| = |(s N - b) + -(s N - a)| := by ring_nf
      _ ≤ |s N - b| + |(s N - a)| := by
        rw [← abs_neg (s N - a)]
        apply abs_add
      _ < ε + ε := by exact add_lt_add absb absa
      _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
