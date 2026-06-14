import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  rintro h x hx
  apply h ⟨x, hx, rfl⟩
  rintro h y ⟨x, hx, rfl⟩
  apply h hx


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro y ⟨x, hx, xeq⟩
  rw [← h xeq]
  exact hx

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, hx, rfl⟩
  apply hx

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  obtain ⟨x, rfl⟩ := h y
  use x, hy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, hx, rfl⟩
  use x, h hx

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  apply h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  repeat
    intro
    assumption


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, hx, rfl⟩
  rw [mem_inter_iff]
  constructor
  use x, inter_subset_left hx
  use x, inter_subset_right hx

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, hx₁, x₁eq⟩, ⟨x₂, hx₂, x₂eq⟩⟩
  have : x₁ ∈ t := by rw [h (Eq.trans x₁eq x₂eq.symm)]; assumption
  use x₁, ⟨hx₁, this⟩


example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro x ⟨⟨y, hy, rfl⟩, h⟩
  have : y ∉ t := by
    by_contra h'
    have : f y ∈ f '' t := by use y
    contradiction
  use y, ⟨hy, this⟩


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨hl, hr⟩
  use hl, hr

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  rintro ⟨⟨x, hx, rfl⟩, hr⟩
  use x
  constructor
  use hx, hr
  rfl

  rintro ⟨x, hx, rfl⟩
  use ⟨x, hx.1, Eq.refl _⟩, hx.2


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, hx, rfl⟩
  use ⟨x, hx.1, Eq.refl (f x)⟩, hx.2

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨hs, hu⟩
  use ⟨x, hs, Eq.refl (f x)⟩, hu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (hs | hiu)
  left
  use x
  right
  exact hiu


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  rintro ⟨x, hx, rfl⟩
  simp at hx
  rcases hx with ⟨i, hi⟩
  simp
  use i, x

  rintro ⟨C, ⟨⟨i, hi⟩, hy⟩⟩
  simp at hi
  rw [← hi] at hy
  rcases hy with ⟨x, hx, rfl⟩
  simp
  use x
  constructor
  use i
  rfl


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, hx, rfl⟩
  simp
  intro i
  use x
  constructor
  rw [mem_iInter] at hx
  apply hx
  rfl

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x hx
  rw [mem_iInter] at hx
  simp
  rcases hx i with ⟨a, ha, rfl⟩
  use a
  constructor
  intro i'
  rcases hx i' with ⟨_, hb, heq⟩
  rw [← injf heq]
  exact hb
  rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy hsqrteq
  rw [← Real.sq_sqrt hx, ← Real.sq_sqrt hy, hsqrteq]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy
  dsimp
  intro hsqeq
  have : √(x^2) = √(y^2) := congrArg _ hsqeq
  convert this
  repeat rw [Real.sqrt_sq]; assumption

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  rintro ⟨x, hx, rfl⟩
  apply Real.sqrt_nonneg
  rintro h
  use y^2, pow_two_nonneg y, Real.sqrt_sq h

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  intro h
  rcases h with ⟨a, ha⟩
  rw [← ha]
  apply pow_two_nonneg a

  intro h
  use √x, sq_sqrt h
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  intro finj y
  have : ∃x, f x = f y := by use y
  rw [inverse, dif_pos this]
  apply finj (choose_spec this)

  intro linvf x y feq
  rw [← linvf x, ← linvf y]
  apply congrArg (inverse f) feq


example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro fsurj y
  rw [inverse, dif_pos (fsurj y)]
  apply choose_spec (fsurj y)

  intro h y
  use inverse f y, h y
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  rw [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
