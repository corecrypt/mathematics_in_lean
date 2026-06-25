import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap End

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  rcases hx with ⟨hp, hq⟩
  rcases h with ⟨a, b, heq⟩
  rw [LinearMap.mem_ker] at hp hq
  have aeval_eq_id := congrArg (aeval φ) heq
  simp at aeval_eq_id
  have hh : x = (1 : End K V) x := rfl
  rw [hh, ← aeval_eq_id]
  rw [add_apply, mul_apply, mul_apply]
  rw [hp, hq]
  simp

#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  rcases h with ⟨a, b, heq⟩

  ext x
  constructor
  intro hx
  rcases Submodule.mem_sup.mp hx with ⟨s, hs, t, ht, rfl⟩
  rw [mem_ker] at *
  rw [map_add]
  nth_rw 1 [mul_comm]
  simp only [map_mul, mul_apply]
  rw [hs, ht]
  rw [map_zero, map_zero, add_zero]

  intro h
  have h' := h
  rw [mul_comm] at h
  rw [map_mul] at h h'

  have aeval_eq_id := congrArg (aeval φ) heq
  have equality := (LinearMap.congr_fun aeval_eq_id x).symm
  rw [map_one, one_apply] at equality
  rw [equality, map_add, add_comm]

  have lem (c R S : K[X]) (h : x ∈ ker ((aeval φ) S * (aeval φ) R))
    : ((aeval φ) (c * R)) x ∈ ker ((aeval φ) S) := by
    rw [mem_ker, ← mul_apply, ← map_mul]
    rw [← mul_assoc, mul_comm S c, mul_assoc, map_mul]
    rw [map_mul, mul_apply]
    rw [mem_ker.mp h]
    rw [map_zero]

  apply Submodule.add_mem_sup
  exact lem b Q P h'
  exact lem a P Q h

example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
