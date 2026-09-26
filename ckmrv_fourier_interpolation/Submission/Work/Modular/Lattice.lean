import Mathlib

/-!
# Lattices and their theta series

This file sets up the theta series of a lattice `Λ ⊆ ℝⁿ` and the concrete lattices needed for
the CKMRV interpolation construction.

## Conventions

* `EuclideanSpace ℝ (Fin n)` carries the Euclidean (`ℓ²`) norm, so `‖x‖ ^ 2 = ∑ i, x i ^ 2`.
* The theta series is normalised *with* the factor `π`:
  `Θ_Λ τ = ∑_{x ∈ Λ} exp (π i τ ‖x‖ ^ 2)`.
  With `q = e^{2πiτ}` this is `∑_{x ∈ Λ} q ^ (‖x‖ ^ 2 / 2)`, so an even lattice (`‖x‖ ^ 2 ∈ 2ℤ`)
  produces a power series in `q` with natural-number exponents.
* `E8` is the standard model: the vectors of `ℝ⁸` whose coordinates are pairwise congruent
  modulo `1` (equivalently all integral or all half-integral) and whose coordinate sum is even.
  Its shortest nonzero vectors have squared length `2`: the `112` vectors `±e_i ± e_j`
  (`i < j`) and the `128` vectors `(±1/2, …, ±1/2)` with an even number of minus signs.
-/

open UpperHalfPlane
open scoped Real MatrixGroups

namespace Work.Modular

/-- The summand `exp (π i τ ‖x‖ ^ 2)` of the theta series. -/
noncomputable def thetaTerm {n : ℕ} (τ : ℍ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (π * Complex.I * (τ : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ))

@[simp]
theorem thetaTerm_zero {n : ℕ} (τ : ℍ) :
    thetaTerm τ (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  simp [thetaTerm]

/-- The theta series `Θ_Λ τ = ∑_{x ∈ Λ} exp (π i τ ‖x‖ ^ 2)` of a submodule `Λ ⊆ ℝⁿ`. -/
noncomputable def thetaSeries {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (τ : ℍ) : ℂ :=
  ∑' x : L, thetaTerm τ (x : EuclideanSpace ℝ (Fin n))

/-- A lattice (submodule of `ℝⁿ`) is *even* if the squared length of every vector is an even
integer. -/
def IsEvenSubmodule {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ L, ∃ k : ℕ, ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 2 * k

/-- The `E₈` lattice in the standard model: vectors of `ℝ⁸` whose coordinates are either all
integers or all half-integers (equivalently, pairwise congruent modulo `1`) and whose coordinate
sum is even. -/
noncomputable def E8 : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) where
  carrier := {x | (∀ i, ∃ m : ℤ, 2 * x.ofLp i = (m : ℝ)) ∧
                  (∀ i j, ∃ m : ℤ, x.ofLp i - x.ofLp j = (m : ℝ)) ∧
                  (∃ m : ℤ, ∑ i, x.ofLp i = 2 * (m : ℝ))}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact ⟨0, by simp⟩
    · intro i j; exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨m, hm⟩ := hx1 i
      obtain ⟨n, hn⟩ := hy1 i
      refine ⟨m + n, ?_⟩
      simp only [WithLp.ofLp_add, Pi.add_apply]
      push_cast
      linear_combination hm + hn
    · intro i j
      obtain ⟨m, hm⟩ := hx2 i j
      obtain ⟨n, hn⟩ := hy2 i j
      refine ⟨m + n, ?_⟩
      simp only [WithLp.ofLp_add, Pi.add_apply]
      push_cast
      linear_combination hm + hn
    · obtain ⟨m, hm⟩ := hx3
      obtain ⟨n, hn⟩ := hy3
      refine ⟨m + n, ?_⟩
      simp only [WithLp.ofLp_add, Pi.add_apply, Finset.sum_add_distrib]
      push_cast
      linear_combination hm + hn
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨m, hm⟩ := hx1 i
      refine ⟨c * m, ?_⟩
      simp only [WithLp.ofLp_smul, Pi.smul_apply, zsmul_eq_mul]
      push_cast
      linear_combination (c : ℝ) * hm
    · intro i j
      obtain ⟨m, hm⟩ := hx2 i j
      refine ⟨c * m, ?_⟩
      simp only [WithLp.ofLp_smul, Pi.smul_apply, zsmul_eq_mul]
      push_cast
      linear_combination (c : ℝ) * hm
    · obtain ⟨m, hm⟩ := hx3
      refine ⟨c * m, ?_⟩
      simp only [WithLp.ofLp_smul, Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum]
      push_cast
      linear_combination (c : ℝ) * hm

@[simp]
theorem mem_E8 {x : EuclideanSpace ℝ (Fin 8)} :
    x ∈ E8 ↔ (∀ i, ∃ m : ℤ, 2 * x.ofLp i = (m : ℝ)) ∧
             (∀ i j, ∃ m : ℤ, x.ofLp i - x.ofLp j = (m : ℝ)) ∧
             (∃ m : ℤ, ∑ i, x.ofLp i = 2 * (m : ℝ)) := Iff.rfl

end Work.Modular

namespace Work.Modular

/-- The dual lattice `Λ* = {y : ℝⁿ | ⟪y, x⟫ ∈ ℤ for all x ∈ Λ}` of a submodule `Λ ⊆ ℝⁿ`. -/
noncomputable def dualLattice {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) where
  carrier := {y | ∀ x ∈ L, ∃ m : ℤ, inner ℝ y x = (m : ℝ)}
  zero_mem' := by
    intro x _
    exact ⟨0, by simp⟩
  add_mem' := by
    intro y z hy hz x hx
    obtain ⟨m, hm⟩ := hy x hx
    obtain ⟨k, hk⟩ := hz x hx
    exact ⟨m + k, by rw [inner_add_left, hm, hk]; push_cast; ring⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨m, hm⟩ := hy x hx
    refine ⟨c * m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ c y, real_inner_smul_left, hm]
    push_cast
    ring

/-- The covolume of a lattice, as the volume of a fundamental domain. -/
noncomputable def covolume {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ZLattice.covolume L

end Work.Modular
