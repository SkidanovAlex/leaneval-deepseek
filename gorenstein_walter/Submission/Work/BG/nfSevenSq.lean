import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_abstractCoherence
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

/-!
# Area BG: the "seven squares" estimate `nfSevenSq`

A virtual character `Ψ ∈ ℤ[Irr K]` of squared norm `N ≤ 4` cannot have four pairwise
orthogonal `±Irr` constituents `g₁, g₂, g₃, φ` with equal Fourier coefficients
`⟨Ψ, gᵢ⟩ = ⟨Ψ, g₁⟩` (`i = 1, 2, 3`) and `⟨Ψ, φ⟩ = 2·⟨Ψ, g₁⟩`, unless that common
coefficient vanishes.

Indeed `⟨Ψ, gᵢ⟩ = m` is an integer (`Work.BG.inner_eq_int_and_sq_le`), and Bessel's
inequality (`OddOrder.RepresentationTheory.sum_sq_inner_le_of_orthonormal`) applied to the
orthonormal family `(g₁, g₂, g₃, φ)` gives

`N ≥ m² + m² + m² + (2m)² = 7m²`,

so `7m² ≤ N ≤ 4` and hence `m = 0`.  (The name refers to the `3·1² + 2² = 7` squares.)

The hypotheses `N : ℤ` and `⟩ Ψ Ψ ⟩ = (N : ℂ)` also force `N ≥ 0` (a squared norm is a sum
of squares of the integer Fourier coefficients), which is used to convert `N` into a
natural number for the Bessel bound.
-/

namespace Work.BG

open OddOrder.RepresentationTheory in
/-- The integer representing the squared norm of a virtual character is nonnegative:
`‖Ψ‖² = Σ c(χ)²` is a sum of squares of the integer Fourier coefficients. -/
lemma zirr_inner_self_nonneg {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {Ψ : ClassFunction K ℂ} (hΨ : Ψ ∈ ZIrr K) {N : ℤ}
    (hN : ClassFunction.inner Ψ Ψ = (N : ℂ)) :
    0 ≤ N := by
  obtain ⟨c, -, -, hnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hΨ
  have hcast : ((N : ℤ) : ℂ) = ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) := by
    rw [← hN, hnorm]; push_cast; ring
  have hNeq : N = ∑ a ∈ c.support, c a ^ 2 := Int.cast_injective hcast
  rw [hNeq]
  exact Finset.sum_nonneg fun a _ => sq_nonneg _

open OddOrder.RepresentationTheory in
theorem nfSevenSq {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {Ψ : ClassFunction K ℂ} (hΨ : Ψ ∈ ZIrr K) (N : ℤ)
    (hN : ClassFunction.inner Ψ Ψ = (N : ℂ)) (hN4 : N ≤ 4)
    {g₁ g₂ g₃ φ : ClassFunction K ℂ}
    (h1 : IsPmIrr g₁) (h2 : IsPmIrr g₂) (h3 : IsPmIrr g₃) (h4 : IsPmIrr φ)
    (h12 : ClassFunction.inner g₁ g₂ = 0) (h13 : ClassFunction.inner g₁ g₃ = 0)
    (h23 : ClassFunction.inner g₂ g₃ = 0)
    (h1φ : ClassFunction.inner g₁ φ = 0) (h2φ : ClassFunction.inner g₂ φ = 0)
    (h3φ : ClassFunction.inner g₃ φ = 0)
    (hΨ1 : ClassFunction.inner Ψ g₁ = ClassFunction.inner Ψ g₂)
    (hΨ2 : ClassFunction.inner Ψ g₁ = ClassFunction.inner Ψ g₃)
    (hΨφ : ClassFunction.inner Ψ φ = 2 * ClassFunction.inner Ψ g₁) :
    ClassFunction.inner Ψ g₁ = 0 := by
  -- `N` is the (nonnegative) squared norm, so we may read it as a natural number.
  have hNnn : 0 ≤ N := zirr_inner_self_nonneg hΨ hN
  have hNcast : ((N.toNat : ℕ) : ℂ) = (N : ℂ) := by
    have h1 : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hNnn
    exact_mod_cast h1
  -- The Fourier coefficient of `Ψ` at the signed irreducible `g₁` is an integer `m`.
  obtain ⟨m, hΨg1, -⟩ := inner_eq_int_and_sq_le hΨ N.toNat (by rw [hNcast]; exact hN) h1
  -- The orthonormal family `(g₁, g₂, g₃, φ)` and its coefficients `(m, m, m, 2m)`.
  let v : Fin 4 → ClassFunction K ℂ := fun i => match i.val with
    | 0 => g₁ | 1 => g₂ | 2 => g₃ | _ => φ
  let n : Fin 4 → ℤ := fun i => match i.val with
    | 0 => m | 1 => m | 2 => m | _ => 2 * m
  -- The reversed inner products (conjugate symmetry of `ClassFunction.inner`).
  have h21 : ClassFunction.inner g₂ g₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h12, star_zero]
  have h31 : ClassFunction.inner g₃ g₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h13, star_zero]
  have h32 : ClassFunction.inner g₃ g₂ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h23, star_zero]
  have hφ1 : ClassFunction.inner φ g₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h1φ, star_zero]
  have hφ2 : ClassFunction.inner φ g₂ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h2φ, star_zero]
  have hφ3 : ClassFunction.inner φ g₃ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h3φ, star_zero]
  -- Every member of the family is a virtual character.
  have hZv : ∀ i, v i ∈ ZIrr K := by
    intro i
    obtain ⟨mi, hi⟩ := i
    interval_cases mi
    · exact h1.mem_ZIrr
    · exact h2.mem_ZIrr
    · exact h3.mem_ZIrr
    · exact h4.mem_ZIrr
  -- The coefficients of `Ψ` at the family: `⟨Ψ, v₀⟩ = ⟨Ψ, v₁⟩ = ⟨Ψ, v₂⟩ = m`,
  -- `⟨Ψ, v₃⟩ = 2m`.
  have hn : ∀ i, ClassFunction.inner Ψ (v i) = (n i : ℂ) := by
    intro i
    obtain ⟨mi, hi⟩ := i
    interval_cases mi
    · exact hΨg1
    · exact hΨ1.symm.trans hΨg1
    · exact hΨ2.symm.trans hΨg1
    · exact (show ClassFunction.inner Ψ φ = ((2 * m : ℤ) : ℂ) from by
        rw [hΨφ, hΨg1]; push_cast; ring)
  -- Bessel: `∑ᵢ nᵢ² ≤ N`.
  have hbessel := sum_sq_inner_le_of_orthonormal hZv ?_ hΨ (hN.trans hNcast.symm) hn
  · -- The sum of the squared coefficients is `7m²`.
    have hsum : ∑ i : Fin 4, n i ^ 2 = 7 * m ^ 2 := by
      rw [Fin.sum_univ_four]
      simp [n]
      ring
    rw [hsum] at hbessel
    rw [Int.toNat_of_nonneg hNnn] at hbessel
    have hle : 7 * m ^ 2 ≤ 4 := le_trans hbessel hN4
    have hm2 : m ^ 2 = 0 := by
      have h0 : (0 : ℤ) ≤ m ^ 2 := sq_nonneg m
      omega
    have hm0 : m = 0 := by
      have h := hm2
      rw [pow_two] at h
      exact mul_self_eq_zero.mp h
    rw [hΨg1, hm0]
    norm_num
  · -- Orthonormality of the family: diagonal entries are `1` (norm-`1` signed
    -- irreducibles), off-diagonal entries vanish by hypothesis.
    intro i k
    by_cases hik : i = k
    · subst hik
      rw [ite_eq_left rfl]
      obtain ⟨mk, hk⟩ := i
      interval_cases mk
      · exact h1.inner_self
      · exact h2.inner_self
      · exact h3.inner_self
      · exact h4.inner_self
    · rw [ite_eq_right hik]
      have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
      obtain ⟨mi, hi⟩ := i
      obtain ⟨mj, hj⟩ := k
      have hne : mi ≠ mj := hval
      interval_cases mi <;> interval_cases mj
      all_goals first
        | exact absurd rfl hne
        | exact h12 | exact h13 | exact h23
        | exact h1φ | exact h2φ | exact h3φ
        | exact h21 | exact h31 | exact h32
        | exact hφ1 | exact hφ2 | exact hφ3

end Work.BG
