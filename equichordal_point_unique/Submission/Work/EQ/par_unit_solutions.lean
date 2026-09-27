import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra

namespace Work.EQ

/-- **The two preimages along a nondegenerate direction.**  If `ρ ≠ 0` and `ρ ^ 2 = bsq Z`, and
`X` is a unit vector of the bilinear form `z₁² + z₂²` parallel to `Z`, then `X` is one of the
two vectors `±ρ⁻¹ • Z`. -/
theorem par_unit_solutions {Z X : ℂ × ℂ} {ρ : ℂ}
    (hρne : ρ ≠ 0) (hρ : ρ ^ 2 = bsq Z) (hX : bsq X = 1) (hpar : par X Z) :
    X = (ρ⁻¹) • Z ∨ X = -(ρ⁻¹) • Z := by
  -- `Z` cannot vanish, since `bsq Z = ρ ^ 2 ≠ 0`.
  have hZne : Z ≠ 0 := by
    intro h0
    have h0' : ρ ^ 2 = 0 := by rw [hρ, h0]; simp [bsq]
    rw [pow_two] at h0'
    exact hρne (mul_self_eq_zero.mp h0')
  -- Parallelism gives `X = σ • Z` for some `σ`.
  obtain ⟨σ, hσ⟩ := exists_smul_of_par (X := Z) (Y := X) (par_comm.mpr hpar) hZne
  -- Normalising with `bsq` gives `(σ * ρ) ^ 2 = 1`.
  have hsq : σ ^ 2 * bsq Z = 1 := by
    have hh : bsq (σ • Z) = 1 := by rw [← hσ]; exact hX
    rwa [bsq_smul] at hh
  have key : (σ * ρ) ^ 2 = 1 := by
    rw [mul_pow, hρ]
    exact hsq
  -- Hence `σ = ρ⁻¹` or `σ = -ρ⁻¹`.
  rw [pow_two] at key
  rcases mul_self_eq_one_iff.mp key with hk | hk
  · left
    have hσρ : σ = ρ⁻¹ := eq_inv_of_mul_eq_one_left hk
    rw [hσ, hσρ]
  · right
    have hk' : σ * (-ρ) = 1 := by rw [mul_neg, hk, neg_neg]
    have hσρ : σ = -(ρ⁻¹) := by
      have := eq_inv_of_mul_eq_one_left hk'
      rwa [inv_neg] at this
    rw [hσ, hσρ]

end Work.EQ
