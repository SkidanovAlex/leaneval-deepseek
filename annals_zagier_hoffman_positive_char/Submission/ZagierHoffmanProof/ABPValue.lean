import Submission.ZagierHoffmanProof.ABPPoly
import Submission.Commons.LinearAlgebra.Matrix.exists_smul_of_mul_eq_zero

/-!
# The final value step of the ABP criterion

If `P ψ = 0`, `P(θ) ≠ 0`, and `P(θ) ϑ = 0` where the columns of `ϑ` are linearly independent and
`ρ ≠ 0` satisfies `ρ ϑ = 0`, then `P(θ) = λ ρ` for some `λ ≠ 0`, and after rescaling `P` by
`λ⁻¹` we obtain a row vector `P'` with `P' ψ = 0` and `P'(θ) = ρ`.
-/

set_option autoImplicit false
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K]

/-- ★ **The final value step of the ABP criterion.** -/
theorem final_value_step {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) K}
    (hind : LinearIndependent K (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i))
    {ρ : Fin ℓ → K} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0) {θ : K}
    {ψ : Fin ℓ → PowerSeries K} {P : Fin ℓ → Polynomial K}
    (hPψ : ∑ j, ((P j : Polynomial K) : PowerSeries K) * ψ j = 0)
    (hPϑ : Matrix.vecMul (fun j => (P j).eval θ) ϑ = 0)
    (hP0 : (fun j => (P j).eval θ) ≠ 0) :
    ∃ P' : Fin ℓ → Polynomial K,
      (∑ j, ((P' j : Polynomial K) : PowerSeries K) * ψ j = 0) ∧
      (∀ j, (P' j).eval θ = ρ j) := by
  classical
  obtain ⟨lam, hlam⟩ := Commons.LinearAlgebra.Matrix.exists_smul_of_mul_eq_zero hℓ hind hρ hρ0 hPϑ
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hP0
    funext j
    simp [congrFun hlam j, h0]
  refine ⟨fun j => Polynomial.C lam⁻¹ * P j, ?_, ?_⟩
  · have h1 : (∑ j, (((Polynomial.C lam⁻¹ * P j : Polynomial K)) : PowerSeries K) * ψ j)
        = (Polynomial.C lam⁻¹ : PowerSeries K) * ∑ j, ((P j : Polynomial K) : PowerSeries K) * ψ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coe_mul, Polynomial.coe_C]
      ring
    rw [h1, hPψ, mul_zero]
  · intro j
    rw [Polynomial.eval_mul, Polynomial.eval_C, congrFun hlam j, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hlam0, one_mul]

end ZagierHoffmanPositiveChar
