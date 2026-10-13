import Mathlib

namespace Work.WilE5.Calc

theorem clm_eq_sum_smul_proj {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ℝ) :
    ∃ lam : Fin k → ℝ, φ = ∑ a, lam a • (ContinuousLinearMap.proj a : (Fin k → ℝ) →L[ℝ] ℝ) := by
  refine ⟨fun a => φ (Pi.single a 1), ?_⟩
  ext x
  have hx : (∑ a, x a • (Pi.single a 1 : Fin k → ℝ)) = x := by
    have h := (Pi.basisFun ℝ (Fin k)).sum_repr x
    simpa [Pi.basisFun_apply, Pi.basisFun_repr] using h
  conv_lhs => rw [← hx]
  rw [map_sum]
  simp only [map_smul, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

end Work.WilE5.Calc
