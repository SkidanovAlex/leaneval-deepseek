import Mathlib.Analysis.Polynomial.Norm
import Submission.Commons.Analysis.Polynomial.aeval_norm_le
import Submission.Commons.Analysis.Polynomial.root_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

lemma aeval_bound_at_root {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖)
    (f₁ f₂ : Polynomial K) (hf₁ : 1 ≤ f₁.natDegree) {α : L}
    (hα : Polynomial.aeval α f₁ = 0) :
    ‖(Polynomial.aeval α) f₂‖ ≤
      ((f₂ - f₁).natDegree + 1 : ℝ) * (f₂ - f₁).supNorm *
        (max 1 (max 1 ((f₁.natDegree : ℝ) * f₁.supNorm / ‖f₁.coeff f₁.natDegree‖))) ^
          (f₂ - f₁).natDegree := by
  set M : ℝ :=
    max 1 (max 1 ((f₁.natDegree : ℝ) * f₁.supNorm / ‖f₁.coeff f₁.natDegree‖)) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact le_max_left _ _
  -- `root_norm_le` bounds `‖α‖` by `max 1 a`, and `M` dominates that.
  have hroot : ‖α‖ ≤ M := by
    refine (root_norm_le h_ext f₁ hf₁ hα).trans ?_
    rw [hM]
    exact le_max_right _ _
  -- the difference `f₂ - f₁` vanishes at `α`
  have hkey : (Polynomial.aeval α) f₂ = (Polynomial.aeval α) (f₂ - f₁) := by
    have h : (Polynomial.aeval α) (f₂ - f₁) = (Polynomial.aeval α) f₂ - (Polynomial.aeval α) f₁ :=
      map_sub (Polynomial.aeval α) f₂ f₁
    rw [h, hα, sub_zero]
  rw [hkey]
  refine (aeval_norm_le h_ext (f₂ - f₁) α).trans ?_
  have hmax : max 1 ‖α‖ ≤ M := max_le hM1 hroot
  have hpow : (max 1 ‖α‖) ^ (f₂ - f₁).natDegree ≤ M ^ (f₂ - f₁).natDegree :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ max 1 ‖α‖) hmax _
  have hnonneg : (0 : ℝ) ≤ ((f₂ - f₁).natDegree + 1 : ℝ) * (f₂ - f₁).supNorm :=
    mul_nonneg (by positivity) (Polynomial.supNorm_nonneg _)
  exact mul_le_mul_of_nonneg_left hpow hnonneg

end Commons.Analysis.Polynomial
