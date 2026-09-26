import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DivisorLowerEAux

namespace Work.Asymptotics

theorem divisor_lower_E :
    ∀ ρ : ℝ, 0 < ρ → ∃ c : ℝ, 0 < c ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ρ * t ^ 2 ≤ ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖) →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  intro ρ hρ
  obtain ⟨cA, TA, hcA0, hTA0, hTA1, hA⟩ := DivisorLowerE.divisor_lower_E_small_t ρ hρ
  obtain ⟨cB, hcB0, hB⟩ := DivisorLowerE.divisor_lower_E_large_t ρ TA hρ hTA0 hTA1
  refine ⟨min cA cB, lt_min hcA0 hcB0, ?_⟩
  intro w t ht hwE ht1 hcon
  have hsmall := hA w t ht hwE
  have hlarge := hB w t ht hwE
  by_cases h : t ≤ TA
  · exact le_trans (min_le_left _ _) (hsmall h hcon)
  · exact le_trans (min_le_right _ _) (hlarge (le_of_lt (not_le.mp h)) ht1 hcon)

end Work.Asymptotics
