import Mathlib
import Submission.Work.ZeroDensity.Zeta.sinTailAux
import Submission.Work.ZeroDensity.Zeta.sinTailBoundsSelf

namespace Work.ZeroDensity.Zeta

noncomputable section

theorem sinTailUniform : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1000000 ≤ t → ∀ A : ℝ, 1 ≤ A →
    ‖∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1)‖
      ≤ C / t := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := SinSelf.expI_boundSelf
  refine ⟨(8 + C₁) / 2, by linarith, ?_⟩
  intro t ht A hA
  have ht4 : 4 ≤ t := by linarith
  have hexp : -((1 / 2 : ℂ) + (t : ℂ) * Complex.I) - 1 = SinAux.ct t - 1 := by
    simp only [SinAux.ct]; ring
  rw [hexp]
  have hJp : ∀ B : ℝ, A ≤ B →
      ‖∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (Complex.I * (v : ℂ))‖ ≤ C₁ :=
    fun B hB => hC₁ t ht4 A B hA hB
  have hJm : ∀ B : ℝ, A ≤ B →
      ‖∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (-(Complex.I * (v : ℂ)))‖ ≤ 4 :=
    fun B hB => SinSelf.expNegI_boundSelf t (by linarith) A B hA hB
  have hbound := SinAux.sinTailIoi t ht4 hA hC₁pos hJp hJm
  calc ‖∫ v in Set.Ioi A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (SinAux.ct t - 1)‖
      ≤ (8 + C₁) / (2 * t) := hbound
    _ = (8 + C₁) / 2 / t := by ring

end

end Work.ZeroDensity.Zeta
