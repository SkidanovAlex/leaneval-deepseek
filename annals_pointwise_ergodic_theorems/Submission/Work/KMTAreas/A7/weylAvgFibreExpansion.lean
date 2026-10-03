import Mathlib
import Submission.Work.KMTAreas.A7.hiFibreCoeff_ident

namespace Work.KMTAreas.A7

theorem weylAvgFibreExpansion (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
        Work.KMTAreas.A7.varphiN N k₁ θ₁ * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
          * Work.KMTAreas.A7.weylAvg P N α₁ 0 θ₁ θ₂
          * Work.KMTAreas.A7.ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          fourier (T := 1) (n : ℤ) α₁
            * Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphiN N k₁) ((n : ℝ) - (p.1 : ℝ))
            * Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂)
                (Work.KMTAreas.A7.PevalR P (n : ℝ) - (p.2 : ℝ)) := by
  rw [weylAvg_fibre P N k₁ k₂ α₁ 0 p]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [acCoefW, psiHi, psiP]
  rw [fourier_eval_zero]
  ring

end Work.KMTAreas.A7
