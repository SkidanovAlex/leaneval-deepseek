import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Measure

open MeasureTheory

/-- Fubini's theorem for a function of four variables, grouped as two pairs, in the form of a
swap of the two iterated double integrals. -/
theorem integral_prod_prod_swap {α α' β β' E : Type*}
    [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {μ' : Measure α'} {ν : Measure β} {ν' : Measure β'}
    [SFinite μ] [SFinite μ'] [SFinite ν] [SFinite ν']
    (G : (α × α') × (β × β') → E)
    (hG : Integrable G ((μ.prod μ').prod (ν.prod ν'))) :
    (∫ a, ∫ a', ∫ b, ∫ b', G ((a, a'), (b, b')) ∂ν' ∂ν ∂μ' ∂μ)
      = ∫ b, ∫ b', ∫ a, ∫ a', G ((a, a'), (b, b')) ∂μ' ∂μ ∂ν' ∂ν := by
  have h1 : (∫ a, ∫ a', ∫ b, ∫ b', G ((a, a'), (b, b')) ∂ν' ∂ν ∂μ' ∂μ)
      = ∫ p : α × α', (∫ q : β × β', G (p, q) ∂(ν.prod ν')) ∂(μ.prod μ') := by
    refine (integral_congr_ae₂
      (f := fun a a' => ∫ b, ∫ b', G ((a, a'), (b, b')) ∂ν' ∂ν)
      (g := fun a a' => ∫ q : β × β', G ((a, a'), q) ∂(ν.prod ν')) ?_).trans ?_
    · filter_upwards [Measure.ae_ae_of_ae_prod (μ := μ) (ν := μ') hG.prod_right_ae] with a ha
      filter_upwards [ha] with a' ha'
      exact (integral_prod (fun q : β × β' => G ((a, a'), q)) ha').symm
    · exact (integral_prod (fun p : α × α' => ∫ q : β × β', G (p, q) ∂(ν.prod ν'))
        hG.integral_prod_left).symm
  have h2 : (∫ b, ∫ b', ∫ a, ∫ a', G ((a, a'), (b, b')) ∂μ' ∂μ ∂ν' ∂ν)
      = ∫ q : β × β', (∫ p : α × α', G (p, q) ∂(μ.prod μ')) ∂(ν.prod ν') := by
    refine (integral_congr_ae₂
      (f := fun b b' => ∫ a, ∫ a', G ((a, a'), (b, b')) ∂μ' ∂μ)
      (g := fun b b' => ∫ p : α × α', G (p, (b, b')) ∂(μ.prod μ')) ?_).trans ?_
    · filter_upwards [Measure.ae_ae_of_ae_prod (μ := ν) (ν := ν') hG.prod_left_ae] with b hb
      filter_upwards [hb] with b' hb'
      exact (integral_prod (fun p : α × α' => G (p, (b, b'))) hb').symm
    · exact (integral_prod (fun q : β × β' => ∫ p : α × α', G (p, q) ∂(μ.prod μ'))
        hG.integral_prod_right).symm
  rw [h1, ← integral_prod G hG, integral_prod_symm G hG, ← h2]

theorem integral_fin_fin_real_real_swap {m : ℕ} (Ψ : (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℂ)
    (h : MeasureTheory.Integrable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
        Ψ p.1.1 p.1.2 p.2.1 p.2.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) :
    (∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, ∫ t : ℝ, ∫ t' : ℝ, Ψ w w' t t')
      = ∫ t : ℝ, ∫ t' : ℝ, ∫ w : Fin m → ℝ, ∫ w' : Fin m → ℝ, Ψ w w' t t' := by
  exact integral_prod_prod_swap
    (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) => Ψ p.1.1 p.1.2 p.2.1 p.2.2) h

end Commons.Analysis.Measure