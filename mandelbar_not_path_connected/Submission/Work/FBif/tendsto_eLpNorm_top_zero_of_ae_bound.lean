import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ENNReal

namespace Work.FBif

theorem tendsto_eLpNorm_top_zero_of_ae_bound {μs : ℕ → ℂ → ℂ} {εs : ℕ → ℝ}
    (hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (μs n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hε : Filter.Tendsto εs Filter.atTop (nhds 0))
    (hb : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μs n z‖ ≤ εs n) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (μs n) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, MeasureTheory.eLpNorm (μs n) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      ≤ ENNReal.ofReal (εs n) := by
    intro n
    rw [MeasureTheory.eLpNorm_exponent_top (hmeas n)]
    exact MeasureTheory.eLpNormEssSup_le_of_ae_bound (hb n)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ENNReal)) (h := fun n => ENNReal.ofReal (εs n))
  · exact tendsto_const_nhds
  · simpa using ENNReal.tendsto_ofReal hε
  · exact fun n => bot_le
  · exact hbound

end Work.FBif
