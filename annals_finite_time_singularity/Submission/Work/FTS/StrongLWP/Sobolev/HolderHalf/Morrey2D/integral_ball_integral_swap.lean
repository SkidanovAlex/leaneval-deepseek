import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

theorem integral_ball_integral_swap {F : (ℝ × ℝ) → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {a : ℝ} (ha : 0 < a) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, (∫ t in (0 : ℝ)..1, F ζ t)
      = ∫ t in (0 : ℝ)..1, ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, F ζ t := by
  -- `F` is continuous, so it is integrable on any product of a compact slab and a compact ball;
  -- we then apply Fubini in the form `intervalIntegral_integral_swap`.
  have hcont : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1) :=
    hF.comp continuous_swap
  -- the compact set `[0,1] × closedBall 0 a`, which contains `uIoc 0 1 × ball 0 a`
  have hcpt : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hint : MeasureTheory.IntegrableOn (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) MeasureTheory.volume :=
    ContinuousOn.integrableOn_compact hcpt hcont.continuousOn
  have hsub : Set.uIoc (0 : ℝ) 1 ×ˢ Metric.ball (0 : ℝ × ℝ) a ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a := by
    intro p hp
    rw [Set.uIoc_of_le zero_le_one] at hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, Metric.ball_subset_closedBall hp.2⟩
  -- integrability of the uncurried integrand for the product measure
  have hInt : MeasureTheory.Integrable (fun p : ℝ × (ℝ × ℝ) => F p.2 p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := by
    rw [MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact MeasureTheory.IntegrableOn.mono_set hint hsub
  have hInt' : MeasureTheory.Integrable (Function.uncurry (fun t ζ => F ζ t))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := hInt
  exact (MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume.restrict (Metric.ball (0 : ℝ × ℝ) a))
    (f := fun t ζ => F ζ t) hInt').symm

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
