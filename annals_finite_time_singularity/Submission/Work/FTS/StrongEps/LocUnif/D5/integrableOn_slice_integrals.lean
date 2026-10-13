import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem integrableOn_slice_integrals {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc a b ×ˢ Set.Icc c d)) :
    MeasureTheory.IntegrableOn (fun θ => ∫ z in a..b, f z θ) (Set.Ioc c d) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in c..d, f z θ) (Set.Ioc a b) := by
  -- `f` is integrable on the compact rectangle `[a,b] × [c,d]`
  have hK : MeasureTheory.Integrable (Function.uncurry f)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- turn the restricted product measure into a product of restricted measures
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict] at hK
  -- the interval integral over `[a,b]` is the set integral over `Icc a b`
  have hset : ∀ {a b : ℝ}, a ≤ b → ∀ g : ℝ → ℝ,
      (∫ x in Set.Icc a b, g x) = ∫ x in a..b, g x := by
    intro a b hab g
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
  constructor
  · -- Fubini: the `z`-marginal is integrable in `θ`, then shrink `Icc c d` to `Ioc c d`
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    refine (hK.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    exact hset hab (fun z => f z θ)
  · -- Fubini: the `θ`-marginal is integrable in `z`, then shrink `Icc a b` to `Ioc a b`
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    refine (hK.integral_prod_left).congr (Filter.Eventually.of_forall fun z => ?_)
    exact hset hcd (fun θ => f z θ)

end Work.FTS.StrongEps.LocUnif.D5
