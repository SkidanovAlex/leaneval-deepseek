import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.V5Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫⁻ V5 ≤ liminf ∫⁻ ofReal (HkIntegrand α 5 (fn n))`

`V5 α fn p` is *defined* as the `liminf`, as `n → ∞`, of `ofReal (HkIntegrand α 5 (fn n) p)`
(see `V5Defs`), so the inequality is exactly Fatou's lemma for the sequence of a.e.-measurable
functions `n ↦ ENNReal.ofReal (HkIntegrand α 5 (fn n) ·)`: the only hypothesis needed is the
a.e.-measurability of the members, which is the hypothesis `hmeas` of the statement.  Nothing
about the rectangle, or about `α`, is used. -/

namespace Work.FTS.StrongEps.LocUnif

theorem lintegral_V5_le_liminf {α : ℝ} {fn : ℕ → ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hmeas : ∀ n, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d), Work.FTS.StrongEps.LocUnif.V5 α fn p
      ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2)) Filter.atTop := by
  -- `V5 α fn p = liminf_n ofReal (HkIntegrand α 5 (fn n) p)`, so this is Fatou's lemma
  simpa only [Work.FTS.StrongEps.LocUnif.V5] using
    MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (u := Filter.atTop)
      (f := fun (n : ℕ) (p : ℝ × ℝ) =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
      hmeas

end Work.FTS.StrongEps.LocUnif
