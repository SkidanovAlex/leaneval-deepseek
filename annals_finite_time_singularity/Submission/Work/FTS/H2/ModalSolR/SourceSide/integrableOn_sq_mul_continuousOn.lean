import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.ModalSol.Auxiliary.integrableOn_mul_of_sq_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.H2.ModalSolR.SourceSide

theorem integrableOn_sq_mul_continuousOn {c : ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun z => c z ^ 2) (Set.Ioi 0))
    {a b c₀ d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c₀) (hcd : c₀ ≤ d)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a b ×ˢ Set.Icc c₀ d)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => c p.1 ^ 2 * g p)
      (Set.Icc a b ×ˢ Set.Icc c₀ d) := by
  -- `[a,b] ⊆ (0,∞)`, so the hypothesis on `c ^ 2` restricts to `[a,b]`.
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  -- `volume` on `ℝ × ℝ` restricted to the rectangle is the product of the two restrictions.
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Set.Icc c₀ d)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c₀ d)) :=
    (Measure.prod_restrict (Set.Icc a b) (Set.Icc c₀ d)).symm
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc c₀ d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact isCompact_Icc.measure_lt_top⟩
  -- `p ↦ c p.1 ^ 2 = d p.1` is integrable on the rectangle (Fubini-trivial), and `g` is
  -- continuous hence bounded there: `IntegrableOn.mul_continuousOn` finishes.
  refine MeasureTheory.IntegrableOn.mul_continuousOn ?_ hg (isCompact_Icc.prod isCompact_Icc)
  rw [MeasureTheory.IntegrableOn, hprod]
  exact (hc2.mono_set hsub).comp_fst _

end Work.FTS.H2.ModalSolR.SourceSide
