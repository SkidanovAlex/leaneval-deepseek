import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

/-- Joint continuity of the two-slot insertion `ins2` with the remaining
particle configuration taken as the *first* variable (the variable order that
occurs in the fibre integral `r ↦ ∫_q B (ins2 i j' q.1 q.2 r) w₁(q)`). -/
lemma continuous_ins2_swap {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    Continuous (fun z : Submission.BoseGases.X p ×
        (Submission.BoseGases.kcE3 × Submission.BoseGases.kcE3) =>
      Submission.BoseGases.ins2 i j' z.2.1 z.2.2 z.1) := by
  change Continuous (fun z : Submission.BoseGases.X p ×
      (Submission.BoseGases.kcE3 × Submission.BoseGases.kcE3) =>
    Submission.BoseGases.kcInsN (p + 1) i
      (z.2.1, Submission.BoseGases.kcInsN p j' (z.2.2, z.1)))
  exact (Submission.BoseGases.kcInsN_cont i).comp (Continuous.prodMk (by fun_prop)
    ((Submission.BoseGases.kcInsN_cont j').comp (by fun_prop)))

lemma aesm_fibre_integral {p : ℕ} {s : ℝ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    {B : Submission.BoseGases.X (p + 2) → ℝ} (hB : Continuous B)
    {w1 : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw1m : MeasureTheory.AEStronglyMeasurable w1
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s))) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X p =>
        ∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s,
          B (Submission.BoseGases.ins2 i j' q.1 q.2 r) * w1 q)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict (Submission.BoseGases.abox p s)) := by
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun z : Submission.BoseGases.X p ×
          (Submission.BoseGases.kcE3 × Submission.BoseGases.kcE3) =>
        B (Submission.BoseGases.ins2 i j' z.2.1 z.2.2 z.1) * w1 z.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict
          (Submission.BoseGases.abox p s)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s))) :=
    (hB.comp (continuous_ins2_swap (p := p) i j')).aestronglyMeasurable.mul (hw1m.comp_snd)
  have h := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict
      (Submission.BoseGases.abox p s))
    (ν := MeasureTheory.volume.restrict (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s)) hF
  simpa only using h

end Work.SmallBoxA0
