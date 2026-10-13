import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

theorem aesm_weighted_prod_restricted {α : ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn} {A : Set ℝ}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume)) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
  -- `DomM` is dominated by the planar Lebesgue measure, hence so is the product measure;
  -- a.e. strong measurability is preserved when the measure is made smaller.
  have hle : (MeasureTheory.volume.restrict A).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM
      ≤ (MeasureTheory.volume.restrict A).prod
          (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    MeasureTheory.Measure.prod_mono le_rfl
      Work.FTS.StrongEps.EpsLocalPStar.DomM_le_volume
  have hΦ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    h.mono_measure hle
  -- the weight `epsW α` is (everywhere) measurable, so a.e. strongly measurable for any measure.
  have hw : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    ((Work.FTS.StrongEps.EpsLocalPStar.measurable_epsW α).comp measurable_snd).aestronglyMeasurable
  exact hΦ.mul hw

end Work.FTS.EpsEngine
