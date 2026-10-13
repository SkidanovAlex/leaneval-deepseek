import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory

/-- Restriction form of `EpsLocalPStar.AK2_sections`: if the uncurried family
`(s, z, θ) ↦ Φ s z θ` is a.e.-strongly-measurable with respect to
`(volume ↾ A) ⊗ volume`, then for a.e. `s ∈ A` the profile `Φ s` is `AK2`. -/
theorem AK2_sections_restrict {α : ℝ} {A : Set ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume)) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict A),
      Work.FTS.StrongEps.EpsLocalPStar.AK2 α (Φ s) := by
  have h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict A),
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Φ s p.1 p.2) (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    h.prodMk_left (ν := (MeasureTheory.volume : Measure (ℝ × ℝ)))
  filter_upwards [h2] with s hs
  unfold Work.FTS.StrongEps.EpsLocalPStar.AK2
  have hs' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Φ s p.1 p.2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    hs.mono_measure Work.FTS.StrongEps.EpsLocalPStar.DomM_le_volume
  refine (hs'.mul (Work.FTS.StrongEps.EpsLocalPStar.measurable_epsW α).aestronglyMeasurable).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

end Work.FTS.EpsEngine
