import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph
import Submission.Lib.Unif2.PackagingOpen
import Submission.Work.FatouCH.injEntireAffineGrowth

namespace Work.BasinSC.StepOneCrit

open scoped Manifold ContDiff
open Set

/-- An open proper subset of `ℂ` is not biholomorphic to `ℂ`: if `E : ↥U ≃ₘ ℂ` with
`U = ⟨V, hVo⟩`, then `F := fun z => ↑(E.symm z)` is an injective entire function, hence affine with
non-zero slope by `Work.FatouCH.injEntire_affine_growth` (module
`Submission.Work.FatouCH.injEntireAffineGrowth`), hence surjective; but its range is `V`, so
`V = Set.univ`.  `F` is entire because the chart representation of the diffeomorphism `E.symm` is
analytic: `Work.Parabolic.analyticAt_chart_representation_infty` (module
`Submission.Lib.Unif2.Work.Parabolic.harmonicOnX_comp_biholomorph`) with `X = ℂ` and
`chartAt_self_eq`, plus `Submission.opens_chartAt_apply` (module
`Submission.Lib.Unif2.PackagingOpen`) to read the target chart. -/
theorem no_diffeomorph_plane {V : Set ℂ} (hVo : IsOpen V) (hVproper : V ≠ Set.univ) :
    ¬ Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (↥(⟨V, hVo⟩ : TopologicalSpace.Opens ℂ)) ℂ ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  set U : TopologicalSpace.Opens ℂ := ⟨V, hVo⟩ with hUdef
  rintro ⟨E⟩
  set F : ℂ → ℂ := fun z => ((E.symm z : U) : ℂ) with hFdef
  have han : ∀ x : ℂ, AnalyticAt ℂ F x := by
    intro x
    have h := Work.Parabolic.analyticAt_chart_representation_infty (Φ := ⇑E.symm) E.symm.contMDiff x
    rw [show chartAt ℂ x = OpenPartialHomeomorph.refl ℂ from chartAt_self_eq] at h
    simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq] at h
    have heq : (fun z => (chartAt ℂ (E.symm x)) (E.symm z)) = F := by
      funext z
      rw [hFdef]
      exact Submission.opens_chartAt_apply U (E.symm x) (E.symm z)
    rwa [heq] at h
  have hdiff : Differentiable ℂ F := fun x => (han x).differentiableAt
  have hinj : Function.Injective F := by
    intro z₁ z₂ h
    rw [hFdef] at h
    exact E.symm.injective (Subtype.coe_injective h)
  obtain ⟨a, b, ha, hab⟩ := Work.FatouCH.injEntire_affine_growth hdiff hinj
  have hsurj : Function.Surjective F := by
    intro w
    refine ⟨(w - b) / a, ?_⟩
    rw [hab]
    field_simp
    ring
  refine hVproper (Set.eq_univ_of_forall fun v => ?_)
  obtain ⟨z, hz⟩ := hsurj v
  have hw : F z ∈ V := by
    rw [hFdef]
    exact (E.symm z).2
  rwa [hz] at hw

end Work.BasinSC.StepOneCrit
