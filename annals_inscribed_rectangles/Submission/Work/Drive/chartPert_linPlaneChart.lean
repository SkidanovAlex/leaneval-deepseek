import Mathlib
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.chartPertData

namespace Work.Drive

/-- The chart perturbation of a *linear* plane chart is again a linear plane chart, with the
functional transported by `Work.Drive.classEquiv τ` and the level scaled by `Work.Drive.levelScale τ`.

(`linPlaneChart φ lam hlam z` has level `lam` and class `[φ (linVecC z)]`
— `Work.Drive.cappingSpaceHomeoProj_linPlaneChart` — and `chartPert τ` acts as
`(level ↦ levelScale τ level, class ↦ classMap τ class)` with `classMap τ [v] = [classEquiv τ v]`
— `Work.Drive.classMap_mk`.)  Both reviewers checked the two sub-identities in Lean; what remains is
`Prod.ext`/`Projectivization.mk_eq_mk_iff` bookkeeping.  This is the input (i) of the lead's 23:55
assignment to the node `chainParity`, needed to keep the *reference* plane of the antisymmetry
computation linear after the chart perturbation. -/
theorem chartPert_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (τ : Eucl 3) :
    Work.Drive.chartPert τ ∘ Work.Drive.linPlaneChart φ lam hlam
      = Work.Drive.linPlaneChart (φ.trans (Work.Drive.classEquiv τ))
          (((Work.Drive.levelScale τ ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) : ℝ)
          (Work.Drive.levelScale τ ⟨lam, hlam⟩).2 := by
  funext z
  apply cappingSpaceHomeoProj.injective
  have hA := cappingSpaceHomeoProj_chartPert τ (linPlaneChart φ lam hlam z)
  have hB := cappingSpaceHomeoProj_linPlaneChart φ lam hlam z
  have hR := cappingSpaceHomeoProj_linPlaneChart (φ.trans (classEquiv τ))
    (↑(levelScale τ ⟨lam, hlam⟩)) ((levelScale τ ⟨lam, hlam⟩).2) z
  rw [Function.comp_apply, hA, hB, hR]
  refine Prod.ext (Subtype.ext rfl) ?_
  simp only [coordFam_snd, classMap_mk]
  refine (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, ContinuousLinearEquiv.trans_apply]

end Work.Drive
