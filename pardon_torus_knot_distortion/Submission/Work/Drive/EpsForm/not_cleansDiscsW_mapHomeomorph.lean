import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.Drive.not_exists_weakCompressingLoop_of_counts

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

/-!
# `CleansDiscsW` is transported by an ambient homeomorphism of `ℝ³`

`Work.Drive.CleansDiscsW P` asks that every innermost disc of the parametrised torus `P`
bound a *weak* disc in the complement of its carrier.  The property is invariant under an
ambient homeomorphism `ψ` of `ℝ³`: the homeomorphism is a bijection of `ℝ³` carrying
`standard` to `ParamTorus.mapHomeomorph ψ`, hence carries innermost-disc data to
innermost-disc data (`InnermostDisc.mapHomeomorph` below) and weak bounding discs back
(`Work.Drive.boundsDiskInComplementW_mapHomeomorph_iff`).

Consequently the failure of `CleansDiscsW standard` is transported to every image torus.
-/

noncomputable section

/-- **Push an innermost-disc datum forward along an ambient homeomorphism of `ℝ³`.**

Every field is transported: the curve `α` and the family `curves i` by
`ClosedCurve.mapHomeomorph` (which preserves simpleness, essentiality, the range and
disjointness, using injectivity of `ψ`), the disc `e` by composition with `ψ`, the curve
`α` by the boundary relation, and the covering property by `mem_carrier_mapHomeomorph_iff`. -/
def InnermostDisc.mapHomeomorph (ψ : R3 ≃ₜ R3) {S : Set R3}
    (D : Work.InnermostDisk.InnermostDisc standard S) :
    Work.InnermostDisk.InnermostDisc (ParamTorus.mapHomeomorph ψ) (ψ '' S) := by
  refine
    { α := ClosedCurve.mapHomeomorph ψ D.α
      simple := ClosedCurve.mapHomeomorph_isSimple ψ D.α D.simple
      essential := ClosedCurve.isEssential_mapHomeomorph ψ D.α D.essential
      mem := ?_
      e := (homeomorphCMap ψ).comp D.e
      inj := ?_
      boundary := ?_
      e_mem := ?_
      ι := D.ι
      fintype := D.fintype
      curves := fun i => ClosedCurve.mapHomeomorph ψ (D.curves i)
      curves_simple := ?_
      curves_inessential := ?_
      curves_disjoint := ?_
      curves_subset := ?_
      covers := ?_ }
  · intro t; exact ⟨D.α.γ t, D.mem t, rfl⟩
  · intro z1 z2 hh
    exact D.inj (ψ.injective (by simpa using hh))
  · intro θ
    show ψ (D.e (circlePoint θ)) = ψ (D.α.γ θ)
    rw [D.boundary θ]
  · intro z; exact ⟨D.e z, D.e_mem z, rfl⟩
  · intro i; exact ClosedCurve.mapHomeomorph_isSimple ψ (D.curves i) (D.curves_simple i)
  · intro i hi
    exact D.curves_inessential i ((ClosedCurve.isEssential_mapHomeomorph_iff ψ (D.curves i)).mp hi)
  · intro i j hij
    rw [ClosedCurve.range_mapHomeomorph, ClosedCurve.range_mapHomeomorph]
    exact Set.disjoint_image_of_injective ψ.injective (D.curves_disjoint hij)
  · intro i X hX
    rw [ClosedCurve.range_mapHomeomorph] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    obtain ⟨z, hz⟩ := D.curves_subset i hY
    exact ⟨z, by simp [hz]⟩
  · intro z hz hmem
    have hmem' : ψ (D.e z) ∈ (ParamTorus.mapHomeomorph ψ).carrier := by
      simpa only [ContinuousMap.comp_apply, homeomorphCMap_apply] using hmem
    have hzstd : D.e z ∈ standard.carrier := (mem_carrier_mapHomeomorph_iff ψ (D.e z)).mp hmem'
    obtain ⟨i, hi⟩ := D.covers z hz hzstd
    refine ⟨i, ?_⟩
    rw [ClosedCurve.range_mapHomeomorph]
    exact ⟨D.e z, hi, rfl⟩

/-- If the standard torus admits no cleaning of discs, then neither does any of its images
under an ambient homeomorphism of `ℝ³`.

Suppose `CleansDiscsW (ParamTorus.mapHomeomorph ψ)` held.  Given an innermost-disc datum `D`
of the standard torus, push it forward along `ψ` (`InnermostDisc.mapHomeomorph`); the assumed
cleaning produces a weak bounding disc of `ClosedCurve.mapHomeomorph ψ D.α` in the complement
of the image torus, and `boundsDiskInComplementW_mapHomeomorph_iff` pulls it back to a weak
bounding disc of `D.α`, contradicting `h`. -/
theorem not_cleansDiscsW_mapHomeomorph
    (h : ¬ Work.Drive.CleansDiscsW Work.CoreTopology.standard) :
    ∀ ψ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3,
      ¬ Work.Drive.CleansDiscsW (Work.CoreTopology.ParamTorus.mapHomeomorph ψ) := by
  intro ψ hψ
  exact h fun S D =>
    (Work.Drive.boundsDiskInComplementW_mapHomeomorph_iff ψ D.α).mp
      (hψ (ψ '' S) (InnermostDisc.mapHomeomorph ψ D))

end

end Work.Drive.EpsForm
