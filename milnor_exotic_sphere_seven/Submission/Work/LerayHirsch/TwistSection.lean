import Mathlib
import Submission.Work.LerayHirsch.TautTwist
import Submission.Work.LerayHirsch.TautEmbedCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The tautological nowhere-zero section of `ℓ^* ⊗ π^*E`, and re-indexing of gluing data

This module contains the *definitions* used by the proof of the splitting principle
`Work.LerayHirsch.SplitsOverProj` (see `Submission/Work/LerayHirsch/SplitsOverProj.lean`):

* `Work.LerayHirsch.tautSectionVec` — the fibre coordinate of the tautological section of
  `Work.LerayHirsch.tautTwist Z = ℓ^* ⊗ π^*E` over `P(E)`, in the *preferred* chart
  `(tautLine Z).indexAt x` of `ℓ` and `Z.indexAt (π x)` of `E`: it is the normalised representative
  of `x` (`Work.LerayHirsch.TautEmbed.chartRatioVec`).  The section it defines is the identity map
  `ℓ_x → E_x`, read through the identification `ℓ^* ⊗ E ≅ Hom(ℓ, E)`; it is the input of
  `Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact`.

(The complement produced by Whitney's splitting lemma is re-presented over the cover
`ι × Fin (m+1)` of the tautological line bundle by `Work.Agree.reindexCore` /
`Work.Agree.nonempty_bundleIso_reindexCore_self`, in `SplitsOverProj.lean`.)
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The tautological section of `ℓ^* ⊗ π^*E` -/

/-- **The fibre coordinate of the tautological section of `ℓ^* ⊗ π^*E`** over `x ∈ P(E)`, read in
the preferred chart `(tautLine Z).indexAt x` of `ℓ` and the preferred chart `Z.indexAt (π x)` of
`E`: the representative of `x` normalised so that its `k`-th coordinate in the chart
`(tautLine Z).indexAt x` equals `1`. -/
def tautSectionVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (x : ProjSpace Z) : EuclideanSpace ℂ (Fin (m + 1)) :=
  TautEmbed.chartRatioVec Z ((tautLine Z).indexAt x).1 ((tautLine Z).indexAt x).2
    (Z.indexAt (projMap Z x)) x

/-- The tautological section of `ℓ^* ⊗ π^*E`, as a map into the total space of the twist. -/
def tautSectionRaw (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ProjSpace Z → (tautTwist Z).TotalSpace :=
  fun x => ⟨x, tautSectionVec Z x⟩

end

end Work.LerayHirsch
