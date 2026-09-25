import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.iw_superset_bound

/-!
# The Ionescu–Wainger input of the MST chapter, unconditionally

`Maximal/mst_scalar_defs.lean` states the estimates of the MST §3–§6 chapter against the corrected
IW input `IWSupersetBoundLift` (the older `IWSupersetBound` of `Maximal/iw_superset.lean` was
vacuous when its Mikhlin hypotheses were phrased for the periodisation; see `MST_H3_CLAIMS.md` §4).
The IW lane has since restated and **proved** `IWSupersetBound` in exactly the corrected form
(`Maximal/iw_superset_bound.lean`, `iwSupersetBound_proof`, axiom-clean).  The two `Prop`s differ
only in the order of hypotheses that do not depend on one another, so `IWSupersetBoundLift` follows.
-/

namespace Work.BourgainPlan.Maximal

/-- `IWSupersetBoundLift` from the landed (and proved) `IWSupersetBound`. -/
theorem iwSupersetBoundLift_of_iwSupersetBound
    (h : Work.BourgainPlan.Maximal.IWSupersetBound) :
    Work.BourgainPlan.Maximal.IWSupersetBoundLift := by
  intro ρ hρ p hp
  obtain ⟨C, hC, N₁, hN⟩ := h ρ hρ p hp
  refine ⟨C, hC, N₁, ?_⟩
  intro N hNle ε hε0 hεle ψ hψ hcd A hA hbd hder hder2 hsupp f hf
  exact hN N hNle ε hε0 hεle ψ hψ hsupp A hA hcd hbd hder hder2 f hf

/-- **The IW input of the MST chapter, unconditionally.** -/
theorem iwSupersetBoundLift_proof : Work.BourgainPlan.Maximal.IWSupersetBoundLift :=
  iwSupersetBoundLift_of_iwSupersetBound iwSupersetBound_proof

end Work.BourgainPlan.Maximal
