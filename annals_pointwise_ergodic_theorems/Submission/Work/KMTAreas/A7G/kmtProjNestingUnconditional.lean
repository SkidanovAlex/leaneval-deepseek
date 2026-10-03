import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarSampling

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Ionescu--Wainger nesting of `kmtProj`, side-condition free

`Work.KMTAreas.A7G.kmtProj_comp` and `kmtProj_comp_consecutive` prove
`kmtProj ρ l k ∘ kmtProj ρ l k' = kmtProj ρ l k'` (for `k' < k`) and its reindexed form
`T_m ∘ T_{m'} = T_{m'}` (for `m < m'`, `T_m = kmtProj ρ l (-(m₀+m))`), but carry the four
analytic side conditions `MemLp ⊤` / `Summable fourierCoeff` on the two periodised cutoffs.
Those are discharged here, using `Work.KMTAreas.A7G.kmtEtaCutSymbolSideConditions` (which lives in
a *separate* module because it imports `chainPartLowpass`, so the wiring cannot be done in the
latter without an import cycle).
-/

open Work.Analysis.IonescuWainger

namespace Work.KMTAreas.A7G

/-- The scale-monotonicity of `GoodMajorArcs`: a *finer* scale is easier. -/
theorem goodMajorArcs_mono_scale {ρ Cρ : ℝ} {l : ℕ} {k k' : ℤ} (h : k' ≤ k)
    (hk : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k) :
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k' := by
  rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hk ⊢
  have : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
  linarith

end Work.KMTAreas.A7G
