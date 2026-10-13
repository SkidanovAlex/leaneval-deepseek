import Mathlib
import Submission.Work.WilE7.CoreStep.realAnalyticIsolatedZero_fin
import Submission.Work.WilE7.CoreStep.isolatedZero_transfer

namespace Work.WilE7.CoreStep

open Filter Topology

theorem finrankOneAnalyticIsolatedZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 1) {k : ℕ}
    {f : E → (Fin k → ℝ)} (hf : AnalyticAt ℝ f 0) :
    (∀ᶠ v in 𝓝 (0 : E), f v = f 0) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : E, ‖v‖ < δ → f v = f 0 → v = 0 := by
  -- A one-dimensional real normed space is continuously linearly isomorphic to `ℝ`.
  let L : E ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_self]; exact hE)
  -- Transport `f` to a function on `ℝ`.
  let g : ℝ → (Fin k → ℝ) := f ∘ (⇑L.symm)
  have hg : AnalyticAt ℝ g (0 : ℝ) := by
    have hLsymm : AnalyticAt ℝ (⇑L.symm) (0 : ℝ) := L.symm.analyticAt 0
    have hf' : AnalyticAt ℝ f (L.symm 0) := by simpa using hf
    exact hf'.comp hLsymm
  -- The one-dimensional dichotomy on `ℝ`.
  have hmain := realAnalyticIsolatedZero_fin hg
  -- Transfer the dichotomy back along `L`.
  have h2 := isolatedZero_transfer L hmain
  have hfun : (g ∘ (⇑L)) = f := by funext v; simp [g, Function.comp_apply]
  rwa [hfun] at h2

end Work.WilE7.CoreStep
