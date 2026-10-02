import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.EXL.z1_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The potential bound at the far left of the repelling coordinate.**  Since `Ψ w → z₁` as
`Re w → -∞` (`ParabolicFlower.Ψ_small`) and the potential is continuous at `z₁` with
`pot z₁ = 0` (`pot_of_mem` at `Work.GATE2.EXL.z1_mem_K`), the value `pot (Ψ w)` is as small as we
like in a far-left half plane. -/
theorem hpot_of_flower {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) :
    ∀ g : ℝ, 0 < g → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Work.EL.pot d.hN (fl.Ψ w) < g := by
  intro g hg
  -- the potential vanishes at `z₁`
  have hpot1 : Work.EL.pot d.hN d.z₁ = 0 :=
    Work.EL.pot_of_mem d.hN (Work.GATE2.EXL.z1_mem_K d)
  -- the potential is continuous at `z₁`
  have hcont : ContinuousAt (Work.EL.pot d.hN) d.z₁ :=
    (d.hN.continuous_potential.continuousAt :
      ContinuousAt (Work.Top.potential (Work.EL.K c) (Work.EL.dynPhi c d.φ)) d.z₁)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont g hg
  -- far to the left, `Ψ w` is within `δ` of `z₁`
  obtain ⟨R, hR⟩ := fl.Ψ_small δ hδpos
  refine ⟨R, fun w hw => ?_⟩
  have hdist : dist (fl.Ψ w) d.z₁ < δ := by
    rw [dist_eq_norm]
    exact (hR w hw).2
  have h2 := hδ hdist
  rw [hpot1, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (Work.EL.pot_nonneg d.hN (fl.Ψ w))] at h2
  exact h2

end Work.GATE2
