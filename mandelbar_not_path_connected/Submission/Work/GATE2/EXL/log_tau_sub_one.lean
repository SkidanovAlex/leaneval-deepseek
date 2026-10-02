import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.GATE2.EXL.exitLoop_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Tantibar)

/-- **Self-similarity of the level map of a `RayCylLift`.**  Shifting the parameter by one period
raises the level to the `1024`-th power: `τ (s + 1) = (τ s) ^ 1024`.

Indeed `L.hΨ₁`, `L.per₁`, `fl.Ψ_shift` and `Work.ELRig.rayPt_F_alpha1` give
`Ψ (L.γ₁ (s+1)) = rayPt α₁ ((L.τ s)^1024)` while `L.hΨ₁` gives `Ψ (L.γ₁ (s+1)) = rayPt α₁ (L.τ (s+1))`,
and `Work.ELRig.rayPt_level_inj` concludes. -/
theorem rayCylLift_tau_succ {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    L.τ (s + 1) = (L.τ s) ^ (1024 : ℕ) := by
  refine Work.ELRig.rayPt_level_inj d.hN (θ := Work.EL.alpha1) (L.hτ1 (s + 1))
    (one_lt_pow₀ (L.hτ1 s) (by norm_num)) ?_
  rw [← L.hΨ₁ (s + 1), L.per₁ s, fl.Ψ_shift (L.γ₁ s), L.hΨ₁ s,
    Work.ELRig.rayPt_F_alpha1 d (L.hτ1 s)]

theorem log_tau_sub_one {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {p s₁ : ℝ} (hτ1 : L.τ s₁ = Real.exp p) :
    Real.log (L.τ (s₁ - 1)) = p / 1024 := by
  have hstep : L.τ ((s₁ - 1) + 1) = (L.τ (s₁ - 1)) ^ (1024 : ℕ) := rayCylLift_tau_succ L (s₁ - 1)
  rw [sub_add_cancel] at hstep
  have hpow : (L.τ (s₁ - 1)) ^ (1024 : ℕ) = Real.exp p := by rw [← hstep, hτ1]
  have hlog : Real.log (L.τ (s₁ - 1)) * 1024 = p := by
    have h := Real.log_pow (L.τ (s₁ - 1)) 1024
    rw [hpow, Real.log_exp] at h
    rw [h]; ring
  rw [eq_div_iff (by norm_num : (1024 : ℝ) ≠ 0)]
  exact hlog

end Work.GATE2.EXL
