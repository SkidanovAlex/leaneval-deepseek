import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELRig.rayCylLift_range_tau
import Submission.Work.ELRig.rayCylLift_far_left_pin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The far-left levels of the cylinder lift, together with the confinement of the fundamental
piece.**  The height `s ↦ (γ₁ s).re - s` of the lift is bounded above by some `M`
(`rayCylLift_height_bdd`), so `(γ₁ s).re < -R` for `s ≤ s★ := -R - M - 1`; and `τ` is strictly
increasing with range `(1,∞)` (`rayCylLift_range_tau`, whose hypothesis `LandsN hN α₁ z₁` is
`nest.P0.lands_a` through `nest.P0_spec`).  Hence with `P₀ := log (τ s★) > 0`, every level
`p ∈ (0, P₀)` has a preimage `s₁ < s★` of `exp p`, and the whole fundamental piece
`[s₁ - 1, s₁]` lies in `Re < -R`. -/
theorem hs1_of_rayCylLift {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl) :
    ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ p ∈ Set.Ioo (0 : ℝ) P₀, ∃ s₁ : ℝ, Lray.τ s₁ = Real.exp p ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -Lray.R := by
  -- the `LandsN` hypothesis of the range statement, read off the `α`-pair of the nest
  have h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ := by
    rw [← nest.P0_spec.2.2, ← nest.P0_spec.1]
    exact nest.P0.lands_a
  -- `τ` is onto `(1,∞)`
  have hrange : Set.range Lray.τ = Set.Ioi 1 :=
    Work.ELRig.rayCylLift_range_tau d fl Lray h₁
  -- the height bound of the lift
  obtain ⟨M, hM⟩ := Work.ELRig.rayCylLift_height_bdd Lray
  -- the far-left threshold of the height bound
  set sstar : ℝ := -Lray.R - M - 1 with hsstar
  have hτsstar : 1 < Lray.τ sstar := Lray.hτ1 sstar
  refine ⟨Real.log (Lray.τ sstar), Real.log_pos hτsstar, ?_⟩
  intro p hp
  have hp1 : 0 < p := hp.1
  have hp2 : p < Real.log (Lray.τ sstar) := hp.2
  -- `exp p` is a level strictly between `1` and `τ s★`
  have hexp1 : 1 < Real.exp p := by
    have := Real.exp_lt_exp.mpr hp1
    rwa [Real.exp_zero] at this
  have hexplt : Real.exp p < Lray.τ sstar := by
    have h := Real.exp_lt_exp.mpr hp2
    rwa [Real.exp_log (lt_trans zero_lt_one hτsstar)] at h
  -- pick the preimage `s₁` of the level `exp p`
  have hmem : Real.exp p ∈ Set.range Lray.τ := by
    rw [hrange]
    exact hexp1
  obtain ⟨s₁, hs₁⟩ := hmem
  refine ⟨s₁, hs₁, ?_⟩
  -- `s₁` lies below the threshold
  have hs₁lt : s₁ < sstar := (Lray.hτmono.lt_iff_lt).mp (by rw [hs₁]; exact hexplt)
  -- hence the whole fundamental piece lies in the far-left half plane
  intro u hu
  have hule : s₁ - 1 + u ≤ sstar := by
    have := hu.1
    have := hu.2
    linarith
  have hheight := hM (s₁ - 1 + u)
  rw [hsstar] at hule
  linarith

end Work.GATE2
