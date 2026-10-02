import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.exists_rayCylLift
import Submission.Work.ELRig.exists_preimage_rayTail
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- **The level parametrisation of a `RayCylLift` attains every level `> 1`.**

From the fields of `RayCylLift` one derives the self-similarity `L.τ (s + 1) = (L.τ s) ^ 1024`:
`L.hΨ₁`, `L.per₁`, `fl.Ψ_shift`, `Work.ELRig.rayPt_F_alpha1` give
`Ψ (L.γ₁ (s+1)) = rayPt α₁ ((L.τ s)^1024)` while `L.hΨ₁` gives
`Ψ (L.γ₁ (s+1)) = rayPt α₁ (L.τ (s+1))`, and `Work.ELRig.rayPt_level_inj` concludes.

For the seed interval: `Work.ELRig.exists_preimage_rayTail d fl h₁ (R := L.R)` yields
`t₁ > 1` such that every `1 < t < t₁` has a preimage `w` of `rayPt α₁ t` under `Ψ` with
`w.re < -L.R`; `L.tailId₁ w` puts `w` on the lift, say `w = L.γ₁ u`, and then
`rayPt α₁ (L.τ u) = Ψ (L.γ₁ u) = rayPt α₁ t` with both levels `> 1`, so
`Work.ELRig.rayPt_level_inj` gives `t = L.τ u ∈ range L.τ`.  Hence `(1, t₁) ⊆ range L.τ`, and
`Work.ELRig.range_eq_Ioi_of_pow1024` (which is stated in the workspace, in
`Submission/Work/ELRig/exists_rayCylLift.lean`) finishes. -/
theorem rayCylLift_range_tau {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁) :
    Set.range L.τ = Set.Ioi 1 := by
  classical
  -- the self-similarity `L.τ (s + 1) = (L.τ s) ^ 1024`
  have hper : ∀ s : ℝ, L.τ (s + 1) = (L.τ s) ^ (1024 : ℕ) := by
    intro s
    refine Work.ELRig.rayPt_level_inj d.hN (θ := Work.EL.alpha1) (L.hτ1 (s + 1))
      (one_lt_pow₀ (L.hτ1 s) (by norm_num)) ?_
    rw [← L.hΨ₁ (s + 1), L.per₁ s, fl.Ψ_shift (L.γ₁ s), L.hΨ₁ s,
      Work.ELRig.rayPt_F_alpha1 d (L.hτ1 s)]
  -- the seed interval of levels
  obtain ⟨t₁, ht₁, hpre₁⟩ := Work.ELRig.exists_preimage_rayTail d fl h₁ (R := L.R)
  have hseed : Set.Ioo 1 t₁ ⊆ Set.range L.τ := by
    rintro t ⟨ht1, htt₁⟩
    obtain ⟨w, hw, hΨw⟩ := hpre₁ t ht1 htt₁
    have hmem : fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
      rw [hΨw]
      exact Work.EL.rayPt_mem_paramRay d.hN ht1
    obtain ⟨u, hu⟩ := L.tailId₁ w hw hmem
    refine ⟨u, ?_⟩
    exact Work.ELRig.rayPt_level_inj d.hN (θ := Work.EL.alpha1) (L.hτ1 u) ht1
      (by rw [← L.hΨ₁ u, hu, hΨw])
  exact Work.ELRig.range_eq_Ioi_of_pow1024 hper L.hτ1 ht₁ hseed

end Work.ELRig
