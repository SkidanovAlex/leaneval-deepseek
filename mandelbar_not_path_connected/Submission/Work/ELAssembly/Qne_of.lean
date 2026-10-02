import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.bAng_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- **The portrait gives the non-degeneracy of the `z₁`-nest.**  If the only rays of angles in
`Ico 0 1` landing at `z₁` are the two root rays `α₁`, `α₂`, then no level-`n` pair of the nest at
`z₁` lands at `z₁`: the pair's first angle is `βₙ'`, which by `Work.ELNest.bAng_range` lies
strictly between `α₂` and `β₀' < 1`, hence is neither `α₁` nor `α₂`. -/
theorem Qne_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) (n : ℕ) : (N.Qp n).y ≠ d.z₁ := by
  intro h
  -- the first ray of the level-`n` pair (angle `βₙ'`) would then land at `z₁`
  have hland : Work.EL.LandsN d.hN (Work.ELNest.bAng' n) d.z₁ := by
    rw [← N.Qpa n, ← h]
    exact (N.Qp n).lands_a
  -- the range of the angle `βₙ'`
  have hrange := Work.ELNest.bAng_range n
  -- `βₙ'` lies in `Ico 0 1`, so the portrait applies to it
  have hmem : Work.ELNest.bAng' n ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have h0 : (0 : ℝ) < Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
      linarith [hrange.2.1]
    · have hb : Work.ELNest.beta0' < 1 := by norm_num [Work.ELNest.beta0']
      linarith [hrange.2.2]
  -- `α₁ < βₙ'`, so `βₙ'` is not a root angle
  have ha1 : Work.EL.alpha1 < Work.ELNest.bAng' n := by
    have h12 : Work.EL.alpha1 < Work.EL.alpha2 := by
      rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
    exact lt_trans h12 hrange.2.1
  rcases (hzero (Work.ELNest.bAng' n) hmem).mp hland with h1 | h2
  · rw [h1] at ha1
    exact absurd ha1 (lt_irrefl _)
  · exact absurd (h2 ▸ hrange.2.1) (lt_irrefl _)

end Work.ELAssembly
