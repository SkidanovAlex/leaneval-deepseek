import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the leaf weights of the `IP4`-unfolding on the open quadrant

`Work.FTS.TransportS.IsLeafW α a ρ` says that `ρ` is one of the three *leaf weights*

* `leafEta     = w(z)² · sin(2θ)^{-η}`,
* `leafOne     = w(z)²`,
* `leafGam α   = w(z)² · sin(2θ)^{-γ(α)}` (only for slots with `a ≥ 1`),

with `w z = (1+z)²/z²`.  On the **open** quadrant `Q0 = (0,∞) × (0,π/2)` every one of them is
continuous: `w` is continuous off `z = 0` (its pole) and `sin(2θ) > 0` on the open quadrant, so
`Real.rpow` is continuous in the base there.

This is the regularity hypothesis the transfer estimates of `JepsTransfer` consume (e.g. the
convolution identities relating `logPair` to the pairings `slotPairing`).
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3

/-- The radial factor `z ↦ w z = (1+z)²/z²` of the leaf weights is continuous on the open
quadrant (the pole at `z = 0` is outside `Q0`). -/
private theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- The angular factor `θ ↦ sin(2θ)^q` is continuous on the open quadrant for every real
exponent `q` (the base is positive there, so no junk value of `Real.rpow` occurs). -/
private theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => ?_)
  exact Or.inl (ne_of_gt (hsinpos p hp))

/-- **Every leaf weight of the `IP4`-unfolding is continuous on the open quadrant.** -/
theorem continuousOn_leafW {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a w) :
    ContinuousOn (Function.uncurry w) Work.FTS.EllipticEst.Q0 := by
  rcases h with rfl | rfl | ⟨_, rfl⟩
  · have he : Function.uncurry Work.FTS.TransportS.leafEta = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := rfl
    rw [he]
    exact (continuousOn_w_Q0.pow 2).mul (continuousOn_sinpow_Q0 (-(Work.Spaces.eta)))
  · have he : Function.uncurry Work.FTS.TransportS.leafOne = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 := rfl
    rw [he]
    exact continuousOn_w_Q0.pow 2
  · have he : Function.uncurry (Work.FTS.TransportS.leafGam α) = fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := rfl
    rw [he]
    exact (continuousOn_w_Q0.pow 2).mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α)))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3
