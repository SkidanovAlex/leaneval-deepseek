import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.lam_sq_timeDeriv_le_Ioo
import Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le
import Submission.Work.ConstructionInstance.bddDt_selfSimVort
import Submission.Work.ConstructionInstance.hasDerivAt_selfSimVort_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

/-- `window S = [-1, S+1]` is contained in `preWindow T = (-2, T)` as soon as `S + 1 < T`.

All the `λ̄`-data of the construction (`hlam`, `hlamdif`, `hlamd`) is stated on the half-window
`preWindow T = (-2,T)`, whereas `TimeHolderOnBall` is about the (physical) window
`window S = [-1,S+1]`; this is the containment that reconciles the two. -/
theorem window_subset_preWindow {S T : ℝ} (hST : S + 1 < T) :
    Work.StabilityFar.window S ⊆ preWindow T := by
  intro t ht
  rw [Work.StabilityFar.window] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **A uniform positive lower bound for `λ̄` on the window.**

The hypotheses are exactly the `λ̄`-fields of the construction: `λ̄` is positive on
`preWindow T = (-2,T)` and differentiable (hence continuous) there.  Since
`window S = [-1,S+1]` is compact and contained in `preWindow T` (as `S + 1 < T`), the continuous
function `λ̄` attains its minimum on the window, and that minimum is positive.

This is what converts the *weighted* box `λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` of
`bddDt_selfSimVort` into an unweighted bound on the window. -/
theorem lam_pos_le_on_window {lam : ℝ → ℝ} {T S : ℝ} (hS : 0 < S) (hST : S + 1 < T)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Work.StabilityFar.window S, m ≤ lam t := by
  have hsub := window_subset_preWindow hST
  -- `λ̄` is continuous on the open half-window, hence on the compact window
  have hcont : ContinuousOn lam (preWindow T) :=
    fun t ht => (hlamdif t ht).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn lam (Work.StabilityFar.window S) := hcont.mono hsub
  have hne : (Work.StabilityFar.window S).Nonempty :=
    ⟨-1, by rw [Work.StabilityFar.window]; exact ⟨le_rfl, by linarith⟩⟩
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont'
  exact ⟨lam a, hlam a (hsub ha), fun t ht => hmin ht⟩

/-- **The time-Hölder regularity of the constructed (cut) self-similar vorticity on the ball.**

For every strip `[0,S]` with `S + 1 < T`, the field `selfSimVort p g L lam` is `(p/3)`-Hölder in
time on `B(0,R) × [-1,S+1]`, with a constant independent of the point.

The proof is the mean value theorem route `timeHolderOnBall_of_timeDeriv_le`, fed by

* `hasDerivAt_selfSimVort_slice`: every time slice is differentiable on `preWindow T` (the chain
  rule for `λ̄(t)⁻¹ F(ρ^p/λ̄(t))`, with the axis case `radial y = 0` where the field vanishes);
* `bddDt_selfSimVort`: the weighted box `λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` on `preWindow T`;
* `lam_pos_le_on_window`: the uniform lower bound `m > 0` for `λ̄` on the window, which turns the
  weighted box into `‖∂ₜω‖ ≤ K(20p + Cg + Cg')/m² =: Λ` there.

The Hölder exponent is `p/3` — the exponent of the angular vanishing of the profile
(`Γ = (sinθcos²θ)^{p/3}`) — and the constant is `H = Λ · max (S+2) 1`. -/
theorem timeHolderOnBall_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg Cg' K : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    {L : ℝ} {lam : ℝ → ℝ} {T : ℝ} (hK : 0 ≤ K)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamd : ∀ t ∈ Work.ConstructionInstance.preWindow T, |deriv lam t| ≤ K)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ S : ℝ, 0 < S → S + 1 < T → ∃ H : ℝ, 0 ≤ H ∧
      Work.StabilityFar.TimeHolderOnBall (p / 3)
        (Work.ConstructionInstance.selfSimVort p g L lam) R S H := by
  intro S hS hST
  have hsub := window_subset_preWindow hST
  -- the constants `Cg`, `Cg'` are nonnegative and so is `20p + Cg + Cg'`
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hsum : 0 ≤ 20 * p + Cg + Cg' := by linarith
  -- the uniform lower bound of `λ̄` on the window
  obtain ⟨m, hmpos, hm⟩ := lam_pos_le_on_window hS hST hlam hlamdif
  -- the resulting unweighted bound `Λ` on `∂ₜω`
  set Λ : ℝ := K * (20 * p + Cg + Cg') / m ^ 2 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact div_nonneg (mul_nonneg hK hsum) (by positivity)
  refine timeHolderOnBall_of_timeDeriv_le (α := p / 3) (Λ := Λ) (R := R) (S := S)
    (ω := Work.ConstructionInstance.selfSimVort p g L lam) (by linarith) (by linarith) hΛ ?_ ?_
  · -- differentiability of every time slice on the window
    intro z _hz s hs
    exact hasDerivAt_selfSimVort_slice hgdiff hlam hlamdif (hsub hs) z
  · -- the uniform bound on `∂ₜω` on the ball and the window
    intro z _hz s hs
    have hbox := bddDt_selfSimVort (L := L) hp hp1 hgbdd hg2 hgdiff hK hlam hlamdif hlamd (hsub hs) z
    have hms : m ≤ lam s := hm s hs
    have hms2 : m ^ 2 ≤ (lam s) ^ 2 := by nlinarith [hmpos, hms]
    rw [hΛdef, le_div_iff₀ (by positivity : (0 : ℝ) < m ^ 2)]
    calc ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          * m ^ 2
        = m ^ 2
          * ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          := by ring
      _ ≤ (lam s) ^ 2
          * ‖FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.selfSimVort p g L lam) z s‖
          := mul_le_mul_of_nonneg_right hms2 (norm_nonneg _)
      _ ≤ K * (20 * p + Cg + Cg') := hbox

end Work.ConstructionInstance
