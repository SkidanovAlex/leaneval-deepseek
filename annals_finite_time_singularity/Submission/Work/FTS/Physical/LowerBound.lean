/-
# `Work.FTS.Physical.LowerBound` — the `c/(T-t)` vorticity lower bound

The Beale–Kato–Majda divergence clause of `theorem_1` is driven by the pointwise-in-time lower
bound `‖ω(·,t)‖_{L^∞} ≥ c/(T-t)`, i.e. by the field `lower` of `BlowupAt`.  The paper obtains it
from the profile bound `|F_* + g| ≥ c₀α` at some point of the self-similar domain
(`Work.StabilityFar.Profile.exists_Fstar_add_ge`) and from the clock comparison
`A(τ(t)) ≤ 2(T - t)` (`PhysClock.tail_le_two_mul`): the physical vorticity is `A(τ(t))^{-1}` times
the profile, so a point where `|profile| ≥ c₀α` gives `‖ω(·,t)‖_∞ ≥ c₀α/A(τ(t)) ≥ c₀α/(2(T-t))`.

This module contains the (elementary) bookkeeping that turns those two inputs into the `lower`
field; the *existence* of the point with `|profile| ≥ c₀α` is the content of
`Physical/Profile.lean`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.BiotSavart

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

/-- **The `c/(T-t)` lower bound from the profile bound and the clock.**  If at every physical time
`t < T` the rescaled profile is `≥ c₀α` at some point (`A(τ(t))·‖ω(·,t)‖ ≥ c₀α`), the clock obeys
`A(τ(t)) ≤ 2(T-t)`, and the vorticity sup-norm is honest (`BddAbove`), then
`‖ω(·,t)‖_∞ ≥ (c₀α/2)/(T-t)`. -/
theorem exists_vortLInf_lower_of_profile {ω : R3 → ℝ → R3} {A τ : ℝ → ℝ} {T c₀ α : ℝ}
    (hT : 0 < T) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hid : ∀ t ∈ Set.Ico 0 T, ∀ x : R3, vorticity (fun y => physVel ω y t) x = ω x t)
    (hbdd : ∀ t ∈ Set.Ico 0 T, BddAbove (Set.range (fun x : R3 => ‖ω x t‖)))
    (hclock : ∀ t ∈ Set.Ico 0 T, A (τ t) ≤ 2 * (T - t))
    (hprof : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * α ≤ A (τ t) * ‖ω x t‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf (physVel ω) t := by
  refine ⟨c₀ * α / 2, by positivity, fun t ht => ?_⟩
  obtain ⟨x, hx⟩ := hprof t ht
  have hTt : (0 : ℝ) < T - t := by linarith [ht.2]
  have hApos : 0 < A (τ t) := by
    by_contra h
    push_neg at h
    have hle : A (τ t) * ‖ω x t‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg _)
    have hpos : 0 < c₀ * α := mul_pos hc₀ hα
    linarith
  have h1 : c₀ * α / (2 * (T - t)) ≤ c₀ * α / A (τ t) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc₀.le hα.le)
    simpa [one_div] using one_div_le_one_div_of_le hApos (hclock t ht)
  have h2 : c₀ * α / A (τ t) ≤ ‖ω x t‖ := by
    rw [div_le_iff₀ hApos]
    linarith
  have h3 : ‖ω x t‖ ≤ Work.LWP.vortLInf (physVel ω) t := by
    rw [vortLInf_physVel_eq hid ht]
    exact le_ciSup (hbdd t ht) x
  rw [div_div]
  exact le_trans h1 (le_trans h2 h3)

end Work.FTS.Physical
