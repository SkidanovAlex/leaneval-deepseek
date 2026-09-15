import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.SpecialFunctions

private lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- For `α ≤ 1` and `x ≥ 0` we have `log (2 + x) - α * x / (2 + x) ≥ log 2 > 0`.
This is the elementary linear lower bound driving the monotonicity. -/
private lemma log_two_le_log_add_two_sub (α : ℝ) (hα : α ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    Real.log 2 ≤ Real.log (2 + x) - α * x / (2 + x) := by
  have hx2 : 0 < 2 + x := by linarith
  have hx2ne : (2 + x) ≠ 0 := ne_of_gt hx2
  have hu : 0 < 2 / (2 + x) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hu
  rw [Real.log_div (by norm_num) hx2ne] at hlog
  have hfrac : x / (2 + x) = 1 - 2 / (2 + x) := by
    have h1 : ((2 : ℝ) + x - 2) / (2 + x) = 1 - 2 / (2 + x) := by
      rw [sub_div, div_self hx2ne]
    have h2 : (2 : ℝ) + x - 2 = x := by ring
    rwa [h2] at h1
  have h1 : Real.log 2 ≤ Real.log (2 + x) - x / (2 + x) := by
    rw [hfrac]; linarith
  have hnn : 0 ≤ x / (2 + x) := div_nonneg hx (le_of_lt hx2)
  have h2 : α * (x / (2 + x)) ≤ x / (2 + x) := by
    simpa using mul_le_mul_of_nonneg_right hα hnn
  have hrewrite : α * x / (2 + x) = α * (x / (2 + x)) := mul_div_assoc α x (2 + x)
  rw [hrewrite]
  linarith

/-- Derivative of `t ↦ t / (log (2 + t))^α` at `x > 0`. -/
private lemma hasDerivAt_div_log_rpow (α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t / (Real.log (2 + t)) ^ α)
      ((1 * (Real.log (2 + x)) ^ α
          - x * ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1)))
        / ((Real.log (2 + x)) ^ α) ^ 2) x := by
  have hx2pos : 0 < 2 + x := by linarith
  have hvpos : 0 < Real.log (2 + x) := Real.log_pos (by linarith : (1:ℝ) < 2 + x)
  have hvne : Real.log (2 + x) ≠ 0 := ne_of_gt hvpos
  have h2xne : (2 + x) ≠ 0 := ne_of_gt hx2pos
  have hlin : HasDerivAt (fun t : ℝ => 2 + t) 1 x := by
    simpa using (hasDerivAt_id x).const_add 2
  have hlog : HasDerivAt (fun t : ℝ => Real.log (2 + t)) (1 / (2 + x)) x := by
    have h := hlin.log h2xne
    simpa using h
  have hrpow : HasDerivAt (fun t : ℝ => (Real.log (2 + t)) ^ α)
      ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1)) x :=
    hlog.rpow_const (Or.inl hvne)
  exact (hasDerivAt_id x).div hrpow (ne_of_gt (Real.rpow_pos_of_pos hvpos α))

/-- The derivative value of the previous lemma is nonnegative when `α ≤ 1`. -/
private lemma div_log_rpow_derivVal_nonneg (α : ℝ) (hα : α ≤ 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ (1 * (Real.log (2 + x)) ^ α
          - x * ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1)))
        / ((Real.log (2 + x)) ^ α) ^ 2 := by
  have hvpos : 0 < Real.log (2 + x) := Real.log_pos (by linarith : (1:ℝ) < 2 + x)
  have hnum : 1 * (Real.log (2 + x)) ^ α
        - x * ((1 / (2 + x)) * α * (Real.log (2 + x)) ^ (α - 1))
      = (Real.log (2 + x)) ^ (α - 1) * (Real.log (2 + x) - α * x / (2 + x)) := by
    have hv1 : (Real.log (2 + x)) ^ (α - 1) * Real.log (2 + x) = (Real.log (2 + x)) ^ α := by
      have hsplit : (Real.log (2 + x)) ^ (α - 1) * (Real.log (2 + x)) ^ (1:ℝ)
          = (Real.log (2 + x)) ^ α := by
        rw [← Real.rpow_add hvpos (α - 1) 1, sub_add_cancel]
      simpa [Real.rpow_one] using hsplit
    rw [one_mul, ← hv1]
    ring
  rw [hnum]
  apply div_nonneg
  · exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hvpos (α - 1)))
      (by have h := log_two_le_log_add_two_sub α hα x (le_of_lt hx); have := log_two_pos'; linarith)
  · exact sq_nonneg _

/-- For `α ≤ 1` the function `t ↦ t / (log (2 + t))^α` is monotone nondecreasing on `[0, ∞)`.
This is the elementary monotonicity behind the comparison between `ℓ₁` and `ℓ₂` damping
functions (Han–Schlag / Cohen). -/
theorem monotoneOn_div_log_rpow (α : ℝ) (hα : α ≤ 1) :
    MonotoneOn (fun t : ℝ => t / (Real.log (2 + t)) ^ α) (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · have key : ∀ x ∈ Set.Ici (0:ℝ), (1:ℝ) < 2 + x := by
      intro x hx
      have hx0 : (0:ℝ) ≤ x := hx
      linarith
    have hlin : ContinuousOn (fun t : ℝ => 2 + t) (Set.Ici 0) :=
      (continuous_const.add continuous_id).continuousOn
    have hlogc : ContinuousOn (fun t : ℝ => Real.log (2 + t)) (Set.Ici 0) :=
      hlin.log (fun x hx => ne_of_gt (by have := key x hx; linarith))
    have hrpowc : ContinuousOn (fun t : ℝ => (Real.log (2 + t)) ^ α) (Set.Ici 0) :=
      hlogc.rpow_const (fun x hx => Or.inl (ne_of_gt (Real.log_pos (key x hx))))
    exact continuous_id.continuousOn.div hrpowc
      (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (key x hx)) α))
  · rw [interior_Ici]
    intro x hx
    exact (hasDerivAt_div_log_rpow α hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    rw [(hasDerivAt_div_log_rpow α hx).deriv]
    exact div_log_rpow_derivVal_nonneg α hα hx

end Commons.Analysis.SpecialFunctions