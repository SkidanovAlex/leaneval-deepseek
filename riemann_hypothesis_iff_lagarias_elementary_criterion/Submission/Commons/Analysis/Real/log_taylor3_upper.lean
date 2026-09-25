import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Real

/-- The auxiliary function `t ↦ t - t²/2 + t³/3 - log (1 + t)` has derivative
`t³ / (1 + t)` (valid for `t ≠ -1`). -/
lemma hasDerivAt_cubic_sub_log (y : ℝ) (hy : 1 + y ≠ 0) :
    HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t)) (y^3/(1 + y)) y := by
  have hpoly : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3) (1 - y + y^2) y := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h2 : HasDerivAt (fun t : ℝ => t^2/2) y y := by
      have h := (hasDerivAt_pow 2 y).div_const (2 : ℝ)
      have heq : ((2 : ℝ) * y ^ (2 - 1)) / 2 = y := by norm_num
      exact h.congr_deriv heq
    have h3 : HasDerivAt (fun t : ℝ => t^3/3) (y^2) y := by
      have h := (hasDerivAt_pow 3 y).div_const (3 : ℝ)
      have heq : ((3 : ℝ) * y ^ (3 - 1)) / 3 = y^2 := by norm_num
      exact h.congr_deriv heq
    exact (h1.sub h2).add h3
  have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1/(1 + y)) y := by
    have hid : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 y := by
      simpa using (hasDerivAt_id y).const_add 1
    simpa using hid.log hy
  have h := hpoly.sub hlog
  have heq : (1 - y + y^2) - 1/(1 + y) = y^3/(1 + y) := by
    field_simp
    ring
  exact h.congr_deriv heq

/-- The third-order Taylor upper bound for the logarithm at `1`:
for `x > -1`, `log (1 + x) ≤ x - x²/2 + x³/3`. -/
lemma log_one_add_le_cubic {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) ≤ x - x^2/2 + x^3/3 := by
  have hcont_pos : ContinuousOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t))
      (Set.Icc 0 x) := by
    have h1 : ContinuousOn (fun t : ℝ => t - t^2/2 + t^3/3) (Set.Icc 0 x) := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc 0 x) := by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht; have : (0 : ℝ) ≤ t := ht.1; linarith
    exact h1.sub h2
  have hcont_neg : ContinuousOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t))
      (Set.Icc x 0) := by
    have h1 : ContinuousOn (fun t : ℝ => t - t^2/2 + t^3/3) (Set.Icc x 0) := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc x 0) := by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht; have : x ≤ t := ht.1; linarith
    exact h1.sub h2
  have h0 : (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t)) 0 = 0 := by
    norm_num [Real.log_one]
  rcases le_total (0 : ℝ) x with hx0 | hx0
  · -- `0 ≤ x`: the function is monotone on `[0, x]`, so its value at `x` is at least its value at `0`
    have hmono : MonotoneOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t))
        (Set.Icc 0 x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => y^3/(1 + y))
        (convex_Icc 0 x) hcont_pos ?_ ?_
      · intro y hy
        have hys := interior_subset hy
        have hy1 : (0 : ℝ) < 1 + y := by linarith [hys.1]
        exact (hasDerivAt_cubic_sub_log y (ne_of_gt hy1)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc, Set.mem_Ioo] at hy
        have hy0 : 0 ≤ y := hy.1.le
        have hy1 : (0 : ℝ) < 1 + y := by linarith [hy.1]
        exact div_nonneg (pow_nonneg hy0 3) hy1.le
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 x := Set.left_mem_Icc.mpr hx0
    have hmemx : x ∈ Set.Icc 0 x := Set.right_mem_Icc.mpr hx0
    have h := hmono hmem0 hmemx hx0
    rw [h0] at h
    linarith
  · -- `x ≤ 0`: the function is antitone on `[x, 0]`, so again its value at `x` is at least its value at `0`
    have hanti : AntitoneOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1 + t))
        (Set.Icc x 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => y^3/(1 + y))
        (convex_Icc x 0) hcont_neg ?_ ?_
      · intro y hy
        have hys := interior_subset hy
        have hy1 : (0 : ℝ) < 1 + y := by linarith [hys.1]
        exact (hasDerivAt_cubic_sub_log y (ne_of_gt hy1)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc, Set.mem_Ioo] at hy
        have hy0 : y ≤ 0 := hy.2.le
        have hy1 : (0 : ℝ) < 1 + y := by linarith [hy.1]
        exact div_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos (by decide : Odd 3) hy0) hy1.le
    have hmemx : x ∈ Set.Icc x 0 := Set.left_mem_Icc.mpr hx0
    have hmem0 : (0 : ℝ) ∈ Set.Icc x 0 := Set.right_mem_Icc.mpr hx0
    have h := hanti hmemx hmem0 hx0
    rw [h0] at h
    linarith

theorem log_taylor3_upper {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    Real.log A ≤ Real.log a + (A - a)/a - (A - a)^2/(2*a^2) + (A - a)^3/(3*a^3) := by
  have hxA : 1 + (A - a)/a = A/a := by
    field_simp
    ring
  have hpos : 0 < 1 + (A - a)/a := by rw [hxA]; exact div_pos hA ha
  have hx : -1 < (A - a)/a := by linarith
  have key := log_one_add_le_cubic (x := (A - a)/a) hx
  rw [hxA, Real.log_div (ne_of_gt hA) (ne_of_gt ha)] at key
  have hR : (A - a)/a - ((A - a)/a)^2/2 + ((A - a)/a)^3/3
      = (A - a)/a - (A - a)^2/(2*a^2) + (A - a)^3/(3*a^3) := by
    field_simp
  rw [hR] at key
  linarith

end Commons.Analysis.Real