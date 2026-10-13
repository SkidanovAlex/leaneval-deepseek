import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- A one-sided continuity statement at the origin: if `g` is bounded by `C` on the open
interval `(0,R)`, then `z ↦ z · g(z)²` tends to `0` as `z → 0⁺` along `[0,R]`.

The point is that the factor `z` kills the potential singularity of the weight: the
bound `|g z| ≤ C` gives `|z g(z)²| = z g(z)² ≤ z C² → 0`. -/
theorem continuousWithinAt_zero_mul_sq {g : ℝ → ℝ} {C R : ℝ} (hR : 0 < R)
    (hb : ∀ z ∈ Set.Ioo 0 R, |g z| ≤ C) :
    ContinuousWithinAt (fun z => z * (g z) ^ 2) (Set.Icc 0 R) 0 := by
  have hCnn : 0 ≤ C := by
    have hmem : R / 2 ∈ Set.Ioo (0 : ℝ) R := ⟨by linarith, by linarith⟩
    exact le_trans (abs_nonneg (g (R / 2))) (hb (R / 2) hmem)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min R (ε / (C ^ 2 + 1)), lt_min hR (by positivity), ?_⟩
  intro x hx hxδ
  have hxnn : 0 ≤ x := hx.1
  have hd : dist x 0 < ε / (C ^ 2 + 1) := lt_of_lt_of_le hxδ (min_le_right _ _)
  have hxR : x < R := by
    have h : dist x 0 < R := lt_of_lt_of_le hxδ (min_le_left _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hxnn] at h
  have hkey : |x * (g x) ^ 2| < ε := by
    rcases eq_or_lt_of_le hxnn with hx0 | hxpos
    · rw [← hx0]; simpa using hε
    · have hmem : x ∈ Set.Ioo 0 R := ⟨hxpos, hxR⟩
      have habs : |g x| ≤ C := hb x hmem
      have hsq : (g x) ^ 2 ≤ C ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hCnn]; exact habs
      have h1 : |x * (g x) ^ 2| = x * (g x) ^ 2 :=
        abs_of_nonneg (mul_nonneg (le_of_lt hxpos) (sq_nonneg _))
      rw [h1]
      have hxlt : x * (C ^ 2 + 1) < ε := by
        have h := hd
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hxnn] at h
        rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)] at h
      have h3 : x * C ^ 2 < ε := by nlinarith [hxlt, hxnn, sq_nonneg C]
      have h2 : x * (g x) ^ 2 ≤ x * C ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hxpos)
      linarith
  have h0 : (fun z : ℝ => z * (g z) ^ 2) 0 = 0 := by ring
  simp only [Real.dist_eq, h0, sub_zero]
  exact hkey

/-- The function `z ↦ z · (u z θ · w z)²` is continuous on the closed interval `[0,R]`.
On the open interval `(0,R)` this is immediate from the smoothness of the `θ`-slice of
`u` and of the weight `w`; at the endpoint `z = 0` the hypothesis that `u z θ · w z` is
bounded for `z ∈ (0,R)` makes the one-sided limit equal to `0` (the value at `0`).

This is the continuity input used when the boundary term `z (u w)²` of the `z`-integration
by parts is handled on a compact interval. -/
theorem continuousOn_zw_sq_finite {u : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd u) {R : ℝ} (hR : 0 < R)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hb1 : ∃ C : ℝ, ∀ z ∈ Set.Ioo 0 R, |u z θ * Work.Spaces.w z| ≤ C) :
    ContinuousOn (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (Set.Icc 0 R) := by
  rcases hb1 with ⟨C, hC⟩
  intro z hz
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · rw [← hz0]
    exact continuousWithinAt_zero_mul_sq hR hC
  · have hslice : ContinuousAt (fun z => u z θ) z :=
      (Work.Spaces.hardyZ_contDiffOn_slice u hsm hθ).continuousOn.continuousAt
        (IsOpen.mem_nhds isOpen_Ioi (by simp only [Set.mem_Ioi]; linarith))
    have hw : ContinuousAt Work.Spaces.w z := by
      show ContinuousAt (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) z
      fun_prop (disch := positivity)
    exact (continuousAt_id.mul ((hslice.mul hw).pow 2)).continuousWithinAt

end Work.Coercivity
