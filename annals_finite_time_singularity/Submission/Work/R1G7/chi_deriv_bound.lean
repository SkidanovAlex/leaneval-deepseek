import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of the cut-off profile `chi` is bounded and vanishes at `±2`

`Work.Stability.chi` is the `C^∞` bump of the cut-off (`= 1` on `[-1,1]`, `= 0` off `(-2,2)`,
`ContDiffBump 0` with `rIn = 1`, `rOut = 2`).  In this file we prove three facts about
`deriv chi`:

* it is bounded on all of `ℝ` (`∃ K ≥ 0, ∀ x, |deriv chi x| ≤ K`): `chi` is `C^1` with compact
  support, so `deriv chi` is continuous and supported in `[-2,2]`, hence bounded there and `0`
  outside;
* `deriv chi 2 = 0` and `deriv chi (-2) = 0`: `chi` vanishes identically on `(2,3)`, resp. on
  `(-3,-2)`, and `deriv chi` is continuous, so its value at the endpoint `2`, resp. `-2`, is the
  one-sided limit `0`.

The two vanishing statements are instances of two general lemmas about a `C^1` function `f`
vanishing on an open interval `(a,b)`: then `deriv f` vanishes at the endpoints `a` and `b`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.R1G7

/-- **The derivative vanishes where the function does.**  If `f` vanishes identically on the open
interval `(a,b)`, then `deriv f y = 0` at every *interior* point `y ∈ (a,b)`: near such a point
`f` agrees with the constant function `0`. -/
theorem deriv_eq_zero_of_eqOn_Ioo {f : ℝ → ℝ} {a b y : ℝ} (hy : y ∈ Ioo a b)
    (h : ∀ z ∈ Ioo a b, f z = 0) : deriv f y = 0 := by
  -- A full neighbourhood of the interior point `y` stays inside `(a,b)`.
  have hε : 0 < min (y - a) (b - y) := lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)
  have hev : f =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) ?_
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    exact h z ⟨by linarith [hz.1, min_le_left (y - a) (b - y)],
                   by linarith [hz.2, min_le_right (y - a) (b - y)]⟩
  rw [hev.deriv_eq]
  simp

/-- **Vanishing at the left endpoint.**  If `f` vanishes identically on `(a,b)` with `a < b` and
`deriv f` is continuous, then `deriv f a = 0`: on `(a,b)` the derivative vanishes, so the
right-hand limit of `deriv f` at `a` is `0`, and by continuity this is `deriv f a`. -/
theorem deriv_eq_zero_left_endpoint {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : Continuous (deriv f)) (h : ∀ y ∈ Ioo a b, f y = 0) : deriv f a = 0 := by
  have hright : Tendsto (deriv f) (𝓝[>] a) (𝓝 (deriv f a)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (deriv f) =ᶠ[𝓝[>] a] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with y hy
    exact deriv_eq_zero_of_eqOn_Ioo hy h
  exact tendsto_nhds_unique hright (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)

/-- **Vanishing at the right endpoint.**  If `f` vanishes identically on `(a,b)` with `a < b` and
`deriv f` is continuous, then `deriv f b = 0`. -/
theorem deriv_eq_zero_right_endpoint {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : Continuous (deriv f)) (h : ∀ y ∈ Ioo a b, f y = 0) : deriv f b = 0 := by
  have hleft : Tendsto (deriv f) (𝓝[<] b) (𝓝 (deriv f b)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (deriv f) =ᶠ[𝓝[<] b] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsLT hab] with y hy
    exact deriv_eq_zero_of_eqOn_Ioo hy h
  exact tendsto_nhds_unique hleft (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)

/-- The derivative of the cut-off `Work.Stability.chi` vanishes on `(2, x+1)`, resp. on
`(x-1, -2)`, for `|x| > 2` — `chi` is `0` off `(-2,2)`. -/
theorem chi_eq_zero_of_two_lt_abs {z : ℝ} (h : 2 < |z|) : Work.Stability.chi z = 0 := by
  rcases lt_abs.mp h with h2 | h2
  · exact Work.Stability.chi_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
  · exact Work.Stability.chi_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)

/-- **The derivative of the cut-off is bounded, and vanishes at `±2`.** -/
theorem chi_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x : ℝ, |deriv Work.Stability.chi x| ≤ K) ∧
      deriv Work.Stability.chi 2 = 0 ∧ deriv Work.Stability.chi (-2) = 0 := by
  -- `chi` is `C^1`, so `deriv chi` is continuous.
  have hc : Continuous (deriv Work.Stability.chi) :=
    (Work.Stability.chi_contDiff.of_le (by exact_mod_cast le_top)).continuous_deriv le_rfl
  -- A continuous function is bounded on the compact interval `[-2,2]`.
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_, ?_, ?_⟩
  · intro x
    rcases le_or_gt |x| 2 with hx | hx
    · -- Inside `[-2,2]` use the compactness bound.
      have hmem : x ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc, abs_le] at *; exact hx
      have h1 := hC x hmem
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_max_left C 0)
    · -- Outside `[-2,2]` the derivative vanishes (`chi` is identically `0` there).
      have hz : deriv Work.Stability.chi x = 0 := by
        rcases lt_abs.mp hx with h2 | h2
        · exact deriv_eq_zero_of_eqOn_Ioo (a := 2) (b := x + 1) ⟨h2, by linarith⟩
            (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1]))
        · have hx2 : x < -2 := by linarith
          exact deriv_eq_zero_of_eqOn_Ioo (a := x - 1) (b := -2) ⟨by linarith, hx2⟩
            (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2]))
      rw [hz, abs_zero]
      exact le_max_right C 0
  · -- `chi` vanishes on `(2,3)`, so its derivative vanishes at the endpoint `2`.
    exact deriv_eq_zero_left_endpoint (a := 2) (b := 3) (by norm_num) hc
      (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1]))
  · -- `chi` vanishes on `(-3,-2)`, so its derivative vanishes at the endpoint `-2`.
    exact deriv_eq_zero_right_endpoint (a := -3) (b := -2) (by norm_num) hc
      (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2]))

end Work.R1G7
