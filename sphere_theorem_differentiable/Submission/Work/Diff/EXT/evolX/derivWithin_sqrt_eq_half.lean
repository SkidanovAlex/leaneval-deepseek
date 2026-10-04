import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff
open Filter
open Set

namespace Work.Diff.EXT.evolX

/-- For an even function `g` which is smooth at `0`, the function `s ↦ g (√s)` has one-sided
derivative `g''(0)/2` at `0`: this is the classical "extend an even smooth function at the origin
via `s ↦ g(√s)`" computation, used to restart the heat/ODE flow at `τ = 0` in the
`√τ`-parametrised evolution estimates.

Proof idea: `heven` gives `g'(0) = 0` (`deriv_comp_neg`), so the second-order Taylor expansion of
`g` at `0` is `g x = g 0 + (g''(0)/2) x² + o(x²)` (`taylor_isLittleO` applied on an open interval
around `0`). Composing with `√` along `𝓝[>] 0` and using `(√s)² = s` turns this into
`g(√s) = g 0 + (g''(0)/2) s + o(s)`, i.e. exactly the required one-sided derivative. -/
theorem derivWithin_sqrt_eq_half {g : ℝ → ℝ} (hg : ContDiffAt ℝ (⊤ : ℕ∞) g 0)
    (heven : ∀ τ : ℝ, g (-τ) = g τ) :
    derivWithin (fun s : ℝ => g (Real.sqrt s)) (Set.Ioi 0) 0 = deriv (deriv g) 0 / 2 := by
  -- Step 1: evenness forces `deriv g 0 = 0`.
  have hg'0 : deriv g 0 = 0 := by
    have hfun : (fun τ : ℝ => g (-τ)) = g := funext heven
    have h := deriv_comp_neg g 0
    rw [hfun] at h
    have h2 : deriv g 0 = -deriv g 0 := by simpa using h
    linarith
  -- Step 2: an open interval `Ioo (-δ) δ` around `0` on which `g` is `C²`.
  obtain ⟨u, hu_mem, hu⟩ := hg.contDiffOn (m := 2) (by norm_num) (by simp)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hu_mem
  have hs_open : IsOpen (Set.Ioo (-δ) δ) := isOpen_Ioo
  have h0s : (0:ℝ) ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hgs : ContDiffOn ℝ 2 g (Set.Ioo (-δ) δ) :=
    hu.mono (fun y hy => hδball (by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact abs_lt.mpr ⟨hy.1, hy.2⟩))
  -- Step 3: the Taylor polynomial of `g` at `0` of order `2` on that interval.
  have hderivWithin0 : derivWithin g (Set.Ioo (-δ) δ) 0 = 0 := by
    rw [derivWithin_of_isOpen hs_open h0s, hg'0]
  have hID : iteratedDerivWithin 2 g (Set.Ioo (-δ) δ) 0 = deriv (deriv g) 0 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    rw [derivWithin_of_isOpen hs_open h0s]
    exact EventuallyEq.deriv_eq
      (eventuallyEq_of_mem (hs_open.mem_nhds h0s)
        (fun y hy => derivWithin_of_isOpen hs_open hy))
  have htaylor : ∀ x : ℝ, taylorWithinEval g 2 (Set.Ioo (-δ) δ) 0 x
      = g 0 + (deriv (deriv g) 0 / 2) * x^2 := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial, Nat.cast_one,
      inv_one, iteratedDerivWithin_zero, iteratedDerivWithin_one]
    rw [hderivWithin0, hID]
    ring
  -- Step 4: Taylor's theorem in little-o form, and composition with `√`.
  have hT := taylor_isLittleO (convex_Ioo (-δ) δ) h0s hgs
  have hsqrt : Tendsto Real.sqrt (𝓝[Set.Ioi (0:ℝ)] 0) (𝓝[Set.Ioo (-δ) δ] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto Real.sqrt (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
        simpa [Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto
      exact h.mono_left nhdsWithin_le_nhds
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds (show (0:ℝ) < δ^2 by positivity)] with t ht htin
      rw [mem_Ioo]
      exact ⟨by linarith [Real.sqrt_nonneg t], Real.sqrt_lt' hδpos |>.mpr ht⟩
  have h1 := hT.comp_tendsto hsqrt
  have h2 : (fun t : ℝ => g (Real.sqrt t) - g 0 - (deriv (deriv g) 0 / 2) * t)
      =o[𝓝[Set.Ioi (0:ℝ)] 0] (fun t : ℝ => t) := by
    refine h1.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_apply]
      rw [htaylor (Real.sqrt t), Real.sq_sqrt (le_of_lt ht)]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_apply, sub_zero]
      rw [Real.sq_sqrt (le_of_lt ht)]
  -- Step 5: read off the one-sided derivative.
  have hfd : HasFDerivWithinAt (fun s : ℝ => g (Real.sqrt s))
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (deriv g) 0 / 2)) (Set.Ioi 0) 0 := by
    rw [hasFDerivWithinAt_iff_isLittleO]
    refine h2.congr (fun t => ?_) (fun t => ?_)
    · simp only [Real.sqrt_zero, sub_zero, ContinuousLinearMap.toSpanSingleton_apply]
      ring
    · simp
  have hd : HasDerivWithinAt (fun s : ℝ => g (Real.sqrt s)) (deriv (deriv g) 0 / 2)
      (Set.Ioi 0) 0 :=
    (hasDerivWithinAt_iff_hasFDerivWithinAt).mpr hfd
  exact hd.derivWithin (uniqueDiffWithinAt_Ioi 0)

end Work.Diff.EXT.evolX
