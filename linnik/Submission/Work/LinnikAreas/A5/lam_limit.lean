import Mathlib
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikContract.Defs

open Filter Topology MeasureTheory
open scoped Interval Topology

namespace Work.LinnikAreas.A5

/-! # The `λ → 0⁺` limits of HB (13.2)

Auxiliary lemmas for the two limits in `Work.LinnikAreas.A5.lam_limit`:

* `tendsto_sinh_mul_div` is the elementary slope limit `sinh(aλ)/λ → a` as `λ → 0⁺`, obtained
  from the derivative of `sinh` at `0` (`HasDerivAt.tendsto_slope_zero_right`);
* `abs_sinh_le` is the bound `|sinh v| ≤ |v| e^{|v|}`, used to dominate the family
  `λ ↦ e^{-zt} sinh((K-t)λ)/λ` uniformly near `λ = 0`;
* `F1_div_tendsto` and `F2_norm_tendsto` are the two conjuncts. -/

/-- The elementary slope limit `sinh (a·λ)/λ → a` as `λ → 0⁺`, for every real `a`
(including `a = 0`, where the function is identically zero).  This is the difference quotient of
`λ ↦ sinh (a·λ)` at `λ = 0`, whose derivative there is `cosh 0 · a = a`. -/
lemma tendsto_sinh_mul_div (a : ℝ) :
    Filter.Tendsto (fun lam : ℝ => Real.sinh (a * lam) / lam)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) := by
  have hinner : HasDerivAt (fun lam : ℝ => a * lam) (a * 1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_mul a
  have h : HasDerivAt (fun lam : ℝ => Real.sinh (a * lam)) (Real.cosh (a * 0) * (a * 1)) 0 :=
    (Real.hasDerivAt_sinh (a * 0)).comp 0 hinner
  have h2 := h.tendsto_slope_zero_right
  simpa [Real.cosh_zero, smul_eq_mul, div_eq_inv_mul, mul_zero, Real.sinh_zero, sub_zero,
    one_mul] using h2

/-- The elementary bound `|sinh v| ≤ |v| e^{|v|}`.  It follows from `Real.add_one_le_exp`
applied at `-2|v|` (i.e. `1 - 2|v| ≤ e^{-2|v|}`, so `1 - e^{-2|v|} ≤ 2|v|`) after writing
`sinh v = (e^{|v|} - e^{-|v|})/2`. -/
lemma abs_sinh_le (v : ℝ) : |Real.sinh v| ≤ |v| * Real.exp |v| := by
  have hbase : 1 - Real.exp (-(2 * |v|)) ≤ 2 * |v| := by
    have h := Real.add_one_le_exp (-(2 * |v|))
    linarith
  have hkey : Real.exp |v| - Real.exp (-|v|) ≤ (2 * |v|) * Real.exp |v| := by
    have hmul : Real.exp |v| * (1 - Real.exp (-(2 * |v|))) ≤ Real.exp |v| * (2 * |v|) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos |v|).le
    have heq : Real.exp |v| * (1 - Real.exp (-(2 * |v|))) = Real.exp |v| - Real.exp (-|v|) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      rw [show |v| + -(2 * |v|) = -|v| by ring]
    rw [heq] at hmul
    linarith [hmul]
  rw [Real.abs_sinh, Real.sinh_eq]
  linarith

/-- The first limit of HB (13.2) at `λ = 0`: `F₁(z)/λ → ∫₀ᴷ e^{-zt}(K-t)dt` as `λ → 0⁺`.
Writing `F₁(z)/λ = ∫₀ᴷ e^{-zt}·sinh((K-t)λ)/λ dt` and applying dominated convergence with the
dominating function `t ↦ ‖e^{-zt}‖·K·e^K` (`abs_sinh_le`), the pointwise limit being
`e^{-zt}(K-t)` (`tendsto_sinh_mul_div`).  No hypothesis on `z` is needed. -/
lemma F1_div_tendsto (K : ℝ) (hK : 0 < K) (z : ℂ) :
    Filter.Tendsto (fun lam : ℝ => Work.LinnikAreas.A5.F1 K lam z / lam)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((K - t : ℝ) : ℂ))) := by
  -- Move the division inside the integral.
  have hstep1 : ∀ lam : ℝ, Work.LinnikAreas.A5.F1 K lam z / lam
      = ∫ t in (0 : ℝ)..K,
          Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * lam) / lam : ℝ) : ℂ) := by
    intro lam
    rw [Work.LinnikAreas.A5.F1_eq_integral hK.le z, div_eq_mul_inv, mul_comm]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [Complex.ofReal_div]
    ring
  have hmain : Filter.Tendsto (fun lam : ℝ => ∫ t in (0 : ℝ)..K,
        Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * lam) / lam : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((K - t : ℝ) : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (bound := fun t => ‖Complex.exp (-(z * (t : ℂ)))‖ * (K * Real.exp K)) ?_ ?_ ?_ ?_
    · -- measurability
      filter_upwards with lam
      exact (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * lam) / lam : ℝ) : ℂ)))
        |>.aestronglyMeasurable
    · -- uniform domination for `0 < λ ≤ 1`
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
      filter_upwards with x hx
      have hxK : (0 : ℝ) < x ∧ x ≤ K := by
        rw [Set.uIoc_of_le hK.le] at hx
        exact hx
      have hlampos : 0 < lam := hlam.1
      have hKx : |K - x| ≤ K := by
        rw [abs_of_nonneg (by linarith [hxK.2])]
        linarith [hxK.1]
      have h3 : |K - x| * lam ≤ K := by
        calc |K - x| * lam ≤ K * lam := mul_le_mul_of_nonneg_right hKx hlampos.le
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hlam.2 hK.le
          _ = K := mul_one K
      have hexp : Real.exp (|K - x| * lam) ≤ Real.exp K := Real.exp_le_exp.mpr h3
      have hsin : |Real.sinh ((K - x) * lam)| / lam ≤ K * Real.exp K := by
        have h0 := abs_sinh_le ((K - x) * lam)
        rw [abs_mul, abs_of_pos hlampos] at h0
        have h1 : |Real.sinh ((K - x) * lam)| / lam ≤ |K - x| * Real.exp (|K - x| * lam) := by
          rw [div_le_iff₀ hlampos]
          calc |Real.sinh ((K - x) * lam)| ≤ |K - x| * lam * Real.exp (|K - x| * lam) := h0
            _ = (|K - x| * Real.exp (|K - x| * lam)) * lam := by ring
        calc |Real.sinh ((K - x) * lam)| / lam ≤ |K - x| * Real.exp (|K - x| * lam) := h1
          _ ≤ K * Real.exp (|K - x| * lam) := mul_le_mul_of_nonneg_right hKx (Real.exp_pos _).le
          _ ≤ K * Real.exp K := mul_le_mul_of_nonneg_left hexp hK.le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlampos]
      exact mul_le_mul_of_nonneg_left hsin (norm_nonneg _)
    · -- the dominating function is interval integrable (it is continuous)
      exact (by fun_prop : Continuous
        (fun t : ℝ => ‖Complex.exp (-(z * (t : ℂ)))‖ * (K * Real.exp K))).intervalIntegrable _ _
    · -- pointwise convergence
      filter_upwards with x _
      have h1 := tendsto_sinh_mul_div (K - x)
      have h2 : Filter.Tendsto (fun lam : ℝ => ((Real.sinh ((K - x) * lam) / lam : ℝ) : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((K - x : ℝ)) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp h1
      exact h2.const_mul _
  exact hmain.congr (fun lam => (hstep1 lam).symm)

/-- The second limit of HB (13.2) at `λ = 0`: `‖F₂(λ+z)‖ → ‖F₂(z)‖` as `λ → 0⁺`, for `z ≠ 0`.
This is continuity of `Work.LinnikContract.F2 K` at `z ≠ 0` (the function has a removable
singularity at `0`). -/
lemma F2_norm_tendsto (K : ℝ) (z : ℂ) (hz : z ≠ 0) :
    Filter.Tendsto (fun lam : ℝ => ‖Work.LinnikContract.F2 K ((lam : ℂ) + z)‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖Work.LinnikContract.F2 K z‖) := by
  have hcont : ContinuousAt (fun w : ℂ => Work.LinnikContract.F2 K w) z := by
    unfold Work.LinnikContract.F2
    fun_prop
  have hin : Filter.Tendsto (fun lam : ℝ => ((lam : ℂ) + z))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds z) := by
    have h : Filter.Tendsto (fun lam : ℝ => ((lam : ℂ) + z)) (nhds (0 : ℝ)) (nhds z) := by
      have hc : ContinuousAt (fun lam : ℝ => ((lam : ℂ) + z)) (0 : ℝ) := by fun_prop
      simpa using hc.tendsto
    exact h.mono_left nhdsWithin_le_nhds
  exact (hcont.tendsto.comp hin).norm

/-- The `λ → 0⁺` limits of the two sides of Heath-Brown's (13.2)
(`Work.LinnikAreas.A5.F1_re_ge` in `Submission/Work/LinnikAreas/A5/Basic.lean`), used to pass
(13.2) to the λ = 0 boundary.  (`nhdsWithin (0:ℝ) (Set.Ioi 0)` is `𝓝[>] 0`; a proof file will want
`open scoped Topology` for that notation.)

Hints: `F1 K lam z = ∫₀ᴷ e^{−zt} sinh((K−t)λ) dt` (`Work.LinnikAreas.A5.F1_eq_integral`), so the
first limit says the function `λ ↦ ∫₀ᴷ e^{−zt}·(sinh((K−t)λ)/λ)` tends to `∫₀ᴷ e^{−zt}(K−t) dt` as
`λ → 0⁺` (dominated convergence, or a uniform estimate using `sinh v = v + O(v³)`); alternatively
use the closed form `Commons.NumberTheory.Linnik.tentF1_laplace` and let `λ → 0` in it (that formula
requires `λ ≠ ±z`, true eventually on `𝓝[>] 0` because `z ≠ 0`).  The second limit is just continuity
of `Work.LinnikContract.F2 K` at the point `z ≠ 0`. -/
theorem lam_limit (K : ℝ) (hK : 0 < K) :
    (∀ z : ℂ, z ≠ 0 →
      Filter.Tendsto (fun lam : ℝ => Work.LinnikAreas.A5.F1 K lam z / lam)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((K - t : ℝ) : ℂ)))) ∧
    (∀ z : ℂ, z ≠ 0 →
      Filter.Tendsto (fun lam : ℝ => ‖Work.LinnikContract.F2 K ((lam : ℂ) + z)‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖Work.LinnikContract.F2 K z‖)) :=
  ⟨fun z _ => F1_div_tendsto K hK z, fun z hz => F2_norm_tendsto K z hz⟩

end Work.LinnikAreas.A5
