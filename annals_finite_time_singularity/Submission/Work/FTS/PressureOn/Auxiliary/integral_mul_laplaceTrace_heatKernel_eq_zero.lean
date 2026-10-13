/-
# The harmonic pairing `∫ u · Δγ_t(x - ·) = 0`

For a bounded smooth harmonic function `u : ℝ³ → ℝ` (i.e. `laplaceTrace u = 0` everywhere and
`|u| ≤ M`) and the heat kernel `γ_t` we prove

  `∫ y, u y * laplaceTrace (fun y' => heatKernel t (x - y')) y = 0`   (`t > 0`).

This is the key "the heat flow of a harmonic function is time-independent" step in the heat-kernel
proof of Liouville's theorem for bounded harmonic functions.  Together with
`deriv_heatKernel_time` (`∂_t γ_t = Δγ_t`) it says `t ↦ ∫ u γ_t(x - ·)` is constant.

## Route

Let `F := fun y => heatKernel t (x - y)`.  The integral of `u · ΔF` is the limit of the truncated
integrals `∫ χ_R · u · ΔF`, where `χ_R = outerCut R` is the smooth cutoff that is `1` on the ball
of radius `R` and `0` outside the ball of radius `2R`.  For each `R` the weighted Green identity

  `∫ χ u ΔF = -∫ u F Δχ - 2 ∫ u ⟪∇χ, ∇F⟫`

holds.  Both terms on the right involve only `u` (bounded), `F`, `∇F`, `ΔF` (Gaussian decay) and
the *derivatives of the cutoff*, which are uniformly bounded and vanish pointwise as `R → ∞`.
Dominated convergence on the three families (dominated by `M|ΔF|`, `M|F|` and `M‖∇F‖`
respectively) gives the result.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.heatKernelShiftAux
import Submission.Work.FTS.PressureOn.Auxiliary.outerCutBoundsAux
import Submission.Work.FTS.PressureOn.Auxiliary.greenWeightedIntegral
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

theorem integral_mul_laplaceTrace_heatKernel_eq_zero (u : Work.FTS.PressureOn.R3 → ℝ)
    (hu : ∀ n : ℕ, ContDiff ℝ n u) (hlap : ∀ x, Work.FTS.PressureOn.laplaceTrace u x = 0)
    (M : ℝ) (hM : ∀ x, |u x| ≤ M) (x : Work.FTS.PressureOn.R3) (t : ℝ) (ht : 0 < t) :
    ∫ y, u y * Work.FTS.PressureOn.laplaceTrace
        (fun y' : Work.FTS.PressureOn.R3 => Work.FTS.PressureOn.Auxiliary.heatKernel t (x - y')) y
      = 0 := by
  obtain ⟨A, hAnn, hA⟩ := exists_bound_fderiv_outerCut
  obtain ⟨B, hBnn, hB⟩ := exists_bound_laplaceTrace_outerCut
  set F : R3 → ℝ := fun y' : R3 => heatKernel t (x - y') with hFdef
  have hF2 : ContDiff ℝ 2 F := by
    rw [hFdef]; exact contDiff_heatKernel_comp_sub t ht x 2
  have hF1 : ContDiff ℝ 1 F := by
    rw [hFdef]; exact contDiff_heatKernel_comp_sub t ht x 1
  have hFcont : Continuous F := hF2.continuous
  have hgFcont : Continuous (fun y : R3 => gradient F y) :=
    (Green.contDiff_gradient F hF2).continuous
  have hlapFcont : Continuous (fun y : R3 => laplaceTrace F y) :=
    Green.continuous_laplaceTrace F hF2
  have hucont : Continuous u := (hu 0).continuous
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hlapFint : Integrable (fun y : R3 => laplaceTrace F y) := by
    rw [hFdef]; exact integrable_laplaceTrace_heatKernel_shift t ht x
  have hgradFint : Integrable (fun y : R3 => ‖gradient F y‖) := by
    rw [hFdef]; exact integrable_gradient_heatKernel_shift t ht x
  have hFint : Integrable F := by
    rw [hFdef]; exact integrable_heatKernel_shift t ht x
  -- the three dominated-convergence limits
  have hlim1 : Tendsto (fun R : ℝ => ∫ y, Work.FTS.PressureOn.outerCut R y * u y
        * laplaceTrace F y) atTop (𝓝 (∫ y, u y * laplaceTrace F y)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (μ := volume) (bound := fun y : R3 => M * |laplaceTrace F y|)
      (F := fun R : ℝ => fun y : R3 => Work.FTS.PressureOn.outerCut R y * u y
        * laplaceTrace F y)
      (f := fun y : R3 => u y * laplaceTrace F y) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact (((Work.FTS.PressureOn.contDiff_outerCut R
        (lt_of_lt_of_le one_pos hR) 0).continuous.mul hucont).mul
        hlapFcont).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with y
      have hχ : |Work.FTS.PressureOn.outerCut R y| ≤ 1 := by
        rw [abs_of_nonneg (Work.FTS.PressureOn.outerCut_nonneg R y)]
        exact Work.FTS.PressureOn.outerCut_le_one R y
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Work.FTS.PressureOn.outerCut R y| * |u y| * |laplaceTrace F y|
          ≤ 1 * M * |laplaceTrace F y| := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul hχ (hM y) (abs_nonneg _) (by norm_num)) (abs_nonneg _)
        _ = M * |laplaceTrace F y| := by ring
    · exact hlapFint.abs.const_mul M
    · filter_upwards with y
      have hev : (fun R : ℝ => Work.FTS.PressureOn.outerCut R y * u y * laplaceTrace F y)
          =ᶠ[atTop] (fun _ : ℝ => u y * laplaceTrace F y) := by
        filter_upwards [eventually_gt_atTop (‖y‖)] with R hR
        rw [Work.FTS.PressureOn.outerCut_eq_one (lt_of_le_of_lt (norm_nonneg y) hR) hR.le]
        ring
      exact Tendsto.congr' hev.symm tendsto_const_nhds
  have hlim2 : Tendsto (fun R : ℝ => ∫ y, u y * F y
        * laplaceTrace (Work.FTS.PressureOn.outerCut R) y) atTop (𝓝 0) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (μ := volume) (bound := fun y : R3 => M * B * F y)
      (F := fun R : ℝ => fun y : R3 => u y * F y
        * laplaceTrace (Work.FTS.PressureOn.outerCut R) y)
      (f := fun _ : R3 => (0 : ℝ)) ?_ ?_ ?_ ?_
    · simpa using hmain
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact ((hucont.mul hFcont).mul (Green.continuous_laplaceTrace _
        (Work.FTS.PressureOn.contDiff_outerCut R (lt_of_lt_of_le one_pos hR) 2)
        )).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with y
      have hχ : |laplaceTrace (Work.FTS.PressureOn.outerCut R) y| ≤ B := hB R hR y
      have hFnn : 0 ≤ F y := by
        show (0 : ℝ) ≤ heatKernel t (x - y)
        exact heatKernel_nonneg ht.le _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hFnn]
      rw [show M * B * F y = M * F y * B from by ring]
      exact mul_le_mul (mul_le_mul (hM y) le_rfl hFnn hMnn) hχ (abs_nonneg _) (by positivity)
    · exact hFint.const_mul (M * B)
    · filter_upwards with y
      have hev : (fun R : ℝ => u y * F y * laplaceTrace (Work.FTS.PressureOn.outerCut R) y)
          =ᶠ[atTop] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [eventually_gt_atTop (‖y‖)] with R hR
        have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg y) hR
        rw [laplaceTrace_outerCut_eq_zero_of_norm_lt hRpos hR]
        ring
      exact Tendsto.congr' hev.symm tendsto_const_nhds
  have hlim3 : Tendsto (fun R : ℝ => ∫ y, u y
        * inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y))
      atTop (𝓝 0) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := atTop) (μ := volume) (bound := fun y : R3 => M * A * ‖gradient F y‖)
      (F := fun R : ℝ => fun y : R3 => u y
        * inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y))
      (f := fun _ : R3 => (0 : ℝ)) ?_ ?_ ?_ ?_
    · simpa using hmain
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      have hcontχ : Continuous (fun y : R3 => gradient (Work.FTS.PressureOn.outerCut R) y) :=
        (Green.contDiff_gradient _ (Work.FTS.PressureOn.contDiff_outerCut R
          (lt_of_lt_of_le one_pos hR) 2)).continuous
      exact (hucont.mul (continuous_inner.comp (hcontχ.prodMk hgFcont))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with y
      have hχ : ‖gradient (Work.FTS.PressureOn.outerCut R) y‖ ≤ A := by
        rw [norm_gradient_eq_norm_fderiv]
        exact hA R hR y
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y)|
          ≤ A * ‖gradient F y‖ := by
        exact le_trans (abs_real_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_right hχ (norm_nonneg _))
      rw [show M * A * ‖gradient F y‖ = M * (A * ‖gradient F y‖) from by ring]
      exact mul_le_mul (hM y) h1 (abs_nonneg _) hMnn
    · exact hgradFint.const_mul (M * A)
    · filter_upwards with y
      have hev : (fun R : ℝ => u y
            * inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y))
          =ᶠ[atTop] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [eventually_gt_atTop (‖y‖)] with R hR
        have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg y) hR
        have hg : gradient (Work.FTS.PressureOn.outerCut R) y = 0 := by
          rw [gradient, fderiv_outerCut_eq_zero_of_norm_lt hRpos hR, map_zero]
        rw [hg]
        simp
      exact Tendsto.congr' hev.symm tendsto_const_nhds
  -- the identity for each cutoff
  have hgreen : (fun R : ℝ => ∫ y, Work.FTS.PressureOn.outerCut R y * u y * laplaceTrace F y)
      =ᶠ[atTop] (fun R : ℝ =>
        -(∫ y, u y * F y * laplaceTrace (Work.FTS.PressureOn.outerCut R) y)
          - 2 * (∫ y, u y * inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y)
              (gradient F y))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
    have hχ1 : ContDiff ℝ 1 (Work.FTS.PressureOn.outerCut R) :=
      Work.FTS.PressureOn.contDiff_outerCut R hRpos 1
    have hχ2 : ContDiff ℝ 2 (Work.FTS.PressureOn.outerCut R) :=
      Work.FTS.PressureOn.contDiff_outerCut R hRpos 2
    have hχcs : HasCompactSupport (Work.FTS.PressureOn.outerCut R) :=
      Work.FTS.PressureOn.hasCompactSupport_outerCut hRpos
    have hcontχ1 : Continuous (fun y : R3 => gradient (Work.FTS.PressureOn.outerCut R) y) :=
      (Green.contDiff_gradient _ hχ2).continuous
    have hcontχ2 : Continuous (fun y : R3 => laplaceTrace (Work.FTS.PressureOn.outerCut R) y) :=
      Green.continuous_laplaceTrace _ hχ2
    have hint1 : Integrable (fun y : R3 =>
        (Work.FTS.PressureOn.outerCut R y * laplaceTrace F y) * u y) := by
      refine Integrable.mono' (hlapFint.abs.const_mul M) ?_ ?_
      · exact ((hχ1.continuous.mul hlapFcont).mul hucont).aestronglyMeasurable
      · filter_upwards with y
        have hχ : |Work.FTS.PressureOn.outerCut R y| ≤ 1 := by
          rw [abs_of_nonneg (Work.FTS.PressureOn.outerCut_nonneg R y)]
          exact Work.FTS.PressureOn.outerCut_le_one R y
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc (|Work.FTS.PressureOn.outerCut R y| * |laplaceTrace F y|) * |u y|
            ≤ (1 * |laplaceTrace F y|) * M := by
              refine mul_le_mul (mul_le_mul hχ le_rfl (abs_nonneg _) (by norm_num)) (hM y)
                (abs_nonneg _) (by positivity)
          _ = M * |laplaceTrace F y| := by ring
    have hint2 : Integrable (fun y : R3 =>
        inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y) * u y) := by
      refine Integrable.mono' (hgradFint.const_mul (M * A)) ?_ ?_
      · exact ((continuous_inner.comp (hcontχ1.prodMk hgFcont)).mul hucont).aestronglyMeasurable
      · filter_upwards with y
        have hχ : ‖gradient (Work.FTS.PressureOn.outerCut R) y‖ ≤ A := by
          rw [norm_gradient_eq_norm_fderiv]
          exact hA R hR y
        rw [Real.norm_eq_abs, abs_mul]
        calc |inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y) (gradient F y)| * |u y|
            ≤ (A * ‖gradient F y‖) * M := by
              refine mul_le_mul (le_trans (abs_real_inner_le_norm _ _)
                (mul_le_mul_of_nonneg_right hχ (norm_nonneg _))) (hM y) (abs_nonneg _)
                (by positivity)
          _ = M * A * ‖gradient F y‖ := by ring
    have hint3 : Integrable (fun y : R3 =>
        (F y * laplaceTrace (Work.FTS.PressureOn.outerCut R) y) * u y) := by
      refine Integrable.mono' (hFint.const_mul (M * B)) ?_ ?_
      · exact ((hFcont.mul hcontχ2).mul hucont).aestronglyMeasurable
      · filter_upwards with y
        have hχ : |laplaceTrace (Work.FTS.PressureOn.outerCut R) y| ≤ B := hB R hR y
        have hFnn : 0 ≤ F y := by
          show (0 : ℝ) ≤ heatKernel t (x - y)
          exact heatKernel_nonneg ht.le _
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hFnn]
        calc (F y * |laplaceTrace (Work.FTS.PressureOn.outerCut R) y|) * |u y|
            ≤ (F y * B) * M := by
              refine mul_le_mul (mul_le_mul le_rfl hχ (abs_nonneg _) hFnn) (hM y)
                (abs_nonneg _) (by positivity)
          _ = M * B * F y := by ring
    exact integral_green_weighted u (Work.FTS.PressureOn.outerCut R) F (hu 1) (hu 2) hχ1 hχ2
      hχcs hF1 hF2 hlap hint1 hint2 hint3
  have hlim23 : Tendsto (fun R : ℝ =>
        -(∫ y, u y * F y * laplaceTrace (Work.FTS.PressureOn.outerCut R) y)
          - 2 * (∫ y, u y * inner ℝ (gradient (Work.FTS.PressureOn.outerCut R) y)
              (gradient F y))) atTop (𝓝 0) := by
    have h := (hlim2.neg).sub (hlim3.const_mul 2)
    simpa using h
  have hlim1' : Tendsto (fun R : ℝ => ∫ y, Work.FTS.PressureOn.outerCut R y * u y
      * laplaceTrace F y) atTop (𝓝 0) :=
    Tendsto.congr' hgreen.symm hlim23
  exact tendsto_nhds_unique hlim1 hlim1'
end

end Work.FTS.PressureOn.Auxiliary
