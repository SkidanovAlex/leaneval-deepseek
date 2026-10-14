import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
-- ===== merged: Submission.Work.FTS.Physical.Clock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal Interval

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-- **The exponential clock** `A(τ) = e^{-τ}`, `μ = 0`: the inhabitation obligation of
`PhysClock`.  Here `1 + μ = 1`, the modulation ODE is `A' = -A`, and the decay bound
`A s ≤ A τ e^{-(s-τ)/2}` is an equality. -/
noncomputable def expClock : PhysClock where
  A := fun τ => Real.exp (-τ)
  mu := fun _ => 0
  hApos := by intro τ _; exact Real.exp_pos _
  hAcont := (Real.continuous_exp.comp continuous_neg).continuousOn
  hAderiv := by
    intro τ _
    have h2 : HasDerivAt (fun x : ℝ => -x) (-1) τ := (hasDerivAt_id τ).neg
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-τ) * (-1)) τ :=
      (Real.hasDerivAt_exp (-τ)).comp τ h2
    have h4 : Real.exp (-τ) * (-1) = -((1 : ℝ) + 0) * Real.exp (-τ) := by ring
    rw [h4] at h3
    exact h3
  hmu_lo := by intro τ _; norm_num
  hmu_hi := by intro τ _; norm_num

noncomputable instance : Inhabited PhysClock := ⟨expClock⟩

/-- `A` is nonnegative in fake time. -/
theorem PhysClock.A_nonneg (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ C.A τ :=
  (C.hApos τ hτ).le

/-- **The decay bound**: `A` decreases at least as fast as `e^{-τ/2}`.  This is the only place
where the modulation bound `1 + μ ≥ 1/2` is used. -/
theorem PhysClock.A_le_exp_mul (C : PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A s ≤ C.A τ * Real.exp (-(s - τ) / 2) :=
  Work.FTS.Physical.Clock.A_le_exp_mul C hτ hτs




/-- **The clock comparison** `T - t(τ) ≤ 2 A(τ)`: the physical time left to blow-up is comparable
to the amplitude. -/
theorem PhysClock.tail_le_two_mul (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.T - C.t τ ≤ 2 * C.A τ :=
  Work.FTS.Physical.Clock.tail_le_two_mul C hτ

/-- **`t' = A`**: the physical time is the integral of the amplitude. -/
theorem PhysClock.hasDerivAt_t (C : PhysClock) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt C.t (C.A τ) τ :=
  Work.FTS.Physical.Clock.hasDerivAt_t C hτ

/-- `t = ∫₀^τ A` is strictly increasing on the fake-time half-line. -/
theorem PhysClock.t_strictMonoOn (C : PhysClock) : StrictMonoOn C.t (Set.Ici 0) :=
  Work.FTS.Physical.Clock.t_strictMonoOn C


/-- The blow-up time is positive. -/
theorem PhysClock.T_pos (C : PhysClock) : 0 < C.T :=
  Work.FTS.Physical.Clock.T_pos C


/-- **Surjectivity of the clock.**  Every physical time `t ∈ [0,T)` is `t(τ)` for some fake time
`τ ≥ 0`; this is the abstract form of the existence of the inverse clock `t ↦ τ(t)`. -/
theorem PhysClock.exists_t_eq (C : PhysClock) {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    ∃ τ : ℝ, 0 ≤ τ ∧ C.t τ = t :=
  Work.FTS.Physical.Clock.exists_t_eq C ht


/-- **The inverse clock.**  There is a function `τ : ℝ → ℝ` with `t(τ(t)) = t`, `τ(t) ≥ 0`,
`T - t ≤ 2 A(τ(t))` for every `t ∈ [0,T)`, differentiable on `(0,T)` with `τ'(t) = 1/A(τ(t))`. -/
theorem PhysClock.exists_inverse_clock (C : PhysClock) :
    ∃ tau : ℝ → ℝ, (∀ t ∈ Set.Ico 0 C.T, C.t (tau t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tau t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt tau ((C.A (tau t))⁻¹) t :=
  Work.FTS.Physical.Clock.exists_inverse_clock C

/-- **The lower half of the clock comparison**: `A τ ≤ 2 (T - t τ)`.  Together with
`tail_le_two_mul` this is `A(τ) ≍ T - t(τ)`; it is the input that converts a lower bound
`‖ω(·,t)‖ ≥ c/A(τ(t))` into the blow-up rate `c'/(T-t)`. -/
theorem PhysClock.A_le_two_mul_tail (C : PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ 2 * (C.T - C.t τ) :=
  Work.FTS.Physical.Clock.A_le_two_mul_tail C hτ

/-- **The extended inverse clock** `Work.FTS.Physical.clockInv`: the inverse clock continued to the
left of `0` by its tangent line, so that it is differentiable at `0` as well. -/
noncomputable abbrev PhysClock.clockInv (C : PhysClock) : ℝ → ℝ := Work.FTS.Physical.clockInv C

end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_laplaceTrace_heatKernel_eq_zero =====
section

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
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- The closed strip `ℝ³ × [0, T/2]` on which the boundary-time analysis is carried out. -/
def bstrip (T : ℝ) : Set (R3 × ℝ) := Set.univ ×ˢ Set.Icc 0 (T / 2)

/-- **The right time derivative of the velocity at the boundary time.**
It is the time block of the within derivative of the uncurried velocity on the strip. -/
def tblock (ω : R3 → ℝ → R3) (T : ℝ) (x : R3) : R3 :=
  fderivWithin ℝ (physVel ω).uncurry (bstrip T) (x, 0) ((0 : R3), 1)

/-- **The right time derivative of the Lamb vector at the boundary time**, obtained from the
product rule: `∂ₜ(u × ω) = (∂ₜu) × ω + u × (∂ₜω)`, all derivatives being the right ones. -/
def dtLamb (ω : R3 → ℝ → R3) (T : ℝ) (y : R3) : R3 :=
  crossVec (tblock ω T y) (ω y 0) + crossVec (physVel ω y 0) (timeDeriv ω y 0)

/-- **The time retraction of the Lamb vector**: it agrees with `lamb` on `[0, T/2]` and extends
it affinely to negative times with slope the right derivative `dtLamb`, so that its two sided
`timeDeriv` at `0` is `dtLamb`. -/
def lambExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then lamb (physVel ω) ω y 0 + t • dtLamb ω T y
    else lamb (physVel ω) ω y t

/-- **The time derivative of the potential, extended to the boundary time**: the Newtonian time
derivative of the retracted Lamb field `lambExt`.  On `[0, T/2]` this is `potTDeriv ω`, and at
`t = 0` it is the limit of the one sided derivatives. -/
def potTDerivExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 → ℝ → ℝ :=
  fun x t => -∫ y, inner ℝ (nablaNfund (x - y)) (timeDeriv (lambExt ω T) y t)

/-- **The space gradient of the potential, extended to the boundary time**: `∂ₜu - u × ω` for
`t > 0`, and its limit `tblock - u × ω` at `t = 0`. -/
def potGradExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 × ℝ → R3 :=
  fun p => if p.2 = 0 then tblock ω T p.1 - crossVec (physVel ω p.1 0) (ω p.1 0)
    else timeDeriv (physVel ω) p.1 p.2 - crossVec (physVel ω p.1 p.2) (ω p.1 p.2)

/-- **The full extended derivative field** of the uncurried potential on the closed strip. -/
def potFDerivExt (ω : R3 → ℝ → R3) (T : ℝ) : R3 × ℝ → (R3 × ℝ →L[ℝ] ℝ) :=
  fun p => (innerSL ℝ (potGradExt ω T p)).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (potTDerivExt ω T p.1 p.2)

end

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

namespace kgiAux

/-! ## General smoothness of partial derivatives -/

theorem contDiff_fderiv_apply_e_of {u : R3 → ℝ} {m : ℕ} (hu : ContDiff ℝ (m + 1) u) (i : Fin 3) :
    ContDiff ℝ m (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) := by
  have h : ContDiff ℝ m (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by simp)
  have h2 : ContDiff ℝ m (fun x : R3 => (x, FiniteTimeSingularity.e i)) := by
    have h3 : ContDiff ℝ m (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), FiniteTimeSingularity.e i)))
  exact h.comp h2

theorem contDiff_fderiv_apply_e_all {u : R3 → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u) (i : Fin 3) :
    ∀ n : ℕ, ContDiff ℝ n (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) :=
  fun n => contDiff_fderiv_apply_e_of (hu (n + 1)) i

/-- `laplaceTrace Ψ` is `C²` when `Ψ` is smooth. -/
theorem contDiff_two_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    ContDiff ℝ 2 (laplaceTrace Ψ) := by
  change ContDiff ℝ 2 (fun x : R3 => ∑ i : Fin 3, fderiv ℝ
    (fun w : R3 => fderiv ℝ Ψ w (FiniteTimeSingularity.e i)) x (FiniteTimeSingularity.e i))
  exact ContDiff.sum fun i _ =>
    contDiff_fderiv_apply_e_of (contDiff_fderiv_apply_e_of (hΨ 4) i) i

/-- The coordinate form of `gradient newtonKernel = newtonGrad`. -/
theorem inner_e_newtonGrad_tmp (z : R3) (i : Fin 3) :
    inner ℝ (FiniteTimeSingularity.e i) (newtonGrad z)
      = fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i) := by
  rw [← gradient_newtonKernel z, real_inner_comm]
  exact inner_gradient_left

/-! ## A smooth approximation of the Newtonian kernel -/

/-- The regularised Newtonian kernel `regN c z = (4π)⁻¹ (‖z‖² + c)^{-1/2}`: for `c > 0` it is a
`C^∞` function on all of `ℝ³` (there is no singularity at the origin), it converges to the
Newtonian kernel `newtonKernel z = (4π‖z‖)⁻¹` as `c → 0⁺`, and its gradient is dominated uniformly
in `c` by `(4π)⁻¹‖z‖⁻²` — which is integrable on balls of `ℝ³`.  This is what makes the limit
`c → 0⁺` of the integration-by-parts identity an instance of dominated convergence. -/
noncomputable abbrev regN (c : ℝ) : R3 → ℝ :=
  fun z => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹

theorem regN_apply (c : ℝ) (z : R3) :
    regN c z = (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ := rfl

theorem contDiff_one_regN (c : ℝ) (hc : 0 < c) : ContDiff ℝ 1 (regN c) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 + c := by positivity
  have h1 : ContDiffAt ℝ 1 (fun w : R3 => ‖w‖ ^ 2 + c) z :=
    ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).add contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ 1 Real.sqrt (‖z‖ ^ 2 + c) :=
    Real.contDiffAt_sqrt (x := ‖z‖ ^ 2 + c) (n := 1) (ne_of_gt hpos)
  have h3 : ContDiffAt ℝ 1 (fun w : R3 => Real.sqrt (‖w‖ ^ 2 + c)) z := h2.comp z h1
  have h4 : ContDiffAt ℝ 1 (fun w : R3 => (Real.sqrt (‖w‖ ^ 2 + c))⁻¹) z :=
    h3.inv (by positivity)
  exact (contDiffAt_const (c := (4 * Real.pi)⁻¹)).mul h4

theorem fderiv_real_apply (f : ℝ → ℝ) (t s : ℝ) :
    (fderiv ℝ f t) s = deriv f t * s := by
  have h : (s : ℝ) • (1 : ℝ) = s := by simp
  calc (fderiv ℝ f t) s = (fderiv ℝ f t) (s • (1 : ℝ)) := by rw [h]
    _ = s • ((fderiv ℝ f t) 1) := map_smul _ _ _
    _ = deriv f t * s := by
        rw [show (fderiv ℝ f t) 1 = deriv f t from rfl, smul_eq_mul]
        ring

theorem fderiv_regN_apply (c : ℝ) (hc : 0 < c) (z : R3) (i : Fin 3) :
    fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)
      = -((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3) * z i := by
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 + c := by positivity
  have hr : DifferentiableAt ℝ (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹)
      (‖z‖ ^ 2 + c) :=
    (((Real.hasDerivAt_sqrt (ne_of_gt hpos)).inv (by positivity)).const_mul
      ((4 * Real.pi)⁻¹)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z : R3 => ‖z‖ ^ 2 + c) z :=
    (((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).add (contDiff_const (c := c))).differentiable
      (by norm_num)).differentiableAt
  have hderiv : deriv (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹) (‖z‖ ^ 2 + c)
      = (4 * Real.pi)⁻¹ * (-(1 / (2 * Real.sqrt (‖z‖ ^ 2 + c)))
          / (Real.sqrt (‖z‖ ^ 2 + c)) ^ 2) := by
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt s)
        (1 / (2 * Real.sqrt (‖z‖ ^ 2 + c))) (‖z‖ ^ 2 + c) :=
      Real.hasDerivAt_sqrt (ne_of_gt hpos)
    have h2 : HasDerivAt (fun s : ℝ => (Real.sqrt s)⁻¹)
        (-(1 / (2 * Real.sqrt (‖z‖ ^ 2 + c))) / (Real.sqrt (‖z‖ ^ 2 + c)) ^ 2)
        (‖z‖ ^ 2 + c) :=
      h1.inv (by positivity)
    have h3 := h2.const_mul ((4 * Real.pi)⁻¹)
    rw [h3.deriv]
  have hinner : (fderiv ℝ (fun z : R3 => ‖z‖ ^ 2 + c) z) (FiniteTimeSingularity.e i)
      = 2 * z i := by
    have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).add_const c
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      Work.FTS.PressureOn.Green.inner_e_eq]
    ring
  rw [show regN c = (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹) ∘
      (fun z : R3 => ‖z‖ ^ 2 + c) from rfl,
    fderiv_comp (x := z) hr hg, ContinuousLinearMap.comp_apply, fderiv_real_apply, hderiv,
    hinner]
  field_simp

theorem norm_fderiv_regN_apply_le (c : ℝ) (hc : 0 < c) (z : R3) (i : Fin 3) :
    ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [fderiv_regN_apply c hc 0 i]
    simp
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hG : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + c) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (‖z‖ ^ 2 + c) := Real.sqrt_le_sqrt (by linarith)
    have hGpos : 0 < Real.sqrt (‖z‖ ^ 2 + c) := lt_of_lt_of_le hzpos hG
    have hinv : ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 ≤ (‖z‖⁻¹) ^ 3 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 3
      exact (inv_le_inv₀ hGpos hzpos).mpr hG
    rw [fderiv_regN_apply c hc z i, Real.norm_eq_abs, abs_mul, abs_neg, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3)]
    have hzi : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    have hstep : ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i| ≤ (‖z‖⁻¹) ^ 3 * ‖z‖ :=
      mul_le_mul hinv hzi (abs_nonneg _) (by positivity)
    calc (4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i|
        = (4 * Real.pi)⁻¹ * (((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i|) := by ring
      _ ≤ (4 * Real.pi)⁻¹ * ((‖z‖⁻¹) ^ 3 * ‖z‖) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
          rw [mul_inv]
          field_simp

theorem tendsto_regN (z : R3) (hz : z ≠ 0) :
    Filter.Tendsto (fun c : ℝ => regN c z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (newtonKernel z)) := by
  have hcont : ContinuousAt (fun c : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹) 0 := by
    refine ContinuousAt.mul continuousAt_const ?_
    refine ContinuousAt.inv₀ ?_ ?_
    · exact Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add continuousAt_id)
    · rw [add_zero, Real.sqrt_sq (norm_nonneg z)]
      exact norm_ne_zero_iff.mpr hz
  have hval : (fun c : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹) 0
      = newtonKernel z := by
    rw [newtonKernel, mul_inv]
    simp only [add_zero, Real.sqrt_sq (norm_nonneg z)]
    ring
  rw [← hval]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_fderiv_regN (z : R3) (hz : z ≠ 0) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i))) := by
  have hcont : ContinuousAt (fun c : ℝ => ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3) 0 := by
    have h1 : ContinuousAt (fun c : ℝ => Real.sqrt (‖z‖ ^ 2 + c)) 0 :=
      Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add continuousAt_id)
    have h2 : (fun c : ℝ => Real.sqrt (‖z‖ ^ 2 + c)) 0 ≠ 0 := by
      show Real.sqrt (‖z‖ ^ 2 + 0) ≠ 0
      rw [add_zero, Real.sqrt_sq (norm_nonneg z)]
      exact norm_ne_zero_iff.mpr hz
    exact (h1.inv₀ h2).pow 3
  have hfun : Filter.Tendsto (fun c : ℝ => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + 0))⁻¹) ^ 3) * z i)) := by
    refine ((continuousAt_const.mul hcont).neg.mul continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (fderiv_regN_apply c hc z i).symm
  have hval : -((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + 0))⁻¹) ^ 3) * z i
      = fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i) := by
    rw [add_zero, Real.sqrt_sq (norm_nonneg z), ← inner_e_newtonGrad_tmp z i, real_inner_comm,
      Work.FTS.PressureOn.Green.inner_e_eq, newtonGrad_apply, inv_pow, mul_inv]
    simp only [smul_eq_mul, WithLp.ofLp_smul, Pi.smul_apply]
  rwa [hval] at hfun

/-! ## The two limits of the regularised identity -/

/-- A uniform bound for `∂ᵢ(laplaceTrace Ψ)` with the ball indicator. -/
theorem exists_bound_fderiv_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : R3,
      ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖
        ≤ C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z := by
  have hcont : Continuous (fun z : R3 => fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) :=
    (contDiff_fderiv_apply_e_of (contDiff_two_laplaceTrace hΨ) i).continuous
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset (hasCompactSupport_fderiv_apply_e
    (hasCompactSupport_laplaceTrace hcs) i)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R3) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, R, le_max_right _ _, fun z => ?_⟩
  by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
  · rw [Set.indicator_of_mem hzc, mul_one]
    exact le_trans (hC z hzc) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hzc, mul_zero]
    have hzts : z ∉ tsupport (fun x : R3 => fderiv ℝ (laplaceTrace Ψ) x
        (FiniteTimeSingularity.e i)) :=
      fun hm => hzc (Metric.ball_subset_closedBall (hR hm))
    have h0 : fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : R3 =>
        fderiv ℝ (laplaceTrace Ψ) x (FiniteTimeSingularity.e i)) hzts
    rw [h0, norm_zero]


theorem tendsto_integral_regN_mul_fderiv_laplaceTrace (Ψ : R3 → ℝ)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ z : R3, newtonKernel z *
        fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))) := by
  obtain ⟨C, R, hC0, hC⟩ := exists_bound_fderiv_laplaceTrace hΨ hcs i
  have hcont : Continuous (fun z : R3 => fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) :=
    (contDiff_fderiv_apply_e_of (contDiff_two_laplaceTrace hΨ) i).continuous
  have hdom : MeasureTheory.Integrable (fun z : R3 =>
      C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z) volume :=
    (((Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball (R + 1)).mono_set
      (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith)).integrable_indicator measurableSet_closedBall).const_mul C
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : R3 => C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z) ?_ ?_
    hdom ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact ((contDiff_one_regN c hc).continuous.mul hcont).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards [ae_ne_zero_volume] with z hz
    have hregnn : 0 ≤ regN c z := by rw [regN_apply]; positivity
    have hnknn : 0 ≤ newtonKernel z := by rw [newtonKernel]; positivity
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h1 : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + c) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (‖z‖ ^ 2 + c) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (le_of_lt hc))
    have h2 : (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ ≤ ‖z‖⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hzpos h1) hzpos).mpr h1
    have hle : regN c z ≤ ‖newtonKernel z‖ := by
      calc regN c z = (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ := rfl
        _ ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ‖newtonKernel z‖ := by
            rw [newtonKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hregnn]
    calc regN c z * ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖
        ≤ ‖newtonKernel z‖ * (C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z) :=
          mul_le_mul hle (hC z) (norm_nonneg _) (norm_nonneg _)
      _ = C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z := by
          by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
          · rw [Set.indicator_of_mem hzc, Set.indicator_of_mem hzc, mul_one]
            rw [Real.norm_eq_abs, abs_of_nonneg hnknn]
            ring
          · rw [Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzc, mul_zero, mul_zero]
  · filter_upwards [ae_ne_zero_volume] with z hz
    exact (tendsto_regN z hz).mul tendsto_const_nhds

theorem tendsto_integral_laplaceTrace_mul_fderiv_regN (Ψ : R3 → ℝ)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        laplaceTrace Ψ z * fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ z : R3, laplaceTrace Ψ z *
        fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i))) := by
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset (hasCompactSupport_laplaceTrace hcs)
  obtain ⟨C, hC⟩ := (hasCompactSupport_laplaceTrace hcs).exists_bound_of_continuous
    (Work.FTS.PressureOn.Green.continuous_laplaceTrace Ψ (hΨ 2))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hdom : MeasureTheory.Integrable (fun z : R3 => C * ((4 * Real.pi)⁻¹ *
      ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)))
      volume := by
    refine (((Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall R).const_mul
      C).const_mul ((4 * Real.pi)⁻¹)).congr ?_
    filter_upwards with z
    ring
  have hΔ : ∀ z : R3, ‖laplaceTrace Ψ z‖
      ≤ C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hzc, mul_one]
      exact hC z
    · rw [Set.indicator_of_notMem hzc, mul_zero]
      have hzts : z ∉ tsupport (laplaceTrace Ψ) :=
        fun hm => hzc (Metric.ball_subset_closedBall (hR hm))
      rw [image_eq_zero_of_notMem_tsupport hzts, norm_zero]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : R3 => C * ((4 * Real.pi)⁻¹ *
      ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z))) ?_ ?_
    hdom ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hker : Continuous (fun z : R3 => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)) :=
      ((contDiff_one_regN c hc).continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
    exact ((Work.FTS.PressureOn.Green.continuous_laplaceTrace Ψ (hΨ 2)).mul hker).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards with z
    rw [norm_mul]
    have hker : ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖
        ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := norm_fderiv_regN_apply_le c hc z i
    calc ‖laplaceTrace Ψ z‖ * ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖
        ≤ (C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)
            * ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) := by
          refine mul_le_mul (hΔ z) hker (norm_nonneg _) ?_
          exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
      _ = C * ((4 * Real.pi)⁻¹ *
            ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)) := by
          ring
  · filter_upwards [ae_ne_zero_volume] with z hz
    exact tendsto_const_nhds.mul (tendsto_fderiv_regN z hz i)

theorem regN_ibp {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ)
    {c : ℝ} (hc : 0 < c) (i : Fin 3) :
    ∫ z, laplaceTrace Ψ z * fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)
      = -∫ z, regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i) := by
  have h := integral_fderiv_mul_eq_neg (g := regN c) (h := laplaceTrace Ψ)
    (contDiff_one_regN c hc) (contDiff_one_laplaceTrace hΨ)
    (hasCompactSupport_laplaceTrace hcs) i
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

/-! ## The centred scalar identity -/

/-- **The centred scalar identity**: `∫ ΔΨ · ∂ᵢN = ∂ᵢΨ(0)`. -/
theorem kernelGrad_coord {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ)
    (i : Fin 3) :
    ∫ z, laplaceTrace Ψ z * fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i)
      = fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i) := by
  have hL := tendsto_integral_laplaceTrace_mul_fderiv_regN Ψ hΨ hcs i
  have hR := tendsto_integral_regN_mul_fderiv_laplaceTrace Ψ hΨ hcs i
  have hRlim : (∫ z : R3, newtonKernel z * fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) = -fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i) := by
    have hone : (∫ z : R3, newtonKernel z * fderiv ℝ (laplaceTrace Ψ) z
          (FiniteTimeSingularity.e i))
        = ∫ z : R3, newtonKernel z * laplaceTrace
            (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z := by
      refine integral_congr_ae ?_
      filter_upwards with z
      rw [show fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)
          = laplaceTrace (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z from
        congrFun (laplaceTrace_fderiv_comm (hΨ 3) i).symm z]
    rw [hone]
    have h := kernelIntegral (contDiff_fderiv_apply_e_all hΨ i)
      (hasCompactSupport_fderiv_apply_e hcs i) 0
    simpa using h
  have hR' : Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-(fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i)))) := by
    rw [hRlim] at hR
    exact hR
  have hneg : Filter.Tendsto (fun c : ℝ => -(∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i))) := by
    simpa using hR'.neg
  have hId : (fun c : ℝ => ∫ z : R3, laplaceTrace Ψ z *
        fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun c : ℝ => -(∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact regN_ibp hΨ hcs hc i
  exact tendsto_nhds_unique hL (hneg.congr' hId.symm)

end kgiAux

end Work.FTS.PressureOn.PoissonAux
end
