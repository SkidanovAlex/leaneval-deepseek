import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.EndpointParamLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false






end Work.EllipticEst.Core.i0Aux.EndpointValues
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. The explicit bump `ψ x = smoothTransition (2 - 4 x)` -/

/-- The explicit bump: `bumpFun x = smoothTransition (2 - 4x)`, which is `1` for `x ≤ 1/4` and
`0` for `x ≥ 1/2`. -/
noncomputable def bumpFun (x : ℝ) : ℝ := Real.smoothTransition (2 - 4 * x)

lemma bumpFun_contDiff : ContDiff ℝ 2 bumpFun := by
  have h1 : ContDiff ℝ 2 Real.smoothTransition := by
    simpa using Real.smoothTransition.contDiff (n := 2)
  have h2 : ContDiff ℝ 2 (fun x : ℝ => 2 - 4 * x) := by fun_prop
  have h3 := h1.comp h2
  first
  | (change ContDiff ℝ 2 fun x : ℝ => Real.smoothTransition (2 - 4 * x); exact h3)
  | simpa only [bumpFun, Function.comp_def] using h3

lemma bumpFun_eq_one {x : ℝ} (hx : x ≤ 1 / 4) : bumpFun x = 1 := by
  rw [bumpFun]
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma bumpFun_eq_zero {x : ℝ} (hx : 1 / 2 ≤ x) : bumpFun x = 0 := by
  rw [bumpFun]
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma bumpFun_nonneg (x : ℝ) : 0 ≤ bumpFun x := by
  rw [bumpFun]; exact Real.smoothTransition.nonneg _

lemma bumpFun_le_one (x : ℝ) : bumpFun x ≤ 1 := by
  rw [bumpFun]; exact Real.smoothTransition.le_one _

lemma bumpFun_deriv_eq_zero_left {x : ℝ} (hx : x < 1 / 4) : deriv bumpFun x = 0 := by
  have h : bumpFun =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact bumpFun_eq_one (le_of_lt hy)
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv_eq_zero_right {x : ℝ} (hx : 1 / 2 < x) : deriv bumpFun x = 0 := by
  have h : bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact bumpFun_eq_zero (le_of_lt hy)
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv2_eq_zero_left {x : ℝ} (hx : x < 1 / 4) : deriv (deriv bumpFun) x = 0 := by
  have h : deriv bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact bumpFun_deriv_eq_zero_left hy
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv2_eq_zero_right {x : ℝ} (hx : 1 / 2 < x) : deriv (deriv bumpFun) x = 0 := by
  have h : deriv bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact bumpFun_deriv_eq_zero_right hy
  rw [h.deriv_eq]; simp

lemma bumpFun_continuous_deriv : Continuous (deriv bumpFun) :=
  bumpFun_contDiff.continuous_deriv (by norm_num)

lemma bumpFun_contDiff_one_deriv : ContDiff ℝ 1 (deriv bumpFun) := by
  first
  | exact bumpFun_contDiff.deriv'
  | (have h : ContDiff ℝ 2 bumpFun := bumpFun_contDiff; fun_prop)
  | exact bumpFun_contDiff.deriv' (n := 1)

lemma bumpFun_continuous_deriv2 : Continuous (deriv (deriv bumpFun)) :=
  bumpFun_contDiff_one_deriv.continuous_deriv_one

lemma bumpFun_deriv_bound : ∃ C : ℝ, ∀ x : ℝ, |deriv bumpFun x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn bumpFun_continuous_deriv.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [bumpFun_deriv_eq_zero_left (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)
    · rw [bumpFun_deriv_eq_zero_right (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)

lemma bumpFun_deriv2_bound : ∃ C : ℝ, ∀ x : ℝ, |deriv (deriv bumpFun) x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn bumpFun_continuous_deriv2.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [bumpFun_deriv2_eq_zero_left (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)
    · rw [bumpFun_deriv2_eq_zero_right (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)

/-- **The existence of a bump.** -/
theorem bumpExists : ∃ (ψ : ℝ → ℝ) (C : ℝ), IsBump ψ C := by
  obtain ⟨C1, hC1⟩ := bumpFun_deriv_bound
  obtain ⟨C2, hC2⟩ := bumpFun_deriv2_bound
  refine ⟨bumpFun, max (max C1 C2) 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact bumpFun_contDiff
  · intro x
    exact (bumpFun_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · intro x
    exact (bumpFun_contDiff.differentiable_deriv_two.differentiableAt).hasDerivAt
  · intro x hx; exact bumpFun_eq_one hx
  · intro x hx; exact bumpFun_eq_zero hx
  · exact bumpFun_nonneg
  · exact bumpFun_le_one
  · intro x
    exact le_trans (hC1 x) (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro x
    exact le_trans (hC2 x) (le_trans (le_max_right _ _) (le_max_left _ _))
  · intro x hx; exact bumpFun_deriv_eq_zero_left hx
  · intro x hx; exact bumpFun_deriv_eq_zero_right hx
  · intro x hx; exact bumpFun_deriv2_eq_zero_left hx
  · intro x hx; exact bumpFun_deriv2_eq_zero_right hx

/-! ## 2. The chain rule for the surrogate -/

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

lemma hasDerivAt_div_const (θ : ℝ) (_hL : L ≠ 0) :
    HasDerivAt (fun θ : ℝ => θ / L) (1 / L) θ := by
  simpa using (hasDerivAt_id θ).div_const L

lemma hasDerivAt_pi_div_two_sub_div (θ : ℝ) (hL : L ≠ 0) :
    HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) / L) (-(1 / L)) θ := by
  have h : HasDerivAt (fun y : ℝ => (Real.pi / 2 - y) / L) ((-1) / L) θ := by
    have h' := ((hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)).div_const L
    convert h' using 1
    all_goals first | (funext y; simp) | ring
  have h2 : (-1 : ℝ) / L = -(1 / L) := by ring
  exact h.congr_deriv h2

lemma hasDerivAt_surr_left (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ψ (θ / L)) (deriv ψ (θ / L) * (1 / L)) θ := by
  have h := (hψ.hasDerivAt (θ / L)).comp θ (hasDerivAt_div_const θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_right (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L))
      (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L))) θ := by
  have h := (hψ.hasDerivAt ((Real.pi / 2 - θ) / L)).comp θ (hasDerivAt_pi_div_two_sub_div θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_deriv (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => deriv ψ (θ / L)) (deriv (deriv ψ) (θ / L) * (1 / L)) θ := by
  have h := (hψ.hasDerivAt_deriv (θ / L)).comp θ (hasDerivAt_div_const θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_deriv_right (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => deriv ψ ((Real.pi / 2 - θ) / L))
      (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) θ := by
  have h := (hψ.hasDerivAt_deriv ((Real.pi / 2 - θ) / L)).comp θ
    (hasDerivAt_pi_div_two_sub_div θ hL)
  simpa only [Function.comp_def] using h

/-- The first derivative of the surrogate, pointwise (raw form). -/
lemma deriv_surr_eq (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    deriv (surrFun ψ F₀ F₁ L) θ
      = F₀ * (deriv ψ (θ / L) * (1 / L))
        + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L))) := by
  have hfun : surrFun ψ F₀ F₁ L
      = (fun y : ℝ => F₀ * ψ (y / L)) + fun y : ℝ => F₁ * ψ ((Real.pi / 2 - y) / L) := by
    funext y; rfl
  rw [hfun]
  exact (((hasDerivAt_surr_left hψ hL θ).const_mul F₀).add
    ((hasDerivAt_surr_right hψ hL θ).const_mul F₁)).deriv

/-- The second derivative of the surrogate, pointwise (raw form). -/
lemma deriv2_surr_eq (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    deriv (deriv (surrFun ψ F₀ F₁ L)) θ
      = F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L)) := by
  have hfun : deriv (surrFun ψ F₀ F₁ L)
      = (fun y : ℝ => F₀ * (deriv ψ (y / L) * (1 / L)))
        + fun y : ℝ => F₁ * (deriv ψ ((Real.pi / 2 - y) / L) * (-(1 / L))) := by
    funext y
    rw [deriv_surr_eq hψ hL y]
    rfl
  rw [hfun]
  have hA : HasDerivAt (fun y : ℝ => F₀ * (deriv ψ (y / L) * (1 / L)))
      (F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)) θ := by
    have h0 : HasDerivAt (fun y : ℝ => F₀ * deriv ψ (y / L))
        (F₀ * (deriv (deriv ψ) (θ / L) * (1 / L))) θ :=
      (hasDerivAt_surr_deriv hψ hL θ).const_mul F₀
    have h1 : HasDerivAt (fun y : ℝ => (F₀ * deriv ψ (y / L)) * (1 / L))
        ((F₀ * (deriv (deriv ψ) (θ / L) * (1 / L))) * (1 / L)) θ :=
      h0.mul_const (1 / L)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  have hB : HasDerivAt (fun y : ℝ => F₁ * (deriv ψ ((Real.pi / 2 - y) / L) * (-(1 / L))))
      (F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))) θ := by
    have h0 : HasDerivAt (fun y : ℝ => F₁ * deriv ψ ((Real.pi / 2 - y) / L))
        (F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L)))) θ :=
      (hasDerivAt_surr_deriv_right hψ hL θ).const_mul F₁
    have h1 : HasDerivAt (fun y : ℝ => (F₁ * deriv ψ ((Real.pi / 2 - y) / L)) * (-(1 / L)))
        ((F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L)))) * (-(1 / L))) θ :=
      h0.mul_const (-(1 / L))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  exact (hA.add hB).deriv

/-! ## 3. Pointwise bounds, support and traces -/

lemma surr_bound (hψ : IsBump ψ C) (θ : ℝ) :
    |surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| := by
  have h1 : |ψ (θ / L)| ≤ 1 := by
    rw [abs_of_nonneg (hψ.nonneg _)]
    exact hψ.le_one _
  have h2 : |ψ ((Real.pi / 2 - θ) / L)| ≤ 1 := by
    rw [abs_of_nonneg (hψ.nonneg _)]
    exact hψ.le_one _
  calc |surrFun ψ F₀ F₁ L θ| = |F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)| := rfl
    _ ≤ |F₀ * ψ (θ / L)| + |F₁ * ψ ((Real.pi / 2 - θ) / L)| := abs_add_le _ _
    _ = |F₀| * |ψ (θ / L)| + |F₁| * |ψ ((Real.pi / 2 - θ) / L)| := by rw [abs_mul, abs_mul]
    _ ≤ |F₀| * 1 + |F₁| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = |F₀| + |F₁| := by ring

lemma deriv_surr_bound (hψ : IsBump ψ C) (hL : 0 < L) (θ : ℝ) :
    |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 := hψ.deriv_bound (θ / L)
  have h2 := hψ.deriv_bound ((Real.pi / 2 - θ) / L)
  have hpos : (0 : ℝ) < 1 / L := by positivity
  have hA : |F₀ * (deriv ψ (θ / L) * (1 / L))| ≤ |F₀| * C / L := by
    rw [abs_mul, abs_mul, abs_of_pos hpos]
    have h4 : |F₀| * |deriv ψ (θ / L)| ≤ |F₀| * C :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg F₀)
    calc |F₀| * (|deriv ψ (θ / L)| * (1 / L)) = (|F₀| * |deriv ψ (θ / L)|) * (1 / L) := by ring
      _ ≤ (|F₀| * C) * (1 / L) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos)
      _ = |F₀| * C / L := by ring
  have hB : |F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))| ≤ |F₁| * C / L := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hpos]
    have h4 : |F₁| * |deriv ψ ((Real.pi / 2 - θ) / L)| ≤ |F₁| * C :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg F₁)
    calc |F₁| * (|deriv ψ ((Real.pi / 2 - θ) / L)| * (1 / L))
        = (|F₁| * |deriv ψ ((Real.pi / 2 - θ) / L)|) * (1 / L) := by ring
      _ ≤ (|F₁| * C) * (1 / L) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos)
      _ = |F₁| * C / L := by ring
  calc |F₀ * (deriv ψ (θ / L) * (1 / L)) + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))|
      ≤ |F₀ * (deriv ψ (θ / L) * (1 / L))| + |F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))| :=
        abs_add_le _ _
    _ ≤ |F₀| * C / L + |F₁| * C / L := add_le_add hA hB
    _ = C * (|F₀| + |F₁|) / L := by ring

lemma deriv2_surr_bound (hψ : IsBump ψ C) (hL : 0 < L) (θ : ℝ) :
    |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ≤ C * (|F₀| + |F₁|) / L ^ 2 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 := hψ.deriv2_bound (θ / L)
  have h2 := hψ.deriv2_bound ((Real.pi / 2 - θ) / L)
  have hpos : (0 : ℝ) < 1 / L := by positivity
  have hpos2 : (0 : ℝ) < 1 / L * (1 / L) := mul_pos hpos hpos
  have hA : |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)| ≤ |F₀| * C / L ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hpos]
    have h4 : |F₀| * |deriv (deriv ψ) (θ / L)| ≤ |F₀| * C :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg F₀)
    calc |F₀| * (|deriv (deriv ψ) (θ / L)| * (1 / L)) * (1 / L)
        = (|F₀| * |deriv (deriv ψ) (θ / L)|) * ((1 / L) * (1 / L)) := by ring
      _ ≤ (|F₀| * C) * ((1 / L) * (1 / L)) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos2)
      _ = |F₀| * C / L ^ 2 := by field_simp [ne_of_gt hL] <;> ring
  have hB : |F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))| ≤ |F₁| * C / L ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hpos]
    have h4 : |F₁| * |deriv (deriv ψ) ((Real.pi / 2 - θ) / L)| ≤ |F₁| * C :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg F₁)
    calc |F₁| * (|deriv (deriv ψ) ((Real.pi / 2 - θ) / L)| * (1 / L)) * (1 / L)
        = (|F₁| * |deriv (deriv ψ) ((Real.pi / 2 - θ) / L)|) * ((1 / L) * (1 / L)) := by ring
      _ ≤ (|F₁| * C) * ((1 / L) * (1 / L)) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos2)
      _ = |F₁| * C / L ^ 2 := by field_simp [ne_of_gt hL] <;> ring
  calc |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))|
      ≤ |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)|
        + |F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))| := abs_add_le _ _
    _ ≤ |F₀| * C / L ^ 2 + |F₁| * C / L ^ 2 := add_le_add hA hB
    _ = C * (|F₀| + |F₁|) / L ^ 2 := by ring

lemma pi_div_two_L_ge_two (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (2 : ℝ) ≤ Real.pi / (2 * L) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)]
  nlinarith [hLp, Real.pi_pos]

lemma sub_div_eq (hL : L ≠ 0) :
    (Real.pi / 2 - L / 4) / L = Real.pi / (2 * L) - 1 / 4 := by
  field_simp <;> ring

lemma deriv_surr_eq_zero_of_lt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [h1, h2]
  ring

lemma deriv_surr_eq_zero_of_gt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  rw [h1, h2]
  ring

lemma deriv2_surr_eq_zero_of_lt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    apply hψ.deriv2_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv2_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [h1, h2]
  ring

lemma deriv2_surr_eq_zero_of_gt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    apply hψ.deriv2_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv2_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  rw [h1, h2]
  ring

lemma surr_eq_on_small (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : surrFun ψ F₀ F₁ L θ = F₀ := by
  have h1 : ψ (θ / L) = 1 := by
    apply hψ.eq_one
    rw [div_le_iff₀ hL]; linarith
  have h2 : ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.eq_zero
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [surrFun, h1, h2]
  ring

lemma surr_eq_on_large (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : surrFun ψ F₀ F₁ L θ = F₁ := by
  have h1 : ψ (θ / L) = 0 := by
    apply hψ.eq_zero
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : ψ ((Real.pi / 2 - θ) / L) = 1 := by
    apply hψ.eq_one
    rw [div_le_iff₀ hL]; linarith
  rw [surrFun, h1, h2]
  ring

lemma surr_smooth (hψ : IsBump ψ C) (hL : L ≠ 0) :
    ContDiff ℝ 2 (surrFun ψ F₀ F₁ L) := by
  have hdiv1 : ContDiff ℝ 2 (fun θ : ℝ => θ / L) := by
    have he : (fun θ : ℝ => θ / L) = fun θ : ℝ => θ * (1 / L) := by funext θ; ring
    rw [he]; fun_prop
  have hdiv2 : ContDiff ℝ 2 (fun θ : ℝ => (Real.pi / 2 - θ) / L) := by
    have he : (fun θ : ℝ => (Real.pi / 2 - θ) / L)
        = fun θ : ℝ => (Real.pi / 2 - θ) * (1 / L) := by funext θ; ring
    rw [he]; fun_prop
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => ψ (θ / L)) := hψ.contDiff.comp hdiv1
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L)) := hψ.contDiff.comp hdiv2
  have h3 : ContDiff ℝ 2 (fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)) :=
    (contDiff_const.mul h1).add (contDiff_const.mul h2)
  have hfun : surrFun ψ F₀ F₁ L
      = fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L) := rfl
  rw [hfun]
  exact h3

lemma surr_tendsto_left (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    Filter.Tendsto (surrFun ψ F₀ F₁ L) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  have hmem : Set.Ioo (0 : ℝ) (L / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Set.Ioo (-1 : ℝ) (L / 4), ?_, ?_⟩
    · exact IsOpen.mem_nhds isOpen_Ioo ⟨by norm_num, by linarith⟩
    · intro x hx; exact ⟨hx.2, hx.1.2⟩
  filter_upwards [hmem] with θ hθ
  first
  | exact surr_eq_on_small hψ hL hLp hθ.2
  | exact (surr_eq_on_small hψ hL hLp hθ.2).symm

lemma surr_tendsto_right (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    Filter.Tendsto (surrFun ψ F₀ F₁ L)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  have hmem : Set.Ioo (Real.pi / 2 - L / 4) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Ioo (Real.pi / 2 - L / 4) (Real.pi / 2 + 1), ?_, ?_⟩
    · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hLp, Real.pi_pos], by linarith [Real.pi_pos]⟩
    · rintro x ⟨hx1, hx2⟩
      exact ⟨hx1.1, hx2⟩
  filter_upwards [hmem] with θ hθ
  first
  | exact surr_eq_on_large hψ hL hLp hθ.1
  | exact (surr_eq_on_large hψ hL hLp hθ.1).symm

end

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 0. The angular weight `thEta` on `(0, t)`, `t < π/2` -/

private theorem lw_thEta_pos {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    0 < Work.FTS.EllipticEst.thEta x :=
  Work.EllipticEst.Core.thEtaFacts.1 x ⟨hx.1, lt_trans hx.2 hta⟩

private theorem lw_inv_thEta {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    (Work.FTS.EllipticEst.thEta x)⁻¹ = (Real.sin (2 * x)) ^ Work.Spaces.eta :=
  Work.EllipticEst.Core.thEtaFacts.2.2.1 x ⟨hx.1, lt_trans hx.2 hta⟩

private theorem lw_one_le_thEta {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta x :=
  Work.EllipticEst.Core.thEtaFacts.2.1 x ⟨hx.1, lt_trans hx.2 hta⟩

private theorem lw_thEta_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.thEta x :=
  (Work.EllipticEst.Core.thEtaFacts.1 x hx).le

/-! ## 1. Continuity of the pieces entering the weighted Cauchy–Schwarz -/

private theorem lw_continuous_etaT (t : ℝ) : Continuous (etaT t) := by
  unfold etaT; fun_prop

private theorem lw_continuous_etaT'' (t : ℝ) : Continuous (etaT'' t) := by
  unfold etaT''; fun_prop

/-- `√thEta` is continuous on `(0, t)` for `t < π/2`. -/
private theorem lw_continuousOn_sqrt_thEta {t : ℝ} (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => Real.sqrt (Work.FTS.EllipticEst.thEta x)) (Set.Ioo 0 t) :=
  ((Work.EllipticEst.Core.thEtaFacts.2.2.2).mono
    (fun _ hx => ⟨hx.1, lt_trans hx.2 hta⟩)).sqrt

/-- `η_t/√thEta` is continuous on `(0, t)`. -/
private theorem lw_continuousOn_etaT_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((lw_continuous_etaT t).continuousOn) (lw_continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (lw_thEta_pos hta hx))

/-- `η_t''/√thEta` is continuous on `(0, t)`. -/
private theorem lw_continuousOn_etaT''_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((lw_continuous_etaT'' t).continuousOn) (lw_continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (lw_thEta_pos hta hx))

/-! ## 2. Pointwise bounds for the test function against the weight -/

/-- `η_t(x)²/thEta x ≤ 2^η t^η x²` on `(0, t)`: the two factors are `η_t(x)² ≤ x²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η = 2^η x^η ≤ 2^η t^η`. -/
private theorem lw_etaT_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹ = (Real.sin (2 * x)) ^ Work.Spaces.eta :=
    lw_inv_thEta hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := lw_thEta_pos hta hx
  have h1 : (etaT t x) ^ 2 ≤ x ^ 2 := by
    have hsq : (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := by
      simp only [etaT]; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu6 : (1 - x / t) ^ 6 ≤ 1 := pow_le_one₀ hu0 hu1
    calc (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := hsq
      _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hu6 (sq_nonneg x)
      _ = x ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹ ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
    rw [hinv]
    calc (Real.sin (2 * x)) ^ Work.Spaces.eta ≤ (2 * x) ^ Work.Spaces.eta :=
          Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
      _ = 2 ^ Work.Spaces.eta * x ^ Work.Spaces.eta := Real.mul_rpow (by norm_num) hx.1.le
      _ ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
          exact Real.rpow_le_rpow hx.1.le hx.2.le Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ x ^ 2 * (2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta) :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (sq_nonneg x)
    _ = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by ring

/-- `η_t''(x)²/thEta x ≤ (36/t²)(2x)^η` on `(0, t)`: `(η_t'')² ≤ 36/t²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η`. -/
private theorem lw_etaT''_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta := by
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹ = (Real.sin (2 * x)) ^ Work.Spaces.eta :=
    lw_inv_thEta hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := lw_thEta_pos hta hx
  have h1 : (etaT'' t x) ^ 2 ≤ 36 / t ^ 2 := by
    have hsq : (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := by
      simp only [etaT'']; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have hxt : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu2 : (1 - x / t) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith, hu1⟩)
    have hv0 : -1 ≤ 2 * (x / t) - 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hv1 : 2 * (x / t) - 1 ≤ 1 := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hv2 : (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨hv0, hv1⟩)
    have hprod : (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      calc (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 * 1 :=
            mul_le_mul hu2 hv2 (sq_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := hsq
      _ ≤ (36 / t ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num) (sq_nonneg t))
      _ = 36 / t ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹ ≤ (2 * x) ^ Work.Spaces.eta := by
    rw [hinv]
    exact Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT'' t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (by positivity)

/-! ## 3. Weighted Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz.**  For `w > 0` on `s`, if `u/√w` and `v·√w` are square
integrable on `s`, then `(∫_s u v)² ≤ (∫_s u²/w)·(∫_s v² w)`. -/
private theorem lw_weighted_cs {u v w : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hw : ∀ x ∈ s, 0 < w x)
    (hu : MemLp (fun x : ℝ => u x / Real.sqrt (w x)) 2 (volume.restrict s))
    (hv : MemLp (fun x : ℝ => v x * Real.sqrt (w x)) 2 (volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2
      ≤ (∫ x in s, (u x) ^ 2 / w x) * (∫ x in s, (v x) ^ 2 * w x) := by
  have hcs := Work.Spaces.cs_integral hu hv
  have e1 : (∫ x in s, (u x / Real.sqrt (w x)) * (v x * Real.sqrt (w x)))
      = ∫ x in s, u x * v x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    have hne : Real.sqrt (w x) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hw x hx))
    field_simp
  have e2 : (∫ x in s, (u x / Real.sqrt (w x)) ^ 2) = ∫ x in s, (u x) ^ 2 / w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [div_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  have e3 : (∫ x in s, (v x * Real.sqrt (w x)) ^ 2) = ∫ x in s, (v x) ^ 2 * w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  rwa [e1, e2, e3] at hcs

/-! ## 4. Integrability of the test function against the weight -/

/-- `η_t²/thEta` is integrable on `(0, t)`. -/
private theorem lw_integrableOn_etaT_sq_div_thEta (t : ℝ) (ht : 0 < t)
    (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((lw_continuous_etaT t).pow 2).continuousOn)
      ((Work.EllipticEst.Core.thEtaFacts.2.2.2).mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (lw_thEta_pos hta hx)
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (lw_thEta_pos hta hx).le)]
  exact lw_etaT_sq_div_thEta_le t x ht hta hx

/-- `η_t''²/thEta` is integrable on `(0, t)`. -/
private theorem lw_integrableOn_etaT''_sq_div_thEta (t : ℝ) (ht : 0 < t)
    (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((lw_continuous_etaT'' t).pow 2).continuousOn)
      ((Work.EllipticEst.Core.thEtaFacts.2.2.2).mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (lw_thEta_pos hta hx)
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (lw_thEta_pos hta hx).le)]
  exact lw_etaT''_sq_div_thEta_le t x ht hta hx

/-! ## 5. The two integral bounds against the weight -/

/-- `∫_0^t η_t²/thEta ≤ t^{3+η}`. -/
private theorem lw_integral_etaT_sq_div_thEta_le (t : ℝ) (ht : 0 < t)
    (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ t ^ (3 + Work.Spaces.eta) := by
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  have hmono : ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 :=
    integral_mono_ae (lw_integrableOn_etaT_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact lw_etaT_sq_div_thEta_le t x ht hta hx)
  have hgval : ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2
      = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3) := by
    rw [MeasureTheory.integral_const_mul,
      EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ 2) ht.le, integral_pow]
    norm_num
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hexp : t ^ (3 + Work.Spaces.eta) = t ^ Work.Spaces.eta * t ^ 3 := by
    rw [show (3 : ℝ) + Work.Spaces.eta = Work.Spaces.eta + 3 by ring,
      Real.rpow_add ht (Work.Spaces.eta) (3 : ℝ)]
    norm_num [Real.rpow_natCast]
  rw [hexp]
  have h3 : (2 : ℝ) ^ Work.Spaces.eta / 3 ≤ 1 := by
    have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
    rw [Real.rpow_one] at h'
    exact le_trans (div_le_div_of_nonneg_right h' (by norm_num)) (by norm_num)
  have hp : 0 ≤ t ^ Work.Spaces.eta * t ^ 3 :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (by positivity)
  calc (2 : ℝ) ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3)
      = ((2 : ℝ) ^ Work.Spaces.eta / 3) * (t ^ Work.Spaces.eta * t ^ 3) := by ring
    _ ≤ 1 * (t ^ Work.Spaces.eta * t ^ 3) := mul_le_mul_of_nonneg_right h3 hp
    _ = t ^ Work.Spaces.eta * t ^ 3 := one_mul _

/-- `∫_0^t η_t''²/thEta ≤ 50 t^{η-1}`. -/
private theorem lw_integral_etaT''_sq_div_thEta_le (t : ℝ) (ht : 0 < t)
    (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := by
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hmono : ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
    integral_mono_ae (lw_integrableOn_etaT''_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact lw_etaT''_sq_div_thEta_le t x ht hta hx)
  have hxpow : ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta
      = t ^ (Work.Spaces.eta + 1) / (Work.Spaces.eta + 1) := by
    rw [EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ Work.Spaces.eta) ht.le,
      integral_rpow (Or.inl (by linarith [Work.Spaces.eta_pos]))]
    rw [Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : Work.Spaces.eta + 1 ≠ 0), sub_zero]
  have hmul : ∫ x in Set.Ioo 0 t, (2 * x) ^ Work.Spaces.eta
      = 2 ^ Work.Spaces.eta * ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo
      (fun x hx => Real.mul_rpow (by norm_num) hx.1.le)
  have hgval : ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta
      = 36 * 2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta) * t ^ (Work.Spaces.eta - 1) := by
    rw [MeasureTheory.integral_const_mul, hmul, hxpow]
    have ht2 : t ^ (Work.Spaces.eta + 1) = t ^ (Work.Spaces.eta - 1) * t ^ 2 := by
      rw [show Work.Spaces.eta + 1 = (Work.Spaces.eta - 1) + 2 by ring,
        Real.rpow_add ht (Work.Spaces.eta - 1) (2 : ℝ)]
      norm_num [Real.rpow_natCast]
    rw [ht2]
    field_simp
    ring
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hcoef : (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) ≤ 50 := by
    have h2 : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
      have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
      rwa [Real.rpow_one] at h'
    have hden : (1 : ℝ) + Work.Spaces.eta = 199 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden]
    calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (199 / 100)
          ≤ (36 : ℝ) * 2 / (199 / 100) := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 50 := by norm_num
  have ht0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta)
        * t ^ (Work.Spaces.eta - 1)
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := mul_le_mul_of_nonneg_right hcoef ht0

/-! ## 6. The weighted endpoint-value estimate at the left endpoint -/

theorem endpointParamLeftW (f : ℝ → ℝ) (F t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta) *
        (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + 100 * t ^ (Work.Spaces.eta - 1) *
        (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
  have hsub : Set.Ioo (0 : ℝ) t ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩
  have h2t := h2.mono_set hsub
  have h1t := h1.mono_set hsub
  -- continuity of the two integrands on `(0, t)`
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    have h1' : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact (h1'.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcont0 : ContinuousOn f (Set.Ioo 0 t) := (hf.continuousOn).mono hsub
  -- the squares are integrable (the weight is `≥ 1`)
  have h2sq : IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h2t ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (deriv (deriv f) x) ^ 2 = (deriv (deriv f) x) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left (lw_one_le_thEta hta hx) (sq_nonneg _)
  have h1sq : IntegrableOn (fun x : ℝ => (f x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h1t ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (f x) ^ 2 = (f x) ^ 2 * 1 := by ring
      _ ≤ (f x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left (lw_one_le_thEta hta hx) (sq_nonneg _)
  -- `L¹` integrability from `L²` integrability
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 t) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hf2L1 : IntegrableOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    refine Integrable.mono' (h2sq.add hconst) (hcont2.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |deriv (deriv f) x| ≤ (deriv (deriv f) x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  have hfL1 : IntegrableOn f (Set.Ioo 0 t) := by
    refine Integrable.mono' (h1sq.add hconst) (hcont0.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |f x| ≤ (f x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  -- `f'` is bounded near `0⁺`
  obtain ⟨M, hM⟩ := EndpointValues.derivBoundedNearLeft ht hta.le hf h2sq
  -- the reproducing formula
  have hid : F = (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, etaT'' t x * f x :=
    EndpointValues.twoIbpEtaT f F t ht hta hf hlim ⟨M, hM⟩ hfL1 hf2L1
  -- positivity of the weight and nonnegativity of the two energies
  have hEtapos : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < Work.FTS.EllipticEst.thEta x :=
    fun x hx => lw_thEta_pos hta hx
  set Jt := ∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x
    with hJt
  set Xt := ∫ x in Set.Ioo 0 t, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hXt
  have hJt0 : 0 ≤ Jt := by
    rw [hJt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  have hXt0 : 0 ≤ Xt := by
    rw [hXt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  -- the four `MemLp` inputs of the weighted Cauchy–Schwarz inequalities
  have hmemA : MemLp (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (lw_continuousOn_etaT_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (lw_integrableOn_etaT_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemA' : MemLp (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (lw_continuousOn_etaT''_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (lw_integrableOn_etaT''_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemB : MemLp
      (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont2.mul (lw_continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h2t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemB' : MemLp (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont0.mul (lw_continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h1t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  -- the two weighted Cauchy–Schwarz inequalities, with the two integral bounds
  have hA2 : (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x) ^ 2
      ≤ t ^ (3 + Work.Spaces.eta) * Jt := by
    refine (lw_weighted_cs measurableSet_Ioo hEtapos hmemA hmemB).trans ?_
    rw [hJt]
    exact mul_le_mul_of_nonneg_right (lw_integral_etaT_sq_div_thEta_le t ht hta) hJt0
  have hB2 : (∫ x in Set.Ioo 0 t, etaT'' t x * f x) ^ 2
      ≤ 50 * t ^ (Work.Spaces.eta - 1) * Xt := by
    refine (lw_weighted_cs measurableSet_Ioo hEtapos hmemA' hmemB').trans ?_
    rw [hXt]
    exact mul_le_mul_of_nonneg_right (lw_integral_etaT''_sq_div_thEta_le t ht hta) hXt0
  -- assembly at the scale `t`
  have hF : F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
      + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := by
    rw [hid]
    nlinarith [hA2, hB2,
      sq_nonneg ((∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
        + (∫ x in Set.Ioo 0 t, etaT'' t x * f x))]
  -- the two integrals over `(0, π/2)` dominate the ones over `(0, t)`
  set J := ∫ x in Set.Ioo 0 (Real.pi / 2),
    (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x with hJ
  set X := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hX
  have hJs : Jt ≤ J := by
    rw [hJt, hJ]
    refine MeasureTheory.setIntegral_mono_set h2 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (lw_thEta_nonneg hx)
  have hXs : Xt ≤ X := by
    rw [hXt, hX]
    refine MeasureTheory.setIntegral_mono_set h1 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (lw_thEta_nonneg hx)
  have htpow0 : 0 ≤ t ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg ht.le _
  have hEtpow0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := hF
    _ ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) := by
        have h1' : 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
            ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJs htpow0) (by norm_num)
        have h2' : 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt)
            ≤ 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hXs (mul_nonneg (by norm_num) hEtpow0)) (by norm_num)
        linarith
    _ = 2 * t ^ (3 + Work.Spaces.eta) * J
        + 100 * t ^ (Work.Spaces.eta - 1) * X := by ring

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary facts about the weight `thEta` -/

/-- The weight `thEta` is invariant under the reflection `x ↦ π/2 - x`. -/
theorem thEta_pi_div_two_sub (x : ℝ) :
    Work.FTS.EllipticEst.thEta (Real.pi / 2 - x) = Work.FTS.EllipticEst.thEta x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- `thEta` is positive on `(0, t)` for `t < π/2`. -/
theorem thEta_pos_of_mem {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    0 < Work.FTS.EllipticEst.thEta x :=
  Work.EllipticEst.Core.thEtaFacts.1 x ⟨hx.1, lt_trans hx.2 hta⟩

/-- On `(0, t)`, `t < π/2`, the inverse of the weight is the power `sin(2x)^η`. -/
theorem inv_thEta_of_mem {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    (Work.FTS.EllipticEst.thEta x)⁻¹ = (Real.sin (2 * x)) ^ Work.Spaces.eta :=
  Work.EllipticEst.Core.thEtaFacts.2.2.1 x ⟨hx.1, lt_trans hx.2 hta⟩

/-- `thEta` is nonnegative on the open angular interval. -/
theorem thEta_nonneg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.thEta x :=
  (Work.EllipticEst.Core.thEtaFacts.1 x hx).le

/-! ## 1. Continuity of the pieces entering the weighted Cauchy–Schwarz -/

theorem continuous_etaT (t : ℝ) : Continuous (etaT t) := by
  unfold etaT; fun_prop

theorem continuous_etaT'' (t : ℝ) : Continuous (etaT'' t) := by
  unfold etaT''; fun_prop

/-- `√thEta` is continuous on `(0, t)`, `t < π/2`. -/
theorem continuousOn_sqrt_thEta {t : ℝ} (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => Real.sqrt (Work.FTS.EllipticEst.thEta x)) (Set.Ioo 0 t) :=
  (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
    (fun _ hx => ⟨hx.1, lt_trans hx.2 hta⟩)).sqrt


/-- `η/√thEta` is continuous on `(0, t)`. -/
theorem continuousOn_etaT_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((continuous_etaT t).continuousOn) (continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (thEta_pos_of_mem hta hx))

/-- `η''/√thEta` is continuous on `(0, t)`. -/
theorem continuousOn_etaT''_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((continuous_etaT'' t).continuousOn) (continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (thEta_pos_of_mem hta hx))

/-! ## 2. Pointwise bounds for the test function against the weight -/

/-- `η_t(x)²/thEta x ≤ 2^η t^η x²` on `(0, t)`.  The two factors are `η_t(x)² ≤ x²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η = 2^η x^η ≤ 2^η t^η`. -/
theorem etaT_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by
  have hxpi : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hta⟩
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹
      = (Real.sin (2 * x)) ^ Work.Spaces.eta := inv_thEta_of_mem hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := thEta_pos_of_mem hta hx
  have h1 : (etaT t x) ^ 2 ≤ x ^ 2 := by
    have hsq : (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := by
      simp only [etaT]; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu6 : (1 - x / t) ^ 6 ≤ 1 := pow_le_one₀ hu0 hu1
    calc (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := hsq
      _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hu6 (sq_nonneg x)
      _ = x ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
    rw [hinv]
    calc (Real.sin (2 * x)) ^ Work.Spaces.eta ≤ (2 * x) ^ Work.Spaces.eta :=
          Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
      _ = 2 ^ Work.Spaces.eta * x ^ Work.Spaces.eta :=
          Real.mul_rpow (by norm_num) hx.1.le
      _ ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
          exact Real.rpow_le_rpow hx.1.le hx.2.le Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ x ^ 2 * (2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta) :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (sq_nonneg x)
    _ = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by ring

/-- `η_t''(x)²/thEta x ≤ (36/t²)(2x)^η` on `(0, t)`: `(η_t'')² ≤ 36/t²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η`. -/
theorem etaT''_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta := by
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹
      = (Real.sin (2 * x)) ^ Work.Spaces.eta := inv_thEta_of_mem hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := thEta_pos_of_mem hta hx
  have h1 : (etaT'' t x) ^ 2 ≤ 36 / t ^ 2 := by
    have hsq : (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := by
      simp only [etaT'']; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have hxt : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu2 : (1 - x / t) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith, hu1⟩)
    have hv0 : -1 ≤ 2 * (x / t) - 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hv1 : 2 * (x / t) - 1 ≤ 1 := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hv2 : (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨hv0, hv1⟩)
    have hprod : (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      calc (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 * 1 :=
            mul_le_mul hu2 hv2 (sq_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := hsq
      _ ≤ (36 / t ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num) (sq_nonneg t))
      _ = 36 / t ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹ ≤ (2 * x) ^ Work.Spaces.eta := by
    rw [hinv]
    exact Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT'' t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (by positivity)

/-! ## 3. Weighted Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz.**  For `w > 0` on `s`, if `u/√w` and `v·√w` are square
integrable on `s`, then `(∫_s u v)² ≤ (∫_s u²/w)·(∫_s v² w)`. -/
theorem weighted_cs_integral {u v w : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hw : ∀ x ∈ s, 0 < w x)
    (hu : MemLp (fun x : ℝ => u x / Real.sqrt (w x)) 2 (volume.restrict s))
    (hv : MemLp (fun x : ℝ => v x * Real.sqrt (w x)) 2 (volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2
      ≤ (∫ x in s, (u x) ^ 2 / w x) * (∫ x in s, (v x) ^ 2 * w x) := by
  have hcs := Work.Spaces.cs_integral hu hv
  have e1 : (∫ x in s, (u x / Real.sqrt (w x)) * (v x * Real.sqrt (w x)))
      = ∫ x in s, u x * v x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    have hne : Real.sqrt (w x) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hw x hx))
    field_simp
  have e2 : (∫ x in s, (u x / Real.sqrt (w x)) ^ 2) = ∫ x in s, (u x) ^ 2 / w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [div_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  have e3 : (∫ x in s, (v x * Real.sqrt (w x)) ^ 2) = ∫ x in s, (v x) ^ 2 * w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  rwa [e1, e2, e3] at hcs

/-! ## 4. Integrability of the test function against the weight -/

/-- `η_t²/thEta` is integrable on `(0, t)`. -/
theorem integrableOn_etaT_sq_div_thEta (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((continuous_etaT t).pow 2).continuousOn)
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (thEta_pos_of_mem hta hx)
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (thEta_pos_of_mem hta hx).le)]
  exact etaT_sq_div_thEta_le t x ht hta hx

/-- `η_t''²/thEta` is integrable on `(0, t)`. -/
theorem integrableOn_etaT''_sq_div_thEta (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((continuous_etaT'' t).pow 2).continuousOn)
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (thEta_pos_of_mem hta hx)
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (thEta_pos_of_mem hta hx).le)]
  exact etaT''_sq_div_thEta_le t x ht hta hx

/-! ## 5. The two integral bounds against the weight -/

/-- `∫_0^t η_t²/thEta ≤ t^{3+η}`. -/
theorem integral_etaT_sq_div_thEta_le (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ t ^ (3 + Work.Spaces.eta) := by
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  have hmono : ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 :=
    integral_mono_ae (integrableOn_etaT_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact etaT_sq_div_thEta_le t x ht hta hx)
  have hgval : ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2
      = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3) := by
    rw [MeasureTheory.integral_const_mul,
      EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ 2) ht.le, integral_pow]
    norm_num
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hexp : t ^ (3 + Work.Spaces.eta) = t ^ Work.Spaces.eta * t ^ 3 := by
    rw [show (3 : ℝ) + Work.Spaces.eta = Work.Spaces.eta + 3 by ring,
      Real.rpow_add ht (Work.Spaces.eta) (3 : ℝ)]
    norm_num [Real.rpow_natCast]
  rw [hexp]
  have h3 : (2 : ℝ) ^ Work.Spaces.eta / 3 ≤ 1 := by
    have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
    rw [Real.rpow_one] at h'
    exact le_trans (div_le_div_of_nonneg_right h' (by norm_num)) (by norm_num)
  have hp : 0 ≤ t ^ Work.Spaces.eta * t ^ 3 :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (by positivity)
  calc (2 : ℝ) ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3)
      = ((2 : ℝ) ^ Work.Spaces.eta / 3) * (t ^ Work.Spaces.eta * t ^ 3) := by ring
    _ ≤ 1 * (t ^ Work.Spaces.eta * t ^ 3) := mul_le_mul_of_nonneg_right h3 hp
    _ = t ^ Work.Spaces.eta * t ^ 3 := one_mul _

/-- `∫_0^t η_t''²/thEta ≤ 50 t^{η-1}`. -/
theorem integral_etaT''_sq_div_thEta_le (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := by
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hmono : ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
    integral_mono_ae (integrableOn_etaT''_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact etaT''_sq_div_thEta_le t x ht hta hx)
  have hxpow : ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta
      = t ^ (Work.Spaces.eta + 1) / (Work.Spaces.eta + 1) := by
    rw [EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ Work.Spaces.eta) ht.le,
      integral_rpow (Or.inl (by linarith [Work.Spaces.eta_pos]))]
    rw [Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : Work.Spaces.eta + 1 ≠ 0), sub_zero]
  have hmul : ∫ x in Set.Ioo 0 t, (2 * x) ^ Work.Spaces.eta
      = 2 ^ Work.Spaces.eta * ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo
      (fun x hx => Real.mul_rpow (by norm_num) hx.1.le)
  have hgval : ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta
      = 36 * 2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta) * t ^ (Work.Spaces.eta - 1) := by
    rw [MeasureTheory.integral_const_mul, hmul, hxpow]
    have ht2 : t ^ (Work.Spaces.eta + 1) = t ^ (Work.Spaces.eta - 1) * t ^ 2 := by
      rw [show Work.Spaces.eta + 1 = (Work.Spaces.eta - 1) + 2 by ring,
        Real.rpow_add ht (Work.Spaces.eta - 1) (2 : ℝ)]
      norm_num [Real.rpow_natCast]
    rw [ht2]
    field_simp
    ring
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hcoef : (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) ≤ 50 := by
    have h2 : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
      have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
      rwa [Real.rpow_one] at h'
    have hden : (1 : ℝ) + Work.Spaces.eta = 199 / 100 := by
      rw [Work.Spaces.eta]; norm_num
    rw [hden]
    calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (199 / 100)
          ≤ (36 : ℝ) * 2 / (199 / 100) := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 50 := by norm_num
  have ht0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) * t ^ (Work.Spaces.eta - 1)
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := mul_le_mul_of_nonneg_right hcoef ht0

/-! ## 6. The weighted endpoint-value estimate at the left endpoint -/

/-- **The weighted endpoint-value estimate at the left endpoint.**  For `F = lim_{x → 0⁺} f x`,
`f` of class `C²` on `(0, π/2)` with `(f'')² thEta` and `f² thEta` integrable there, and every
`t ∈ (0, π/2)`:

  `F² ≤ 2 t^{3+η} ∫_{Iθ} (f'')² thEta + 100 t^{η-1} ∫_{Iθ} f² thEta`. -/
theorem endpointParamLeftW_aux (f : ℝ → ℝ) (F t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta) *
        (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + 100 * t ^ (Work.Spaces.eta - 1) *
        (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
  have hsub : Set.Ioo (0 : ℝ) t ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩
  have h2t := h2.mono_set hsub
  have h1t := h1.mono_set hsub
  -- continuity of the two integrands on `(0, t)`
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    have h1' : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact (h1'.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcont0 : ContinuousOn f (Set.Ioo 0 t) := (hf.continuousOn).mono hsub
  -- the squares are integrable (the weight is `≥ 1`)
  have h2sq : IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h2t ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (deriv (deriv f) x) ^ 2 = (deriv (deriv f) x) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left
            (Work.EllipticEst.Core.thEtaFacts.2.1 x (hsub hx)) (sq_nonneg _)
  have h1sq : IntegrableOn (fun x : ℝ => (f x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h1t ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (f x) ^ 2 = (f x) ^ 2 * 1 := by ring
      _ ≤ (f x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left
            (Work.EllipticEst.Core.thEtaFacts.2.1 x (hsub hx)) (sq_nonneg _)
  -- `L¹` integrability from `L²` integrability
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 t) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hf2L1 : IntegrableOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    refine Integrable.mono' (h2sq.add hconst) (hcont2.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |deriv (deriv f) x| ≤ (deriv (deriv f) x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  have hfL1 : IntegrableOn f (Set.Ioo 0 t) := by
    refine Integrable.mono' (h1sq.add hconst) (hcont0.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |f x| ≤ (f x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  -- `f'` is bounded near `0⁺`
  obtain ⟨M, hM⟩ := EndpointValues.derivBoundedNearLeft ht hta.le hf h2sq
  -- the reproducing formula
  have hid : F = (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, etaT'' t x * f x :=
    EndpointValues.twoIbpEtaT f F t ht hta hf hlim ⟨M, hM⟩ hfL1 hf2L1
  -- positivity of the weight and nonnegativity of the two energies
  have hEtapos : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < Work.FTS.EllipticEst.thEta x :=
    fun x hx => thEta_pos_of_mem hta hx
  set Jt := ∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x
    with hJt
  set Xt := ∫ x in Set.Ioo 0 t, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hXt
  have hJt0 : 0 ≤ Jt := by
    rw [hJt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  have hXt0 : 0 ≤ Xt := by
    rw [hXt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  -- the weighted Cauchy–Schwarz inputs, first piece
  have hmemA : MemLp (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (continuousOn_etaT_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (integrableOn_etaT_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemA' : MemLp (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (continuousOn_etaT''_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (integrableOn_etaT''_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  -- second pieces
  have hmemB : MemLp (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
      2 (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont2.mul (continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h2t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemB' : MemLp (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont0.mul (continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h1t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  -- the two weighted Cauchy–Schwarz inequalities
  have hcsA := weighted_cs_integral measurableSet_Ioo hEtapos hmemA hmemB
  have hcsB := weighted_cs_integral measurableSet_Ioo hEtapos hmemA' hmemB'
  have hA2 : (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x) ^ 2
      ≤ t ^ (3 + Work.Spaces.eta) * Jt := by
    refine hcsA.trans ?_
    rw [hJt]
    exact mul_le_mul_of_nonneg_right (integral_etaT_sq_div_thEta_le t ht hta) hJt0
  have hB2 : (∫ x in Set.Ioo 0 t, etaT'' t x * f x) ^ 2
      ≤ 50 * t ^ (Work.Spaces.eta - 1) * Xt := by
    refine hcsB.trans ?_
    rw [hXt]
    exact mul_le_mul_of_nonneg_right (integral_etaT''_sq_div_thEta_le t ht hta) hXt0
  -- assembly
  have hF : F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
      + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := by
    rw [hid]
    nlinarith [hA2, hB2,
      sq_nonneg ((∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
        + (∫ x in Set.Ioo 0 t, etaT'' t x * f x))]
  set J := ∫ x in Set.Ioo 0 (Real.pi / 2),
    (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x with hJ
  set X := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hX
  have hJs : Jt ≤ J := by
    rw [hJt, hJ]
    refine MeasureTheory.setIntegral_mono_set h2 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Ioo hx)
  have hXs : Xt ≤ X := by
    rw [hXt, hX]
    refine MeasureTheory.setIntegral_mono_set h1 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Ioo hx)
  have htpow0 : 0 ≤ t ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg ht.le _
  have hEtpow0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := hF
    _ ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) := by
        have h1' : 2 * (t ^ (3 + Work.Spaces.eta) * Jt) ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJs htpow0) (by norm_num)
        have h2' : 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt)
            ≤ 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hXs (mul_nonneg (by norm_num) hEtpow0)) (by norm_num)
        linarith
    _ = 2 * t ^ (3 + Work.Spaces.eta) * J
        + 100 * t ^ (Work.Spaces.eta - 1) * X := by ring

theorem endpointParamRightW (f : ℝ → ℝ) (F t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F))
    (h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta) *
        (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + 100 * t ^ (Work.Spaces.eta - 1) *
        (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
  obtain ⟨hintR, hintIR, hcdR, _hd1R, hd2R, hlimR⟩ := EndpointValues.reflectFacts
  set g : ℝ → ℝ := fun x => f (Real.pi / 2 - x) with hg_eq
  have hg_cd : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [hg_eq] using hcdR f hf
  have hg_lim : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
    simpa only [hg_eq] using hlimR f F hlim
  -- pointwise identification of the two integrands with the reflected ones
  have hpt2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x
        = (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
            (Real.pi / 2 - x) := by
    intro x hx
    have h1 : deriv (deriv g) x = deriv (deriv f) (Real.pi / 2 - x) := by
      simpa only [hg_eq] using hd2R f hf x hx
    rw [h1]
    simp only [thEta_pi_div_two_sub]
  have hpt1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (g x) ^ 2 * Work.FTS.EllipticEst.thEta x
        = (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) (Real.pi / 2 - x) := by
    intro x _
    simp only [hg_eq]
    rw [thEta_pi_div_two_sub]
  -- transfer of the two integrability hypotheses
  have hg_2 : IntegrableOn (fun x : ℝ => (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hintIR (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y) h2).congr_fun
      (fun x hx => (hpt2 x hx).symm) measurableSet_Ioo
  have hg_1 : IntegrableOn (fun x : ℝ => (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hintIR (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) h1).congr_fun
      (fun x hx => (hpt1 x hx).symm) measurableSet_Ioo
  -- the weighted left-endpoint estimate for the reflected function
  have hmain := endpointParamLeftW_aux g F t ht hta hg_cd hg_lim hg_2 hg_1
  -- the two integrals are invariant under the reflection
  have hIg : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
    calc (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
              (Real.pi / 2 - x) :=
          setIntegral_congr_fun measurableSet_Ioo hpt2
      _ = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
          simpa using hintR (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
  have hIf : (∫ x in Set.Ioo 0 (Real.pi / 2), (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
    calc (∫ x in Set.Ioo 0 (Real.pi / 2), (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) (Real.pi / 2 - x) :=
          setIntegral_congr_fun measurableSet_Ioo hpt1
      _ = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
          simpa using hintR (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y)
  rwa [hIg, hIf] at hmain

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.sliceBoundaryLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

-- ===== my helpers =====

/-- FTC on the open interval for a function of class `C¹` there. -/
private lemma sbl_deriv_ftc {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hb : b ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  refine intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hf.mono ?_)
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt h2 hb.2⟩
  · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt h2 ha.2⟩

/-- Set integral over `Ioo a b` equals the interval integral, for `a ≤ b`. -/
private lemma sbl_setIntegral_Ioo_eq_intervalIntegral {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Ioo a b, F t) = ∫ t in a..b, F t := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- A set and a superset differing by a finite set are a.e. equal. -/
private lemma sbl_ae_eq_set_of_sdiff_finite {s t : Set ℝ} (h : s ⊆ t) (hfin : (t \ s).Finite) :
    s =ᵐ[MeasureTheory.volume] t := by
  have h0 : MeasureTheory.volume (t \ s) = 0 := Set.Finite.measure_zero hfin MeasureTheory.volume
  have hmem : ∀ᵐ x : ℝ, x ∉ (t \ s) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using h0
  filter_upwards [hmem] with x hx
  exact propext ⟨fun hxs => h hxs, fun hxt => by
    by_contra hxs
    exact hx ⟨hxt, hxs⟩⟩

private lemma sbl_integrableOn_of_ae_eq_set {F : ℝ → ℝ} {s t : Set ℝ}
    (h : s =ᵐ[MeasureTheory.volume] t) (hF : MeasureTheory.IntegrableOn F s) :
    MeasureTheory.IntegrableOn F t := by
  rw [MeasureTheory.IntegrableOn] at hF ⊢
  exact MeasureTheory.Measure.restrict_congr_set h ▸ hF

/-- `IntegrableOn F (Ioo a b)` implies `IntegrableOn F (Ioc a b)`. -/
private lemma sbl_integrableOn_Ioc_of_Ioo {F : ℝ → ℝ} {a b : ℝ}
    (h : MeasureTheory.IntegrableOn F (Set.Ioo a b)) :
    MeasureTheory.IntegrableOn F (Set.Ioc a b) :=
  sbl_integrableOn_of_ae_eq_set
    (sbl_ae_eq_set_of_sdiff_finite (fun x hx => ⟨hx.1, le_of_lt hx.2⟩) (by
      refine Set.Finite.subset (Set.finite_singleton b) ?_
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_singleton_iff]
      by_contra hxb
      exact hx2 ⟨hx1.1, lt_of_le_of_ne hx1.2 hxb⟩)) h

/-- Interval integrability from integrability on the open interval, for `a ≤ b`. -/
private lemma sbl_intervalIntegrable_of_integrableOn_Ioo {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : MeasureTheory.IntegrableOn F (Set.Ioo a b)) : IntervalIntegrable F volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact sbl_integrableOn_Ioc_of_Ioo h

private lemma sbl_setIntegral_nonneg_Ioo {F : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t ∈ Set.Ioo a b, 0 ≤ F t) : 0 ≤ ∫ t in Set.Ioo a b, F t :=
  MeasureTheory.setIntegral_nonneg measurableSet_Ioo h

/-- The angular energy `∫_{(0,θ)} (f')² thEta` is monotone in `θ`. -/
private lemma sbl_energy_mono {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  · filter_upwards with t ht
    exact ⟨ht.1, lt_trans ht.2 hθ.2⟩

private lemma sbl_energy_mono_right {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  · filter_upwards with t ht
    exact ⟨lt_trans hθ.1 ht.1, ht.2⟩

theorem sliceBoundaryLimit : ∃ K : ℝ, 0 < K ∧
  ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi/2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi/2)) →
    (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi/2), (f θ - c)^2 ≤ K * θ^(1 + Work.Spaces.eta) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo 0 θ))
          (fun θ' : ℝ => (deriv f θ')^2 * Work.FTS.EllipticEst.thEta θ'))
    ∧ (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi/2), (f θ - c)^2 ≤ K * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi/2)))
          (fun θ' : ℝ => (deriv f θ')^2 * Work.FTS.EllipticEst.thEta θ')) := by
  refine ⟨2, by norm_num, ?_⟩
  intro f hf hint
  obtain ⟨hth_pos, hth_one, hth_inv, hth_cont⟩ := thEtaFacts
  obtain ⟨hwiL, hbL, hwiR, hbR⟩ := thEtaInvIntegralBounds
  obtain ⟨hsqInt, habsInt, hderivInt⟩ := derivIntegrableOfEnergy f hf hint
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
  have hpi4 : (Real.pi / 4) ∈ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hInt : ∀ {a b : ℝ}, Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t => deriv f t) (Set.Ioo a b) := by
    intro a b hsub
    refine MeasureTheory.Integrable.mono' (habsInt.mono_set hsub) ?_ ?_
    · exact (hderiv_cont.mono hsub).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards with t using le_of_eq (Real.norm_eq_abs (deriv f t))
  have hII : ∀ {a b : ℝ}, a ≤ b → Set.Ioo a b ⊆ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun t => deriv f t) volume a b :=
    fun hab hsub => sbl_intervalIntegrable_of_integrableOn_Ioo hab (hInt hsub)
  have hA0 : 0 ≤ ∫ t in Set.Ioo 0 (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  -- ### Left endpoint
  have hleft : ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2 ≤ 2 * θ^(1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
    have hI0 : IntervalIntegrable (fun t => deriv f t) volume (0:ℝ) (Real.pi/4) :=
      hII (by linarith [Real.pi_pos])
        (fun t ht => ⟨ht.1, lt_trans ht.2 (by linarith [Real.pi_pos])⟩)
    set c : ℝ := f (Real.pi/4) - ∫ x in (0:ℝ)..(Real.pi/4), deriv f x with hc
    have hkeyI : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = ∫ x in (0:ℝ)..θ, deriv f x := by
      intro θ hθ
      have h1 : f θ - c
          = (f θ - f (Real.pi/4)) + ∫ x in (0:ℝ)..(Real.pi/4), deriv f x := by
        rw [hc]; ring
      have hftc : f θ - f (Real.pi/4) = ∫ x in (Real.pi/4)..θ, deriv f x :=
        (sbl_deriv_ftc hf hpi4 hθ).symm
      rcases le_total θ (Real.pi/4) with hle | hge
      · have hIθ4 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/4) :=
          hII hle (fun t ht => ⟨lt_trans hθ.1 ht.1, lt_trans ht.2 hpi4.2⟩)
        have hI0θ : IntervalIntegrable (fun t => deriv f t) volume (0:ℝ) θ :=
          hII (le_of_lt hθ.1) (fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩)
        have hsym : (∫ x in (Real.pi/4)..θ, deriv f x) = -(∫ x in θ..(Real.pi/4), deriv f x) :=
          intervalIntegral.integral_symm θ (Real.pi/4)
        have hadd : (∫ x in (0:ℝ)..θ, deriv f x) + (∫ x in θ..(Real.pi/4), deriv f x)
            = ∫ x in (0:ℝ)..(Real.pi/4), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI0θ hIθ4
        rw [h1, hftc, hsym]
        linarith
      · have hI4θ : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) θ :=
          hII hge (fun t ht => ⟨lt_trans hpi4.1 ht.1, lt_trans ht.2 hθ.2⟩)
        have hadd : (∫ x in (0:ℝ)..(Real.pi/4), deriv f x) + (∫ x in (Real.pi/4)..θ, deriv f x)
            = ∫ x in (0:ℝ)..θ, deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI0 hI4θ
        rw [h1, hftc]
        linarith
    have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = ∫ t in Set.Ioo 0 θ, deriv f t := by
      intro θ hθ
      rw [sbl_setIntegral_Ioo_eq_intervalIntegral (le_of_lt hθ.1)]
      exact hkeyI θ hθ
    have hbound : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        (f θ - c)^2 ≤ 2 * θ^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
      intro θ hθ
      have hsub : Set.Ioo 0 θ ⊆ Set.Ioo 0 (Real.pi/2) := fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩
      have hcs := weightedCS (s := Set.Ioo 0 θ) measurableSet_Ioo
        (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
        (fun t ht => hth_pos t (hsub ht))
        (hth_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hwiL θ hθ)
      have hA : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg
            ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
      rw [hkey θ hθ]
      calc (∫ t in Set.Ioo 0 θ, deriv f t)^2
          ≤ (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (2 * θ^(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left (hbL θ hθ) hA
        _ = 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by ring
    refine ⟨c, ?_, hbound⟩
    refine tendstoSqBoundLeft (M := 2 * (∫ t in Set.Ioo 0 (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)) ?_ ?_
    · exact mul_nonneg (by norm_num) hA0
    · intro θ hθ
      calc (f θ - c)^2
          ≤ 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            hbound θ hθ
        _ ≤ 2 * θ^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            mul_le_mul_of_nonneg_left (sbl_energy_mono hint hθ)
              (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hθ.1 _)))
        _ = (2 * (∫ t in Set.Ioo 0 (Real.pi/2),
                (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * θ^(1 + Work.Spaces.eta) := by ring
  -- ### Right endpoint
  have hright : ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2
        ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
    have hI42 : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) (Real.pi/2) :=
      hII (by linarith [Real.pi_pos]) (fun t ht => ⟨lt_trans hpi4.1 ht.1, ht.2⟩)
    set c : ℝ := f (Real.pi/4) + ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x with hc
    have hkeyI : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = -∫ x in θ..(Real.pi/2), deriv f x := by
      intro θ hθ
      have h1 : f θ - c
          = (f θ - f (Real.pi/4)) - ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x := by
        rw [hc]; ring
      have hftc : f θ - f (Real.pi/4) = ∫ x in (Real.pi/4)..θ, deriv f x :=
        (sbl_deriv_ftc hf hpi4 hθ).symm
      rcases le_total θ (Real.pi/4) with hle | hge
      · have hIθ4 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/4) :=
          hII hle (fun t ht => ⟨lt_trans hθ.1 ht.1, lt_trans ht.2 hpi4.2⟩)
        have hsym : (∫ x in (Real.pi/4)..θ, deriv f x) = -(∫ x in θ..(Real.pi/4), deriv f x) :=
          intervalIntegral.integral_symm θ (Real.pi/4)
        have hadd : (∫ x in θ..(Real.pi/4), deriv f x)
              + (∫ x in (Real.pi/4)..(Real.pi/2), deriv f x)
            = ∫ x in θ..(Real.pi/2), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hIθ4 hI42
        rw [h1, hftc, hsym]
        linarith
      · have hI4θ : IntervalIntegrable (fun t => deriv f t) volume (Real.pi/4) θ :=
          hII hge (fun t ht => ⟨lt_trans hpi4.1 ht.1, lt_trans ht.2 hθ.2⟩)
        have hIθ2 : IntervalIntegrable (fun t => deriv f t) volume θ (Real.pi/2) :=
          hII (le_of_lt hθ.2) (fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩)
        have hadd : (∫ x in (Real.pi/4)..θ, deriv f x)
              + (∫ x in θ..(Real.pi/2), deriv f x)
            = ∫ x in (Real.pi/4)..(Real.pi/2), deriv f x :=
          intervalIntegral.integral_add_adjacent_intervals hI4θ hIθ2
        rw [h1, hftc]
        linarith
    have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        f θ - c = -∫ t in Set.Ioo θ (Real.pi/2), deriv f t := by
      intro θ hθ
      rw [hkeyI θ hθ, sbl_setIntegral_Ioo_eq_intervalIntegral (le_of_lt hθ.2)]
    have hbound : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (f θ - c)^2
        ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) *
          ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t := by
      intro θ hθ
      have hsub : Set.Ioo θ (Real.pi/2) ⊆ Set.Ioo 0 (Real.pi/2) :=
        fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
      have hcs := weightedCS (s := Set.Ioo θ (Real.pi/2)) measurableSet_Ioo
        (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
        (fun t ht => hth_pos t (hsub ht))
        (hth_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hwiR θ hθ)
      have hA : 0 ≤ ∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        sbl_setIntegral_nonneg_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg
            ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
      have hsq : (f θ - c)^2 = (∫ t in Set.Ioo θ (Real.pi/2), deriv f t)^2 := by
        rw [hkey θ hθ]; ring
      rw [hsq]
      calc (∫ t in Set.Ioo θ (Real.pi/2), deriv f t)^2
          ≤ (∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (∫ t in Set.Ioo θ (Real.pi/2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo θ (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * (2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left (hbR θ hθ) hA
        _ = 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by ring
    refine ⟨c, ?_, hbound⟩
    refine tendstoSqBoundRight (M := 2 * (∫ t in Set.Ioo 0 (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)) ?_ ?_
    · exact mul_nonneg (by norm_num) hA0
    · intro θ hθ
      calc (f θ - c)^2
          ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            hbound θ hθ
        _ ≤ 2 * (Real.pi/2 - θ)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 (Real.pi/2),
                  (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) :=
            mul_le_mul_of_nonneg_left (sbl_energy_mono_right hint hθ)
              (mul_nonneg (by norm_num)
                (le_of_lt (Real.rpow_pos_of_pos (by linarith [hθ.2, Real.pi_pos]) _)))
        _ = (2 * (∫ t in Set.Ioo 0 (Real.pi/2),
                (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) := by ring
  exact ⟨hleft, hright⟩

end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.thetaAgmonCompact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (thEta)

namespace Work.EllipticEst.Core

/-! ## 1. The integrands vanish off the support

`f` vanishes off `Icc a b`; since `Icc a b` is closed, the complement is an open
neighbourhood of every point outside it, so all the derivatives of `f` that occur in the
Agmon inequality vanish there as well. -/


/-! ## 2. Set integral over `Iθ` versus interval integral over `[a,b]` -/


/-! ## 3. Vanishing at the endpoints of the support -/


/-! ## 4. `thEta` is `C²` at every point of `[a,b] ⊆ (0,π/2)` -/


/-! ## 5. The second derivative of the weight `thEta θ = sin(2θ)^{-η}`

On `(0,π/2)` one has `ρ'' = 4η(η+1) sin(2θ)^{-(η+2)} - 4η² ρ`. -/


/-! ## 6. Weighted integration by parts on `[a,b]` -/


/-! ## 7. The integral of `f² ρ''` -/


/-! ## 8. The angular Agmon inequality -/


end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.psiTrunc_tail_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam

/-! ## Three elementary auxiliary facts -/

/-- The tail sum over `Finset.Icc (M+1) N` as a difference of partial sums of `Finset.range`. -/
private lemma sum_Icc_eq_sum_range_sub (f : ℕ → ℝ) {M N : ℕ} (h : M ≤ N) :
    ∑ m ∈ Finset.Icc (M + 1) N, f m
      = ∑ m ∈ Finset.range (N + 1), f m - ∑ m ∈ Finset.range (M + 1), f m := by
  have hI : (Finset.Icc (M + 1) N : Finset ℕ) = Finset.Ico (M + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI]
  exact Finset.sum_Ico_eq_sub f (Nat.succ_le_succ h)

/-- Two functions agreeing on the open interval `(0, π/2)` agree almost everywhere on
`Iθ = [0, π/2]` (the two endpoints form a null set). -/
private lemma ae_eq_restrict_Iθ_of_eqOn_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = h θ) :
    g =ᵐ[volume.restrict Iθ] h := by
  show ∀ᵐ θ ∂(volume.restrict Iθ), g θ = h θ
  rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc),
    MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬(x ∈ Iθ → g x = h x)} = {x : ℝ | x ∈ Iθ ∧ g x ≠ h x} := by
    ext x; simp only [not_imp]
  rw [hset]
  refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · rintro x ⟨hxI, hxg⟩
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    rcases eq_or_lt_of_le hxI.1 with h0 | h0
    · exact Or.inl h0.symm
    · rcases eq_or_lt_of_le hxI.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (hgh x ⟨h0, h2⟩) hxg
  · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

/-- Comparison of an interval integral over `[c,d] ⊆ Iθ` with the `cos`-weighted set integral over
`Iθ`: because `cos t ≥ cos d > 0` on `[c,d]`, the factor `1/cos d` is the only loss. -/
private lemma intervalIntegral_le_inv_cos_Itheta' (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) {c d : ℝ} (hcd : c < d) (hc : 0 < c) (hd : d < Real.pi / 2) :
    (∫ t in c..d, F t) ≤ (1 / Real.cos d) * ∫ t in Iθ, F t * Real.cos t := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hsub : Set.Ioc c d ⊆ Iθ := by
    intro t ht
    exact ⟨(lt_trans hc ht.1).le, (lt_of_le_of_lt ht.2 hd).le⟩
  have hcos_t : ∀ t ∈ Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hcos_ge : ∀ t ∈ Set.Ioc c d, Real.cos d ≤ Real.cos t := by
    intro t ht
    exact Real.cos_le_cos_of_nonneg_of_le_pi (lt_trans hc ht.1).le
      (by linarith [Real.pi_pos, hd]) ht.2
  have hIntF : IntegrableOn F (Set.Ioc c d) :=
    hF.integrableOn_Icc.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hIntFc : IntegrableOn (fun t => F t * Real.cos t) (Set.Ioc c d) :=
    (hF.mul Real.continuous_cos).integrableOn_Icc.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hIntIθ : IntegrableOn (fun t => F t * Real.cos t) Iθ :=
    (hF.mul Real.continuous_cos).integrableOn_Icc
  rw [intervalIntegral.integral_of_le hcd.le]
  have hstep1 : (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := by
    refine setIntegral_mono_on hIntF (hIntFc.const_mul _) measurableSet_Ioc (fun t ht => ?_)
    have h1 : 1 ≤ Real.cos t / Real.cos d := (one_le_div hcosd).mpr (hcos_ge t ht)
    calc F t = F t * 1 := by ring
      _ ≤ F t * (Real.cos t / Real.cos d) := mul_le_mul_of_nonneg_left h1 (hF0 t)
      _ = (1 / Real.cos d) * (F t * Real.cos t) := by ring
  have hstep2 : (∫ t in Set.Ioc c d, F t * Real.cos t) ≤ ∫ t in Iθ, F t * Real.cos t := by
    refine setIntegral_mono_set hIntIθ ?_ (Filter.Eventually.of_forall (fun t ht => hsub ht))
    show ∀ᵐ t ∂(volume.restrict Iθ), 0 ≤ F t * Real.cos t
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Filter.Eventually.of_forall (fun t ht => mul_nonneg (hF0 t) (hcos_t t ht))
  calc (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := hstep1
    _ = (1 / Real.cos d) * ∫ t in Set.Ioc c d, F t * Real.cos t := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / Real.cos d) * ∫ t in Iθ, F t * Real.cos t :=
        mul_le_mul_of_nonneg_left hstep2 (div_nonneg zero_le_one hcosd.le)

/-! ## The main theorem -/

theorem psiTrunc_tail_bound (α : ℝ) {F : ℝ → ℝ → ℝ} {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z θ : ℝ) (M N : ℕ), θ ∈ Set.Icc c d → M ≤ N →
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
        ≤ K * Real.sqrt
            ((∑ m ∈ Finset.Icc (M + 1) N,
                (∫ θ' in Work.Spaces.Iθ,
                    Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                  * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
              + ∑ m ∈ Finset.Icc (M + 1) N,
                  Work.FTS.PhiStar.Gegenbauer.lam m
                    * (∫ θ' in Work.Spaces.Iθ,
                        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                    * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hcosd0 : 0 ≤ Real.cos d := hcosd.le
  refine ⟨Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d), ?_, ?_⟩
  · have h1 : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c) :=
      div_pos (Real.sqrt_pos_of_pos (div_pos one_pos hcosd)) (Real.sqrt_pos_of_pos hLpos)
    have h2 : 0 ≤ Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  intro z θ M N hθ hMN
  -- ## abbreviations
  set s : Finset ℕ := Finset.Icc (M + 1) N with hs
  set P : ℝ := ∑ m ∈ s,
      (∫ t in Iθ, eF m t ^ 2 * Real.cos t)
        * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 with hPdef
  set Q : ℝ := ∑ m ∈ s, lamF m
      * (∫ t in Iθ, eF m t ^ 2 * Real.cos t)
      * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 with hQdef
  set V : ℝ → ℝ := fun t => ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z * eF m t with hV
  set K : ℝ := Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d) with hKdef
  have hVeq : ∀ t : ℝ, V t = ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z * eF m t := fun t => rfl
  -- ## the difference of the partial sums is the tail sum
  have hdiff : ∀ t : ℝ, Work.FTS.PhiStar.Series.psiTrunc α F N z t
      - Work.FTS.PhiStar.Series.psiTrunc α F M z t = V t := by
    intro t
    rw [hVeq t]
    have h2 := sum_Icc_eq_sum_range_sub
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z * eF m t) hMN
    simp only [Work.FTS.PhiStar.Series.psiTrunc]
    rw [hs]
    exact h2.symm
  -- ## vanishing at the two endpoints
  have hV0 : V 0 = 0 := by
    rw [hVeq]
    simp [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]
  have hVpi : V (Real.pi / 2) = 0 := by
    rw [hVeq]
    simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]
  -- ## smoothness
  have hVcont : ContDiff ℝ 3 V := by
    rw [hV]
    refine ContDiff.sum (fun m _ => ?_)
    have hcst : ContDiff ℝ 3 (fun _ : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z) :=
      contDiff_const
    exact hcst.mul (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m)
  have hderiv : Continuous (deriv V) := hVcont.continuous_deriv (by norm_num)
  -- ## the pointwise `Lzero` action on the tail sum
  have hLz : ∀ t : ℝ, Work.FTS.EllipticEst.Lzero1 V t
      = Work.Elliptic.Lzero (fun _ θ' => V θ') 0 t := by
    intro t
    simpa using congrArg (fun f : ℝ → ℝ => f t)
      (Work.FTS.EllipticEst.Lzero1_eq_Lzero V 0)
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Elliptic.Lzero (fun _ θ' => V θ') 0 t
        = ∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t := by
    intro t ht
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    have h1 : (fun (_ : ℝ) θ' => V θ')
        = (fun (_ : ℝ) θ' => ∑ m ∈ s,
            Work.FTS.PhiStar.Series.acoeff α m F z * eF m θ') := by
      funext x θ'
      exact hVeq θ'
    rw [h1]
    exact PTBSupp.lzero_finSum_gen (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s 0 t hcos
  -- ## the two diagonal pairings
  have hP : (∫ t in Iθ, V t ^ 2 * Real.cos t) = P := by
    rw [hPdef]
    have hsq : (∫ t in Iθ, V t ^ 2 * Real.cos t)
        = ∫ t in Iθ, V t * V t * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      ring
    have hcongr : (∫ t in Iθ, V t * V t * Real.cos t)
        = ∫ t in Iθ,
            (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      simp only [hVeq]
    rw [hsq, hcongr]
    exact (PTBSupp.finSum_bilin_gen (fun m => Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s).trans
      (Finset.sum_congr rfl (fun m _ => by
        have h1 : (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
            = (∫ t in Iθ, eF m t ^ 2 * Real.cos t) := rfl
        rw [h1]
        ring))
  have hQ : (∫ t in Iθ, Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t) = Q := by
    rw [hQdef]
    have hae : (fun t : ℝ => Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t)
        =ᵐ[volume.restrict Iθ]
        (fun t : ℝ =>
            (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * V t * Real.cos t) := by
      refine ae_eq_restrict_Iθ_of_eqOn_Ioo ?_
      intro t ht
      rw [hLz t, hpt t ht]
    rw [integral_congr_ae hae]
    have h2 : (∫ t in Iθ,
          (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
            * V t * Real.cos t)
        = ∫ t in Iθ,
            (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      simp only [hVeq]
    rw [h2]
    exact (PTBSupp.finSum_bilin_gen
        (fun m => lamF m * Work.FTS.PhiStar.Series.acoeff α m F z)
        (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s).trans
      (Finset.sum_congr rfl (fun m _ => by
        have h1 : (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
            = (∫ t in Iθ, eF m t ^ 2 * Real.cos t) := rfl
        rw [h1]
        ring))
  -- ## positivity of the two sums
  have hsig : ∀ m : ℕ, 0 ≤ ∫ t in Iθ, eF m t ^ 2 * Real.cos t := by
    intro m
    refine setIntegral_nonneg measurableSet_Icc (fun t ht => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos],
        by linarith [ht.2, Real.pi_pos]⟩)
  have hlam : ∀ m : ℕ, 0 ≤ lamF m := by
    intro m
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    positivity
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hsig m) (sq_nonneg _))
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg (fun m _ =>
      mul_nonneg (mul_nonneg (hlam m) (hsig m)) (sq_nonneg _))
  -- ## integrability of the four energy integrands
  have hintA : IntegrableOn (fun t => (deriv V t) ^ 2 * Real.cos t) Iθ :=
    ((hderiv.pow 2).mul Real.continuous_cos).integrableOn_Icc
  have hintC : IntegrableOn (fun t => V t ^ 2 * Real.cos t) Iθ :=
    ((hVcont.continuous.pow 2).mul Real.continuous_cos).integrableOn_Icc
  have hUcont : Continuous (fun t : ℝ => ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z
        * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) :=
    continuous_finsetSum s (fun m _ =>
      ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
        Real.continuous_sin).const_mul (Work.FTS.PhiStar.Series.acoeff α m F z))
  have hintB : IntegrableOn (fun t => (V t / Real.cos t) ^ 2 * Real.cos t) Iθ := by
    have hnice : IntegrableOn (fun t : ℝ => (∑ m ∈ s,
        Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) ^ 2 * Real.cos t) Iθ :=
      ((hUcont.pow 2).mul Real.continuous_cos).integrableOn_Icc
    refine hnice.congr_fun_ae (ae_eq_restrict_Iθ_of_eqOn_Ioo ?_)
    intro t ht
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    have hVt : V t = Real.cos t * (∑ m ∈ s,
        Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) := by
      rw [hVeq]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
      ring
    rw [hVt, mul_div_cancel_left₀ _ hcos]
  have hScont : Continuous (fun t : ℝ => ∑ m ∈ s, lamF m
      * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t) :=
    continuous_finsetSum s (fun m _ =>
      (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous.const_mul
        (lamF m * Work.FTS.PhiStar.Series.acoeff α m F z))
  have hintL : IntegrableOn (fun t => Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t) Iθ := by
    have hnice : IntegrableOn (fun t : ℝ =>
        (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
          * V t * Real.cos t) Iθ :=
      ((hScont.mul hVcont.continuous).mul Real.continuous_cos).integrableOn_Icc
    refine hnice.congr_fun_ae (ae_eq_restrict_Iθ_of_eqOn_Ioo ?_)
    intro t ht
    rw [hLz t, hpt t ht]
  -- ## the weighted energy identity
  have hVcd : ContDiffOn ℝ 2 V (Set.Icc 0 (Real.pi / 2)) :=
    (hVcont.contDiffOn (s := Set.Icc (0 : ℝ) (Real.pi / 2))).of_le (by norm_num)
  have henergy := Lzero1_energy_cos_correct V hVcd hV0 hVpi hintL hintA hintB hintC
  have hBnn : 0 ≤ ∫ t in Iθ, (V t / Real.cos t) ^ 2 * Real.cos t := by
    refine setIntegral_nonneg measurableSet_Icc (fun t ht => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos],
        by linarith [ht.2, Real.pi_pos]⟩)
  have hEnergy : (∫ t in Iθ, (deriv V t) ^ 2 * Real.cos t) ≤ Q + 6 * P := by
    rw [hQ, hP] at henergy
    linarith
  -- ## comparison of the `[c,d]` and `Iθ` integrals
  have hIntV : (∫ x in c..d, V x ^ 2) ≤ (1 / Real.cos d) * P :=
    calc (∫ x in c..d, V x ^ 2)
        ≤ (1 / Real.cos d) * ∫ t in Iθ, V t ^ 2 * Real.cos t :=
          intervalIntegral_le_inv_cos_Itheta' (fun x : ℝ => V x ^ 2)
            (hVcont.continuous.pow 2) (fun t => sq_nonneg _) hcd hc hd
      _ = (1 / Real.cos d) * P := by simp only [hP]
  have hIntD : (∫ x in c..d, (deriv V x) ^ 2) ≤ (1 / Real.cos d) * (Q + 6 * P) := by
    have hbase := intervalIntegral_le_inv_cos_Itheta'
      (fun x : ℝ => (deriv V x) ^ 2) (hderiv.pow 2) (fun t => sq_nonneg _) hcd hc hd
    calc (∫ x in c..d, (deriv V x) ^ 2)
        ≤ (1 / Real.cos d) * ∫ t in Iθ, deriv V t ^ 2 * Real.cos t := hbase
      _ ≤ (1 / Real.cos d) * (Q + 6 * P) :=
          mul_le_mul_of_nonneg_left hEnergy (div_nonneg zero_le_one hcosd0)
  -- ## the two square-root bounds
  have hsV : Real.sqrt (∫ x in c..d, V x ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q) := by
    calc Real.sqrt (∫ x in c..d, V x ^ 2) ≤ Real.sqrt ((1 / Real.cos d) * P) :=
          Real.sqrt_le_sqrt hIntV
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt P :=
          Real.sqrt_mul (div_nonneg zero_le_one hcosd0) P
      _ ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_right hQ0))
            (Real.sqrt_nonneg _)
  have hsD : Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
      ≤ Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q) := by
    have h2 : (1 / Real.cos d) * (Q + 6 * P) ≤ (7 / Real.cos d) * (P + Q) := by
      have h3 : Q + 6 * P ≤ 7 * (P + Q) := by linarith
      calc (1 / Real.cos d) * (Q + 6 * P) = (Q + 6 * P) / Real.cos d := by ring
        _ ≤ (7 * (P + Q)) / Real.cos d := div_le_div_of_nonneg_right h3 hcosd0
        _ = (7 / Real.cos d) * (P + Q) := by ring
    calc Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * (Q + 6 * P)) := Real.sqrt_le_sqrt hIntD
      _ ≤ Real.sqrt ((7 / Real.cos d) * (P + Q)) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q) :=
          Real.sqrt_mul (div_nonneg (by norm_num) hcosd0) (P + Q)
  have hA : Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
      ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q) := by
    calc Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
        ≤ (Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q)) / Real.sqrt (d - c) :=
          div_le_div_of_nonneg_right hsV (Real.sqrt_nonneg _)
      _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q) := by ring
  have hB : Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
      ≤ (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) := by
    calc Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
        ≤ Real.sqrt (d - c) * (Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q)) :=
          mul_le_mul_of_nonneg_left hsD (Real.sqrt_nonneg _)
      _ = (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) := by ring
  -- ## the one-dimensional `L∞`–`L²` bound
  have hVcd1 : ContDiffOn ℝ 1 V (Set.Icc c d) :=
    (hVcont.contDiffOn (s := Set.Icc c d)).of_le (by norm_num)
  have habs := abs_le_of_l2_Icc V hcd hθ hVcd1
  calc |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
      = |V θ| := by rw [hdiff θ]
    _ ≤ Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2) := habs
    _ ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q)
          + (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) :=
        add_le_add hA hB
    _ = K * Real.sqrt (P + Q) := by rw [hKdef]; ring

end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.BSSwirl.CdCont =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- `smulRight` is additive in its first argument. -/
theorem sub_smulRight (c c' : R3 →L[ℝ] ℝ) (v : R3) :
    (c - c').smulRight v = c.smulRight v - c'.smulRight v := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply, sub_smul]

/-- The integrand `z ↦ (A z).smulRight (g (c + z))` is a.e. strongly measurable as soon as `A`
and `g` are. -/
theorem aestronglyMeasurable_smulRight_comp {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {c : R3}
    (hA : AEStronglyMeasurable A volume) (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun z : R3 => (A z).smulRight (g (c + z))) volume := by
  have h1 : AEMeasurable A volume := aestronglyMeasurable_iff_aemeasurable.mp hA
  have h2 : AEMeasurable (fun z : R3 => g (c + z)) volume :=
    aestronglyMeasurable_iff_aemeasurable.mp
      (hg.comp_quasiMeasurePreserving
        (measurePreserving_add_left (volume : Measure R3) c).quasiMeasurePreserving)
  have hcont : Continuous fun p : (R3 →L[ℝ] ℝ) × R3 => p.1.smulRight p.2 :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := R3) (F := R3)).continuous
  exact (hcont.aemeasurable2 h1 h2).aestronglyMeasurable

/-- The integrand `z ↦ (A (z + t)).smulRight (g (c + z))` is integrable when `A` is integrable
and `g` is bounded and a.e. strongly measurable. -/
theorem integrable_smulRight_shift {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {M : ℝ} {t c : R3}
    (hA : Integrable A volume) (hg : ∀ y, ‖g y‖ ≤ M) (hgmeas : AEStronglyMeasurable g volume) :
    Integrable (fun z : R3 => (A (z + t)).smulRight (g (c + z))) volume := by
  have hAt : Integrable (fun z : R3 => A (z + t)) volume := by
    simpa only [sub_neg_eq_add] using hA.comp_sub_right (-t)
  refine Integrable.mono' (hAt.norm.mul_const M) ?_ ?_
  · refine aestronglyMeasurable_smulRight_comp ?_ hgmeas
    exact hA.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right (volume : Measure R3) t).quasiMeasurePreserving
  · filter_upwards with z
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_left (hg (c + z)) (norm_nonneg _)

/-- **Continuity of the singular kernel integral.**  If `A` is integrable and `g` is bounded by `M`
and a.e. strongly measurable, and if the `L¹`-norm of `A` is continuous under translations
(`htrans`), then `x ↦ ∫ z, (A z).smulRight (g (x + z))` is continuous. -/
theorem continuous_integral_smulRight_shift {A : R3 → (R3 →L[ℝ] ℝ)} {g : R3 → R3} {M : ℝ}
    (hA : Integrable A volume) (hg : ∀ y, ‖g y‖ ≤ M) (hgmeas : AEStronglyMeasurable g volume)
    (htrans : Tendsto (fun h : R3 => ∫ z, ‖A (z + h) - A z‖) (𝓝 0) (𝓝 0)) :
    Continuous (fun x : R3 => ∫ z, (A z).smulRight (g (x + z))) := by
  have hM : 0 ≤ M := (norm_nonneg (g 0)).trans (hg 0)
  -- the key estimate: shifting the density to the kernel
  have hkey : ∀ x₀ h : R3,
      dist (∫ z, (A z).smulRight (g (x₀ + h + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
        ≤ M * ∫ z, ‖A (z + h) - A z‖ := by
    intro x₀ h
    have hsplit : (∫ z, (A z).smulRight (g (x₀ + z)))
        = ∫ z, (A (z + h)).smulRight (g (x₀ + h + z)) := by
      have hsub := integral_add_right_eq_self (μ := (volume : Measure R3))
        (f := fun z : R3 => (A z).smulRight (g (x₀ + z))) h
      rw [← hsub]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (A (z + h)).smulRight (g (x₀ + (z + h))) = (A (z + h)).smulRight (g (x₀ + h + z))
      have harg : x₀ + (z + h) = x₀ + h + z := by abel
      rw [harg]
    have hint1 : Integrable (fun z : R3 => (A z).smulRight (g (x₀ + h + z))) volume := by
      simpa only [add_zero] using
        integrable_smulRight_shift (t := 0) (c := x₀ + h) hA hg hgmeas
    have hint2 : Integrable (fun z : R3 => (A (z + h)).smulRight (g (x₀ + h + z))) volume :=
      integrable_smulRight_shift (t := h) (c := x₀ + h) hA hg hgmeas
    have hdiff : (∫ z, (A z).smulRight (g (x₀ + h + z)))
          - (∫ z, (A z).smulRight (g (x₀ + z)))
        = ∫ z, ((A z) - (A (z + h))).smulRight (g (x₀ + h + z)) := by
      rw [hsplit, ← integral_sub hint1 hint2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact (sub_smulRight (A z) (A (z + h)) (g (x₀ + h + z))).symm
    have hAh : Integrable (fun z : R3 => A (z + h)) volume := by
      simpa only [sub_neg_eq_add] using hA.comp_sub_right (-h)
    have hint3 : Integrable (fun z : R3 => M * ‖A (z + h) - A z‖) volume :=
      ((hAh.sub hA).norm).const_mul M
    have hbnd : ∀ᵐ z ∂(volume : Measure R3),
        ‖((A z) - (A (z + h))).smulRight (g (x₀ + h + z))‖ ≤ M * ‖A (z + h) - A z‖ := by
      filter_upwards with z
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_sub_rev, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hg (x₀ + h + z)) (norm_nonneg _)
    rw [dist_eq_norm, hdiff]
    calc ‖∫ z, ((A z) - (A (z + h))).smulRight (g (x₀ + h + z))‖
        ≤ ∫ z, M * ‖A (z + h) - A z‖ := norm_integral_le_of_norm_le hint3 hbnd
      _ = M * ∫ z, ‖A (z + h) - A z‖ := integral_const_mul M _
  have hbound : ∀ x x₀ : R3,
      dist (∫ z, (A z).smulRight (g (x + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
        ≤ M * ∫ z, ‖A (z + (x - x₀)) - A z‖ := by
    intro x x₀
    have h := hkey x₀ (x - x₀)
    rwa [show x₀ + (x - x₀) = x from by abel] at h
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hJ : Tendsto (fun h : R3 => M * ∫ z, ‖A (z + h) - A z‖) (𝓝 0) (𝓝 0) := by
    have h1 := htrans.const_mul M
    simpa using h1
  have hJnn : ∀ h : R3, 0 ≤ M * ∫ z, ‖A (z + h) - A z‖ := fun h =>
    mul_nonneg hM (integral_nonneg (fun z => norm_nonneg _))
  have hball : ∀ᶠ h : R3 in 𝓝 (0 : R3), M * ∫ z, ‖A (z + h) - A z‖ < ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hJ) ε hε] with h hh
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hJnn h)] at hh
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hball
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have hyball : y - x₀ ∈ Metric.ball (0 : R3) δ := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hy
  calc dist (∫ z, (A z).smulRight (g (y + z))) (∫ z, (A z).smulRight (g (x₀ + z)))
      ≤ M * ∫ z, ‖A (z + (y - x₀)) - A z‖ := hbound y x₀
    _ < ε := hδ hyball

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.VortVV.fderiv_div_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

theorem fderiv_div_apply (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x v : Work.FTS.BSSwirl.R3) :
    fderiv ℝ (FiniteTimeSingularity.div Ψ) x v
      = (fderiv ℝ (fderiv ℝ Ψ) x v).trace ℝ Work.FTS.BSSwirl.R3 := by
  -- `div Ψ = divTrCLM ∘ fderiv ℝ Ψ`, definitionally (trace as a continuous linear
  -- functional of the derivative).
  have hdiv : FiniteTimeSingularity.div Ψ
      = fun y => Work.FTS.BSSwirl.divTrCLM (fderiv ℝ Ψ y) := by
    funext y
    rfl
  rw [hdiv]
  -- `fderiv ℝ Ψ` is `C¹` because `Ψ` is `C²`; hence it is differentiable at `x` with
  -- derivative `fderiv ℝ (fderiv ℝ Ψ) x`, and the chain rule applies to `divTrCLM`.
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    (((hΨ 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hder : HasFDerivAt (fun y => Work.FTS.BSSwirl.divTrCLM (fderiv ℝ Ψ y))
      (Work.FTS.BSSwirl.divTrCLM.comp (fderiv ℝ (fderiv ℝ Ψ) x)) x :=
    Work.FTS.BSSwirl.divTrCLM.hasFDerivAt.comp x hd.hasFDerivAt
  rw [hder.fderiv, ContinuousLinearMap.comp_apply]
  exact Work.FTS.BSSwirl.divTrCLM_apply _

end Work.FTS.BSSwirl.VortVV
end
-- ===== merged: Submission.Work.FTS.BSSwirl.VortVV.fderiv_vorticity_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

open FiniteTimeSingularity

/-- **The derivative of the vorticity (curl) operator.**

Mathematics: the curl `∇ × Ψ` of a field `Ψ : ℝ³ → ℝ³` is the *linear* differential operator
`∑ i, eᵢ × ∂ᵢΨ`.  Its Fréchet derivative at `x` in the direction `v` is obtained by
differentiating under the sum and commuting `∂ᵢ` with the derivative, giving
`v ↦ ∑ i, eᵢ × (D²Ψ(x)[v, eᵢ])`.

Formalisation: `vorticity Ψ x = ∑ i, crossR3 (e i) (fderiv ℝ Ψ x (e i))`
(`vorticity_eq_sum_crossR3`).  Each summand is the continuous linear map `crossBilin (e i)`
applied to the evaluation `y ↦ fderiv ℝ Ψ y (e i)`, whose derivative is
`(fderiv ℝ (fderiv ℝ Ψ) x).flip (e i)` by `HasFDerivAt.clm_apply` (the second factor being the
constant `e i`); `flip` is then eliminated with `ContinuousLinearMap.flip_apply`.  Smoothness of
`fderiv ℝ Ψ` (so that its Fréchet derivative exists) comes from `ContDiff.fderiv_right` applied
to `hΨ 2`. -/
theorem fderiv_vorticity_apply (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (x v : Work.FTS.BSSwirl.R3) :
    fderiv ℝ (FiniteTimeSingularity.vorticity Ψ) x v
      = ∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e i)
          (fderiv ℝ (fderiv ℝ Ψ) x v (FiniteTimeSingularity.e i)) := by
  -- `Ψ` is `C^∞`, hence `fderiv ℝ Ψ` is `C^1`, hence differentiable everywhere.
  have hdiff : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    have h1 : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ Ψ) :=
      ContDiff.fderiv_right (hΨ 2) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    (h1.differentiable (by norm_num)).differentiableAt
  -- The derivative of each summand of the coordinate expression of the curl.
  have key : ∀ i : Fin 3,
      HasFDerivAt (fun y => crossR3 (e i) (fderiv ℝ Ψ y (e i)))
        ((crossBilin (e i)).comp ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i))) x := by
    intro i
    have hc : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) x) x := hdiff.hasFDerivAt
    have hu : HasFDerivAt (fun _ : R3 => e i) (0 : R3 →L[ℝ] R3) x := hasFDerivAt_const _ _
    have h2 : HasFDerivAt (fun y => (fderiv ℝ Ψ y) (e i))
        ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i)) x := by
      simpa using hc.clm_apply hu
    exact (crossBilin (e i)).hasFDerivAt.comp x h2
  -- Differentiate the finite sum.
  have hsum : HasFDerivAt (fun y => ∑ i : Fin 3, crossR3 (e i) (fderiv ℝ Ψ y (e i)))
      (∑ i : Fin 3, (crossBilin (e i)).comp ((fderiv ℝ (fderiv ℝ Ψ) x).flip (e i))) x :=
    HasFDerivAt.fun_sum fun i _ => key i
  -- The curl is that sum, pointwise.
  have hvort : vorticity Ψ = fun y => ∑ i : Fin 3, crossR3 (e i) (fderiv ℝ Ψ y (e i)) := by
    funext y; exact vorticity_eq_sum_crossR3 Ψ y
  rw [hvort, hsum.fderiv, sum_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, crossBilin_apply]

end Work.FTS.BSSwirl.VortVV
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_vorticity_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 2000000

open FiniteTimeSingularity MeasureTheory
open scoped Matrix Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The pointwise Weyl identity for the curl.**  For fields `V, Ψ` differentiable at `x`,

  `⟪∇×V x, Ψ x⟫ - ⟪V x, ∇×Ψ x⟫ = div (V × Ψ) x`.

Concretely, `∇×V = ∑ i, eᵢ × ∂ᵢV` and `div (V × Ψ) = ∑ i, ⟪eᵢ, ∂ᵢV × Ψ + V × ∂ᵢΨ⟫`, and the
scalar triple product identity identifies the two sums term by term. -/
theorem inner_vorticity_sub_eq_div {V Ψ : R3 → R3} {x : R3}
    (hV : DifferentiableAt ℝ V x) (hΨ : DifferentiableAt ℝ Ψ x) :
    inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x)
      = div (fun y => crossR3 (V y) (Ψ y)) x := by
  have hFD := hasFDerivAt_crossR3 hV.hasFDerivAt hΨ.hasFDerivAt
  have hsum : ∀ i : Fin 3,
      inner ℝ (crossR3 (e i) (fderiv ℝ V x (e i))) (Ψ x)
          - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
        = inner ℝ (e i) (((crossBilin.flip (Ψ x)).comp (fderiv ℝ V x)
            + (crossBilin (V x)).comp (fderiv ℝ Ψ x)) (e i)) := by
    intro i
    have h1 : inner ℝ (crossR3 (e i) (fderiv ℝ V x (e i))) (Ψ x)
        = inner ℝ (e i) (crossR3 (fderiv ℝ V x (e i)) (Ψ x)) :=
      inner_crossR3_cyclic₁ _ _ _
    have h2 : - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
        = inner ℝ (e i) (crossR3 (V x) (fderiv ℝ Ψ x (e i))) := by
      have hA : - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
          = inner ℝ (V x) (crossR3 (fderiv ℝ Ψ x (e i)) (e i)) := by
        simp only [← inner_neg_right, neg_crossR3]
      have hB : inner ℝ (e i) (crossR3 (V x) (fderiv ℝ Ψ x (e i)))
          = inner ℝ (V x) (crossR3 (fderiv ℝ Ψ x (e i)) (e i)) :=
        inner_crossR3_cyclic₂ _ _ _
      rw [hA, hB]
    rw [sub_eq_add_neg, h1, h2, ← inner_add_right]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, crossBilin_apply]
  simp only [div_eq_sum_inner, vorticity_eq_sum_crossR3, hFD.fderiv]
  rw [sum_inner, inner_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hsum i

theorem integral_vorticity_eq {V : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hV : ContDiff ℝ 1 V)
    {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ∫ x, inner ℝ (FiniteTimeSingularity.vorticity V x) (Ψ x)
      = ∫ x, inner ℝ (V x) (FiniteTimeSingularity.vorticity Ψ x) := by
  obtain ⟨hVd, hΨd⟩ : Differentiable ℝ V ∧ Differentiable ℝ Ψ :=
    ⟨hV.differentiable one_ne_zero, (hΨ 1).differentiable one_ne_zero⟩
  -- the field `G = V × Ψ` is `C¹` with compact support
  have hGc1 : ContDiff ℝ 1 (fun y => crossR3 (V y) (Ψ y)) := contDiff_crossR3 hV (hΨ 1)
  have hGcs : HasCompactSupport (fun y => crossR3 (V y) (Ψ y)) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  have hdiv0 : ∫ x, div (fun y => crossR3 (V y) (Ψ y)) x = 0 :=
    integral_div_eq_zero_compact hGc1 hGcs
  -- the pointwise identity
  have hpt : ∀ x, inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x)
      = div (fun y => crossR3 (V y) (Ψ y)) x :=
    fun x => inner_vorticity_sub_eq_div (hVd x) (hΨd x)
  -- the curl of `Ψ` is compactly supported
  have hvort_cs : HasCompactSupport (vorticity Ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    refine hx ?_
    have h0 : Ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport Ψ).isOpen_compl.mem_nhds hcon] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hd : fderiv ℝ Ψ x = 0 := by rw [h0.fderiv_eq]; simp
    rw [vorticity_eq_sum_crossR3]
    simp [hd]
  -- integrability of both sides
  have hint1 : Integrable (fun x => inner ℝ (vorticity V x) (Ψ x)) :=
    (continuous_inner.comp ((continuous_vorticity hV).prodMk
      (hΨ 0).continuous)).integrable_of_hasCompactSupport (by
        refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
        intro x hx
        rw [Function.mem_support] at hx
        exact subset_tsupport _ (by
          rw [Function.mem_support]
          intro h0
          exact hx (by simp [h0])))
  have hint2 : Integrable (fun x => inner ℝ (V x) (vorticity Ψ x)) :=
    (continuous_inner.comp (hV.continuous.prodMk
      (continuous_vorticity (hΨ 1)))).integrable_of_hasCompactSupport (by
        refine HasCompactSupport.of_support_subset_isCompact hvort_cs ?_
        intro x hx
        rw [Function.mem_support] at hx
        exact subset_tsupport _ (by
          rw [Function.mem_support]
          intro h0
          exact hx (by simp [h0])))
  have hzero : (∫ x, (inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x))) = 0 := by
    rw [show (fun x => inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x))
        = fun x => div (fun y => crossR3 (V y) (Ψ y)) x from funext hpt]
    exact hdiv0
  rw [integral_sub hint1 hint2] at hzero
  linarith

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.potDeriv_eq_integral_potKerBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

theorem potDeriv_eq_integral_potKerBall {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R ρ : ℝ} {x : Work.FTS.BSSwirl.R3}
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hρ : R + ‖x‖ + 1 ≤ ρ) :
    Work.FTS.BSSwirl.potDeriv ω x = (4 * Real.pi)⁻¹ •
      ∫ z, (Work.FTS.BSSwirl.potKerBall ρ z).smulRight (ω (x + z)) := by
  rw [Work.FTS.BSSwirl.potDeriv]
  congr 1
  -- Step 1: rewrite the integrand of `potDeriv` as `potKer (y-x)` applied to `ω y`, and change
  -- variables `z = y - x`.
  have h1 : (∫ y : R3, (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y))
      = ∫ z : R3, (potKer z).smulRight (ω (x + z)) := by
    have hcongr : ∀ y : R3,
        (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y)
          = (potKer (y - x)).smulRight (ω (x + (y - x))) := by
      intro y
      rw [show x + (y - x) = y by abel, norm_sub_rev, potKer_smulRight]
    have hcongr' : (∫ y : R3, (‖x - y‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ (y - x)).smulRight (ω y))
        = ∫ y : R3, (potKer (y - x)).smulRight (ω (x + (y - x))) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr)
    rw [hcongr']
    exact MeasureTheory.integral_sub_right_eq_self
      (fun z => (potKer z).smulRight (ω (x + z))) x
  -- Step 2: the cut-off kernel agrees with the singular one on the support of `z ↦ ω (x+z)`.
  have h2 : (∫ z : R3, (potKer z).smulRight (ω (x + z)))
      = ∫ z : R3, (potKerBall ρ z).smulRight (ω (x + z)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : ω (x + z) = 0
    · simp only [hz, ContinuousLinearMap.smulRight_zero]
    · have hmem : x + z ∈ Metric.closedBall (0 : R3) R := hsupp (x + z) hz
      have hle : ‖x + z‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      have hlt : ‖z‖ < ρ := by
        have hle' : ‖z‖ ≤ ‖x + z‖ + ‖x‖ := by
          have h := norm_sub_le (x + z) x
          rwa [show (x + z) - x = z by abel] at h
        linarith
      have hzball : z ∈ Metric.ball (0 : R3) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hlt
      rw [potKerBall_apply_of_mem hzball]
  rw [h1]
  exact h2

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

open Work.FTS.EllExist (rgK rgP rgQ rgA rgB rgG1 rgG2)

/-- `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_abs_add_aux (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

theorem radGreen_far_pointwise_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ C / z
      ∧ |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z| ≤ C / z := by
  obtain ⟨CA, hCA0, hAb⟩ := Work.FTS.ClassC.rgA_growth hα hα4 m hcont hdec h0
  obtain ⟨C2, hC20, hBb⟩ := Work.FTS.ClassC.rgB_far_bound hα hα4 m hdec hinf
  have hKpos : 0 < rgK α m := Work.FTS.EllExist.rgK_pos hα m
  have hK0 : 0 ≤ rgK α m := hKpos.le
  have hq0 : 0 ≤ rgQ α m := (Work.FTS.EllExist.rgQ_pos hα m).le
  have hp0 : 0 ≤ rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- ## the two branches in `C/z` form
  have hG1le : ∀ z : ℝ, 1 ≤ z → |rgG1 α m c z| ≤ CA / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hcomb : z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1) = z ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    simp only [Work.FTS.EllExist.rgG1]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    calc z ^ (-(rgQ α m)) * |rgA α m c z|
        ≤ z ^ (-(rgQ α m)) * (CA * z ^ (rgQ α m - 1)) :=
          mul_le_mul_of_nonneg_left (hAb z hz1) (Real.rpow_nonneg hz0.le _)
      _ = CA * (z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1)) := by ring
      _ = CA / z := by rw [hcomb, Real.rpow_neg_one, div_eq_mul_inv]
  have hG2le : ∀ z : ℝ, 1 ≤ z → |rgG2 α m c z| ≤ C2 / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    simp only [Work.FTS.EllExist.rgG2]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    exact hBb z hz1
  -- ## the pointwise bounds for `radGreen` and `z·∂_z radGreen`
  have hBnd_rad : ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ (rgK α m * (CA + C2)) / z := by
    intro z hz1
    rw [Work.FTS.ClassC.radGreen_eq_rgG α m c z, abs_mul, abs_of_nonneg hK0]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ ≤ rgK α m * (CA / z + C2 / z) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hG1le z hz1) (hG2le z hz1)) hK0
      _ = (rgK α m * (CA + C2)) / z := by ring
  have hBnd_zd : ∀ z : ℝ, 1 ≤ z →
      |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hd := Work.FTS.ClassC.radGreen_deriv1_form hα m hcont h0 hinf z hz0
    rw [hd, abs_mul, abs_of_nonneg hK0]
    have e1 : |rgP α m * rgG2 α m c z| = rgP α m * |rgG2 α m c z| := by
      rw [abs_mul, abs_of_nonneg hp0]
    have e2 : |rgQ α m * rgG1 α m c z| = rgQ α m * |rgG1 α m c z| := by
      rw [abs_mul, abs_of_nonneg hq0]
    calc rgK α m * |rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z|
        ≤ rgK α m * (|rgP α m * rgG2 α m c z| + |rgQ α m * rgG1 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_abs_add_aux _ _) hK0
      _ = rgK α m * (rgP α m * |rgG2 α m c z| + rgQ α m * |rgG1 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (rgP α m * (C2 / z) + rgQ α m * (CA / z)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hG2le z hz1) hp0)
              (mul_le_mul_of_nonneg_left (hG1le z hz1) hq0)) hK0
      _ = (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by ring
  -- ## assembly with the maximum of the two constants
  refine ⟨max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)),
    le_trans (mul_nonneg hK0 (by linarith)) (le_max_left _ _), fun z hz1 => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
  refine ⟨?_, ?_⟩
  · calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ (rgK α m * (CA + C2)) / z := hBnd_rad z hz1
      _ ≤ max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z :=
          div_le_div_of_nonneg_right (le_max_left _ _) hz0.le
  · calc |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := hBnd_zd z hz1
      _ ≤ max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z :=
          div_le_div_of_nonneg_right (le_max_right _ _) hz0.le

end Work.FTS.ClassC.HonestCut
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.EllExist
open Work.FTS.ClassC

namespace Work.FTS.ClassC.HonestCut

theorem radGreen_near_pointwise_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∃ B d : ℝ, 0 ≤ B ∧ 3 / 2 < d ∧ ∀ z : ℝ, 0 < z → z ≤ 1 →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ B * z ^ d
      ∧ |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z| ≤ B * z ^ d := by
  obtain ⟨Kc, pc, hKc, hpc32, hvy⟩ := hvy
  have hpc : 0 < pc := by linarith
  have hqpos : 0 < rgQ α m := rgQ_pos hα m
  have hKpos : 0 < rgK α m := rgK_pos hα m
  have hppos : 0 < rgP α m := rgP_pos hα hm
  have hpnn : 0 ≤ rgP α m := hppos.le
  -- integrability of the tail kernel on all of `(0,∞)`, from `(0,1)` and `(1,∞)`
  have h2 : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) := by
    have hnear : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioo 0 1) := h0'
    have hfar : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 1) := hinf
    have hsing : MeasureTheory.IntegrableOn (rgF2 α m c) ({1} : Set ℝ) :=
      MeasureTheory.integrableOn_singleton (f := rgF2 α m c) (x := 1)
        (by finiteness) (by rw [measure_singleton]; exact ENNReal.zero_lt_top)
    have hIoc : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1) := by
      rw [← Set.Ioo_union_right (show (0 : ℝ) < 1 by norm_num)]
      exact hnear.union hsing
    have h := hIoc.union hfar
    rwa [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 from by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · linarith
      · intro hx
        by_cases h : x ≤ 1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (lt_of_not_ge h)] at h
  -- the three constants of the estimate
  set Cf : ℝ := ∫ t in Set.Ioi 0, ‖rgF2 α m c t‖ with hCfdef
  set c1 : ℝ := Kc / (pc + rgQ α m) with hc1def
  set d : ℝ := min pc (rgP α m) with hddef
  set A : ℝ := rgK α m * (rgP α m * Cf + rgQ α m * c1) with hAdef
  set B0 : ℝ := rgK α m * (c1 + Cf) with hB0def
  have hc1nn : 0 ≤ c1 := by
    rw [hc1def]
    exact div_nonneg hKc.le (add_nonneg hpc.le hqpos.le)
  have hCfnn : 0 ≤ Cf := by
    rw [hCfdef]
    exact integral_nonneg fun t => norm_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hKpos.le (add_nonneg (mul_nonneg hpnn hCfnn) (mul_nonneg hqpos.le hc1nn))
  have hB0nn : 0 ≤ B0 := by
    rw [hB0def]
    exact mul_nonneg hKpos.le (add_nonneg hc1nn hCfnn)
  have hd32 : (3 : ℝ) / 2 < d := by
    rw [hddef]
    exact lt_min hpc32 (by linarith [rgP_ge hα hα4 hm])
  have hdpc : d ≤ pc := by rw [hddef]; exact min_le_left _ _
  have hdp : d ≤ rgP α m := by rw [hddef]; exact min_le_right _ _
  -- the two branch bounds
  have hbd1 : ∀ z : ℝ, 0 < z → z ≤ 1 →
      |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) :=
    rgG1_near_bound hα hKc hpc hvy
  have hbd2 : ∀ z : ℝ, 0 < z →
      |rgG2 α m c z| ≤ (∫ t in Set.Ioi 0, ‖rgF2 α m c t‖) * z ^ (rgP α m) :=
    rgG2_near_bound h2
  have hG1 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG1 α m c z| ≤ c1 * z ^ d := by
    intro z hz0 hz1
    have hpcδ : z ^ pc ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdpc
    calc |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) := hbd1 z hz0 hz1
      _ = c1 * z ^ pc := by rw [hc1def]; ring_nf
      _ ≤ c1 * z ^ d := mul_le_mul_of_nonneg_left hpcδ hc1nn
  have hG2 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG2 α m c z| ≤ Cf * z ^ d := by
    intro z hz0 hz1
    have hpδ : z ^ (rgP α m) ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdp
    have h1 : |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := by
      have hp := hbd2 z hz0
      rwa [← hCfdef] at hp
    calc |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := h1
      _ ≤ Cf * z ^ d := mul_le_mul_of_nonneg_left hpδ hCfnn
  -- `radGreen` is `rgK (g₁ + g₂)` and hence `O(z^d)`
  have hgeq : ∀ z : ℝ, radGreen α m c z = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
    intro z
    rw [radGreen_eq]
    simp only [rgG1, rgG2]
  have hG : ∀ z : ℝ, 0 < z → z ≤ 1 → ‖radGreen α m c z‖ ≤ B0 * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    rw [Real.norm_eq_abs, hgeq z, abs_mul, abs_of_pos hKpos]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
      _ ≤ rgK α m * (c1 * z ^ d + Cf * z ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2') hKpos.le
      _ = B0 * z ^ d := by rw [hB0def]; ring
  -- and the combination `rgK (p g₂ - q g₁)` occurring in the derivative is `O(z^d)` too
  have hT : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)‖ ≤ A * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    have h2n : ‖rgG2 α m c z‖ ≤ Cf * z ^ d := by rw [Real.norm_eq_abs]; exact h2'
    have h1n : ‖rgG1 α m c z‖ ≤ c1 * z ^ d := by rw [Real.norm_eq_abs]; exact h1
    rw [norm_mul, Real.norm_of_nonneg hKpos.le]
    calc rgK α m * ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
        ≤ rgK α m * (rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d)) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          calc ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
              = ‖rgP α m * rgG2 α m c z + -(rgQ α m * rgG1 α m c z)‖ := by
                rw [sub_eq_add_neg]
            _ ≤ ‖rgP α m * rgG2 α m c z‖ + ‖-(rgQ α m * rgG1 α m c z)‖ := norm_add_le _ _
            _ = rgP α m * ‖rgG2 α m c z‖ + rgQ α m * ‖rgG1 α m c z‖ := by
                simp only [norm_neg, norm_mul, Real.norm_of_nonneg hpnn,
                  Real.norm_of_nonneg hqpos.le]
            _ ≤ rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d) :=
                add_le_add (mul_le_mul_of_nonneg_left h2n hpnn)
                  (mul_le_mul_of_nonneg_left h1n hqpos.le)
      _ = A * z ^ d := by rw [hAdef]; ring
  refine ⟨max B0 A, d, le_trans hB0nn (le_max_left B0 A), hd32, ?_⟩
  intro z hz0 hz1
  have hzpd : (0 : ℝ) ≤ z ^ d := Real.rpow_nonneg hz0.le d
  constructor
  · have h := hG z hz0 hz1
    rw [Real.norm_eq_abs] at h
    calc |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ B0 * z ^ d := h
      _ ≤ max B0 A * z ^ d := mul_le_mul_of_nonneg_right (le_max_left B0 A) hzpd
  · have h := hT z hz0 hz1
    rw [Real.norm_eq_abs] at h
    have hd1 := radGreen_deriv1_form hα m hcont h0 hinf z hz0
    calc |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z|
        = |z * deriv (radGreen α m c) z| := by rfl
      _ = |rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)| := by rw [hd1]
      _ ≤ A * z ^ d := h
      _ ≤ max B0 A * z ^ d := mul_le_mul_of_nonneg_right (le_max_right B0 A) hzpd

end Work.FTS.ClassC.HonestCut
end
end
-- ===== merged: Submission.Work.FTS.ClassC.UopGenAux.wsq_sKer_log_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.UopGenAux

/-!
### The weighted logarithmic Schur bound for the bump `sKer`

We prove

`∫_{z>0} w(z)² · sKer δ (log z - log y) dz ≤ 5 · w(y)² · y`  (`0 < δ ≤ 1/2`, `y > 0`),

where `w(z) = (1+z)²/z²` and `sKer δ` is the normalised smooth bump of `MollDefs`.

The proof has three ingredients:

* the substitution `z = exp s`, which turns the half-line integral into a convolution
  against `sKer δ` on the logarithmic variable (`MeasureTheory.integral_comp_exp`);
* the pointwise comparison `w(e^s)² e^s ≤ 5 · w(e^t)² e^t` for `|s - t| ≤ 1/2`
  (`EllPkgAux.wExpCmp`, whose numerical content is `e^{3/2} ≤ 5`), combined with
  `sKer δ (s - t) = 0` whenever `δ ≤ |s - t|`;
* the normalisation `∫ sKer δ = 1`.

The constant `5` comes from the pointwise comparison: the kernel has vanishing moments of
order `< 1` only up to the factor `e^{δ}` contributed by the logarithmic Jacobian, and
`e^{3/2} ≤ 5`.
-/

/-- `sKer ε` is continuous. -/
private lemma pk5_sKer_continuous (ε : ℝ) : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have h : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Work.FTS.EllSol.PkgK5.K5c.sBump (t / ε) := by
    funext t; rw [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [h]
  exact continuous_const.mul
    (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp (continuous_id.div_const ε))

/-- `sKer ε` has compact support (contained in `[-ε, ε]`). -/
private lemma pk5_sKer_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

/-- `sKer ε` is integrable for `ε > 0`. -/
private lemma pk5_sKer_integrable {ε : ℝ} (hε : 0 < ε) :
    MeasureTheory.Integrable (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
  (pk5_sKer_continuous ε).integrable_of_hasCompactSupport (pk5_sKer_hasCompactSupport hε)

theorem wsq_sKer_log_integral_le {δ y : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hy : 0 < y) :
    (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))
      ≤ 5 * ((Work.Spaces.w y) ^ 2 * y) := by
  -- integrability of the shifted kernel
  have hker : MeasureTheory.Integrable
      (fun x : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) :=
    (pk5_sKer_integrable hδ).comp_sub_right (Real.log y)
  have hmass : (∫ x : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) = 1 := by
    rw [MeasureTheory.integral_sub_right_eq_self (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log y),
      Work.FTS.EllSol.PkgK5.K5c.sKer_integral_eq_one hδ]
  -- the substitution `z = exp x`
  have hsub : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))
      = ∫ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
          * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)) := by
    rw [← MeasureTheory.integral_comp_exp
      (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - Real.log y))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.log_exp, smul_eq_mul]
  -- the pointwise comparison
  have hpt : ∀ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y))
      ≤ 5 * ((Work.Spaces.w y) ^ 2 * y)
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by
    intro x
    by_cases hx : |x - Real.log y| ≤ 1 / 2
    · have hc := Work.FTS.EllSol.EllPkgAux.wExpCmp x (Real.log y) hx
      rw [Real.exp_log hy] at hc
      have h1 : Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2
          ≤ 5 * ((Work.Spaces.w y) ^ 2 * y) := by
        rw [mul_comm ((Work.Spaces.w (Real.exp x)) ^ 2) (Real.exp x)] at hc
        exact hc
      calc Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
            * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y))
          = (Real.exp x * (Work.Spaces.w (Real.exp x)) ^ 2)
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by ring
        _ ≤ (5 * ((Work.Spaces.w y) ^ 2 * y))
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) :=
            mul_le_mul_of_nonneg_right h1 (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ _)
        _ = 5 * ((Work.Spaces.w y) ^ 2 * y)
              * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by ring
    · -- outside the support of the kernel both sides vanish
      rw [not_le] at hx
      have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) = 0 :=
        Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_trans hδ2 hx.le)
      rw [hz]
      simp
  refine le_trans hsub.le ?_
  have hmain : (∫ x : ℝ, Real.exp x * ((Work.Spaces.w (Real.exp x)) ^ 2
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y)))
      ≤ ∫ x : ℝ, 5 * ((Work.Spaces.w y) ^ 2 * y)
        * Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - Real.log y) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with x
      exact mul_nonneg (Real.exp_pos x).le
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ _))
    · exact hker.const_mul (5 * ((Work.Spaces.w y) ^ 2 * y))
    · filter_upwards with x
      exact hpt x
  refine le_trans hmain ?_
  rw [MeasureTheory.integral_const_mul, hmass]
  exact le_of_eq (by ring)

end Work.FTS.ClassC.UopGenAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thetaPoincare_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Uniform weighted angular Poincaré inequality with vanishing mean.**

The sibling `thetaPoincare` proves the estimate with a constant depending on `f`; the proof
there in fact uses the *same* explicit constant `10000 * (π/2) + 1` for every `f`, so the
quantifier can be exchanged.  We simply repeat that argument with the constant fixed in
advance.

For `f` differentiable on the open interval `(0, π/2)` with derivative `f'`, with `(f')²`
and `f` integrable on `Iθ = [0, π/2]` and vanishing (unweighted) mean over `Iθ`, the
weighted square of `f` against the angular weight `thEta θ = sin(2θ)^{-η}` is controlled
by the *unweighted* `L²`-norm of the derivative, with a constant independent of `f`.

Proof.  By the mean-zero Poincaré sup bound (`Honest.PthCore.mean_zero_sup_bound`) every
interior value obeys `|f θ| ≤ K := ∫_{Iθ} |f'|` (the increment form
`f θ = (π/2)⁻¹ ∫_{Iθ} (f θ - f t) dt` of the vanishing mean together with the fundamental
theorem of calculus on the intervals between `θ` and `t`).  Hence
`thEta θ * (f θ)² ≤ K² * thEta θ` a.e. on `Iθ`, and integrating against the weight
(`∫_{Iθ} thEta ≤ 10⁴`) gives `∫_{Iθ} thEta f² ≤ 10⁴ K²`.  Finally Cauchy–Schwarz on `Iθ`
turns `K = ∫_{Iθ} |f'|` into `K² ≤ (π/2) ∫_{Iθ} (f')²`. -/
theorem thetaPoincare_unif : ∃ C : ℝ, 0 < C ∧ ∀ {f f' : ℝ → ℝ},
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ) →
    MeasureTheory.IntegrableOn (fun θ => (f' θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, f θ) = 0 →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ C * ∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2 := by
  refine ⟨10000 * (Real.pi / 2) + 1, by positivity, ?_⟩
  intro f f' hd hf'int hfint hmean
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hlt : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- interval integrability of `f` on `[0, π/2]`
  have hIf : IntervalIntegrable f volume (0 : ℝ) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hfint
  -- on the open interval the derivative of `f` is `f'`
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv f θ = f' θ :=
    fun θ hθ => (hd θ hθ).deriv
  have haeeq : deriv f =ᵐ[volume.restrict Work.Spaces.Iθ] f' := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => deriv f θ = f' θ) (fun θ hθ => hderiv θ hθ)
    exact h
  have hvol_lt : volume (Work.Spaces.Iθ) < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable f' (volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv f).aestronglyMeasurable.congr haeeq
  -- `f'` is integrable on `Iθ` (its square is, and `Iθ` has finite measure)
  have hIf' : IntegrableOn f' Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.H2W.integrableOn_of_sq_integrableOn haesm hvol_lt hf'int
  have hIntf' : IntervalIntegrable f' volume (0 : ℝ) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hIf'
  -- the vanishing mean as an interval integral
  have hmeanz : (∫ x in (0 : ℝ)..(Real.pi / 2), f x) = 0 := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hmean
  -- the mean-zero sup bound
  have hsup : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f x| ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), |f' t| :=
    Work.FTS.EllipticEst.Honest.PthCore.mean_zero_sup_bound (a := 0) (b := Real.pi / 2)
      hlt hd hIf hIntf' hmeanz
  set K : ℝ := ∫ t in (0 : ℝ)..(Real.pi / 2), |f' t| with hK
  have hKnn : 0 ≤ K := by
    rw [hK, intervalIntegral.integral_of_le hle]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 ≤ K ^ 2 := by
    intro θ hθ
    have h1 : |f θ| ≤ K := by rw [hK]; exact hsup θ hθ
    calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- the pointwise bound holds a.e. on `Iθ`
  have haept : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2 ≤ Work.FTS.EllipticEst.thEta θ * K ^ 2 := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.thEta θ * K ^ 2)
      (fun θ hθ => mul_le_mul_of_nonneg_left (hpt θ hθ)
        (Work.FTS.EllipticEst.thEta_nonneg (Set.Ioo_subset_Icc_self hθ)))
    exact h
  have hWint : IntegrableOn Work.FTS.EllipticEst.thEta Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hRHSint : IntegrableOn (fun θ => Work.FTS.EllipticEst.thEta θ * K ^ 2) Work.Spaces.Iθ :=
    hWint.mul_const (K ^ 2)
  -- measurability of the weighted integrand
  have hcont : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt
  have hsin_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id)
  have hw_cont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) _
    exact hsin_cont.rpow_const (fun x hx => Or.inl (ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos]))))
  have hg_cont : ContinuousOn (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hw_cont.mul (hcont.pow 2)
  have hres : volume.restrict (Work.Spaces.Iθ)
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm
  have hAESM : AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [hres]
    exact hg_cont.aestronglyMeasurable measurableSet_Ioo
  have hLHSint : IntegrableOn (fun θ => Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      Work.Spaces.Iθ := by
    refine hRHSint.mono' hAESM ?_
    filter_upwards [haept, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ hmem
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hmem) (sq_nonneg _))]
    exact hθ
  have hmono : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * K ^ 2 :=
    MeasureTheory.integral_mono_ae hLHSint hRHSint haept
  have hval : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * K ^ 2)
      = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ) * K ^ 2 :=
    MeasureTheory.integral_mul_const (K ^ 2) _
  have hbound1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ 10000 * K ^ 2 := by
    have h1 := hmono
    rw [hval] at h1
    exact h1.trans
      (mul_le_mul_of_nonneg_right Work.FTS.EllipticEst.integrableOn_thEta.2 (sq_nonneg K))
  -- Cauchy–Schwarz: `K² ≤ (π/2) ∫ (f')²`
  have hvol : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul,
      mul_one, sub_zero]
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
    haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr hvol_lt.ne
    exact MeasureTheory.memLp_const (1 : ℝ)
  have hmemabs : MemLp (fun θ : ℝ => |f' θ|) 2 (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ : ℝ => |f' θ|) (by simpa only [Real.norm_eq_abs] using haesm.norm)]
    have h2 : Integrable (fun θ : ℝ => (|f' θ|) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
      rw [show (fun θ : ℝ => (|f' θ|) ^ 2) = (fun θ : ℝ => (f' θ) ^ 2)
        from funext (fun θ => sq_abs (f' θ))]
      exact hf'int
    exact h2
  have hKabs : K = ∫ θ in Work.Spaces.Iθ, |f' θ| := by
    rw [hK, intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  have hcs : K ^ 2 ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) := by
    have h := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) (u := fun _ : ℝ => (1 : ℝ))
      (v := fun θ : ℝ => |f' θ|) hmem1 hmemabs
    simp only [one_mul, one_pow, sq_abs] at h
    rw [hvol] at h
    rw [← hKabs] at h
    exact h
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (f θ) ^ 2)
      ≤ 10000 * K ^ 2 := hbound1
    _ ≤ 10000 * ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = (10000 * (Real.pi / 2)) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) := by ring
    _ ≤ (10000 * (Real.pi / 2) + 1) * (∫ θ in Work.Spaces.Iθ, (f' θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hBnn

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.sKer_conv_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c


/-- `sKer δ` is supported in `[-δ, δ]`, hence has compact support. -/
private lemma sKer_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun u : ℝ => sKer δ u) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-δ) δ) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < δ := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hδ (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩



end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz.sKerd_eq_zero_of_le_abs`

The first derivative of the normalised bump `sKer ε` vanishes on the *closed* complement of
its support, `{t | ε ≤ |t|}`:

  `deriv (sKer ε) t = 0`  for `0 < ε` and `ε ≤ |t|`.

The strict version `ε < |t|` is immediate from the support containment
(`sKer_eq_zero_of_le_abs` from `MollDefs`, i.e. `sBump` is a genuine bump); at the two
boundary points `t = ±ε` it is *not* an eventual-equality statement, but it follows from
the flatness of `Real.smoothTransition` at `0`, packaged here as:

* `contDiff_two_sKer` — `sKer ε` is `C²`, hence `deriv (sKer ε)` is continuous, and
* `deriv_sKer_eq_zero_of_lt_abs` — the strict-support vanishing.

Indeed `deriv (sKer ε)` is continuous and vanishes on the *dense* subset `{|t| > ε}` of each
of `[ε, ∞)` and `(-∞, -ε]`; a continuous function vanishing on a dense set vanishes
everywhere.  (Equivalently: `{x | deriv (sKer ε) x = 0}` is closed and contains `Ioi ε`,
hence contains `closure (Ioi ε) = Ici ε`.)
-/

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz

open scoped Real Topology
open MeasureTheory Set Filter

/-- `sKer ε = (ε * sMass)⁻¹ • sBump (· / ε)` is smooth; in particular it is `C²`. -/
theorem contDiff_two_sKer (ε : ℝ) :
    ContDiff ℝ (2 : ℕ∞) (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have hinner : ContDiff ℝ (2 : ℕ∞) (fun t : ℝ => 1 - (t / ε) ^ 2) :=
    contDiff_const.sub ((contDiff_id.div_const ε).pow 2)
  have hcomp : ContDiff ℝ (2 : ℕ∞) (fun t : ℝ => Real.smoothTransition (1 - (t / ε) ^ 2)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp hinner
  have hmul : ContDiff ℝ (2 : ℕ∞)
      (fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
        * Real.smoothTransition (1 - (t / ε) ^ 2)) := contDiff_const.mul hcomp
  have hfun : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Real.smoothTransition (1 - (t / ε) ^ 2) := rfl
  rw [hfun]
  exact hmul

/-- The derivative of `sKer ε` is continuous. -/
theorem continuous_deriv_sKer (ε : ℝ) :
    Continuous (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) :=
  (contDiff_two_sKer ε).continuous_deriv (by norm_num)

/-- The first derivative of the bump vanishes off its support (strict version). -/
theorem deriv_sKer_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (h : ε < |t|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    rcases lt_or_ge (0 : ℝ) t with hpos | hnonpos
    · have htε : ε < t := by rwa [abs_of_pos hpos] at h
      filter_upwards [isOpen_Ioi.mem_nhds htε] with u hu
      have hu' : ε ≤ |u| := by
        rw [abs_of_pos (lt_trans hε hu)]
        exact le_of_lt hu
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hu'
    · have htε : t < -ε := by
        rw [abs_of_nonpos hnonpos] at h; linarith
      filter_upwards [isOpen_Iio.mem_nhds htε] with u hu
      have hu2 : u < -ε := hu
      have hu0 : u < 0 := by linarith
      have hu' : ε ≤ |u| := by
        rw [abs_of_neg hu0]; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hu'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

theorem sKerd_eq_zero_of_le_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ |t|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) t = 0 := by
  have hclosed : IsClosed {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
    isClosed_eq (continuous_deriv_sKer ε) continuous_const
  rcases lt_or_eq_of_le ht with h | h
  · exact deriv_sKer_eq_zero_of_lt_abs hε h
  · rcases lt_or_ge t (0 : ℝ) with ht0 | ht0
    · -- `t = -ε`: the derivative vanishes on `Iio (-ε)`
      have htε : t = -ε := by rw [abs_of_neg ht0] at h; linarith
      rw [htε]
      have hsub : Set.Iio (-ε) ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} := by
        intro u hu
        have hu2 : u < -ε := hu
        exact deriv_sKer_eq_zero_of_lt_abs hε (by
          have hu0 : u < 0 := by linarith
          rw [abs_of_neg hu0]
          linarith)
      have hsub' : closure (Set.Iio (-ε))
          ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
        hclosed.closure_subset_iff.mpr hsub
      have hmem : (-ε) ∈ closure (Set.Iio (-ε)) := by
        rw [closure_Iio]
        exact Set.mem_Iic.mpr le_rfl
      exact hsub' hmem
    · -- `t = ε`: the derivative vanishes on `Ioi ε`, whose closure contains `ε`
      have htε : t = ε := by rw [abs_of_nonneg ht0] at h; exact h.symm
      rw [htε]
      have hsub : Set.Ioi ε ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} := by
        intro u hu
        exact deriv_sKer_eq_zero_of_lt_abs hε (by
          rw [abs_of_pos (lt_trans hε hu)]
          exact hu)
      have hsub' : closure (Set.Ioi ε)
          ⊆ {x : ℝ | deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0} :=
        hclosed.closure_subset_iff.mpr hsub
      have hmem : ε ∈ closure (Set.Ioi ε) := by
        rw [closure_Ioi]
        exact Set.mem_Ici.mpr le_rfl
      exact hsub' hmem

end Work.FTS.EllSol.PkgK5.i0TraceMoll.AuxDz
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.WindowBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.Trunc

set_option autoImplicit false

/-! ## The strip and the angular weight -/

/-- The open strip `ℝ × (0,π/2)` on which the hypotheses of `window_mass_le` live. -/
def Strip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- `g` is `C²` on the open strip `ℝ × (0,π/2)`. -/
def StripC2 (g : ℝ → ℝ → ℝ) : Prop := ContDiffOn ℝ 2 (Function.uncurry g) Strip

theorem isOpen_Strip : IsOpen Strip := isOpen_univ.prod isOpen_Ioo

/-- The angular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`) of the zero-th slot. -/
def Sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))






/-! ## `z`-slices -/

/-- The `z`-slice of a `C²` function on the strip has derivative `pz g z θ`. -/
theorem hasDerivAt_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (z : ℝ) :
    HasDerivAt (fun z' => g z' θ) (Work.Spaces.pz g z θ) z := by
  have hmem : (z, θ) ∈ Strip := ⟨trivial, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    ((hg.differentiableOn (by norm_num)).differentiableAt (isOpen_Strip.mem_nhds hmem))
  have h1 : HasDerivAt (fun z' => Function.uncurry g (z', θ))
      ((fderiv ℝ (Function.uncurry g) (z, θ)) (1, 0)) z :=
    Work.Spaces.hasDerivAt_slice_fst hd.hasFDerivAt
  have h2 : (fderiv ℝ (Function.uncurry g) (z, θ)) (1, 0) = Work.Spaces.pz g z θ :=
    (Work.Spaces.pz_eq_fderiv hd).symm
  rw [h2] at h1
  simpa [Function.uncurry] using h1

/-- The `z`-slice of a `C²` function on the strip is `C²` on `ℝ`. -/
theorem contDiffOn_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffOn ℝ 2 (fun z => g z θ) Set.univ := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) Set.univ Strip := fun _ _ => ⟨trivial, hθ⟩
  have h := hg.comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ))) hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The `z`-slice of a `C²` function on the strip is continuous. -/
theorem continuous_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Continuous (fun z => g z θ) :=
  continuousOn_univ.mp (contDiffOn_zslice hg hθ).continuousOn

/-- The `z`-slice of `pz g` is continuous. -/
theorem continuous_pz_zslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Continuous (fun z => Work.Spaces.pz g z θ) := by
  have hcd := contDiffOn_zslice hg hθ
  have h1 : ContinuousOn (derivWithin (fun z => g z θ) Set.univ) Set.univ :=
    hcd.continuousOn_derivWithin uniqueDiffOn_univ (by norm_num)
  rw [derivWithin_univ, continuousOn_univ] at h1
  have h2 : deriv (fun z => g z θ) = fun z => Work.Spaces.pz g z θ := by
    funext z
    exact (hasDerivAt_zslice hg hθ z).deriv
  rwa [← h2]


/-! ## `θ`-slices -/


/-- The `θ`-slice of a `C²` function on the strip has derivative `pth g t θ`. -/
theorem hasDerivAt_thslice {g : ℝ → ℝ → ℝ} (hg : StripC2 g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (t : ℝ) :
    HasDerivAt (fun θ' => g t θ') (Work.Spaces.pth g t θ) θ := by
  have hmem : (t, θ) ∈ Strip := ⟨trivial, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (t, θ) :=
    ((hg.differentiableOn (by norm_num)).differentiableAt (isOpen_Strip.mem_nhds hmem))
  have h1 : HasDerivAt (fun θ' => Function.uncurry g (t, θ'))
      ((fderiv ℝ (Function.uncurry g) (t, θ)) (0, 1)) θ :=
    Work.Spaces.hasDerivAt_slice_snd hd.hasFDerivAt
  have h2 : (fderiv ℝ (Function.uncurry g) (t, θ)) (0, 1) = Work.Spaces.pth g t θ :=
    (Work.Spaces.pth_eq_fderiv hd).symm
  rw [h2] at h1
  simpa [Function.uncurry] using h1





end Work.FTS.EllSol.Trunc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeakFts

open Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## Auxiliary lemmas -/

/-- A function which is dominated on the *open* interval `(0, π/2)` by `C · sin(2θ)^p`, with
`p > -1`, is interval integrable on `[0, π/2]`: the majorant is integrable
(`Work.FTS.H2.intervalIntegrable_sin_rpow`) and the two sets differ by a null set. -/
theorem intervalIntegrable_of_sin_bound_Ioo {g : ℝ → ℝ} {C p : ℝ} (hp : -1 < p)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (π / 2))))
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), |g θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    IntervalIntegrable g volume 0 (π / 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hae : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioc (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)
  have hmaj : IntegrableOn (fun θ : ℝ => C * (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (π / 2)) := by
    have h0 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioc 0 (π / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
        (Work.FTS.H2.intervalIntegrable_sin_rpow p hp)
    exact IntegrableOn.congr_set_ae (h0.const_mul C) hae
  have hInt : IntegrableOn g (Set.Ioo 0 (π / 2)) :=
    Integrable.mono' hmaj hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [Real.norm_eq_abs]; exact h θ hθ))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
    (IntegrableOn.congr_set_ae hInt hae.symm)

/-- The four Hardy integrands are a.e. strongly measurable on the open angular interval: each of
them is continuous there (`f` because it is `C²`, `deriv f` because it is `C¹`, and the
`sin(2θ)^{-q}` factors because `sin(2θ) > 0` on the open interval). -/
theorem hardyFtsAesm (η : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (hardyFtsL η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsB η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsG η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsD η f) (volume.restrict (Set.Ioo 0 (π / 2))) := by
  have hsc : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hfc : ContinuousOn f (Set.Ioo 0 (π / 2)) := hf.continuousOn
  have hdc : ContinuousOn (deriv f) (Set.Ioo 0 (π / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ θ ∈ Set.Ioo 0 (π / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (hardyFts_sin_pos hθ)
  have hpw : ∀ q : ℝ, ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ q) (Set.Ioo 0 (π / 2)) :=
    fun q => hsc.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
  have hLc : ContinuousOn (hardyFtsL η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsL
    exact ((hfc.pow 2).mul (hcc.pow 2)).mul (hpw (-(2 + η)))
  have hBc : ContinuousOn (hardyFtsB η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsB
    exact (hfc.pow 2).mul (hpw (-η))
  have hGc : ContinuousOn (hardyFtsG η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsG
    exact ((hdc.mul hfc).mul hcc).mul (hpw (-(1 + η)))
  have hDc : ContinuousOn (hardyFtsD η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsD
    exact (hdc.pow 2).mul (hpw (-η))
  exact ⟨hLc.aestronglyMeasurable measurableSet_Ioo,
    hBc.aestronglyMeasurable measurableSet_Ioo,
    hGc.aestronglyMeasurable measurableSet_Ioo,
    hDc.aestronglyMeasurable measurableSet_Ioo⟩

/-- The pointwise domination of the four Hardy integrands by `M² sin(2θ)^{-η}` on the open
angular interval, from `|f θ| ≤ M sin(2θ)` and `|deriv f θ| ≤ M`. -/
theorem hardyFtsBounds (η : ℝ) {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hMd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |hardyFtsL η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
        |hardyFtsB η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
          |hardyFtsG η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
            |hardyFtsD η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := hs.le
  have hfθ : |f θ| ≤ M * Real.sin (2 * θ) := hMf θ hθ
  have hdθ : |deriv f θ| ≤ M := hMd θ hθ
  have hMs : 0 ≤ M * Real.sin (2 * θ) := mul_nonneg hM hs0
  -- squared bounds for `f` and `deriv f`
  have hf2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
    rw [← sq_abs (f θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hfθ 2
  have hd2 : (deriv f θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs (deriv f θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdθ 2
  have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
  have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  -- the two `rpow` identities on the open interval
  have hpow2 : (Real.sin (2 * θ)) ^ (-η)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [show (-η : ℝ) = (2 : ℝ) + (-(2 + η)) by ring]
    rw [Real.rpow_add hs (2 : ℝ) (-(2 + η)), Real.rpow_two]
  have hpow1 : (Real.sin (2 * θ)) ^ (-η)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η)) := by
    rw [show (-η : ℝ) = (1 : ℝ) + (-(1 + η)) by ring]
    rw [Real.rpow_add hs (1 : ℝ) (-(1 + η)), Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `L = f² cos²(2θ) sin(2θ)^{-(2+η)}`
    have h1 : (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 :=
      mul_le_mul hf2 hcos2 (sq_nonneg _) (sq_nonneg _)
    have h2 : (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(2 + η)) :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0 _)
    rw [hardyFtsL, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
      abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))), abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    calc (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(2 + η)) := h2
      _ = M ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by ring
      _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by rw [hpow2]
  · -- `B = f² sin(2θ)^{-η}`
    have h1 : (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      mul_le_mul_of_nonneg_right hf2 (Real.rpow_nonneg hs0 _)
    have h3 : (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
      have h4 : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          ≤ 1 * (Real.sin (2 * θ)) ^ (-η) :=
        mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hs0 _)
      calc (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          = M ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by ring
        _ ≤ M ^ 2 * (1 * (Real.sin (2 * θ)) ^ (-η)) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg M)
        _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by ring
    rw [hardyFtsB, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    exact le_trans h1 h3
  · -- `G = f' f cos(2θ) sin(2θ)^{-(1+η)}`
    have hab : |deriv f θ| * |f θ| ≤ M * (M * Real.sin (2 * θ)) :=
      mul_le_mul hdθ hfθ (abs_nonneg _) hM
    have habc : |deriv f θ| * |f θ| * |Real.cos (2 * θ)|
        ≤ M * (M * Real.sin (2 * θ)) * 1 :=
      mul_le_mul hab (Real.abs_cos_le_one (2 * θ)) (abs_nonneg _) (mul_nonneg hM hMs)
    have h1 : |deriv f θ| * |f θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η))
        ≤ M * (M * Real.sin (2 * θ)) * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) :=
      mul_le_mul_of_nonneg_right habc (Real.rpow_nonneg hs0 _)
    rw [hardyFtsG, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    calc |deriv f θ| * |f θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η))
        ≤ M * (M * Real.sin (2 * θ)) * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) := h1
      _ = M ^ 2 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))) := by ring
      _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by rw [hpow1]
  · -- `D = (f')² sin(2θ)^{-η}`
    rw [hardyFtsD, abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)),
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    exact mul_le_mul_of_nonneg_right hd2 (Real.rpow_nonneg hs0 _)

/-! ## The target -/

theorem fluxIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ} {M : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hMd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsB η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsD η f) MeasureTheory.volume
        0 (Real.pi / 2) := by
  obtain ⟨hLm, hBm, hGm, hDm⟩ := hardyFtsAesm η hf
  have hb := hardyFtsBounds η hM hMf hMd
  have hp : (-1 : ℝ) < -η := by linarith
  exact ⟨intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hLm
      (fun θ hθ => (hb θ hθ).1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hBm
      (fun θ hθ => (hb θ hθ).2.1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hGm
      (fun θ hθ => (hb θ hθ).2.2.1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hDm
      (fun θ hθ => (hb θ hθ).2.2.2)⟩

end Work.FTS.EllipticEst.AngAWeakFts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.IP_abs_le_of_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-! ## Helper lemmas

`IP g h = ∫_z ∫_θ g z θ * h z θ * w2 z * sig θ` with `w2 z = w z ^ 2` and
`sig θ = sin(2θ)^{-η}`.  The proof of the Cauchy–Schwarz inequality for `IP` is Cauchy–Schwarz
twice: on each angular slice (Hölder with `p = q = 2`, `slice_abs_le_aux`) and then in the
radial variable (`z_sqrt_aux`).  Both steps only need the a.e. strong measurability of the
slice functions: `aesm_slice_of_smoothNbhd` for a `SmoothNbhd` profile and `measurable_sig`
for the angular weight. -/

/-- The angular weight `sig θ = sin(2θ)^{-η}` is measurable. -/
theorem measurable_sig : Measurable sig := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _





/-! ## The main statement -/


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.Lzero_self_form_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Auxiliary

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Two functions which agree on the open interval `(0, π/2)` agree almost everywhere on the
closed interval, since the two endpoints are a null set. -/
private lemma ae_eq_restrict_of_eqOn_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), g θ = h θ) :
    g =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] h := by
  show ∀ᵐ θ ∂(volume.restrict (Icc (0 : ℝ) (π / 2))), g θ = h θ
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [mem_ofPred_eq, not_imp, mem_Icc] at hθ
    obtain ⟨hθs, hne⟩ := hθ
    rcases eq_or_lt_of_le hθs.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hθs.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (hgh θ ⟨h, h2⟩) hne
  · rw [show ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} from by
      ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
    exact measure_union_null (measure_singleton 0) (measure_singleton (π / 2))

/-- The main workhorse: the angular integration by parts for a single function `f`. -/
private lemma Lzero_self_form_aux (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Icc (0 : ℝ) (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    (∫ θ in Icc (0 : ℝ) (π / 2), Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      = (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hlt : (0 : ℝ) < π / 2 := by positivity
  set dW : ℝ → ℝ := derivWithin f (Icc (0 : ℝ) (π / 2)) with hdW
  set ps : ℝ → ℝ := derivWithin dW (Icc (0 : ℝ) (π / 2)) with hps
  set FW : ℝ → ℝ := fun θ => -(dW θ) * f θ + (1 / 2) * Real.tan θ * (f θ) ^ 2 with hFW
  set R0 : ℝ → ℝ := fun θ => (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
    + Real.sin θ * (f θ / Real.cos θ) * dW θ with hR0
  -- continuity of the auxiliary functions
  have hdW_cont : ContinuousOn dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hdW_cd : ContDiffOn ℝ 1 dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hps_cont : ContinuousOn ps (Icc (0 : ℝ) (π / 2)) := by
    rw [hps]
    exact hdW_cd.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hf_cont : ContinuousOn f (Icc (0 : ℝ) (π / 2)) := hs.continuousOn
  -- the pointwise facts relating `deriv f` to `dW`, `deriv (deriv f)` to `ps`
  have hcos_ne : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    have hmem : θ ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
  have hdf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv f θ = dW θ := by
    intro θ hθ
    rw [hdW]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  have hddf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv (deriv f) θ = ps θ := by
    intro θ hθ
    have hev : deriv f =ᶠ[𝓝 θ] dW := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)).symm
    rw [hev.deriv_eq, hps]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  -- the pointwise derivative identity, via the delegated lemma
  have hderiv_FW : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = Work.Elliptic.Lzero (fun _ s => f s) 0 θ * f θ
        - (deriv f θ) ^ 2 - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2 := by
    intro θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hA := hasDerivAt_self_antideriv f θ hθ h2
    have hev : FW =ᶠ[𝓝 θ]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact (hA.congr_of_eventuallyEq hev).deriv
  -- the a.e. identity for `Lzero · f`
  have hA_ae : (fun θ => Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))]
      (fun θ => deriv FW θ + (deriv f θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        - 6 * (f θ) ^ 2) := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hderiv_FW θ hθ]
    ring
  -- the explicit computation of `deriv FW`
  have hFW_deriv : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := hcos_ne θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hfd : HasDerivAt f (dW θ) θ :=
      ((h2.differentiableAt (by norm_num)).hasDerivAt).congr_deriv (hdf θ hθ)
    have hev : dW =ᶠ[𝓝 θ] deriv f := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    have hdW_d : HasDerivAt dW (ps θ) θ :=
      ((((h2.derivWithin (m := 1) (by norm_num)).differentiableAt (n := 1)
        (by norm_num)).hasDerivAt).congr_deriv (hddf θ hθ)).congr_of_eventuallyEq hev
    have h1 : HasDerivAt (fun y => (-(dW y)) * f y)
        ((-(ps θ)) * f θ + (-(dW θ)) * dW θ) θ := hdW_d.neg.mul hfd
    have h2p : HasDerivAt (fun y => (f y) ^ 2) (2 * f θ ^ (2 - 1) * dW θ) θ := hfd.pow 2
    have h3 : HasDerivAt (fun y => Real.tan y * (f y) ^ 2)
        ((1 / Real.cos θ ^ 2) * (f θ) ^ 2 + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ)) θ :=
      (Real.hasDerivAt_tan hcos).mul h2p
    have h4 : HasDerivAt (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))
        ((1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
          + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ))) θ := h3.const_mul (1 / 2)
    have h5 := (h1.add h4).congr_of_eventuallyEq
      (show FW =ᶠ[𝓝 θ] ((fun y => (-(dW y)) * f y)
        + (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))) from by
        filter_upwards with y
        simp only [Pi.add_apply, hFW]
        ring)
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [h5.deriv, h21, pow_one, div_pow]
    ring
  -- the a.e. identity for the derivative of `FW`, in a form with bounded pieces
  have hE_ae : (fun θ => deriv FW θ) =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] R0 := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hFW_deriv θ hθ, hR0]
    change (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ
      = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.sin θ * (f θ / Real.cos θ) * dW θ
    rw [Real.tan_eq_sin_div_cos]
    ring
  -- bounds
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bound_div_cos f hs h1
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hdW_cont
  -- measurability
  have hf_aem : AEMeasurable f (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_cont.aemeasurable measurableSet_Icc
  have hdiv_aem : AEMeasurable (fun θ => f θ / Real.cos θ)
      (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_aem.div Real.measurable_cos.aemeasurable
  have hdW_aem : AEMeasurable dW (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hdW_cont.aemeasurable measurableSet_Icc
  -- integrability of the pieces
  have hD_int : IntegrableOn (fun θ => (f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hf_cont.pow 2).integrableOn_compact isCompact_Icc
  have hC_int : IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb ^ 2) ?_
    · have heq : (fun θ => (f θ / Real.cos θ) ^ 2)
          = (fun θ => f θ / Real.cos θ) * (fun θ => f θ / Real.cos θ) := by
        funext θ; simp only [Pi.mul_apply, sq]
      rw [heq]
      exact (hdiv_aem.mul hdiv_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have h2 : (f θ / Real.cos θ) ^ 2 ≤ Cb ^ 2 := by
        rw [← sq_abs (f θ / Real.cos θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
  have hBsq_int : IntegrableOn (fun θ => (dW θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hdW_cont.pow 2).integrableOn_compact isCompact_Icc
  have hB_int : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    have h := ae_eq_restrict_of_eqOn_Ioo (g := fun θ => deriv f θ) (h := dW)
      (fun θ hθ => hdf θ hθ)
    refine hBsq_int.congr_fun_ae ?_
    filter_upwards [h.symm] with θ hθ
    rw [hθ]
  have hA4_int : IntegrableOn (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
      (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb * M1) ?_
    · have heq : (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
          = (Real.sin * (fun θ => f θ / Real.cos θ)) * dW := by
        funext θ; simp only [Pi.mul_apply]
      rw [heq]
      exact ((Real.continuous_sin.measurable.aemeasurable.mul hdiv_aem).mul
        hdW_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have hy' : |dW θ| ≤ M1 := by simpa only [Real.norm_eq_abs] using hM1 θ hθ
      have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Real.sin θ| * |f θ / Real.cos θ| * |dW θ|
          ≤ 1 * Cb * M1 := by gcongr
        _ = Cb * M1 := by ring
  have hA1_int : IntegrableOn (fun θ => (-(ps θ)) * f θ) (Icc (0 : ℝ) (π / 2)) :=
    ((continuous_neg.comp_continuousOn hps_cont).mul hf_cont).integrableOn_compact
      isCompact_Icc
  have hR0_int : IntegrableOn R0 (Icc (0 : ℝ) (π / 2)) := by
    have hsum := (hA1_int.sub hBsq_int).add
      ((Integrable.const_mul hC_int (1 / 2)).add hA4_int)
    refine hsum.congr_fun_ae ?_
    refine Eventually.of_forall (fun θ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hR0]
    ring
  have hE_int : IntegrableOn (fun θ => deriv FW θ) (Icc (0 : ℝ) (π / 2)) :=
    hR0_int.congr_fun_ae hE_ae.symm
  -- the fundamental theorem of calculus for the antiderivative
  have hFW_cont : ContinuousOn FW (Icc (0 : ℝ) (π / 2)) := by
    rw [hFW, hdW]
    exact continuousOn_antideriv_fts f hs h1
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt FW (deriv FW x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hs.contDiffAt (Icc_mem_nhds hx.1 hx.2)
    have hA := hasDerivAt_self_antideriv f x hx h2
    have hev : FW =ᶠ[𝓝 x]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    have hA' := hA.congr_of_eventuallyEq hev
    rw [hA'.deriv]
    exact hA'
  have hint : IntervalIntegrable (fun θ => deriv FW θ) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr hE_int
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2), deriv FW θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFW_cont hderiv hint, hFW]
    simp only [h0, h1, mul_zero, Real.tan_zero]
    norm_num
  have hFTC' : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hFTC
  -- assemble
  have hF1 : IntegrableOn ((fun θ => deriv FW θ) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hE_int
  have hF2 : IntegrableOn ((fun θ => (deriv f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hB_int
  have hF3 : IntegrableOn ((fun θ => (1 / 2) * (f θ / Real.cos θ) ^ 2) : ℝ → ℝ)
      (Icc (0 : ℝ) (π / 2)) := Integrable.const_mul hC_int (1 / 2)
  have hF4 : IntegrableOn ((fun θ => 6 * (f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) :=
    Integrable.const_mul hD_int 6
  have hF12 := hF1.add hF2
  have hF123 := hF12.add hF3
  have hsp1 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2 - 6 * (f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
          + (1 / 2) * (f θ / Real.cos θ) ^ 2)
        - (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2) :=
    integral_sub hF123 hF4
  have hsp2 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2) :=
    integral_add hF12 hF3
  have hsp3 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2) :=
    integral_add hF1 hF2
  have hsp4 : (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2) :=
    integral_const_mul (1 / 2) (fun θ => (f θ / Real.cos θ) ^ 2)
  have hsp5 : (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2)
      = 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) :=
    integral_const_mul 6 (fun θ => (f θ) ^ 2)
  rw [integral_congr_ae hA_ae, hsp1, hsp2, hsp3, hsp4, hsp5, hFTC']
  ring


end Work.FTS.EllipticEst.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.sf_LopIter_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks


end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.SliceSigmaHardyTwo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

/-- **Second-order weighted Hardy inequality for angular slices** (the `sEta` weight
`sin(2θ)^{-η}`, `η = 99/100`).  For `g` of class `C²` on `(0, π/2)` with vanishing one-sided
limits at both endpoints and `(g'')² sEta` integrable on `Iθ`, the function itself is
controlled by its second derivative in the same weighted `L²`:
`∫⁻_θ∈Iθ ofReal (g² sEta) ≤ ofReal C · ∫⁻_θ∈Iθ ofReal ((g'')² sEta)`.

Proved in `Submission/Work/FTS/EllipticEst/H2W/Ae/ZeroHardy/sliceZeroLimitHardy.lean` as
`Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy`; see the module docstring above
for the route (Green-function pointwise bound `|g θ| ≤ (π/8)∫|g''|` + weighted
Cauchy–Schwarz + the `∫⁻` assembly). -/
theorem SliceSigmaHardyTwo : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal C
        * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) :=
  Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy

end Work.FTS.EllipticEst.H2W.Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.crossThetaIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-integration by parts of the cross term of `I₁`

With `η ∈ (0,1)` and a function `v` of class `C¹` on the *open* interval `(0,π/2)` (no
closed-interval regularity, and no hypothesis on the endpoint values of `v` — this is what the
almost-everywhere class `H2W.Ae.AeData` supplies), the identity

```
∫_θ v · v' · cos(2θ) · sin(2θ)^{-1-η}
  = ∫_θ v² · sin(2θ)^{-η} + (1+η) · ∫_θ v² · cos²(2θ) · sin(2θ)^{-2-η}
```

holds, where all integrals are over `(0,π/2)` (`v' = deriv v`).

This is the third step of the paper's chain for the `I₁` lower bound (Elgindi, Annals **194**
(2021), tex 873–890): with `U = z∂_zu` it says `CROSS = ⟨U,U⟩ + (1+η)N`, which combined with the
`z`-IBP (`SlotA.I1_z_ibp_open`) and the `θ`-IBP of the mixed term
(`H2W.I1_cross_bookkeeping`, `T₂ = -Pp + 2η·CROSS`) gives the identity

`⟨z²∂_zzu, ∂_θ²u⟩ = Pp - 2η⟨U,U⟩ - 2η(1+η)N - ⟨U, cw·∂_θ²u⟩`

consumed by the algebraic core `H2W.Ae.i1Lower_algebra_eta`.

## Route

Write `P θ := v θ² · cos(2θ) · sin(2θ)^{-1-η}`, whose derivative on `(0,π/2)` is exactly

`2·(v v' cos(2θ) sin(2θ)^{-1-η}) - 2·(v² sin(2θ)^{-η}) - 2(1+η)·(v² cos²(2θ) sin(2θ)^{-2-η})`.

The integrability of that derivative puts us in the hypotheses of `I1cb.ftc_open_interval`: `P`
has one-sided limits `fa` at `0⁺`, `fb` at `π/2⁻`, and `∫ P' = fb - fa`.  Both limits vanish by
*integrability*: near `θ = 0` (resp. `π/2`) one has `|cos 2θ| ≥ 1/2`, hence `|cos 2θ| ≤ 2 cos²2θ`
and therefore `|P θ| ≤ 2·sin(2θ)·|v² cos²(2θ) sin(2θ)^{-2-η}|`, while
`v² cos²(2θ) sin(2θ)^{-2-η}` is integrable near the endpoint by `hintN`; so a non-zero limit
would make a `1/θ`-like function integrable (`I1cb.boundary_vanish_left` / `_right`).  Hence
`∫ P' = 0`, and splitting the integral of `P'` against the three integrable pieces gives the
identity.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)






end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.slice_deriv_of_sq_deriv_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter



end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.SliceAgmonWeighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

/-! ## Elementary facts about the angular weight `thEta θ = sin(2θ)^{-η}` -/

lemma thEta_zero : thEta 0 = 0 := by
  rw [thEta, mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by have := Work.Spaces.eta_pos; linarith)

lemma thEta_pi_half : thEta (Real.pi / 2) = 0 := by
  rw [thEta, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by have := Work.Spaces.eta_pos; linarith)

lemma one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ thEta θ := by
  have hpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hneg : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hpos hle hneg
  simpa [thEta, Real.rpow_zero] using h

lemma intervalIntegral_eq_setIntegral_Iθ (f : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) = ∫ θ in Work.Spaces.Iθ, f θ := by
  rw [intervalIntegral.integral_of_le (by positivity),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

lemma intervalIntegrable_thEta {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    IntervalIntegrable (fun θ : ℝ => thEta θ) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact integrableOn_thEta.1.mono_set (fun x hx =>
    ⟨le_trans ha (le_of_lt hx.1), le_trans hx.2 hb⟩)

lemma intervalIntegral_thEta_le {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ Real.pi / 2) :
    (∫ θ in a..b, thEta θ) ≤ 10000 := by
  have hcomp : (∫ θ in a..b, thEta θ) ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), thEta θ :=
    intervalIntegral.integral_mono_interval ha hab hb
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        exact thEta_nonneg ⟨le_of_lt hx.1, hx.2⟩)
      (intervalIntegrable_thEta (by positivity) le_rfl le_rfl)
  rw [intervalIntegral_eq_setIntegral_Iθ thEta] at hcomp
  linarith [hcomp, integrableOn_thEta.2]

/-! ## Two elementary comparison lemmas -/

/-- If `(g')² ≤ K` on the open interval `(0, π/2)`, then for `[a,b] ⊆ Iθ`
`∫_a^b (g')² w ≤ K ∫_a^b w` (the endpoints `0`, `π/2` are harmless because `w = 0` there). -/
lemma piece_le {g : ℝ → ℝ} {K a b : ℝ} (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ)
    (hab : a ≤ b)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2 ≤ K)
    (hL : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume a b) :
    (∫ θ in a..b, (deriv g θ) ^ 2 * thEta θ) ≤ K * (∫ θ in a..b, thEta θ) := by
  have hW : IntervalIntegrable (fun θ : ℝ => thEta θ) volume a b :=
    intervalIntegrable_thEta hab ha.1 hb.2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab hL (hW.const_mul K) ?_
  intro θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_trans ha.1 hθ.1, le_trans hθ.2 hb.2⟩
  by_cases h0 : θ = 0
  · subst h0
    simp [thEta_zero]
  by_cases hπ : θ = Real.pi / 2
  · subst hπ
    simp [thEta_pi_half]
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθI.1 (Ne.symm h0), lt_of_le_of_ne hθI.2 hπ⟩
    exact mul_le_mul_of_nonneg_right (hpt θ hθ') (thEta_nonneg hθI)

/-- For a nonnegative `f` that is integrable on `Iθ` together with `f · thEta`, the unweighted
interval integral over `[a,b] ⊆ Iθ` is at most the weighted integral over the whole `Iθ`. -/
lemma intervalIntegral_le_weighted {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) (hab : a ≤ b)
    (hfn : ∀ θ : ℝ, 0 ≤ f θ)
    (hf : IntegrableOn f Work.Spaces.Iθ)
    (hfw : IntegrableOn (fun θ => f θ * thEta θ) Work.Spaces.Iθ) :
    (∫ y in a..b, f y) ≤ ∫ θ in Work.Spaces.Iθ, f θ * thEta θ := by
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha.1 (le_of_lt hx.1), le_trans hx.2 hb.2⟩
  have hfa : IntegrableOn f (Set.Ioc a b) := hf.mono_set hsub
  have hfwa : IntegrableOn (fun θ => f θ * thEta θ) (Set.Ioc a b) := hfw.mono_set hsub
  -- almost every `θ ∈ (a,b]` lies in the open interval `(0, π/2)`
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton (Real.pi / 2)
  have hmem_ae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc a b)), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with x hx hmem
    exact ⟨lt_of_le_of_lt ha.1 hmem.1, lt_of_le_of_ne (le_trans hmem.2 hb.2) hx⟩
  have h1 : (∫ y in a..b, f y) ≤ ∫ y in a..b, f y * thEta y := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ _
      exact hfn θ
    · exact hfwa
    · filter_upwards [hmem_ae] with θ hθ
      calc f θ = f θ * 1 := by ring
        _ ≤ f θ * thEta θ := mul_le_mul_of_nonneg_left (one_le_thEta hθ) (hfn θ)
  have h2 : (∫ y in a..b, f y * thEta y)
      ≤ ∫ y in (0 : ℝ)..(Real.pi / 2), f y * thEta y := by
    refine intervalIntegral.integral_mono_interval ha.1 hab hb.2 ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (hfn x) (thEta_nonneg ⟨le_of_lt hx.1, hx.2⟩)
    · rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
      exact hfw.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  rw [intervalIntegral_eq_setIntegral_Iθ (fun y => f y * thEta y)] at h2
  linarith

/-! ## The assembly -/

/-- **Assembly of the weighted slice Agmon inequality.**  Assuming the one-dimensional inputs
(the local interpolation inequality `hS1`, the averaging bound `hS2` and the two removals of the
weight `hInt0`, `hInt2`), the weighted `L²`-bound for the first angular derivative holds with the
explicit constant `10 ^ 8`. -/
lemma assembly {g : ℝ → ℝ} {x₁ x₂ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hx₁ : 0 ≤ x₁) (hx₁₂ : x₁ < x₂) (hx₂ : x₂ ≤ Real.pi / 2)
    (hL : x₂ - x₁ = Real.pi / 4)
    (hLint : IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hGint : IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hFint : IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hInt2 : IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2) Work.Spaces.Iθ)
    (hInt0 : IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hS1 : (∫ y in x₁..x₂, (deriv g y) ^ 2)
        ≤ (64 / (x₂ - x₁) ^ 2) * (∫ y in x₁..x₂, (g y) ^ 2)
          + (x₂ - x₁) ^ 2 * (∫ y in x₁..x₂, (deriv (deriv g) y) ^ 2))
    (hS2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2
        ≤ (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
          + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)) :
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * thEta θ)
      ≤ 10 ^ 8 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)) := by
  have hpi := Real.pi_pos
  have hx₁I : x₁ ∈ Work.Spaces.Iθ := ⟨hx₁, by linarith⟩
  have hx₂I : x₂ ∈ Work.Spaces.Iθ := ⟨le_trans hx₁ hx₁₂.le, hx₂⟩
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := Work.Spaces.zero_mem_Iθ
  have hpI : (Real.pi / 2) ∈ Work.Spaces.Iθ := Work.Spaces.pi_half_mem_Iθ
  have hLpos : 0 < x₂ - x₁ := by linarith
  -- nonnegativity of the two energy integrals
  have hF0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  have hG0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  -- step 1: comparisons of the unweighted pieces with the weighted ones
  have hJg : (∫ y in x₁..x₂, (g y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted hx₁I hx₂I hx₁₂.le (fun θ => sq_nonneg _) hInt0 hFint
  have hJ2g : (∫ y in x₁..x₂, (deriv (deriv g) y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted hx₁I hx₂I hx₁₂.le (fun θ => sq_nonneg _) hInt2 hGint
  have hI2g : (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ :=
    intervalIntegral_le_weighted h0I hpI (by positivity) (fun θ => sq_nonneg _) hInt2 hGint
  -- step 2: the uniform pointwise bound `K`, and its nonnegativity
  have hJnn : 0 ≤ ∫ y in x₁..x₂, (deriv g y) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hx₁₂.le (fun y => sq_nonneg _)
  have hJ2nn : 0 ≤ (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall (by positivity) (fun y => sq_nonneg _)
  set K : ℝ := (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
    + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 / (x₂ - x₁) := div_nonneg (by norm_num) hLpos.le
    have h2 : 0 ≤ 2 * (Real.pi / 2 - 0) := by have := Real.pi_pos; nlinarith
    nlinarith [hJnn, hJ2nn]
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv g θ) ^ 2 ≤ K := by
    intro θ hθ
    rw [hKdef]
    exact hS2 θ hθ
  -- step 3: the numeric bound on `K`
  have hJbound : (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (64 / (x₂ - x₁) ^ 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) :=
    le_trans hS1
      (add_le_add (mul_le_mul_of_nonneg_left hJg (div_nonneg (by norm_num) (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hJ2g (sq_nonneg _)))
  have hcoef1 : 128 / (x₂ - x₁) ^ 3 ≤ 304 := by
    have hcube : (27 : ℝ) < Real.pi ^ 3 := by
      have h := pow_lt_pow_left₀ Real.pi_gt_three (by norm_num : (0:ℝ) ≤ 3)
        (by norm_num : (3:ℕ) ≠ 0)
      norm_num at h
      exact h
    have hrew : (128 : ℝ) / (x₂ - x₁) ^ 3 = 8192 / Real.pi ^ 3 := by
      rw [hL, show (Real.pi / 4) ^ 3 = Real.pi ^ 3 / 64 by ring, div_div_eq_mul_div]
      norm_num
    rw [hrew, div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 3)]
    nlinarith [hcube]
  have hcoef2 : 2 * (x₂ - x₁) + Real.pi ≤ 6 := by
    rw [hL]; linarith [Real.pi_le_four]
  have hA0 : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (2 / (x₂ - x₁)) * ((64 / (x₂ - x₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)) :=
    mul_le_mul_of_nonneg_left hJbound (div_nonneg (by norm_num) hLpos.le)
  have hrew : (2 / (x₂ - x₁)) * ((64 / (x₂ - x₁) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + (x₂ - x₁) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ))
      = (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁)) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have hne : x₂ - x₁ ≠ 0 := ne_of_gt hLpos
    field_simp
    ring
  have hA : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      ≤ (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁)) * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) :=
    le_trans hA0 (le_of_eq hrew)
  have hB : 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ Real.pi * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have h2pi : 2 * (Real.pi / 2 - 0) = (Real.pi : ℝ) := by ring
    rw [h2pi]
    exact mul_le_mul_of_nonneg_left hI2g Real.pi_pos.le
  have htot : (2 / (x₂ - x₁)) * (∫ y in x₁..x₂, (deriv g y) ^ 2)
      + 2 * (Real.pi / 2 - 0) * (∫ y in (0 : ℝ)..(Real.pi / 2), (deriv (deriv g) y) ^ 2)
      ≤ (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + (2 * (x₂ - x₁) + Real.pi)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    linarith [hA, hB]
  have hfin : (128 / (x₂ - x₁) ^ 3) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + (2 * (x₂ - x₁) + Real.pi)
        * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
      ≤ 304 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
        + 6 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef1 hF0
    have h2 := mul_le_mul_of_nonneg_right hcoef2 hG0
    linarith
  have hKb : K ≤ 304 * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)
      + 6 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ) := by
    rw [hKdef]
    linarith [htot, hfin]
  -- step 4: split the weighted integral of `(g')²` into three pieces
  have hf : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hf01 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 x₁ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 (le_trans hx₁₂.le hx₂)⟩)
  have hf12 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume x₁ x₂ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁₂.le]
    exact hLint.mono_set (fun x hx => ⟨le_trans hx₁ (le_of_lt hx.1), le_trans hx.2 hx₂⟩)
  have hf2h : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume x₂ (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₂]
    exact hLint.mono_set (fun x hx => ⟨le_trans hx₁ (le_trans hx₁₂.le (le_of_lt hx.1)), hx.2⟩)
  have hf02 : IntervalIntegrable (fun θ : ℝ => (deriv g θ) ^ 2 * thEta θ) volume 0 x₂ := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (le_trans hx₁ hx₁₂.le)]
    exact hLint.mono_set (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hx₂⟩)
  have hp1 : (∫ θ in (0 : ℝ)..x₁, (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le h0I hx₁I hx₁ hpt hf01)
      (mul_le_mul_of_nonneg_left
        (intervalIntegral_thEta_le hx₁ le_rfl (le_trans hx₁₂.le hx₂)) hKnn)
  have hp2 : (∫ θ in x₁..x₂, (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le hx₁I hx₂I hx₁₂.le hpt hf12)
      (mul_le_mul_of_nonneg_left (intervalIntegral_thEta_le hx₁₂.le hx₁ hx₂) hKnn)
  have hp3 : (∫ θ in x₂..(Real.pi / 2), (deriv g θ) ^ 2 * thEta θ) ≤ K * 10000 :=
    le_trans (piece_le hx₂I hpI hx₂ hpt hf2h)
      (mul_le_mul_of_nonneg_left
        (intervalIntegral_thEta_le hx₂ (le_trans hx₁ hx₁₂.le) le_rfl) hKnn)
  have hsum : (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv g θ) ^ 2 * thEta θ) ≤ 30000 * K := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals hf01 hf12
    have e2 := intervalIntegral.integral_add_adjacent_intervals hf02 hf2h
    rw [← e2, ← e1]
    linarith [hp1, hp2, hp3]
  -- step 5: conclude
  have hsum' : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * thEta θ) ≤ 30000 * K := by
    rw [← intervalIntegral_eq_setIntegral_Iθ (fun θ => (deriv g θ) ^ 2 * thEta θ)]
    exact hsum
  have hfinal : 30000 * K ≤ 10 ^ 8 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * thEta θ)
      + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * thEta θ)) := by
    have h := mul_le_mul_of_nonneg_left hKb (by norm_num : (0:ℝ) ≤ 30000)
    nlinarith [h, hF0, hG0]
  linarith [hsum', hfinal]

theorem SliceAgmonWeighted : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ),
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro g hg hGint hFint
  by_cases hLint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ
  · -- the honest case: the hypotheses supply the two energy bounds of `assembly`
    have hder1 : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
      hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hcont2' : ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hder1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn
    have hcont2 : ContinuousOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hcont2'.pow 2
    have hcont0 : ContinuousOn (fun θ : ℝ => (g θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
      hg.continuousOn.pow 2
    have hInt2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2)
        Work.Spaces.Iθ :=
      (Support.integrableOn_of_mul_thEta hcont2 (fun θ _ => sq_nonneg _) hGint).1
    have hInt0 : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2) Work.Spaces.Iθ :=
      (Support.integrableOn_of_mul_thEta hcont0 (fun θ _ => sq_nonneg _) hFint).1
    have hInt2int : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) volume
        (0 : ℝ) (Real.pi / 2) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity)]
      exact hInt2.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
    have hInt2intJ : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) volume
        (Real.pi / 8) (3 * Real.pi / 8) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith [Real.pi_pos])]
      exact hInt2.mono_set (fun x hx =>
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    refine assembly (x₁ := Real.pi / 8) (x₂ := 3 * Real.pi / 8) hg (by positivity)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by ring)
      hLint hGint hFint hInt2 hInt0 ?_ ?_
    · exact Support.slice_local_interp (p := 0) (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hg hInt2intJ
    · exact Support.deriv_sq_le_local_avg (p := 0) (r := Real.pi / 2)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        hg hInt2int
  · -- otherwise the left-hand side is the junk value `0`
    rw [MeasureTheory.integral_undef hLint]
    refine mul_nonneg (by norm_num) (add_nonneg ?_ ?_)
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Ang2.AePpReduce =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.Ang2

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- `HkIntegrand` is independent of `α` at level `0`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand 1 0 f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

theorem HkSq_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f = Work.Spaces.HkSq 1 0 f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici
    (fun z _ => setIntegral_congr_fun measurableSet_Icc (fun θ _ => HkIntegrand_zero_eq α f z θ))


end Work.FTS.EllipticEst.Prop.Ang2
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceFluxAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop
set_option autoImplicit false
set_option maxHeartbeats 4000000






end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary facts about the weight `thEta` and the cutoff intervals

Auxiliary lemmas used by the integration-by-parts proof of the boundary product `F₀ L₀`
(`Work.FTS.EllipticEst.Prop.TraceLeftCore.prodTraceBound`).
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Elementary facts about the weight `thEta` -/


theorem one_le_thEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ thEta θ :=
  Work.EllipticEst.Core.one_le_thEta hθ

theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

theorem continuousOn_thEta_Ioo :
    ContinuousOn thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (Work.FTS.EllipticEst.sin_two_pos hθ).ne')






end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.zFluxHasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped ContDiff Real Topology
open Filter

set_option autoImplicit false

/-!
# `zFluxHasDerivAt`

The pointwise `z`-derivative of the radial flux integrand
`z' ↦ -(z' · D_z v(z',θ) · ∂_θ²v(z',θ) · w(z')² · sin(2θ)^q)`.

With `D z = D_z v(z,θ) = z ∂_z v(z,θ)`, `P z = ∂_θ²v(z,θ)` and the weight
`w(z) = (1+z)²/z²`, the product rule together with the one-dimensional identity
`(z w(z)²)' = w(z)² (z-3)/(1+z)` (`Work.FTS.EllipticEst.weight_algebra_fts`) gives

`(z D P w²)' = w² [ D·D_zP + D_zD·P + D·P·(z-3)/(1+z) ]`,

which is exactly the stated right-hand side.  The only analytic input is the
`z`-differentiability of the slices of `v`, `∂_z v` and `∂_θ²v` (hence the third
joint derivative in the hypothesis): `∂_θ²v` is only `C¹` jointly, so the generic
order-lowering lemmas `cdOn_pz_of`/`cdOn_pth_of` (`F` smooth on an open set ⇒ its
partials lose one order) are used to obtain joint `C¹` of `D_z v` and of `∂_θ²v`.
-/

/-! ## Order-lowering lemmas for the curried partial derivatives

The versions `Work.Spaces.contDiffOn_uncurry_pz`/`_pth` are stated for `⊤`-smoothness;
the following are the honest finite-order analogues used below. -/





/-- The derivative of the radial weight factor `z ↦ z·w(z)²`:
`(z w(z)²)' = w(z)² (z-3)/(1+z)`, the form in which the identity is used below. -/
theorem hasDerivAt_mul_w_sq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hw : ContDiffOn ℝ 1 (fun y : ℝ => Work.Spaces.w y) (Set.Ioi 0) := by
    show ContDiffOn ℝ 1 (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) (Set.Ioi 0)
    exact ContDiffOn.div (by fun_prop) (by fun_prop)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < y from hy)))
  have hd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
    differentiableAt_id.mul (((hw.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).pow 2)
  refine hd.hasDerivAt.congr_deriv ?_
  have h1 : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = (z - 3) * (1 + z) ^ 3 / z ^ 4 :=
    Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)
  rw [h1, show (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 from by
    simp only [Work.Spaces.w]
    field_simp]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.AngIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

open MeasureTheory Set intervalIntegral
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000


/-- `(cot(2θ))' = -2 sin(2θ)^{-2}` on `(0,π/2)`. -/
theorem hasDerivAt_cot_two {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun t : ℝ => Real.cot (2*t)) (-(2:ℝ) * (Real.sin (2*θ))^(-(2:ℝ))) θ := by
  have hsin : (0:ℝ) < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-(2:ℝ) * Real.sin (2*θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2*t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_cos (2*θ)).comp θ h
    simpa [Function.comp_def, mul_comm] using h2
  have hsin' : HasDerivAt (fun t : ℝ => Real.sin (2*t)) ((2:ℝ) * Real.cos (2*θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2*t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_sin (2*θ)).comp θ h
    simpa [Function.comp_def, mul_comm] using h2
  have hquot : HasDerivAt (fun t : ℝ => Real.cos (2*t) / Real.sin (2*t))
      (((-(2:ℝ) * Real.sin (2*θ)) * Real.sin (2*θ) - Real.cos (2*θ) * ((2:ℝ) * Real.cos (2*θ)))
        / (Real.sin (2*θ))^2) θ :=
    hcos.div hsin' hsin.ne'
  have hfun : (fun t : ℝ => Real.cot (2*t)) = fun t : ℝ => Real.cos (2*t) / Real.sin (2*t) := by
    funext t; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine hquot.congr_deriv ?_
  have key : (Real.sin (2*θ))^(-(2:ℝ)) = 1/(Real.sin (2*θ))^2 := by
    rw [← Real.rpow_two, Real.rpow_neg hsin.le, one_div]
  rw [key]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (2*θ)]








end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.integrable_deriv_psi_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.wrho_mul_sq_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

/-! ## The boundary behaviour of the weight `ρ`

`ρ θ = sin θ cos θ sin(2θ)^{-η}` equals `(1/2) sin(2θ)^{1-η}` on the open quadrant, so it
vanishes at both endpoints like `sin(2θ)^{1-η}` with `1 - η > 0`. -/

/-- On the open angular interval `ρ θ = (1/2) sin (2θ)^{1-η}`. -/
theorem wrho_eq_half_sin_rpow (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    wrho η θ = (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_Ioo hθ
  have hsin : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]; ring
  have hrs : (Real.sin (2 * θ)) ^ (1 - η)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-η) := by
    rw [show (1 : ℝ) - η = 1 + (-η) by ring, Real.rpow_add hs, Real.rpow_one]
  unfold wrho
  rw [hsin, hrs]
  ring


/-- `ρ` agrees with `(1/2) sin (2θ)^{1-η}` near `π/2` from the left. -/
theorem wrho_eventuallyEq_left (η : ℝ) :
    (fun θ : ℝ => wrho η θ) =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η)) := by
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  exact wrho_eq_half_sin_rpow η hθ


/-- `ρ θ → 0` as `θ → π/2⁻`, for `η < 1`. -/
theorem wrho_tendsto_zero_left (η : ℝ) (hp : 0 < 1 - η) :
    Tendsto (wrho η) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
  have h : Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hp).const_mul (1 / 2 : ℝ)
  exact h.congr' (wrho_eventuallyEq_left η).symm

/-- Squeezing `ρ · f²` against `K² · ρ`, where `f` is eventually bounded by `K` and `ρ → 0`
along the same filter. (No sign restriction on `K` is needed: `‖f θ‖² ≤ K²` follows from
`‖f θ‖ ≤ K` alone, since `‖f θ‖ ≥ 0`.) -/
theorem tendsto_wrho_mul_sq_zero {η K : ℝ} {f : ℝ → ℝ} {L : Filter ℝ}
    (hf : ∀ᶠ θ in L, ‖f θ‖ ≤ K) (hw : Tendsto (wrho η) L (𝓝 0)) :
    Tendsto (fun θ => wrho η θ * (f θ) ^ 2) L (𝓝 0) := by
  have hb : ∀ᶠ θ in L, ‖wrho η θ * (f θ) ^ 2‖ ≤ ‖wrho η θ‖ * K ^ 2 := by
    filter_upwards [hf] with θ hθ
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hθ 2) (norm_nonneg _)
  have hlim : Tendsto (fun θ => ‖wrho η θ‖ * K ^ 2) L (𝓝 0) := by
    simpa using hw.norm.mul_const (K ^ 2)
  exact squeeze_zero_norm' hb hlim


end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.WeakMoment.Open.IntegrableD2OfWeighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.WeakMoment.Open

/-- **Removing the weight `sEta = sin(2θ)^{-η}` from an integrability hypothesis on `D2 u`.**

`Iθ = [0, π/2]` differs from the open interval `(0, π/2)` by the two endpoints, a null set, and
on `(0, π/2)` the weight satisfies `1 ≤ sEta` (`0 < sin(2θ) ≤ 1` and the exponent `-η` is
nonpositive).  Hence `(u'')² ≤ (u'')²·sEta` there, and the two transfers

* `sliceLim_integrableOn_sq_of_integrableOn_mul_sEta` (`(u'')²·sEta ∈ L¹ ⟹ (u'')² ∈ L¹`), and
* `sliceLim_integrableOn_abs_of_integrableOn_sq` (`(u'')² ∈ L¹ ⟹ |u''| ∈ L¹`),

proved in `Submission.Work.FTS.EllipticEst.sliceLimitLeftExists` for the open interval, together
with `volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))` give the two claims. -/
theorem IntegrableD2OfWeighted {u : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ := by
  -- `Iθ = [0, π/2]` and `(0, π/2)` carry the same measure (the two endpoints are null).
  have hms : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  -- both transfers are available on the open interval
  have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h
  have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  constructor
  · change MeasureTheory.Integrable (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
    rw [hms]
    exact hsq
  · change MeasureTheory.Integrable (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
    rw [hms]
    exact habs

end Work.FTS.EllipticEst.WeakMoment.Open
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.AeNj

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The endpoint rate at `π/2`.**  For a `C¹` slice `f` on `(0, π/2)` with integrable
weighted derivative energy `∫ (f')² thEta` and vanishing right endpoint trace
`f → 0` as `θ → (π/2)⁻`,

  `|f θ| ≤ 2 (π/2 - θ)^((1+η)/2) (∫_{θ}^{π/2} (f')² thEta)^{1/2}`

on `(0, π/2)`.  The proof is the fundamental theorem of calculus
(`sliceFtcKey`), Cauchy–Schwarz for the weighted integral (`weightedCS`) with the sharp
bound `∫_{θ}^{π/2} thEta⁻¹ ≤ 2 (π/2-θ)^{1+η}` (`thEtaInvIntegralBounds`), and the
identification of the boundary constant with `0` (uniqueness of limits, using h1). -/
theorem sliceRateTwoRight {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ')
        * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by
  have heta0 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have heta1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  -- ## Integrability of `deriv f` on every open subinterval of `(0, π/2)`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.thEta] using hint
  have hI : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b) :=
    (Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable (-(Work.Spaces.eta))
      (by linarith) (by linarith) f hf hint').2
  -- ## The primitive computed from the right end
  obtain ⟨c, hc⟩ := (Work.FTS.EllipticEst.TT.sliceFtcKey f hf hI).2
  have hEtaPos := Work.EllipticEst.Core.thEtaFacts
  have hEtaInv := Work.EllipticEst.Core.thEtaInvIntegralBounds
  -- ## The key Cauchy–Schwarz bound with the sharp endpoint constant
  have hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo θ (Real.pi / 2))
      measurableSet_Ioo
      (w := Work.FTS.EllipticEst.thEta) (g := fun t => deriv f t)
      (fun t ht => hEtaPos.1 t (hsub ht))
      (hEtaPos.2.2.2.mono hsub)
      ((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub)
      (hint.mono_set hsub)
      (hEtaInv.2.2.1 θ hθ)
    have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
    rw [hc θ hθ, neg_sq]
    calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left (hEtaInv.2.2.2 θ hθ) hAnn
      _ = 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  -- ## Monotonicity of the energy
  have hAtot0 : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hmono : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    · filter_upwards with t ht
      exact ⟨lt_trans hθ.1 ht.1, ht.2⟩
  -- ## The boundary constant is the limit, which is `0`
  have hboundTot : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
        * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) := by
    intro θ hθ
    have hpos : 0 ≤ (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) :=
      Real.rpow_nonneg (by linarith [hθ.2]) _
    calc (f θ - c) ^ 2 ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hkey θ hθ
      _ ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_left (hmono θ hθ) (mul_nonneg (by norm_num) hpos)
      _ = (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
          * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) := by ring
  have hp : 0 < 1 + Work.Spaces.eta := by linarith
  have hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) :=
    (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := 1 + Work.Spaces.eta) hp).2 f c
      (2 * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
      (by linarith) hboundTot
  have hc0 : c = 0 := tendsto_nhds_unique hlim h1
  -- ## Conclusion
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  intro θ hθ
  have h := hkey θ hθ
  rw [hc0, sub_zero] at h
  have hbase : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
  have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg
        ⟨le_of_lt (lt_trans hθ.1 ht.1), le_of_lt ht.2⟩))
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
      = (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
    congr 1
    ring
  calc |f θ| = Real.sqrt ((f θ) ^ 2) := (Real.sqrt_sq_eq_abs (f θ)).symm
    _ ≤ Real.sqrt (2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt 2 * Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
          (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [show 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
                (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
              = 2 * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
                (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) from by ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * (Real.sqrt ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [Real.sqrt_mul (Real.rpow_nonneg hbase _)]
    _ = Real.sqrt 2 * ((Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by
          rw [hsqrt_rpow]
    _ = (Real.sqrt 2 * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
    _ ≤ (2 * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) *
          Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsqrt2 (Real.rpow_nonneg hbase _)) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2) := by ring

end Work.FTS.EllipticEst.remov.AeNj
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HardyFin.TruncFin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The truncated finite-order Hardy bound

Finite-order version of the private `hardyA_trunc_bound` inside
`Submission/Work/FTS/H2/DivQ/hardyA_le_W.lean`: for `ε < x < x₁` the truncated weighted `L²`
norm of `∂_x^k(f/x)` is bounded by `6/(1+γ)²·∫_0^{x₁} x^{2k-γ}(f^{(k+1)})²`, under the finite
smoothness hypothesis `ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)` with `N ≥ k + 2`.
-/

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Set Filter
open scoped Topology

/-! ## Elementary helpers -/

/-- `x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2m) * A ^ 2` for `x > 0` and a natural power `m`. -/
private lemma rpow_natpow_mul_sq {x A : ℝ} (hx : 0 < x) (p : ℝ) (m : ℕ) :
    x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2 * (m : ℝ)) * A ^ 2 := by
  have hm : (x ^ m) ^ 2 = x ^ (2 * (m : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast x (m * 2)]
    congr 1
    push_cast
    ring
  rw [mul_pow, hm, Real.rpow_add hx]
  ring

/-- The rpow rearrangement used at the top level `k + 1`. -/
private lemma rpow_shift1 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 2) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 2) (k + 1)
  have e : -γ - 2 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the boundary term `ε ^ (-γ-1) G(ε)²`. -/
private lemma rpow_shift2 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 1) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 1) (k + 1)
  have e : -γ - 1 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the weight `t ^ (-γ) * ψ(t)²`. -/
private lemma rpow_shift3 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ) * (x ^ k * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ) k
  have e : -γ + 2 * ((k : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by ring
  rw [e] at h
  exact h

/-- Pointwise AM–GM with the Hardy weights: for `x > 0` and `1 + γ > 0`,
`2 x^{-γ-1} A B ≤ ((1+γ)/2) x^{-γ-2} A² + (2/(1+γ)) x^{-γ} B²`. -/
private lemma amgm_hardy {γ x A B : ℝ} (hx : 0 < x) (hc : 0 < 1 + γ) :
    2 * (x ^ (-γ - 1) * A * B)
      ≤ (1 + γ) / 2 * (x ^ (-γ - 2) * A ^ 2) + (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
  have h1 : (x ^ ((-γ - 2) / 2) * A) ^ 2 = x ^ (-γ - 2) * A ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have h2 : (x ^ (-γ / 2) * B) ^ 2 = x ^ (-γ) * B ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have hdiv : ((x ^ (-γ / 2) * B) ^ 2) / ((1 + γ) / 2)
      = (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
    rw [h2]
    field_simp
  have hxx : x ^ ((-γ - 2) / 2) * x ^ (-γ / 2) = x ^ (-γ - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hL : 2 * ((x ^ ((-γ - 2) / 2) * A) * (x ^ (-γ / 2) * B))
      = 2 * (x ^ (-γ - 1) * A * B) := by
    rw [← hxx]
    ring
  have ham := Work.FTS.H2.DivQ.two_mul_le_mul_sq_add_div_sq (a := (1 + γ) / 2)
    (u := x ^ ((-γ - 2) / 2) * A) (v := x ^ (-γ / 2) * B) (by linarith)
  rw [hL, h1, hdiv] at ham
  exact ham

/-- Continuity of a weighted product on a compact subinterval. -/
private lemma contOn_rpow_mul {a b p : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc a b)) :
    ContinuousOn (fun t : ℝ => t ^ p * F t) (Set.Icc a b) :=
  (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1))).mul hF

/-! ## The truncated Hardy bound -/

/-- **The core estimate (finite order).** -/
theorem hardyA_trunc_bound_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) (N : ℕ)
    (hN : k + 2 ≤ N) (f : ℝ → ℝ) (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hf0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x,
          t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun z : ℝ => f z / z) t) ^ 2)
        ≤ 6 * (∫ t in (0 : ℝ)..x₁,
            t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f t) ^ 2) / (1 + γ) ^ 2 := by
  intro y x hy hyx hxx₁
  set v : ℝ → ℝ := fun s => iteratedDeriv k (fun z : ℝ => f z / z) s with hv
  set ψ : ℝ → ℝ := fun s => s ^ k * iteratedDeriv (k + 1) f s with hψ
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hG
  set u : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * v s ^ 2 with hu
  set w : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hw
  set Btot : ℝ := ∫ t in (0 : ℝ)..x₁, w t with hBtot
  have hc : 0 < 1 + γ := by linarith
  -- § continuity of `v` and `ψ` on the open interval
  have hgm : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) := by
    have h1 : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      hf.mono Set.Ioo_subset_Ioc_self
    have h2 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      h1.of_le (by exact_mod_cast (show k ≤ N by omega))
    have hid : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := h2.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rwa [hfun] at hdiv
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact continuousOn_iteratedDeriv_Ioo_fin' hgm le_rfl
  have hψcont : ContinuousOn ψ (Set.Ioo 0 x₁) := by
    rw [hψ]
    exact (continuousOn_id.pow k).mul
      (continuousOn_iteratedDeriv_Ioo_fin hf (by omega : k + 1 ≤ N))
  -- § primitive data
  obtain ⟨_, hGcont, hGderiv⟩ := primitiveDerivData_fin k γ x₁ hx₁ hγ f hf (by omega) hB
  have hGcont' : ContinuousOn G (Set.Icc 0 x₁) := hGcont
  have hGderiv' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, HasDerivAt G (ψ t) t := hGderiv
  -- § the two ingredients coming from `divSinPrimitive_fin`
  obtain ⟨hident, hbnd⟩ := divSinPrimitive_fin k γ x₁ hx₁ hγ N hN f hf hf0 hB
  have hident' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, t ^ (k + 1) * v t = G t :=
    fun t ht => hident t ht
  have hbnd' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁,
      t ^ (2 * (k : ℝ) + 1 - γ) * v t ^ 2 ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..t, w s) :=
    fun t ht => hbnd t ht
  -- § continuity of the integrands on `[y,x]`
  have hGcx : ContinuousOn G (Set.Icc y x) :=
    hGcont'.mono fun t ht => ⟨le_trans (le_of_lt hy) ht.1, le_trans ht.2 (le_of_lt hxx₁)⟩
  have hψcx : ContinuousOn ψ (Set.Icc y x) :=
    hψcont.mono fun t ht => ⟨lt_of_lt_of_le hy ht.1, lt_of_le_of_lt ht.2 hxx₁⟩
  have hdG : ∀ t ∈ Set.Ioo y x, HasDerivAt G (ψ t) t :=
    fun t ht => hGderiv' t ⟨lt_trans hy ht.1, lt_trans ht.2 hxx₁⟩
  -- § the integration by parts
  have hibp := Work.FTS.H2.DivQ.rpowSq_ibp (γ := γ) hy hyx.le hGcx hdG hψcx
  -- § identification of the left-hand integral
  have hEq1 : (∫ t in y..x, t ^ (-γ - 2) * G t ^ 2) = ∫ t in y..x, u t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hyx.le] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
    have htI : t ∈ Set.Ioo (0 : ℝ) x₁ := ⟨ht0, lt_of_le_of_lt ht.2 hxx₁⟩
    rw [← hident' t htI]
    simp only [hu]
    exact rpow_shift1 k ht0
  rw [hEq1] at hibp
  -- § AM–GM
  have hAM1 : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := by
    have hpt : ∀ t ∈ Set.Icc y x,
        2 * (t ^ (-γ - 1) * G t * ψ t)
          ≤ (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
            + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2) :=
      fun t ht => amgm_hardy (lt_of_lt_of_le hy ht.1) hc
    have hca : ContinuousOn (fun t : ℝ => t ^ (-γ - 2) * G t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hGcx.pow 2)
    have hcb : ContinuousOn (fun t : ℝ => t ^ (-γ) * ψ t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hψcx.pow 2)
    have hcf : ContinuousOn (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t)) (Set.Icc y x) :=
      ((contOn_rpow_mul hy (hGcx.mul hψcx)).const_mul 2).congr fun t _ => by
        simp only [Pi.mul_apply]
        ring
    have hcg : ContinuousOn
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) (Set.Icc y x) :=
      (hca.const_mul _).add (hcb.const_mul _)
    have hif : IntervalIntegrable (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t))
        volume y x := hcf.intervalIntegrable_of_Icc hyx.le
    have hig : IntervalIntegrable
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) volume y x :=
      hcg.intervalIntegrable_of_Icc hyx.le
    have hmono := intervalIntegral.integral_mono_on hyx.le hif hig hpt
    have hif1 : IntervalIntegrable (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2))
        volume y x := (hca.const_mul _).intervalIntegrable_of_Icc hyx.le
    have hif2 : IntervalIntegrable (fun t : ℝ => (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2))
        volume y x := (hcb.const_mul _).intervalIntegrable_of_Icc hyx.le
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hif1 hif2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    rw [hEq1] at hmono
    exact hmono
  -- § the `ψ²` integral is dominated by `Btot`
  have hK : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) ≤ Btot := by
    have heq : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) = ∫ t in y..x, w t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hψ, hw]
      exact rpow_shift3 k ht0
    rw [heq, hBtot, intervalIntegral.integral_of_le hx₁.le,
      intervalIntegral.integral_of_le hyx.le]
    refine setIntegral_mono_set hB ?_ ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        simp only [hw]
        exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
    · exact Eventually.of_forall fun t ht =>
        ⟨lt_trans hy ht.1, le_of_lt (lt_of_le_of_lt ht.2 hxx₁)⟩
  -- § the boundary bound at `y`
  have hybd : y ^ (-γ - 1) * G y ^ 2 ≤ Btot / (1 + γ) := by
    have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := ⟨hy, lt_trans hyx hxx₁⟩
    have hb := hbnd' y hyI
    have hInt : (∫ s in (0 : ℝ)..y, w s) ≤ Btot := by
      rw [hBtot, intervalIntegral.integral_of_le hx₁.le,
        intervalIntegral.integral_of_le hy.le]
      refine setIntegral_mono_set hB ?_ ?_
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun t ht => by
          simp only [hw]
          exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
      · exact Eventually.of_forall fun t ht =>
          ⟨ht.1, le_trans ht.2 (le_of_lt (lt_trans hyx hxx₁))⟩
    rw [← hident' y hyI, rpow_shift2 k hy]
    calc y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2
        ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..y, w s) := hb
      _ ≤ 1 / (1 + γ) * Btot := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = Btot / (1 + γ) := by ring
  -- § assembling
  have hxterm : 0 ≤ x ^ (-γ - 1) * G x ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos (lt_trans hy hyx) _).le (sq_nonneg _)
  have hAM1' : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := hAM1
  have hK' : (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2)
      ≤ (2 / (1 + γ)) * Btot := mul_le_mul_of_nonneg_left hK (by positivity)
  have hstep : (1 + γ) * (∫ t in y..x, u t)
      ≤ y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot := by
    linarith [hibp, hAM1', hK', hxterm]
  -- § final arithmetic
  have hmult := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
  have eL : 2 * (1 + γ) * ((1 + γ) * (∫ t in y..x, u t))
      = 2 * (1 + γ) ^ 2 * (∫ t in y..x, u t) := by ring
  have e4 : 2 * (1 + γ) * (2 / (1 + γ) * Btot) = 4 * Btot := by
    field_simp
    ring
  have eR : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot)
      = 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) + (1 + γ) ^ 2 * (∫ t in y..x, u t)
        + 4 * Btot := by
    rw [mul_add, mul_add, e4]
    ring
  rw [eL, eR] at hmult
  have hP2 : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) ≤ 2 * Btot := by
    have h3 := mul_le_mul_of_nonneg_left hybd (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
    have e : 2 * (1 + γ) * (Btot / (1 + γ)) = 2 * Btot := by
      field_simp
    rwa [e] at h3
  have h4 : (1 + γ) ^ 2 * (∫ t in y..x, u t) ≤ 6 * Btot := by
    linarith [hmult, hP2]
  have hgoal : (∫ t in y..x, u t)
      ≤ 6 * Btot / (1 + γ) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + γ) ^ 2)]
    linarith [h4]
  exact hgoal

end Work.FTS.EllipticEst.remov.HardyFin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_of_pos_open (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

theorem sliceCSWeightedOpen {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |g θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- ## Step 0: the two endpoints form a null set, hence the integral over `Iθ = [0, π/2]`
  -- equals the integral over the open interval `Ioo 0 (π/2)`, where `sin (2·) > 0`.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ (x : ℝ), x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
        lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  rw [hms]
  -- ## Step 1: Cauchy–Schwarz over `Ioo 0 (π/2)`.
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hIoomeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) :=
    fun θ hθ => sin_two_pos hθ
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hvcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inr (by rw [Work.Spaces.eta]; norm_num))
  -- the only difference from the closed version: `hg` is already on the open interval
  have hucont : ContinuousOn
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hg.abs.mul hwcont
  have huaesm : AEStronglyMeasurable
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hucont.aestronglyMeasurable hIoomeas
  have hvaesm : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hvcont.aestronglyMeasurable hIoomeas
  -- the two squares are exactly the two weights of the statement
  have hEq1 : Set.EqOn (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hx : 0 < Real.sin (2 * θ) := hsinpos θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
    rw [mul_pow, sq_abs, rpow_sq_of_pos_open _ _ hx,
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have hEq2 : Set.EqOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
    rw [rpow_sq_of_pos_open _ _ (hsinpos θ hθ),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  have hu2int : MeasureTheory.Integrable
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hint.mono_set hsub).congr_fun hEq1 hIoomeas
  have hv2int : MeasureTheory.Integrable
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((integrableOn_sin_two_rpow hη).1.mono_set hsub).congr_fun hEq2 hIoomeas
  have humem : MeasureTheory.MemLp
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr hu2int
  have hvmems : MeasureTheory.MemLp
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvaesm).mpr hv2int
  have hcs := Work.Spaces.cs_integral humem hvmems
  -- ## Step 2: identify the three integrals of the Cauchy–Schwarz inequality
  have e1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
          * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |g x| := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
        * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2) = |g x|
    rw [mul_assoc, ← Real.rpow_add hx',
      show -(Work.Spaces.eta / 2) + Work.Spaces.eta / 2 = 0 by ring, Real.rpow_zero,
      mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (g x) ^ 2 * Work.FTS.EllipticEst.sEta x := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (g x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    rw [mul_pow, sq_abs, rpow_sq_of_pos_open _ _ hx',
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sin (2 * x)) ^ (Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    show ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    rw [rpow_sq_of_pos_open _ _ (hsinpos x hx),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  rw [e1, e2, e3] at hcs
  exact hcs

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.slice_deriv_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

/-- If a smooth slice takes the same value at the two endpoints `0` and `π/2`, then its
derivative vanishes somewhere in `Iθ = [0, π/2]` (Rolle / Lagrange mean value theorem). -/
private lemma deriv_zero_exists_of_endpoints {u : ℝ → ℝ} (hsm : SliceSmooth u)
    (h0 : u 0 = u (Real.pi / 2)) : ∃ θ₀ ∈ Work.Spaces.Iθ, deriv u θ₀ = 0 := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub2 : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  have hle : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcont : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := hsm.continuousOn.mono hsub
  have hdiff : DifferentiableOn ℝ u (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.differentiableOn (by norm_num)).mono hsub2
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hle hcont hdiff
  refine ⟨c, ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
  rw [hcd]
  have hz : u (Real.pi / 2) - u 0 = 0 := by rw [← h0]; ring
  simp [hz]

/-- The second derivative of a smooth slice is continuous on `Iθ`. -/
private lemma sliceV_continuousOn {u : ℝ → ℝ} (hsm : SliceSmooth u) :
    ContinuousOn (sliceV u) Work.Spaces.Iθ := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub

/-- If the derivative of a smooth slice vanishes at some `θ₀ ∈ Iθ`, then everywhere on `Iθ`
the derivative is bounded by the full integral of `|u''|` over `Iθ` (fundamental theorem of
calculus plus the triangle inequality for the integral). -/
private lemma abs_deriv_le_integral_abs_sliceV {u : ℝ → ℝ} (hsm : SliceSmooth u) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Work.Spaces.Iθ) (hz : deriv u θ₀ = 0) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |deriv u θ| ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
  have hsub : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |sliceV u x|)
      = ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  have hgi : IntervalIntegrable (fun x => |sliceV u x|) volume 0 (Real.pi / 2) :=
    hcont.abs.intervalIntegrable_of_Icc hle
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ₀
  have huIcc : Set.uIcc θ₀ θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hθ₀.1 h1, le_trans h2 hθ.2⟩
    · exact ⟨le_trans hθ.1 h1, le_trans h2 hθ₀.2⟩
  have hFTC : (∫ x in θ₀..θ, sliceV u x) = deriv u θ - deriv u θ₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hd1.mono (huIcc.trans hsub))
  have hvaleq : deriv u θ = ∫ x in θ₀..θ, sliceV u x := by
    rw [hFTC, hz, sub_zero]
  rw [hvaleq]
  rcases le_total θ₀ θ with hle2 | hle2
  · have h1 : |∫ x in θ₀..θ, sliceV u x| ≤ ∫ x in θ₀..θ, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ₀..θ, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ₀.1 hle2 hθ.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · have hsym : (∫ x in θ₀..θ, sliceV u x) = -(∫ x in θ..θ₀, sliceV u x) := intervalIntegral.integral_symm ..
    have h1 : |∫ x in θ..θ₀, sliceV u x| ≤ ∫ x in θ..θ₀, |sliceV u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle2
    have h2 : (∫ x in θ..θ₀, |sliceV u x|) ≤ ∫ x in Work.Spaces.Iθ, |sliceV u x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1 hle2 hθ₀.2
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

/-- Boundary (FTC) bound for the first derivative of a smooth slice with equal endpoint values,
with `A = ∫_{Iθ} (u'')² sin(2θ)^{-η}`:

`(∂_θ u θ)² ≤ A · ∫_{Iθ} sin(2θ)^η`   for every `θ ∈ Iθ`.

Route: `∂_θ u` is continuous on `Iθ` and `∫_{Iθ} ∂_θ u = u(π/2) - u(0) = 0`
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`), so `∂_θ u` has a zero `θ₀` (a continuous
function on an interval whose integral vanishes cannot have a constant non-zero sign); then
`|∂_θ u θ| = |∫_{θ₀}^{θ} u''| ≤ ∫_{Iθ}|u''|`, and Cauchy–Schwarz (`Work.Spaces.cs_integral`)
applied to `|u''|·sin(2θ)^{-η/2}` and `sin(2θ)^{η/2}` — using `sin(2θ)^{-η} ≥ 1` on `Iθ` — gives
`(∫|u''|)² ≤ A · ∫ sin(2θ)^η`.  The hypothesis
`IntegrableOn (fun θ => (u'')² sin(2θ)^{-η}) Iθ` makes `A` honest (not the junk value `0`);
note `η = 99/100 < 1` so `∫_{Iθ} sin(2θ)^η ≤ π/2` is finite. -/
theorem slice_deriv_sq_le {u : ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SliceSmooth u)
    (h0 : u 0 = u (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- Rolle: pick `θ₀ ∈ Iθ` with `deriv u θ₀ = 0` (the mean value theorem, since `u` has the
  -- same value at `0` and `π/2`).
  obtain ⟨θ₀, hθ₀, hz⟩ := deriv_zero_exists_of_endpoints hsm h0
  -- Cauchy–Schwarz on the slice, with the second derivative as the `g` of `slice_cs_weighted`.
  have hvcont : ContinuousOn (sliceV u) Work.Spaces.Iθ := sliceV_continuousOn hsm
  have hcs := slice_cs_weighted (g := sliceV u) hvcont hint
  intro θ hθ
  -- FTC from `θ₀` to `θ`: `deriv u θ = ∫_{θ₀}^{θ} u''`, hence `|deriv u θ| ≤ ∫_{Iθ} |u''|`.
  have habs := abs_deriv_le_integral_abs_sliceV hsm hθ₀ hz θ hθ
  have hsq : (deriv u θ) ^ 2 ≤ (∫ x in Work.Spaces.Iθ, |sliceV u x|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  linarith [hcs, hsq]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.middleRegionLHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The middle interval `[π/8, 3π/8]`

Throughout this file `midA = π/8` and `midB = 3π/8` are the two ends of the *middle* region, on
which `sin(2θ) ∈ [1/2, 1]`.  The two abbreviations are `abbrev`s, so they are definitionally the
literal expressions occurring in the statement of `middleRegionLHS`. -/

/-- The left end `π/8` of the middle region. -/
abbrev midA : ℝ := Real.pi / 8

/-- The right end `3π/8` of the middle region. -/
abbrev midB : ℝ := 3 * Real.pi / 8

/-- The middle region, as a set. -/
abbrev midSet : Set ℝ := Set.Icc midA midB

theorem midA_lt_midB : midA < midB := by
  change Real.pi / 8 < 3 * Real.pi / 8
  linarith [Real.pi_pos]

theorem midA_pos : 0 < midA := by
  change (0 : ℝ) < Real.pi / 8
  linarith [Real.pi_pos]

theorem midB_lt_pi_div_two : midB < Real.pi / 2 := by
  change 3 * Real.pi / 8 < Real.pi / 2
  linarith [Real.pi_pos]

/-- The middle region is contained in the open angular interval `(0, π/2)`. -/
theorem midSet_subset_Ioo : midSet ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  exact ⟨lt_of_lt_of_le midA_pos hx.1, lt_of_le_of_lt hx.2 midB_lt_pi_div_two⟩

/-- The middle region is contained in `Iθ`. -/
theorem midSet_subset_Iθ : midSet ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨le_trans midA_pos.le hx.1, le_trans hx.2 midB_lt_pi_div_two.le⟩

/-! ## Elementary bounds for `sin (2θ)` on the middle region -/

/-- `1/2 ≤ sin (2θ)` for `θ ∈ [π/8, 3π/8]`: indeed `2θ ∈ [π/4, 3π/4]` and `sin ≥ √2/2` there. -/
theorem half_le_sin_two_of_mem_mid {θ : ℝ} (hθ : θ ∈ midSet) :
    (1 : ℝ) / 2 ≤ Real.sin (2 * θ) := by
  have h1 : Real.pi / 4 ≤ 2 * θ := by
    have := hθ.1; change Real.pi / 8 ≤ θ at this; linarith [this, Real.pi_pos]
  have h2 : 2 * θ ≤ 3 * Real.pi / 4 := by
    have := hθ.2; change θ ≤ 3 * Real.pi / 8 at this; linarith [this, Real.pi_pos]
  have key : ∀ t : ℝ, Real.pi / 4 ≤ t → t ≤ 3 * Real.pi / 4 → (1 : ℝ) / 2 ≤ Real.sin t := by
    intro t ht1 ht2
    rcases le_total t (Real.pi / 2) with h | h
    · have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := t)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) ht1
      rw [Real.sin_pi_div_four] at h3
      have := Real.one_lt_sqrt_two; linarith
    · have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := Real.pi - t)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
      rw [Real.sin_pi_div_four, Real.sin_pi_sub] at h3
      have := Real.one_lt_sqrt_two; linarith
  exact key (2 * θ) h1 h2

/-- `0 < sin (2θ)` for `θ ∈ [π/8, 3π/8]`. -/
theorem sin_two_pos_of_mem_mid {θ : ℝ} (hθ : θ ∈ midSet) : 0 < Real.sin (2 * θ) :=
  lt_of_lt_of_le (by norm_num) (half_le_sin_two_of_mem_mid hθ)


/-! ## The weight `sin(2θ)^{-γ}` on the middle region -/

/-- On the middle region the weight `sin(2θ)^{-γ}` is bounded by `2^γ` (for `γ ≥ 0`). -/
theorem rpow_neg_sin_two_le_mid {γ : ℝ} (hγ : 0 ≤ γ) {θ : ℝ} (hθ : θ ∈ midSet) :
    (Real.sin (2 * θ)) ^ (-γ) ≤ 2 ^ γ := by
  have hhalf := half_le_sin_two_of_mem_mid hθ
  have h1 : (Real.sin (2 * θ)) ^ (-γ) ≤ ((1 : ℝ) / 2) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by linarith)
  have h2 : ((1 : ℝ) / 2) ^ (-γ) = 2 ^ γ := by
    rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
      Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) γ, inv_inv]
  rwa [h2] at h1

/-- On the middle region, `sin(2θ)^{-γ} ≤ 2^γ · sin(2θ)^{-η}` for `γ ≥ η ≥ 0`: split off the
excess exponent `γ - η` (the factor `sin(2θ)^{-(γ-η)}` is at most `2^{γ-η} ≤ 2^γ` because
`sin(2θ) ≥ 1/2` there). -/
theorem rpow_neg_sin_two_le_mid_eta {γ : ℝ} (hγ : Work.Spaces.eta ≤ γ) {θ : ℝ}
    (hθ : θ ∈ midSet) :
    (Real.sin (2 * θ)) ^ (-γ) ≤ 2 ^ γ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs := sin_two_pos_of_mem_mid hθ
  have hhalf := half_le_sin_two_of_mem_mid hθ
  have hγη : 0 ≤ γ - Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hsplit : (Real.sin (2 * θ)) ^ (-γ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) := by
    rw [← Real.rpow_add hs]; ring_nf
  have hb : (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta))
      ≤ ((1 : ℝ) / 2) ^ (-(γ - Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by linarith)
  have hb' : ((1 : ℝ) / 2) ^ (-(γ - Work.Spaces.eta)) = 2 ^ (γ - Work.Spaces.eta) := by
    rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num),
      Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (γ - Work.Spaces.eta), inv_inv]
  have hb2 : (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) ≤ 2 ^ (γ - Work.Spaces.eta) :=
    hb.trans_eq hb'
  have hb3 : (2 : ℝ) ^ (γ - Work.Spaces.eta) ≤ 2 ^ γ :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
      (by linarith [Work.Spaces.eta_pos])
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
  calc (Real.sin (2 * θ)) ^ (-γ)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(γ - Work.Spaces.eta)) := hsplit
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 2 ^ (γ - Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left hb2 hnn
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 2 ^ γ :=
        mul_le_mul_of_nonneg_left hb3 hnn
    _ = 2 ^ γ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## Smoothness of the pieces on the middle region -/

/-- The angular quotient `h / sin(2θ)` is `C^∞` on `(0, π/2)` when `h` is. -/
theorem contDiffOn_div_sin_two {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun θ => h θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  apply hsm.div
  · fun_prop
  · intro θ hθ
    exact ne_of_gt (Work.FTS.H2.sin_two_pos_of_Ioo hθ)

/-- Every iterate `D_θ^m h` is `C^∞` on `(0, π/2)` when `h` is. -/
theorem contDiffOn_Dth1Iter {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m h) (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => simpa using hsm
  | succ k ih =>
    rw [Work.Elliptic.Dth1Iter_succ]
    exact (by fun_prop : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo 0 (Real.pi / 2))).mul (ih.deriv_of_isOpen isOpen_Ioo (by simp))

/-- The derivative of a `C^∞` slice is `C^∞` on `(0, π/2)`. -/
theorem contDiffOn_deriv_slice {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.deriv_of_isOpen isOpen_Ioo (by simp)

/-- The weight `θ ↦ sin(2θ)^{-γ}` is continuous on the middle region. -/
theorem continuousOn_rpow_neg_sin_two (γ : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ)) midSet := by
  apply ContinuousOn.rpow
  · fun_prop
  · exact continuousOn_const
  · intro θ hθ
    exact Or.inl (ne_of_gt (sin_two_pos_of_mem_mid hθ))

/-- `h / sin(2θ)` is continuous on the middle region. -/
theorem continuousOn_div_sin_two {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => h θ / Real.sin (2 * θ)) midSet :=
  ((contDiffOn_div_sin_two hsm).continuousOn).mono midSet_subset_Ioo

/-- `D_θ^m (∂_θ h)` is continuous on the middle region. -/
theorem continuousOn_Dth1Iter_deriv {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContinuousOn (fun θ => Work.Elliptic.Dth1Iter m (deriv h) θ) midSet :=
  ((contDiffOn_Dth1Iter (contDiffOn_deriv_slice hsm) m).continuousOn).mono midSet_subset_Ioo

/-- `D_θ^i (h / sin(2θ))` is continuous on the middle region. -/
theorem continuousOn_Dth1Iter_div {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (i : ℕ) :
    ContinuousOn
      (fun θ => Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) midSet :=
  ((contDiffOn_Dth1Iter (contDiffOn_div_sin_two hsm) i).continuousOn).mono midSet_subset_Ioo

/-- `∂_θ h` is continuous on the middle region. -/
theorem continuousOn_deriv_slice {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv h) midSet :=
  ((contDiffOn_deriv_slice hsm).continuousOn).mono midSet_subset_Ioo

/-- The length of the middle interval: `|(π/8, 3π/8)| = π/4`. -/
theorem volume_real_Ioc_mid : (volume : MeasureTheory.Measure ℝ).real (Set.Ioc midA midB)
    = Real.pi / 4 := by
  rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by
      change (0 : ℝ) ≤ 3 * Real.pi / 8 - Real.pi / 8
      linarith [Real.pi_pos])]
  change 3 * Real.pi / 8 - Real.pi / 8 = Real.pi / 4
  ring



end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.HardSlotVan =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.L12ZeroLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.lzero1FinSumAE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory Set Filter
open scoped Real Topology BigOperators

/-!
# `ModalSolR/lzero1FinSumAE` — the angular operator on a finite mode sum, almost everywhere

For a finite set `s` of modes and coefficients `a : ℕ → ℝ`, put

  `v θ = ∑_{m ∈ s} a m · eFam m θ`

(`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is the `m`-th Dirichlet eigenfunction of the
angular operator `Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6`).  The two statements proved here are

* **almost everywhere** the operator acts diagonally on the finite sum,
  `Lzero1 v θ = ∑_{m ∈ s} lam m · a m · eFam m θ`,  `lam m = 2m(2m+5)`;
* the `cos θ`-weighted product `Lzero1 v · v · cos θ` is integrable on `Iθ = [0, π/2]`.

The pointwise identity is a finite-sum linearity statement: it holds at every `θ` with
`cos θ ≠ 0`, i.e. at every `θ ∈ Iθ` except the endpoint `π/2` (which is a null set).  The
linearity input is `Work.EllipticEst.ModalSolution.PTB.finSum_lzero`, transported to `Lzero1`
along the definitional bridge `Lzero1_eq_Lzero`; the per-mode eigenvalue relation is
`Gegenbauer.eFam_Lzero`.  Integrability follows because the integrand agrees a.e. on `Iθ` with
the continuous function `(∑ lam m · a m · eFam m) · (∑ a m · eFam m) · cos`, and `Iθ` is
compact.
-/

/-- `θ ≠ π/2` holds almost everywhere on the line (a singleton is null). -/
private lemma ae_ne_pi_half : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ), θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ≠ Real.pi / 2} = {Real.pi / 2} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ne_eq, not_not]
  rw [hset]
  exact measure_singleton _

/-- On `Iθ = [0, π/2]` the only zero of `cos` is the right endpoint: for `θ ∈ Iθ`, `θ ≠ π/2`
one has `cos θ ≠ 0`. -/
private lemma cos_ne_zero_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hne : θ ≠ Real.pi / 2) : Real.cos θ ≠ 0 := by
  rw [Work.Spaces.Iθ] at hθ
  have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hne
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩)

/-- **`Lzero1` on a finite sum of eigenmodes.**  For any finite set `s` of modes, any
coefficients `a`, and any `θ` with `cos θ ≠ 0`, the operator acts mode-wise with the
eigenvalues `lam m = 2m(2m+5)`. -/
private lemma lzero1_finSum_eFam (a : ℕ → ℝ) (s : Finset ℕ) {θ : ℝ}
    (hcos : Real.cos θ ≠ 0) :
    Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  rw [show Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      = Work.Elliptic.Lzero
          (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ from
    congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero
      (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0) θ]
  exact Work.EllipticEst.ModalSolution.PTB.finSum_lzero a s 0 θ hcos

theorem lzero1FinSumAE (a : ℕ → ℝ) (s : Finset ℕ) :
    (∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ →
      Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    ∧ MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1
            (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
          * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
        Work.Spaces.Iθ := by
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ∈ Work.Spaces.Iθ →
      Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        = ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    filter_upwards [ae_ne_pi_half] with θ hne hθ
    exact lzero1_finSum_eFam a s (cos_ne_zero_of_mem_Iθ hθ hne)
  refine ⟨hae, ?_⟩
  -- the pointwise identity, as an a.e. equality on the restricted measure
  have hid : (fun θ => Work.FTS.EllipticEst.Lzero1
        (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Work.Spaces.Iθ :=
      MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
    have hne : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ Real.pi / 2 :=
      MeasureTheory.ae_restrict_of_ae ae_ne_pi_half
    filter_upwards [hmem, hne] with θ h1 h2
    exact lzero1_finSum_eFam a s (cos_ne_zero_of_mem_Iθ h1 h2)
  -- the comparison integrand is continuous, hence integrable on the compact `Iθ`
  have hcont1 : Continuous fun θ : ℝ => ∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
    continuous_finsetSum _ (fun m _ =>
      (Work.FTS.PhiStar.Series.continuous_eFam m).const_mul
        (Work.FTS.PhiStar.Gegenbauer.lam m * a m))
  have hcont2 : Continuous fun θ : ℝ => ∑ m ∈ s, a m
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
    continuous_finsetSum _ (fun m _ =>
      (Work.FTS.PhiStar.Series.continuous_eFam m).const_mul (a m))
  have hS : MeasureTheory.Integrable
      (fun θ : ℝ => (∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hcont1.mul hcont2).mul Real.continuous_cos).continuousOn
  -- the two integrands agree a.e. on `Iθ`
  have hcongr : (fun θ : ℝ => (∑ m ∈ s, Work.FTS.PhiStar.Gegenbauer.lam m * a m
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.FTS.EllipticEst.Lzero1
          (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ) := by
    filter_upwards [hid] with θ h
    rw [h]
  exact hS.congr hcongr

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.radGreenWeakOdeMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory Set Filter
open scoped Real Topology
open Work.EllipticEst.ModalSolution.RadGreenWeak (sM sP qW wgt pwt Lneg srcM srcP)
open Work.FTS.H2.ModalSolR.RGWeak (Fgen Fgen_eq_zero integral_Ioi_eq_intervalIntegral)

theorem radGreenWeakOdeMeas {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c ψ : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioi 0) :
    (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
        (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
        * z ^ ((5 - α) / α))
      + Work.FTS.PhiStar.Radial.lamR m
          * (∫ z in Set.Ioi 0,
              Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * z ^ ((5 - α) / α))
      = ∫ z in Set.Ioi 0, c z * ψ z * z ^ ((5 - α) / α) := by
  -- ## 0. the support interval
  obtain ⟨a, b, ha, hab, hsub, hvan⟩ :=
    Work.EllipticEst.ModalSolution.RGW.support_extract ψ hψ hψc hψs
  have hable : a ≤ b := le_of_lt hab
  have hvan2 : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0 :=
    fun z hz => ⟨(hvan z hz).1, (hvan z hz).2.1⟩
  have hsubI : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hable
  -- ## 1. continuity of the elementary factors on `(0,∞)`
  have hpowM : ContinuousOn (fun z : ℝ => z ^ (sM α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowP : ContinuousOn (fun z : ℝ => z ^ (sP α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowMm : ContinuousOn (fun z : ℝ => z ^ (sM α m - 1)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m - 1) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hpowPm : ContinuousOn (fun z : ℝ => z ^ (sP α m - 1)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m - 1) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψ.contDiffOn
  have hpsic : ContinuousOn ψ (Set.Ioi 0) := hψ.continuous.continuousOn
  have hψdc : ContinuousOn (deriv ψ) (Set.Ioi 0) :=
    (hψ.continuous_deriv (by norm_num)).continuousOn
  have hpwtc : ContinuousOn (pwt α) (Set.Ioi 0) := by
    have h : pwt α = fun z : ℝ => α ^ 2 * (z ^ 2 * wgt α z) := by
      funext z; simp only [pwt]
    rw [h]
    exact continuousOn_const.mul ((continuousOn_id.pow 2).mul hwgtc)
  have hFgenM : ContinuousOn (fun z : ℝ => Fgen α (sM α m) ψ z) (Set.Ioi 0) :=
    (hpwtc.mul ((hpowM.mul hψdc).sub
      (((continuousOn_const (c := sM α m)).mul hpowMm).mul hpsic))).congr
      (fun z _ => by simp only [Fgen, Pi.mul_apply, Pi.sub_apply] <;> ring)
  have hFgenP : ContinuousOn (fun z : ℝ => Fgen α (sP α m) ψ z) (Set.Ioi 0) :=
    (hpwtc.mul ((hpowP.mul hψdc).sub
      (((continuousOn_const (c := sP α m)).mul hpowPm).mul hpsic))).congr
      (fun z _ => by simp only [Fgen, Pi.mul_apply, Pi.sub_apply] <;> ring)
  -- ## 2. the local abbreviations
  set GM : ℝ → ℝ := fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z) with hGM
  set GP : ℝ → ℝ := fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z) with hGP
  set RM : ℝ → ℝ := fun z => z ^ (sM α m) * (wgt α z * ψ z) with hRM
  set RP : ℝ → ℝ := fun z => z ^ (sP α m) * (wgt α z * ψ z) with hRP
  set fM : ℝ → ℝ := srcM α m c with hfM
  set fP : ℝ → ℝ := srcP α m c with hfP
  set A : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, srcM α m c t with hA
  set Bz : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, srcP α m c t with hB
  -- ## 3. continuity / integrability of the pieces
  have hGMcontI : ContinuousOn GM (Set.Icc a b) := by
    rw [hGM]
    exact (hpowM.mono hsubI).mul ((hwgtc.mono hsubI).mul (hLc.mono hsubI))
  have hGPcontI : ContinuousOn GP (Set.Icc a b) := by
    rw [hGP]
    exact (hpowP.mono hsubI).mul ((hwgtc.mono hsubI).mul (hLc.mono hsubI))
  have hRMcontI : ContinuousOn RM (Set.Icc a b) := by
    rw [hRM]
    exact (hpowM.mono hsubI).mul ((hwgtc.mono hsubI).mul (hpsic.mono hsubI))
  have hRPcontI : ContinuousOn RP (Set.Icc a b) := by
    rw [hRP]
    exact (hpowP.mono hsubI).mul ((hwgtc.mono hsubI).mul (hpsic.mono hsubI))
  have hGMcontU : ContinuousOn GM (Set.uIcc a b) := by rw [huIcc]; exact hGMcontI
  have hGPcontU : ContinuousOn GP (Set.uIcc a b) := by rw [huIcc]; exact hGPcontI
  have hRMcontU : ContinuousOn RM (Set.uIcc a b) := by rw [huIcc]; exact hRMcontI
  have hRPcontU : ContinuousOn RP (Set.uIcc a b) := by rw [huIcc]; exact hRPcontI
  have hFgenMcontU : ContinuousOn (fun t : ℝ => Fgen α (sM α m) ψ t) (Set.uIcc a b) := by
    rw [huIcc]; exact hFgenM.mono hsubI
  have hFgenPcontU : ContinuousOn (fun t : ℝ => Fgen α (sP α m) ψ t) (Set.uIcc a b) := by
    rw [huIcc]; exact hFgenP.mono hsubI
  have hGMint : IntervalIntegrable GM volume a b := hGMcontI.intervalIntegrable_of_Icc hable
  have hGPint : IntervalIntegrable GP volume a b := hGPcontI.intervalIntegrable_of_Icc hable
  have hRMint : IntervalIntegrable RM volume a b := hRMcontI.intervalIntegrable_of_Icc hable
  have hRPint : IntervalIntegrable RP volume a b := hRPcontI.intervalIntegrable_of_Icc hable
  have hGM_uIcc : IntegrableOn GM (Set.uIcc a b) volume := by
    rw [huIcc]; exact hGMcontI.integrableOn_compact isCompact_Icc
  have hGP_uIcc : IntegrableOn GP (Set.uIcc a b) volume := by
    rw [huIcc]; exact hGPcontI.integrableOn_compact isCompact_Icc
  have hRM_uIcc : IntegrableOn RM (Set.uIcc a b) volume := by
    rw [huIcc]; exact hRMcontI.integrableOn_compact isCompact_Icc
  have hRP_uIcc : IntegrableOn RP (Set.uIcc a b) volume := by
    rw [huIcc]; exact hRPcontI.integrableOn_compact isCompact_Icc
  -- the source functions and their primitives
  have hfM_int : IntervalIntegrable fM volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hable, hfM]
    exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm
      (lt_of_lt_of_le ha hable)).mono_set (fun t ht => ⟨lt_of_lt_of_le ha ht.1.le, ht.2⟩)
  have hfP_int : IntervalIntegrable fP volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hable, hfP]
    exact (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
      (fun t ht => ht.1)
  have hfM_Icc : IntegrableOn fM (Set.Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hfM_int.1
  have hfP_Icc : IntegrableOn fP (Set.Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hfP_int.1
  have hfM_uIcc : IntegrableOn fM (Set.uIcc a b) volume := by rw [huIcc]; exact hfM_Icc
  have hfP_uIcc : IntegrableOn fP (Set.uIcc a b) volume := by rw [huIcc]; exact hfP_Icc
  have hprimMint : IntervalIntegrable (fun z => ∫ t in a..z, fM t) volume a b :=
    (intervalIntegral.continuousOn_primitive_interval hfM_uIcc).intervalIntegrable
  have hprimPint : IntervalIntegrable (fun z => ∫ t in z..b, fP t) volume a b :=
    (intervalIntegral.continuousOn_primitive_interval_left hfP_uIcc).intervalIntegrable
  -- continuity of the running integrals (with the `b`-end resp. `a`-end fixed)
  have hQMcont : ContinuousOn (fun t => ∫ z in t..b, GM z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left hGM_uIcc
  have hQMcontR : ContinuousOn (fun t => ∫ z in t..b, RM z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left hRM_uIcc
  have hQPcont : ContinuousOn (fun t => ∫ z in a..t, GP z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval hGP_uIcc
  have hQPcontR : ContinuousOn (fun t => ∫ z in a..t, RP z) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval hRP_uIcc
  -- ## 4. `A` and `Bz` are continuous
  have hAB := Work.FTS.H2.ModalSolR.RGWeak.AB_continuous hα hα1 m hc hcm ha hable
  have hAc : ContinuousOn A (Set.Icc a b) := by rw [hA]; exact hAB.1
  have hBc : ContinuousOn Bz (Set.Icc a b) := by rw [hB]; exact hAB.2
  have hAGM_int : IntervalIntegrable (fun z => A z * GM z) volume a b :=
    (hAc.mul hGMcontI).intervalIntegrable_of_Icc hable
  have hBGP_int : IntervalIntegrable (fun z => Bz z * GP z) volume a b :=
    (hBc.mul hGPcontI).intervalIntegrable_of_Icc hable
  have hARM_int : IntervalIntegrable (fun z => A z * RM z) volume a b :=
    (hAc.mul hRMcontI).intervalIntegrable_of_Icc hable
  have hBRP_int : IntervalIntegrable (fun z => Bz z * RP z) volume a b :=
    (hBc.mul hRPcontI).intervalIntegrable_of_Icc hable
  -- the Fgen values at the two endpoints of the support interval
  have hFa : Fgen α (sM α m) ψ a = 0 :=
    Fgen_eq_zero (hvan a (by simp [Set.mem_Ioo])).1 (hvan a (by simp [Set.mem_Ioo])).2.1
  have hFb : Fgen α (sP α m) ψ b = 0 :=
    Fgen_eq_zero (hvan b (by simp [Set.mem_Ioo])).1 (hvan b (by simp [Set.mem_Ioo])).2.1
  -- ## 5. splitting `A` and `Bz`
  have hA_split : ∀ z ∈ Set.Icc a b, A z = A a + ∫ t in a..z, fM t := by
    intro z hz
    simp only [hA, hfM]
    have hb : 0 < b := lt_of_lt_of_le ha hable
    have h1 : IntervalIntegrable (srcM α m c) volume 0 a := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le ha.le]
      exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb).mono_set
        (fun t ht => ⟨ht.1, le_trans ht.2 hable⟩)
    have h2 : IntervalIntegrable (srcM α m c) volume a z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.1]
      exact (Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb).mono_set
        (fun t ht => ⟨lt_of_lt_of_le ha ht.1.le, le_trans ht.2 hz.2⟩)
    have h3 := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [h3]
  have hB_split : ∀ z ∈ Set.Icc a b, Bz z = Bz b + ∫ t in z..b, fP t := by
    intro z hz
    simp only [hB, hfP]
    have hdisj : Disjoint (Set.Ioi b) (Set.Ioc z b) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht2.2 (not_le.mpr ht1)
    have hunion : Set.Ioi b ∪ Set.Ioc z b = Set.Ioi z := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro (h | h)
        · exact lt_of_le_of_lt hz.2 h
        · exact h.1
      · intro ht
        by_cases h : t ≤ b
        · exact Or.inr ⟨ht, h⟩
        · exact Or.inl (lt_of_not_ge h)
    have hb_int : IntegrableOn (srcP α m c) (Set.Ioi b) volume :=
      (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
        (fun t ht => lt_of_le_of_lt hable ht)
    have hz_int : IntegrableOn (srcP α m c) (Set.Ioc z b) volume :=
      (Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha).mono_set
        (fun t ht => lt_of_le_of_lt hz.1 ht.1)
    have hsum := setIntegral_union hdisj measurableSet_Ioc hb_int hz_int
    rw [← hunion, hsum, ← intervalIntegral.integral_of_le hz.2]
  -- ## 6. the four integration-by-parts / Fubini identities
  have hFubiniM : ∫ z in a..b, A z * GM z
      = A a * (∫ z in a..b, GM z) + ∫ t in a..b, fM t * (∫ z in t..b, GM z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, A z * GM z = (A a + ∫ t in a..z, fM t) * GM z := by
      intro z hz
      rw [hA_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => A a * GM z) (g := fun z => (∫ t in a..z, fM t) * GM z)
      (hGMint.const_mul (A a)) (hprimMint.mul_continuousOn hGMcontU)
    rw [show (fun z => (A a + ∫ t in a..z, fM t) * GM z)
        = fun z => A a * GM z + (∫ t in a..z, fM t) * GM z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_left hable hfM_int hGMint]
  have hFubiniP : ∫ z in a..b, Bz z * GP z
      = Bz b * (∫ z in a..b, GP z) + ∫ t in a..b, fP t * (∫ z in a..t, GP z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, Bz z * GP z = (Bz b + ∫ t in z..b, fP t) * GP z := by
      intro z hz
      rw [hB_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => Bz b * GP z) (g := fun z => (∫ t in z..b, fP t) * GP z)
      (hGPint.const_mul (Bz b)) (hprimPint.mul_continuousOn hGPcontU)
    rw [show (fun z => (Bz b + ∫ t in z..b, fP t) * GP z)
        = fun z => Bz b * GP z + (∫ t in z..b, fP t) * GP z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_right hable hfP_int hGPint]
  have hFubiniRM : ∫ z in a..b, A z * RM z
      = A a * (∫ z in a..b, RM z) + ∫ t in a..b, fM t * (∫ z in t..b, RM z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, A z * RM z = (A a + ∫ t in a..z, fM t) * RM z := by
      intro z hz
      rw [hA_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => A a * RM z) (g := fun z => (∫ t in a..z, fM t) * RM z)
      (hRMint.const_mul (A a)) (hprimMint.mul_continuousOn hRMcontU)
    rw [show (fun z => (A a + ∫ t in a..z, fM t) * RM z)
        = fun z => A a * RM z + (∫ t in a..z, fM t) * RM z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_left hable hfM_int hRMint]
  have hFubiniRP : ∫ z in a..b, Bz z * RP z
      = Bz b * (∫ z in a..b, RP z) + ∫ t in a..b, fP t * (∫ z in a..t, RP z) := by
    have hsplitpt : ∀ z ∈ Set.Icc a b, Bz z * RP z = (Bz b + ∫ t in z..b, fP t) * RP z := by
      intro z hz
      rw [hB_split z hz]
    rw [intervalIntegral.integral_congr (fun z hz => hsplitpt z (huIcc ▸ hz))]
    have h2 := intervalIntegral.integral_add
      (f := fun z => Bz b * RP z) (g := fun z => (∫ t in z..b, fP t) * RP z)
      (hRPint.const_mul (Bz b)) (hprimPint.mul_continuousOn hRPcontU)
    rw [show (fun z => (Bz b + ∫ t in z..b, fP t) * RP z)
        = fun z => Bz b * RP z + (∫ t in z..b, fP t) * RP z from by funext z; ring]
    rw [h2, intervalIntegral.integral_const_mul]
    rw [Work.EllipticEst.ModalSolution.RGW.primitive_mul_right hable hfP_int hRPint]
  -- ## 7. the endpoint values of the Lagrange antiderivative
  have hB1 : ∫ z in a..b, GM z = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..b, RM z) := by
    have h := Work.FTS.H2.ModalSolR.RGWeak.qm_formula hα m hψ ha hable hvan2 a ⟨le_rfl, hable⟩
    rw [hFa, add_zero] at h
    simpa only [hGM, hRM] using h
  have hB2 : ∫ z in a..b, GP z = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..b, RP z) := by
    have h := Work.FTS.H2.ModalSolR.RGWeak.qp_formula hα m hψ ha hable hvan2 b ⟨hable, le_rfl⟩
    rw [hFb, sub_zero] at h
    simpa only [hGP, hRP] using h
  -- ## 8. the two remaining running-integral identities
  have hC1 : ∫ t in a..b, fM t * (∫ z in t..b, GM z)
      = - Work.FTS.PhiStar.Radial.lamR m * (∫ t in a..b, fM t * (∫ z in t..b, RM z))
        + ∫ t in a..b, fM t * Fgen α (sM α m) ψ t := by
    have hcongr : ∫ t in a..b, fM t * (∫ z in t..b, GM z)
        = ∫ t in a..b,
            (-(Work.FTS.PhiStar.Radial.lamR m) * (fM t * (∫ z in t..b, RM z))
              + fM t * Fgen α (sM α m) ψ t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have h := Work.FTS.H2.ModalSolR.RGWeak.qm_formula hα m hψ ha hable hvan2 t ht
      have h' : (∫ z in t..b, GM z)
          = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in t..b, RM z)
            + Fgen α (sM α m) ψ t := by
        simpa only [hGM, hRM] using h
      rw [h']
      ring
    rw [hcongr]
    have h1 := (hfM_int.mul_continuousOn hQMcontR).const_mul (-(Work.FTS.PhiStar.Radial.lamR m))
    have h2 := hfM_int.mul_continuousOn hFgenMcontU
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  have hC2 : ∫ t in a..b, fP t * (∫ z in a..t, GP z)
      = - Work.FTS.PhiStar.Radial.lamR m * (∫ t in a..b, fP t * (∫ z in a..t, RP z))
        - ∫ t in a..b, fP t * Fgen α (sP α m) ψ t := by
    have hcongr : ∫ t in a..b, fP t * (∫ z in a..t, GP z)
        = ∫ t in a..b,
            (-(Work.FTS.PhiStar.Radial.lamR m) * (fP t * (∫ z in a..t, RP z))
              - fP t * Fgen α (sP α m) ψ t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have h := Work.FTS.H2.ModalSolR.RGWeak.qp_formula hα m hψ ha hable hvan2 t ht
      have h' : (∫ z in a..t, GP z)
          = - Work.FTS.PhiStar.Radial.lamR m * (∫ z in a..t, RP z)
            - Fgen α (sP α m) ψ t := by
        simpa only [hGP, hRP] using h
      rw [h']
      ring
    rw [hcongr]
    have h1 := (hfP_int.mul_continuousOn hQPcontR).const_mul (-(Work.FTS.PhiStar.Radial.lamR m))
    have h2 := hfP_int.mul_continuousOn hFgenPcontU
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  -- ## 9. the pointwise cancellation of the source terms
  have hD : (∫ t in a..b, fM t * Fgen α (sM α m) ψ t)
        - (∫ t in a..b, fP t * Fgen α (sP α m) ψ t)
      = ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
    have h1 := hfM_int.mul_continuousOn hFgenMcontU
    have h2 := hfP_int.mul_continuousOn hFgenPcontU
    have hsub := intervalIntegral.integral_sub
      (f := fun t => fM t * Fgen α (sM α m) ψ t)
      (g := fun t => fP t * Fgen α (sP α m) ψ t) h1 h2
    have hcongr : ∫ t in a..b, (fM t * Fgen α (sM α m) ψ t - fP t * Fgen α (sP α m) ψ t)
        = ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le hable] at ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      have h := Work.FTS.H2.ModalSolR.RGWeak.Fgen_algebra hα m (c := c) (ψ := ψ) t ht0
      simpa only [hfM, hfP] using h
    exact hsub.symm.trans hcongr
  have hE : ∫ t in a..b, α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t)
      = α * (4 * (m : ℝ) + 5) * (∫ t in a..b, c t * ψ t * wgt α t) := by
    rw [intervalIntegral.integral_const_mul]
  -- ## 10. the middle identity
  have hmid : (A a * (∫ z in a..b, GM z) + ∫ t in a..b, fM t * (∫ z in t..b, GM z))
        + (Bz b * (∫ z in a..b, GP z) + ∫ t in a..b, fP t * (∫ z in a..t, GP z))
        + Work.FTS.PhiStar.Radial.lamR m
          * ((A a * (∫ z in a..b, RM z) + ∫ t in a..b, fM t * (∫ z in t..b, RM z))
            + (Bz b * (∫ z in a..b, RP z) + ∫ t in a..b, fP t * (∫ z in a..t, RP z)))
      = (∫ t in a..b, fM t * Fgen α (sM α m) ψ t)
        - (∫ t in a..b, fP t * Fgen α (sP α m) ψ t) := by
    rw [hB1, hB2, hC1, hC2]
    ring
  -- ## 11. the crux
  have hcrux : ((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
        + Work.FTS.PhiStar.Radial.lamR m
          * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z))
      = α * (4 * (m : ℝ) + 5) * (∫ t in a..b, c t * ψ t * wgt α t) := by
    rw [hFubiniM, hFubiniP, hFubiniRM, hFubiniRP]
    exact hmid.trans (by rw [hD, hE])
  -- ## 12. rewriting the `radGreen` integrals
  have hT1 : ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
      = (1 / (α * (4 * (m : ℝ) + 5)))
        * ((∫ z in a..b, A z * GM z) + ∫ z in a..b, Bz z * GP z) := by
    have h1 : ∀ z ∈ Set.Icc a b,
        Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
          = (1 / (α * (4 * (m : ℝ) + 5))) * (A z * GM z + Bz z * GP z) := by
      intro z hz
      rw [Work.EllipticEst.ModalSolution.RadGreenWeak.radGreen_eq, hA, hB, hGM, hGP]
      ring
    rw [intervalIntegral.integral_congr (fun z hz => h1 z (huIcc ▸ hz)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hAGM_int hBGP_int]
  have hT2 : ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z
      = (1 / (α * (4 * (m : ℝ) + 5)))
        * ((∫ z in a..b, A z * RM z) + ∫ z in a..b, Bz z * RP z) := by
    have h1 : ∀ z ∈ Set.Icc a b,
        Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z
          = (1 / (α * (4 * (m : ℝ) + 5))) * (A z * RM z + Bz z * RP z) := by
      intro z hz
      rw [Work.EllipticEst.ModalSolution.RadGreenWeak.radGreen_eq, hA, hB, hRM, hRP]
      ring
    rw [intervalIntegral.integral_congr (fun z hz => h1 z (huIcc ▸ hz)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hARM_int hBRP_int]
  -- ## 13. the interval form of the identity
  have hmain : (∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z)
        + Work.FTS.PhiStar.Radial.lamR m
          * (∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z)
      = ∫ z in a..b, c z * ψ z * wgt α z := by
    rw [hT1, hT2]
    have hK : (1 / (α * (4 * (m : ℝ) + 5))) * (α * (4 * (m : ℝ) + 5)) = 1 := by
      field_simp
    rw [show (1 / (α * (4 * (m : ℝ) + 5)))
            * ((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
          + Work.FTS.PhiStar.Radial.lamR m
            * ((1 / (α * (4 * (m : ℝ) + 5)))
              * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z)))
        = (1 / (α * (4 * (m : ℝ) + 5)))
            * (((∫ z in a..b, A z * GM z) + (∫ z in a..b, Bz z * GP z))
              + Work.FTS.PhiStar.Radial.lamR m
                * ((∫ z in a..b, A z * RM z) + (∫ z in a..b, Bz z * RP z))) from by ring]
    rw [hcrux, ← mul_assoc, hK, one_mul]
  -- ## 14. reduction of the original half-line integrals
  have hI1 : (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
        (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
        * z ^ ((5 - α) / α))
      = ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z := by
    rw [show (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z *
            (-(α ^ 2) * z ^ 2 * deriv (deriv ψ) z - (α * (5 + α) * z) * deriv ψ z)
            * z ^ ((5 - α) / α))
        = ∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z * Lneg α ψ z * wgt α z
        from setIntegral_congr_fun measurableSet_Ioi (fun z _ => by
          simp only [Lneg, wgt, qW]
          ring)]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, h1, h2⟩ := hvan z hz
      simp only [Lneg, h0, h1, h2]
      ring)
  have hI2 : (∫ z in Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z
        * z ^ ((5 - α) / α))
      = ∫ z in a..b, Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z := by
    rw [show (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * z ^ ((5 - α) / α))
        = fun z => Work.FTS.PhiStar.Radial.radGreen α m c z * ψ z * wgt α z from by
          funext z; simp only [wgt, qW]]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, -⟩ := hvan z hz
      simp only [h0, mul_zero, zero_mul])
  have hI3 : (∫ z in Set.Ioi 0, c z * ψ z * z ^ ((5 - α) / α))
      = ∫ z in a..b, c z * ψ z * wgt α z := by
    rw [show (fun z => c z * ψ z * z ^ ((5 - α) / α))
        = fun z => c z * ψ z * wgt α z from by funext z; simp only [wgt, qW]]
    exact integral_Ioi_eq_intervalIntegral ha hable (fun z hz => by
      obtain ⟨h0, -⟩ := hvan z hz
      simp only [h0, mul_zero, zero_mul])
  rw [hI1, hI2, hI3]
  exact hmain

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.Dzu_radGreen_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- If `f` vanishes off the closed interval `[a,b]`, then so does `deriv f`: the complement of
`[a,b]` is open, so `f` is *eventually* `0` near every point of it. -/
theorem deriv_eq_zero_of_notMem_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    ∀ t : ℝ, t ∉ Set.Icc a b → deriv f t = 0 := by
  intro t ht
  have hcompl : t ∈ (Set.Icc a b)ᶜ := ht
  have hev : f =ᶠ[𝓝 t] 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hcompl] with s hs
    exact hsupp s hs
  rw [hev.deriv_eq]
  simp

/-- A function continuous on `(0,∞)` and supported in `[a,b]` with `0 < a` gives an integrable
function after multiplication with any real power `t^s`: the product is continuous on the
compact set `[a,b] ⊆ (0,∞)` and vanishes outside it. -/
theorem integrable_mul_rpow_of_support {f : ℝ → ℝ} {a b s : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    Integrable (fun t : ℝ => f t * t ^ s) := by
  have hg : ContinuousOn (fun t : ℝ => f t * t ^ s) (Set.Icc a b) := by
    have h1 : ContinuousOn f (Set.Icc a b) := hf.mono (fun t ht => lt_of_lt_of_le ha ht.1)
    have h2 : ContinuousOn (fun t : ℝ => t ^ s) (Set.Icc a b) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))
    exact h1.mul h2
  have hI : IntegrableOn (fun t : ℝ => f t * t ^ s) (Set.Icc a b) :=
    hg.integrableOn_compact isCompact_Icc
  have hind : (Set.Icc a b).indicator (fun t : ℝ => f t * t ^ s) = fun t => f t * t ^ s := by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht, hsupp t ht]
  rw [← hind]
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).2 hI

/-- The compact support of `c` propagates to every iterated `Dzu`-derivative: `Dzu n c` vanishes
off `[a,b]` as well. -/
theorem Dzu_eq_zero_of_support {c : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ (n : ℕ) (t : ℝ), t ∉ Set.Icc a b → Work.FTS.EllExist.Honesty.Dzu n c t = 0 := by
  intro n
  induction n with
  | zero => intro t ht; exact hsupp t ht
  | succ k ih =>
      intro t ht
      simp only [Work.FTS.EllExist.Honesty.Dzu_succ]
      rw [deriv_eq_zero_of_notMem_Icc (f := Work.FTS.EllExist.Honesty.Dzu k c) ih t ht, mul_zero]

/-- **`radGreen_Dz` with the four integrability hypotheses discharged from compact support.**
For `f` of class `C^1` on `(0,∞)`, with `t ↦ t ∂_t f t` also `C^1` there, and `f` supported in
`[a,b]` (`0 < a`),

  `z ∂_z (radGreen α m f) z = radGreen α m (z ∂_z f) z`   for `z > 0`. -/
theorem radGreen_Dz_support {α : ℝ} (hα : 0 < α) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf1 : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (hf2 : ContDiffOn ℝ 1 (fun t : ℝ => t * deriv f t) (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m f) z
        = Work.FTS.PhiStar.Radial.radGreen α m (fun t => t * deriv f t) z := by
  have hd0 := deriv_eq_zero_of_notMem_Icc hsupp
  have hsupp' : ∀ t : ℝ, t ∉ Set.Icc a b → t * deriv f t = 0 := by
    intro t ht
    rw [hd0 t ht, mul_zero]
  have hcont : ContinuousOn (fun t : ℝ => t * deriv f t) (Set.Ioi 0) := hf2.continuousOn
  have hcd : ∀ t : ℝ, 0 < t → HasDerivAt f (deriv f t) t := by
    intro t ht
    have hd : DifferentiableAt ℝ f t :=
      (hf1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds ht)
    exact hd.hasDerivAt
  have h0 : IntegrableOn (fun t : ℝ => f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hf1.continuousOn hsupp).integrableOn
  have hinf : IntegrableOn (fun t : ℝ => f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hf1.continuousOn hsupp).integrableOn
  have hd0' : IntegrableOn
      (fun t : ℝ => t * deriv f t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hcont hsupp').integrableOn
  have hdinf : IntegrableOn
      (fun t : ℝ => t * deriv f t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hcont hsupp').integrableOn
  exact Work.FTS.ClassCHon.Zpz.radGreen_Dz hα m hcd h0 hinf hd0' hdinf

/-- The induction behind `Dzu_radGreen_comm`, stated with the smoothness order `M` of `c` as a
free parameter (so that the induction hypothesis can be applied at the lower order `M`, which is
all the step for `n` needs). -/
theorem dzu_radGreen_comm_aux {α : ℝ} (hα : 0 < α) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    {c : ℝ → ℝ} (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ (n : ℕ) (M : WithTop ℕ∞), ((n + 1 : ℕ) : WithTop ℕ∞) ≤ M →
      ContDiffOn ℝ M c (Set.Ioi 0) →
      ∀ z : ℝ, 0 < z →
        Work.FTS.EllExist.Honesty.Dzu n (Work.FTS.PhiStar.Radial.radGreen α m c) z
          = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu n c) z := by
  intro n
  induction n with
  | zero =>
      intro M _ _ z _
      simp [Work.FTS.EllExist.Honesty.Dzu_zero]
  | succ n ih =>
      intro M hM hc z hz
      have hM' : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ M := by
        refine le_trans ?_ hM
        exact_mod_cast (by omega : n + 1 ≤ n + 2)
      have hrec : ∀ w : ℝ, 0 < w →
          Work.FTS.EllExist.Honesty.Dzu n (Work.FTS.PhiStar.Radial.radGreen α m c) w
            = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu n c) w :=
        ih M hM' hc
      -- `Dzu n c` is `C^1` on `(0,∞)` (the iterate of a `C^{n+2}` function)
      have hf1 : ContDiffOn ℝ 1 (Work.FTS.EllExist.Honesty.Dzu n c) (Set.Ioi 0) := by
        refine Work.FTS.EllExist.Honesty.contDiffOn_Dzu c n 1 ?_
        refine hc.of_le ?_
        have hcast : ((1 : WithTop ℕ∞) + (n : WithTop ℕ∞)) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
          push_cast
          ring
        rw [hcast]
        exact hM'
      -- and so is `t ↦ t ∂_t (Dzu n c) t = Dzu (n+1) c t`
      have hf2 : ContDiffOn ℝ 1 (fun t : ℝ => t * deriv (Work.FTS.EllExist.Honesty.Dzu n c) t)
          (Set.Ioi 0) := by
        rw [← Work.FTS.EllExist.Honesty.Dzu_succ n c]
        refine Work.FTS.EllExist.Honesty.contDiffOn_Dzu c (n + 1) 1 ?_
        refine hc.of_le ?_
        have hcast : ((1 : WithTop ℕ∞) + ((n + 1 : ℕ) : WithTop ℕ∞))
            = ((n + 2 : ℕ) : WithTop ℕ∞) := by
          push_cast
          ring
        rw [hcast]
        exact hM
      have hsupn := Dzu_eq_zero_of_support hsupp n
      have hstep := radGreen_Dz_support (a := a) (b := b) hα m ha hf1 hf2 hsupn z hz
      -- the induction hypothesis identifies the two functions on the neighbourhood `(0,∞)`
      have hderiv : deriv (Work.FTS.EllExist.Honesty.Dzu n
            (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          = deriv (Work.FTS.PhiStar.Radial.radGreen α m
            (Work.FTS.EllExist.Honesty.Dzu n c)) z := by
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hrec w hw
      calc Work.FTS.EllExist.Honesty.Dzu (n + 1)
              (Work.FTS.PhiStar.Radial.radGreen α m c) z
          = z * deriv (Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.EllExist.Honesty.Dzu n c)) z := by
            simp only [Work.FTS.EllExist.Honesty.Dzu_succ, hderiv]
        _ = Work.FTS.PhiStar.Radial.radGreen α m
              (fun t => t * deriv (Work.FTS.EllExist.Honesty.Dzu n c) t) z := hstep
        _ = Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.EllExist.Honesty.Dzu (n + 1) c) z := by
            rw [Work.FTS.EllExist.Honesty.Dzu_succ]

theorem Dzu_radGreen_comm {α : ℝ} (hα : 0 < α) (m l : ℕ) {c : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hc : ContDiffOn ℝ (l + 1 : ℕ) c (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.Honesty.Dzu l (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu l c) z :=
  dzu_radGreen_comm_aux hα m ha hsupp l ((l + 1 : ℕ) : WithTop ℕ∞) le_rfl hc

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_Lzero1_mul_cos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory



end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the `σ_η`-weighted slice mass on `(1,∞)`

At level `0` the `H^k`-integrand of `Work.Spaces.HkMem α 0 F` collapses to the single square

    `HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})²`,

which on the angular interval is *literally* the weighted slice mass of `F`,

    `HkIntegrand α 0 F z θ = w z² · ((F z θ)² · sin(2θ)^{-η})`   (`AngSecond.sq_mul_W`).

Hence, for `z ∈ (1,∞)` (where `w z = (1+z)²/z² ≥ 1`), the honest `θ`-slice

    `z ↦ ∫_θ (F z θ)² sin(2θ)^{-η}`

is the slice mass of the `H^k`-integrand divided by `w z²`, and `HkMem α 0 F` says exactly that
the latter is integrable on `Iz ⊇ (1,∞)`.  Dividing by `w z² ≥ 1` cannot destroy integrability, so
the `σ_η`-weighted slice mass is integrable on `(1,∞)`.

The only two things that have to be checked besides the pointwise identity are (a) the measurability
of `z ↦ ∫_θ (F z θ)² sin(2θ)^{-η}` on `(1,∞)` — which is *not* part of `HkMem`, but follows from
the identity above and the a.e. strong measurability of the (integrable) `Iθ`-integral `h`, and
(b) the pointwise bound `‖G z‖ ≤ h z`, i.e. nonnegativity of the slice mass and `w z² ≥ 1`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Filter

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq_prv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- On `[1,∞)` the radial weight is at least `1`: `w z = ((1+z)/z)² ≥ 1`. -/
private lemma one_le_w_sq {z : ℝ} (hz : 1 ≤ z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w z := by
    change 1 ≤ (1 + z) ^ 2 / z ^ 2
    rw [one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  nlinarith [h1]

theorem integrableOn_sliceMass_Ioi_one_of_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 0 F) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioi 1) := by
  classical
  -- The `σ_η`-weighted slice mass `G` and the `H^k`-slice mass `h`.
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hG
  set h : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ with hh
  set W2 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 with hW2
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The two integrands agree on the angular interval, up to the factor `w z²`.
  have hpt : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 F z θ
        = (Work.Spaces.w z) ^ 2
          * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z θ hθ
    rw [HkIntegrand_zero_eq_prv α F z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
    simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig, sq]
    ring
  -- Hence the slice identity `h z = w z² · G z`.
  have hslice : ∀ z, h z = W2 z * G z := by
    intro z
    simp only [hh, hG, hW2]
    rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from
      setIntegral_congr_fun hIθ (fun θ hθ => hpt z θ hθ)]
    rw [MeasureTheory.integral_const_mul]
  -- `h` is integrable on `(1,∞)`, being the `H^k`-outer integral restricted to a subset of `Iz`.
  have hInt_h : IntegrableOn h (Set.Ioi 1) := by
    exact hF.2.mono_set (show Set.Ioi 1 ⊆ Work.Spaces.Iz from
      fun z hz => (le_trans (by norm_num) (le_of_lt hz) : (0 : ℝ) ≤ z))
  -- Measurability of the radial factor `w z²`.
  have hmeas_w : Measurable Work.Spaces.w := by
    change Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
    fun_prop
  have hmeasW : AEStronglyMeasurable W2 (volume.restrict (Set.Ioi 1)) := by
    have : Measurable W2 := by
      simpa only [hW2] using hmeas_w.pow_const 2
    exact this.aestronglyMeasurable
  -- Measurability of `G` on `(1,∞)`: it agrees there with `h / w z²`.
  have hmeasG : AEStronglyMeasurable G (volume.restrict (Set.Ioi 1)) := by
    have hd : AEMeasurable (fun z => h z / W2 z) (volume.restrict (Set.Ioi 1)) :=
      hInt_h.aemeasurable.div hmeasW.aemeasurable
    refine hd.aestronglyMeasurable.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => by
      have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
      have hw2 : W2 z ≠ 0 := by
        have := one_le_w_sq hz1
        linarith
      change h z / W2 z = G z
      rw [hslice z]
      field_simp
  -- The pointwise domination `‖G z‖ ≤ h z` on `(1,∞)`, since `w z² ≥ 1` and `G z ≥ 0`.
  have hbound : ∀ᵐ z ∂(volume.restrict (Set.Ioi 1)), ‖G z‖ ≤ h z := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have hw2 : 1 ≤ W2 z := one_le_w_sq hz1
    have hgnn : 0 ≤ G z := by
      show 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      exact setIntegral_nonneg hIθ fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _)
    have hhnn : 0 ≤ h z := by
      show 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ
      exact setIntegral_nonneg hIθ fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 F z θ
    have hGeq : G z = h z / W2 z := by
      have hz0 : W2 z ≠ 0 := by linarith
      rw [hslice z, mul_div_cancel_left₀ _ hz0]
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn, hGeq]
    exact div_le_self hhnn hw2
  exact Integrable.mono' hInt_h hmeasG hbound

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_tendsto_of_weightedL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radGreen_tendsto_of_weightedL2`

For fixed `z > 0` the radial Green function `radGreen α m c z` is *continuous in the source*
`c` with respect to the two weighted `L²` norms

  `c ↦ ∫_{(0,1)} c²/t⁴`,      `c ↦ ∫_{(1,∞)} c²`.

The value bound rests on two Cauchy–Schwarz estimates (proved in the sibling modules
`WeightedL2Aux.rgA_sq_le`, `WeightedL2Aux.rgB_sq_le`):

  `(rgA α m d z)² ≤ ((Ad) + (Bd))·z^{2q+3}/(2q+3)`,
  `(rgB α m d z)² ≤ ((Ad) + (Bd))·z^{-2p-1}/(2p+1)`,

with `q = rgQ α m ≥ 28`, `p = rgP α m ≥ 8` and
`Ad = ∫_{(0,1)} d²/t⁴`, `Bd = ∫_{(1,∞)} d²`.  Together with the *junk-robust* linearity
`|∫_s f - ∫_s g| ≤ |∫_s (f-g)|` (`WeightedL2Aux.integral_sub_abs_le`) this gives

  `|radGreen α m c' z - radGreen α m c z| ≤ C(z)·(√Ad + √Bd)`,   `d = c' - c`,

whence the convergence: the two positive quantities `√(Ad n)`, `√(Bd n)` tend to `0` by
hypothesis (the integrabilities `hint1`, `hint2` are what make the Bochner integrals honest),
so the values converge.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

open Work.FTS.EllExist
open Work.FTS.PhiStar.Honesty.WeightedL2Aux

/-! ## Elementary helpers -/

/-- `AEMeasurable d` gives a.e. strong measurability of `|d|` on `(0,∞)`. -/
private lemma aesm_abs_of_aemeasurable {d : ℝ → ℝ} (hd : AEMeasurable d) :
    AEStronglyMeasurable (fun t : ℝ => |d t|) (volume.restrict (Set.Ioi 0)) := by
  exact (hd.abs.aestronglyMeasurable).restrict

/-- **Integrability of the tail integrand `rgF2`** on `(z,∞)` for every `z > 0`, from the two
weighted `L²` bounds and a.e. measurability of the source. -/
private lemma integrableOn_rgF2_of {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → IntegrableOn (rgF2 α m d) (Set.Ioi z) := by
  intro z hz
  have hp1 : (1 : ℝ) ≤ rgP α m := by have h := rgP_ge hα hα4 hm; linarith
  have hnorm : IntegrableOn (fun t : ℝ => ‖d t * t ^ (-(rgP α m) - 1)‖) (Set.Ioi z) :=
    rgB_int_Ioi hp1 hz (aesm_abs_of_aemeasurable hd) hnear hfar
  have haesm : AEStronglyMeasurable (fun t : ℝ => d t * t ^ (-(rgP α m) - 1))
      (volume.restrict (Set.Ioi z)) := by
    have h1 : AEStronglyMeasurable d (volume.restrict (Set.Ioi z)) :=
      hd.aestronglyMeasurable.restrict
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(rgP α m) - 1))
        (volume.restrict (Set.Ioi z)) :=
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))).aestronglyMeasurable
          measurableSet_Ioi)
    exact h1.mul h2
  have hmain : IntegrableOn (fun t : ℝ => d t * t ^ (-(rgP α m) - 1)) (Set.Ioi z) :=
    MeasureTheory.Integrable.mono' hnorm haesm (Filter.Eventually.of_forall (fun t => le_rfl))
  show IntegrableOn (fun t : ℝ => d t * t ^ (-(rgP α m) - 1)) (Set.Ioi z)
  exact hmain

/-- **Pointwise value bound for the difference of two radial Green functions.**  For
`d = c' - c`,

  `|radGreen α m c' z - radGreen α m c z| ≤ |rgK α m|·(z^{-q}·|rgA α m d z| + z^p·|rgB α m d z|)`.

The content is the junk-robust linearity `|∫_s f - ∫_s g| ≤ |∫_s (f - g)|`: since
`rgF1 α m d = rgF1 α m c' - rgF1 α m c` (and likewise for `rgF2`), and the left-hand integrand
is genuinely integrable on the relevant set, either both of `rgF1 α m c'`, `rgF1 α m c` are
integrable (and the difference is the integral of `rgF1 α m d`) or neither is (and both
integrals vanish). -/
private lemma radGreen_diff_bound {α : ℝ} {m : ℕ} {c c' : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c) (hc' : AEMeasurable c')
    (hnear : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c' z - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m (fun t => c' t - c t) z|
          + z ^ (rgP α m) * |rgB α m (fun t => c' t - c t) z|) := by
  set d : ℝ → ℝ := fun t => c' t - c t with hd
  have hdae : AEMeasurable d := hc'.sub hc
  have hF1 : IntegrableOn (rgF1 α m d) (Set.Ioc 0 z) :=
    rgF1_integrableOn_Ioc hα hα4 hm hdae hnear hfar z hz
  have hF2 : IntegrableOn (rgF2 α m d) (Set.Ioi z) :=
    integrableOn_rgF2_of hα hα4 hm hdae hnear hfar z hz
  -- the two integrands are the differences of the corresponding integrands of `c'` and `c`
  have hsub1 : IntegrableOn (fun t => rgF1 α m c' t - rgF1 α m c t) (Set.Ioc 0 z) :=
    MeasureTheory.Integrable.congr hF1 (Filter.Eventually.of_forall (fun t => by
      show rgF1 α m d t = rgF1 α m c' t - rgF1 α m c t
      simp only [rgF1, hd]
      ring))
  have hsub2 : IntegrableOn (fun t => rgF2 α m c' t - rgF2 α m c t) (Set.Ioi z) :=
    MeasureTheory.Integrable.congr hF2 (Filter.Eventually.of_forall (fun t => by
      show rgF2 α m d t = rgF2 α m c' t - rgF2 α m c t
      simp only [rgF2, hd]
      ring))
  have hA : |rgA α m c' z - rgA α m c z| ≤ |rgA α m d z| := by
    have e1 : rgA α m c' z = ∫ t in Set.Ioc 0 z, rgF1 α m c' t := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
    have e2 : rgA α m c z = ∫ t in Set.Ioc 0 z, rgF1 α m c t := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
    have e3 : rgA α m d z = ∫ t in Set.Ioc 0 z, (rgF1 α m c' t - rgF1 α m c t) := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
      exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
        show rgF1 α m d t = rgF1 α m c' t - rgF1 α m c t
        simp only [rgF1, hd]
        ring)
    rw [e1, e2, e3]
    exact integral_sub_abs_le hsub1
  have hB : |rgB α m c' z - rgB α m c z| ≤ |rgB α m d z| := by
    have e1 : rgB α m c' z = ∫ t in Set.Ioi z, rgF2 α m c' t := rfl
    have e2 : rgB α m c z = ∫ t in Set.Ioi z, rgF2 α m c t := rfl
    have e3 : rgB α m d z = ∫ t in Set.Ioi z, (rgF2 α m c' t - rgF2 α m c t) := by
      rw [rgB]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
        show rgF2 α m d t = rgF2 α m c' t - rgF2 α m c t
        simp only [rgF2, hd]
        ring)
    rw [e1, e2, e3]
    exact integral_sub_abs_le hsub2
  -- expand both Green values and combine
  rw [radGreen_eq, radGreen_eq]
  have hsplit : rgK α m * (z ^ (-(rgQ α m)) * rgA α m c' z + z ^ (rgP α m) * rgB α m c' z)
        - rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z)
      = rgK α m * (z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)
          + z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)) := by
    ring
  rw [hsplit, abs_mul]
  calc |rgK α m| * |z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)
          + z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)|
      ≤ |rgK α m| * (|z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)|
          + |z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m c' z - rgA α m c z|
          + z ^ (rgP α m) * |rgB α m c' z - rgB α m c z|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hz.le _),
          abs_of_nonneg (Real.rpow_nonneg hz.le _)]
    _ ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m d z| + z ^ (rgP α m) * |rgB α m d z|) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz.le _))
          (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hz.le _))) (abs_nonneg _)

/-! ## The main theorem -/

theorem radGreen_tendsto_of_weightedL2 {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c) (hc_ : ∀ n, AEMeasurable (c_ n))
    (hint1 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
      (Set.Ioo 0 1))
    (hint2 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1))
    (hconv1 : Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
      Filter.atTop (nhds 0))
    (hconv2 : Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
      Filter.atTop (nhds 0)) :
    ∀ z : ℝ, 0 < z → Filter.Tendsto (fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z)
      Filter.atTop (nhds (Work.FTS.PhiStar.Radial.radGreen α m c z)) := by
  intro z hz
  set d : ℕ → ℝ → ℝ := fun n t => c_ n t - c t with hd
  have hdae : ∀ n, AEMeasurable (d n) := fun n => (hc_ n).sub hc
  set Ad : ℕ → ℝ := fun n => ∫ t in Set.Ioo (0:ℝ) 1, (d n t) ^ 2 / t ^ 4 with hAd
  set Bd : ℕ → ℝ := fun n => ∫ t in Set.Ioi (1:ℝ), (d n t) ^ 2 with hBd
  have hAdnn : ∀ n, 0 ≤ Ad n := fun n =>
    setIntegral_nonneg measurableSet_Ioo (fun t _ => div_nonneg (sq_nonneg _) (by positivity))
  have hBdnn : ∀ n, 0 ≤ Bd n := fun n =>
    setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
  have hAdc : Filter.Tendsto Ad Filter.atTop (nhds 0) := by
    simpa only [hAd, hd] using hconv1
  have hBdc : Filter.Tendsto Bd Filter.atTop (nhds 0) := by
    simpa only [hBd, hd] using hconv2
  -- the sequence of `√` of the two masses tends to zero
  have hSc : Filter.Tendsto (fun n => Real.sqrt (Ad n) + Real.sqrt (Bd n))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => Real.sqrt (Ad n)) Filter.atTop (nhds 0) := by
      have h := hAdc.sqrt
      rwa [Real.sqrt_zero] at h
    have h2 : Filter.Tendsto (fun n => Real.sqrt (Bd n)) Filter.atTop (nhds 0) := by
      have h := hBdc.sqrt
      rwa [Real.sqrt_zero] at h
    simpa using h1.add h2
  -- the constant of the value bound
  have hCnn : 0 ≤ z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
      + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1) := by
    have h1 : 0 ≤ z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3) := by positivity
    have h2 : 0 ≤ z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1) := by positivity
    linarith
  -- the pointwise bound
  have hbd : ∀ n, |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
        - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)))
        * (Real.sqrt (Ad n) + Real.sqrt (Bd n)) := by
    intro n
    have hd1 : IntegrableOn (fun t : ℝ => (d n t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
      simpa only [hd] using hint1 n
    have hd2 : IntegrableOn (fun t : ℝ => (d n t) ^ 2) (Set.Ioi 1) := by
      simpa only [hd] using hint2 n
    have hdiff := radGreen_diff_bound (c := c) (c' := c_ n) hα hα4 hm hc (hc_ n)
      (by simpa only [hd] using hint1 n) (by simpa only [hd] using hint2 n) hz
    have hnear2 := rgA_sq_le hα hα4 hm (hdae n) hd1 hd2 hz
    have hfar2 := rgB_sq_le hα hα4 hm (hdae n) hd1 hd2 hz
    have hGnn : 0 ≤ Ad n + Bd n := add_nonneg (hAdnn n) (hBdnn n)
    -- the near half
    have hA' : z ^ (-(rgQ α m)) * |rgA α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)) := by
      have hsq : Real.sqrt ((rgA α m (d n) z) ^ 2)
          ≤ Real.sqrt ((Ad n + Bd n) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3))) :=
        Real.sqrt_le_sqrt hnear2
      rw [Real.sqrt_sq_eq_abs] at hsq
      have hstep := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz.le (-(rgQ α m)))
      have hpow : z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2) = z ^ ((3:ℝ)/2) := by
        rw [← Real.rpow_add hz]
        congr 1
        ring
      have hsqz : Real.sqrt (z ^ (2 * rgQ α m + 3)) = z ^ (rgQ α m + 3 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
        congr 1
        ring
      have hval : z ^ (-(rgQ α m))
            * Real.sqrt ((Ad n + Bd n) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)))
          = Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)) := by
        rw [Real.sqrt_mul hGnn, Real.sqrt_div (Real.rpow_nonneg hz.le _), hsqz, ← hpow]
        ring
      rwa [hval] at hstep
    -- the far half
    have hB' : z ^ (rgP α m) * |rgB α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
      have hsq : Real.sqrt ((rgB α m (d n) z) ^ 2)
          ≤ Real.sqrt ((Ad n + Bd n) * (z ^ (-(2 * rgP α m) - 1) / (2 * rgP α m + 1))) :=
        Real.sqrt_le_sqrt hfar2
      rw [Real.sqrt_sq_eq_abs] at hsq
      have hstep := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz.le (rgP α m))
      have hpow : z ^ (rgP α m) * z ^ (-(rgP α m) - 1 / 2) = z ^ (-(1:ℝ)/2) := by
        rw [← Real.rpow_add hz]
        congr 1
        ring
      have hsqz : Real.sqrt (z ^ (-(2 * rgP α m) - 1)) = z ^ (-(rgP α m) - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
        congr 1
        ring
      have hval : z ^ (rgP α m)
            * Real.sqrt ((Ad n + Bd n) * (z ^ (-(2 * rgP α m) - 1) / (2 * rgP α m + 1)))
          = Real.sqrt (Ad n + Bd n) * (z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
        rw [Real.sqrt_mul hGnn, Real.sqrt_div (Real.rpow_nonneg hz.le _), hsqz, ← hpow]
        ring
      rwa [hval] at hstep
    -- combine
    have hmid : z ^ (-(rgQ α m)) * |rgA α m (d n) z| + z ^ (rgP α m) * |rgB α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
      refine le_trans (add_le_add hA' hB') (le_of_eq ?_)
      ring
    have hsqrt := sqrt_add_le (hAdnn n) (hBdnn n)
    calc |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
          - Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m (d n) z|
            + z ^ (rgP α m) * |rgB α m (d n) z|) := hdiff
      _ ≤ |rgK α m| * (Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) :=
          mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
      _ ≤ |rgK α m| * ((Real.sqrt (Ad n) + Real.sqrt (Bd n))
            * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
              + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt hCnn) (abs_nonneg _)
      _ = (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)))
          * (Real.sqrt (Ad n) + Real.sqrt (Bd n)) := by
          ring
  -- squeeze
  have hlimC : Filter.Tendsto (fun n => (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
      + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) * (Real.sqrt (Ad n) + Real.sqrt (Bd n)))
      Filter.atTop (nhds 0) := by
    simpa using hSc.const_mul _
  have habs : Filter.Tendsto (fun n => |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => hbd n) hlimC
  have hsub : Filter.Tendsto (fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  have h3 := hsub.add_const (Work.FTS.PhiStar.Radial.radGreen α m c z)
  have heq : (fun n => (Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z) + Work.FTS.PhiStar.Radial.radGreen α m c z)
      = fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z := by
    funext n
    ring
  rw [heq] at h3
  simpa using h3

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG1_lintegral_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

/-- **`lintegral` bound for the far-field square of the decaying Green branch.**

The pointwise bound `rgG1_pt_bound`, the Cauchy–Schwarz/Tonelli computation
`∫_1^∞ z^{-q} ∫_1^z (c t)² t^{q-1} dt dz = (1/(q-1)) ∫_1^∞ (c t)² dt` (Taubinian swap
`lintegral_tail_swap_Ioi_one`, evaluation `lintegral_ofReal_rpow_Ioi`), and the `ofReal`
identification `ofReal_integral_rpow_mul_sq_eq_lintegral` combine to give the stated bound. -/
theorem rgG1_lintegral_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≤ ENNReal.ofReal (2 * (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t) ^ 2
            / (2 * Work.FTS.EllExist.rgQ α m - 1)
          + 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hqm1 : 0 < Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have h2qm1 : 0 < 2 * Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  set A0 : ℝ := ∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t with hA0
  set KK : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)
    with hKK
  have hpt : ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))
          + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
    intro z hz
    simpa [hA0, hKK] using rgG1_pt_bound hα hα4 hm hc hnear hfar z hz
  have hKKnn : ∀ z : ℝ, 1 ≤ z → 0 ≤ KK z := by
    intro z hz
    simp only [hKK]
    exact intervalIntegral.integral_nonneg hz
      (fun t ht => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one ht.1) _))
  -- ### measurability of the two ENNReal integrands
  have hP : AEMeasurable (fun u : ℝ => ENNReal.ofReal ((c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have h1 : AEMeasurable c (volume.restrict (Set.Ioi (1 : ℝ))) := hc.restrict
    have h2 : AEMeasurable (fun u : ℝ => u ^ (Work.FTS.EllExist.rgQ α m - 1)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (measurable_id.pow_const (Work.FTS.EllExist.rgQ α m - 1)).aemeasurable
    have h4 : AEMeasurable (fun u : ℝ => (c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (h1.pow_const 2).mul h2
    exact h4.ennreal_ofReal
  have hQ : AEMeasurable (fun u : ℝ => ENNReal.ofReal (u ^ (-(Work.FTS.EllExist.rgQ α m))))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((measurable_id.pow_const (-(Work.FTS.EllExist.rgQ α m))).aemeasurable).ennreal_ofReal
  -- ### the `ENNReal`-level pointwise bound
  have hptE : ∀ z : ℝ, 1 < z →
      ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2)
        ≤ ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
          + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have h1nn : 0 ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A0)) (Real.rpow_nonneg hz0.le _)
    have h2nn : 0 ≤ 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hz0.le _))
        (hKKnn z (le_of_lt hz))
    have h := ENNReal.ofReal_le_ofReal (hpt z hz)
    rw [ENNReal.ofReal_add h1nn h2nn] at h
    have h2nn' : 0 ≤ 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hz0.le _)
    rw [ENNReal.ofReal_mul h2nn'] at h
    simp only [hKK] at h
    rw [ofReal_integral_rpow_mul_sq_eq_lintegral hα hα4 hm hc hfar z (le_of_lt hz)] at h
    exact h
  -- ### the evaluation of the first term
  have hA0part : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
      = ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
    have hz2q : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
        = ENNReal.ofReal (1 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
      have h := lintegral_ofReal_rpow_Ioi (p := -(2 * Work.FTS.EllExist.rgQ α m)) (z := 1) (by linarith) (by norm_num)
      rw [Real.one_rpow] at h
      have h2 : -(1 : ℝ) / (-(2 * Work.FTS.EllExist.rgQ α m) + 1) = 1 / (2 * Work.FTS.EllExist.rgQ α m - 1) := by
        rw [show -(2 * Work.FTS.EllExist.rgQ α m) + 1 = -(2 * Work.FTS.EllExist.rgQ α m - 1) from by ring, div_neg, neg_div, neg_neg]
      rwa [h2] at h
    calc (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
        = ∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (2 * A0 ^ 2) * ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          exact ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (2 * A0 ^ 2)
            * ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m))) :=
          lintegral_const_mul' (ENNReal.ofReal (2 * A0 ^ 2))
            (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))) ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 * A0 ^ 2) * ENNReal.ofReal (1 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by rw [hz2q]
      _ = ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- ### the evaluation of the second term
  have hKpart : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
        (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
      ≤ ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hinner : ∀ z ∈ Set.Ioi (1 : ℝ),
        (∫⁻ t in Set.Ioi z, ENNReal.ofReal (t ^ (-(Work.FTS.EllExist.rgQ α m))))
          = ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)) := by
      intro z hz
      have hz0 : 0 < z := lt_trans zero_lt_one hz
      have h := lintegral_ofReal_rpow_Ioi (p := -(Work.FTS.EllExist.rgQ α m)) (z := z) (by linarith) hz0
      rwa [show -(z ^ (-(Work.FTS.EllExist.rgQ α m) + 1)) / (-(Work.FTS.EllExist.rgQ α m) + 1) = z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1) from by
            rw [show -(Work.FTS.EllExist.rgQ α m) + 1 = -(Work.FTS.EllExist.rgQ α m - 1) from by ring, div_neg, neg_div, neg_neg,
              show -(Work.FTS.EllExist.rgQ α m - 1) = 1 - Work.FTS.EllExist.rgQ α m from by ring]] at h
    have hswap := lintegral_tail_swap_Ioi_one
      (P := fun u : ℝ => ENNReal.ofReal ((c u) ^ 2 * u ^ (Work.FTS.EllExist.rgQ α m - 1)))
      (Q := fun u : ℝ => ENNReal.ofReal (u ^ (-(Work.FTS.EllExist.rgQ α m)))) hP hQ
      (fun u => ENNReal.ofReal_ne_top) (fun u => ENNReal.ofReal_ne_top)
    have hchain : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
          (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        = ENNReal.ofReal ((1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in (Set.Ioi (1 : ℝ) ∩ Set.Iio z), ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) from by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
        have hsub : Set.Ioo (1 : ℝ) z = Set.Ioi (1 : ℝ) ∩ Set.Iio z := by
          ext x
          exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
        rw [hsub]]
      rw [← hswap]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
            (∫⁻ t in Set.Ioi z, ENNReal.ofReal (t ^ (-(Work.FTS.EllExist.rgQ α m)))))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
              ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
            rw [hinner z hz]]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1)) *
            ENNReal.ofReal (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1)))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2) * ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
            have hz0 : 0 < z := lt_trans zero_lt_one hz
            rw [← ENNReal.ofReal_mul
                (mul_nonneg (sq_nonneg (c z)) (Real.rpow_nonneg hz0.le _)),
              ← ENNReal.ofReal_mul (sq_nonneg (c z))]
            congr 1
            have hnum : z ^ (Work.FTS.EllExist.rgQ α m - 1) * z ^ (1 - Work.FTS.EllExist.rgQ α m) = 1 := by
              rw [← Real.rpow_add hz0, show Work.FTS.EllExist.rgQ α m - 1 + (1 - Work.FTS.EllExist.rgQ α m) = 0 from by ring, Real.rpow_zero]
            calc (c z) ^ 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) * (z ^ (1 - Work.FTS.EllExist.rgQ α m) / (Work.FTS.EllExist.rgQ α m - 1))
                = (c z) ^ 2 * (z ^ (Work.FTS.EllExist.rgQ α m - 1) * z ^ (1 - Work.FTS.EllExist.rgQ α m)) / (Work.FTS.EllExist.rgQ α m - 1) := by ring
              _ = (c z) ^ 2 * 1 / (Work.FTS.EllExist.rgQ α m - 1) := by rw [hnum]
              _ = (c z) ^ 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) := by ring]
      rw [show (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c z) ^ 2) * ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)))
          = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)) * ENNReal.ofReal ((c z) ^ 2) from by
            refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => mul_comm _ _)]
      rw [lintegral_const_mul' (ENNReal.ofReal (1 / (Work.FTS.EllExist.rgQ α m - 1)))
        (fun z : ℝ => ENNReal.ofReal ((c z) ^ 2)) ENNReal.ofReal_ne_top]
      rw [← ofReal_integral_eq_lintegral_ofReal hfar (ae_of_all _ (fun t => sq_nonneg _))]
      rw [← ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hqm1))]
    calc (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
          (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        = ∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m)))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 : ℝ) *
            (ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          ring
      _ = ENNReal.ofReal (2 : ℝ) * (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-(Work.FTS.EllExist.rgQ α m))) *
            (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 : ℝ) *
            ENNReal.ofReal ((1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
          rw [hchain]
      _ ≤ ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
          exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  -- ### assemble
  have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
  have hbound : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
      ≤ ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1)
          + 2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hm1 : (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal ((Work.FTS.EllExist.rgG1 α m c z) ^ 2))
        ≤ ∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
            + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact hptE z hz
    have hm2 : (∫⁻ z in Set.Ioi (1 : ℝ), (ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)))
            + ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))))
        = (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))))
          + (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)))) :=
      lintegral_add_left'
        ((measurable_const.mul (measurable_id.pow_const (-(2 * Work.FTS.EllExist.rgQ α m)))).aemeasurable.ennreal_ofReal) _
    rw [hm2, hA0part] at hm1
    have hAB : ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1))
          + (∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * z ^ (-(Work.FTS.EllExist.rgQ α m))) *
              (∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))))
        ≤ ENNReal.ofReal (2 * A0 ^ 2 / (2 * Work.FTS.EllExist.rgQ α m - 1))
          + ENNReal.ofReal (2 * (1 / (Work.FTS.EllExist.rgQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
      add_le_add (le_refl _) hKpart
    refine hm1.trans (hAB.trans ?_)
    exact (ENNReal.ofReal_add
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg A0)) (le_of_lt h2qm1))
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hPnn)).symm.le
  simpa [hA0] using hbound

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-- **Far-field square bound for the growing Green branch.**

With `p = rgP α m ≥ 8` and `rgG2 α m c z = z^p * ∫_{Ioi z} c t * t^{-p-1} dt`, the function
`z ↦ (rgG2 α m c z)²` is integrable on `(1,∞)`.

HINT (verified by two reviewers).  For `z > 1` split
`c t * t^{-p-1} = (c t * t^{-1/2}) * t^{-p-1/2}`, so Cauchy–Schwarz on `Ioi z` gives
`(∫ t in Ioi z, c t t^{-p-1})² ≤ (∫ t in Ioi z, (c t)² t^{-1}) * (∫ t in Ioi z, t^{-2p-1})`
with `∫ t in Ioi z, t^{-2p-1} = z^{-2p}/(2p)` (`p > 0`, use `integral_Ioi_rpow_of_lt`). Hence
`(rgG2 z)² ≤ (1/(2p)) * ∫ t in Ioi z, (c t)² t^{-1}` (the `t`-integral is honest: the same
Cauchy–Schwarz bounds `∫ t in Ioi z, |c t| t^{-p-1}`).
Then Tonelli on the region `1 < z < t < ∞`
(`Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one`) gives
`∫_1^∞ ∫_z^∞ (c t)² t^{-1} dt dz = ∫_1^∞ (c t)² (t-1)/t dt ≤ ∫_1^∞ (c t)² dt < ∞` (`hfar`, and
`1/t ≤ 1` on `(1,∞)`, so `(c t)²/t ∈ L¹(Ioi 1)` by `IntegrableOn.mono_set`).
For `AEStronglyMeasurable` of `z ↦ ∫ t in Ioi z, rgF2 α m c t` on `(1,∞)`: write it as
`C₁ - ∫ t in 1..z, rgF2 α m c t` with `C₁ = ∫ t in Ioi 1, rgF2 α m c t`, a sum of a constant and a
primitive, hence continuous on `(1,∞)`
(`intervalIntegral.continuousOn_primitive_interval`; the identity follows from
`setIntegral_union` on `Ioi 1 = Ioc 1 z ∪ Ioi z`). -/
/- PROOF (as implemented; the two measure-theoretic bricks below are separate modules).

Write `p = rgP α m > 0` and `Q t = (c t)² t^{-1}`.

* `Work.FTS.PhiStar.Honesty.sq_rpow_tail_mul_integral_le` is the Cauchy–Schwarz step with the
  splitting `c t · t^{-p-1} = (c t · t^{-1/2})·(t^{-p-1/2})`: for `z ≥ 1`,
  `(rgG2 α m c z)² ≤ (1/(2p)) ∫ t in Ioi z, Q t` (the factor `z^{2p}` cancels `z^{-2p}` coming
  from `∫ t in Ioi z, t^{-2p-1} = z^{-2p}/(2p)`).
* `Work.FTS.PhiStar.Honesty.integrableOn_tailSetIntegral_Ioi_one` is Tonelli on the region
  `1 < z < t`: since `Q ∈ L¹(1,∞)` (dominated by `c²` there, as `t^{-1} ≤ 1`) and also
  `t ↦ t·Q t = c²` is integrable, the tail integral `z ↦ ∫ t in Ioi z, Q t` is integrable on
  `(1,∞)`.
* Measurability of `z ↦ ∫ t in Ioi z, rgF2 α m c t` is obtained from the product-measure
  identity `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` applied to
  `(z,t) ↦ 1_{z<t}·rgF2 α m c t` (the integrand restricted to `(1,∞)`), and then `rgG2` is the
  product of that map with the continuous weight `z^p`; the conclusion is `Integrable.mono'`
  against the integrable dominating function `(1/(2p)) ∫ t in Ioi z, Q t`. -/
theorem rgG2_sq_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2) (Set.Ioi 1) := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hp : 0 < Work.FTS.EllExist.rgP α m := lt_of_lt_of_le (by norm_num) hp8
  -- the weight of the Cauchy–Schwarz estimate
  set Q : ℝ → ℝ := fun t => (c t) ^ 2 * t ^ (-1 : ℝ) with hQdef
  have hQnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] Q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans one_pos ht)) _)
  -- `Q` is integrable on `(1,∞)`: it is dominated there by `c²`
  have hQint : IntegrableOn Q (Ioi 1) := by
    refine Integrable.mono' hfar ?_ ?_
    · have h1 : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Ioi 1)) :=
        (hc.aestronglyMeasurable.restrict).pow 2
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-1 : ℝ)) (volume.restrict (Ioi 1)) :=
        ((continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos ht)))).aestronglyMeasurable
            measurableSet_Ioi)
      simpa only [hQdef] using
        (h1.mul h2).congr (Filter.EventuallyEq.of_eq (by funext t; simp only [Pi.mul_apply]))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hpow : t ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans one_pos ht)) _)]
      calc (c t) ^ 2 * t ^ (-1 : ℝ) ≤ (c t) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = (c t) ^ 2 := mul_one _
  -- and so is `t ↦ t·Q t`, which is just `c²` on `(1,∞)`
  have hQt : IntegrableOn (fun t : ℝ => Q t * t) (Ioi 1) := by
    refine hfar.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans one_pos ht)
    simp only [hQdef, Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
  -- the Tonelli step on the region `1 < z < t`
  have hTail : IntegrableOn (fun z : ℝ => ∫ t in Ioi z, Q t) (Ioi 1) :=
    (integrableOn_tailSetIntegral_Ioi_one hQint hQnn hQt).1
  -- the Cauchy–Schwarz pointwise bound
  have hbound : ∀ z ∈ Ioi (1 : ℝ), (Work.FTS.EllExist.rgG2 α m c z) ^ 2
      ≤ (1 / (2 * Work.FTS.EllExist.rgP α m)) * (∫ t in Ioi z, Q t) := by
    intro z hz
    have h1 := sq_rpow_tail_mul_integral_le (c := c) (p := Work.FTS.EllExist.rgP α m)
      (z := z) hp hz.le hc hfar
    simpa only [hQdef, Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB,
      Work.FTS.EllExist.rgF2] using h1
  -- a.e.-strong measurability of the tail integrand `rgF2 α m c` …
  have hrgF2_aesm : AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
      (volume.restrict (Ioi (1 : ℝ))) := by
    have h1 : AEStronglyMeasurable c (volume.restrict (Ioi (1 : ℝ))) :=
      hc.aestronglyMeasurable.restrict
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(Work.FTS.EllExist.rgP α m) - 1))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos ht)))).aestronglyMeasurable
          measurableSet_Ioi)
    refine (h1.mul h2).congr (Filter.EventuallyEq.of_eq ?_)
    funext t
    simp only [Pi.mul_apply, Work.FTS.EllExist.rgF2]
  -- … hence of its tail integral, by the product-measure form of Fubini
  have htail_aesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in Ioi z, Work.FTS.EllExist.rgF2 α m c t)
      (volume.restrict (Ioi (1 : ℝ))) := by
    set g : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (Work.FTS.EllExist.rgF2 α m c) with hg_def
    have hg : AEStronglyMeasurable g (volume.restrict (Ioi (1 : ℝ))) :=
      hrgF2_aesm.indicator measurableSet_Ioi
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.1 < p.2 then g p.2 else (0 : ℝ))
        ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2)
          ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) :=
        hg.comp_snd
      have h2 : Measurable (fun p : ℝ × ℝ => (if p.1 < p.2 then (1 : ℝ) else 0)) :=
        Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
          measurable_const
      refine (h1.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with p
      by_cases h : p.1 < p.2 <;> simp [h]
    refine (hpair.integral_prod_right').congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hsuby : Ioi y ⊆ Ioi (1 : ℝ) :=
      fun t ht => Set.mem_Ioi.mpr (lt_trans (Set.mem_Ioi.mp hy) (Set.mem_Ioi.mp ht))
    calc ∫ t, (if y < t then g t else (0 : ℝ)) ∂(volume.restrict (Ioi (1 : ℝ)))
        = ∫ t, (Ioi y).indicator (Work.FTS.EllExist.rgF2 α m c) t
            ∂(volume.restrict (Ioi (1 : ℝ))) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          by_cases h : y < t
          · rw [ite_eq_left h, Set.indicator_of_mem (Set.mem_Ioi.mpr h),
              hg_def, Set.indicator_of_mem ht]
          · rw [ite_eq_right h, Set.indicator_of_notMem (by simpa using h)]
      _ = ∫ t in Ioi y, Work.FTS.EllExist.rgF2 α m c t
            ∂(volume.restrict (Ioi (1 : ℝ))) := integral_indicator measurableSet_Ioi
      _ = ∫ t in Ioi y, Work.FTS.EllExist.rgF2 α m c t := by
          rw [Measure.restrict_restrict_of_subset hsuby]
  -- a.e.-strong measurability of `rgG2` and of its square
  have hrg_aesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.rgG2 α m c z)
      (volume.restrict (Ioi (1 : ℝ))) := by
    have hzpow : AEStronglyMeasurable (fun z : ℝ => z ^ (Work.FTS.EllExist.rgP α m))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((continuousOn_id.rpow_const
        (fun z hz => Or.inl (ne_of_gt (lt_trans one_pos hz)))).aestronglyMeasurable
          measurableSet_Ioi)
    refine (hzpow.mul htail_aesm).congr (Filter.EventuallyEq.of_eq ?_)
    funext z
    simp only [Pi.mul_apply]
    rw [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB]
  have htarget : AEStronglyMeasurable (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2)
      (volume.restrict (Ioi (1 : ℝ))) := hrg_aesm.pow 2
  -- the dominating function is integrable, and the target is dominated by it
  have hdom_int : IntegrableOn
      (fun z : ℝ => (1 / (2 * Work.FTS.EllExist.rgP α m)) * (∫ t in Ioi z, Q t)) (Ioi 1) :=
    hTail.const_mul _
  refine Integrable.mono' hdom_int htarget ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hbound z hz

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped ENNReal

namespace Work.FTS.PhiStar.Honesty

-- ================================ the main auxiliary estimate ================================

/-- Abstract form of the target: for `p > 3`,
`z ↦ z^{2p-4} (∫_{t > z} c t t^{-p-1})²` is integrable on `(0,1)`. -/
private theorem key_tail {p : ℝ} (hp : 0 < p) (hp3 : 3 < p) {c : ℝ → ℝ} (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    IntegrableOn
      (fun z : ℝ => z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
      (Set.Ioo 0 1) := by
  have hr : (-1 : ℝ) < p - 4 := by linarith
  have hc_aesm : AEStronglyMeasurable c volume := hc.aestronglyMeasurable
  -- ### (1) weighted Cauchy–Schwarz on the tail `(z,∞)`
  have hcs : ∀ z : ℝ, 0 < z →
      (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
        ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    intro z hz
    exact psi_cs_of_aesm hp hz (hc_aesm.mono_measure Measure.restrict_le_self)
      (sq_integrableOn_Ioi_of hz hnear hfar)
  -- ### (2) the pointwise `ENNReal` bound
  have hstep : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
        ≤ ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hzp : ENNReal.ofReal (z ^ (2 * p - 4)) * ENNReal.ofReal (z ^ (-p))
        = ENNReal.ofReal (z ^ (p - 4)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _)]
      congr 1
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have hA : ENNReal.ofReal ((1 / p) * z ^ (-p)
          * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))
        = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
            * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.rpow_nonneg hz0.le _)),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / p), mul_assoc]
    have hWaesm : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2 * t ^ (-p - 1))
        (volume.restrict (Set.Ioi z)) := by
      have h1 : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2)
          (volume.restrict (Set.Ioi z)) :=
        (hc_aesm.pow 2).mono_measure Measure.restrict_le_self
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1))
          (volume.restrict (Set.Ioi z)) :=
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))).aestronglyMeasurable measurableSet_Ioi
      exact h1.mul h2
    have hWnn : 0 ≤ᵐ[volume.restrict (Set.Ioi z)]
        (fun t : ℝ => (c t) ^ 2 * t ^ (-p - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans hz0 ht)) _)
    calc ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
        = ENNReal.ofReal (z ^ (2 * p - 4))
            * ENNReal.ofReal ((∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _)]
      _ ≤ ENNReal.ofReal (z ^ (2 * p - 4))
            * ENNReal.ofReal ((1 / p) * z ^ (-p)
                * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hcs z hz0))
      _ = ENNReal.ofReal (z ^ (2 * p - 4))
            * (ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
                * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)))) := by
          rw [hA]
      _ ≤ ENNReal.ofReal (z ^ (2 * p - 4))
            * (ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
            (ofReal_setIntegral_le_setLIntegral' hWaesm hWnn)))
      _ = ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          rw [← hzp]; ring
  -- ### (3) the two measurability inputs of the swap lemma
  have hF_aem : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (p - 4)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))).aemeasurable
        measurableSet_Ioo)
  have hG_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (hc.pow aemeasurable_const).mono_measure Measure.restrict_le_self
    have h2 : AEMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).aemeasurable measurableSet_Ioi
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.mul h2)
  have hswap := lintegral_Ioo_tail_swap
    (F := fun z : ℝ => ENNReal.ofReal (z ^ (p - 4)))
    (G := fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) hF_aem hG_aem
  -- ### (4) the factor `ofReal (1/(p-3))`
  have hfac : (∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
        * ENNReal.ofReal (t ^ (p - 3) / (p - 3))))
      = ENNReal.ofReal (1 / (p - 3))
        * ∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
            * ENNReal.ofReal (t ^ (p - 3))) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (1 / (p - 3))) _
      ENNReal.ofReal_lt_top.ne]
    refine lintegral_congr_ae ?_
    filter_upwards with t
    rw [show t ^ (p - 3) / (p - 3) = (1 / (p - 3)) * t ^ (p - 3) from by ring]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (p - 3))]
    ring
  -- ### (5) the exponent identity `(c t)² t^{-p-1} t^{p-3} = (c t)²/t⁴`
  have hident : (∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
        * ENNReal.ofReal (t ^ (p - 3))))
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _))]
    congr 1
    have hpw : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) from by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast t 4]
    rw [mul_assoc, ← Real.rpow_add ht0, show -p - 1 + (p - 3) = -4 by ring, div_eq_mul_inv, hpw]
  -- ### (6) finiteness of `∫⁻_{t>0} ofReal ((c t)²/t⁴)`
  have hfin' : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
        + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    have hnn1 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun t : ℝ => (c t) ^ 2 / t ^ 4) :=
      Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (by positivity)
    have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] (fun t : ℝ => (c t) ^ 2) :=
      Eventually.of_forall fun t => sq_nonneg _
    have hfirst : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4) :=
      (ofReal_integral_eq_lintegral_ofReal hnear hnn1).symm
    have hsecond : (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2))
        = ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hfar hnn2).symm
    have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 := by
      intro t ht
      rcases lt_or_ge t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht2 (not_le.mpr ht1.2)
    have hdisj2 : Disjoint ({1} : Set ℝ) (Set.Ioi 1) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      simp only [Set.mem_singleton_iff] at ht1
      rw [ht1] at ht2
      simp only [Set.mem_Ioi] at ht2
      exact lt_irrefl 1 ht2
    have hIci : (∫⁻ t in Set.Ici (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
      rw [show Set.Ici (1 : ℝ) = ({1} : Set ℝ) ∪ Set.Ioi 1 from by
            ext t
            simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
            constructor
            · intro h
              rcases eq_or_lt_of_le h with h' | h'
              · exact Or.inl h'.symm
              · exact Or.inr h'
            · rintro (h | h)
              · exact le_of_eq h.symm
              · exact le_of_lt h,
        lintegral_union measurableSet_Ioi hdisj2,
        lintegral_singleton, measure_singleton, mul_zero, zero_add]
    have hIoi_le : (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        ≤ ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine ENNReal.ofReal_le_ofReal ?_
      have ht1 : (1 : ℝ) ≤ t ^ 4 := one_le_pow₀ (le_of_lt ht)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c t)]
    calc (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        ≤ ∫⁻ t in (Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) :=
          lintegral_mono_set hsub
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ici (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) :=
          lintegral_union measurableSet_Ici hdisj
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) := by rw [hIci]
      _ ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2)) :=
          add_le_add le_rfl hIoi_le
      _ = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
            + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by rw [hfirst, hsecond]
  -- ### (7) the chain
  have hbdd : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
      ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
          * (ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
              + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2))) := by
    calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
          exact hstep z hz
      _ = ENNReal.ofReal (1 / p)
            * ∫⁻ z in Set.Ioo (0 : ℝ) 1, (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
      _ = ENNReal.ofReal (1 / p)
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t),
                    ENNReal.ofReal (z ^ (p - 4))) := by
          rw [hswap]
      _ ≤ ENNReal.ofReal (1 / p)
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * ENNReal.ofReal (t ^ (p - 3) / (p - 3)) := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have h := lintegral_ofReal_rpow_Ioo_zero_min (r := p - 4) (t := t) hr ht
          rw [show (p - 4) + 1 = p - 3 by ring] at h
          exact mul_le_mul' le_rfl h
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * ENNReal.ofReal (t ^ (p - 3))) := by
          rw [hfac]
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) := by
          rw [hident]
      _ ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * (ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
                + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hfin')
  -- ### (8) measurability and conclusion
  have hne : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
      ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hbdd ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
  have hT_aesm : AEStronglyMeasurable
      (fun z : ℝ => z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-p - 1))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi (fun t : ℝ => c t * t ^ (-p - 1))).mono_measure
        (Measure.restrict_mono Set.Ioo_subset_Ioi_self le_rfl)
    have h2 : AEStronglyMeasurable (fun z : ℝ => z ^ (2 * p - 4))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))).aestronglyMeasurable
        measurableSet_Ioo
    exact h2.mul (h1.pow 2)
  exact (lintegral_ofReal_ne_top_iff_integrable hT_aesm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _))).mp hne

/-- **Near-zero weighted square bound for the growing Green branch.**

With `rgG2 α m c z = z^p * ∫_{Ioi z} c t * t^{-p-1} dt`, `p = rgP α m ≥ 8`, the function
`z ↦ (rgG2 α m c z)² / z⁴` is integrable on `(0,1)`.

HINT (verified by two reviewers).  For `z ∈ (0,1)` write `B z = ∫ t in Set.Ioi z, rgF2 α m c t`,
so `rgG2 α m c z = z^{p} * B z` and `rgG2 z / z² = z^{p-2} B z`.
* First `∫ t in Set.Ioi z, f2 = ∫ t in z..1, f2 t + C₁` with `C₁ = ∫ t in Set.Ioi 1, rgF2 α m c t`,
  a finite constant: `|C₁| ≤ (1/2)∫_1^∞ (c t)² + (1/2)∫_1^∞ t^{-2p-2}` using `hfar` and
  `integrableOn_Ioi_rpow_of_lt`.  The `C₁`-part contributes
  `C₁² ∫_0^1 z^{2p-4} dz = C₁²/(2p-3)` (as `2p - 4 ≥ 12 > -1`).
* For the first part: split `c t * t^{-p-1} = (c t * t^{-5/2}) * t^{-p+3/2}`, so
  Cauchy–Schwarz on `z..1` gives
  `(∫ t in z..1, c t * t^{-p-1})² ≤ (∫ t in z..1, (c t)² t^{-5}) * (∫ t in z..1, t^{-2p+3})`
  and `∫ t in z..1, t^{-2p+3} = (z^{-2p+4} - 1)/(2p-4) ≤ z^{-2p+4}/(2p-4)` (`2p-3 > 1`).
  Multiplying by `z^{2p-4}` cancels, giving
  `(z^{p-2} ∫ t in z..1, c t t^{-p-1})² ≤ (1/(2p-4)) * ∫ t in z..1, (c t)² t^{-5}`.
  Tonelli on the triangle `0 < z < t < 1` (`Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle`,
  with the roles of `F`/`G` interchanged) gives
  `∫_0^1 ∫_z^1 (c t)² t^{-5} dt dz = ∫_0^1 (c t)² t^{-5} * t dt = ∫_0^1 (c t)² t^{-4} dt < ∞`.

You must also check that `∫ t in Set.Ioi z, rgF2 α m c t` is an honest (non-junk) number for
`z ∈ (0,1)`: `f2 = c t t^{-p-1}` is integrable on `(z,1)` by Cauchy–Schwarz
`|c t| t^{-p-1} = (|c t|/t²) t^{1-p} ≤ (1/2)((c t)²/t⁴) + (1/2) t^{2-2p}` — note the last term
is NOT integrable on `(0,1)`, so use
`∫_z^1 |c| t^{-p-1} ≤ ‖c/t²‖_{L²(z,1)} * (∫_z^1 t^{2-2p})^{1/2}` instead
(`∫_z^1 t^{2-2p} = (z^{3-2p}-1)/(3-2p) < ∞` for `z > 0`).
Finally `∫ t in Set.Ioi z, f2 = ∫ t in z..1, f2 + ∫ t in Set.Ioi 1, f2` for `z ∈ (0,1)` by
`setIntegral_union` / `integral_add_compl` on the disjoint union
`Ioi z = Ioc z 1 ∪ Ioi 1` (or use `∫ t in Ioi 1, f2 = C₁`).
`AEStronglyMeasurable` of the target: `z ↦ ∫ t in Ioi z, f2` can be written as
`z ↦ C₁ + ∫ t in 1..z, f2 t`, a sum of a constant and a primitive, hence continuous on `(0,1)`. -/
theorem rgG2_sq_div_z4_Ioo {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hp0 : 0 < Work.FTS.EllExist.rgP α m := by linarith
  have hp3 : 3 < Work.FTS.EllExist.rgP α m := by linarith
  have hkey := key_tail (p := Work.FTS.EllExist.rgP α m) hp0 hp3 hc hnear hfar
  refine hkey.congr_fun ?_ measurableSet_Ioo
  intro z hz
  have hz0 : 0 < z := hz.1
  simp only [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
  have h1 : (z ^ Work.FTS.EllExist.rgP α m) ^ 2 = z ^ (2 * Work.FTS.EllExist.rgP α m) := by
    rw [sq, ← Real.rpow_add hz0]
    congr 1
    ring
  have h2 : (z ^ 4)⁻¹ = z ^ (-4 : ℝ) := by
    have h4 : z ^ (4 : ℝ) = z ^ 4 := Real.rpow_natCast z 4
    rw [← h4, ← Real.rpow_neg hz0.le (4 : ℝ)]
  have h3 : z ^ (2 * Work.FTS.EllExist.rgP α m) * z ^ (-4 : ℝ)
      = z ^ (2 * Work.FTS.EllExist.rgP α m - 4) := by
    have he : 2 * Work.FTS.EllExist.rgP α m + (-4) = 2 * Work.FTS.EllExist.rgP α m - 4 := by
      ring
    rw [← Real.rpow_add hz0, he]
  rw [mul_pow, div_eq_mul_inv, h1, h2, ← h3]
  ring

end Work.FTS.PhiStar.Honesty
end
