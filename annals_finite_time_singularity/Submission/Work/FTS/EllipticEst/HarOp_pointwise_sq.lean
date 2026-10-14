import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.Coercivity.C0D_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Antiderivative of `s²/(1+s)⁶`: `G(s) = -1/(3(1+s)³) + 1/(2(1+s)⁴) - 1/(5(1+s)⁵)`. -/
private def c0G (s : ℝ) : ℝ :=
  (-1 / 3) * ((1 + s)⁻¹) ^ 3 + (1 / 2) * ((1 + s)⁻¹) ^ 4 - (1 / 5) * ((1 + s)⁻¹) ^ 5

/-- `G'(s) = s²/(1+s)⁶` for `s ≥ 0`. -/
private lemma c0G_hasDerivAt (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt c0G (x ^ 2 / (1 + x) ^ 6) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  have hbase : HasDerivAt (fun t : ℝ => ((1 : ℝ) + t)⁻¹) (-1 / (1 + x) ^ 2) x :=
    Work.FM.hasDerivAt_inv_add_const 1 x hx1
  have h1 : HasDerivAt (fun t : ℝ => (-1 / 3) * ((1 + t)⁻¹) ^ 3)
      ((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 3).const_mul (-1 / 3)
  have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * ((1 + t)⁻¹) ^ 4)
      ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 4).const_mul (1 / 2)
  have h3 : HasDerivAt (fun t : ℝ => (1 / 5) * ((1 + t)⁻¹) ^ 5)
      ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2))) x :=
    (hbase.pow 5).const_mul (1 / 5)
  have hG : HasDerivAt c0G
      (((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2)))
        + ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2)))
        - ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2)))) x :=
    (h1.add h2).sub h3
  have hval : ((-1 / 3) * (3 * ((1 + x)⁻¹) ^ 2 * (-1 / (1 + x) ^ 2)))
        + ((1 / 2) * (4 * ((1 + x)⁻¹) ^ 3 * (-1 / (1 + x) ^ 2)))
        - ((1 / 5) * (5 * ((1 + x)⁻¹) ^ 4 * (-1 / (1 + x) ^ 2)))
      = x ^ 2 / (1 + x) ^ 6 := by
    field_simp
    ring
  rw [hval] at hG
  exact hG

/-- `G(s) → 0` as `s → +∞`. -/
private lemma c0G_tendsto : Tendsto c0G atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => (-1 / 3) * ((1 + t)⁻¹) ^ 3 + (1 / 2) * ((1 + t)⁻¹) ^ 4
      - (1 / 5) * ((1 + t)⁻¹) ^ 5) atTop (𝓝 0)
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using h2.pow 3
  have h4 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa using h2.pow 4
  have h5 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 5) atTop (𝓝 0) := by
    simpa using h2.pow 5
  have hG := ((h3.const_mul (-1 / 3)).add (h4.const_mul (1 / 2))).sub (h5.const_mul (1 / 5))
  simpa using hG

/-- `s²/(1+s)⁶ ≥ 0` on `(0,∞)`. -/
private lemma c0G'_nonneg {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ x ^ 2 / (1 + x) ^ 6 := by
  have hx' : (0 : ℝ) < x := hx
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  positivity

/-- The improper integral `∫_0^∞ s²/(1+s)⁶ ds = 1/30`. -/
private lemma c0D_integral_key : ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s) ^ 6 = 1 / 30 := by
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := c0G) (g' := fun t : ℝ => t ^ 2 / (1 + t) ^ 6) (a := 0) (l := 0)
    (fun x hx => c0G_hasDerivAt x hx) (fun x hx => c0G'_nonneg hx) c0G_tendsto
  rw [key]
  norm_num [c0G]

/-- `C0D = 1/30`. -/
private lemma c0D_eq : C0D = 1 / 30 := by
  have hcongr : ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s) * Spaces.w s)) ^ 2
      = ∫ s in Set.Ioi (0 : ℝ), s ^ 2 / (1 + s) ^ 6 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have hs0 : s ≠ 0 := ne_of_gt hs'
    have hs1 : (1 : ℝ) + s ≠ 0 := by
      have : (0 : ℝ) < 1 + s := by linarith
      positivity
    rw [Spaces.w]
    field_simp
  unfold C0D
  rw [hcongr, c0D_integral_key]

theorem C0D_le : C0D ≤ 1 / 16 := by
  rw [c0D_eq]
  norm_num

end

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.C0Ih_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set
open scoped Real Topology

set_option autoImplicit false

/-- Pointwise bound for the angular density `h' = C0g`:
`C0g(θ)² ≤ 432` for every `θ`.  Writing `u = cos²θ ∈ [0,1]` one has
`C0g(θ)² = 324 (1-u)u²(5u-3)²`, and `(1-u)u² ≤ 4/27`, `(5u-3)² ≤ 9`. -/
private lemma C0g_sq_le (θ : ℝ) : (C0g θ) ^ 2 ≤ 432 := by
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hc1 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  -- the purely polynomial bound at `u = cos²θ`
  have hpoly : Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2 ≤ 4 / 3 := by
    rw [hs]
    have hA : (1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2 ≤ 4 / 27 := by
      have h3 : 0 ≤ (3 * Real.cos θ ^ 2 - 2) ^ 2 * (3 * Real.cos θ ^ 2 + 1) := by
        nlinarith [sq_nonneg (3 * Real.cos θ ^ 2 - 2)]
      nlinarith [h3]
    have hB : (5 * Real.cos θ ^ 2 - 3) ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    calc (1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2
        = ((1 - Real.cos θ ^ 2) * (Real.cos θ ^ 2) ^ 2) * ((5 * Real.cos θ ^ 2 - 3) ^ 2) := by
          ring
      _ ≤ (4 / 27) * 9 := mul_le_mul hA hB (by positivity) (by positivity)
      _ = 4 / 3 := by norm_num
  -- rewrite `C0g` in terms of `u = cos²θ`
  have hC0g : C0g θ = 18 * Real.sin θ * Real.cos θ ^ 2 * (5 * Real.cos θ ^ 2 - 3) := by
    simp only [C0g]
    rw [hs]; ring
  rw [hC0g]
  have key : (18 * Real.sin θ * Real.cos θ ^ 2 * (5 * Real.cos θ ^ 2 - 3)) ^ 2
      = 324 * (Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 * (5 * Real.cos θ ^ 2 - 3) ^ 2) := by
    ring
  rw [key]
  nlinarith [hpoly]

/-- `C0Ih = ∫_{Iθ} h'(θ)² dθ ≤ 729`.  Since `Iθ = [0,π/2]` has length `π/2` and
`C0g² ≤ 432` pointwise, `C0Ih ≤ 432 · π/2 = 216π < 729`. -/
theorem C0Ih_le : C0Ih ≤ 729 := by
  rw [C0Ih]
  have h0 : (0 : ℝ) ≤ π / 2 := by positivity
  rw [Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h0]
  have hcont : Continuous fun θ : ℝ => (C0g θ) ^ 2 := by
    simp only [C0g]; fun_prop
  calc ∫ θ in (0 : ℝ)..(π / 2), (C0g θ) ^ 2
      ≤ ∫ θ in (0 : ℝ)..(π / 2), (432 : ℝ) := by
        apply intervalIntegral.integral_mono h0
        · exact hcont.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · exact C0g_sq_le
    _ = 432 * (π / 2) := by
        rw [intervalIntegral.integral_const]; ring
    _ ≤ 729 := by nlinarith [Real.pi_lt_d2]

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.C0h_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem C0h_deriv (θ : ℝ) : deriv Work.Coercivity.C0h θ = Work.Coercivity.C0g θ := by
  -- derivative of `sin (2 ·)`
  have hsin2 : deriv (fun t : ℝ => Real.sin (2 * t)) θ = Real.cos (2 * θ) * 2 := by
    rw [show (fun t : ℝ => Real.sin (2 * t)) = (Real.sin ∘ (fun t : ℝ => 2 * t)) from rfl]
    rw [deriv_comp θ (by fun_prop : DifferentiableAt ℝ Real.sin (2 * θ))
          (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => 2 * t) θ)]
    have h1 : deriv Real.sin (2 * θ) = Real.cos (2 * θ) := (Real.hasDerivAt_sin (2 * θ)).deriv
    have h2 : deriv (fun t : ℝ => 2 * t) θ = 2 := by
      rw [show (fun t : ℝ => 2 * t) = (fun y : ℝ => 2 * id y) from rfl]
      rw [((hasDerivAt_id θ).const_mul (2 : ℝ)).deriv]
      norm_num
    rw [h1, h2]
  -- derivative of `cos ^ 2`
  have hcos2 : deriv (fun t : ℝ => Real.cos t ^ 2) θ = 2 * Real.cos θ * (-Real.sin θ) := by
    rw [show (fun t : ℝ => Real.cos t ^ 2) = (Real.cos ^ 2) from rfl]
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.cos t) θ) 2]
    rw [Real.deriv_cos]
    ring
  -- derivative of the density `sin θ · cos²θ · sin(2θ)`
  have hF : deriv (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t)) θ
      = (Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * (2 * Real.cos θ * -Real.sin θ)) * Real.sin (2 * θ)
        + Real.sin θ * Real.cos θ ^ 2 * (Real.cos (2 * θ) * 2) := by
    rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t))
        = ((fun t : ℝ => Real.sin t * Real.cos t ^ 2) * (fun t : ℝ => Real.sin (2 * t))) from rfl]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
        = ((fun t : ℝ => Real.sin t) * (fun t : ℝ => Real.cos t ^ 2)) from rfl]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    have h1 : deriv (fun t : ℝ => Real.sin t) θ = Real.cos θ := by
      rw [show (fun t : ℝ => Real.sin t) = Real.sin from rfl]
      exact (Real.hasDerivAt_sin θ).deriv
    rw [h1, hcos2, hsin2]
  -- unfold `C0h = 9 · (density)` and apply the computation
  rw [show C0h = (fun t : ℝ => 9 * (Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t))) from by
        funext t
        simp only [C0h, Spaces.K]
        ring]
  rw [deriv_const_mul (9 : ℝ)
        (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Real.sin (2 * t)) θ)]
  rw [hF]
  -- the trigonometric bookkeeping
  simp only [C0g, Real.sin_two_mul, Real.cos_two_mul]
  ring_nf
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [show Real.sin θ ^ 3 = Real.sin θ * Real.sin θ ^ 2 from by ring]
  rw [hs]
  ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_Frad_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

namespace CommutZ

/-! ## Analyticity of the three rational profiles -/




/-! ## Analyticity of the `z`-profile `G` -/


end CommutZ

/-! ## The main statement -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_SumI =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 4000000



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.CommutZ_mult =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The one-variable operator `DzR` of `CTDefs` is `z ↦ z ∂_z` -/




/-! ## The angular Leibniz rule -/

/-- `D_θ^i` commutes with multiplication by a function of `z` alone. -/
theorem DthIter_mulZm (i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => m z * f z θ)
      = fun z θ => m z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.pth,
        deriv_const_mul_field]
      ring

/-! ## The radial Leibniz rule -/


/-! ## Locality of `D_z`-iterates in the `z`-variable -/


/-! ## The mixed Leibniz rule -/


/-! ## The pointwise bound for the `H^n`-integrand -/


/-! ## The target lemma -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Dz_near_zero_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **Near-zero coercivity data.**  If `f` is smooth on a neighbourhood of the closed
quadrant and the boundary quantity `z (D_z f · w)²` vanishes at `z = 0⁺` for every
`θ ∈ [0,π/2]`, then near `z = 0` the function `D_z f`, the boundary quantity
`z (D_z f · w)²` and the derivative `∂_z (z (D_z f · w)²)` are all bounded by the powers
of `z` given below. -/
theorem Dz_near_zero_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
        |Spaces.Dz f z θ| ≤ C * z ^ 2 ∧
        |z * (Spaces.Dz f z θ * Spaces.w z) ^ 2| ≤ C * z ∧
        |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C := by
  -- The boundary condition forces `∂_z f(0,θ) = 0`.
  have h0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0 := Dz_zero_at_zero f hsm hbd
  -- Hence `∂_z f = O(z)` and `∂_z² f = O(1)` uniformly on a small box.
  obtain ⟨M, δ, hδpos, hδle1, hMnn, hbdM⟩ := Dz_bound_near_zero f hsm h0
  set C : ℝ := max 1 (max M (80 * M ^ 2)) with hCdef
  have hCM : M ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left M (80 * M ^ 2)) (le_max_right 1 (max M (80 * M ^ 2)))
  have hC80 : 80 * M ^ 2 ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right M (80 * M ^ 2)) (le_max_right 1 (max M (80 * M ^ 2)))
  have hC16 : 16 * M ^ 2 ≤ C := by
    have h1 : (16:ℝ) * M ^ 2 ≤ 80 * M ^ 2 := by nlinarith [sq_nonneg M]
    exact le_trans h1 hC80
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨C, δ, hCpos, hδpos, ?_⟩
  intro z hz θ hθ
  obtain ⟨h1z, h2z⟩ := hbdM z hz θ hθ
  have hzpos : 0 < z := hz.1
  have hzle1 : z ≤ 1 := le_of_lt (lt_of_lt_of_le hz.2 hδle1)
  -- (1) `|D_z f| ≤ C z²`.
  have hDzb : |Spaces.Dz f z θ| ≤ M * z ^ 2 := by
    have hstep : |Spaces.Dz f z θ| = z * |Spaces.pz f z θ| := by
      rw [Spaces.Dz, abs_mul, abs_of_pos hzpos]
    rw [hstep]
    calc z * |Spaces.pz f z θ| ≤ z * (M * z) :=
          mul_le_mul_of_nonneg_left h1z (le_of_lt hzpos)
      _ = M * z ^ 2 := by ring
  -- (2) `|z (D_z f · w)²| ≤ C z`.
  have hw : |Spaces.w z| ≤ 4 / z ^ 2 := by
    have h1 : |Spaces.w z| = (1 + z) ^ 2 / z ^ 2 := by
      rw [Spaces.w, abs_div, abs_of_nonneg (sq_nonneg (1 + z)), abs_of_nonneg (sq_nonneg z)]
    rw [h1]
    have h1z2 : (1 + z) ^ 2 ≤ 4 := by
      have hprod : 0 ≤ (1 - z) * (z + 3) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact div_le_div_of_nonneg_right h1z2 (sq_nonneg z)
  have hDzw : |Spaces.Dz f z θ * Spaces.w z| ≤ 4 * M := by
    rw [abs_mul]
    calc |Spaces.Dz f z θ| * |Spaces.w z| ≤ (M * z ^ 2) * (4 / z ^ 2) :=
          mul_le_mul hDzb hw (abs_nonneg _) (mul_nonneg hMnn (sq_nonneg z))
      _ = 4 * M := by field_simp
  -- (3) `|∂_z (z (D_z f · w)²)| ≤ C`.
  have h3 : |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C := by
    have h := Dz_deriv_bound f hsm hθ hzpos hzle1 h1z h2z
    have hval : 32 * M * M + 48 * M ^ 2 = 80 * M ^ 2 := by ring
    rw [hval] at h
    linarith [h, hC80]
  refine ⟨?_, ?_, h3⟩
  · calc |Spaces.Dz f z θ| ≤ M * z ^ 2 := hDzb
      _ ≤ C * z ^ 2 := mul_le_mul_of_nonneg_right hCM (sq_nonneg z)
  · have hsq : (Spaces.Dz f z θ * Spaces.w z) ^ 2 ≤ (4 * M) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4 * M)]
      exact hDzw
    rw [abs_mul, abs_of_pos hzpos, abs_of_nonneg (sq_nonneg _)]
    calc z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 ≤ z * (4 * M) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (le_of_lt hzpos)
      _ = 16 * M ^ 2 * z := by ring
      _ ≤ C * z := mul_le_mul_of_nonneg_right hC16 (le_of_lt hzpos)

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkMem_congr_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

set_option autoImplicit false

/-
# Congruence of `HkMem` on the positive half-line

`HkMem α k f` is an *integrability* statement about the integrand `HkIntegrand α k f`,
which is built out of the iterated differential operators `DzIter i` and `mixed j i`
applied to `f`, together with weights depending only on `(z,θ)`.

Because every differential operator is local, two functions that agree on
`(0,∞) × [0,π/2]` have the same `HkIntegrand` at every *interior* point of the domain
`[0,∞) × [0,π/2]` (this is `CommutZ_HkIntegrand_congr_pt`).  The only points not covered
are those with `z = 0` or `θ ∈ {0, π/2}`, i.e. two null sets.  Hence:
* for every `z > 0` the two `θ`-slices are equal a.e. on `Iθ`, so integrability transfers;
* at `z = 0` the integrand vanishes identically, since the weight `w` vanishes there;
* consequently also the outer `z`-integrals agree everywhere on `Iz`.

This file records these facts and deduces `HkMem`-congruence.
-/

/-- At `z = 0` the `H^k` integrand vanishes identically, because the radial weight `w`
vanishes there (Lean's totalised division gives `w 0 = 1/0 = 0`). -/
theorem HkIntegrand_zero_left (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    HkIntegrand α k f 0 θ = 0 := by
  simp [HkIntegrand, Wt, wTheta, w]

/-- Two functions that agree on the open angle interval `(0,π/2)` agree almost everywhere
on `Iθ = [0,π/2]`. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    f =ᵐ[volume.restrict Iθ] g := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

theorem HkMem_congr_Ioi (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ} (hu : Work.Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ, u z θ = v z θ) :
    Work.Spaces.HkMem α k v := by
  obtain ⟨hu1, hu2⟩ := hu
  -- The `θ`-slices of the integrands agree a.e. for every `z > 0`.
  have hae : ∀ z ∈ Set.Ioi (0 : ℝ),
      HkIntegrand α k v z =ᵐ[volume.restrict Iθ] HkIntegrand α k u z :=
    fun z hz => ae_eq_of_eqOn_Ioo
      (fun θ hθ => (CommutZ_HkIntegrand_congr_pt α k u v h z hz θ hθ).symm)
  -- The outer `z`-integrals agree on all of `Iz` (`z = 0` is the trivial case).
  have hint : ∀ z ∈ Iz, ∫ θ in Iθ, HkIntegrand α k u z θ
      = ∫ θ in Iθ, HkIntegrand α k v z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp [HkIntegrand_zero_left]
    · exact (integral_congr_ae (hae z hzpos)).symm
  constructor
  · -- Slicewise integrability of the integrand of `v`.
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp only [HkIntegrand_zero_left]
      exact integrableOn_zero
    · exact Integrable.congr (hu1 z hz) (hae z hzpos).symm
  · -- Integrability of the outer integral of `v`, by congruence with `u`.
    exact IntegrableOn.congr_fun hu2 (fun z hz => hint z hz) measurableSet_Ici

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.I2Mem_mul_of_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The elementary AM–GM bound `|a·b| ≤ (a²+b²)/2`, used to dominate the product of two
`L²`-functions by the sum of their squares. -/
private theorem abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.IBP_of_zsupport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Smoothness of the weight `w` on `(0,∞)` -/



/-! ## Continuity of the derivative of the boundary term, slicewise -/


/-! ## Continuity of the joint integrands on the box -/



/-! ## The main theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L12f_contDiffOn_infty =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Note: the imports are those needed for this proof (`CTDefs` for `L12f`, `contDiffOn_infty_integral_Itheta`
-- for the smoothness of the parametric `θ`-integral, `FM.Core2` for `hasDerivAt_L12`).

namespace Work.Coercivity

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Integrability of one tail propagates to all tails -/


/-! ## The angular density is `C^∞` -/


/-! ## The main theorem -/


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.T4aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The radial factor `2z²/(1+z)³` of `T4`. -/
def T4g (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The half angular weight `sin(2θ)^{-γ/2}`, whose square is `sin(2θ)^{-γ}`. -/
def T4h (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))

/-- The `L²` factor of the Cauchy–Schwarz estimate carrying the angular data and the
radial weight: `Γ(θ)·g(z)·sin(2θ)^{-γ/2}·w(z)`. -/
def T4A (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1

/-- The `L²` factor of the Cauchy–Schwarz estimate carrying the unknown:
`sin(2θ)^{-γ/2}·w(z)·D_θ f(z,θ)`. -/
def T4B (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  T4h α p.2 * Spaces.w p.1 * Spaces.Dth f p.1 p.2

/-- The integrand `D_θΓ(z,θ)·g(z)·sin(2θ)^{-γ}·w(z)²·D_θ f(z,θ)`: this is
`T4 α f z θ · D_θ f z θ · thetaW α z θ` divided by `C0 f / c α`. -/
def T4W (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  DthGam α p.1 p.2 * T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
    * (Spaces.w p.1) ^ 2 * Spaces.Dth f p.1 p.2

/-- The measure of the quadrant: the product of the restrictions of Lebesgue measure
to `Iz = [0,∞)` and `Iθ = [0,π/2]`. -/
def T4P : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)

/-- The angular quantity `∫_θ Γ(θ)² sin(2θ)^{-γ}` controlling the `L²` norm of `T4A`. -/
def T4J (α : ℝ) : ℝ :=
  ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-! ## Elementary properties -/

theorem T4g_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ T4g z := by
  rw [T4g]
  exact div_nonneg (by positivity) (by positivity)

theorem T4h_sq (α θ : ℝ) (hθ : 0 ≤ Real.sin (2 * θ)) :
    (T4h α θ) ^ 2 = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  rw [T4h]
  exact rpow_neg_sq _ _ hθ

theorem T4h_nonneg (α θ : ℝ) (hθ : 0 ≤ Real.sin (2 * θ)) : 0 ≤ T4h α θ := by
  rw [T4h]
  exact Real.rpow_nonneg hθ _

/-- Pointwise description of `(T4A α p)²` as a product of a function of `p.1` and a
function of `p.2`, on the angular interval. -/
theorem T4A_sq_eq (α : ℝ) {p : ℝ × ℝ} (hθ : p.2 ∈ Spaces.Iθ) :
    (T4A α p) ^ 2 = ((T4g p.1) ^ 2 * (Spaces.w p.1) ^ 2)
      * ((Spaces.Gam α p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [T4A, mul_pow, mul_pow, mul_pow, T4h_sq α p.2 hsin]
  ring

/-- Pointwise description of `(T4B α f p)²`. -/
theorem T4B_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {p : ℝ × ℝ} (hθ : p.2 ∈ Spaces.Iθ) :
    (T4B α f p) ^ 2
      = Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * (Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [T4B, mul_pow, mul_pow, T4h_sq α p.2 hsin]
  ring


/-! ## Measurability -/

theorem measurable_T4g : Measurable T4g := by
  unfold T4g
  exact (measurable_const.mul (measurable_id.pow_const (2 : ℕ))).div
    ((measurable_const.add measurable_id).pow_const (3 : ℕ))

theorem measurable_T4h (α : ℝ) : Measurable (T4h α) := by
  unfold T4h
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

theorem measurable_w : Measurable Spaces.w := by
  unfold Spaces.w
  exact ((measurable_const.add measurable_id).pow_const (2 : ℕ)).div
    (measurable_id.pow_const (2 : ℕ))

theorem measurable_Gam (α : ℝ) : Measurable (fun θ : ℝ => Spaces.Gam α θ) := by
  unfold Spaces.Gam
  exact (Real.measurable_sin.mul (Real.measurable_cos.pow_const (2 : ℕ))).pow_const (α / 3)

theorem measurable_DthGam (α : ℝ) : Measurable (fun θ : ℝ => DthGam α 0 θ) := by
  have h : (fun θ : ℝ => DthGam α 0 θ)
      = fun θ => Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ := by
    funext θ
    rw [DthGam_eq]
  rw [h]
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul (measurable_deriv _)

theorem measurable_DthGam_prod (α : ℝ) : Measurable (fun p : ℝ × ℝ => DthGam α p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => DthGam α p.1 p.2)
      = fun p => Real.sin (2 * p.2) * deriv (fun t => Spaces.Gam α t) p.2 := by
    funext p
    rw [DthGam_eq]
  rw [h]
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).mul
    ((measurable_deriv _).comp measurable_snd)

theorem aesm_T4A (α : ℝ) : AEStronglyMeasurable (T4A α) T4P := by
  have h1 : Measurable (fun p : ℝ × ℝ => Spaces.Gam α p.2) :=
    (measurable_Gam α).comp measurable_snd
  have h2 : Measurable (fun p : ℝ × ℝ => T4g p.1) := measurable_T4g.comp measurable_fst
  have h3 : Measurable (fun p : ℝ × ℝ => T4h α p.2) := (measurable_T4h α).comp measurable_snd
  have h4 : Measurable (fun p : ℝ × ℝ => Spaces.w p.1) := measurable_w.comp measurable_fst
  have hm : Measurable (fun p : ℝ × ℝ =>
      Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1) :=
    ((h1.mul h2).mul h3).mul h4
  have hfun : T4A α = fun p : ℝ × ℝ => Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1 := rfl
  rw [hfun]
  exact hm.aestronglyMeasurable

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.XetaDz_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Scalar `rpow` identity: for `s ≥ 0` and reals `w`, `a`,
`(w / s ^ a) * (w / s ^ a) = w ^ 2 * s ^ (-(2 * a))`.

This is the algebraic core of the identities `D_z a · D_z b · ρη = XetaDz a · XetaDz b`
(and similarly for the `η`-block `Xeta`): the block carries the weight `w / √(sin 2θ^η)`,
whose square is `w² · sin(2θ)^{-η}`. -/
theorem div_rpow_mul_self_eq (s w a : ℝ) (hs : 0 ≤ s) :
    (w / s ^ a) * (w / s ^ a) = w ^ 2 * s ^ (-(2 * a)) := by
  have h2 : (s ^ (-a)) ^ 2 = s ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast (s ^ (-a)) 2]
    rw [show -(2 * a) = -a * 2 by ring, Real.rpow_mul hs]
    norm_num
  have h1 : w / s ^ a = w * s ^ (-a) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs a]
  calc (w / s ^ a) * (w / s ^ a) = (w * s ^ (-a)) * (w * s ^ (-a)) := by rw [h1]
    _ = w ^ 2 * (s ^ (-a)) ^ 2 := by ring
    _ = w ^ 2 * s ^ (-(2 * a)) := by rw [h2]

/-- `D_z a · D_z b · ρη = XetaDz a · XetaDz b`: the product of the two `D_z¹`-blocks of the
`ℋ¹` integrand reproduces the weighted pairing integrand `D_z a · D_z b · ρη`. -/
theorem XetaDz_mul_eq (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    XetaDz a z θ * XetaDz b z θ = Spaces.Dz a z θ * Spaces.Dz b z θ * lamEta z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    have h1 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    constructor <;> linarith [Real.pi_pos]
  have hkey : (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) *
        (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))
      = Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.eta) := by
    have h := div_rpow_mul_self_eq (Real.sin (2 * θ)) (Spaces.w z) (Spaces.eta / 2) hs
    simpa [show -(2 * (Spaces.eta / 2)) = -Spaces.eta by ring] using h
  simp only [XetaDz, lamEta]
  rw [show (Spaces.Dz a z θ * (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))) *
          (Spaces.Dz b z θ * (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)))
        = Spaces.Dz a z θ * Spaces.Dz b z θ *
          ((Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) *
           (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2))) by ring]
  rw [hkey]

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.Xeta_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The pointwise identity `Xeta a · Xeta b = a · b · lamEta` on the angular domain
`Iθ = [0, π/2]`: the square of the `η`-weight `w/√(sin 2θ⁽η⁾)` reproduces the weight
`lamEta = w²·sin(2θ)^(-η)`.  This is what lets the `ℋ¹` pairing `∫ a·b·ρη` be rewritten
as the `L²` pairing `∫ Xeta a · Xeta b` of the weighted blocks. -/
theorem Xeta_mul_eq (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Xeta a z θ * Xeta b z θ = a z θ * b z θ * lamEta z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hkey : (Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2
      = Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-Spaces.eta) := by
    rw [div_pow, hsq, Real.rpow_neg hs]
    ring
  rw [Xeta, Xeta, lamEta]
  rw [← hkey]
  ring

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.XgamDth_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The squared angular weight: `w_θ(θ)² = sin(2θ)^{-γ}` for `θ ∈ Iθ`. -/
theorem wTheta_mul_self (α θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.wTheta α θ * Spaces.wTheta α θ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h := rpow_neg_sq (Real.sin (2 * θ)) (Spaces.gam α) hs0
  rw [Spaces.wTheta, ← sq]
  exact h

/-- The product weight `W = w·w_θ` of the `D_θ`-blocks squares to the `D_θ`-pairing
weight `ργ = lamGam α`. -/
theorem Wt_mul_self (α z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.Wt α z θ * Spaces.Wt α z θ = lamGam α z θ := by
  rw [Spaces.Wt, lamGam]
  rw [show (Spaces.w z * Spaces.wTheta α θ) * (Spaces.w z * Spaces.wTheta α θ)
      = (Spaces.w z) ^ 2 * (Spaces.wTheta α θ * Spaces.wTheta α θ) by ring]
  rw [wTheta_mul_self α θ hθ]

/-- The two `D_θ`-blocks multiply to `D_θ a · D_θ b · ργ`. -/
theorem XgamDth_mul_eq (α : ℝ) (a b : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    XgamDth α a z θ * XgamDth α b z θ
      = Spaces.Dth a z θ * Spaces.Dth b z θ * lamGam α z θ := by
  simp only [XgamDth]
  calc (Spaces.Dth a z θ * Spaces.Wt α z θ) * (Spaces.Dth b z θ * Spaces.Wt α z θ)
      = (Spaces.Dth a z θ * Spaces.Dth b z θ) * (Spaces.Wt α z θ * Spaces.Wt α z θ) := by
        ring
    _ = (Spaces.Dth a z θ * Spaces.Dth b z θ) * lamGam α z θ := by
        rw [Wt_mul_self α z θ hθ]
    _ = Spaces.Dth a z θ * Spaces.Dth b z θ * lamGam α z θ := by ring

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.box_slice_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem box_slice_ftc (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    ∫ z in Set.Ioo 0 R, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 := by
  set G : ℝ → ℝ := fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 with hG
  -- the slice is smooth (hence differentiable) on `(0,∞)`
  have hcd : ContDiffOn ℝ ⊤ G (Set.Ioi (0 : ℝ)) := by
    rw [hG]
    exact contDiffOn_BoxG_slice f hsm hθ
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) R, DifferentiableAt ℝ G x := fun x hx =>
    (hcd.differentiableOn (by decide)).differentiableAt (isOpen_Ioi.mem_nhds hx.1)
  -- the derivative of the slice is bounded, hence integrable, on `(0,R)`
  obtain ⟨M, _hMpos, hM⟩ := box_joint_bound f hsm hC hR
  have hInt : IntegrableOn (deriv G) (Set.Ioo (0 : ℝ) R) := by
    refine Measure.integrableOn_of_bounded (M := M) ?_ ?_ ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · exact (measurable_deriv G).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
      rw [Real.norm_eq_abs]
      exact hM x hx θ hθ
  -- the two boundary values
  have h0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hG]
    simpa using hbd θ hθ
  have hcont : ContinuousAt G R :=
    ((hcd.differentiableOn (by decide)).differentiableAt (isOpen_Ioi.mem_nhds hR)).continuousAt
  -- fundamental theorem of calculus for the slice
  have hftc : ∫ x in Set.Ioo (0 : ℝ) R, deriv G x = G R := by
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) R, HasDerivAt G (deriv G x) x := fun x hx =>
      (hdiff x hx).hasDerivAt
    have hint' : IntervalIntegrable (deriv G) volume (0 : ℝ) R :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mpr hInt
    have hb : Tendsto G (𝓝[<] R) (𝓝 (G R)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR hderiv hint' h0 hb
    rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo] at h
    simpa using h
  rw [hG] at hftc ⊢
  exact hftc

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.cos_sin_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.dth_LGammaT_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The four summands of `𝓛_Γ^T` and their `θ`-derivatives

`𝓛_Γ^T f = 𝓛 f - (2zΓ/(c(1+z)²))L₁₂(f) - Transport f + (Γ/c)(2z²/(1+z)³)C₀(f)`,
where `C₀(f) = L₁₂(Transport f)(0)`.  The two "Γ-correction" summands are packaged
as `T1fun` and `T4fun`; since `L₁₂(f)` and `C₀(f)` do not depend on `θ`, their
`θ`-derivatives are the `D_θΓ`-multiples appearing in `T2` and `T4`. -/

/-- The `L₁₂`-term of `𝓛_Γ`: `(2zΓ(θ)/(c(1+z)²))·L₁₂(f)(z)`. -/
def T1fun (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- The projector term of `𝓛_Γ^T`: `(Γ(θ)/c)(2z²/(1+z)³)·C₀(f)`. -/
def T4fun (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * C0 f

/-- `𝓛_Γ^T` is the sum of the coercive part `𝓛 f` and the three corrections. -/
theorem LGammaT_eq_sum (α : ℝ) (f : ℝ → ℝ → ℝ) :
    LGammaT α f = fun z θ =>
      L f z θ - T1fun α f z θ - Transport f z θ + T4fun α f z θ := by
  funext z θ
  simp only [LGammaT, LGamma, Proj, T1fun, T4fun, C0]
  ring

/-- `Γ` is differentiable on the open angular interval, for every exponent `α`. -/
theorem differentiableAt_Gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun t => Spaces.Gam α t) θ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hG : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by positivity
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  exact (hprod.rpow_const (p := α / 3) (Or.inl hG)).differentiableAt




/-- The `θ`-derivative of the transport term: `∂_θ(3 D_θ f/(1+z)) = (3/(1+z))∂_θ D_θ f`. -/
theorem pth_Transport (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pth (Transport f) z θ = (3 / (1 + z)) * Spaces.pth (Spaces.Dth f) z θ := by
  show deriv (fun θ' => Transport f z θ') θ = _
  have e : (fun θ' => Transport f z θ')
      = (fun θ' => (3 / (1 + z)) * Spaces.Dth f z θ') := by
    funext θ'; simp only [Transport]; ring
  rw [e, deriv_const_mul_field]
  rfl

/-- The `z`-derivative of `D_θ f`, used to identify `𝓛(D_θ f)`. -/
theorem pz_Dth_val (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.pz (Spaces.Dth f) z θ = Real.sin (2 * θ) * Spaces.pz (Spaces.pth f) z θ := by
  show deriv (fun z' => Spaces.Dth f z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Spaces.pth f z' θ) z
  have e : (fun z' => Spaces.Dth f z' θ)
      = (fun z' => Real.sin (2 * θ) * Spaces.pth f z' θ) := by
    funext z'; simp only [Spaces.Dth]
  rw [e, deriv_const_mul_field]





end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.dth_bd0_of_IBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false







end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.dth_box_domination =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary analytic helpers -/




/-! ## The four pointwise estimates -/






end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.dth_integrands_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.gamDth_l2_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The pointwise form of the paper's condition `(GammaAssumption2)`:
`(D_θΓ)² ≤ 4α²Γ²`.  Indeed `D_θΓ = sin(2θ) ∂_θΓ` (`DthGam_eq`), so the hypothesis
`|D_θΓ| ≤ 2αΓ` becomes this after squaring. -/
theorem DthGam_sq_le_GamSq (α : ℝ) (hΓ2 : GammaPointwiseBnd α) (θ : ℝ)
    (hθ : θ ∈ Spaces.Iθ) :
    (DthGam α 0 θ) ^ 2 ≤ 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2 := by
  have h := hΓ2 θ hθ
  change (Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ) ^ 2
      ≤ 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2
  set g : ℝ := deriv (fun t => Spaces.Gam α t) θ with hg
  have hb : 0 ≤ 2 * α * Spaces.Gam α θ := le_trans (abs_nonneg _) h
  have habs : |Real.sin (2 * θ) * g| ≤ |2 * α * Spaces.Gam α θ| := by
    rwa [abs_of_nonneg hb]
  have hsq := sq_le_sq.mpr habs
  calc (Real.sin (2 * θ) * g) ^ 2 ≤ (2 * α * Spaces.Gam α θ) ^ 2 := hsq
    _ = 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring

/-- `Γ(θ)² ≤ sin(2θ)^{2α/3}` on the angular interval, for `α > 0`.

Since `Γ = (sin θ cos²θ)^{α/3}` and `sin θ cos²θ ≤ sin(2θ)` on `Iθ` (because
`cos θ ≤ 1 ≤ 2`), this is monotonicity of `rpow` with the nonnegative exponent `2α/3`. -/
theorem Gam_sq_le_sin_two (α : ℝ) (hα : 0 < α) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) := by
  obtain ⟨hb0, hb1⟩ := Spaces.sin_mul_cos_sq_mem_Icc θ hθ
  have hsq : (Spaces.Gam α θ) ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Spaces.Gam, ← Real.rpow_natCast ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) 2]
    calc ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) ^ (2 : ℝ)
        = (Real.sin θ * Real.cos θ ^ 2) ^ ((α / 3) * 2) :=
          (Real.rpow_mul hb0 (α / 3) 2).symm
      _ = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
          rw [show α / 3 * 2 = 2 * α / 3 by ring]
  rw [hsq]
  refine Real.rpow_le_rpow hb0 ?_ (by positivity)
  rw [Real.sin_two_mul]
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsc : 0 ≤ Real.sin θ * Real.cos θ := mul_nonneg hs hc0
  have hc2 : Real.cos θ - 2 ≤ 0 := by linarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hsc hc2]

/-- **The pointwise estimate of the integrand of `gamDth_l2_bound`**:
on `Iθ`,
`sin(2θ)^{-γ}(D_θΓ)² ≤ 4α² sin(2θ)^{2α/3-γ}`.

It combines `DthGam_sq_le_GamSq` (from `(GammaAssumption2)`), `Gam_sq_le_sin_two`, and the
`rpow` addition `sin(2θ)^{-γ} sin(2θ)^{2α/3} = sin(2θ)^{2α/3-γ}` (the exponent is
nonzero because `γ = 1 + α/10 > 2α/3` for `α ≤ 1`). -/
theorem gamDth_integrand_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ2 : GammaPointwiseBnd α) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
  have hD := DthGam_sq_le_GamSq α hΓ2 θ hθ
  have hG := Gam_sq_le_sin_two α hα θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne : 2 * α / 3 + (-(Spaces.gam α)) ≠ 0 := by
    have hg : 2 * α / 3 < Spaces.gam α := by
      rw [Spaces.gam]; nlinarith [hα1]
    linarith
  have hcomb : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ (2 * α / 3)
      = (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
    rw [show 2 * α / 3 - Spaces.gam α = 2 * α / 3 + (-(Spaces.gam α)) by ring,
      Real.rpow_add' hs0 hne]
    ring
  calc (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (4 * α ^ 2 * (Spaces.Gam α θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hD hw0
    _ = 4 * α ^ 2 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Gam α θ) ^ 2) := by
        ring
    _ ≤ 4 * α ^ 2 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * (Real.sin (2 * θ)) ^ (2 * α / 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hw0) (by positivity)
    _ = 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by rw [hcomb]

theorem gamDth_l2_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΓ2 : GammaPointwiseBnd α) :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ 100 * α := by
  set q : ℝ := 1 - 17 * α / 30 with hqdef
  have hq0 : 0 < q := by simp only [hqdef]; linarith
  have hq1 : q < 1 := by simp only [hqdef]; linarith
  obtain ⟨hBint, hBval⟩ := integral_sin_two_neg_rpow_le q hq0 hq1
  have hgint : IntegrableOn (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Spaces.Iθ := hBint.const_mul _
  have hfnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2)
      ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have h := gamDth_integrand_le α hα hα1 hΓ2 θ hθ
    have hexp : 2 * α / 3 - Spaces.gam α = -q := by
      simp only [hqdef, Spaces.gam]; ring
    rwa [hexp] at h
  have hmono := MeasureTheory.integral_mono_of_nonneg hfnn hgint hle
  have hval : ∫ θ in Spaces.Iθ, 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      = 4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) := by
    rw [MeasureTheory.integral_const_mul]
  have hnum : 4 * α ^ 2 * (4 / (17 * α / 30)) = 480 * α / 17 := by
    field_simp
    ring
  calc ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ ∫ θ in Spaces.Iθ, 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q) := hmono
    _ = 4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) := hval
    _ ≤ 4 * α ^ 2 * (4 / (1 - q)) := mul_le_mul_of_nonneg_left hBval (by positivity)
    _ ≤ 100 * α := by
        have h1 : 1 - q = 17 * α / 30 := by simp only [hqdef]; ring
        rw [h1, hnum]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.mixed_sep2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.Coercivity




end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.radial_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Polynomial
open MeasureTheory Set Filter

namespace Work.Coercivity
namespace CT

set_option autoImplicit false

/-! ## The change of variable `u = z/(1+z)` -/













/-! ## `D_z` in the `u` coordinate -/




/-! ## The quotient polynomials `Qseq1`, `Qseq2` -/

/-- The quotient polynomials for `u(1-u)`: `D_u^k (u(1-u)) = u(1-u)·Qseq1 k(u)`. -/
def Qseq1 : ℕ → ℝ[X]
  | 0 => 1
  | (k + 1) => (1 - Polynomial.X) * Qseq1 k - Polynomial.X * Qseq1 k
      + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq1 k)

/-- The quotient polynomials for `u²(1-u)`: `D_u^k (u²(1-u)) = u²(1-u)·Qseq2 k(u)`. -/
def Qseq2 : ℕ → ℝ[X]
  | 0 => 1
  | (k + 1) => 2 * (1 - Polynomial.X) * Qseq2 k - Polynomial.X * Qseq2 k
      + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq2 k)

/-- `Rseq1 k(u) := u(1-u)·Qseq1 k(u) = D_u^k(u(1-u))`. -/
def Rseq1 (k : ℕ) : ℝ[X] := Polynomial.X * (1 - Polynomial.X) * Qseq1 k

/-- `Rseq2 k(u) := u²(1-u)·Qseq2 k(u) = D_u^k(u²(1-u))`. -/
def Rseq2 (k : ℕ) : ℝ[X] := Polynomial.X ^ 2 * (1 - Polynomial.X) * Qseq2 k

@[simp] theorem Qseq1_zero : Qseq1 0 = 1 := rfl

@[simp] theorem Qseq2_zero : Qseq2 0 = 1 := rfl

@[simp] theorem Rseq1_zero : Rseq1 0 = Polynomial.X * (1 - Polynomial.X) := by
  simp [Rseq1]

@[simp] theorem Rseq2_zero : Rseq2 0 = Polynomial.X ^ 2 * (1 - Polynomial.X) := by
  simp [Rseq2]





/-! ## Iterates of `D_u` on the two base polynomials -/



/-! ## The model identities `D_z^k ∘ u = (D_u)^k` -/



/-! ## The coefficient functions `pcoef` and `Wcoef` -/



/-! ## Bounding a polynomial on the unit interval -/


/-! ## The weighted bounds on `Rseq1`, `Rseq2` -/



/-! ## The two per-`k` estimates -/



end CT

/-! ## The target theorem -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.thetaBoxAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Almost-everywhere equal sets -/




/-! ## Integrability on an interval or a box -/





/-! ## The Fubini bridge -/



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_add_of_PairHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem wip_add_of_PairHonest (ρ A₁ A₂ B : ℝ → ℝ → ℝ)
    (h₁ : PairHonest ρ A₁ B) (h₂ : PairHonest ρ A₂ B) :
    wip ρ (A₁ + A₂) B = wip ρ A₁ B + wip ρ A₂ B := by
  simp only [PairHonest, I2Mem] at h₁ h₂
  obtain ⟨hs₁, hi₁⟩ := h₁
  obtain ⟨hs₂, hi₂⟩ := h₂
  simp only [wip]
  have hpt : ∀ z ∈ Spaces.Iz,
      (∫ θ in Spaces.Iθ, (A₁ z θ + A₂ z θ) * B z θ * ρ z θ)
        = (∫ θ in Spaces.Iθ, A₁ z θ * B z θ * ρ z θ)
            + ∫ θ in Spaces.Iθ, A₂ z θ * B z θ * ρ z θ := by
    intro z hz
    have hcongr : (fun θ => (A₁ z θ + A₂ z θ) * B z θ * ρ z θ)
        = (fun θ => A₁ z θ * B z θ * ρ z θ + A₂ z θ * B z θ * ρ z θ) := by
      funext θ; ring
    rw [hcongr]
    exact integral_add (hs₁ z hz) (hs₂ z hz)
  rw [show (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (A₁ + A₂) z θ * B z θ * ρ z θ)
        = ∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A₁ z θ * B z θ * ρ z θ)
            + ∫ θ in Spaces.Iθ, A₂ z θ * B z θ * ρ z θ) from by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      exact hpt z hz]
  rw [integral_add hi₁ hi₂]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.Apriori =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- The `ℋ⁴`-norm `|g|_{ℋ⁴}` of the estimates of §Modulation. -/
def H4N (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ := Work.Spaces.HkNorm α 4 g





/-- The triangle inequality for a sum of five terms. -/
theorem abs_sum_le_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  nlinarith [h1, h2, h3, h4, abs_nonneg (a + b + c + d), abs_nonneg (a + b + c),
    abs_nonneg (a + b)]

/-- The triangle inequality for a sum of four terms. -/
theorem abs_sum_le_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  nlinarith [h1, h2, h3, abs_nonneg (a + b + c), abs_nonneg (a + b)]

/-! ## The inputs for `N₀` -/

/-- The per-summand inputs for Proposition `N0Estimate` (tex 1433-1436).  Each field is one of
the paper's estimates for one summand of `\eqref{N0}`:

* `h12`: `I^{N₀}_1 + I^{N₀}_2` is `O(α²)` in `ℋ⁴` — the "direct calculation" using the exact
  form of `Γ` (tex 1398-1402; here via `N0_first_two_eq`);
* `h3`: `|(I^{N₀}_3,g)_{ℋ⁴}| ≤ Cα^{-3/2}|g|³` (tex 1406: `HProductRule` + `L12H`);
* `h4`: the two halves of `I^{N₀}_4` (tex 1410-1414: `WProductRule` + `L12H` and
  `Transport1` + `L12H`), merged into one bound;
* `h5`: the two halves of `I^{N₀}_5` (tex 1416-1421: `WProductRule` + `L12H` and
  `Transport2` + `L12H`), merged;
* `h6`: `I^{N₀}_6` (tex 1423: `Transport3`). -/
structure N0Inputs (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F g : ℝ → ℝ → ℝ) : Prop where
  h12 : H4N α (N01 α F g + N02 α F g) ≤ C * α ^ 2
  h3 : |IP (N03 α F g) g| ≤ C * α ^ (-(3 / 2 : ℝ)) * H4N α g ^ 3
  h4 : |IP (N04 α F g) g|
    ≤ C * (Real.sqrt α + α ^ (-(3 / 2 : ℝ)) * H4N α g) * H4N α g ^ 2
  h5 : |IP (N05 α F g) g|
    ≤ C * (Real.sqrt α + α ^ (-(1 / 2 : ℝ)) * H4N α g) * H4N α g ^ 2
  h6 : |IP (N06 α F g) g| ≤ C * Real.sqrt α * H4N α g ^ 2


/-! ## The inputs for `N` -/

/-- The per-summand inputs for Proposition `NEstimate` (tex 1488-1492).  The fields are the
paper's estimates for `I^{N}_1` (tex 1450-1454: `RemovingL12_R`, `HProductRule`,
`WProductRule`, `WtoH`) and for `I^{N}_2, …, I^{N}_5` (tex 1472-1490: `DivisionBySin`,
`Transport1`, `SpecialTransport`, `WtoH`, `PhiStarRegularity`). -/
structure NInputs (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F Φ g : ℝ → ℝ → ℝ) : Prop where
  h1 : |IP (N1 α F Φ) g| ≤ C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
    + α ^ (-(1 / 2 : ℝ)) * H4N α g ^ 3)
  h25 : |IP (N2 α F Φ) g| + |IP (N3 α F Φ) g| + |IP (N4 α F Φ) g| + |IP (N5 α F Φ) g|
    ≤ C * (α ^ 2 * H4N α g + Real.sqrt α * H4N α g ^ 2
      + α ^ (-(1 / 2 : ℝ)) * H4N α g ^ 3)


/-! ## The inputs for `N_*` -/

/-- The inputs for Proposition `N*Estimate` (tex 1528-1531): the paper's estimate on the
modulation constant `μ` (Proposition `muestimate`, tex 1507) and the elementary pairing bound
`|(g,g)_{ℋ⁴}| + |(g,z∂_zg)_{ℋ⁴}| ≤ |g|_{ℋ⁴}²` (tex 1502, from Cauchy--Schwarz and
`|z∂_zg|_{ℋ⁴} ≤ |g|_{ℋ⁴}`). -/
structure NstarInputs (α μ lam : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (C : ℝ)
    (F Φ g : ℝ → ℝ → ℝ) : Prop where
  hmu : |μ| ≤ C * (α + α ^ (-(3 / 2 : ℝ)) * H4N α g + α ^ (-(5 / 2 : ℝ)) * H4N α g ^ 2)
  hpair : |IP g g| + |IP (Work.Spaces.Dz g) g| ≤ H4N α g ^ 2


/-! ## The combined estimate and the coercivity corollary -/



end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.H4N_GammaTerm_Lop_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## Derivatives of the explicit polynomials `Aᵢ` -/

theorem glop_deriv_Aang_zero (x α : ℝ) : deriv (fun y : ℝ => Aang 0 y α) x = 3 := by
  have h : (fun y : ℝ => Aang 0 y α)
      = fun y : ℝ => (-2) + 3 * y + 0 * y ^ 2 + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_zero]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_one (x α : ℝ) :
    deriv (fun y : ℝ => Aang 1 y α) x = (-8 * α - 12) + 2 * (6 * α + 12) * x := by
  have h : (fun y : ℝ => Aang 1 y α)
      = fun y : ℝ => (8 * α / 3) + (-8 * α - 12) * y + (6 * α + 12) * y ^ 2
          + 0 * y ^ 3 + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_one]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_two (x α : ℝ) :
    deriv (fun y : ℝ => Aang 2 y α) x
      = (16 * α ^ 2 + 48 * α + 48) + 2 * (-24 * α ^ 2 - 120 * α - 144) * x
        + 3 * (12 * α ^ 2 + 72 * α + 96) * x ^ 2 := by
  have h : (fun y : ℝ => Aang 2 y α)
      = fun y : ℝ => (-32 * α ^ 2 / 9) + (16 * α ^ 2 + 48 * α + 48) * y
          + (-24 * α ^ 2 - 120 * α - 144) * y ^ 2 + (12 * α ^ 2 + 72 * α + 96) * y ^ 3
          + 0 * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_two]
    ring
  rw [h, deriv_mono5]
  ring

theorem glop_deriv_Aang_three (x α : ℝ) :
    deriv (fun y : ℝ => Aang 3 y α) x
      = (-256 * α ^ 3 / 9 - 128 * α ^ 2 - 256 * α - 192)
        + 2 * (64 * α ^ 3 + 512 * α ^ 2 + 1440 * α + 1344) * x
        + 3 * (-64 * α ^ 3 - 672 * α ^ 2 - 2240 * α - 2304) * x ^ 2
        + 4 * (24 * α ^ 3 + 288 * α ^ 2 + 1056 * α + 1152) * x ^ 3 := by
  have h : (fun y : ℝ => Aang 3 y α)
      = fun y : ℝ => (128 * α ^ 3 / 27) + (-256 * α ^ 3 / 9 - 128 * α ^ 2 - 256 * α - 192) * y
          + (64 * α ^ 3 + 512 * α ^ 2 + 1440 * α + 1344) * y ^ 2
          + (-64 * α ^ 3 - 672 * α ^ 2 - 2240 * α - 2304) * y ^ 3
          + (24 * α ^ 3 + 288 * α ^ 2 + 1056 * α + 1152) * y ^ 4 + 0 * y ^ 5 := by
    funext y
    simp only [Aang_three]
    ring
  rw [h, deriv_mono5]
  ring

/-- The polynomials `Aᵢ` (`i ≤ 4`) are differentiable. -/
theorem differentiable_Aang (j : ℕ) (hj : j ≤ 4) (α : ℝ) :
    Differentiable ℝ (fun y : ℝ => Aang j y α) := by
  interval_cases j
  · simp only [Aang_zero]; fun_prop
  · simp only [Aang_one]; fun_prop
  · simp only [Aang_two]; fun_prop
  · simp only [Aang_three]; fun_prop
  · simp only [Aang_four]; fun_prop

/-- The recurrence `Aᵢ₊₁ = -4x(1-x)Aᵢ' + (α/3)(6x-4)Aᵢ` for `i ≤ 3`. -/
theorem glop_Aang_succ (j : ℕ) (hj : j ≤ 3) (x α : ℝ) :
    -4 * x * (1 - x) * deriv (fun y : ℝ => Aang j y α) x
      + (α / 3) * (6 * x - 4) * Aang j x α
      = Aang (j + 1) x α := by
  interval_cases j
  · rw [glop_deriv_Aang_zero, Aang_zero, Aang_one]; ring
  · rw [glop_deriv_Aang_one, Aang_one, Aang_two]; ring
  · rw [glop_deriv_Aang_two, Aang_two, Aang_three]; ring
  · rw [glop_deriv_Aang_three, Aang_three, Aang_four]; ring

/-! ## The two building blocks of the `θ`-calculation -/

/-- `D_θ(Γ) = (α/3)(6cos²θ - 4)·Γ` on the open quadrant. -/
theorem glop_Gam_deriv (α θ : ℝ) (_hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Lop (Work.Spaces.Gam α) θ
      = (α / 3) * (6 * Real.cos θ ^ 2 - 4) * Work.Spaces.Gam α θ := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hg : 0 < Real.sin θ * Real.cos θ ^ 2 := mul_pos hsin (pow_pos hcos 2)
  have hcos2' : HasDerivAt (fun y : ℝ => Real.cos y ^ 2) (-2 * Real.cos θ * Real.sin θ) θ := by
    have h : HasDerivAt (fun y : ℝ => Real.cos y * Real.cos y)
        (-2 * Real.cos θ * Real.sin θ) θ := by
      have hh := (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_cos θ)
      have hv : -Real.sin θ * Real.cos θ + Real.cos θ * -Real.sin θ
          = -2 * Real.cos θ * Real.sin θ := by ring
      rw [hv] at hh
      exact hh
    simpa [pow_two] using h
  have hg' : HasDerivAt (fun y : ℝ => Real.sin y * Real.cos y ^ 2)
      (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)) θ := by
    have h := (Real.hasDerivAt_sin θ).mul hcos2'
    convert h using 1
    · ring_nf
      rw [Real.sin_sq]
      ring
  have hderivG : deriv (Work.Spaces.Gam α) θ
      = (α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)) := by
    have hrpow : HasDerivAt (fun y : ℝ => y ^ (α / 3))
        ((α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
        (Real.sin θ * Real.cos θ ^ 2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hg))
    have hcomp := hrpow.comp θ hg'
    have hd := hcomp.deriv
    change deriv ((fun y : ℝ => y ^ (α / 3))
      ∘ (fun y : ℝ => Real.sin y * Real.cos y ^ 2)) θ = _
    rw [hd]
  rw [show Work.Spaces.Lop (Work.Spaces.Gam α) θ
        = Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ from rfl, hderivG,
      show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl,
      Real.sin_two_mul]
  have hgpow : (Real.sin θ * Real.cos θ ^ 2) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
    have h := Real.rpow_add hg (α / 3 - 1) 1
    rw [sub_add_cancel, Real.rpow_one] at h
    rw [h]
    ring
  calc 2 * Real.sin θ * Real.cos θ *
        ((α / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)
          * (Real.cos θ * (3 * Real.cos θ ^ 2 - 2)))
      = (α / 3) * (2 * Real.sin θ * Real.cos θ * Real.cos θ * (3 * Real.cos θ ^ 2 - 2))
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
    _ = (α / 3) * ((6 * Real.cos θ ^ 2 - 4) * (Real.sin θ * Real.cos θ ^ 2))
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
    _ = (α / 3) * (6 * Real.cos θ ^ 2 - 4)
          * ((Real.sin θ * Real.cos θ ^ 2) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1)) := by
        ring
    _ = (α / 3) * (6 * Real.cos θ ^ 2 - 4) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
        rw [hgpow]

/-- The chain rule `D_θ(a(cos²θ)) = -4cos²θ(1-cos²θ)·a'(cos²θ)`. -/
theorem glop_comp_cos_sq (a : ℝ → ℝ) (ha : Differentiable ℝ a) (θ : ℝ) :
    Work.Spaces.Lop (fun θ => a (Real.cos θ ^ 2)) θ
      = -4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) * deriv a (Real.cos θ ^ 2) := by
  show Real.sin (2 * θ) * deriv (fun θ => a (Real.cos θ ^ 2)) θ = _
  have hu : DifferentiableAt ℝ (fun θ : ℝ => Real.cos θ ^ 2) θ := by fun_prop
  have ha' : DifferentiableAt ℝ a (Real.cos θ ^ 2) := ha.differentiableAt
  rw [show (fun θ : ℝ => a (Real.cos θ ^ 2)) = a ∘ (fun θ : ℝ => Real.cos θ ^ 2) from rfl,
    deriv_comp θ ha' hu]
  have hdu : deriv (fun θ : ℝ => Real.cos θ ^ 2) θ = -2 * Real.cos θ * Real.sin θ := by
    have h := ((hasDerivAt_pow 2 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).deriv
    change deriv ((fun x : ℝ => x ^ 2) ∘ Real.cos) θ = -2 * Real.cos θ * Real.sin θ
    rw [h]
    ring
  rw [hdu, Real.sin_two_mul]
  ring_nf
  rw [Real.sin_sq]
  ring

/-! ## The one-step identity -/

/-- One step of the `θ`-calculation: the action of `D_θ` on `Γ(θ)·a(cos²θ)`. -/
theorem glop_step (α : ℝ) (hα : 0 < α) (a : ℝ → ℝ) (ha : Differentiable ℝ a) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * a (Real.cos y ^ 2)) θ
      = Work.Spaces.Gam α θ * (-4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)
          * deriv a (Real.cos θ ^ 2)
          + (α / 3) * (6 * Real.cos θ ^ 2 - 4) * a (Real.cos θ ^ 2)) := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hGam_diff : DifferentiableAt ℝ (Work.Spaces.Gam α) θ := by
    rw [show Work.Spaces.Gam α = fun y : ℝ => (Real.sin y * Real.cos y ^ 2) ^ (α / 3) from rfl]
    exact (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => Real.sin y * Real.cos y ^ 2) θ).rpow_const
      (Or.inl (ne_of_gt (mul_pos hsin (pow_pos hcos 2))))
  have ha_comp : DifferentiableAt ℝ (fun y : ℝ => a (Real.cos y ^ 2)) θ :=
    ha.differentiableAt.comp θ (by fun_prop)
  rw [show (fun y : ℝ => Work.Spaces.Gam α y * a (Real.cos y ^ 2))
      = Work.Spaces.Gam α * (fun y : ℝ => a (Real.cos y ^ 2)) from rfl,
    Work.Spaces.Lop_mul _ _ θ hGam_diff ha_comp]
  rw [glop_Gam_deriv α θ hα hθ, glop_comp_cos_sq a ha θ]
  ring

/-! ## The iterates of `ψ` -/

/-- `D_θ^i ψ(θ) = Γ(θ)·Aᵢ(cos²θ, α)` for `i ≤ 4` and `θ ∈ (0,π/2)`. -/
theorem glop_Lop_iter_psiA (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i] (psiA α)) θ = Work.Spaces.Gam α θ * Aang i (Real.cos θ ^ 2) α := by
  induction i with
  | zero =>
      intro θ hθ
      have hc : c2m θ = 3 * Real.cos θ ^ 2 - 2 := by
        rw [c2m_eq, Real.cos_two_mul, Real.sin_sq]
        ring
      simp only [Function.iterate_zero, id_eq, psiA, Aang_zero]
      rw [hc]
      ring
  | succ j ih =>
      intro θ hθ
      have hj : j ≤ 4 := le_trans (Nat.le_succ j) hi
      have hev : (Work.Spaces.Lop^[j] (psiA α))
          =ᶠ[𝓝 θ] (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
        exact ih hj y hy
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop (Work.Spaces.Lop^[j] (psiA α)) θ
          = Work.Spaces.Lop (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) θ from by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (psiA α)) θ
            = Real.sin (2 * θ) * deriv (fun y => Work.Spaces.Gam α y * Aang j (Real.cos y ^ 2) α) θ
        rw [hev.deriv_eq]]
      rw [glop_step α hα (fun y : ℝ => Aang j y α) (differentiable_Aang j hj α) θ hθ]
      rw [glop_Aang_succ j (by omega) (Real.cos θ ^ 2) α]

/-! ## The pointwise bounds for the polynomials `Aᵢ` -/

/-- Five-term triangle inequality. -/
theorem abs_five_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  linarith

/-- `|A₁(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_one (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (_hα1 : α ≤ 1) :
    |Aang 1 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hW : |4 * x * (1 - x) * (-3)| ≤ 3 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4, abs_of_nonpos (by norm_num : (-3 : ℝ) ≤ 0)]
    linarith
  have hP1 : |18 * x ^ 2 - 24 * x + 8| ≤ 50 := by
    have h2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx.2
    have h2' : 0 ≤ x ^ 2 := pow_nonneg hx0 2
    rw [abs_le]
    constructor <;> nlinarith
  have hR1 : |(α / 3) * (18 * x ^ 2 - 24 * x + 8)| ≤ 50 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 h0 h0 h0
  calc |Aang 1 x α|
      = |4 * x * (1 - x) * (-3) + (α / 3) * (18 * x ^ 2 - 24 * x + 8) + 0 + 0 + 0| := by
        rw [Aang_one]
        ring
    _ ≤ 3 * (4 * x * (1 - x)) + 50 * (α / 3) + 0 + 0 + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1]

/-- `|A₂(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_two (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 2 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk4
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |12 - 24 * x| ≤ 36 := by
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |216 * x ^ 3 - 360 * x ^ 2 + 144 * x| ≤ 720 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32| ≤ 500 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (12 - 24 * x)| ≤ 36 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)| ≤ 720 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32)| ≤ 500 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 hR2 h0 h0
  calc |Aang 2 x α|
      = |4 * x * (1 - x) * (12 - 24 * x) + (α / 3) * (216 * x ^ 3 - 360 * x ^ 2 + 144 * x)
          + (α / 3) ^ 2 * (108 * x ^ 3 - 216 * x ^ 2 + 144 * x - 32) + 0 + 0| := by
        rw [Aang_two]
        ring
    _ ≤ 36 * (4 * x * (1 - x)) + 720 * (α / 3) + 500 * (α / 3) ^ 2 + 0 + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2]

/-- `|A₃(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_three (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 3 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hk3 : (α / 3) ^ 3 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk4
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |-48 + 288 * x - 288 * x ^ 2| ≤ 624 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x| ≤ 14976 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x| ≤ 14400 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP3 : |648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128| ≤ 5000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)| ≤ 624 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)|
      ≤ 14976 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)|
      ≤ 14400 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have hR3 : |(α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128)|
      ≤ 5000 * (α / 3) ^ 3 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 3)]
    have := mul_le_mul_of_nonneg_left hP3 (pow_nonneg hα3 3)
    linarith
  have h0 : |(0 : ℝ)| ≤ 0 := by norm_num
  have hsum := abs_five_le hW hR1 hR2 hR3 h0
  calc |Aang 3 x α|
      = |4 * x * (1 - x) * (-48 + 288 * x - 288 * x ^ 2)
          + (α / 3) * (3168 * x ^ 4 - 6720 * x ^ 3 + 4320 * x ^ 2 - 768 * x)
          + (α / 3) ^ 2 * (2592 * x ^ 4 - 6048 * x ^ 3 + 4608 * x ^ 2 - 1152 * x)
          + (α / 3) ^ 3 * (648 * x ^ 4 - 1728 * x ^ 3 + 1728 * x ^ 2 - 768 * x + 128) + 0| := by
        rw [Aang_three]
        ring
    _ ≤ 624 * (4 * x * (1 - x)) + 14976 * (α / 3) + 14400 * (α / 3) ^ 2 + 5000 * (α / 3) ^ 3
          + 0 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2, hk3]

/-- `|A₄(x,α)| ≤ 10^7(α + 4x(1-x))` on `[0,1]`, `0 < α ≤ 1`. -/
theorem glop_Aang_bound_four (x α : ℝ) (hx : x ∈ Set.Icc 0 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    |Aang 4 x α| ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  have h4 : 0 ≤ 4 * x * (1 - x) := by nlinarith
  have hα3 : 0 ≤ α / 3 := by linarith
  have hk1 : (α / 3) ^ 1 ≤ α := by nlinarith
  have hk2 : (α / 3) ^ 2 ≤ α := by nlinarith
  have hk3 : (α / 3) ^ 3 ≤ α := by nlinarith
  have hk4 : (α / 3) ^ 4 ≤ α := by nlinarith
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ 5 → 0 ≤ x ^ k ∧ x ^ k ≤ 1 := by
    intro k hk0 hk5
    exact ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx.2⟩
  have hV : |192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3| ≤ 14400 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP1 : |57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2 + 3840 * x|
      ≤ 387840 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP2 : |60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2 + 7680 * x|
      ≤ 460800 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP3 : |25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2 + 7680 * x|
      ≤ 240000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hP4 : |3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2 + 3840 * x - 512|
      ≤ 50000 := by
    obtain ⟨h1', h1⟩ := hmono 1 (by norm_num) (by norm_num)
    obtain ⟨h2', h2⟩ := hmono 2 (by norm_num) (by norm_num)
    obtain ⟨h3', h3⟩ := hmono 3 (by norm_num) (by norm_num)
    obtain ⟨h4', h4⟩ := hmono 4 (by norm_num) (by norm_num)
    obtain ⟨h5', h5⟩ := hmono 5 (by norm_num) (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
  have hW : |4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)|
      ≤ 14400 * (4 * x * (1 - x)) := by
    rw [abs_mul, abs_of_nonneg h4]
    have := mul_le_mul_of_nonneg_left hV h4
    linarith
  have hR1 : |(α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2
        + 3840 * x)| ≤ 387840 * (α / 3) := by
    rw [abs_mul, abs_of_nonneg hα3]
    have := mul_le_mul_of_nonneg_left hP1 hα3
    linarith
  have hR2 : |(α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2
        + 7680 * x)| ≤ 460800 * (α / 3) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 2)]
    have := mul_le_mul_of_nonneg_left hP2 (pow_nonneg hα3 2)
    linarith
  have hR3 : |(α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2
        + 7680 * x)| ≤ 240000 * (α / 3) ^ 3 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 3)]
    have := mul_le_mul_of_nonneg_left hP3 (pow_nonneg hα3 3)
    linarith
  have hR4 : |(α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2
        + 3840 * x - 512)| ≤ 50000 * (α / 3) ^ 4 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hα3 4)]
    have := mul_le_mul_of_nonneg_left hP4 (pow_nonneg hα3 4)
    linarith
  have hsum := abs_five_le hW hR1 hR2 hR3 hR4
  calc |Aang 4 x α|
      = |4 * x * (1 - x) * (192 - 2688 * x + 6912 * x ^ 2 - 4608 * x ^ 3)
          + (α / 3) * (57600 * x ^ 5 - 149760 * x ^ 4 + 132480 * x ^ 3 - 44160 * x ^ 2
              + 3840 * x)
          + (α / 3) ^ 2 * (60480 * x ^ 5 - 167040 * x ^ 4 + 162240 * x ^ 3 - 63360 * x ^ 2
              + 7680 * x)
          + (α / 3) ^ 3 * (25920 * x ^ 5 - 77760 * x ^ 4 + 86400 * x ^ 3 - 42240 * x ^ 2
              + 7680 * x)
          + (α / 3) ^ 4 * (3888 * x ^ 5 - 12960 * x ^ 4 + 17280 * x ^ 3 - 11520 * x ^ 2
              + 3840 * x - 512)| := by
        rw [Aang_four]
    _ ≤ 14400 * (4 * x * (1 - x)) + 387840 * (α / 3) + 460800 * (α / 3) ^ 2
          + 240000 * (α / 3) ^ 3 + 50000 * (α / 3) ^ 4 := hsum
    _ ≤ 10 ^ 7 * (α + 4 * x * (1 - x)) := by nlinarith [h4, hα, hk1, hk2, hk3, hk4]

/-! ## The target theorem -/

theorem H4N_GammaTerm_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    ring_nf
    rw [Real.sin_sq]
    ring
  have hb : |Aang i (Real.cos θ ^ 2) α| ≤ 10 ^ 7 * (α + 4 * Real.cos θ ^ 2
      * (1 - Real.cos θ ^ 2)) := by
    interval_cases i
    · exact glop_Aang_bound_one _ _ hxc hα hα1
    · exact glop_Aang_bound_two _ _ hxc hα hα1
    · exact glop_Aang_bound_three _ _ hxc hα hα1
    · exact glop_Aang_bound_four _ _ hxc hα hα1
  rw [glop_Lop_iter_psiA α hα i hi4 θ hθ]
  calc |Work.Spaces.Gam α θ * Aang i (Real.cos θ ^ 2) α|
      = Work.Spaces.Gam α θ * |Aang i (Real.cos θ ^ 2) α| := by
        rw [abs_mul, abs_of_nonneg hGam0]
    _ ≤ Work.Spaces.Gam α θ
          * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hb hGam0
    _ = 10 ^ 7 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
        rw [hsin2]
        ring

end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.H4N_rhoR_numbound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

/-- Elementary numerical bounds for the surviving radial profile coefficients:
each of the five polynomials is dominated by `840 * (1 + z)^k` on `z ≥ 0`. -/
theorem H4N_rhoR_numbound :
    (∀ z : ℝ, 0 ≤ z → |(1:ℝ)| ≤ 840 * (1 + z)^0)
    ∧ (∀ z : ℝ, 0 ≤ z → |2 - 2*z| ≤ 840 * (1 + z)^1)
    ∧ (∀ z : ℝ, 0 ≤ z → |4 - 12*z + 4*z^2| ≤ 840 * (1 + z)^2)
    ∧ (∀ z : ℝ, 0 ≤ z → |8 - 52*z + 52*z^2 - 8*z^3| ≤ 840 * (1 + z)^3)
    ∧ (∀ z : ℝ, 0 ≤ z → |16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4| ≤ 840 * (1 + z)^4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z _
    norm_num
  · intro z _
    rw [abs_le]
    constructor <;> nlinarith
  · intro z _
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  · intro z hz
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, mul_nonneg hz (sq_nonneg z)]
  · intro z hz
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg z, mul_nonneg hz (sq_nonneg z), sq_nonneg (z^2)]

end Work.Construction
end
-- ===== merged: Submission.Work.Construction.H4N_rhoR_shape12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

open scoped Topology

/-- The elementary derivative of the radial factor `ρ(z) = z²/(1+z)⁴` away from `z = -1`. -/
private lemma deriv_rhoR (x : ℝ) (hx : x ≠ -1) :
    deriv rhoR x = (2*x*(1+x)^4 - x^2*(4*(1+x)^3))/((1+x)^4)^2 := by
  show deriv (fun z : ℝ => z^2/(1+z)^4) x = _
  have hden : (1+x)^4 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hd1 : DifferentiableAt ℝ (fun z : ℝ => z^2) x := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun z : ℝ => (1+z)^4) x := by fun_prop
  have hv2 : deriv (fun z : ℝ => (1+z)^4) x = 4*(1+x)^3 := by
    change deriv ((fun z : ℝ => 1+z)^4) x = 4*(1+x)^3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun z : ℝ => 1+z) x)]
    simp
  change deriv ((fun z : ℝ => z^2) / (fun z : ℝ => (1+z)^4)) x = _
  rw [deriv_div hd1 hd2 hden]
  rw [hv2]
  simp

/-- The closed form of `D_z ρ = Zop ρ` away from `z = -1`. -/
private lemma Zop_rhoR_eq (x : ℝ) (hx : x ≠ -1) :
    Work.Spaces.Zop rhoR x = x^2*(2-2*x)/(1+x)^5 := by
  rw [Zop_apply, deriv_rhoR x hx]
  have hden : (1+x)^4 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hden5 : (1+x)^5 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The elementary derivative of `w ↦ w²(2-2w)/(1+w)⁵` away from `w = -1`. -/
private lemma deriv_g1 (x : ℝ) (hx : x ≠ -1) :
    deriv (fun w : ℝ => w^2*(2-2*w)/(1+w)^5) x = 2*(2*x - 6*x^2 + 2*x^3)/(1+x)^6 := by
  have hden : (1+x)^5 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(2-2*w)) x := by fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^5) x := by fun_prop
  have hdnum : deriv (fun w : ℝ => w^2*(2-2*w)) x = 2*x*(2-2*x) - 2*x^2 := by
    have hd1 : DifferentiableAt ℝ (fun w : ℝ => w^2) x := by fun_prop
    have hd2 : DifferentiableAt ℝ (fun w : ℝ => 2-2*w) x := by fun_prop
    change deriv ((fun w : ℝ => w^2) * (fun w : ℝ => 2-2*w)) x = _
    rw [deriv_mul hd1 hd2]
    simp
    ring
  change deriv ((fun w : ℝ => w^2*(2-2*w)) / (fun w : ℝ => (1+w)^5)) x = _
  rw [deriv_div hnum hden' hden]
  rw [hdnum]
  have hv5 : deriv (fun w : ℝ => (1+w)^5) x = 5*(1+x)^4 := by
    change deriv ((fun w : ℝ => 1+w)^5) x = 5*(1+x)^4
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  rw [hv5]
  field_simp
  ring

/-- The derivative of `Zop ρ` away from `z = -1`, transported through the closed form of
`Zop ρ` on a neighbourhood of the point. -/
private lemma Zop_rhoR_deriv (x : ℝ) (hx : x ≠ -1) :
    deriv (Work.Spaces.Zop rhoR) x = 2*(2*x - 6*x^2 + 2*x^3)/(1+x)^6 := by
  have hev : (Work.Spaces.Zop rhoR) =ᶠ[𝓝 x] (fun w : ℝ => w^2*(2-2*w)/(1+w)^5) := by
    filter_upwards [eventually_ne_nhds hx] with w hw
    exact Zop_rhoR_eq w hw
  rw [hev.deriv_eq]
  exact deriv_g1 x hx

theorem H4N_rhoR_shape12 :
    (∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[1] Work.Construction.rhoR) z
        = z^2 * (2 - 2*z) / (1 + z)^5)
    ∧ (∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[2] Work.Construction.rhoR) z
        = z^2 * (4 - 12*z + 4*z^2) / (1 + z)^6) := by
  constructor
  · intro z hz
    rw [Function.iterate_one]
    exact Zop_rhoR_eq z hz
  · intro z hz
    rw [Function.iterate_succ_apply, Function.iterate_one]
    show Work.Spaces.Zop (Work.Spaces.Zop rhoR) z = z^2 * (4 - 12*z + 4*z^2) / (1 + z)^6
    rw [Zop_apply, Zop_rhoR_deriv z hz]
    have hden : (1+z)^6 ≠ 0 := pow_ne_zero _ (by intro h; exact hz (by linarith))
    field_simp
    ring

end Work.Construction
end
-- ===== merged: Submission.Work.Construction.H4N_rhoR_shape3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shape of the third `D_z`-iterate of `ρ(z) = z²/(1+z)⁴`

`Work.Construction.rhoR z = z²/(1+z)⁴` is the radial factor of the `Γ`-term of the
`N₀` nonlinearity (`Work.Construction.GammaTermAux`).  Its `D_z`-iterates are the
`Work.Spaces.Zop`-iterates (`Zop u = fun z ↦ z * u'(z)`), and the third one is

`Zop^[3] rhoR = fun z ↦ z²·(8 - 52z + 52z² - 8z³)/(1+z)⁷`  on `z ≠ -1`.

The proof is a three-step computation: each iterate has the shape
`z²·Q(z)/(1+z)^m` with `Q` a cubic, and one application of `Zop` replaces
`(Q, m)` by `(Q', m+1)`.  The general step is isolated as `Zop_div_pow`:

`Zop (w ↦ u w / (1+w)^m) z = (z·u'·(1+z) - m·z·u z)/(1+z)^(m+1)`

for `z ≠ -1` and `HasDerivAt u u' z`; the three instances are `step1`, `step2`,
`step3`.  The only place where the restriction `z ≠ -1` enters the iteration is
the transfer of the pointwise value to the next derivative (`Zop_congr_off`):
two functions that agree off `-1` have the same derivative at `z ≠ -1`.
-/

open scoped Real Topology
open Filter

namespace Work.Construction

/-- One step of `Zop` on functions of the shape `w ↦ u w / (1+w)^m`. -/
lemma Zop_div_pow (m : ℕ) (hm : 1 ≤ m) (u : ℝ → ℝ) (u' z : ℝ)
    (hu : HasDerivAt u u' z) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w => u w / (1+w)^m) z
      = (z * u' * (1+z) - (m:ℝ) * z * u z) / (1+z)^(m+1) := by
  have h1z : (1:ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  unfold Work.Spaces.Zop
  have hd : HasDerivAt (fun w : ℝ => u w / (1+w)^m)
      ((u' * (1+z)^m - u z * ((m:ℝ) * (1+z)^(m-1))) / ((1+z)^m)^2) z := by
    apply HasDerivAt.div
    · exact hu
    · have h0 : HasDerivAt (fun w : ℝ => 1 + w) (1:ℝ) z := (hasDerivAt_id z).const_add 1
      have h := h0.pow m
      convert h using 1
      ring
    · exact pow_ne_zero m h1z
  rw [hd.deriv]
  have hB : (1+z)^m = (1+z)^(m-1) * (1+z) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ']; ring
  have hAB : (1+z)^(m+1) = (1+z)^(m-1) * (1+z) * (1+z) := by
    rw [pow_succ', hB]; ring
  field_simp
  rw [hAB, hB]
  ring

/-- `Zop` only depends on the values of the function away from `-1`, at points `≠ -1`. -/
lemma Zop_congr_off (u f g : ℝ → ℝ) (hu : ∀ w, w ≠ -1 → u w = f w)
    (hf : ∀ w, w ≠ -1 → Work.Spaces.Zop f w = g w) :
    ∀ z, z ≠ -1 → Work.Spaces.Zop u z = g z := by
  intro z hz
  have hev : u =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact hu w hw
  have h1 : deriv u z = deriv f z := hev.deriv_eq
  unfold Work.Spaces.Zop
  rw [h1]
  exact hf z hz

/-- `Zop rhoR = fun z ↦ z²(2 - 2z)/(1+z)⁵` off `-1`. -/
lemma Zop_rhoR_step1 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4) z = z^2 * (2 - 2*z)/(1+z)^5 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2) (2*z) z := by
    have h' : HasDerivAt (fun w : ℝ => w^2) (↑2 * z^(2-1)) z := hasDerivAt_pow 2 z
    have he : (↑2 * z^(2-1) : ℝ) = 2*z := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 4 (by norm_num) (fun w : ℝ => w^2) (2*z) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The second iterate: `Zop (z²(2-2z)/(1+z)⁵) = z²(4 - 12z + 4z²)/(1+z)⁶` off `-1`. -/
lemma Zop_rhoR_step2 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 * (2 - 2*w) / (1+w)^5) z
      = z^2 * (4 - 12*z + 4*z^2)/(1+z)^6 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2 * (2 - 2*w)) (4*z - 6*z^2) z := by
    have h2 : HasDerivAt (fun w : ℝ => 2 - 2*w) (-2) z := by
      have h' : HasDerivAt (fun w : ℝ => 2 - 2*w) (-(2*1)) z :=
        ((hasDerivAt_id' z).const_mul (2:ℝ)).const_sub (2:ℝ)
      have he : (-(2*1) : ℝ) = -2 := by ring
      rw [he] at h'
      exact h'
    have h' : HasDerivAt (fun w : ℝ => w^2 * (2 - 2*w))
        ((↑2 * z^(2-1)) * (2 - 2*z) + z^2 * (-2)) z := (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2 * z^(2-1)) * (2 - 2*z) + z^2 * (-2) : ℝ) = 4*z - 6*z^2 := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 5 (by norm_num) (fun w : ℝ => w^2 * (2 - 2*w)) (4*z - 6*z^2) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The third iterate, in the shape requested by `H4N_rhoR_shape3`. -/
lemma Zop_rhoR_step3 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6) z
      = z^2 * (8 - 52*z + 52*z^2 - 8*z^3)/(1+z)^7 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2)) (8*z - 36*z^2 + 16*z^3) z := by
    have h2 : HasDerivAt (fun w : ℝ => 4 - 12*w + 4*w^2) (-12 + 8*z) z := by
      have h' : HasDerivAt (fun w : ℝ => 4 - 12*w + 4*w^2)
          (-(12*1) + 4*(↑2 * z^(2-1))) z :=
        (((hasDerivAt_id' z).const_mul (12:ℝ)).const_sub (4:ℝ)).add
          ((hasDerivAt_pow 2 z).const_mul (4:ℝ))
      have he : (-(12*1) + 4*(↑2 * z^(2-1)) : ℝ) = -12 + 8*z := by ring
      rw [he] at h'
      exact h'
    have h' : HasDerivAt (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2))
        ((↑2 * z^(2-1)) * (4 - 12*z + 4*z^2) + z^2 * (-12 + 8*z)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2 * z^(2-1)) * (4 - 12*z + 4*z^2) + z^2 * (-12 + 8*z) : ℝ)
        = 8*z - 36*z^2 + 16*z^3 := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 6 (by norm_num) (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2))
    (8*z - 36*z^2 + 16*z^3) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

theorem H4N_rhoR_shape3 :
    ∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[3] Work.Construction.rhoR) z
        = z^2 * (8 - 52*z + 52*z^2 - 8*z^3) / (1 + z)^7 := by
  intro z hz
  have hAC := Zop_congr_off (Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4))
    (fun w : ℝ => w^2 * (2 - 2*w) / (1+w)^5)
    (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6) Zop_rhoR_step1 Zop_rhoR_step2
  have hAD := Zop_congr_off (Work.Spaces.Zop (Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4)))
    (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6)
    (fun w : ℝ => w^2 * (8 - 52*w + 52*w^2 - 8*w^3) / (1+w)^7) hAC Zop_rhoR_step3
  have e : (Work.Spaces.Zop^[3] Work.Construction.rhoR) z
      = Work.Spaces.Zop (Work.Spaces.Zop (Work.Spaces.Zop
          (fun w : ℝ => w^2 / (1+w)^4))) z := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rfl
  rw [e]
  exact hAD z hz

end Work.Construction
end
-- ===== merged: Submission.Work.Cyl.Elliptic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The stream-function field: vorticity, divergence and the elliptic reduction

For the stream-function field `psiField ψ` (i.e. `u_r = ∂_z ψ`, `u_z = -ψ/r - ∂_r ψ`):

* `Work.Cyl.vorticity_psiField` : `∇×u = -(Lψ) e_θ`, i.e. `ω^θ = -Lψ` where
  `Lψ = -∂_rrψ - ∂_zzψ - (1/r)∂_rψ + ψ/r²` is `Work.Cyl.cylOp ψ` (paper (3dBSL));
* `Work.Cyl.vortTheta_psiField` : the same identity for `Work.Cyl.vortTheta` on the `(r,x₃)` plane;
* `Work.Cyl.div_psiField` : `div u = 0`.

`Work.Cyl.norm_vorticity_psiField` below records the pointwise norm of the vorticity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl



end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.Parity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Parity in the axial variable

The `IsOdd` dictionary for axisymmetric no-swirl fields, for the stream-function field `psiField`,
and the derivative parity lemmas.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix Topology
open Filter
open Work.Cyl
open FiniteTimeSingularity

namespace Work.Cyl

/-! ## Derivatives of functions with a parity in the axial variable -/






/-! ## Propagation of the reflection symmetry -/




/-! ## The converse: oddness of the field forces oddness of the stream function -/


/-! ## Parity of the scalar vorticity -/


end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.fderiv_R_theta_eR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial derivative of `x ↦ F(ρ(x)^α, θ(x))`: the `e_r` direction

For a two-variable function `F`, a point `x` off the symmetry axis (`0 < radial x`) and any real
`α`,

`fderiv ℝ (fun y ↦ F (rho y ^ α) (theta y)) x eR
   = (cos θ / ρ) · (α ρ^α ∂_R F(ρ^α, θ)) − (sin θ / ρ) · ∂_θ F(ρ^α, θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically, moving along the radial direction `e_r` keeps `x₃` fixed and increases `r` at unit
speed: `rho (x + t e_r) = rhoP (r + t) x₃` and `theta (x + t e_r) = thetaP (r + t) x₃` near
`t = 0`, where `r = radial x`, `x₃ = axial x`.  Hence the directional derivative is exactly the
radial partial derivative `∂_r` of `(r,z) ↦ F (ρP(r,z)^α) (θP(r,z))` at `(r, x₃)`, which is
`Work.Cyl.pdR_comp_polar`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-! ## The line `t ↦ x + t e_r`

Along the radial direction the axial coordinate is constant and the radial coordinate is `r + t`
(up to the absolute value, which only matters away from `t = 0`). -/




/-! ## Differentiability of `rho` and `theta` off the axis -/



/-! ## The main computation -/


end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.fderiv_rho_theta_eR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial derivative of `x ↦ F(ρ(x), θ(x))`: the `e_r` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x eR
   = cos θ · ∂_ρ F(ρ,θ) − (sin θ / ρ) · ∂_θ F(ρ,θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically, moving along the unit radial direction `e_r` increases the planar radius `r` at
unit speed and keeps `x₃` fixed, so the pair `(ρ, θ)` traverses the radial curve
`t ↦ (ρP(r+t, x₃), θP(r+t, x₃))`; the directional derivative is therefore the radial partial
derivative `∂_r` of `(r,z) ↦ F(ρP(r,z), θP(r,z))` evaluated at `(radial x, axial x)`, which is
`Work.Cyl.pdR_comp_polar_rho`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on ℝ³ and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP_aux (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP_aux (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-! ## Differentiability of `(r,z) ↦ F(ρP(r,z), θP(r,z))` -/

/-- If `F` is differentiable as a function of two variables at `(ρP r z, θP r z)` and `0 < r`,
then so is the composite `(r,z) ↦ F(ρP r z, θP r z)`: the pair `(ρP, θP)` is differentiable
there (`ρP` is a square root of a strictly positive quantity, `θP` is `arctan` of the
differentiable quotient `z/r`, legitimate since `r ≠ 0`). -/
private lemma polar_comp_diffAt2_aux (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z) (thetaP r z)) :
    DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z := by
  have hρ : DifferentiableAt ℝ (fun p : ℝ × ℝ => rhoP p.1 p.2) (r, z) := by
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) := by fun_prop
    have hne : (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) ≠ 0 := by
      simp only; positivity
    simpa [rhoP] using h.sqrt hne
  have hθ : DifferentiableAt ℝ (fun p : ℝ × ℝ => thetaP p.1 p.2) (r, z) := by
    have hinv : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1)⁻¹) (r, z) :=
      differentiableAt_fst.inv (by simpa using hr.ne')
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2 * (p.1)⁻¹) (r, z) :=
      differentiableAt_snd.mul hinv
    simpa [thetaP, div_eq_mul_inv] using h.arctan
  have hΦ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (rhoP p.1 p.2, thetaP p.1 p.2)) (r, z) :=
    hρ.prodMk hθ
  have hcomp := hF.comp (r, z) hΦ
  exact hcomp

/-! ## Directional derivatives of the planar radius and the axial coordinate -/

/-- `t ↦ radial (x + t • v)` has derivative `((x₀ v₀ + x₁ v₁))/r` at `0`, i.e. the directional
derivative of `r = √(x₀²+x₁²)` in direction `v`. -/
private lemma hasDerivAt_radial_dir_aux (x v : R3) (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => radial (x + t • v)) ((x 0 * v 0 + x 1 * v 1) / radial x) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => x 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (x 0)
  have h1 : HasDerivAt (fun t : ℝ => x 1 + t * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (x 1)
  have hradsq : HasDerivAt (fun t : ℝ => radSq (x + t • v))
      (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
    have hfun : (fun t : ℝ => radSq (x + t • v)) =
        fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1) := by
      funext t; simp [radSq, pow_two]
    rw [hfun]
    have hsq : HasDerivAt (fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1))
        (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
      have h := (h0.mul h0).add (h1.mul h1)
      convert h using 1
      ring
    exact hsq
  have hne : radSq (x + (0:ℝ) • v) ≠ 0 := by
    rw [zero_smul, add_zero]
    rw [← radial_sq]; exact pow_ne_zero 2 (ne_of_gt hr)
  have hmain : (fun t : ℝ => radial (x + t • v)) =
      fun t : ℝ => Real.sqrt (radSq (x + t • v)) := by
    funext t; rw [radial]
  rw [hmain]
  have hder := hradsq.sqrt hne
  have hval : (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) / (2 * Real.sqrt (radSq (x + (0:ℝ) • v)))
      = (x 0 * v 0 + x 1 * v 1) / radial x := by
    rw [zero_smul, add_zero, radial]
    have hpos : 0 < radSq x := by rw [← radial_sq]; positivity
    have hsne : Real.sqrt (radSq x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
  rw [hval] at hder
  exact hder

/-- `t ↦ axial (x + t • v)` has derivative `v₂` at `0`. -/
private lemma hasDerivAt_axial_dir_aux (x v : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • v)) (v 2) 0 := by
  have hfun : (fun t : ℝ => axial (x + t • v)) = fun t : ℝ => x 2 + t * v 2 := by
    funext t; simp [axial]
  rw [hfun]
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 2)).const_add (x 2)

/-! ## The main computation -/

theorem fderiv_rho_theta_eR (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x (Work.Cyl.eR x) =
      Real.cos (Work.Cyl.theta x) * Work.Cyl.pdR F (Work.Cyl.rho x) (Work.Cyl.theta x)
        - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← rho_eq_rhoP_aux, ← theta_eq_thetaP_aux]; exact hF
  have hH : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x) :=
    polar_comp_diffAt2_aux F (radial x) (axial x) hr hF'
  have hG : DifferentiableAt ℝ (fun y : R3 => F (rho y) (theta y)) x :=
    differentiableAt_rho_theta_comp F x hF hr
  -- the pair `(radial, axial)` moves with velocity `(1, 0)` along the line `t ↦ x + t • eR x`
  have hradline : HasDerivAt (fun t : ℝ => radial (x + t • eR x)) 1 0 := by
    have h := hasDerivAt_radial_dir_aux x (eR x) hr
    have hval : (x 0 * (eR x) 0 + x 1 * (eR x) 1) / radial x = 1 := by
      rw [eR_apply_zero, eR_apply_one]
      field_simp
      rw [radial_sq]; rfl
    rw [hval] at h; exact h
  have haxline : HasDerivAt (fun t : ℝ => axial (x + t • eR x)) 0 0 := by
    have h := hasDerivAt_axial_dir_aux x (eR x)
    simpa [eR_apply_two] using h
  have hH0 : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (radial (x + (0:ℝ) • eR x)) (axial (x + (0:ℝ) • eR x)) := by simpa using hH
  have hline : HasDerivAt (fun t : ℝ => F (rho (x + t • eR x)) (theta (x + t • eR x)))
      (pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x)) 0 := by
    have hc := hasDerivAt_comp_two (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (fun t : ℝ => radial (x + t • eR x)) (fun t : ℝ => axial (x + t • eR x))
      1 0 0 hH0 hradline haxline
    have heq : (fun t : ℝ => F (rho (x + t • eR x)) (theta (x + t • eR x))) =
        fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
          (radial (x + t • eR x)) (axial (x + t • eR x)) := by
      funext t; rw [rho_eq_rhoP_aux (x + t • eR x), theta_eq_thetaP_aux (x + t • eR x)]
    rw [heq]
    simpa using hc
  rw [fderiv_apply_eq_deriv_line _ _ _ hG]
  rw [hline.deriv]
  rw [pdR_comp_polar_rho F (radial x) (axial x) hr hF']
  rw [rho_eq_rhoP_aux x, theta_eq_thetaP_aux x]

end Work.Cyl
end
-- ===== merged: Submission.Work.Elliptic.DivSinIdentDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false



/-- The difference of the two integrands of `DivSinIdentityB`: the left hand side integrand
`(h'')² sin(2θ)^{2-γ}` minus the right hand side integrand. -/
def Dfun (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (deriv (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
    - ((Real.sin (2 * θ)) ^ (4 - γ) * (deriv (deriv (SinQ h)) θ) ^ 2
      + 8 * (γ - 1) * ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          * (deriv (SinQ h) θ) ^ 2)
      + 16 * ((Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2)
      + 16 * (3 - γ) * ((Real.sin (2 * θ)) ^ (4 - γ) * (SinQ h θ) ^ 2)
      - 16 * (2 - γ) * (3 - γ) * ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          * (SinQ h θ) ^ 2))

/-! ## Derivatives of the elementary angular functions -/

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIntegrable_u0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The angular interval `[0, π/2]` is contained in the open neighbourhood of smoothness. -/
private lemma Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hx
  exact ⟨by linarith [hx'.1], by linarith [hx'.2, Real.pi_pos]⟩

private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc











end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIntegrable_u1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-!
## The angular integrability of the first-order terms of `SinQ h`

`SliceBdd_ae_bounds` shows that `deriv (SinQ h)` is bounded on `Iθ = [0,π/2]` by a constant
`C`, almost everywhere.  On `Iθ` the factors `sin(2θ)^p` for `p ≥ 0` are bounded by `1`
(because `0 ≤ sin(2θ) ≤ 1` and `y ↦ y^p` is increasing for `p ≥ 0`), and `cos(2θ)² ≤ 1`.
Hence each of the three integrands below is dominated almost everywhere by the constant
`C ^ 2`, which is integrable on the finite-measure set `Iθ`.

The only non-trivial ingredients are the almost-everywhere bound for `deriv (SinQ h)` and
the (Borel) measurability of `deriv (SinQ h)`, which is the general Mathlib fact
`measurable_deriv`. -/
end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinIntegrable_u2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoH_Mixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary absolute-value bookkeeping -/

/-- Comparison of powers: `|z^k X| ≤ |(z+1)^k X|` for `z ≥ 0`. -/
private lemma abs_mul_pow_le_succ (z X : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    |z ^ k * X| ≤ |(z + 1) ^ k * X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz k),
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (by linarith) k) (abs_nonneg X)

/-- Triangle inequality for three weighted terms. -/
private lemma abs_comb3_le {Cst : ℝ} (hCst : 0 ≤ Cst) {a b c : ℝ} (ha : |a| ≤ Cst)
    (hb : |b| ≤ Cst) (hc : |c| ≤ Cst) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |A * a + B * b + D * c| ≤ (A + B + D) * Cst := by
  have h1 : |A * a| ≤ A * Cst := by
    rw [abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left ha hA
  have h2 : |B * b| ≤ B * Cst := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left hb hB
  have h3 : |D * c| ≤ D * Cst := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hc hD
  have htri : |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := by
    calc |A * a + B * b + D * c| ≤ |A * a + B * b| + |D * c| := abs_add_le _ _
      _ ≤ (|A * a| + |B * b|) + |D * c| := by linarith [abs_add_le (A * a) (B * b)]
      _ = |A * a| + |B * b| + |D * c| := by ring
  calc |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := htri
    _ ≤ A * Cst + B * Cst + D * Cst := by linarith
    _ = (A + B + D) * Cst := by ring

/-! ## The Leibniz expansion of `∂_z^l D_θ^i f` through `f = z²·divZ2 f` -/


/-! ## From the `𝒲^{4,∞}`-bounds on `(z+1)³/z²·f` to bounds on `∂_z^j κ` -/


/-! ## The elementary weighted estimate -/

/-- If `|(z+1)^{j+3} K j| ≤ 6000 M Φ` for `j ≤ l ≤ 3`, `z > 0`, `M, Φ ≥ 0`, then the
weighted expression `((z+1)³ z^l/z²)·(z²K_l + 2l z K_{l-1} + l(l-1)K_{l-2})` is
`≤ 200000 M Φ`. -/
private theorem arith_aux {z : ℝ} (hz : 0 < z) {M Φ : ℝ} (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (l : ℕ) (hl : l ≤ 3) (K : ℕ → ℝ)
    (hK : ∀ j ≤ l, |(z + 1) ^ (j + 3) * K j| ≤ 6000 * (M * Φ)) :
    |(z + 1) ^ 3 * z ^ l / z ^ 2 * (z ^ 2 * K l + (2 * (l : ℝ)) * z * K (l - 1)
        + ((l : ℝ) * ((l : ℝ) - 1)) * K (l - 2))| ≤ 200000 * (M * Φ) := by
  have hMΦ : 0 ≤ M * Φ := mul_nonneg hM hΦ
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hterm : ∀ j ≤ l, |z ^ j * ((z + 1) ^ 3 * K j)| ≤ 6000 * (M * Φ) := by
    intro j hj
    refine le_trans (abs_mul_pow_le_succ z ((z + 1) ^ 3 * K j) hz0 j) ?_
    have h2 : (z + 1) ^ j * ((z + 1) ^ 3 * K j) = (z + 1) ^ (j + 3) * K j := by
      rw [← mul_assoc, ← pow_add]
    rw [h2]
    exact hK j hj
  interval_cases l
  · -- l = 0
    have hid : (z + 1) ^ 3 * z ^ 0 / z ^ 2
          * (z ^ 2 * K 0 + (2 * ((0 : ℕ) : ℝ)) * z * K (0 - 1)
              + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * K (0 - 2))
        = 1 * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (2 * ((0 : ℕ) : ℝ)) * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * (z ^ 0 * ((z + 1) ^ 3 * K 0)) := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 0 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 1
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 1 / z ^ 2
          * (z ^ 2 * K 1 + (2 * ((1 : ℕ) : ℝ)) * z * K (1 - 1)
              + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1)) * K (1 - 2))
        = 1 * (z ^ 1 * ((z + 1) ^ 3 * K 1))
          + (2 * ((1 : ℕ) : ℝ)) * (z ^ (1 - 1) * ((z + 1) ^ 3 * K (1 - 1)))
          + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1))
              * (z ^ (1 - 2) * ((z + 1) ^ 3 * K (1 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 1 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 2
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 2 / z ^ 2
          * (z ^ 2 * K 2 + (2 * ((2 : ℕ) : ℝ)) * z * K (2 - 1)
              + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) * K (2 - 2))
        = 1 * (z ^ 2 * ((z + 1) ^ 3 * K 2))
          + (2 * ((2 : ℕ) : ℝ)) * (z ^ (2 - 1) * ((z + 1) ^ 3 * K (2 - 1)))
          + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1))
              * (z ^ (2 - 2) * ((z + 1) ^ 3 * K (2 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 2 (by norm_num))
      (hterm 1 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 3
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 3 / z ^ 2
          * (z ^ 2 * K 3 + (2 * ((3 : ℕ) : ℝ)) * z * K (3 - 1)
              + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) * K (3 - 2))
        = 1 * (z ^ 3 * ((z + 1) ^ 3 * K 3))
          + (2 * ((3 : ℕ) : ℝ)) * (z ^ (3 - 1) * ((z + 1) ^ 3 * K (3 - 1)))
          + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))
              * (z ^ (3 - 2) * ((z + 1) ^ 3 * K (3 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 3 (by norm_num))
      (hterm 2 (by norm_num)) (hterm 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]

/-! ## The transfer -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoW_f_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

open Work.Spaces

set_option autoImplicit false

/-! ## Derivative facts for `sin (2·)` -/





/-! ## The angular factor `D_θ^i (sin (2·)) = sin (2·) · sigCoeff i` -/






/-! ## The term bound from the `𝒲^{4,∞}`-norm -/


/-! ## Linearity of `pzIter` over a finite sum of angular-weighted functions -/


/-! ## The Leibniz expansion of `D_θ^{b+1} f` -/


/-! ## The main estimate -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.hardy_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

/-!
# From a finite iterated `lintegral` to honest integrability

The technical step `HkMemAe_of_lintegral` is a pure measure-theory statement: for a
*pointwise nonnegative* integrand `f z θ` whose iterated Lebesgue integral over
`(0,∞) × Iθ` is finite, the `θ`-slices are integrable for almost every `z > 0` and the
function `z ↦ ∫ θ, f z θ` is integrable on `(0,∞)`.

This is exactly what turns the `H^k`-finiteness assumption (an `HkSq` bound, which is
naturally proved as a bound on the iterated `lintegral` `∫⁻ z ∫⁻ θ ofReal (integrand)`)
into the honest statement `HkMem α 0 Ψ` modulo the null set where a slice blows up.

The pointwise nonnegativity is automatic for the level-`0` weighted integrand
(`HkIntegrand_zero_nonneg`: it is a sum of squares and of zero terms), so the general
lemma below is applied to it verbatim.
-/

/-- The level-`0` weighted integrand of `HkIntegrand` is nonnegative: for `k = 0` the
definition reduces to the single square `(Ψ z θ · w z / sin(2θ)^{η/2})²` (the mixed sum
is empty because its condition `1 ≤ i ∧ i + j ≤ 0` is false for `i = j = 0`). -/
theorem HkIntegrand_zero_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α 0 Ψ z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

/-- **Finiteness of an iterated `lintegral` gives honest integrability.**  Let
`f : ℝ → ℝ → ℝ` be pointwise nonnegative, with `θ`-slices satisfying
`∫⁻ θ in Iθ, ofReal (f z θ) < ∞` in the `lintegral` sense, the whole iterated `lintegral`
bounded by `ofReal C`, and the outer function `z ↦ ∫⁻ θ, ofReal (f z θ)` a.e.-measurable
on `(0,∞)`.  Then

* for almost every `z ∈ (0,∞)` the slice `θ ↦ f z θ` is integrable on `Iθ`, and
* `z ↦ ∫ θ in Iθ, f z θ` is integrable on `(0,∞)`.

The proof is the standard one: the outer `lintegral` being `< ∞` makes the outer
function finite a.e. (`ae_lt_top'`), finiteness of the slice identifies the honest
Bochner integral of the slice with `(∫⁻ θ, ofReal (f z θ)).toReal`, and this outer
function is integrable because its `ofReal`-`lintegral` is exactly the given one. -/
theorem ae_integrableOn_and_integrableOn_of_lintegral_le {f : ℝ → ℝ → ℝ} {C : ℝ}
    (hnn : ∀ z θ, 0 ≤ f z θ)
    (hslmeas : ∀ z ∈ Set.Ioi 0,
      AEMeasurable (fun θ => ENNReal.ofReal (f z θ)) (volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (f z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (f z θ)) (volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) (Set.Ioi 0) := by
  set G : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ) with hG
  have hGmeas : AEMeasurable G (volume.restrict (Set.Ioi 0)) := hmeas
  have hfin' : (∫⁻ z in Set.Ioi 0, G z) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  have hGlt : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), G z < ⊤ :=
    MeasureTheory.ae_lt_top' hGmeas hfin'
  have hmem : ∀ᵐ z : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))), z ∈ Set.Ioi (0 : ℝ) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the slices are integrable a.e.
  have hsl : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := by
    filter_upwards [hmem, hGlt] with z hz hlt
    have hms : AEMeasurable (fun θ => ENNReal.ofReal (f z θ))
        (volume.restrict Work.Spaces.Iθ) := hslmeas z hz
    have has : AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) := by
      refine (hms.ennreal_toReal.aestronglyMeasurable).congr ?_
      filter_upwards with θ
      exact ENNReal.toReal_ofReal (hnn z θ)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable has
      (Filter.Eventually.of_forall fun θ => hnn z θ)).mp (ne_of_lt hlt)
  -- the honest slice integral agrees with the `toReal` of the `lintegral`, a.e.
  have hP_eq : (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      =ᵐ[volume.restrict (Set.Ioi 0)] fun z => (G z).toReal := by
    filter_upwards [hmem, hGlt] with z hz hlt
    have hms : AEMeasurable (fun θ => ENNReal.ofReal (f z θ))
        (volume.restrict Work.Spaces.Iθ) := hslmeas z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, f z θ)
        = ∫ θ in Work.Spaces.Iθ, (ENNReal.ofReal (f z θ)).toReal := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with θ
      exact (ENNReal.toReal_ofReal (hnn z θ)).symm
    rw [h1, MeasureTheory.integral_toReal hms
      (Filter.Eventually.of_forall fun θ => ENNReal.ofReal_lt_top)]
  have hP_asm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      (volume.restrict (Set.Ioi 0)) :=
    (hmeas.ennreal_toReal.aestronglyMeasurable).congr hP_eq.symm
  have hP_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) :=
    hP_eq.mono fun z hz => by rw [hz]; exact ENNReal.toReal_nonneg
  have hP_fin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ)) ≠ ⊤ := by
    have heq : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ))
        = ∫⁻ z in Set.Ioi 0, G z := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hP_eq, hGlt] with z h1 h2
      rw [h1]
      exact ENNReal.ofReal_toReal (ne_of_lt h2)
    rw [heq]
    exact ne_of_lt (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  exact ⟨hsl, (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hP_asm hP_nn).mp hP_fin⟩

theorem HkMemAe_of_lintegral {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        (Set.Ioi 0) := by
  exact ae_integrableOn_and_integrableOn_of_lintegral_le
    (fun z θ => HkIntegrand_zero_nonneg α Ψ z θ)
    (fun z hz => hslmeas z (Set.Ioi_subset_Ici_self hz)) hfin hmeas

end Work.FTS.ClassC.HonestCut
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.radGreen_split_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set Filter
open scoped Real Topology

local notation "rq" => Work.FTS.EllExist.rgQ
local notation "rp" => Work.FTS.EllExist.rgP
local notation "rK" => Work.FTS.EllExist.rgK
local notation "w" => Work.Spaces.w

/-- The weight `w` is continuous on `(0,∞)` (`w t = (1+t)²/t²` has a pole at `0`). -/
private lemma w_contOn : ContinuousOn w (Set.Ioi (0:ℝ)) := by
  have hfun : (w : ℝ → ℝ) = fun t => (1 + t)^2 / t^2 := rfl
  rw [hfun]
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro t ht; exact pow_ne_zero 2 (ne_of_gt ht)

/-- A function whose product with `w` is a.e. strongly measurable on `(0,∞)` is itself a.e.
strongly measurable on `(a,b] ⊂ (0,∞)` (`w` does not vanish there, so one may divide). -/
private lemma aesm_c_of_aesm_mul_w {c : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hcm : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi 0))) :
    AEStronglyMeasurable c (volume.restrict (Set.Ioc a b)) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_trans ha ht.1
  have h1 : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioc a b)) :=
    hcm.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have h2 : AEStronglyMeasurable (fun t : ℝ => w t) (volume.restrict (Set.Ioc a b)) :=
    (w_contOn.mono hsub).aestronglyMeasurable measurableSet_Ioc
  refine (h1.div₀ h2).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := lt_trans ha ht.1
  have hwt : w t ≠ 0 := by
    have hw : (w t) = (1 + t)^2 / t^2 := rfl
    rw [hw]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt ht0))
  simp only [Pi.div_apply]
  rw [mul_div_assoc, div_self hwt, mul_one]

/-- `z^{-q}·(z/2)^q = 2^{-q}` for `z > 0`: the scaling identity converting the near-field
Cauchy–Schwarz bound at the half point `z/2` into a bound at `z`. -/
private lemma rpow_neg_mul_half {q z : ℝ} (hz : 0 < z) :
    z ^ (-q) * (z / 2) ^ q = (2:ℝ) ^ (-q) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hinv : (1/2 : ℝ) ^ q = (2:ℝ) ^ (-q) := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow h2, ← Real.rpow_neg h2 q]
  calc z ^ (-q) * (z / 2) ^ q
      = z ^ (-q) * (z ^ q * (1/2:ℝ) ^ q) := by
        rw [show z / 2 = z * (1/2 : ℝ) by ring,
          Real.mul_rpow hz.le (by norm_num : (0:ℝ) ≤ (1/2:ℝ))]
    _ = (z ^ (-q) * z ^ q) * (1/2:ℝ)^q := by ring
    _ = z ^ (-q + q) * (1/2:ℝ)^q := by rw [Real.rpow_add hz]
    _ = (2:ℝ)^(-q) := by rw [hinv, neg_add_cancel, Real.rpow_zero, one_mul]

/-- `z^p·(2z)^{-p} = 2^{-p}` for `z > 0`: the mirror of `rpow_neg_mul_half`, converting the
far-field Cauchy–Schwarz bound at `2z` into a bound at `z`. -/
private lemma rpow_mul_two_neg {p z : ℝ} (hz : 0 < z) :
    z ^ p * (2 * z) ^ (-p) = (2:ℝ) ^ (-p) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  calc z ^ p * (2 * z) ^ (-p)
      = z ^ p * ((2:ℝ)^(-p) * z ^ (-p)) := by rw [Real.mul_rpow h2 hz.le]
    _ = (z ^ p * z ^ (-p)) * (2:ℝ)^(-p) := by ring
    _ = z ^ (p + -p) * (2:ℝ)^(-p) := by rw [Real.rpow_add hz]
    _ = (2:ℝ)^(-p) := by rw [add_neg_cancel, Real.rpow_zero, one_mul]

theorem radGreen_split_le {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ}
    {z L B : ℝ} (hz : 0 < z) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hq : 1 < Work.FTS.EllExist.rgQ α m) (hp : 3 / 2 < Work.FTS.EllExist.rgP α m)
    (hcL : ∀ t ∈ Set.Icc (z / 2) (2 * z), |c t| ≤ L)
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ Work.FTS.EllExist.rgK α m *
      (L * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
        + B * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
            + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) := by
  have hz2 : 0 < z / 2 := by linarith
  have h2z : 0 < 2 * z := by linarith
  have hz2le : z / 2 ≤ z := by linarith
  have hzle2 : z ≤ 2 * z := by linarith
  have hqpos : 0 < rq α m := by linarith
  have hppos : 0 < rp α m := by linarith
  have hKpos : 0 < rK α m := Work.FTS.EllExist.rgK_pos hα m
  -- a.e. strong measurability of `c` on the two middle intervals
  have hcme1 : AEStronglyMeasurable c (volume.restrict (Set.Ioc (z / 2) z)) :=
    aesm_c_of_aesm_mul_w hz2 hcm
  have hcme2 : AEStronglyMeasurable c (volume.restrict (Set.Ioc z (2 * z))) :=
    aesm_c_of_aesm_mul_w hz hcm
  -- the four pieces of the split
  obtain ⟨hintN, hbdN⟩ := near_cs (q := rq α m) (a := z / 2)
      (B := Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)) hq hz2 hc hcm le_rfl
  obtain ⟨hintM, hbdM⟩ := near_inner (q := rq α m) (L := L) (a := z / 2) (b := z)
      hqpos hz2 hz2le hL hcme1 (fun t ht => hcL t ⟨ht.1, le_trans ht.2 hzle2⟩)
  obtain ⟨hintF1, hbdF1⟩ := far_inner (p := rp α m) (L := L) (a := z) (b := 2 * z)
      hppos hz hzle2 hL hcme2 (fun t ht => hcL t ⟨le_trans hz2le ht.1, ht.2⟩)
  obtain ⟨hintF2, hbdF2⟩ := far_cs (p := rp α m) (a := 2 * z)
      (B := Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)) hp h2z hc hcm le_rfl
  -- the two splits of the Green integrals
  have hsplit1 : ∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1)
      = (∫ t in Set.Ioc (0 : ℝ) (z / 2), c t * t ^ (rq α m - 1))
        + ∫ t in Set.Ioc (z / 2) z, c t * t ^ (rq α m - 1) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hz2.le hz2le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hintN hintM
  have hsplit2 : ∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1)
      = (∫ t in Set.Ioc z (2 * z), c t * t ^ (-(rp α m) - 1))
        + ∫ t in Set.Ioi (2 * z), c t * t ^ (-(rp α m) - 1) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hzle2]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hintF1 hintF2
  -- bound on the decaying branch
  have hG1 : |Work.FTS.EllExist.rgG1 α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)) + L / rq α m := by
    rw [Work.FTS.ClassCHon.rgG1_eq (α := α) (m := m) (c := c) hz, hsplit1]
    have hzQ : 0 < z ^ (-(rq α m)) := Real.rpow_pos_of_pos hz _
    rw [abs_mul, abs_of_pos hzQ]
    refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hzQ.le).trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · refine (mul_le_mul_of_nonneg_left hbdN hzQ.le).trans ?_
      rw [show z ^ (-(rq α m)) * (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z / 2) ^ (rq α m) / Real.sqrt (2 * rq α m - 1)))
          = Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z ^ (-(rq α m)) * (z / 2) ^ (rq α m)) / Real.sqrt (2 * rq α m - 1))
          from by ring,
        rpow_neg_mul_half hz]
    · refine (mul_le_mul_of_nonneg_left hbdM hzQ.le).trans ?_
      rw [show z ^ (-(rq α m)) * (L * z ^ (rq α m) / rq α m)
          = L * (z ^ (-(rq α m)) * z ^ (rq α m)) / rq α m from by ring,
        ← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero, mul_one]
  -- bound on the growing branch
  have hG2 : |Work.FTS.EllExist.rgG2 α m c z| ≤ L / rp α m
      + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
    rw [Work.FTS.ClassCHon.rgG2_eq (α := α) (m := m) (c := c), hsplit2]
    have hzP : 0 < z ^ (rp α m) := Real.rpow_pos_of_pos hz _
    rw [abs_mul, abs_of_pos hzP]
    refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hzP.le).trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · refine (mul_le_mul_of_nonneg_left hbdF1 hzP.le).trans ?_
      rw [show z ^ (rp α m) * (L * z ^ (-(rp α m)) / rp α m)
          = L * (z ^ (rp α m) * z ^ (-(rp α m))) / rp α m from by ring,
        ← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero, mul_one]
    · refine (mul_le_mul_of_nonneg_left hbdF2 hzP.le).trans ?_
      rw [show z ^ (rp α m) * (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((2 * z) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)))
          = Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z ^ (rp α m) * (2 * z) ^ (-(rp α m))) / Real.sqrt (2 * rp α m - 3))
          from by ring,
        rpow_mul_two_neg hz]
  -- `radGreen` in terms of the two branches
  have hrad : |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      rK α m * (|Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|) := by
    rw [Work.FTS.EllExist.radGreen_eq α m c z, abs_mul, abs_of_pos hKpos]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
  -- assembly of the four pieces
  have hmain : |Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z| ≤
      L * (1 / rq α m + 1 / rp α m)
        + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
            + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
    have hsum : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1))
        + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))
        ≤ B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
            + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_right hBs (add_nonneg ?_ ?_)
      · exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
      · exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
    calc |Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|
        ≤ (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)) + L / rq α m)
          + (L / rp α m + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := add_le_add hG1 hG2
      _ = (L / rq α m + L / rp α m)
          + (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1))
            + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := by ring
      _ ≤ (L / rq α m + L / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) :=
          add_le_add_right hsum _
      _ = L * (1 / rq α m + 1 / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by ring
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ rK α m * (|Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|) := hrad
    _ ≤ rK α m * (L * (1 / rq α m + 1 / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) :=
        mul_le_mul_of_nonneg_left hmain hKpos.le

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.gammaL2Bnd_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `GammaL2Bnd`: the angular `L²`-estimate `|Γ/c − K|₂ ≤ 7/10`

`GammaL2Bnd α` is the paper's `(GammaAssumption)`: on `Iθ = [0,π/2]`,

  `∫_θ (Γ(θ)/c − K(θ))² ≤ (7/10)²`,

where `Γ(θ) = (sinθ cos²θ)^{α/3}`, `K(θ) = 3 sinθ cos²θ` and `c = ∫_θ Γ K`.

For `α → 0⁺` the weight `Γ/c` degenerates to `1`, so the estimate is a perturbation
of the identity `∫_θ (1 − K)² = π/2 − 2 + 9π/32 = 0.4543… ≤ 0.49` (using
`∫_θ K = 1`, `∫_θ sin²θcos⁴θ = π/32` and `∫_θ 1 = π/2`, all available).  Writing
`u = sinθ cos²θ` and `p = α/3`, the perturbation is controlled by

  `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1 − u)`   (`0 ≤ u ≤ 1`, `0 < p`),

whose right-hand side integrates to `25π/32 − 2 + 6p(π/2)` (`int_F`), together with
the normalisation defect `c ≤ 1`, `1 − c ≤ 3p(π/2)`.  The final step splits

  `Γ/c − K = (Γ − K) + Γ·(1/c − 1)`,

uses `|Γ − K| ≤ 3`, `Γ ≤ 1` and `|1/c − 1| ≤ 6p(π/2) = 3πp` to bound the cross term,
and closes numerically: for `p ≤ 1/(3·10¹⁴)` the corrections are `≤ 10⁻¹²`, far
inside the margin `0.49 − 0.46094 = 0.029`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open GamL2

theorem gammaL2Bnd_fts (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) :
    Work.Coercivity.GammaL2Bnd α := by
  have hα1' : α ≤ 1 := by
    have h : (1 : ℝ) / 10 ^ 14 ≤ 1 := by norm_num
    linarith
  set p : ℝ := α / 3 with hp
  have hp_bound : p ≤ 1 / (3 * 10 ^ 14) := by
    have h : (1 : ℝ) / 10 ^ 14 / 3 = 1 / (3 * 10 ^ 14) := by norm_num
    rw [hp, ← h]
    linarith
  have hp0 : 0 < p := by rw [hp]; linarith
  have hF := int_F α hα hα1'
  rw [← hp] at hF
  have hcle := c_le_one α hα hα1'
  have hcub := one_sub_c_le α hα hα1
  rw [← hp] at hcub
  have hcpos : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1').1
    linarith
  have hcl : (1 : ℝ) / 2 ≤ Work.Spaces.c α := by
    have h3 : 3 * p * (Real.pi / 2) ≤ 1 / 2 := by
      nlinarith [Real.pi_lt_d2, hp_bound, hp0]
    linarith
  have h1mc : |1 - Work.Spaces.c α| ≤ 3 * p * (Real.pi / 2) := by
    rw [abs_of_nonneg (by linarith [hcle])]
    exact hcub
  have he : |1 / Work.Spaces.c α - 1| ≤ 3 * Real.pi * p := by
    have hkey : 1 / Work.Spaces.c α - 1 = (1 - Work.Spaces.c α) / Work.Spaces.c α := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    have hprod : 3 * Real.pi * p * (1 / 2) ≤ 3 * Real.pi * p * Work.Spaces.c α :=
      mul_le_mul_of_nonneg_left hcl (by positivity)
    linarith [h1mc, hprod]
  -- the pointwise reduction to the `F`-part plus a constant
  set C : ℝ := 6 * |1 / Work.Spaces.c α - 1| + (1 / Work.Spaces.c α - 1) ^ 2 with hCdef
  have hpt2 : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2
        ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C := by
    intro θ hθ
    have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hG1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hK0 := K_nonneg hθ
    have hK3 := K_le_three hθ
    have hcne : Work.Spaces.c α ≠ 0 := ne_of_gt hcpos
    have hkey : Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ
        = (Work.Spaces.Gam α θ - Work.Spaces.K θ)
          + Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1) := by
      field_simp
      ring
    have hA3 : |Work.Spaces.Gam α θ - Work.Spaces.K θ| ≤ 3 := by
      rw [abs_le]; constructor <;> linarith
    have hE1 : 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
        * (Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|)
        ≤ 6 * |1 / Work.Spaces.c α - 1| := by
      have hπ0 : 0 ≤ |1 / Work.Spaces.c α - 1| := abs_nonneg _
      have h1 : 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ| ≤ 6 := by linarith
      have h2 : Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|
          ≤ |1 / Work.Spaces.c α - 1| := mul_le_of_le_one_left hπ0 hG1
      exact (mul_le_mul_of_nonneg_right h1 (mul_nonneg hG0 hπ0)).trans
        (mul_le_mul_of_nonneg_left h2 (by norm_num))
    have hE2 : (Work.Spaces.Gam α θ) ^ 2 * (1 / Work.Spaces.c α - 1) ^ 2
        ≤ (1 / Work.Spaces.c α - 1) ^ 2 := by
      have hg2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by nlinarith [hG0, hG1]
      exact mul_le_of_le_one_left (sq_nonneg (1 / Work.Spaces.c α - 1)) hg2
    calc (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2
        = ((Work.Spaces.Gam α θ - Work.Spaces.K θ)
            + Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)) ^ 2 := by rw [hkey]
      _ ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
              * |Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)|
            + (Work.Spaces.Gam α θ * (1 / Work.Spaces.c α - 1)) ^ 2 := sq_abs_add_le _ _
      _ = (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 2 * |Work.Spaces.Gam α θ - Work.Spaces.K θ|
              * (Work.Spaces.Gam α θ * |1 / Work.Spaces.c α - 1|)
            + (Work.Spaces.Gam α θ) ^ 2 * (1 / Work.Spaces.c α - 1) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hG0]; ring
      _ ≤ (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
            + 6 * |1 / Work.Spaces.c α - 1| + (1 / Work.Spaces.c α - 1) ^ 2 := by
          linarith [hE1, hE2]
      _ = (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C := by rw [hCdef]; ring
  -- integrability and the integral inequality
  have hcontG : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := continuous_Gam α hα
  have hA_int : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := ((hcontG.sub cont_K).pow 2).integrableOn_Icc
  have hConst_int : IntegrableOn (fun _ : ℝ => C) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hL_int : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := (((hcontG.div_const _).sub cont_K).pow 2).integrableOn_Icc
  have hR_int : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C) Work.Spaces.Iθ :=
    hA_int.add hConst_int
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C) :=
    integral_mono_ae hL_int hR_int
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt2 θ hθ)
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2 + C))
      = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
        + C * (Real.pi / 2) := by
    rw [integral_add hA_int hConst_int, int_const]
  rw [hsplit] at hmono
  -- the size of the correction constant
  have hCbound : C ≤ 18 * Real.pi * p + 9 * Real.pi ^ 2 * p ^ 2 := by
    rw [hCdef]
    have h1 : 6 * |1 / Work.Spaces.c α - 1| ≤ 18 * Real.pi * p := by linarith [he]
    have h2 : (1 / Work.Spaces.c α - 1) ^ 2 ≤ 9 * Real.pi ^ 2 * p ^ 2 := by
      have h3 : (3 * Real.pi * p) ^ 2 = 9 * Real.pi ^ 2 * p ^ 2 := by ring
      rw [← h3]
      have hb := abs_le.mp he
      exact sq_le_sq' hb.1 hb.2
    linarith
  have hstep := mul_le_mul_of_nonneg_right hCbound (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  -- final arithmetic
  have hπ2 : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hπ3 : Real.pi ^ 3 ≤ 31.255875 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [Work.Coercivity.GammaL2Bnd]
  have hfin : 25 * Real.pi / 32 - 2 + 6 * p * (Real.pi / 2)
      + (18 * Real.pi * p + 9 * Real.pi ^ 2 * p ^ 2) * (Real.pi / 2) ≤ (7 / 10 : ℝ) ^ 2 := by
    nlinarith [hπ2, hπ3, Real.pi_lt_d2, Real.pi_pos, hp_bound, le_of_lt hp0]
  linarith [hmono, hF, hstep, hfin]

end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_est =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

-- ROUTE (the `z → 0` half of the weighted `L²`-honesty of the `z^{s⁻}` Green term of `radGreen`).
-- Let `a := (2*(m:ℝ)+5)/α > 0` (from `hα`), `A z := ∫ t in (0:ℝ)..z, c t * t^(a-1)`,
-- `Φ := Work.FTS.EllExist.Honesty.G1 α m c` (so `Φ z = z^(-a) * A z`), and
-- `M0 := ∫ z in Ioo 0 1, c z^2/z^4` — a NONNEGATIVE real number, finite because `c z^2/z^4 ≥ 0` is
-- integrable by `h0`.
--
-- (1) For `z > 0`: `z * deriv Φ z = -a * Φ z + c z`  (product rule; `A' = c z * z^{a-1}` and
--     `z^(-a) * z^(a-1) = 1/z`, via `Real.rpow_add` with `0 < z`).
-- (2) Energy identity.  `u z := Φ z^2 / z^3` satisfies `u' z = ((-2a-3)*Φ z^2 + 2*c z*Φ z)/z^4`, so the
--     FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) on `[x,y] ⊆ (0,1)` gives
--       `(3+2a) * ∫ z in x..y, Φ z^2/z^4 = 2 * ∫ z in x..y, c z * Φ z / z^4 + Φ x^2/x^3 - Φ y^2/y^3`.
-- (3) ENDPOINT (this is the delicate step).  The pointwise Cauchy–Schwarz bound
--     `|Φ z| ≤ z^(3/2) * √(M0/(2a+3))` only gives `Φ z^2/z^4 = O(1/z)`, which is NOT integrable, so it cannot
--     be used directly; but it is exactly enough for the endpoint term.  Equivalently (avoiding a
--     substitution): the `x`-dependent AM-GM `2*|X*Y| ≤ λ*X^2 + Y^2/λ` with `X = |c u|*u^{-1}`, `Y = u^a`
--     and `λ := x^(a-1/2) > 0` gives, using `∫ u in (0)..x, c u^2/u^2 ≤ x^2 * M0`,
--       `|A x| ≤ x^(a+3/2) * C0`,  `C0 := M0/2 + 1/(2*(2a+1))`,
--     hence `Φ x^2/x^3 ≤ CΦ := C0^2` for every `x ∈ (0,1]`.
-- (4) AM-GM `2*|c z * Φ z|/z^4 ≤ η*c z^2/z^4 + η^{-1}*Φ z^2/z^4` with `η := 2/(3+2a)` (`3+2a > 0`),
--     combined with `∫ z in x..y, c z^2/z^4 ≤ M0` (monotonicity of the integral, `(x,y) ⊆ (0,1)`),
--     yields `∫ z in x..y, Φ z^2/z^4 ≤ M := 2*(η*M0 + CΦ)/(3+2a)` uniformly for all `0 < x < y < 1`.
-- (5) Continuity of `Φ` on `(0,1)`: product of `z ↦ z^(-a)` (continuous on `Ioi 0`) and the primitive `A`
--     (`MeasureTheory.continuousOn_primitive_interval`, or the FTC for primitives); integrability of
--     `t ↦ c t * t^(a-1)` on `[0,1]` follows from `h0` and the AM-GM bound
--     `2*|c t| * t^(a-1) ≤ c t^2/t^4 + t^(2a+2)` (both summands are integrable on `(0,1)`).
--
-- PROOF (as formalised): the three ingredients are the auxiliary file `G1Aux` (`a`, `A`, `M0`, `C0`,
-- `CΦ = C0²`, `η`, `M = 2(η M0 + CΦ)/(3+2a)`, `G1f_integrableOn`, `G1A_algebra: G1A_hasDerivAt`,
-- `G1_two_mul_abs_mul_le_mul`, `G1_csq_mono`) together with the three proved lemmas
-- `G1_endpoint_bound` (3), `G1_energy_identity` (2) and `G1_continuousOn` (5); the remaining step (4)
-- is the AM–GM comparison of interval integrals carried out below.
theorem G1_est (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, 0 < x → x < y → y < 1 →
        (∫ z in x..y, Work.FTS.EllExist.Honesty.G1 α m c z ^ 2 / z ^ 4) ≤ M) ∧
      ContinuousOn (fun z => Work.FTS.EllExist.Honesty.G1 α m c z) (Set.Ioo 0 1) := by
  refine ⟨⟨G1M α m c, G1M_nonneg hα m c, ?_⟩, G1_continuousOn hα m hc h0⟩
  intro x y hx hxy hy1
  have hη : 0 < G1eta α m := G1eta_pos hα m
  have hIn : ∀ z ∈ Set.Icc x y, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le hx hz.1
  have hsub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) 1 := fun z hz =>
    ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy1⟩
  have hΦc : ContinuousOn (G1 α m c) (Set.Icc x y) :=
    (G1_continuousOn hα m hc h0).mono hsub
  have hcc : ContinuousOn c (Set.Icc x y) :=
    hc.mono (fun z hz => lt_of_lt_of_le hx hz.1)
  have hpow : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x y) := continuousOn_id.pow 4
  have hz4ne : ∀ z ∈ Set.Icc x y, z ^ 4 ≠ 0 := fun z hz => pow_ne_zero 4 (ne_of_gt (hIn z hz))
  -- pointwise AM–GM
  have hpt : ∀ z ∈ Set.Icc x y,
      2 * |c z * G1 α m c z / z ^ 4|
        ≤ G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4) := by
    intro z hz
    have h := G1_two_mul_abs_mul_le_mul (l := G1eta α m) (X := c z / z ^ 2)
      (Y := G1 α m c z / z ^ 2) hη
    have e1 : (c z / z ^ 2) * (G1 α m c z / z ^ 2) = c z * G1 α m c z / z ^ 4 := by
      rw [div_mul_div_comm, show z ^ 2 * z ^ 2 = z ^ 4 from by ring]
    have e2 : G1eta α m * (c z / z ^ 2) ^ 2 + (G1 α m c z / z ^ 2) ^ 2 / G1eta α m
        = G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4) := by
      rw [div_pow, div_pow, div_eq_mul_inv]
      field_simp
    rwa [e1, e2] at h
  -- continuity / interval integrability of the two comparison functions
  have hcont1 : ContinuousOn (fun z : ℝ => 2 * |c z * G1 α m c z / z ^ 4|) (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy.le]
    exact continuousOn_const.mul (ContinuousOn.abs (ContinuousOn.div (hcc.mul hΦc) hpow hz4ne))
  have hcont2 : ContinuousOn
      (fun z : ℝ => G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.add (continuousOn_const.mul (ContinuousOn.div (hcc.pow 2) hpow hz4ne))
      (continuousOn_const.mul (ContinuousOn.div (hΦc.pow 2) hpow hz4ne))
  have hI1 : IntervalIntegrable (fun z : ℝ => 2 * |c z * G1 α m c z / z ^ 4|) volume x y :=
    ContinuousOn.intervalIntegrable hcont1
  have hI2 : IntervalIntegrable
      (fun z : ℝ => G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      volume x y := ContinuousOn.intervalIntegrable hcont2
  have hIc : IntervalIntegrable (fun z : ℝ => c z ^ 2 / z ^ 4) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.div (hcc.pow 2) hpow hz4ne
  have hIg : IntervalIntegrable (fun z : ℝ => G1 α m c z ^ 2 / z ^ 4) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxy.le]
    exact ContinuousOn.div (hΦc.pow 2) hpow hz4ne
  -- linearity
  have hlin : (∫ z in x..y,
        G1eta α m * (c z ^ 2 / z ^ 4) + (G1eta α m)⁻¹ * (G1 α m c z ^ 2 / z ^ 4))
      = G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_add (hIc.const_mul (G1eta α m)) (hIg.const_mul (G1eta α m)⁻¹),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the AM–GM step
  have hmono_int := intervalIntegral.integral_mono_on hxy.le hI1 hI2 hpt
  have h2I2 : 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
      ≤ ∫ z in x..y, 2 * |c z * G1 α m c z / z ^ 4| := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun z : ℝ => c z * G1 α m c z / z ^ 4) hxy.le
    have hle : (∫ z in x..y, c z * G1 α m c z / z ^ 4)
        ≤ ∫ z in x..y, |c z * G1 α m c z / z ^ 4| := le_trans (le_abs_self _) habs
    have hmul : 2 * (∫ z in x..y, |c z * G1 α m c z / z ^ 4|)
        = ∫ z in x..y, 2 * |c z * G1 α m c z / z ^ 4| := by
      rw [intervalIntegral.integral_const_mul]
    linarith
  have hA : 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
      ≤ G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) :=
    le_trans h2I2 (le_trans hmono_int (le_of_eq hlin))
  have hcsq := G1_csq_mono h0 x y hx hxy hy1
  have hB : G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4) ≤ G1eta α m * G1M0 c :=
    mul_le_mul_of_nonneg_left hcsq (le_of_lt hη)
  have hei := G1_energy_identity hα m hc h0 x y hx hxy hy1
  have hend := G1_endpoint_bound hα m hc h0 x hx (hxy.trans hy1)
  have hy0 : (0 : ℝ) < y := lt_trans hx hxy
  have hyend : 0 ≤ G1 α m c y ^ 2 / y ^ 3 :=
    div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hy0) 3)
  have h3 : (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      ≤ G1eta α m * G1M0 c + G1CPhi α m c
        + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    calc (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4)
          + G1 α m c x ^ 2 / x ^ 3 - G1 α m c y ^ 2 / y ^ 3 := hei
      _ ≤ 2 * (∫ z in x..y, c z * G1 α m c z / z ^ 4) + G1CPhi α m c := by
          linarith [hend, hyend]
      _ ≤ (G1eta α m * (∫ z in x..y, c z ^ 2 / z ^ 4)
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) + G1CPhi α m c := by
          linarith [hA]
      _ ≤ (G1eta α m * G1M0 c
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) + G1CPhi α m c := by
          linarith [hB]
      _ = G1eta α m * G1M0 c + G1CPhi α m c
            + (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by ring
  have heta : 3 + 2 * G1a α m - (G1eta α m)⁻¹ = (G1eta α m)⁻¹ := by
    rw [G1eta, inv_div]; ring
  have hcoef : (3 + 2 * G1a α m) * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
        - (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      = (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4) := by
    rw [← sub_mul, heta]
  have key : (G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      ≤ G1eta α m * G1M0 c + G1CPhi α m c := by linarith [h3, hcoef]
  have hM : G1M α m c = G1eta α m * (G1eta α m * G1M0 c + G1CPhi α m c) := by
    rw [G1M, G1eta]
    have h3a : 3 + 2 * G1a α m ≠ 0 := by
      have := G1a_pos hα m; intro hc0; linarith [hc0]
    field_simp
  rw [hM]
  calc (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)
      = G1eta α m * ((G1eta α m)⁻¹ * (∫ z in x..y, G1 α m c z ^ 2 / z ^ 4)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), one_mul]
    _ ≤ G1eta α m * (G1eta α m * G1M0 c + G1CPhi α m c) :=
        mul_le_mul_of_nonneg_left key (le_of_lt hη)

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AgmonSlice.CutDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AgmonSlice

set_option autoImplicit false

/-- `ρ = w²`, the square of the radial weight `w z = (1+z)²/z²`. -/
def cutRho (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The function `u = ρ z χ² (z h')` of the integration by parts. -/
def cutU (h ψ : ℝ → ℝ) (y : ℝ) : ℝ := cutRho y * y * ψ y ^ 2 * (y * deriv h y)

/-- The integrand `ρ χ² (z h')² = u · h'` of the Agmon estimate. -/
def cutF (h ψ : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * ψ z ^ 2 * (z * deriv h z) ^ 2

/-- `ρ χ² h²`. -/
def cutHs (h ψ : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * ψ z ^ 2 * (h z) ^ 2

/-- `ρ h²`. -/
def cutH (h : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * (h z) ^ 2

/-- `ρ χ² (z² h'')²`. -/
def cutQs (h ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  cutRho z * ψ z ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2

@[simp] theorem cutRho_nonneg (z : ℝ) : 0 ≤ cutRho z := by
  rw [cutRho]; positivity


/-- `cutU h ψ · h' = cutF h ψ`, the pointwise identity behind the integration by parts. -/
theorem cutU_mul_deriv (h ψ : ℝ → ℝ) (z : ℝ) :
    cutU h ψ z * deriv h z = cutF h ψ z := by
  simp only [cutU, cutF]
  ring

end Work.FTS.EllipticEst.AgmonSlice
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.radial_ibp_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 800000



/-- `z ↦ w z ^ 2` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.add continuous_id).continuousOn.pow 2
    · exact (continuous_id.continuousOn).pow 2
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      exact pow_ne_zero 2 (ne_of_gt hz')
  refine (hw.pow 2).congr ?_
  intro z hz
  simp only [Work.Spaces.w, Pi.pow_apply]


end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.corrLeftRate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter intervalIntegral

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ### Local copies of the transfer and Gronwall steps

`sliceLimLeft.lean` and `sliceGronwallLeft.lean` contain the proofs we need, but the latter does
not elaborate (it uses `sliceGronwallInterface` / `sliceGronwallPointwise` / `gronwallIntegralOn`
without importing them), so `sliceLimLeft` is unusable too.  The steps are reproduced here with
local names, importing the three building ingredients directly. -/







end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.corrRightRate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### The flux integrand and elementary trigonometric extractions -/






/-! ### The `L²` datum and the flux tail bound -/





/-! ### The flux decomposition -/


/-! ### Vanishing of the flux limit -/


/-! ### Boundedness of the amplitude -/


/-! ### The target -/


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I4_Gprim_deriv =====
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

set_option linter.unusedSimpArgs false

/-! ## Elementary angular identities -/

/-- **The weight identity.**  On the open quadrant
`sin θ cos θ σ(θ) = (1/2) sin(2θ)^{1-η}`, the form in which the vanishing at the two
endpoints is visible (`1 - η = 1/100 > 0`). -/
private lemma sin_cos_sig_eq (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin θ * Real.cos θ * sig θ
      = (1 / 2) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hkey : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
      Real.rpow_add hx, Real.rpow_one]
  have hsc : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]; ring
  simp only [sig]
  rw [hkey, hsc]
  ring

/-- The coefficient `A` of the `I₄`-identity, in the form in which the `cos 2θ` terms cancel:
`A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ`. -/
private lemma acoef_eq_cos_two_mul (θ : ℝ) :
    acoef θ = ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2 := by
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  rw [acoef_eq, Real.cos_two_mul', hc]
  ring

/-- **The `σ`-derivative identity.**  `(cos²θ - sin²θ)σ(θ) + sin θ cos θ σ'(θ)
= (1-η) cos 2θ σ(θ)`, i.e. the derivative of `sin θ cos θ σ(θ)` in the shape needed below. -/
private lemma sig_deriv_identity (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
        + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ
      = (1 - Work.Spaces.eta) * Real.cos (2 * θ) * sig θ := by
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos2 : Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ) = Real.cos (2 * θ) := by
    rw [Real.cos_two_mul']; ring
  have hkey : 2 * Real.sin θ * Real.cos θ * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← Real.sin_two_mul θ]
  have hkey2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [show -(Work.Spaces.eta) = 1 + (-(1 + Work.Spaces.eta)) by ring,
      Real.rpow_add hx, Real.rpow_one]
  have hrpow : Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ
      = -(Work.Spaces.eta) * Real.cos (2 * θ) * sig θ := by
    simp only [sigD_apply, sig]
    rw [show Real.sin θ * Real.cos θ
          * (-2 * Work.Spaces.eta * Real.cos (2 * θ)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        = -(Work.Spaces.eta) * Real.cos (2 * θ)
          * (2 * Real.sin θ * Real.cos θ
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) by ring,
      hkey.trans hkey2.symm]
  rw [hrpow, hcos2]
  ring

/-! ## The second derivative of `Ψ̄ = u / cos` -/

/-- **The chain rule for `u = cos θ · Ψ̄`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then
`u''(θ) = Ψ̄''(θ) cos θ - 2 Ψ̄'(θ) sin θ - Ψ̄(θ) cos θ`. -/
private lemma psi_second_deriv (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  -- `u' = Ψ̄' cos - Ψ̄ sin`, as an eventual equality of functions
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  -- the two factors of the explicit function are differentiable at `θ`
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-! ## The derivative of `σ` and the endpoint limits of the weight -/

/-- **The derivative of the angular weight.**  `σ'(θ) = sigD η θ` on the open quadrant,
where `sigD η θ = -2η cos 2θ sin(2θ)^{-(1+η)}`. -/
private lemma sig_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt sig (sigD Work.Spaces.eta θ) θ := by
  change HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta)))
    (-2 * Work.Spaces.eta * Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) θ
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    exact h
  have h4 : HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta)))
      ((Real.cos (2 * θ) * 2) * (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1)) θ :=
    h3.rpow_const (p := -(Work.Spaces.eta)) (Or.inl (ne_of_gt hx))
  have hexp : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1)
      = (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    congr 1
    ring
  rw [hexp] at h4
  have hval : (Real.cos (2 * θ) * 2) * (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = -2 * Work.Spaces.eta * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by ring
  rw [hval] at h4
  exact h4

/-- **The endpoint vanishing of the weight.**  For any `g` bounded on the open quadrant,
`(1/2) sin θ cos θ σ(θ) g(θ) → 0` both as `θ → 0⁺` and as `θ → (π/2)⁻`. -/
private lemma weight_tendsto (g : ℝ → ℝ) (C : ℝ)
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |g θ| ≤ C) :
    Filter.Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have heta : 0 < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _)
      (hg (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hweight : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
        = (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
    intro θ hθ
    rw [sin_cos_sig_eq θ hθ]
    ring
  have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ‖
        ≤ (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
    intro θ hθ
    have hx : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hnn : 0 ≤ (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hx _)
    rw [hweight θ hθ, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * |g θ|
        ≤ (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * C :=
          mul_le_mul_of_nonneg_left (hg θ hθ) hnn
      _ = (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by ring
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hs0 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hspi : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := hcont.tendsto (Real.pi / 2)
    have h0 : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : ∀ a : Filter ℝ, Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) a (nhds 0) →
      Filter.Tendsto (fun θ : ℝ => (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta))
        a (nhds 0) := by
    intro a ha
    have h := ha.rpow tendsto_const_nhds (Or.inr heta)
    rw [Real.zero_rpow (ne_of_gt heta)] at h
    simpa using h.const_mul ((1 / 4) * C)
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := by
    have h2 : Set.Iio (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    exact Filter.inter_mem self_mem_nhdsWithin h2
  have hmempi : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    have h1 : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (Real.pi / 2) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    exact Filter.inter_mem h1 self_mem_nhdsWithin
  refine ⟨?_, ?_⟩
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) ?_ (hlim _ hs0))
    filter_upwards [hmem0] with θ hθ
    exact hbnd θ hθ
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) ?_ (hlim _ hspi))
    filter_upwards [hmempi] with θ hθ
    exact hbnd θ hθ

/-- The primitive `Gprim u` (defined in `Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs`
as `(1/2)·sin θ cos θ·σ(θ)·((u/cos)'(θ)² - (u/cos)(θ)²)`, with `σ(θ) = sin(2θ)^{-η}`) has
derivative `Hintegrand u θ` at every `θ ∈ (0, π/2)`, and tends to `0` at both endpoints `0` and
`π/2` from within the interval.

Route: write `c = cos θ`, `s = sin θ`, `Ψ̄ = u/c`, `a(θ) = s·c·σ(θ)`.  On `(0,π/2)`,
`a'(θ) = ((1-η)/2)·cos(2θ)·σ(θ)` (from `σ' = -η·2cos(2θ)·sin(2θ)^{-η-1}`), and
`G' = (a'/2)((Ψ̄')² - Ψ̄²) + a(Ψ̄'Ψ̄'' - Ψ̄Ψ̄')`.  The relation `u = c·Ψ̄` gives
`u'' = -c·Ψ̄ - 2s·Ψ̄' + c·Ψ̄''`, which turns the second term into
`s·Ψ̄'·u'' = scσ(Ψ̄'Ψ̄'' - Ψ̄Ψ̄') - 2s²σ(Ψ̄')²`, so that
`G' = Acoef(θ)(Ψ̄')²σ + s·Ψ̄'·u''·σ - ((1-η)/2)cos 2θ·Ψ̄²σ` with
`Acoef(θ) = ((1-η)/2)cos 2θ + 2 sin²θ`; this is `Hintegrand u θ`.  The endpoint limits follow
from `|Ψ̄|, |Ψ̄'| ≤ C` (the hypothesis `hbdd`) and `a(θ) → 0` at both endpoints. -/
theorem I4_Gprim_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Gprim u) (Hintegrand u θ) θ) ∧
      Filter.Tendsto (Gprim u) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (Gprim u) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the derivative on the open quadrant
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have huAt : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
    have hVAt : ContDiffAt ℝ 2 (fun t : ℝ => u t / Real.cos t) θ :=
      huAt.div (Real.contDiff_cos.contDiffAt) hc
    have hVd : DifferentiableAt ℝ (fun t : ℝ => u t / Real.cos t) θ :=
      hVAt.differentiableAt (by simp)
    have hDd : DifferentiableAt ℝ (deriv (fun t : ℝ => u t / Real.cos t)) θ :=
      (hVAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by simp)
    have hdu := psi_second_deriv u huAt hc
    have hsig := sig_hasDerivAt hθ
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    have hA : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t * sig t)
        ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
          + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ) θ := by
      have h2 := ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).mul hsig
      convert h2 using 1 <;> ring
    have hF : HasDerivAt
        (fun y : ℝ => (deriv (fun t : ℝ => u t / Real.cos t) y) ^ 2 - (u y / Real.cos y) ^ 2)
        (2 * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
          - 2 * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ) θ := by
      have hp1 := hDd.hasDerivAt.pow 2
      have hp2 := hVd.hasDerivAt.pow 2
      convert hp1.sub hp2 using 1 <;> simp only [h21, pow_one] <;> ring
    have hA2 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * (Real.sin t * Real.cos t * sig t))
        ((1 / 2 : ℝ) * ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
          + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ)) θ := by
      have h2 := hA.const_mul (1 / 2 : ℝ)
      convert h2 using 1 <;> ring
    have hprod := hA2.mul hF
    change HasDerivAt (fun t : ℝ => (1 / 2) * (Real.sin t * Real.cos t * sig t)
        * ((deriv (fun t' : ℝ => u t' / Real.cos t') t) ^ 2 - (u t / Real.cos t) ^ 2))
      (Hintegrand u θ) θ
    convert hprod using 1 <;> simp only [Hintegrand, sig_deriv_identity θ hθ, hdu,
      acoef_eq_cos_two_mul θ, h21, pow_one] <;> ring
  · -- vanishing at `θ → 0⁺`
    obtain ⟨C, hC0, hC⟩ := hbdd
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      obtain ⟨h1, h2⟩ := hC θ hθ
      obtain ⟨hu1', hu2'⟩ := abs_le.mp h1
      obtain ⟨hd1, hd2⟩ := abs_le.mp h2
      have h3 : (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]
      have h4 : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (u θ / Real.cos θ)]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg (u θ / Real.cos θ)],
        by nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]⟩
    obtain ⟨hw1, hw2⟩ :=
      weight_tendsto (fun θ => (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        - (u θ / Real.cos θ) ^ 2) (C ^ 2) hbnd
    have hGeq : Gprim u = fun θ : ℝ =>
        (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
          * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2) := by
      funext θ
      simp only [Gprim]
    rw [hGeq]
    exact hw1
  · -- vanishing at `θ → (π/2)⁻`
    obtain ⟨C, hC0, hC⟩ := hbdd
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      obtain ⟨h1, h2⟩ := hC θ hθ
      obtain ⟨hu1', hu2'⟩ := abs_le.mp h1
      obtain ⟨hd1, hd2⟩ := abs_le.mp h2
      have h3 : (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]
      have h4 : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (u θ / Real.cos θ)]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg (u θ / Real.cos θ)],
        by nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]⟩
    obtain ⟨hw1, hw2⟩ :=
      weight_tendsto (fun θ => (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        - (u θ / Real.cos θ) ^ 2) (C ^ 2) hbnd
    have hGeq : Gprim u = fun θ : ℝ =>
        (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
          * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2) := by
      funext θ
      simp only [Gprim]
    rw [hGeq]
    exact hw2

end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz =====
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
set_option linter.unusedVariables false

/-! ## The two Cauchy–Schwarz steps

The proof is Cauchy–Schwarz twice: on each angular slice `θ ↦ ·` (where the weight `w2 z * sig θ`
is only known to make the *products* `g²`, `h²`, `g h` integrable — nothing is known about the
measurability of the slices themselves), and then in the radial variable `z`.

The slice step is `Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le`: the weighted
Cauchy–Schwarz for the *products*, i.e. the discriminant argument for
`t ↦ ∫_θ (g z θ - t h z θ)² w2 z σ θ ≥ 0`, which needs only the integrability of the three
weighted products.  The radial step is
`Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt`, the ordinary Cauchy–Schwarz
in `z` applied to `z ↦ √(∫_θ g² w²σ)` and `z ↦ √(∫_θ h² w²σ)`. -/

/-- **Cauchy–Schwarz for the angular-weight pairing** (namespace `Work.FTS.EllipticEst.AngSecond`).

For `g h : ℝ → ℝ → ℝ` whose pairings `IP g g`, `IP h h`, `IP g h` are honest (integrand
integrable, slicewise in `θ` and then in `z`),

  `|IP g h| ≤ √(IP g g) · √(IP h h)`,

where `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`, `w z = (1+z)²/z²`, `σ θ = sin(2θ)^{-η}`.
Since `IP u u = L2Sq (u · W)` with `W = w/sin(2θ)^{η/2}` (`L2Sq_mul_W`), this is Cauchy–Schwarz in
the weighted `L²` space, in iterated form.

Route: write `A z = ∫_θ g² w²σ`, `B z = ∫_θ h² w²σ`, `C z = ∫_θ g h w²σ`, so that `IP g g`,
`IP h h`, `IP g h` are the `z`-integrals of `A`, `B`, `C`.  The slicewise inequality
`C z² ≤ A z · B z` is `slice_sq_integral_mul_le` with `F = g z`, `G = h z`, `κ = w²σ` (the weight
enters only through the three integrability hypotheses, which `IPMem` supplies); it gives
`|C z| = √(C z²) ≤ √(A z)·√(B z)` because `A z ≥ 0`.  The `z`-integral is then handled by
`abs_setIntegral_le_sqrt_mul_sqrt`. -/
theorem IP_cauchy_schwarz {g h : ℝ → ℝ → ℝ} (hgg : IPMem g g) (hhh : IPMem h h)
    (hgh : IPMem g h) :
    |IP g h| ≤ Real.sqrt (IP g g) * Real.sqrt (IP h h) := by
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ with hAdef
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * w2 z * sig θ with hBdef
  set C : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ with hCdef
  have hAgg : IntegrableOn A Work.Spaces.Iz := by rw [hAdef]; exact hgg.2
  have hBgg : IntegrableOn B Work.Spaces.Iz := by rw [hBdef]; exact hhh.2
  have hCgg : IntegrableOn C Work.Spaces.Iz := by rw [hCdef]; exact hgh.2
  have hAz_nonneg : ∀ z ∈ Work.Spaces.Iz, 0 ≤ A z := by
    intro z _
    rw [hAdef]
    refine setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (mul_self_nonneg (g z θ)) (w2_nonneg z)) (sig_nonneg hθ)
  have hBz_nonneg : ∀ z ∈ Work.Spaces.Iz, 0 ≤ B z := by
    intro z _
    rw [hBdef]
    refine setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (mul_self_nonneg (h z θ)) (w2_nonneg z)) (sig_nonneg hθ)
  have hslice : ∀ z ∈ Work.Spaces.Iz, |C z| ≤ Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z hz
    have hκ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (fun θ => w2 z * sig θ) θ :=
      fun θ hθ => mul_nonneg (w2_nonneg z) (sig_nonneg hθ)
    have hF : IntegrableOn (fun θ => g z θ * g z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hgg.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hG : IntegrableOn (fun θ => h z θ * h z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hhh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hFG : IntegrableOn (fun θ => g z θ * h z θ * (w2 z * sig θ)) Work.Spaces.Iθ :=
      (hgh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
    have hcs := slice_sq_integral_mul_le (s := Work.Spaces.Iθ)
      (F := fun θ => g z θ) (G := fun θ => h z θ) (κ := fun θ => w2 z * sig θ) hκ hF hG hFG
    have hCeq : C z = ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * (w2 z * sig θ) := by
      rw [hCdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hAeq : A z = ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * (w2 z * sig θ) := by
      rw [hAdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hBeq : B z = ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * (w2 z * sig θ) := by
      rw [hBdef]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hC2 : C z ^ 2 ≤ A z * B z := by
      rw [hCeq, hAeq, hBeq]
      exact hcs
    calc |C z| = Real.sqrt ((C z) ^ 2) := (Real.sqrt_sq_eq_abs (C z)).symm
      _ ≤ Real.sqrt (A z * B z) := Real.sqrt_le_sqrt hC2
      _ = Real.sqrt (A z) * Real.sqrt (B z) := Real.sqrt_mul (hAz_nonneg z hz) (B z)
  change |∫ z in Work.Spaces.Iz, C z|
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, A z) * Real.sqrt (∫ z in Work.Spaces.Iz, B z)
  exact abs_setIntegral_le_sqrt_mul_sqrt hAgg hBgg hCgg hAz_nonneg hBz_nonneg hslice

end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.sigE_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond


end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

theorem slice_ftc_zero (g g' : ℝ → ℝ)
    (hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint : IntervalIntegrable g' MeasureTheory.volume 0 (Real.pi / 2))
    (h0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, g' θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval g']
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := g) (f' := g')
    (a := 0) (b := Real.pi / 2) hπ hderiv hint h0 h1
  rw [h, sub_self]

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareGap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngGap

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-! ## The angular gap-Wirtinger inequality, around the shared `AngGap` development

The sibling development `Submission/Work/FTS/EllipticEst/AngGap/` proves the pieces of the
sharp gap inequality on the orthogonal complement of `sin 2θ`:

* `AngGap.hBounds`: `|h θ| ≤ C sin 2θ` and `|deriv h θ| ≤ C` on `[0,π/2]`;
* `AngGap.stepD`: `∫ Q² = ∫ h'² - 4 ∫ h²` for `Q = h' - 2 cot(2θ) h`;
* `AngGap.ibp`: `∫ h² = -∫ V Q` for `V = angG h / sin 2θ`;
* `AngGap.assembly`: the final Cauchy–Schwarz + arithmetic step, given `12 ∫ V² ≤ ∫ h²`;
* `AngGap.PhiHCalc.*`: the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²` (the pointwise
  derivative of the antiderivative `6 V² cot 2θ`, its vanishing at both endpoints and the
  interval-integrability of the three pieces) — everything except the final assembly;
* `AngGap.primProps`: the primitive facts about `angG h` (the other half of the route), whose
  proof is complete except for two elementary integral estimates that are proved separately
  in `AngGap.int_sinSq_le_cube` and `AngGap.int_sinSq_shift`.

This file re-does those last two assembly steps *here* (so that this development does not
depend on the two in-flight files, whose proofs are not yet finished) and derives the gap
inequality. -/

/-- The primitive facts about `G = angG h`: its derivative is `h · sin 2θ` on `(0,π/2)`, it
vanishes at both endpoints (the mean-zero condition), and it is `O((sin 2θ)³)`.  The two
elementary integral estimates are taken from the proved siblings
`AngGap.int_sinSq_le_cube` and `AngGap.int_sinSq_shift`. -/
theorem primPropsP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hme : ∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ) = 0)
    (C : ℝ) (hC : 0 < C) (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ)) :
    (∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
      ∧ angG h 0 = 0 ∧ angG h (π / 2) = 0
      ∧ (∃ C' : ℝ, 0 < C' ∧ ∀ θ ∈ Set.Icc 0 (π / 2),
            |angG h θ| ≤ C' * (Real.sin (2 * θ)) ^ 3) := by
  have int_sinSq_le_cube : ∀ v ∈ Set.Icc (0 : ℝ) (π / 4),
      ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2
        ≤ 4 * (π / 4) ^ 3 * (Real.sin (2 * v)) ^ 3 :=
    fun v hv => Work.FTS.EllipticEst.AngGap.int_sinSq_le_cube v hv
  have int_sinSq_shift : ∀ θ : ℝ, ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2
      = ∫ t in (0 : ℝ)..(π / 2 - θ), (Real.sin (2 * t)) ^ 2 :=
    fun θ => Work.FTS.EllipticEst.AngGap.int_sinSq_shift θ
  -- the integrand and its continuity
  have hcont : ContinuousOn (fun s : ℝ => h s * Real.sin (2 * s)) (Set.Icc 0 (π / 2)) := by
    refine hh.continuousOn.mul ?_
    fun_prop
  -- the mean-zero condition as an interval integral
  have hzero : ∫ s in (0 : ℝ)..(π / 2), h s * Real.sin (2 * s) = 0 := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
    rw [← this]
    exact hme
  have hπ : angG h (π / 2) = 0 := hzero
  refine ⟨?_, by simp [angG], hπ, ?_⟩
  · -- the derivative
    intro θ hθ
    have hsub : Set.uIcc (0 : ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le (le_of_lt hθ.1)]
      exact Set.Icc_subset_Icc le_rfl hθ.2.le
    have hint : IntervalIntegrable (fun s : ℝ => h s * Real.sin (2 * s)) volume 0 θ :=
      (hcont.mono hsub).intervalIntegrable
    have hmem : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ :=
      Filter.mem_of_superset (Ioo_mem_nhds hθ.1 hθ.2) Set.Ioo_subset_Icc_self
    have hcontAt : ContinuousAt (fun s : ℝ => h s * Real.sin (2 * s)) θ :=
      hcont.continuousAt hmem
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => h s * Real.sin (2 * s)) (𝓝 θ) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_interior (hcont.mono interior_subset) θ
        (by simpa [interior_Icc] using hθ)
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
  · -- the bound
    refine ⟨C * (4 * (π / 4) ^ 3), by positivity, fun θ hθ => ?_⟩
    have hsubI : Set.uIcc (0 : ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le hθ.1]
      exact Set.Icc_subset_Icc le_rfl hθ.2
    have hsubJ : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le hθ.2]
      exact Set.Icc_subset_Icc hθ.1 le_rfl
    -- pointwise domination of the integrand by `C sin²2s`
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) (π / 2),
        |h s * Real.sin (2 * s)| ≤ C * (Real.sin (2 * s)) ^ 2 := by
      intro s hs
      have hsin_nonneg : 0 ≤ Real.sin (2 * s) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hs.1], by linarith [hs.2, Real.pi_pos]⟩
      rw [abs_mul, abs_of_nonneg hsin_nonneg]
      calc |h s| * Real.sin (2 * s) ≤ (C * Real.sin (2 * s)) * Real.sin (2 * s) :=
            mul_le_mul_of_nonneg_right (hbdd s hs) hsin_nonneg
        _ = C * (Real.sin (2 * s)) ^ 2 := by ring
    have hstepA : |angG h θ| ≤ C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 := by
      have hfi : IntervalIntegrable (fun s : ℝ => |h s * Real.sin (2 * s)|) volume 0 θ :=
        (hcont.abs.mono hsubI).intervalIntegrable
      have hgi : IntervalIntegrable (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) volume 0 θ := by
        have hc : ContinuousOn (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) (Set.Icc 0 (π / 2)) := by
          fun_prop
        exact (hc.mono hsubI).intervalIntegrable
      have h1 : |∫ s in (0)..θ, h s * Real.sin (2 * s)|
          ≤ ∫ s in (0)..θ, |h s * Real.sin (2 * s)| :=
        intervalIntegral.abs_integral_le_integral_abs hθ.1
      have h2 : ∫ s in (0)..θ, |h s * Real.sin (2 * s)|
          ≤ ∫ s in (0)..θ, C * (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_mono_on hθ.1 hfi hgi
          (fun s hs => hpt s ⟨hs.1, le_trans hs.2 hθ.2⟩)
      have h3 : ∫ s in (0)..θ, C * (Real.sin (2 * s)) ^ 2
          = C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_const_mul C _
      simp only [angG]
      rw [h3] at h2
      exact le_trans h1 h2
    have hstepB : |angG h θ| ≤ C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 := by
      have hfi : IntervalIntegrable (fun s : ℝ => |h s * Real.sin (2 * s)|) volume θ (π / 2) :=
        (hcont.abs.mono hsubJ).intervalIntegrable
      have hgi : IntervalIntegrable (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) volume θ (π / 2) := by
        have hc : ContinuousOn (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) (Set.Icc 0 (π / 2)) := by
          fun_prop
        exact (hc.mono hsubJ).intervalIntegrable
      have hfi0 : IntervalIntegrable (fun s : ℝ => h s * Real.sin (2 * s)) volume θ (π / 2) :=
        (hcont.mono hsubJ).intervalIntegrable
      have hsplt : (∫ s in (0)..θ, h s * Real.sin (2 * s))
          + ∫ s in θ..(π / 2), h s * Real.sin (2 * s) = 0 := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          ((hcont.mono hsubI).intervalIntegrable) hfi0, hzero]
      have heq : angG h θ = - ∫ s in θ..(π / 2), h s * Real.sin (2 * s) := by
        show (∫ s in (0)..θ, h s * Real.sin (2 * s)) = _
        linarith
      rw [heq, abs_neg]
      have h1 : |∫ s in θ..(π / 2), h s * Real.sin (2 * s)|
          ≤ ∫ s in θ..(π / 2), |h s * Real.sin (2 * s)| :=
        intervalIntegral.abs_integral_le_integral_abs hθ.2
      have h2 : ∫ s in θ..(π / 2), |h s * Real.sin (2 * s)|
          ≤ ∫ s in θ..(π / 2), C * (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_mono_on hθ.2 hfi hgi
          (fun s hs => hpt s ⟨le_trans hθ.1 hs.1, hs.2⟩)
      have h3 : ∫ s in θ..(π / 2), C * (Real.sin (2 * s)) ^ 2
          = C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_const_mul C _
      rw [h3] at h2
      exact le_trans h1 h2
    by_cases hcase : θ ≤ π / 4
    · -- left half
      have hA : θ ∈ Set.Icc (0 : ℝ) (π / 4) := ⟨hθ.1, hcase⟩
      calc |angG h θ| ≤ C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 := hstepA
        _ ≤ C * (4 * (π / 4) ^ 3 * (Real.sin (2 * θ)) ^ 3) :=
            mul_le_mul_of_nonneg_left (int_sinSq_le_cube θ hA) hC.le
        _ = (C * (4 * (π / 4) ^ 3)) * (Real.sin (2 * θ)) ^ 3 := by ring
    · -- right half: reflect in `π/4`
      have hcase' : π / 4 < θ := not_le.mp hcase
      have hu : π / 2 - θ ∈ Set.Icc (0 : ℝ) (π / 4) :=
        ⟨by linarith [hθ.2], by linarith [hcase']⟩
      have hcube := int_sinSq_le_cube (π / 2 - θ) hu
      have hsin_eq : Real.sin (2 * (π / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
      rw [hsin_eq] at hcube
      calc |angG h θ| ≤ C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 := hstepB
        _ = C * ∫ t in (0)..(π / 2 - θ), (Real.sin (2 * t)) ^ 2 := by rw [int_sinSq_shift θ]
        _ ≤ C * (4 * (π / 4) ^ 3 * (Real.sin (2 * θ)) ^ 3) :=
            mul_le_mul_of_nonneg_left hcube hC.le
        _ = (C * (4 * (π / 4) ^ 3)) * (Real.sin (2 * θ)) ^ 3 := by ring

/-- **The weighted Hardy inequality** `12 ∫ V² ≤ ∫ h²` for `V = angG h / sin 2θ`.

The exact identity `h² - 12 V² - (h - 6 cot(2θ) V)² = (6 V² cot(2θ))'` on `(0,π/2)` is
integrated over `[0,π/2]`: the antiderivative `angPhiH h = 6 V² cot 2θ` vanishes at both
endpoints and the integrand `angF h` is interval-integrable, so
`∫ (h² - 12 V²) = ∫ (h - 6 cot 2θ V)² ≥ 0`. -/
theorem hardyP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2), |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    12 * (∫ θ in Work.Spaces.Iθ, (angV h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
  have hlt : (0 : ℝ) < π / 2 := by positivity
  -- the pointwise derivative identity
  have hΦderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angPhiH h) (angF h θ) θ :=
    fun θ hθ => (Work.FTS.EllipticEst.AngGap.PhiHCalc.deriv_angPhiH h hg θ hθ).2
  -- integrability of the pieces, and of `angF h`
  obtain ⟨hInt1, hInt2, hInt3⟩ :=
    Work.FTS.EllipticEst.AngGap.PhiHCalc.integrable_pieces h hh hg C hC hbdd hCg
  have hInt12 : IntervalIntegrable (fun y : ℝ => (h y) ^ 2 - 12 * (angV h y) ^ 2)
      volume 0 (π / 2) := IntervalIntegrable.sub hInt1 (IntervalIntegrable.const_mul hInt2 12)
  have hIntF : IntervalIntegrable (angF h) volume 0 (π / 2) :=
    IntervalIntegrable.sub hInt12 hInt3
  -- the fundamental theorem of calculus for `angPhiH h`
  have hFTC : (∫ y in (0 : ℝ)..(π / 2), angF h y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (b := π / 2) (f := angPhiH h) (f' := angF h) (fa := 0) (fb := 0) hlt hΦderiv hIntF
      (Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_right h C hC hCg)
      (Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_left h C hC hCg)
    simpa using h
  -- splitting the integral
  have hconv : (∫ y in (0 : ℝ)..(π / 2), angF h y)
      = ∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2) - angFt h y :=
    intervalIntegral.integral_congr (fun y _ => angF_eq_sub h y)
  have hs1 : (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2) - angFt h y)
      = (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2))
        - ∫ y in (0 : ℝ)..(π / 2), angFt h y :=
    intervalIntegral.integral_sub (f := fun y : ℝ => (h y) ^ 2 - 12 * (angV h y) ^ 2)
      (g := angFt h) hInt12 hInt3
  have hs2 : (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2))
      = (∫ y in (0 : ℝ)..(π / 2), (h y) ^ 2)
        - 12 * (∫ y in (0 : ℝ)..(π / 2), (angV h y) ^ 2) := by
    rw [intervalIntegral.integral_sub (f := fun y : ℝ => (h y) ^ 2)
        (g := fun y : ℝ => 12 * (angV h y) ^ 2) hInt1
        (IntervalIntegrable.const_mul hInt2 12),
      intervalIntegral.integral_const_mul]
  have hFt_nonneg : 0 ≤ ∫ y in (0 : ℝ)..(π / 2), angFt h y :=
    intervalIntegral.integral_nonneg hlt.le (fun y _ => angFt_nonneg h y)
  rw [Iθ_eq_interval (fun θ => (angV h θ) ^ 2), Iθ_eq_interval (fun θ => (h θ) ^ 2)]
  linarith [hFTC, hconv, hs1, hs2, hFt_nonneg]

/-- **The angular gap-Wirtinger inequality**: a `C²` function on `[0,π/2]` vanishing at both
endpoints whose first sine mode vanishes satisfies `16 ∫ h² ≤ ∫ (h')²`. -/
theorem gapP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) (hmean : (∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ)) = 0) :
    16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 := by
  obtain ⟨C, hCpos, hbdd, hbdd'⟩ := hBounds h hh h0 h1
  obtain ⟨hg, -, -, hRest⟩ := primPropsP9 h hh hmean C hCpos hbdd
  obtain ⟨Cg, hCgpos, hCg⟩ := hRest
  -- a single constant dominating both `C` and the constant of the cubic bound of `angG h`
  set Cm : ℝ := max C Cg with hCmdef
  have hCm : 0 < Cm := by rw [hCmdef]; exact lt_of_lt_of_le hCpos (le_max_left C Cg)
  have hCCm : C ≤ Cm := by rw [hCmdef]; exact le_max_left C Cg
  have hCgCm : Cg ≤ Cm := by rw [hCmdef]; exact le_max_right C Cg
  have hbddC : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ Cm * Real.sin (2 * θ) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact le_trans (hbdd θ hθ) (mul_le_mul_of_nonneg_right hCCm hs)
  have hbdd'C : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ Cm :=
    fun θ hθ => le_trans (hbdd' θ hθ) hCCm
  have hCgC : ∀ θ ∈ Set.Icc 0 (π / 2), |angG h θ| ≤ Cm * (Real.sin (2 * θ)) ^ 3 := by
    intro θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ 3 := pow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) 3
    exact le_trans (hCg θ hθ) (mul_le_mul_of_nonneg_right hCgCm hs)
  exact assembly h hh Cm hCm hbddC hbdd'C hg Cm hCm hCgC
    (stepD h hh h0 h1 Cm hCm hbddC hbdd'C)
    (hardyP9 h hh hg Cm hCm hbddC hCgC)
    (ibp h hh hg Cm hCm hbddC hbdd'C hCgC)

/-- **The constrained slice Poincaré inequality, constant `9`** (Elgindi, Annals 194 (3)
2021): for `f` of class `C²` on `[0,π/2]` with `f 0 = f (π/2) = 0` and
`∫_{Iθ} f θ · sinθcos²θ dθ = 0`, one has `9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`. -/
theorem slicePoincare9_fts : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 →
    f (π / 2) = 0 → (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 :=
  fun f hf h0 h1 horth => slicePoincare9_of_gap gapP9 f hf h0 h1 horth

end Work.FTS.EllipticEst.P9
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary



end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.SliceZDeriv_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option maxHeartbeats 800000

/-! ## Measurability of the second `z`-partial and of the `θ`-slice of `V`

The ingredients of the proof that have nothing to do with the Taylor identity itself: a.e. strong
measurability of the `t`-slice of `∂_z²V` (from joint continuity of `∂_z²V` on the open
quadrant, `Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn`) and a.e. measurability of the
`θ`-slice of `V`.
-/

/-- The `t`-slice `t ↦ ∂_z²V (z₀+t) θ` (for an interior angle `θ`) is a.e. strongly measurable
on `(0,δ]`: it is continuous there, being the composition of the jointly continuous
`(z,θ) ↦ ∂_z²V z θ` on the quadrant with the continuous map `t ↦ (z₀+t, θ)`, whose image of
`(0,δ]` lies in the quadrant because `z₀ > 0` and `θ ∈ (0,π/2)`. -/
private lemma aesm_timeSlice_pzIter2 (V : ℝ → ℝ → ℝ)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ θ : ℝ} (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun t => Work.Spaces.pzIter 2 V (z₀ + t) θ)
      (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) := by
  have hmap : ContinuousOn (fun t : ℝ => (z₀ + t, θ)) (Set.Ioc 0 δ) :=
    (by fun_prop : Continuous fun t : ℝ => (z₀ + t, θ)).continuousOn
  have hc : ContinuousOn (fun t : ℝ => Work.Spaces.pzIter 2 V (z₀ + t) θ) (Set.Ioc 0 δ) := by
    have hcomp := (PzIterTwoContinuousOn (isOpen_Ioi.prod isOpen_Ioo) hV).comp hmap
      (fun t ht => by
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨by linarith [ht.1, hz₀], hθ⟩)
    have hfun : (Function.uncurry (Work.Spaces.pzIter 2 V) ∘ fun t : ℝ => (z₀ + t, θ))
        = fun t : ℝ => Work.Spaces.pzIter 2 V (z₀ + t) θ := by
      funext t; rfl
    rwa [hfun] at hcomp
  exact hc.aestronglyMeasurable measurableSet_Ioc

/-- The `θ`-slice `θ ↦ ofReal ((V z θ · wth θ)²)` is a.e. measurable on `(0,π/2)`: the slice
`θ ↦ V z θ` is continuous there (as `z > 0`), `wth` is measurable, and `ofReal` and squaring
are measurable. -/
private lemma aemeasurable_slice_V_sq (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun θ => ENNReal.ofReal ((V z θ * wth θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
  have hcomp := hV.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun θ hθ => ⟨hz, hθ⟩)
  have hcont : ContinuousOn (fun θ : ℝ => V z θ) (Set.Ioo 0 (Real.pi / 2)) := hcomp
  have h1 : AEMeasurable (fun θ : ℝ => V z θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hcont.aestronglyMeasurable measurableSet_Ioo).aemeasurable
  have h2 : AEMeasurable wth (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hwthmeas.aemeasurable
  have h3 : AEMeasurable (fun θ : ℝ => V z θ * wth θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := h1.mul h2
  have h4 : AEMeasurable (fun θ : ℝ => (V z θ * wth θ) * (V z θ * wth θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := h3.mul h3
  exact ENNReal.measurable_ofReal.comp_aemeasurable (by simpa only [pow_two] using h4)

/-- **Finiteness of the `∂_z`-slice from finiteness of the slice and its second derivative.**

Let `V : ℝ → ℝ → ℝ` be `C²` on the open quadrant `(0,∞) × (0,π/2)` and let `wth : ℝ → ℝ` be
measurable, nonnegative.  Assume

* for every `z > 0`, `∫⁻_{θ ∈ (0,π/2)} ofReal ((V z θ · wth θ)²) < ∞`;
* for every `z > 0` there is `δ > 0` with
  `∫⁻_{z' ∈ (z, z+δ)} ( ∫⁻_{θ ∈ (0,π/2)} ofReal ((∂_z²V (z',θ) · wth θ)²) ) < ∞`.

Then for every `z₀ > 0`, `∫⁻_{θ ∈ (0,π/2)} ofReal ((∂_zV (z₀,θ) · wth θ)²) < ∞`.

(This is the statement of `Submission.Work.FTS.EllipticEst.DzAmgm.SliceDerivLtTop`, currently
`sorry` there; a copy is needed here since that file cannot be edited.)

ROUTE.  Fix `z₀ > 0` and `δ > 0` as in the second hypothesis.  For every `θ ∈ (0,π/2)` the
one-variable Taylor formula with integral remainder applied to the `C²` slice `z ↦ V z θ`
between `z₀` and `z₀+δ` gives

  `V (z₀+δ) θ - V z₀ θ = δ · ∂_zV z₀ θ + ∫_0^δ (δ-t) ∂_z²V (z₀+t) θ dt`,

hence `∂_zV z₀ θ = (1/δ)(V (z₀+δ) θ - V z₀ θ - F θ)` with
`F θ = ∫_0^δ (δ-t) ∂_z²V (z₀+t) θ dt`, and `(a+b+c)² ≤ 3(a²+b²+c²)` reduces the claim to the
finiteness of `∫⁻_θ ofReal ((F θ · wth θ)²)`.  The weighted Cauchy–Schwarz inequality
`F θ² ≤ (δ²/2) ∫_0^δ (δ-t) (∂_z²V (z₀+t) θ)² dt` followed by Tonelli (pull the `t`-integral out
of the `θ`-`lintegral`) bounds this by
`ofReal (δ³/2) ∫⁻_{z' ∈ (z₀, z₀+δ)} ( ∫⁻_θ ofReal ((∂_z²V (z',θ) · wth θ)²) )`,
which is finite by the second hypothesis at `z = z₀`.  Measurability: `V` is continuous on the
open quadrant, so its uncurried form is a.e. strongly measurable for the product measure
(`Work.Spaces.aesm_of_continuousOn_Qd`); `wth` is measurable; slices of a.e. strongly
measurable functions are a.e. strongly measurable.  The `θ`-endpoints `0, π/2` are null and
irrelevant.  No integrability of `∂_zV` and no smoothness beyond `C²` of the uncurried `V` are
assumed. -/
theorem SliceZDeriv_finite (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwth : ∀ θ, 0 ≤ wth θ)
    (hwthmeas : Measurable wth)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
        (fun θ => ENNReal.ofReal ((V z θ * wth θ) ^ 2)) < ⊤)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo z (z + δ)))
        (fun z' => MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
          (fun θ => ENNReal.ofReal ((Work.Spaces.pzIter 2 V z' θ * wth θ) ^ 2))) < ⊤)
    {z₀ : ℝ} (hz₀ : 0 < z₀) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (fun θ => ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)) < ⊤ := by
  obtain ⟨δ, hδpos, hBfin⟩ := hB z₀ hz₀
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδpos
  set c3 : ℝ≥0∞ := ENNReal.ofReal (3 * δ⁻¹ ^ 2) with hc3
  set c6 : ℝ≥0∞ := ENNReal.ofReal (δ ^ 3 / 3) with hc6
  have hc3top : c3 ≠ ⊤ := by rw [hc3]; exact ENNReal.ofReal_ne_top
  have hc6top : c6 ≠ ⊤ := by rw [hc6]; exact ENNReal.ofReal_ne_top

  -- ### The pointwise bound
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2) ≤
        c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    intro θ hθ
    -- (1) the Cauchy–Schwarz bound for the integral remainder
    have hZA : ENNReal.ofReal
        (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ) ^ 2)
        ≤ c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) := by
      have hcs := Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe (a := (0 : ℝ))
        (b := δ) hδnn (fun t => Work.Spaces.pzIter 2 V (z₀ + t) θ)
        (aesm_timeSlice_pzIter2 V hsm hz₀ hθ)
      have hsq : 0 ≤ (wth θ) ^ 2 := sq_nonneg _
      calc ENNReal.ofReal
              (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ) ^ 2)
          = ENNReal.ofReal
              (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)) ^ 2)
              * ENNReal.ofReal ((wth θ) ^ 2) := by
            rw [show ((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                  * wth θ) ^ 2
                  = (∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2
                    * (wth θ) ^ 2 from by ring,
                ENNReal.ofReal_mul (sq_nonneg _)]
        _ ≤ (ENNReal.ofReal ((δ - 0) ^ 3 / 3) * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2))
              * ENNReal.ofReal ((wth θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcs bot_le
        _ = c6 * (ENNReal.ofReal ((wth θ) ^ 2) * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2)) := by
            rw [hc6, sub_zero]
            ring
        _ = c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((wth θ) ^ 2)
                * ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2) := by
            rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((wth θ) ^ 2)) _
              ENNReal.ofReal_ne_top]
        _ = c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) := by
            congr 1
            refine lintegral_congr (fun t => ?_)
            rw [← ENNReal.ofReal_mul (sq_nonneg (wth θ)),
              show (wth θ) ^ 2 * (Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2
                = (Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2 from by ring]
    -- (2) Taylor + the three term inequality
    have hmain : ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2) ≤
        c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := by
      have htay := Work.FTS.EllipticEst.DzAmgm.SliceTaylorIdentity V hsm hz₀ hδpos hθ
      set A : ℝ := V (z₀ + δ) θ * wth θ with hA
      set B : ℝ := V z₀ θ * wth θ with hBreal
      set C : ℝ := (∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ
        with hC
      have hreal : (δ⁻¹ * (A - B - C)) ^ 2 ≤ (3 * δ⁻¹ ^ 2) * (A ^ 2 + (B ^ 2 + C ^ 2)) := by
        have h3 : (A - B - C) ^ 2 ≤ 3 * (A ^ 2 + (B ^ 2 + C ^ 2)) := by
          nlinarith [sq_nonneg (A + B), sq_nonneg (C - B), sq_nonneg (A + C)]
        have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (δ⁻¹))
        nlinarith [h4]
      have hconv : (Work.Spaces.pz V z₀ θ * wth θ) ^ 2 = (δ⁻¹ * (A - B - C)) ^ 2 := by
        rw [htay]
        simp only [hA, hBreal, hC]
        ring
      calc ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)
          = ENNReal.ofReal ((δ⁻¹ * (A - B - C)) ^ 2) := by rw [hconv]
        _ ≤ ENNReal.ofReal ((3 * δ⁻¹ ^ 2) * (A ^ 2 + (B ^ 2 + C ^ 2))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = c3 * (ENNReal.ofReal (A ^ 2) + (ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (C ^ 2))) := by
            rw [hc3, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_add (sq_nonneg A) (by positivity),
              ENNReal.ofReal_add (sq_nonneg B) (sq_nonneg C)]
        _ = c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := by
            rw [hA, hBreal, hC]
    calc ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)
        ≤ c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := hmain
      _ ≤ c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
            have hstep : ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                  + ENNReal.ofReal
                      (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2)
                ≤ ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                  + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                      ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) :=
              add_le_add (le_refl _) hZA
            refine mul_le_mul_of_nonneg_left ?_ bot_le
            exact add_le_add (le_refl _) hstep

  -- ### Integration
  have h1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2))
      ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    refine lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun θ hθ => hpt θ hθ)

  have h2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))))
      = c3 * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2))
          + ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2))
             + c6 * ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                 ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                   ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    rw [MeasureTheory.lintegral_const_mul' c3 _ hc3top]
    congr 1
    rw [MeasureTheory.lintegral_add_left'
      (aemeasurable_slice_V_sq V wth hwthmeas hsm (by linarith : 0 < z₀ + δ))]
    congr 1
    rw [MeasureTheory.lintegral_add_left'
      (aemeasurable_slice_V_sq V wth hwthmeas hsm hz₀)]
    rw [MeasureTheory.lintegral_const_mul' c6 _ hc6top]

  have hXAfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)) < ⊤ :=
    hG (z₀ + δ) (by simp only [Set.mem_Ioi]; linarith)
  have hYAfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)) < ⊤ := hG z₀ hz₀
  have hHfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫⁻ t in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)) < ⊤ := by
    rw [SliceSwapLintegral V wth hwthmeas hsm hz₀ hδpos]
    exact hBfin

  have hfin : c3 * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2))
        + ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2))
           + c6 * ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
               ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                 ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) < ⊤ :=
    ENNReal.mul_lt_top (by rw [hc3]; exact ENNReal.ofReal_lt_top)
      ((ENNReal.add_lt_top).mpr ⟨hXAfin,
        (ENNReal.add_lt_top).mpr ⟨hYAfin,
          ENNReal.mul_lt_top (by rw [hc6]; exact ENNReal.ofReal_lt_top) hHfin⟩⟩)

  exact lt_of_le_of_lt (h1.trans (le_of_eq h2)) hfin

end Work.FTS.EllipticEst.Blocks
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.HarOp_eq_sub_of_chain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin

open MeasureTheory Set Filter
open scoped Topology

/-- For `1 < β` and `0 ≤ x` one has `x ^ (β - 1) * x = x ^ β`. -/
theorem rpow_sub_one_mul_self_aux {β : ℝ} (hβ : 1 < β) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (β - 1) * x = x ^ β := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.zero_rpow (x := β - 1) (by linarith), zero_mul,
      Real.zero_rpow (x := β) (ne_of_gt (lt_trans zero_lt_one hβ))]
  · have h : x ^ β = x ^ (β - 1) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [h, Real.rpow_one]

theorem HarOp_eq_sub_of_chain (β : ℝ) (hβ : 1 < β) {u v : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => v r / r) (Set.Ioo 0 z))
    (hchain : ∀ s ∈ Set.Ioo (0 : ℝ) z, u z - u s = ∫ r in s..z, v r / r) :
    Work.FTS.EllipticEst.HarOp β v z = u z - β * Work.FTS.EllipticEst.HarOp β u z := by
  have hβ0 : (0 : ℝ) < β := lt_trans zero_lt_one hβ
  have hβm : (0 : ℝ) < β - 1 := by linarith
  have hzle : (0 : ℝ) ≤ z := hz.le
  set g : ℝ → ℝ := fun r => v r / r with hgdef
  have hintI : IntervalIntegrable g volume (0 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hzle).mpr hint
  set F : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, g r with hFdef
  have hFac : AbsolutelyContinuousOnInterval F (0 : ℝ) z :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hintI (c := 0)
      (by simp [hzle])
  have hFcont : ContinuousOn F (Set.uIcc (0 : ℝ) z) := hFac.continuousOn
  set c : ℝ := u z - F z with hcdef
  set A : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * v s with hAdef
  set B : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s with hBdef
  set C : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * F s with hCdef
  -- ### the chain relation, in terms of the primitive `F`
  have hsub : ∀ s ∈ Set.Ioo (0 : ℝ) z, F s = u s - c := by
    intro s hs
    have h1 : u z - u s = ∫ r in s..z, g r := hchain s hs
    have hzi : IntervalIntegrable g volume s z := hintI.mono_set (by
      rw [uIcc_of_le hzle, uIcc_of_le hs.2.le]
      exact Icc_subset_Icc hs.1.le le_rfl)
    have h0i : IntervalIntegrable g volume (0 : ℝ) s := hintI.mono_set (by
      rw [uIcc_of_le hzle, uIcc_of_le hs.1.le]
      exact Icc_subset_Icc le_rfl hs.2.le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0i hzi
    have hus : u s = u z - ((∫ r in (0 : ℝ)..z, g r) - ∫ r in (0 : ℝ)..s, g r) := by
      linarith [hadd, h1]
    rw [hcdef, hFdef]
    linarith [hus]
  -- ### step 1: `s ^ (β-1) * v s = s ^ β * g s` pointwise
  have hA : A = ∫ s in (0 : ℝ)..z, s ^ β * g s := by
    rw [hAdef]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hzle] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hgdef]
      simp only [Real.zero_rpow (x := β - 1) (by linarith),
        Real.zero_rpow (x := β) (ne_of_gt hβ0), zero_mul]
    · rw [hgdef]
      rw [← rpow_sub_one_mul_self_aux hβ h0.le]
      field_simp
  -- ### step 2: integration by parts
  have hpow_ac : AbsolutelyContinuousOnInterval (fun s : ℝ => s ^ β) (0 : ℝ) z :=
    ContDiffOn.absolutelyContinuousOnInterval fun x _ =>
      (Real.contDiffAt_rpow_const_of_le (x := x) (p := β) (n := 1)
        (by exact_mod_cast hβ.le : ((1 : ℕ) : ℝ) ≤ β)).contDiffWithinAt
  have hIbpRaw := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hpow_ac hFac
  have hderivF : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) z → deriv F x = g x := by
    filter_upwards [hintI.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (Set.uIoc_subset_uIcc hxI) 0 (by simp [hzle])).deriv
  have hstep1 : (∫ x in (0 : ℝ)..z, x ^ β * deriv F x) = ∫ x in (0 : ℝ)..z, x ^ β * g x :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hderivF] with x hx hxI
      rw [hx hxI])
  have hstep2 : (∫ x in (0 : ℝ)..z, deriv (fun s : ℝ => s ^ β) x * F x)
      = β * C := by
    have hp : ∀ x ∈ Set.uIcc (0 : ℝ) z,
        deriv (fun s : ℝ => s ^ β) x * F x = β * (x ^ (β - 1) * F x) := by
      intro x _
      rw [(Real.hasDerivAt_rpow_const (p := β) (Or.inr (le_of_lt hβ))).deriv]
      ring
    rw [intervalIntegral.integral_congr hp, intervalIntegral.integral_const_mul, hCdef]
  have hIbp : (∫ s in (0 : ℝ)..z, s ^ β * g s) = z ^ β * F z - β * C := by
    have hbd : ((fun s : ℝ => s ^ β) 0) * F 0 = 0 := by
      simp only [Real.zero_rpow (ne_of_gt hβ0), zero_mul]
    rw [hstep1, hstep2, hbd] at hIbpRaw
    simpa using hIbpRaw
  -- ### step 3: `∫_0^z x^{β-1} = z^β/β`
  have hrpowint : (∫ x in (0 : ℝ)..z, x ^ (β - 1)) = z ^ β / β := by
    have hInt : IntervalIntegrable (fun x : ℝ => x ^ (β - 1)) volume (0 : ℝ) z :=
      (Real.continuous_rpow_const hβm.le).continuousOn.intervalIntegrable
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) z,
        HasDerivAt (fun y : ℝ => y ^ β / β) (x ^ (β - 1)) x := by
      intro x _
      have h := (Real.hasDerivAt_rpow_const (p := β) (Or.inr (le_of_lt hβ)) (x := x)).div_const β
      convert h using 1
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    rw [Real.zero_rpow (ne_of_gt hβ0), zero_div, sub_zero] at h
    exact h
  -- ### step 4: `B = C + c * (z^β/β)`
  have hBrel : B = C + c * (z ^ β / β) := by
    have hcongr1 : B = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * (F s + c) := by
      rw [hBdef]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hzle] at hs
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · rw [← h0, Real.zero_rpow (x := β - 1) (by linarith), zero_mul, zero_mul]
      · rcases eq_or_lt_of_le hs.2 with hz' | hz'
        · rw [hz', hcdef, hFdef]
          ring
        · have hsI : s ∈ Set.Ioo (0 : ℝ) z := ⟨h0, hz'⟩
          rw [hsub s hsI]
          ring
    have hcongr2 : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * (F s + c))
        = ∫ s in (0 : ℝ)..z, (s ^ (β - 1) * F s + c * s ^ (β - 1)) :=
      intervalIntegral.integral_congr fun s _ => by ring
    have hint1 : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * F s) volume (0 : ℝ) z :=
      (((Real.continuous_rpow_const hβm.le).continuousOn).mul hFcont).intervalIntegrable
    have hint2 : IntervalIntegrable (fun s : ℝ => c * s ^ (β - 1)) volume (0 : ℝ) z :=
      (continuous_const.mul (Real.continuous_rpow_const hβm.le)).continuousOn.intervalIntegrable
    have hadd := intervalIntegral.integral_add hint1 hint2
    have hcm : (∫ s in (0 : ℝ)..z, c * s ^ (β - 1)) = c * (z ^ β / β) := by
      rw [intervalIntegral.integral_const_mul, hrpowint]
    rw [hcongr1, hcongr2, hadd, hcm, hCdef]
  -- ### assembly
  show z ^ (-β) * A = u z - β * (z ^ (-β) * B)
  have hzpow : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  rw [hA, hIbp, hBrel]
  have hL : z ^ (-β) * (z ^ β * F z - β * C) = F z - β * (z ^ (-β) * C) := by
    rw [mul_sub, ← mul_assoc, hzpow, one_mul]
    ring
  have hX : β * (z ^ (-β) * (C + c * (z ^ β / β))) = β * (z ^ (-β) * C) + c := by
    have h1 : z ^ (-β) * (c * (z ^ β / β)) = c / β := by
      rw [show c * (z ^ β / β) = z ^ β * (c / β) by ring, ← mul_assoc, hzpow, one_mul]
    rw [mul_add, h1]
    field_simp
  rw [hL, hX]
  linarith [hcdef]

end Work.FTS.EllipticEst.Cert.GbarSin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.Cert


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.sliceThetaIbpSep2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

theorem sliceThetaIbpSep2 (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ * deriv (deriv v) θ))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ) ^ 2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (deriv v θ) ^ 2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                  * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ * (v θ) ^ 2) := by
  exact sliceThetaIbpSep v ψ hv hψ hsep

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DthIter_mul_of_angular =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Iterates of `Lop` commute with constant factors -/

/-- Every iterate of `Lop` commutes with multiplication by a constant. -/
lemma Lop_iter_const_mul_angular (c : ℝ) (u : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.Lop^[i] (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop^[i] u θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [deriv_const_mul_field (u := c) (v := Work.Spaces.Lop^[n] u) (x := θ)]
      ring

/-! ## The main identity -/

theorem DthIter_mul_of_angular (i : ℕ) (g u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => g z * u θ) z θ
      = g z * (Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ) := by
  have h1 : Work.Spaces.DthIter i (fun z θ => g z * u θ) z θ
      = Work.Spaces.Lop^[i] (fun θ' => g z * u θ') θ := by
    have h := congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (fun z θ => g z * u θ) z) θ
    simpa using h
  have h2 : Work.Spaces.DthIter i (fun _ θ' => u θ') 0 θ
      = Work.Spaces.Lop^[i] u θ := by
    have h := congrFun (Work.Spaces.DthIter_eq_iterate_Lop i (fun _ θ' => u θ') 0) θ
    simpa using h
  rw [h1, h2]
  exact congrFun (Lop_iter_const_mul_angular (g z) u i) θ

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The one-variable product rule, without differentiability hypotheses -/

/-- `deriv (A · c) z = deriv A z * c` for a constant `c`, with no differentiability
hypothesis: `deriv_mul_const_field` is stated unconditionally, the convention being that
`deriv` is `0` where the function is not differentiable. -/
theorem deriv_mul_radial (A : ℝ → ℝ) (c z : ℝ) :
    deriv (fun z' => A z' * c) z = deriv A z * c :=
  deriv_mul_const_field (u := A) c

/-! ## `D_z` on a separated product -/

/-- `D_z (g(z)·u(θ)) = (rDz g)(z) · u(θ)`: the operator `D_z = z∂_z` sees only the
`z`-variable and the radial factor becomes the one-variable operator `rDz`. -/
theorem Dz_radial_mul (g u : ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => g z * u θ) = fun z θ => rDz g z * u θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz, rDz]
  rw [deriv_mul_radial (A := g) (u θ)]
  ring

/-- Iterated form of `Dz_radial_mul`: `D_z^j (g(z)·u(θ)) = (rDzIter j g)(z) · u(θ)`. -/
theorem DzIter_radial_mul (j : ℕ) (g u : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => g z * u θ)
      = fun z θ => rDzIter j g z * u θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, rDzIter_succ]
      exact Dz_radial_mul (rDzIter n g) u

/-! ## The requested pointwise form -/

theorem DzIter_mul_of_radial (j : ℕ) (g u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => g z * u θ) z θ
      = Work.FTS.EllipticEst.rDzIter j g z * u θ :=
  congrFun (congrFun (DzIter_radial_mul j g u) z) θ

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.hkIntegrand0Prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint integrability of the level-`0` integrand over `Iz × Iθ`

The level-`0` integrand `HkIntegrand α 0 f` is the single square
`(f · w / sin(2θ)^{η/2})²` (there are no derivative slots when `k = 0`), so it is continuous
on the open quadrant whenever `f` is, hence a.e. strongly measurable for the product of the
restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.  The hypothesis
`HkMem α 0 f` supplies integrability of every angular slice and of the outer integral, and
`Work.Spaces.integrable_prod_of_iterated` (Tonelli, in the nonnegative case) then yields joint
integrability over `Iz × Iθ`.
-/

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- For `θ ∈ (0, π/2)` the sine `sin(2θ)` is positive. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The level-`0` integrand is the single square `(f · w / sin(2θ)^{η/2})²`, because the
sums defining `HkIntegrand` are indexed by `range (0+1) = {0}` and the mixed slot
requires `1 ≤ i` with `i + j ≤ 0`, hence never occurs. -/
theorem hkIntegrand_zero_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]



end

end Work.FTS.EllipticEst.H2W.AeProof.ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.VTwoAlt.vTwoW4WeakAlt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.VTwoAlt

open MeasureTheory Set Filter
open scoped Real Topology Interval

set_option maxHeartbeats 1000000

/-! ## Elementary trigonometric facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

lemma one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h2θ : 0 < 2 * θ := by linarith [hθ.1]
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi h2θ (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs.le]
  exact (one_le_inv₀ hpos).mpr h1

lemma cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

lemma cos_le_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have h := Real.sin_le (x := Real.pi / 2 - θ) (by linarith [hθ.2])
  rwa [Real.sin_pi_div_two_sub] at h

lemma two_div_pi_mul_sub_le_cos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
  have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2]) (by linarith [hθ.1])
  rwa [Real.sin_pi_div_two_sub] at h

lemma sin_two_eq_sin_two_sub {θ : ℝ} :
    Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
  rw [show 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) by ring, Real.sin_pi_sub]



/-! ## The weighted Hardy (Agmon) inequality

With `y = π/2 - θ` we prove `(2+γ) ∫ G²y^{-4-γ} ≤ ∫ (G')²y^{-2-γ}` on `(θ₀,π/2)`,
assuming only the *finiteness* of the left integral (and of the right one, so that the
statement is not vacuous). -/

/-- The weighted flux `G² y^{-3-γ}` whose derivative is the sum of the two weights. -/
noncomputable def agFlux (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-3 - γ)

/-- The derivative of `agFlux`. -/
noncomputable def agFluxDeriv (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  2 * G θ * deriv G θ * (Real.pi / 2 - θ) ^ (-3 - γ)
    + G θ ^ 2 * ((3 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ))

/-- The left integrand `G² y^{-4-γ}`. -/
noncomputable def agF (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)

/-- The right integrand `(G')² y^{-2-γ}`. -/
noncomputable def agFd (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv G θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)

lemma agF_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agF γ G θ := by
  rw [agF]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

lemma agFd_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agFd γ G θ := by
  rw [agFd]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

lemma agFlux_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agFlux γ G θ := by
  rw [agFlux]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

/-- The Agmon inequality on a compact subinterval `[a,t]`, `θ₀ < a ≤ t < π/2`, without any
integrability hypothesis (all integrands are continuous on `[a,t]`):

  `(2+γ) ∫_a^t G²y^{-4-γ} ≤ (G t)²y_t^{-3-γ} + ∫_a^t (G')²y^{-2-γ}`. -/
lemma agmon_interval (γ θ₀ : ℝ) (hγ1 : 1 ≤ γ) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo θ₀ (Real.pi / 2)))
    {a t : ℝ} (ha : θ₀ < a) (hat : a ≤ t) (ht : t < Real.pi / 2) :
    (2 + γ) * (∫ x in a..t, agF γ G x) ≤ agFlux γ G t + ∫ x in a..t, agFd γ G x := by
  have hsub : Set.uIcc a t ⊆ Set.Ioo θ₀ (Real.pi / 2) := by
    rw [Set.uIcc_of_le hat]
    exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 ht⟩
  have hGc : ContinuousOn G (Set.uIcc a t) := hG.continuousOn.mono hsub
  have hGd : ContinuousOn (deriv G) (Set.uIcc a t) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hpos : ∀ x ∈ Set.uIcc a t, 0 < Real.pi / 2 - x := by
    intro x hx
    rw [Set.uIcc_of_le hat] at hx
    linarith [hx.2, ht]
  have hyc : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-3 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hy4c : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-4 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hy2c : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-2 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  -- the derivative of the flux
  have hderiv : ∀ x ∈ Set.uIcc a t, HasDerivAt (agFlux γ G) (agFluxDeriv γ G x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo θ₀ (Real.pi / 2) := hsub hx
    have hy : 0 < Real.pi / 2 - x := hpos x hx
    have hGat : HasDerivAt G (deriv G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have h1 : HasDerivAt (fun θ => G θ ^ 2) (2 * G x * deriv G x) x := by
      have h := hGat.pow 2
      convert h using 1
      ring
    have h2 : HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-3 - γ))
        ((-3 - γ) * (Real.pi / 2 - x) ^ (-3 - γ - 1) * (-1)) x := by
      have hinner : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
      have hout := Real.hasDerivAt_rpow_const (x := Real.pi / 2 - x) (p := -3 - γ)
        (Or.inl (ne_of_gt hy))
      exact hout.comp x hinner
    have hprod : HasDerivAt (fun θ : ℝ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-3 - γ))
        (2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
          + G x ^ 2 * ((3 + γ) * (Real.pi / 2 - x) ^ (-4 - γ))) x := by
      have hp := h1.mul h2
      have hval : 2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
          + G x ^ 2 * ((-3 - γ) * (Real.pi / 2 - x) ^ (-3 - γ - 1) * (-1))
          = 2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
            + G x ^ 2 * ((3 + γ) * (Real.pi / 2 - x) ^ (-4 - γ)) := by
        rw [show (-3 : ℝ) - γ - 1 = -4 - γ by ring]
        ring
      rw [hval] at hp
      exact hp
    exact hprod
  have hFluxInt : IntervalIntegrable (agFluxDeriv γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact ((((continuousOn_const.mul hGc).mul hGd).mul hyc)).add
      ((hGc.pow 2).mul (continuousOn_const.mul hy4c))
  have hFInt : IntervalIntegrable (agF γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact (hGc.pow 2).mul hy4c
  have hFdInt : IntervalIntegrable (agFd γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact (hGd.pow 2).mul hy2c
  -- pointwise arithmetic–geometric mean
  have hpt : ∀ x ∈ Set.Icc a t, (2 + γ) * agF γ G x ≤ agFluxDeriv γ G x + agFd γ G x := by
    intro x hx
    have hxu : x ∈ Set.uIcc a t := by rwa [Set.uIcc_of_le hat]
    have hy : 0 < Real.pi / 2 - x := hpos x hxu
    set y := Real.pi / 2 - x with hydef
    have e1 : y ^ (-2 - γ / 2) * y ^ (-2 - γ / 2) = y ^ (-4 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have e2 : y ^ (-1 - γ / 2) * y ^ (-1 - γ / 2) = y ^ (-2 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have e3 : y ^ (-2 - γ / 2) * y ^ (-1 - γ / 2) = y ^ (-3 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have hsq : 0 ≤ (G x * y ^ (-2 - γ / 2) + deriv G x * y ^ (-1 - γ / 2)) ^ 2 := sq_nonneg _
    have hexp : (G x * y ^ (-2 - γ / 2) + deriv G x * y ^ (-1 - γ / 2)) ^ 2
        = G x ^ 2 * y ^ (-4 - γ) + 2 * (G x * deriv G x * y ^ (-3 - γ))
          + (deriv G x) ^ 2 * y ^ (-2 - γ) := by
      rw [add_sq, mul_pow, mul_pow, pow_two (y ^ (-2 - γ / 2)), pow_two (y ^ (-1 - γ / 2)), e1, e2]
      rw [show 2 * (G x * y ^ (-2 - γ / 2)) * (deriv G x * y ^ (-1 - γ / 2))
          = 2 * (G x * deriv G x * y ^ (-3 - γ)) by rw [← e3]; ring]
    rw [hexp] at hsq
    have hA : 0 ≤ G x ^ 2 * y ^ (-4 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _)
    have hC : 0 ≤ (deriv G x) ^ 2 * y ^ (-2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _)
    have h3 : 0 ≤ (3 + γ) * y ^ (-4 - γ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hy.le _)
    have hB : 0 ≤ G x ^ 2 * ((3 + γ) * y ^ (-4 - γ)) := mul_nonneg (sq_nonneg _) h3
    rw [agF, agFluxDeriv, agFd, ← hydef]
    nlinarith [hsq]
  have hstep : (2 + γ) * (∫ x in a..t, agF γ G x)
      ≤ (∫ x in a..t, agFluxDeriv γ G x) + (∫ x in a..t, agFd γ G x) := by
    have h1 : (∫ x in a..t, (2 + γ) * agF γ G x)
        ≤ ∫ x in a..t, (agFluxDeriv γ G x + agFd γ G x) :=
      intervalIntegral.integral_mono_on hat (hFInt.const_mul (2 + γ))
        (hFluxInt.add hFdInt) hpt
    rwa [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hFluxInt hFdInt] at h1
  have hFTC : ∫ x in a..t, agFluxDeriv γ G x = agFlux γ G t - agFlux γ G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hFluxInt
  have hUa : 0 ≤ agFlux γ G a := agFlux_nonneg γ G (by linarith)
  linarith [hstep, hFTC, hUa]

/-- `(π/2 - θ)^{-1}` is not integrable near `π/2`. -/
lemma not_integrableOn_sub_inv (T : ℝ) (hT : T < Real.pi / 2) :
    ¬ IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ)) (Set.Ioo T (Real.pi / 2)) := by
  intro hI
  have hb : 0 < Real.pi / 2 - T := by linarith
  set K : ℝ := ∫ θ in Set.Ioo T (Real.pi / 2), (Real.pi / 2 - θ) ^ (-1 : ℝ) with hK
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo T (Real.pi / 2))]
      (fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Real.rpow_nonneg (by linarith [hθ.2]) _
  -- bound by the full set integral and compute by the fundamental theorem of calculus
  have hkey : ∀ s ∈ Set.Ioo T (Real.pi / 2),
      Real.log (Real.pi / 2 - T) - Real.log (Real.pi / 2 - s) ≤ K := by
    intro s hs
    have hTs : T ≤ s := hs.1.le
    have h1 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ))
        = ∫ x in Set.Ioo T s, (Real.pi / 2 - x) ^ (-1 : ℝ) := by
      rw [intervalIntegral.integral_of_le hTs, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have h2 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ)) ≤ K := by
      rw [h1, hK]
      exact MeasureTheory.setIntegral_mono_set hI hnn
        (Filter.Eventually.of_forall (fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hs.2⟩))
    have h3 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ))
        = Real.log (Real.pi / 2 - T) - Real.log (Real.pi / 2 - s) := by
      have hderiv : ∀ x ∈ Set.uIcc T s,
          HasDerivAt (fun θ : ℝ => -Real.log (Real.pi / 2 - θ)) ((Real.pi / 2 - x) ^ (-1 : ℝ)) x := by
        intro x hx
        rw [Set.uIcc_of_le hTs] at hx
        have hx2 : Real.pi / 2 - x ≠ 0 := ne_of_gt (by linarith [hx.2, hs.2])
        have hinner : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
        have hlog := (hinner.log hx2).neg
        convert hlog using 1
        rw [Real.rpow_neg_one]
        ring
      have hint : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (-1 : ℝ)) volume T s := by
        refine ContinuousOn.intervalIntegrable ?_
        refine (continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl ?_)
        have hpx : 0 < Real.pi / 2 - x := by
          rw [Set.uIcc_of_le hTs] at hx
          linarith [hx.2, hs.2]
        exact ne_of_gt hpx
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      rw [this]
      ring
    linarith [h2, h3]
  -- take `s = π/2 - 1/(n+1)` and let `n → ∞`: the logarithm diverges
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      K - Real.log (Real.pi / 2 - T) < Real.log ((n : ℝ) + 1) := by
    have h3 : ∀ᶠ x : ℝ in Filter.atTop,
        K - Real.log (Real.pi / 2 - T) < Real.log x ∧ (1 : ℝ) ≤ x :=
      (Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)).and (eventually_ge_atTop 1)
    filter_upwards [Filter.Tendsto.eventually tendsto_natCast_atTop_atTop h3] with n hn
    have h4 : Real.log ((n : ℝ)) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith [hn.2]) (by linarith)
    linarith [hn.1, h4]
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hb
  obtain ⟨n, hn, hnN⟩ := (hev.and (eventually_ge_atTop N₀)).exists
  have hlog1 : Real.log (1 / ((n : ℝ) + 1)) = -Real.log ((n : ℝ) + 1) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hmem : Real.pi / 2 - 1 / ((n : ℝ) + 1) ∈ Set.Ioo T (Real.pi / 2) := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    refine ⟨?_, by linarith [show (0:ℝ) < 1 / ((n:ℝ)+1) by positivity]⟩
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hnN
      linarith
    linarith [hN₀, hle]
  have hle := hkey _ hmem
  have hs_eq : Real.pi / 2 - (Real.pi / 2 - 1 / ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by ring
  rw [hs_eq, hlog1] at hle
  linarith [hle, hn]


/-- The weighted Hardy (Agmon) inequality.  See the module docstring. -/
theorem agmonWeightedHardy (γ θ₀ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (hθ₀ : θ₀ < Real.pi / 2)
    (G : ℝ → ℝ) (hG : ContDiffOn ℝ 1 G (Set.Ioo θ₀ (Real.pi / 2)))
    (hInt : IntegrableOn (agF γ G) (Set.Ioo θ₀ (Real.pi / 2)))
    (hInt' : IntegrableOn (agFd γ G) (Set.Ioo θ₀ (Real.pi / 2))) :
    (2 + γ) * (∫ θ in Set.Ioo θ₀ (Real.pi / 2), agF γ G θ)
      ≤ ∫ θ in Set.Ioo θ₀ (Real.pi / 2), agFd γ G θ := by

  have hII : ∀ t, θ₀ < t → t < Real.pi / 2 →
      (2 + γ) * (∫ x in Set.Ioo θ₀ t, agF γ G x)
        ≤ agFlux γ G t + (∫ x in Set.Ioo θ₀ t, agFd γ G x) := by
    intro t ht0 ht1
    set aSeq : ℕ → ℝ := fun n => θ₀ + (t - θ₀) / ((n : ℝ) + 2) with haSeq
    have hd : 0 < t - θ₀ := by linarith
    have hmono_a : Monotone (fun n => Set.Ioo (aSeq n) t) := by
      intro i j hij
      refine Set.Ioo_subset_Ioo_left ?_
      have hij' : ((i : ℝ) + 2) ≤ ((j : ℝ) + 2) := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      have h1 : (t - θ₀) / ((j : ℝ) + 2) ≤ (t - θ₀) / ((i : ℝ) + 2) :=
        div_le_div_of_nonneg_left hd.le (by positivity) hij'
      simp only [haSeq]
      linarith
    have hlt_t : ∀ n, aSeq n < t := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hpos : 0 < ((n : ℝ) + 2) := by positivity
      have h1 : (t - θ₀) / ((n : ℝ) + 2) < t - θ₀ := by
        rw [div_lt_iff₀ hpos]
        nlinarith [hd, hn0]
      simp only [haSeq]
      linarith
    have hgt_0 : ∀ n, θ₀ < aSeq n := by
      intro n
      have hpos : 0 < ((n : ℝ) + 2) := by positivity
      have h1 : 0 < (t - θ₀) / ((n : ℝ) + 2) := div_pos hd hpos
      simp only [haSeq]
      linarith
    have hUnion : (⋃ n, Set.Ioo (aSeq n) t) = Set.Ioo θ₀ t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Ioo]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨lt_trans (hgt_0 n) h1, h2⟩
      · rintro ⟨hx1, hx2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (x - θ₀) / (t - θ₀) by positivity)
        refine ⟨n, ?_, hx2⟩
        have hpos : 0 < ((n : ℝ) + 1) := by positivity
        have h2 : (t - θ₀) / ((n : ℝ) + 1) < x - θ₀ := by
          have h4 : (1 / ((n : ℝ) + 1)) * (t - θ₀) < ((x - θ₀) / (t - θ₀)) * (t - θ₀) :=
            mul_lt_mul_of_pos_right hn hd
          rw [div_mul_cancel₀ (x - θ₀) (ne_of_gt hd)] at h4
          rwa [one_div_mul_eq_div] at h4
        have h3 : (t - θ₀) / ((n : ℝ) + 2) ≤ (t - θ₀) / ((n : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left hd.le (by positivity)
          linarith
        simp only [haSeq]
        linarith
    have hstep : ∀ n, (2 + γ) * (∫ x in Set.Ioo (aSeq n) t, agF γ G x)
        ≤ agFlux γ G t + (∫ x in Set.Ioo (aSeq n) t, agFd γ G x) := by
      intro n
      have h := agmon_interval γ θ₀ hγ1 hG (hgt_0 n) (le_of_lt (hlt_t n)) ht1
      have e1 : (∫ x in aSeq n..t, agF γ G x) = ∫ x in Set.Ioo (aSeq n) t, agF γ G x := by
        rw [intervalIntegral.integral_of_le (le_of_lt (hlt_t n)), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have e2 : (∫ x in aSeq n..t, agFd γ G x) = ∫ x in Set.Ioo (aSeq n) t, agFd γ G x := by
        rw [intervalIntegral.integral_of_le (le_of_lt (hlt_t n)), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [e1, e2] at h
      exact h
    have hIntU : IntegrableOn (agF γ G) (⋃ n, Set.Ioo (aSeq n) t) := by
      rw [hUnion]; exact hInt.mono_set (Set.Ioo_subset_Ioo_right ht1.le)
    have hIntU' : IntegrableOn (agFd γ G) (⋃ n, Set.Ioo (aSeq n) t) := by
      rw [hUnion]; exact hInt'.mono_set (Set.Ioo_subset_Ioo_right ht1.le)
    have hT1 := MeasureTheory.tendsto_setIntegral_of_monotone (f := agF γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo (aSeq n) t) (fun n => measurableSet_Ioo) hmono_a hIntU
    have hT2 := MeasureTheory.tendsto_setIntegral_of_monotone (f := agFd γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo (aSeq n) t) (fun n => measurableSet_Ioo) hmono_a hIntU'
    rw [hUnion] at hT1 hT2
    refine le_of_tendsto_of_tendsto (hT1.const_mul (2 + γ)) (tendsto_const_nhds.add hT2) ?_
    exact Filter.Eventually.of_forall hstep

  set A : ℝ := ∫ x in Set.Ioo θ₀ (Real.pi / 2), agF γ G x with hA
  set B : ℝ := ∫ x in Set.Ioo θ₀ (Real.pi / 2), agFd γ G x with hB
  have hmono : ∀ {s t : ℝ}, s ≤ t → t ≤ Real.pi / 2 →
      (∫ x in Set.Ioo θ₀ s, agF γ G x) ≤ ∫ x in Set.Ioo θ₀ t, agF γ G x := by
    intro s t hst ht
    refine MeasureTheory.setIntegral_mono_set (hInt.mono_set (Set.Ioo_subset_Ioo_right ht)) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agF_nonneg γ G (by linarith [hx.2, hst, ht])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hst⟩
  have hmonod : ∀ {s t : ℝ}, s ≤ t → t ≤ Real.pi / 2 →
      (∫ x in Set.Ioo θ₀ s, agFd γ G x) ≤ ∫ x in Set.Ioo θ₀ t, agFd γ G x := by
    intro s t hst ht
    refine MeasureTheory.setIntegral_mono_set (hInt'.mono_set (Set.Ioo_subset_Ioo_right ht)) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agFd_nonneg γ G (by linarith [hx.2, hst, ht])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hst⟩
  have hleA : ∀ t, t ≤ Real.pi / 2 → (∫ x in Set.Ioo θ₀ t, agF γ G x) ≤ A := by
    intro t ht
    rw [hA]
    refine MeasureTheory.setIntegral_mono_set hInt ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agF_nonneg γ G (by linarith [hx.2])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 ht⟩
  have hleB : ∀ t, t ≤ Real.pi / 2 → (∫ x in Set.Ioo θ₀ t, agFd γ G x) ≤ B := by
    intro t ht
    rw [hB]
    refine MeasureTheory.setIntegral_mono_set hInt' ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agFd_nonneg γ G (by linarith [hx.2])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 ht⟩
  set cs : ℕ → ℝ := fun n => Real.pi / 2 - 1 / ((n : ℝ) + 1) with hcs
  have hcs_lt : ∀ n, cs n < Real.pi / 2 := by
    intro n; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hcs]; linarith
  have hcs_mono : Monotone cs := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      linarith
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hij'
    simp only [hcs]; linarith
  have hcs_tend : Tendsto cs Filter.atTop (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hcs] using tendsto_const_nhds.sub h1
  have hUnion_cs : (⋃ n, Set.Ioo θ₀ (cs n)) = Set.Ioo θ₀ (Real.pi / 2) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨h1, lt_of_lt_of_le h2 (le_of_lt (hcs_lt n))⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < Real.pi / 2 - x by linarith)
      refine ⟨n, hx1, ?_⟩
      simp only [hcs]; linarith
  have hA_tend : Tendsto (fun n => ∫ x in Set.Ioo θ₀ (cs n), agF γ G x) Filter.atTop (𝓝 A) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (f := agF γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo θ₀ (cs n)) (fun n => measurableSet_Ioo)
      (fun i j hij => Set.Ioo_subset_Ioo_right (hcs_mono hij)) (by rw [hUnion_cs]; exact hInt)
    rwa [hUnion_cs, ← hA] at h
  have hB_tend : Tendsto (fun n => ∫ x in Set.Ioo θ₀ (cs n), agFd γ G x) Filter.atTop (𝓝 B) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (f := agFd γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo θ₀ (cs n)) (fun n => measurableSet_Ioo)
      (fun i j hij => Set.Ioo_subset_Ioo_right (hcs_mono hij)) (by rw [hUnion_cs]; exact hInt')
    rwa [hUnion_cs, ← hB] at h
  have hA_lim : Tendsto (fun t => ∫ x in Set.Ioo θ₀ t, agF γ G x) (𝓝[<] (Real.pi / 2)) (𝓝 A) := by
    rw [tendsto_order]
    constructor
    · intro a' ha'
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hA_tend.eventually (eventually_gt_nhds ha'))
      obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
      set M := max N N₀ with hM
      have hMa : a' < ∫ x in Set.Ioo θ₀ (cs M), agF γ G x := hN M (le_max_left _ _)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (show cs M < Real.pi / 2 from hcs_lt M)] with t ht htlt
      exact lt_of_lt_of_le hMa (hmono ht.le htlt.le)
    · intro a' ha'
      rw [eventually_nhdsWithin_iff]
      filter_upwards with t ht
      exact lt_of_le_of_lt (hleA t ht.le) ha'
  have hB_lim : Tendsto (fun t => ∫ x in Set.Ioo θ₀ t, agFd γ G x) (𝓝[<] (Real.pi / 2)) (𝓝 B) := by
    rw [tendsto_order]
    constructor
    · intro a' ha'
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hB_tend.eventually (eventually_gt_nhds ha'))
      obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
      set M := max N N₀ with hM
      have hMa : a' < ∫ x in Set.Ioo θ₀ (cs M), agFd γ G x := hN M (le_max_left _ _)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (show cs M < Real.pi / 2 from hcs_lt M)] with t ht htlt
      exact lt_of_lt_of_le hMa (hmonod ht.le htlt.le)
    · intro a' ha'
      rw [eventually_nhdsWithin_iff]
      filter_upwards with t ht
      exact lt_of_le_of_lt (hleB t ht.le) ha'
  by_contra hcon
  have hc : 0 < (2 + γ) * A - B := by
    have h' : B < (2 + γ) * A := not_le.mp hcon
    linarith
  by_cases hcase : ∀ T, T < Real.pi / 2 → ∃ t ∈ Set.Ioo T (Real.pi / 2), agFlux γ G t ≤ ((2 + γ) * A - B) / 2
  · choose tS htS using fun n : ℕ => hcase (cs n) (hcs_lt n)
    have htS_tend : Tendsto tS Filter.atTop (𝓝[<] (Real.pi / 2)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hcs_tend tendsto_const_nhds ?_ ?_
        · exact fun n => (htS n).1.1.le
        · exact fun n => (htS n).1.2.le
      · exact Filter.Eventually.of_forall fun n => (htS n).1.2
    have hlimA : Tendsto (fun n => (2 + γ) * (∫ x in Set.Ioo θ₀ (tS n), agF γ G x)) Filter.atTop (𝓝 ((2 + γ) * A)) := by
      simpa only [Function.comp_apply] using (hA_lim.comp htS_tend).const_mul (2 + γ)
    have hlimB : Tendsto (fun n => ((2 + γ) * A - B) / 2 + (∫ x in Set.Ioo θ₀ (tS n), agFd γ G x))
        Filter.atTop (𝓝 (((2 + γ) * A - B) / 2 + B)) :=
      tendsto_const_nhds.add (hB_lim.comp htS_tend)
    obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
    have hfin : (2 + γ) * A ≤ ((2 + γ) * A - B) / 2 + B := by
      refine le_of_tendsto_of_tendsto hlimA hlimB ?_
      refine (eventually_ge_atTop N₀).mono ?_
      intro n hn
      have hgt : θ₀ < tS n := lt_trans (lt_of_lt_of_le hN₀ (hcs_mono hn)) (htS n).1.1
      have h1 := hII (tS n) hgt (htS n).1.2
      have h2 : agFlux γ G (tS n) ≤ ((2 + γ) * A - B) / 2 := (htS n).2
      linarith
    linarith [hc, hfin]
  · push_neg at hcase
    obtain ⟨T, hTπ, hT2⟩ := hcase
    set T' : ℝ := (max T θ₀ + Real.pi / 2) / 2 with hT'def
    have hmax : max T θ₀ < Real.pi / 2 := max_lt hTπ hθ₀
    have hT'θ : θ₀ < T' := by rw [hT'def]; linarith [le_max_right T θ₀, hθ₀]
    have hT'π : T' < Real.pi / 2 := by rw [hT'def]; linarith [hmax]
    have hT'T : T < T' := by rw [hT'def]; linarith [le_max_left T θ₀, hTπ]
    have hpt : ∀ θ ∈ Set.Ioo T' (Real.pi / 2),
        ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ) ≤ agF γ G θ := by
      intro θ hθ
      have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have h1 : ((2 + γ) * A - B) / 2 ≤ agFlux γ G θ :=
        le_of_lt (hT2 θ ⟨lt_trans hT'T hθ.1, hθ.2⟩)
      have h2 : agFlux γ G θ * (Real.pi / 2 - θ) ^ (-1 : ℝ) = agF γ G θ := by
        rw [agFlux, agF, mul_assoc, ← Real.rpow_add hy]
        congr 1
        ring_nf
      calc ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
          ≤ agFlux γ G θ * (Real.pi / 2 - θ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le _)
        _ = agF γ G θ := h2
    have hbase : IntegrableOn (fun θ => ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ))
        (Set.Ioo T' (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono (hInt.mono_set (Set.Ioo_subset_Ioo_left hT'θ.le)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ((continuousOn_const.sub continuousOn_id).rpow_const (fun θ hθ => Or.inl ?_)).const_mul _
        have hpx : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
        exact ne_of_gt hpx
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith [hc]) (Real.rpow_nonneg (by linarith [hθ.2]) _)),
          abs_of_nonneg (agF_nonneg γ G (by linarith [hθ.2]))]
        exact hpt θ hθ
    have h2 := hbase.const_mul (2 / ((2 + γ) * A - B))
    have h3 : (fun θ : ℝ => (2 / ((2 + γ) * A - B)) *
        (((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ)))
        = fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ) := by
      funext θ
      have hne : (2 + γ) * A - B ≠ 0 := ne_of_gt hc
      field_simp
    exact not_integrableOn_sub_inv T' hT'π (by rwa [h3] at h2)

/-- The pointwise Hardy bound near `π/2`: `u(θ)² ≤ (π/2 - θ)·∫(u')²` for `u` continuous on
`[0,π/2]`, of class `C¹` on the open interval, with `u(π/2) = 0`. -/
theorem sq_le_weight_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by
  have hc0 : 0 < Real.pi / 2 := by positivity
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hderiv_cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (derivWithin u (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn_derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2)) le_rfl
    refine h1.congr (fun x hx => ?_)
    exact (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm
  have htend : Tendsto u (𝓝[<] (Real.pi / 2)) (𝓝 (u (Real.pi / 2))) := by
    have hle : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)
        ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds hc0] with y hy hyc
      exact ⟨le_of_lt hy, le_of_lt hyc⟩
    exact ((hcont.continuousWithinAt ⟨hc0.le, le_rfl⟩).tendsto).mono_left hle
  intro θ hθ
  have hθ0 : 0 < θ := by linarith [Real.pi_pos, hθ.1]
  have hθc : θ < Real.pi / 2 := hθ.2
  have hlim : Tendsto (fun t => |u t - u θ| ^ 2) (𝓝[<] (Real.pi / 2))
      (𝓝 ((u θ) ^ 2)) := by
    have h2 : Tendsto (fun t => u t - u θ) (𝓝[<] (Real.pi / 2))
        (𝓝 (u (Real.pi / 2) - u θ)) := htend.sub tendsto_const_nhds
    have h3 := h2.abs.pow 2
    rw [hπ, zero_sub, abs_neg, sq_abs] at h3
    exact h3
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioi_mem_nhds hθc] with t ht htc
  have ht1 : θ < t := ht
  have ht2 : t < Real.pi / 2 := htc
  have hθt : θ ≤ t := le_of_lt ht1
  have hsub : Set.uIcc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hθt, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
  have hsubIoc : Set.Ioc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
  have hderiv : ∀ x ∈ Set.uIcc θ t, HasDerivAt u (deriv u x) x := fun x hx =>
    (hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt_one.hasDerivAt
  have hInt1 : IntervalIntegrable (deriv u) volume θ t :=
    (hderiv_cont.mono hsub).intervalIntegrable
  have hftc : ∫ x in θ..t, deriv u x = u t - u θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
  have h1 : |u t - u θ| ≤ ∫ x in θ..t, |deriv u x| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (μ := volume) hθt
    rwa [hftc] at h
  have hfi : IntegrableOn (fun x => |deriv u x| ^ 2 * 1) (Set.Ioc θ t) := by
    simpa only [mul_one, sq_abs] using hInt.mono_set hsubIoc
  have hsi : IntegrableOn (fun _ : ℝ => (1 : ℝ)⁻¹) (Set.Ioc θ t) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hθt]
    simpa using (continuousOn_const (c := (1 : ℝ)) (s := Set.uIcc θ t)).intervalIntegrable
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
    (f := fun x => |deriv u x|) (σ := fun _ => (1 : ℝ)) hθt (fun s _ => zero_lt_one) hfi hsi
  have hc1 : (∫ x in θ..t, |deriv u x| ^ 2 * 1) = ∫ x in θ..t, (deriv u x) ^ 2 := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [mul_one, sq_abs]
  have hc2 : (∫ x in θ..t, (1 : ℝ)⁻¹) = t - θ := by
    have h : (∫ x in θ..t, (1 : ℝ)) = t - θ := by
      simpa using intervalIntegral.integral_const (1 : ℝ) (a := θ) (b := t)
    simpa [inv_one] using h
  rw [hc1, hc2] at hcs
  have hInt2 : (∫ x in θ..t, (deriv u x) ^ 2) ≤ A := by
    rw [hA, intervalIntegral.integral_of_le hθt, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hsubIoc ⟨hx.1, le_of_lt hx.2⟩))
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have h2 : |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have htθ : 0 ≤ t - θ := sub_nonneg.mpr hθt
  have hcle : t - θ ≤ Real.pi / 2 - θ := by linarith
  have h3 : (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) ≤ A * (Real.pi / 2 - θ) :=
    calc (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ)
        ≤ A * (t - θ) := mul_le_mul_of_nonneg_right hInt2 htθ
      _ ≤ A * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcle hA0
  calc |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 := h2
    _ ≤ (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) := hcs
    _ ≤ A * (Real.pi / 2 - θ) := h3
    _ = (Real.pi / 2 - θ) * A := by ring

/-- Integrability of `u² (π/2-θ)^{-γ}` near `π/2`, `1 ≤ γ < 2`. -/
theorem integrableOn_sq_mul_sub_rpow (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hkey := sq_le_weight_mul u hu hcont hπ hInt
  set maj : ℝ → ℝ := fun θ => A * (Real.pi / 2 - θ) ^ (1 - γ) with hmaj
  have hmajInt : IntegrableOn maj (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [hmaj]
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - γ))
        volume (Real.pi / 4) (Real.pi / 2) := by
      have h := IntervalIntegrable.comp_sub_left (f := fun x : ℝ => x ^ (1 - γ)) h1.symm (Real.pi / 2)
      have e1 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      have e2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
      rw [e1, e2] at h
      exact h
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])] at h2
    exact (h2.mono_set Set.Ioo_subset_Ioc_self).const_mul A
  refine Integrable.mono' hmajInt ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ((hcont.mono ?_).pow 2).mul
      ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
        have hpx : (0:ℝ) < Real.pi / 2 - x := by linarith [hx.2]
        simpa using ne_of_gt hpx)))
    intro x hx
    exact ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), hx.2.le⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
      have := hkey θ hθ
      rwa [← hA] at this
    have hrw : Real.rpow (Real.pi / 2 - θ) (1 - γ)
        = (Real.pi / 2 - θ) * Real.rpow (Real.pi / 2 - θ) (-γ) := by
      have h := Real.rpow_add hy 1 (-γ)
      rw [show (1 : ℝ) + (-γ) = 1 - γ by ring, Real.rpow_one] at h
      exact h
    calc ‖(u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)‖
        = (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _))]
      _ ≤ ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le _)
      _ = maj θ := by
          rw [hmaj]
          change (Real.pi / 2 - θ) * A * Real.rpow (Real.pi / 2 - θ) (-γ)
            = A * Real.rpow (Real.pi / 2 - θ) (1 - γ)
          rw [show (Real.pi / 2 - θ) * A * Real.rpow (Real.pi / 2 - θ) (-γ)
              = A * ((Real.pi / 2 - θ) * Real.rpow (Real.pi / 2 - θ) (-γ)) by ring, ← hrw]

theorem hardyUDivY (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by
  have hc0 : 0 < Real.pi / 2 := by positivity
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hderiv_cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (derivWithin u (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn_derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2)) le_rfl
    refine h1.congr (fun x hx => ?_)
    exact (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm
  have htend : Tendsto u (𝓝[<] (Real.pi / 2)) (𝓝 (u (Real.pi / 2))) := by
    have hle : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)
        ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds hc0] with y hy hyc
      exact ⟨le_of_lt hy, le_of_lt hyc⟩
    exact ((hcont.continuousWithinAt ⟨hc0.le, le_rfl⟩).tendsto).mono_left hle
  -- the pointwise Hardy bound
  have hkey : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθc : θ < Real.pi / 2 := hθ.2
    have hlim : Tendsto (fun t => |u t - u θ| ^ 2) (𝓝[<] (Real.pi / 2))
        (𝓝 ((u θ) ^ 2)) := by
      have h2 : Tendsto (fun t => u t - u θ) (𝓝[<] (Real.pi / 2))
          (𝓝 (u (Real.pi / 2) - u θ)) := htend.sub tendsto_const_nhds
      have h3 := h2.abs.pow 2
      rw [hπ, zero_sub, abs_neg, sq_abs] at h3
      exact h3
    refine le_of_tendsto hlim ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds hθc] with t ht htc
    have ht1 : θ < t := ht
    have ht2 : t < Real.pi / 2 := htc
    have hθt : θ ≤ t := le_of_lt ht1
    have hsub : Set.uIcc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hθt, Set.mem_Icc] at hx
      exact ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
    have hsubIoc : Set.Ioc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
      ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
    have hderiv : ∀ x ∈ Set.uIcc θ t, HasDerivAt u (deriv u x) x := fun x hx =>
      (hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt_one.hasDerivAt
    have hInt1 : IntervalIntegrable (deriv u) volume θ t :=
      (hderiv_cont.mono hsub).intervalIntegrable
    have hftc : ∫ x in θ..t, deriv u x = u t - u θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
    have h1 : |u t - u θ| ≤ ∫ x in θ..t, |deriv u x| := by
      have h := intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (μ := volume) hθt
      rwa [hftc] at h
    have hfi : IntegrableOn (fun x => |deriv u x| ^ 2 * 1) (Set.Ioc θ t) := by
      simpa only [mul_one, sq_abs] using hInt.mono_set hsubIoc
    have hsi : IntegrableOn (fun _ : ℝ => (1 : ℝ)⁻¹) (Set.Ioc θ t) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hθt]
      simpa using (continuousOn_const (c := (1 : ℝ)) (s := Set.uIcc θ t)).intervalIntegrable
    have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
      (f := fun x => |deriv u x|) (σ := fun _ => (1 : ℝ)) hθt (fun s _ => zero_lt_one) hfi hsi
    have hc1 : (∫ x in θ..t, |deriv u x| ^ 2 * 1) = ∫ x in θ..t, (deriv u x) ^ 2 := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [mul_one, sq_abs]
    have hc2 : (∫ x in θ..t, (1 : ℝ)⁻¹) = t - θ := by
      have h : (∫ x in θ..t, (1 : ℝ)) = t - θ := by
        simpa using intervalIntegral.integral_const (1 : ℝ) (a := θ) (b := t)
      simpa [inv_one] using h
    rw [hc1, hc2] at hcs
    have hInt2 : (∫ x in θ..t, (deriv u x) ^ 2) ≤ A := by
      rw [hA, intervalIntegral.integral_of_le hθt, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (Filter.Eventually.of_forall (fun x hx => hsubIoc ⟨hx.1, le_of_lt hx.2⟩))
    have h2 : |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    have htθ : 0 ≤ t - θ := sub_nonneg.mpr hθt
    have hcle : t - θ ≤ Real.pi / 2 - θ := by linarith
    have h3 : (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) ≤ A * (Real.pi / 2 - θ) :=
      calc (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ)
          ≤ A * (t - θ) := mul_le_mul_of_nonneg_right hInt2 htθ
        _ ≤ A * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcle hA0
    calc |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 := h2
      _ ≤ (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) := hcs
      _ ≤ A * (Real.pi / 2 - θ) := h3
      _ = (Real.pi / 2 - θ) * A := by ring
  -- the value of the weight integral
  have hInt' : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ))
      = (Real.pi / 4) ^ (2 - γ) / (2 - γ) := by
    have h1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ))
        = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ) := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [h1, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - γ)) (Real.pi / 2)]
    have hsubv : Real.pi / 2 - Real.pi / 2 = 0 := by ring
    have hsubv2 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [hsubv, hsubv2]
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        HasDerivAt (fun y : ℝ => y ^ (2 - γ) / (2 - γ)) (x ^ (1 - γ)) x := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      have h1 := (Real.hasDerivAt_rpow_const (x := x) (p := 2 - γ) (Or.inl hx0)).div_const (2 - γ)
      have h2 : (2 - γ) * x ^ (2 - γ - 1) / (2 - γ) = x ^ (1 - γ) := by
        rw [show (2:ℝ) - γ - 1 = 1 - γ by ring,
          mul_div_cancel_left₀ _ (by linarith : (2:ℝ) - γ ≠ 0)]
      rw [← h2]
      exact h1
    have hcont' : ContinuousOn (fun y : ℝ => y ^ (2 - γ) / (2 - γ))
        (Set.Icc 0 (Real.pi / 4)) :=
      (continuousOn_id.rpow_const (fun y hy => Or.inr (by linarith))).div_const _
    have hint' : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0)
      (b := Real.pi / 4) (by positivity) hcont' hderiv hint'
    rw [hFTC]
    have hzero : (0 : ℝ) ^ (2 - γ) / (2 - γ) = 0 := by
      rw [Real.zero_rpow (by linarith)]
      simp
    rw [hzero]
    ring
  -- bound the weight integral
  have hbnd : (Real.pi / 4) ^ (2 - γ) / (2 - γ) ≤ 2 := by
    have h1 : (Real.pi / 4) ^ (2 - γ) ≤ (1:ℝ) := by
      have hπ4 : (0:ℝ) < Real.pi / 4 := by positivity
      have hle1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
      have h2 : (1/2 : ℝ) ≤ 2 - γ := by linarith
      calc (Real.pi / 4) ^ (2 - γ) ≤ (Real.pi / 4) ^ (1/2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hπ4 hle1 h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hπ4) hle1 (by norm_num)
    have h3 : (0:ℝ) < 2 - γ := by linarith
    rw [div_le_iff₀ h3]
    nlinarith [h1, h3, hγ2]
  have hIntW : IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - γ))
        volume (Real.pi / 4) (Real.pi / 2) := by
      have h := IntervalIntegrable.comp_sub_left (f := fun x : ℝ => x ^ (1 - γ)) h1.symm (Real.pi / 2)
      have e1 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      have e2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
      rw [e1, e2] at h
      exact h
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])] at h2
    exact h2.mono_set Set.Ioo_subset_Ioc_self
  have hmaj : IntegrableOn (fun θ => A * (Real.pi / 2 - θ) ^ (1 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hIntW.const_mul A
  -- pointwise comparison with the majorant
  have hpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)
        ≤ ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) :=
      mul_le_mul_of_nonneg_right (hkey θ hθ') (Real.rpow_nonneg hy.le _)
    have h2 : ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)
        = A * (Real.pi / 2 - θ) ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = 1 + (-γ) by ring, Real.rpow_add hy, Real.rpow_one]
      ring
    linarith [h1, h2]
  have hLHSint : IntegrableOn (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine Integrable.mono hmaj ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hcont.mono ?_).pow 2).mul
        ((continuousOn_const.sub continuousOn_id).rpow_const
          (fun x hx => Or.inl (by
            have hpx : 0 < Real.pi / 2 - x := by linarith [hx.2]
            exact ne_of_gt hpx)))
      intro x hx
      exact ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), hx.2.le⟩
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hfnn : 0 ≤ (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
      have hgnn : 0 ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) :=
        mul_nonneg hA0 (Real.rpow_nonneg (by linarith [hθ.2]) _)
      calc ‖(u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)‖ = (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
        _ ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) := hpt θ hθ
        _ = ‖A * (Real.pi / 2 - θ) ^ (1 - γ)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
  have hmain : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), A * (Real.pi / 2 - θ) ^ (1 - γ) :=
    MeasureTheory.integral_mono_ae hLHSint hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact hpt θ hθ)
  rw [MeasureTheory.integral_const_mul] at hmain
  calc (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ A * (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ)) := hmain
    _ = A * ((Real.pi / 4) ^ (2 - γ) / (2 - γ)) := by rw [hInt']
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left hbnd hA0
    _ = 2 * A := by ring
    _ = 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by rw [hA]

theorem vTwoW4NIdents (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) θ
        = (Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
          + 2 * Real.cos θ * Real.sin θ * u θ)
    ∧ ContDiffOn ℝ 1
        (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hCpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ :=
    fun θ hθ => Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  -- ## Conjunct 1
  have hconj1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ := by
    intro θ hθ
    have hC := (hCpos θ hθ).ne'
    have h1 := (Work.FTS.EllipticEst.remov.slice5_v_rel_pure u hu θ hθ).1
    have h2 := Work.FTS.EllipticEst.remov.slice5_v_rel_one u hu θ hθ
    have ha : Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
        - deriv (deriv u) θ - 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - Real.cos θ * (u θ / Real.cos θ) = 0 := by linarith [h1]
    have hb : Real.cos θ * deriv (fun t => u t / Real.cos t) θ
        - deriv u θ - Real.sin θ * (u θ / Real.cos θ) = 0 := by linarith [h2]
    have hc : Real.cos θ * (u θ / Real.cos θ) - u θ = 0 := by
      field_simp
      ring
    have hCv : Real.cos θ * deriv (fun t => u t / Real.cos t) θ
        = deriv u θ + Real.sin θ * (u θ / Real.cos θ) := by linarith [h2]
    have hCu : Real.cos θ * (u θ / Real.cos θ) = u θ := by field_simp
    have hCv2 : Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
        = deriv (deriv u) θ + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          + Real.cos θ * (u θ / Real.cos θ) := by linarith [h1]
    have step3 : (Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ
        = Real.cos θ * deriv u θ + Real.sin θ * u θ := by
      rw [show (Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ
          = Real.cos θ * (Real.cos θ * deriv (fun t => u t / Real.cos t) θ) by ring, hCv,
        mul_add]
      rw [show Real.cos θ * (Real.sin θ * (u θ / Real.cos θ)) = Real.sin θ * (Real.cos θ * (u θ / Real.cos θ)) by ring,
        hCu]
    rw [show (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) by ring,
      hCv2]
    rw [show (Real.cos θ) ^ 2 * (deriv (deriv u) θ + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          + Real.cos θ * (u θ / Real.cos θ))
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ
          + 2 * Real.sin θ * ((Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ)
          + (Real.cos θ) ^ 2 * (Real.cos θ * (u θ / Real.cos θ)) by ring]
    rw [step3, hCu]
    ring
  refine ⟨hconj1, ?_, ?_⟩
  · intro θ hθ
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hev : (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ')
        =ᶠ[𝓝 θ] fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ'
            + 2 * Real.cos θ' * Real.sin θ' * deriv u θ'
            + ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ' := by
      filter_upwards [hmem] with t ht
      exact hconj1 t ht
    have h1 : ContDiffOn ℝ 3 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 2 (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h1d : DifferentiableAt ℝ (deriv u) θ :=
      (h1.differentiableOn (by norm_num)).differentiableAt hmem
    have h2d : DifferentiableAt ℝ (deriv (deriv u)) θ :=
      (h2.differentiableOn (by norm_num)).differentiableAt hmem
    have hud : DifferentiableAt ℝ u θ :=
      (hu.differentiableOn (by norm_num)).differentiableAt hmem
    have hd1 : HasDerivAt (fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ')
        ((Real.cos θ) ^ 2 * deriv (deriv (deriv u)) θ
          + (2 * Real.cos θ * (-Real.sin θ)) * deriv (deriv u) θ) θ := by
      refine (((Real.hasDerivAt_cos θ).pow 2).mul h2d.hasDerivAt).congr_deriv ?_
      simp only [Pi.pow_apply]
      ring
    have hd2 : HasDerivAt (fun θ' => 2 * Real.cos θ' * Real.sin θ' * deriv u θ')
        (2 * (Real.cos θ * Real.cos θ - Real.sin θ * Real.sin θ) * deriv u θ
          + (2 * Real.cos θ * Real.sin θ) * deriv (deriv u) θ) θ := by
      refine ((((Real.hasDerivAt_cos θ).const_mul 2).mul (Real.hasDerivAt_sin θ)).mul
        h1d.hasDerivAt).congr_deriv ?_
      simp only [Pi.mul_apply]
      ring
    have hd3 : HasDerivAt (fun θ' => ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ')
        ((2 * Real.cos θ * Real.sin θ) * u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * deriv u θ) θ := by
      refine ((((Real.hasDerivAt_cos θ).pow 2).add
        (((Real.hasDerivAt_sin θ).pow 2).const_mul 2)).mul hud.hasDerivAt).congr_deriv ?_
      simp only [Pi.pow_apply, Pi.add_apply]
      ring
    have hfun : (fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ'
          + 2 * Real.cos θ' * Real.sin θ' * deriv u θ'
          + ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ')
        = ((fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ')
            + fun θ' => 2 * Real.cos θ' * Real.sin θ' * deriv u θ')
          + fun θ' => ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ' := by
      funext x
      simp only [Pi.add_apply]
    rw [hev.deriv_eq, hfun, ((hd1.add hd2).add hd3).deriv]
    ring
  · -- ## Conjunct 3
    have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun x hx => ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
    have hv : ContDiffOn ℝ 4 (fun t => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.div Real.contDiff_cos.contDiffOn (fun t ht => (hCpos t ht).ne')
    have hv1 : ContDiffOn ℝ 3 (deriv (fun t => u t / Real.cos t)) (Set.Ioo 0 (Real.pi / 2)) :=
      hv.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hv2 : ContDiffOn ℝ 2 (deriv (deriv (fun t => u t / Real.cos t)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hv1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hC3 : ContDiffOn ℝ 1 (fun θ : ℝ => (Real.cos θ) ^ 3) (Set.Ioo 0 (Real.pi / 2)) := by
      have h : ContDiffOn ℝ 1 (Real.cos ^ 3) (Set.Ioo 0 (Real.pi / 2)) :=
        ((Real.contDiff_cos (n := 1)) |>.contDiffOn).pow 3
      exact h.congr (fun x hx => by simp only [Pi.pow_apply])
    have hN : ContDiffOn ℝ 1
        (fun θ : ℝ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine ((hC3.mul (hv2.of_le (by norm_num))).congr ?_)
      intro x hx
      simp only [Pi.mul_apply]
    exact hN.mono hsub

lemma near_weight_id (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8
      = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ) := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hid1 : (2 * Real.sin θ * Real.cos θ) ^ (4 - γ)
      = (2 * Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (4 - γ) :=
    Real.mul_rpow (by positivity) hc.le
  have hid2 : (2 * Real.sin θ) ^ (4 - γ) = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) :=
    Real.mul_rpow (by norm_num) hSp.le
  have hden : (Real.cos θ) ^ 8 = (Real.cos θ) ^ (8 : ℝ) := (Real.rpow_natCast (Real.cos θ) 8).symm
  rw [Real.sin_two_mul, hid1, hid2, hden,
    show (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (4 - γ) / (Real.cos θ) ^ (8 : ℝ)
        = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ)
          * ((Real.cos θ) ^ (4 - γ) / (Real.cos θ) ^ (8 : ℝ)) by ring,
    ← Real.rpow_sub hc, show (4 : ℝ) - γ - 8 = -4 - γ by ring]

lemma near_weight_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8
      ≤ 512 * (Real.pi / 2 - θ) ^ (-4 - γ) := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hCl : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := two_div_pi_mul_sub_le_cos hθ0
  have hhalf : (1/2 : ℝ) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have hpi : (1/2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith [Real.pi_lt_four]
    nlinarith [hCl, hpi, hy]
  rw [near_weight_id γ hθ]
  have hS1 : (Real.sin θ) ^ (4 - γ) ≤ 1 :=
    Real.rpow_le_one hSp.le (Real.sin_le_one _) (by linarith)
  have h2g : (2 : ℝ) ^ (4 - γ) ≤ 8 := by
    have h1 : (2 : ℝ) ^ (4 - γ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    linarith [h1, h3]
  have hCb : (Real.cos θ) ^ (-4 - γ) ≤ (2 : ℝ) ^ (4 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ) := by
    have h1 : (Real.cos θ) ^ (-4 - γ) ≤ ((1/2 : ℝ) * (Real.pi / 2 - θ)) ^ (-4 - γ) :=
      Real.rpow_le_rpow_of_nonpos (z := -4 - γ) (by positivity) hhalf (by linarith)
    have h2 : ((1/2 : ℝ) * (Real.pi / 2 - θ)) ^ (-4 - γ)
        = (1/2 : ℝ) ^ (-4 - γ) * (Real.pi / 2 - θ) ^ (-4 - γ) :=
      Real.mul_rpow (by norm_num) hy.le
    have h3 : (1/2 : ℝ) ^ (-4 - γ) = (2 : ℝ) ^ (4 + γ) := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
        show (-4 : ℝ) - γ = -(4 + γ) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_inv _
    rw [h2, h3] at h1
    exact h1
  have hpi : (2 : ℝ) ^ (4 + γ) ≤ 64 := by
    have h1 : (2 : ℝ) ^ (4 + γ) ≤ (2 : ℝ) ^ (6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
    linarith [h1, h3]
  have hSnn : 0 ≤ (Real.sin θ) ^ (4 - γ) := Real.rpow_nonneg hSp.le _
  have hCnn : 0 ≤ (Real.cos θ) ^ (-4 - γ) := Real.rpow_nonneg hc.le _
  have h2nn : 0 ≤ (2 : ℝ) ^ (4 - γ) := Real.rpow_nonneg (by norm_num) _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-4 - γ) := Real.rpow_nonneg hy.le _
  have h64 : 0 ≤ (2 : ℝ) ^ (4 + γ) := Real.rpow_nonneg (by norm_num) _
  calc (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ)
      ≤ 8 * 1 * ((2 : ℝ) ^ (4 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
        have h1 : (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) ≤ 8 * 1 :=
          mul_le_mul h2g hS1 hSnn (by norm_num)
        exact mul_le_mul h1 hCb hCnn (by positivity)
    _ ≤ 512 * (Real.pi / 2 - θ) ^ (-4 - γ) := by
        have h1 := mul_le_mul_of_nonneg_right hpi hyn
        linarith [h1]

lemma near_weight_ge (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8 := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hCu : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_sub hθ0
  have hSge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
      (by linarith [Real.pi_pos]) hθ.2.le hθ.1.le
    rwa [Real.sin_pi_div_four] at h
  have hCge : (Real.pi / 2 - θ) ^ (-4 - γ) ≤ (Real.cos θ) ^ (-4 - γ) :=
    Real.rpow_le_rpow_of_nonpos (z := -4 - γ) hc hCu (by linarith)
  have h2S : Real.sqrt 2 ≤ (2 : ℝ) * Real.sin θ := by nlinarith [hSge]
  have hkey : 1 ≤ (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hSp.le]
    calc (1 : ℝ) = (Real.sqrt 2) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (Real.sqrt 2) ^ (4 - γ) :=
          Real.rpow_le_rpow_of_exponent_le (by
            rw [← Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num) (by linarith)
      _ ≤ ((2 : ℝ) * Real.sin θ) ^ (4 - γ) :=
          Real.rpow_le_rpow (z := 4 - γ) (by norm_num) h2S (by linarith)
  have hCnn : 0 ≤ (Real.cos θ) ^ (-4 - γ) := Real.rpow_nonneg hc.le _
  rw [near_weight_id γ hθ]
  calc (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ (Real.cos θ) ^ (-4 - γ) := hCge
    _ = 1 * (Real.cos θ) ^ (-4 - γ) := by ring
    _ ≤ ((2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ)) * (Real.cos θ) ^ (-4 - γ) :=
        mul_le_mul_of_nonneg_right hkey hCnn
    _ = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ) := by ring

/-- `cos θ ≥ √2/2` on `(0,π/4]`. -/
lemma half_le_cos_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (1 : ℝ) / 2 ≤ (Real.cos θ) ^ 2 := by
  have h1 : Real.cos θ ≥ Real.cos (Real.pi / 4) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [hθ.2, Real.pi_pos]) hθ.2.le
  rw [Real.cos_pi_div_four] at h1
  have h2 : (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h2]
  exact pow_le_pow_left₀ (by positivity) h1 2

/-! ### Three weight comparisons on the near field `(π/4, π/2)` -/

/-- On the near field, `cos⁴θ · (π/2-θ)^{-2-γ} ≤ 2 (sin 2θ)^{2-γ}`. -/
lemma cos4_mul_sub_rpow_le_two (θ γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ)
    (hCy : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ)
    (hCS : Real.cos θ ≤ Real.sin (2 * θ)) (hs : 0 < Real.sin (2 * θ)) :
    (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc4 : (Real.cos θ) ^ 4 ≤ (Real.pi / 2 - θ) ^ 4 := pow_le_pow_left₀ hc.le hCu 4
  have hy4 : (Real.pi / 2 - θ) ^ 4 = (Real.pi / 2 - θ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (2 - γ) := by
    rw [hy4, ← Real.rpow_add hy]
    congr 1
    ring
  have hstep3 : (Real.pi / 2 - θ) ^ (2 - γ) ≤ (Real.pi / 2 * Real.cos θ) ^ (2 - γ) :=
    Real.rpow_le_rpow hyl hCy (by linarith)
  have hstep4 : (Real.pi / 2 * Real.cos θ) ^ (2 - γ)
      = (Real.pi / 2) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) :=
    Real.mul_rpow (by linarith [Real.pi_pos]) hc.le
  have h4 : (Real.pi / 2) ^ (2 - γ) ≤ 2 := by
    have h5 : (Real.pi / 2) ^ (2 - γ) ≤ (2 : ℝ) ^ (2 - γ) :=
      Real.rpow_le_rpow (by linarith [Real.pi_pos]) (by linarith [Real.pi_lt_four]) (by linarith)
    have h6 : (2 : ℝ) ^ (2 - γ) ≤ 2 := by
      have h7 : (2 : ℝ) ^ (2 - γ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rwa [Real.rpow_one] at h7
    linarith
  have h5 : (Real.cos θ) ^ (2 - γ) ≤ (Real.sin (2 * θ)) ^ (2 - γ) :=
    Real.rpow_le_rpow hc.le hCS (by linarith)
  have hstep5 : (Real.pi / 2) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ)
      ≤ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    mul_le_mul h4 h5 (Real.rpow_nonneg hc.le _) (by norm_num)
  linarith [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- On the near field, `cos⁴θ · (π/2-θ)^{-2-γ} ≤ 1`. -/
lemma cos4_mul_sub_rpow_le_one (θ γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ) (hy1 : Real.pi / 2 - θ ≤ 1) :
    (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ 1 := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc4 : (Real.cos θ) ^ 4 ≤ (Real.pi / 2 - θ) ^ 4 := pow_le_pow_left₀ hc.le hCu 4
  have hy4 : (Real.pi / 2 - θ) ^ 4 = (Real.pi / 2 - θ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (2 - γ) := by
    rw [hy4, ← Real.rpow_add hy]
    congr 1
    ring
  have hstep3 : (Real.pi / 2 - θ) ^ (2 - γ) ≤ 1 := Real.rpow_le_one hyl hy1 (by linarith)
  linarith [hstep1, hstep2, hstep3]

/-- On the near field, `cos²θ · (π/2-θ)^{-2-γ} ≤ (π/2-θ)^{-γ}`. -/
lemma cos2_mul_sub_rpow_le (θ γ : ℝ)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ) :
    (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ (Real.pi / 2 - θ) ^ (-γ) := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc2 : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := pow_le_pow_left₀ hc.le hCu 2
  have hy2 : (Real.pi / 2 - θ) ^ 2 = (Real.pi / 2 - θ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (-γ) := by
    rw [hy2, ← Real.rpow_add hy]
    congr 1
    ring
  linarith [hstep1, hstep2]

/-- The global identity `(v'')²·σ₄/cos²θ = (cos³θ v'')²·σ₄/cos⁸θ`. -/
lemma F_eq_N (u : ℝ → ℝ) (γ : ℝ) (θ : ℝ) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      = ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8) := by
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · field_simp

/-- The far-field pointwise bound, with the weight `sEta` absorbed in the `u''`-term. -/
lemma far_F_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      ≤ 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hc2 : (1 : ℝ) / 2 ≤ (Real.cos θ) ^ 2 := half_le_cos_sq hθ
  have hsEta : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_Ioo hθ'
  have hN1 := (vTwoW4NIdents u hu4).1 θ hθ'
  have hw : (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8 ≤ 16 := by
    have h1 : (Real.sin (2 * θ)) ^ (4 - γ) ≤ 1 :=
      Real.rpow_le_one hsnn (Real.sin_le_one _) (by linarith)
    have h2 : (1 : ℝ) / 16 ≤ (Real.cos θ) ^ 8 := by
      have h3 : ((1 : ℝ) / 2) ^ 4 ≤ ((Real.cos θ) ^ 2) ^ 4 := pow_le_pow_left₀ (by norm_num) hc2 4
      calc (1 : ℝ) / 16 = ((1 : ℝ) / 2) ^ 4 := by norm_num
        _ ≤ ((Real.cos θ) ^ 2) ^ 4 := h3
        _ = (Real.cos θ) ^ 8 := by ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.cos θ) ^ 8)]
    linarith [h1, h2]
  rw [F_eq_N u γ θ]
  have hN2 : ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
      ≤ 3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2) := by
    rw [hN1]
    have hsq : ((Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2
        ≤ 3 * (((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2
          + (2 * Real.cos θ * Real.sin θ * deriv u θ) ^ 2
          + (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2) := by
      nlinarith [sq_nonneg ((Real.cos θ) ^ 2 * deriv (deriv u) θ
            - 2 * Real.cos θ * Real.sin θ * deriv u θ),
        sq_nonneg (2 * Real.cos θ * Real.sin θ * deriv u θ
            - ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ),
        sq_nonneg (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ
            - (Real.cos θ) ^ 2 * deriv (deriv u) θ)]
    have hC2 : (Real.cos θ) ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
    have hCS : (2 * Real.cos θ * Real.sin θ) ^ 2 ≤ 1 := by
      nlinarith [Real.cos_sq_add_sin_sq θ, hC2, Real.sin_sq_le_one θ]
    have hCoef : ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) ^ 2 ≤ 9 := by
      have h1 : (Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2 ≤ 3 := by
        nlinarith [Real.cos_sq_add_sin_sq θ, hC2, Real.sin_sq_le_one θ]
      nlinarith [h1, show (0 : ℝ) ≤ (Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2 by positivity]
    have ha : ((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2 ≤ (deriv (deriv u) θ) ^ 2 * 1 := by
      have hC4 : ((Real.cos θ) ^ 2) ^ 2 ≤ 1 := by nlinarith [hC2, sq_nonneg ((Real.cos θ) ^ 2)]
      calc ((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2
          = ((Real.cos θ) ^ 2) ^ 2 * (deriv (deriv u) θ) ^ 2 := by ring
        _ ≤ 1 * (deriv (deriv u) θ) ^ 2 := mul_le_mul_of_nonneg_right hC4 (sq_nonneg _)
        _ = (deriv (deriv u) θ) ^ 2 * 1 := by ring
    have hb : (2 * Real.cos θ * Real.sin θ * deriv u θ) ^ 2 ≤ 4 * (deriv u θ) ^ 2 := by
      nlinarith [hCS, sq_nonneg (deriv u θ)]
    have hcc : (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2 ≤ 9 * (u θ) ^ 2 := by
      nlinarith [hCoef, sq_nonneg (u θ)]
    linarith [hsq, ha, hb, hcc]
  have hstep : ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8)
      ≤ (3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2)) * 16 := by
    refine mul_le_mul hN2 hw (by positivity) (by positivity)
  have hbig : (3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2)) * 16
      ≤ 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 := by
    have h1 : (deriv (deriv u) θ) ^ 2 ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      nlinarith [sq_nonneg (deriv (deriv u) θ), hsEta]
    nlinarith [h1, sq_nonneg (deriv u θ), sq_nonneg (u θ), hsEta]
  linarith [hstep, hbig]

/-- Near-field comparison of the left-hand integrand with the Agmon weight. -/
lemma near_F_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      ≤ 512 * (((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
  rw [F_eq_N u γ θ]
  have hw := near_weight_le γ hγ1 hγ2 hθ
  have hnn : 0 ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 :=
    sq_nonneg _
  calc ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8)
      ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (512 * (Real.pi / 2 - θ) ^ (-4 - γ)) := mul_le_mul_of_nonneg_left hw hnn
    _ = 512 * (((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) := by ring

/-- Near-field bound for `(deriv N)²` with the Agmon weight. -/
lemma near_Nd_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (deriv (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ') θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := cos_pos_of_mem_Ioo hθ'
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hy1 : Real.pi / 2 - θ ≤ 1 := by linarith [Real.pi_lt_four, hθ.1]
  have hCu : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_sub hθ'
  have hCy : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have h := two_div_pi_mul_sub_le_cos hθ'
    have h2 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) ≤ Real.pi / 2 * Real.cos θ :=
      mul_le_mul_of_nonneg_left h (by linarith [Real.pi_pos])
    have h3 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h2, h3]
  have hSge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
      (by linarith [Real.pi_pos]) hθ.2.le hθ.1.le
    rwa [Real.sin_pi_div_four] at h
  have hCS : Real.cos θ ≤ Real.sin (2 * θ) := by
    have h1 : (1:ℝ) ≤ 2 * Real.sin θ := by
      have h2 : Real.sqrt 2 ≤ 2 * Real.sin θ := by nlinarith [hSge, Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)]
      nlinarith [h2, Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)]
    rw [Real.sin_two_mul]
    nlinarith [h1, hc]
  set C4 : ℝ := (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) with hC4def
  set C2 : ℝ := (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) with hC2def
  set S2 : ℝ := (Real.sin (2 * θ)) ^ (2 - γ) with hS2def
  set Y : ℝ := (Real.pi / 2 - θ) ^ (-γ) with hYdef
  have hkey1 : C4 ≤ 2 * S2 :=
    cos4_mul_sub_rpow_le_two θ γ hγ1 hγ2 hc hy hCu hCy hCS hs
  have hkey2 : C4 ≤ 1 := cos4_mul_sub_rpow_le_one θ γ hγ1 hγ2 hc hy hCu hy1
  have hkey3 : C2 ≤ Y := cos2_mul_sub_rpow_le θ γ hc hy hCu
  have hy2g : 0 ≤ (Real.pi / 2 - θ) ^ (-2 - γ) := Real.rpow_nonneg hyl _
  rw [show (deriv (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ') θ)
      = (Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ from (vTwoW4NIdents u hu4).2.1 θ hθ']
  have hsq : ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ) ^ 2
      ≤ 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        + 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 := by
    nlinarith [sq_nonneg ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
      - 2 * Real.cos θ * Real.sin θ * u θ)]
  have hsqm : ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
          * (Real.pi / 2 - θ) ^ (-2 - γ)
        + 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) := by
    have := mul_le_mul_of_nonneg_right hsq hy2g
    linarith [this]
  have hA : 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * S2) + 36 * (deriv u θ) ^ 2 := by
    have e1 : 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      = 2 * C4 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2 := by
      rw [hC4def]
      ring
    rw [e1]
    have hC4nn : 0 ≤ C4 := by rw [hC4def]; positivity
    have h3u : (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2
        ≤ 2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2) := by
      nlinarith [sq_nonneg (deriv (deriv (deriv u)) θ - 3 * deriv u θ)]
    have hstep : 2 * C4 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2
        ≤ 2 * C4 * (2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2)) :=
      mul_le_mul_of_nonneg_left h3u (by linarith)
    have hfin : 2 * C4 * (2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2))
        ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * S2) + 36 * (deriv u θ) ^ 2 := by
      have h1 : 4 * C4 * (deriv (deriv (deriv u)) θ) ^ 2
          ≤ 8 * S2 * (deriv (deriv (deriv u)) θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hkey1]) (sq_nonneg _)
      have h2 : 36 * C4 * (deriv u θ) ^ 2 ≤ 36 * (deriv u θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hkey2]) (sq_nonneg _)
      nlinarith [h1, h2]
    linarith [hstep, hfin]
  have hB : 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((u θ) ^ 2 * Y) := by
    have e1 : 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = 8 * C2 * ((Real.sin θ) ^ 2 * (u θ) ^ 2) := by
      rw [hC2def]
      ring
    rw [e1]
    have hs1 : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hu2 : 0 ≤ (u θ) ^ 2 := sq_nonneg _
    calc 8 * C2 * ((Real.sin θ) ^ 2 * (u θ) ^ 2)
        ≤ 8 * C2 * (1 * (u θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs1 hu2) (by positivity)
      _ = 8 * (C2 * (u θ) ^ 2) := by ring
      _ ≤ 8 * (Y * (u θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey3 hu2) (by norm_num)
      _ = 8 * ((u θ) ^ 2 * Y) := by ring
  linarith [hsqm, hA, hB, sq_nonneg (deriv u θ)]

/-! ### Integrability of the Agmon integrands on the near field -/

/-- `N² y^{-4-γ}` (`N = cos³θ v''`) is integrable on the near field. -/
lemma integrableOn_agF_near (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hIntF : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.pi / 2 - θ) ^ (-4 - γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hs
  have hae : (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
      =ᵐ[volume.restrict s]
      (fun θ => (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
        + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (vTwoW4NIdents u hu4).1 θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ) (volume.restrict s) :=
    (Real.continuous_cos.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ) (volume.restrict s) :=
    (Real.continuous_sin.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hcc : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ) ^ 2) (volume.restrict s) := hcos.pow 2
  have hss : AEStronglyMeasurable (fun θ : ℝ => (Real.sin θ) ^ 2) (volume.restrict s) := hsin.pow 2
  have hu : AEStronglyMeasurable u (volume.restrict s) :=
    (hu4.continuousOn.mono (by
      intro x hx; exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)).aestronglyMeasurable measurableSet_Ioo
  have hdu : AEStronglyMeasurable (deriv u) (volume.restrict s) :=
    (measurable_deriv u).aestronglyMeasurable
  have hddu : AEStronglyMeasurable (deriv (deriv u)) (volume.restrict s) :=
    (measurable_deriv (deriv u)).aestronglyMeasurable
  have hr1 : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (deriv u) θ)
      (volume.restrict s) := hcc.mul hddu
  have hr2 : AEStronglyMeasurable (fun θ : ℝ => 2 * Real.cos θ * Real.sin θ * deriv u θ)
      (volume.restrict s) := ((hcos.const_mul 2).mul hsin).mul hdu
  have hr3 : AEStronglyMeasurable (fun θ : ℝ => ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ)
      (volume.restrict s) := (hcc.add (hss.const_mul 2)).mul hu
  have hrs : AEStronglyMeasurable
      (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
        + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) (volume.restrict s) := (hr1.add hr2).add hr3
  have hN : AEStronglyMeasurable
      (fun θ : ℝ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
      (volume.restrict s) := (aestronglyMeasurable_congr hae).mpr hrs
  have hY : AEStronglyMeasurable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-4 - γ)) (volume.restrict s) :=
    ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
      show ((Real.pi : ℝ) / 2 - x) ≠ 0
      linarith [hx.2]))).aestronglyMeasurable measurableSet_Ioo
  have hagF : AEStronglyMeasurable
      (fun θ : ℝ => ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) (volume.restrict s) := (hN.pow 2).mul hY
  refine Integrable.mono' hIntF hagF ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hN2 : 0 ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 := sq_nonneg _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-4 - γ) := Real.rpow_nonneg (by linarith [hθ.2]) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hN2 hyn)]
  calc ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8) :=
        mul_le_mul_of_nonneg_left (near_weight_ge γ hγ1 hγ2 hθ) hN2
    _ = (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2) := (F_eq_N u γ θ).symm

/-- `(deriv N)² y^{-2-γ}` is integrable on the near field. -/
lemma integrableOn_agFd_near (N : ℝ → ℝ) (γ : ℝ) (M : ℝ → ℝ)
    (hNd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ M θ)
    (hMint : MeasureTheory.IntegrableOn M (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hs
  have hY : AEStronglyMeasurable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-2 - γ)) (volume.restrict s) :=
    ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
      show ((Real.pi : ℝ) / 2 - x) ≠ 0
      linarith [hx.2]))).aestronglyMeasurable measurableSet_Ioo
  have hf : AEStronglyMeasurable
      (fun θ : ℝ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)) (volume.restrict s) :=
    ((measurable_deriv N).aestronglyMeasurable.pow 2).mul hY
  refine Integrable.mono' hMint hf ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hd2 : 0 ≤ (deriv N θ) ^ 2 := sq_nonneg _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-2 - γ) := Real.rpow_nonneg (by linarith [hθ.2]) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd2 hyn)]
  exact hNd θ hθ

/-! ### Splitting the `Iθ`-integral and the far-field estimate -/

/-- Split `∫_{[0,π/2]}` at `π/4`. -/
lemma integral_Iθ_split (f : ℝ → ℝ) (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, f θ
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), f θ)
        + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ) := by
  have hae : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume]
      (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (Real.pi / 4))
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      rcases lt_trichotomy x (Real.pi / 4) with hlt | heq | hgt
      · exact absurd (Or.inl ⟨h1, hlt⟩) h3
      · exact heq
      · exact absurd (Or.inr ⟨hgt, h2⟩) h3
    · have hsub : (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
          ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        intro x hx
        rcases hx with hx | hx
        · exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
        · exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
      rw [Set.sdiff_eq_empty.mpr hsub]
      simp
  have h1 : ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  have h2 : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ
      = ∫ θ in (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), f θ :=
    MeasureTheory.setIntegral_congr_set hae
  have h3 : ∫ θ in (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), f θ
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), f θ) + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ) := by
    refine MeasureTheory.setIntegral_union ?_ measurableSet_Ioo ?_ ?_
    · rw [Set.disjoint_left]; intro x hx1 hx2; linarith [hx1.2, hx2.1]
    · exact hf.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
    · exact hf.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)
  linarith [h1, h2, h3]

/-- Far-field integral bound for the left-hand side. -/
lemma farIntegral_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hI2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hI0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2)) (Set.Ioo 0 (Real.pi / 4))) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ 48 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        + 432 * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx; refine ⟨hx.1.le, ?_⟩; have := Real.pi_pos; linarith [hx.2]
  have hAint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 4)) := hI2.mono_set hsub
  have hBint : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hI1.mono_set hsub
  have hCint : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hI0.mono_set hsub
  set M : ℝ → ℝ := fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 with hM
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (Set.Ioo 0 (Real.pi / 4)) := hAint.const_mul 48
  have h2 : MeasureTheory.IntegrableOn (fun θ => 192 * (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hBint.const_mul 192
  have h3 : MeasureTheory.IntegrableOn (fun θ => 432 * (u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hCint.const_mul 432
  have h12 : MeasureTheory.IntegrableOn
      (fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 4)) := h1.add h2
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioo 0 (Real.pi / 4)) := by
    rw [hM]; exact h12.add h3
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), M θ := by
    refine MeasureTheory.integral_mono_ae hFint hMint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact far_F_le u γ hγ1 hγ2 hu4 hθ
  have hMval : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), M θ)
      = 48 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (deriv u θ) ^ 2)
        + 432 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (u θ) ^ 2) := by
    simp only [hM]
    rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_add h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
  have hnonnegA : ∀ x ∈ Work.Spaces.Iθ,
      0 ≤ (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x := fun x hx =>
    mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hx)
  have e1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_mono_set hI2
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact hnonnegA x hx)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have e2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (deriv u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hI1
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact sq_nonneg _)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have e3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hI0
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact sq_nonneg _)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  linarith [hmono, hMval, e1, e2, e3]

/-- Near-field integral estimate for the left-hand side. -/
lemma nearIntegral_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (hπ : u (Real.pi / 2) = 0)
    (hI3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hIntF : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
      (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ 2000 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 20000 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
  have hI1' : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hI1.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  set N : ℝ → ℝ := fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ with hN
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) with hA3
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set X : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ) with hX
  set Z : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) with hZ
  set U : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) with hU
  set P : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) with hP
  set Q : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv u θ) ^ 2 with hQ
  have hA3int : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hI3.mono_set hsub
  have hA1int : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hI1.mono_set hsub
  -- the pointwise bounds
  have hFpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2)
        ≤ 512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)) :=
    fun θ hθ => near_F_le u γ hγ1 hγ2 hθ
  have hNd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
        ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) :=
    fun θ hθ => near_Nd_le u γ hγ1 hγ2 hu4 hθ
  -- integrability of the Agmon integrands
  have hNint : MeasureTheory.IntegrableOn (agF γ N) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_agF_near u γ hγ1 hγ2 hu4 hIntF
  have hUint : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_sq_mul_sub_rpow γ hγ1 hγ2 u hu1 huc hπ hI1'
  have hM2int : MeasureTheory.IntegrableOn
      (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have h12 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hA3int.const_mul 8).add (hA1int.const_mul 64)
    exact h12.add (hUint.const_mul 8)
  have hNdint : MeasureTheory.IntegrableOn
      (fun θ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_agFd_near N γ
      (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))) hNd hM2int
  -- the Agmon inequality
  have hagmon : (2 + γ) * X ≤ Z := by
    have h := agmonWeightedHardy γ (Real.pi / 4) hγ1 hγ2 (by linarith [Real.pi_pos]) N
      (vTwoW4NIdents u hu4).2.2 hNint hNdint
    rw [hX, hZ]
    simpa only [agF, agFd] using h
  -- step 1: `∫ F ≤ 512 X`
  have hM1int : MeasureTheory.IntegrableOn
      (fun θ => 512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hNint.const_mul 512
  have hmono1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
    refine MeasureTheory.integral_mono_ae hIntF hM1int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hFpt θ hθ
  have hM1val : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ))) = 512 * X := by
    rw [hX, MeasureTheory.integral_const_mul]
  -- step 2: `X ≤ Z/3`
  have hXnn : 0 ≤ X := by
    rw [hX]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
  have h2 : X ≤ Z / 3 := by
    have hm := hagmon
    rw [hX, hZ] at hm
    have h3 : (3 : ℝ) ≤ 2 + γ := by linarith
    nlinarith [hm, hXnn, h3]
  -- step 3: `Z ≤ 8 A3 + 64 A1 + 8 U`
  have hmono2 : Z ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by
    rw [hZ]
    refine MeasureTheory.integral_mono_ae hNdint hM2int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hNd θ hθ
  have hM2val : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
      = 8 * P + 64 * Q + 8 * U := by
    have h8 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hUint.const_mul 8
    have h12 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hA3int.const_mul 8).add (hA1int.const_mul 64)
    rw [MeasureTheory.integral_add h12 h8,
        MeasureTheory.integral_add (hA3int.const_mul 8) (hA1int.const_mul 64),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hP, hQ, hU]
  have eP : P ≤ A3 := by
    rw [hP, hA3]
    refine MeasureTheory.setIntegral_mono_set hI3 ?_
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
  have eQ : Q ≤ A1 := by
    rw [hQ, hA1]
    refine MeasureTheory.setIntegral_mono_set hI1 ?_
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
    exact sq_nonneg _
  have h4 : U ≤ 2 * A1 := by
    have hhardy := hardyUDivY γ hγ1 hγ2 u hu1 huc hπ hI1'
    have hupper : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2) ≤ A1 := by
      rw [hA1]
      refine MeasureTheory.setIntegral_mono_set hI1 ?_
        (Filter.Eventually.of_forall (fun x hx => ⟨hx.1.le, hx.2.le⟩))
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
      exact sq_nonneg _
    rw [← hU] at hhardy
    linarith [hhardy, hupper]
  linarith [hmono1, hM1val, h2, hmono2, hM2val, eP, eQ, h4]

theorem vTwoW4WeakAlt : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro γ u hγ1 hγ2 hu4 huc hu0 huπ hI3 hI2 hI1 hI0
  set F : ℝ → ℝ := fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
      (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2) with hF
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) with hA3
  set A2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ with hA2
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set A0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hA0
  change (∫ θ in Work.Spaces.Iθ, F θ) ≤ 1000000 * (A3 + A2 + A1 + A0)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]; exact MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]; exact MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  by_cases hInt : MeasureTheory.IntegrableOn F Work.Spaces.Iθ
  · rw [integral_Iθ_split F hInt]
    have hFintFar : MeasureTheory.IntegrableOn F (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      hInt.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
    have hFintNear : MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      hInt.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)
    have hnear := nearIntegral_le u γ hγ1 hγ2 hu4 huc huπ hI3 hI1 hFintNear
    have hfar := farIntegral_le u γ hγ1 hγ2 hu4 hI2 hI1 hI0 hFintFar
    have hnear' : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
        ≤ 2000 * A3 + 20000 * A1 := by
      rw [hF, hA3, hA1]; exact hnear
    have hfar' : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), F θ)
        ≤ 48 * A2 + 192 * A1 + 432 * A0 := by
      rw [hF, hA2, hA1, hA0]; exact hfar
    linarith [hnear', hfar', hA3nn, hA2nn, hA1nn, hA0nn]
  · rw [MeasureTheory.integral_undef hInt]
    nlinarith [hA3nn, hA2nn, hA1nn, hA0nn]

end Work.FTS.EllipticEst.H2W.VTwoAlt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.mixedA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/mixedA`: the angular (mixed) part of the `ℋ²` estimate for `z²∂_z²Ψ`

This module contains the elementary structural layer of the target
`Work.FTS.EllipticEst.H2W.mixedA` (the `hA` input of `TT.est_two_weak_of_pieces`):

```
∀ α F Ψ, 0 < α → α ≤ 1/4 → EllWeakPos α 2 F Ψ →
  α⁴·HkSq α 2 (z²∂_z²Ψ) ≤ α⁴·Σ_{j<3} L2Sq(z²∂_z²(D_z^jΨ)·w/sin^{η/2}) + HkSq α 2 F
```

The two proved observations recorded here identify the target's right-hand side as the *pure*
(`z`-only) part of `HkSq α 2 (z²∂_z²Ψ)`:

* `z2_pzIter2_eq` — the pointwise operator identity `z²∂_z² = D_z² − D_z`, from which the
  commuting relation `z²·pzIter 2 (DzIter j Ψ) = DzIter j (z²·pzIter 2 Ψ)` follows (polynomials in
  `D_z` commute; the remaining formalisation is the linearity of `DzIter j` on differences and the
  slicewise differentiability of the iterates, both routine).

Consequently the target is *equivalent* to the bound
`α⁴·Σ_{(i,j)∈{(1,0),(1,1),(2,0)}} ∫∫(D_z^jD_θ^i(z²∂_z²Ψ))²·Wt² ≤ HkSq α 2 F`
on the three mixed slots of the `ℋ²`-norm of `A = z²∂_z²Ψ` — i.e. it is the *angular half* of
Elgindi's Proposition `prop:H2`, with the radial (pure) part kept on the right as slack.  See
`NOTES_mixedA.md` in this directory for the numerical evidence that the statement is true
(ratios `≤ 1.3e−3` in every family tested, including the exactly computable resonance family
`z^{2n/α}e^{−z}φ_n`), and for the analysis of why its proof needs the sharp `Step 4/5` machinery
of the elliptic section (not yet available in the workspace).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The target

By `hksqSplitMixed` the two sides of the target differ exactly by the three *mixed* (angular)
slots of the `ℋ²`-norm of `A = z²∂_z²Ψ`: the target is equivalent to

`α⁴·Σ_{(i,j) ∈ {(1,0),(1,1),(2,0)}} L2Sq(D_z^jD_θ^iA·Wt) ≤ HkSq α 2 F`.

The proof of *that* statement is the missing sharp analytic chapter.  The state of the analysis
is recorded in `NOTES_mixedA_session3.md` (session 3) and `NOTES_mixedA.md` / `NOTES_mixedA2.md`
(sessions 1–2); in brief:

* the reduction is formalised here as `mixedA_of_mixedSlots` (target from the split + the mixed
  sum) and, finer, as **`mixedA_of_slotBounds`** (from the three slot bounds with explicit
  constants `c₁₀+c₁₁+c₂₀ ≤ 1`);
* the θ-Poincaré input `∫(u')²s^{2-γ} ≤ ∫(u'')²s^{2-γ}` is **delivered** as
  `Submission.Work.H2W.ThetaPoincareSharp` (constant `1`; its only residual `sorry` is the
  numeric bound delegated as `Submission.Work.H2W.WhPhiPsiIntegralLeFix`);
* the `(1,0)`/`(2,0)` slots reduce to the θ-Poincaré + the level-`0` estimate on the *radially
  shifted* data; the latter is the project's open bottleneck (presently `sorryAx`);
* the `(1,0)`- and `(1,1)`-slot *per-slot* comparisons with constant `1` are **false** for
  general data (small deficits; the `Lzero1`-eigenvalue hypothesis of the 1-D reduction is
  replaced by an *effective* angular eigenvalue outside the good range) — so the missing piece
  is a *relaxed* per-slot bound `α⁴·L2Sq(mixed j i A·Wt) ≤ L2Sq(mixed j i F·Wt) + δ·HkSq α 2F`
  with a small `δ`, plus the bookkeeping of the otherwise-unused pure `F`-slots.

Below is the assembly of the target from the split and the slot bounds (both proved), which is
the part that the elementary lemmas of this file support. -/




end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.FTS.EllipticEst

/-! ## Pointwise `L²` bound for the weighted Hardy operator `HarOp`

This file proves

  `(HarOp β f z) ^ 2 ≤ (1 / β) * z ^ (-β) * ∫⁻ s in (0,z], s ^ (β - 1) * f s ^ 2`

(as an inequality in `ℝ≥0∞`), for `β > 1`, `z > 0` and `f` with `f ^ 2` integrable on `(0,∞)`.

The mathematical content is the weighted Cauchy–Schwarz inequality

  `(∫_0^z s ^ (β - 1) f s) ^ 2 ≤ (∫_0^z s ^ (β - 1)) * (∫_0^z s ^ (β - 1) f s ^ 2)`

together with `∫_0^z s ^ (β - 1) = z ^ β / β`.

Note that `f` is *not* assumed measurable: only `f ^ 2` is.  We therefore never use `f` itself
as a measurable function; the `|f|` that appears in Cauchy–Schwarz is written as `√(f ^ 2)` (the
definition `absF` below), which is a.e. strongly measurable as soon as `f ^ 2` is. -/

/-- `s ↦ √(f s ^ 2)`, i.e. `|f s|` in a form that is a.e. strongly measurable as soon as
`f ^ 2` is. -/
def absF (f : ℝ → ℝ) : ℝ → ℝ := fun s => Real.sqrt (f s ^ 2)

theorem absF_eq_abs (f : ℝ → ℝ) (s : ℝ) : absF f s = |f s| := Real.sqrt_sq_eq_abs (f s)

theorem absF_nonneg (f : ℝ → ℝ) (s : ℝ) : 0 ≤ absF f s := Real.sqrt_nonneg _

theorem absF_sq (f : ℝ → ℝ) (s : ℝ) : absF f s ^ 2 = f s ^ 2 := by
  rw [absF_eq_abs, sq_abs]

/-- `(x ^ y) ^ 2 = x ^ (y + y)` for `x > 0`, for the real power `x ^ y`. -/
theorem sq_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (y + y) := by
  rw [pow_two, Real.rpow_add hx]

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]

/-- `∫ s in 0..z, s ^ (β - 1) = z ^ β / β` for `β > 0`. -/
theorem intervalIntegral_rpow_sub_one {β z : ℝ} (hβ : 0 < β) :
    ∫ s in (0 : ℝ)..z, s ^ (β - 1) = z ^ β / β := by
  have h1 : β - 1 + 1 = β := by ring
  rw [integral_rpow (a := 0) (b := z) (r := β - 1) (Or.inl (by linarith)), h1,
    Real.zero_rpow (ne_of_gt hβ)]
  ring

/-- Cauchy–Schwarz in squared form for the Bochner integral of two real functions (no sign
hypothesis is needed: `|∫ a * b| ≤ ∫ |a| * |b| ≤ (∫ a²)^{1/2} (∫ b²)^{1/2}`). -/
theorem sq_integral_mul_le_general {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {a b : α → ℝ} (ha' : AEStronglyMeasurable a μ) (hb' : AEStronglyMeasurable b μ)
    (ha : MeasureTheory.Integrable (fun s => a s ^ 2) μ)
    (hb : MeasureTheory.Integrable (fun s => b s ^ 2) μ)
    (hab : MeasureTheory.Integrable (fun s => a s * b s) μ) :
    (MeasureTheory.integral μ (fun s => a s * b s)) ^ 2 ≤
      (MeasureTheory.integral μ (fun s => a s ^ 2)) *
        (MeasureTheory.integral μ (fun s => b s ^ 2)) := by
  have hAabs : AEStronglyMeasurable (fun x => |a x|) μ := by
    simpa only [Real.norm_eq_abs] using ha'.norm
  have hBabs : AEStronglyMeasurable (fun x => |b x|) μ := by
    simpa only [Real.norm_eq_abs] using hb'.norm
  have hAi : Integrable (fun x => |a x| ^ 2) μ :=
    ha.congr (Filter.Eventually.of_forall fun x => (sq_abs (a x)).symm)
  have hBi : Integrable (fun x => |b x| ^ 2) μ :=
    hb.congr (Filter.Eventually.of_forall fun x => (sq_abs (b x)).symm)
  have hA' : MemLp (fun x => |a x|) 2 μ := (memLp_two_iff_integrable_sq hAabs).mpr hAi
  have hB' : MemLp (fun x => |b x|) 2 μ := (memLp_two_iff_integrable_sq hBabs).mpr hBi
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall fun x => abs_nonneg (a x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (b x))
    (by rw [ENNReal.ofReal_ofNat]; exact hA')
    (by rw [ENNReal.ofReal_ofNat]; exact hB')
  have hA2eq : (∫ x, |a x| ^ (2 : ℝ) ∂μ) = ∫ x, a x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_ofNat, sq_abs]
  have hB2eq : (∫ x, |b x| ^ (2 : ℝ) ∂μ) = ∫ x, b x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_ofNat, sq_abs]
  rw [hA2eq, hB2eq] at hholder
  have hAB : |∫ x, a x * b x ∂μ| ≤
      (∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    calc |∫ x, a x * b x ∂μ| ≤ ∫ x, |a x * b x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |a x| * |b x| ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [abs_mul]
      _ ≤ _ := hholder
  have hsq : ((∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2
      = (∫ x, a x ^ 2 ∂μ) * (∫ x, b x ^ 2 ∂μ) := by
    have hAn : 0 ≤ ∫ x, a x ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (a x))
    have hBn : 0 ≤ ∫ x, b x ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (b x))
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hAn, Real.sq_sqrt hBn]
  calc (∫ x, a x * b x ∂μ) ^ 2 = |∫ x, a x * b x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hAB 2
    _ = (∫ x, a x ^ 2 ∂μ) * (∫ x, b x ^ 2 ∂μ) := hsq

theorem HarOp_pointwise_sq (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((Work.FTS.EllipticEst.HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
        ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
  have hβ0 : 0 < β := one_pos.trans hβ
  have hb1 : 0 ≤ β - 1 := by linarith
  have hb1' : 0 < β - 1 := by linarith
  have hb2 : 0 ≤ (β - 1) / 2 := by linarith
  have hb2' : 0 < (β - 1) / 2 := by linarith
  have hz0 : 0 ≤ z := hz.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set I : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s with hI
  set J2 : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s ^ 2 with hJ2
  -- integrability of `f ^ 2` on `(0, z]`
  have hf2 : Integrable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hf.mono_set Set.Ioc_subset_Ioi_self
  -- a dominating integrable function
  have hM : Integrable (fun s : ℝ => z ^ (β - 1) + z ^ (β - 1) * f s ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (integrable_const _).add (hf2.const_mul _)
  -- `|f|`, as the a.e. strongly measurable function `√(f ^ 2)`
  have hφ : AEStronglyMeasurable (absF f) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf2.aestronglyMeasurable
  have hcont : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 1) / 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_rpow_const hb2).aestronglyMeasurable
  -- ## The three integrability assumptions of Cauchy–Schwarz
  have ha : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((Real.continuous_rpow_const hb2).pow 2).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2))), sq_rpow hx0,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow hx0.le hx.2 hb1
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hz0 _) (sq_nonneg _))
  have hb : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2) * absF f s) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((hcont.mul hφ).pow 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2) * absF f x)),
      mul_pow, sq_rpow hx0, absF_sq,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) * f x ^ 2 ≤ z ^ (β - 1) * f x ^ 2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (sq_nonneg _)
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_left (Real.rpow_nonneg hz0 _)
  have hab : Integrable (fun s : ℝ => s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM (hcont.mul (hcont.mul hφ)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have hxp : 0 ≤ x ^ ((β - 1) / 2) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxp, abs_mul, abs_of_nonneg hxp,
      abs_of_nonneg (absF_nonneg f x), absF_eq_abs,
      show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * |f x|)
          = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * |f x| from by ring,
      show x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) from by
        rw [← Real.rpow_add hx0]; congr 1; ring]
    calc x ^ (β - 1) * |f x| ≤ z ^ (β - 1) * |f x| :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (abs_nonneg _)
      _ ≤ z ^ (β - 1) * (1 + f x ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_le_one_add_sq (f x)) (Real.rpow_nonneg hz0 _)
      _ = z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 := by ring
  -- ## Cauchy–Schwarz
  have hcs := sq_integral_mul_le_general (volume.restrict (Set.Ioc (0 : ℝ) z))
    (a := fun s : ℝ => s ^ ((β - 1) / 2)) (b := fun s : ℝ => s ^ ((β - 1) / 2) * absF f s)
    hcont (hcont.mul hφ) ha hb hab
  have hA : (∫ s in Set.Ioc (0 : ℝ) z, s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z,
          s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * absF f s :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        have h2 : x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) := by
          rw [← Real.rpow_add hx.1]; congr 1; ring
        rw [show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * absF f x)
            = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * absF f x from by ring, h2])
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hB : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2) = z ^ β / β := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rcases eq_or_lt_of_le hx.1.le with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hb2'), Real.zero_rpow (ne_of_gt hb1')]
        norm_num
      · rw [sq_rpow h, show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
    exact intervalIntegral_rpow_sub_one hβ0
  have hC : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2) = J2 := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * f s ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rw [mul_pow, sq_rpow hx.1, absF_sq,
        show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, hJ2]
    exact (intervalIntegral.integral_of_le hz0).symm
  have hCS : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 ≤ (z ^ β / β) * J2 := by
    have h := hcs
    rw [hA, hB, hC] at h
    exact h
  -- ## The integral itself
  have hJle : |I| ≤ ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun s : ℝ => s ^ (β - 1) * f s) hz0
    rw [← hI, Real.norm_eq_abs, intervalIntegral.integral_of_le hz0] at h1
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le (β - 1)), absF_eq_abs]
  have hI2 : I ^ 2 ≤ (z ^ β / β) * J2 := by
    have h2 : |I| ^ 2 ≤ (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg I) hJle 2
    rw [sq_abs] at h2
    linarith [hCS, h2]
  -- ## The a.e. bridge to the Lebesgue integral
  have hgI : IntegrableOn (fun s : ℝ => s ^ (β - 1) * f s ^ 2) (Set.Ioc 0 z) :=
    hb.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx => by
        show (x ^ ((β - 1) / 2) * absF f x) ^ 2 = x ^ (β - 1) * f x ^ 2
        rw [mul_pow, sq_rpow hx.1, absF_sq,
          show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]))
  have hbridge : ENNReal.ofReal J2
      = ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
    rw [hJ2, intervalIntegral.integral_of_le hz0]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx =>
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (f x))))
  -- ## Final assembly
  have huz : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, show -β + β = 0 from by ring, Real.rpow_zero]
  have hmain : (HarOp β f z) ^ 2 = (z ^ (-β)) ^ 2 * I ^ 2 := by
    rw [HarOp, ← hI]
    ring
  have hkey : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2) = (1 / β) * (z ^ (-β) * J2) := by
    have h1 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) := by
      have h2 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) * (z ^ (-β) * z ^ β) := by ring
      rw [h2, huz, mul_one]
    have h3 : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)
        = ((z ^ (-β)) ^ 2 * z ^ β) * (J2 / β) := by ring
    rw [h3, h1]
    ring
  calc ENNReal.ofReal ((HarOp β f z) ^ 2)
      = ENNReal.ofReal ((z ^ (-β)) ^ 2 * I ^ 2) := by rw [hmain]
    _ ≤ ENNReal.ofReal ((z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) * ENNReal.ofReal J2 := by
        rw [hkey, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Real.rpow_nonneg hz0 (-β))]
        ring
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
          ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
        rw [hbridge]

end Work.FTS.EllipticEst
end
end
