import Mathlib
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
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
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Coercivity.Dz_deriv_bound =====
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

/-- **Exact derivative of the weighted square.**  For `z > 0` and a function smooth on a
neighbourhood of the closed quadrant,

  `d/dz [ z (D_z f z θ · w z)² ] = 2 ∂_z f · ∂_z² f · (1+z)^4/z
      + (∂_z f)² · (1+z)^3 (3z-1)/z²`.

Indeed, for `z' > 0` the algebraic identity `zw_sq_factor` rewrites the left-hand side as
`(∂_z f)² (1+z)^4/z`; the derivative of that expression is the displayed one by the
Leibniz rule, using `deriv (∂_z f(·,θ)) z = ∂_z² f(z,θ)` (smoothness of the `θ`-slice). -/
private theorem deriv_zw_sq_factor (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {θ z : ℝ} (hθ : θ ∈ Spaces.Iθ) (hz : 0 < z) :
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = 2 * (Spaces.pz f z θ) * (Spaces.pz (Spaces.pz f) z θ) * ((1 + z) ^ 4 / z)
        + (Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2) := by
  -- `z (D_z f · w)² = (∂_z f)² (1+z)^4/z` in a neighbourhood of `z` (where `z' ≠ 0`).
  have hEq : (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2)
      =ᶠ[𝓝 z] (fun z' => (Spaces.pz f z' θ) ^ 2 * (1 + z') ^ 4 / z') := by
    filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hz)] with z' hz'
    exact zw_sq_factor f hz'
  rw [Filter.EventuallyEq.deriv_eq hEq]
  -- The `θ`-slice is smooth at `z`, so `∂_z f(·,θ)` has derivative `∂_z² f(z,θ)`.
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have ha : HasDerivAt (fun z' => Spaces.pz f z' θ) (Spaces.pz (Spaces.pz f) z θ) z := by
    have hs : ContDiffAt ℝ ⊤ (fun z'' => f z'' θ) z :=
      ((Spaces.hardyZ_contDiffOn_slice f hsm hθ).contDiffAt (isOpen_Ioi.mem_nhds hzmem))
    have hd : DifferentiableAt ℝ (deriv (fun z'' => f z'' θ)) z := by
      have h1 : ContDiffAt ℝ 1 (deriv (fun z'' => f z'' θ)) z :=
        hs.derivWithin (m := 1) (by simp)
      exact h1.differentiableAt (by norm_num)
    have := (hasDerivAt_deriv_iff (f := deriv (fun z'' => f z'' θ)) (x := z)).mpr hd
    simpa [Spaces.pz] using this
  have hz' : z ≠ 0 := ne_of_gt hz
  -- Derivative of `(1+z')^4/z'`.
  have hc : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4 / z')
      ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h1 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4) (4 * (1 + z) ^ 3) z := by
      convert h.pow 4 using 1
      ring
    have h2 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have hd := h1.div h2 hz'
    convert hd using 1
    · field_simp
      ring
  -- Leibniz rule for `(∂_z f)² · (1+z')^4/z'`.
  have h2 := (ha.pow 2).mul hc
  have hfun : (fun z' => (Spaces.pz f z' θ) ^ 2 * (1 + z') ^ 4 / z')
      = ((fun z' => Spaces.pz f z' θ) ^ 2 * fun z' => (1 + z') ^ 4 / z') := by
    ext z'; simp only [Pi.pow_apply, Pi.mul_apply]; ring_nf
  rw [hfun, h2.deriv]
  simp only [Pi.pow_apply]
  ring

/-- **Elementary bound on the derivative expression.**  For `0 < z ≤ 1`, `|P| ≤ C₁ z`
and `|Q| ≤ M`,

  `|2 P Q (1+z)^4/z + P² (1+z)^3 (3z-1)/z²| ≤ 32 C₁ M + 48 C₁²`.

The two inequalities `h1, h2` force `C₁, M ≥ 0`.  Splitting with the triangle inequality
and using `|P| ≤ C₁ z`, `|Q| ≤ M`, `(1+z)^4 ≤ 16`, `(1+z)^3 ≤ 8`, `|3z-1| ≤ 2` gives the
claim (only the triples `32` and `16 ≤ 48` being used, so the constants are loose). -/
private theorem deriv_ineq {P Q z C₁ M : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : |P| ≤ C₁ * z) (h2 : |Q| ≤ M) :
    |2 * P * Q * ((1 + z) ^ 4 / z) + P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ 32 * C₁ * M + 48 * C₁ ^ 2 := by
  have hC1 : 0 ≤ C₁ := by
    have h : 0 ≤ C₁ * z := le_trans (abs_nonneg P) h1
    exact (mul_nonneg_iff_of_pos_right hz).mp h
  have hM : 0 ≤ M := le_trans (abs_nonneg Q) h2
  have hcpos : (0 : ℝ) ≤ (1 + z) ^ 4 / z := by positivity
  have hp4 : (1 + z) ^ 4 ≤ 16 := by
    have h2' : (1 + z) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + z := by linarith
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2' 4
      _ = 16 := by norm_num
  have hp3 : (1 + z) ^ 3 ≤ 8 := by
    have h2' : (1 + z) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + z := by linarith
    calc (1 + z) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h2' 3
      _ = 8 := by norm_num
  have h3z : |3 * z - 1| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hT1 : |2 * P * Q * ((1 + z) ^ 4 / z)| ≤ 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) := by
    have h_eq : |2 * P * Q * ((1 + z) ^ 4 / z)| = 2 * |P| * |Q| * ((1 + z) ^ 4 / z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcpos,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h_eq]
    have hPQ : |P| * |Q| ≤ (C₁ * z) * M :=
      mul_le_mul h1 h2 (abs_nonneg Q) (by positivity)
    calc 2 * |P| * |Q| * ((1 + z) ^ 4 / z)
        = 2 * (|P| * |Q|) * ((1 + z) ^ 4 / z) := by ring
      _ ≤ 2 * ((C₁ * z) * M) * ((1 + z) ^ 4 / z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQ (by norm_num)) hcpos
      _ = 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) := by ring
  have hT2 : |P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) := by
    have h_eq : |P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
        = |P| ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) := by
      rw [abs_mul, abs_pow, abs_div, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
    rw [h_eq]
    have hP2 : |P| ^ 2 ≤ (C₁ * z) ^ 2 := pow_le_pow_left₀ (abs_nonneg P) h1 2
    have hepos : (0 : ℝ) ≤ (1 + z) ^ 3 * |3 * z - 1| / z ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hP2 hepos
  have hmain : |2 * P * Q * ((1 + z) ^ 4 / z) + P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z)
        + (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) :=
    le_trans (abs_add_le _ _) (add_le_add hT1 hT2)
  refine le_trans hmain ?_
  have e1 : 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) = 2 * C₁ * M * (1 + z) ^ 4 := by field_simp
  have e2 : (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2)
      = C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) := by field_simp
  rw [e1, e2]
  have hb1 : 2 * C₁ * M * (1 + z) ^ 4 ≤ 32 * C₁ * M := by
    have hcm : (0 : ℝ) ≤ 2 * C₁ * M := by positivity
    calc 2 * C₁ * M * (1 + z) ^ 4 ≤ 2 * C₁ * M * 16 := mul_le_mul_of_nonneg_left hp4 hcm
      _ = 32 * C₁ * M := by ring
  have hb2 : C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) ≤ 48 * C₁ ^ 2 := by
    have hbound : (1 + z) ^ 3 * |3 * z - 1| ≤ 16 := by
      calc (1 + z) ^ 3 * |3 * z - 1| ≤ 8 * 2 :=
            mul_le_mul hp3 h3z (abs_nonneg _) (by norm_num)
        _ = 16 := by norm_num
    calc C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) ≤ C₁ ^ 2 * 16 :=
          mul_le_mul_of_nonneg_left hbound (sq_nonneg C₁)
      _ ≤ 48 * C₁ ^ 2 := by nlinarith [sq_nonneg C₁]
  linarith

theorem Dz_deriv_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {θ z C₁ M : ℝ} (hθ : θ ∈ Spaces.Iθ) (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : |Spaces.pz f z θ| ≤ C₁ * z) (h2 : |Spaces.pz (Spaces.pz f) z θ| ≤ M) :
    |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z|
      ≤ 32 * C₁ * M + 48 * C₁ ^ 2 := by
  rw [deriv_zw_sq_factor f hsm hθ hz]
  exact deriv_ineq hz hz1 h1 h2

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.Dz_zero_at_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set

namespace Work.Coercivity

set_option autoImplicit false

/-- **Vanishing of the radial derivative at the origin.**  For a function `f` smooth on a
neighbourhood of the closed quadrant whose boundary quantity `z (D_z f · w)²` tends to `0`
at `0⁺`, the radial derivative of the slice `z ↦ f z θ` vanishes at `z = 0`. -/
theorem Dz_zero_at_zero (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0 := by
  intro θ hθ
  have hself : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
  -- Step 1: rewrite the hypothesis using `zw_sq_factor`.
  have heq1 : (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z) := by
    filter_upwards [hself] with z hz
    exact zw_sq_factor f (by simp only [Set.mem_Ioi] at hz; linarith)
  have h1 : Filter.Tendsto (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := (hbd θ hθ).congr' heq1
  -- The auxiliary factor `z/(1+z)^4` is continuous at `0` with value `0`.
  have hzcont : Filter.Tendsto (fun z : ℝ => z / (1 + z) ^ 4)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℝ => z / (1 + z) ^ 4) 0 :=
      continuousAt_id.div (by fun_prop) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  -- Step 2: multiply back to recover `(∂_z f ·)²`.
  have heq2 : (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z * (z / (1 + z) ^ 4))
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] (fun z => (Spaces.pz f z θ) ^ 2) := by
    filter_upwards [hself] with z hz
    have hz0 : z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
    have h1z : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 (by simp only [Set.mem_Ioi] at hz; linarith)
    have h1z' : 1 + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
    field_simp
  have h2 : Filter.Tendsto (fun z => (Spaces.pz f z θ) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (h1.mul hzcont).congr' heq2
  -- Step 3: take square roots: `|∂_z f| → 0`.
  have h3 : Filter.Tendsto (fun z => Real.sqrt ((Spaces.pz f z θ) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp h2
  have h4 : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using h3
  -- Step 4: continuity of the slice derivative at `0` identifies the limit.
  have hcont : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi (-1))) (nhds (Spaces.pz f 0 θ)) :=
    (Spaces.hardyZ_continuousOn_pz_slice f hsm hθ).continuousWithinAt (by simp)
  have hcont' : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Spaces.pz f 0 θ)) :=
    hcont.mono_left (nhdsWithin_mono 0 (fun z hz => by
      simp only [Set.mem_Ioi] at hz ⊢; linarith))
  have hnb : (nhdsWithin (0:ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique hcont' h4

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.EL12z_hardy =====
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

/-- **The abstract Hardy inequality**: for `g` differentiable on `(0,∞)` with derivative
`g'`, whose "boundary term" `z ↦ g z ^ 2 / z` vanishes at `0⁺` and at `+∞`, and with
`g ^ 2 / z ^ 2` and `g' ^ 2` integrable on `(0,∞)`,

  `∫_0^∞ g(z)² / z² dz ≤ 4 ∫_0^∞ g'(z)² dz`.

This is the sharp Hardy constant `4`.  The two halves of the proof are
`∫_0^∞ g²/z² = ∫_0^∞ 2 g g'/z` (integration by parts) and the AM–GM bound
`∫ 2 g g'/z ≤ (1/2) ∫ g²/z² + 2 ∫ g'²`; combining them gives
`A ≤ A/2 + 2B`, hence `A ≤ 4B` for `A = ∫ g²/z²`, `B = ∫ g'²`. -/
theorem hardy_core (g g' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' z) z)
    (h0 : Tendsto (fun z => g z ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (htop : Tendsto (fun z => g z ^ 2 / z) atTop (𝓝 0))
    (hA : IntegrableOn (fun z => g z ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)))
    (hB : IntegrableOn (fun z => g' z ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), g z ^ 2 / z ^ 2 ≤ 4 * ∫ z in Set.Ioi (0 : ℝ), (g' z) ^ 2 := by
  -- `A = ∫ 2 g g'/z` (integration by parts; `HardyHyp`-style boundary conditions).
  have h1 := HardyCore.hardy_ftc g g' hderiv h0 htop hA hB
  -- `∫ 2 g g'/z ≤ A/2 + 2B` (AM–GM).
  have h2 := HardyCore.hardy_amgm g g' hA hB
  linarith

/-- **The Hardy inequality for the fundamental model's `L₁₂`**: for `f` satisfying the
analytic hypotheses `HardyHyp` and with `L₁₂dens K f` square integrable,

  `∫_0^∞ (L₁₂(f)(z))² / z² dz ≤ 4 ∫_0^∞ (L₁₂dens(f)(z))² dz`.

Here `L₁₂(f) = ∫_z^∞ L₁₂dens(f)` is the radial function of the fundamental model, and
`L₁₂dens(f)(z) = ∫_θ K(θ) f(z,θ)/z dθ` is its (negative) derivative.  This is the sharp
`z^{-2}` component of the paper's Lemma `HardyWeight` (Annals 194 (3) 2021, tex 503). -/
theorem EL12z_hardy (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hQ : MeasureTheory.IntegrableOn (fun z => (FM.L12dens Spaces.K f z) ^ 2) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), (L12f f z) ^ 2 / z ^ 2
      ≤ 4 * ∫ z in Set.Ioi (0 : ℝ), (FM.L12dens Spaces.K f z) ^ 2 := by
  -- `L₁₂(f)` is differentiable on `(0,∞)` with derivative `-L₁₂dens(f)`.
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (L12f f) (-(FM.L12dens Spaces.K f z)) z := fun z hz =>
    FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  -- The two boundary terms `(L₁₂(f))²/z` vanish at `0⁺` and at `+∞`
  -- (`HardyHyp.bd0`/`HardyHyp.bdTop` at `j = 1`).
  have h0 : Tendsto (fun z => (L12f f z) ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hf.bd0 1 (by norm_num)).1
    have hexp : (2 * ((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [hexp] at h
    simpa [Real.rpow_one] using h
  have htop : Tendsto (fun z => (L12f f z) ^ 2 / z) atTop (𝓝 0) := by
    have h := (hf.bdTop 1 (by norm_num)).1
    have hexp : (2 * ((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [hexp] at h
    simpa [Real.rpow_one] using h
  -- `∫ (L₁₂(f))²/z²` is finite (`HardyHyp.intA` at `j = 1`).
  have hA : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    have h := hf.intA 1 (by norm_num)
    simpa using h
  -- `∫ (L₁₂dens(f))²` is finite by hypothesis.
  have hB : IntegrableOn (fun z => (-(FM.L12dens Spaces.K f z)) ^ 2) (Set.Ioi 0) := by
    simpa using hQ
  have hmain := hardy_core (L12f f) (fun z => -(FM.L12dens Spaces.K f z))
    hderiv h0 htop hA hB
  simpa using hmain

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.L12dens_sq_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- The squared angular density `L₁₂^K(f)(z) = (1/z)∫_θ K(θ) f(z,θ) dθ` of the fundamental
model is controlled by the angular energy of the slice: for `z > 0`,
`(L₁₂^K(f)(z))² ≤ 3 (∫_θ f(z,θ)² dθ)/z²`.

This is the Cauchy–Schwarz inequality for the weight `K(θ) = 3 sin θ cos²θ` on
`Iθ = [0,π/2]` (whose `L²`-norm on the slice is at most `3 = ‖K‖_∞`), together with the
elementary identity `L₁₂^K(f)(z) = (1/z)∫_θ K(θ) f(z,θ) dθ`.  The normalisation
`∫_θ K = 1` is not needed for the estimate. -/
theorem L12dens_sq_slice (f : ℝ → ℝ → ℝ)
    (hK : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = (1 : ℝ)) {z : ℝ} (hz : 0 < z)
    (hsl : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ) :
    (Work.FM.L12dens Work.Spaces.K f z) ^ 2
      ≤ 3 * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 := by
  -- Cauchy–Schwarz on the angular slice, against the weight `K`.
  have hcs : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2
      ≤ 3 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 :=
    slice_cs_K f z K_facts_nonneg K_facts_sq_integrableOn K_facts.2.2.2 hsl
  -- `L₁₂^K(f)(z)` is `(1/z)` times that angular integral, and `z > 0`.
  rw [Work.FM.L12dens, MeasureTheory.integral_div, div_pow]
  exact div_le_div_of_nonneg_right hcs (by positivity)

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.angular_avg_w_sq_le =====
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
-- ===== merged: Submission.Work.Coercivity.bd0_Dz =====
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

/-! ## The real-analysis step

The whole content is the second-order Taylor expansion of a real function at
`0`.  Hypotheses: `g` is `C²` at `0` and `|g z| / z^{3/2} → 0` along `𝓝[>] 0`.

1. `|g z| = z^{3/2} · (|g z|/z^{3/2}) → 0`, so `g z → 0` and, `g` being
   continuous at `0`, `g 0 = 0`.
2. `slope g 0 z = g z / z = z^{1/2} · (|g z|/z^{3/2}) → 0` (up to sign), so the
   right-sided limit of the slope is `0`; `g` being differentiable at `0` with
   two-sided slope limit `deriv g 0`, uniqueness gives `deriv g 0 = 0`.
3. `ContDiffAt ℝ 2 g 0` gives `ContDiffAt ℝ 1 (deriv g) 0`, hence
   `deriv g z = deriv g 0 + z · deriv (deriv g) 0 + o(z) = O(z)`; consequently
   `(deriv g z)²/z = z · (deriv g z / z)²` tends to `0`. -/


/-! ## The boundary term for `D_z f` -/


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.L12_Fstar_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F_*) = 2α/(1+z)`

For the profile `F_*(z,θ) = α (Γ(θ)/c(α)) 2z/(1+z)²` of Elgindi's paper the integral
operator `L₁₂` collapses to the elementary function `2α/(1+z)`.  The proof separates
variables (`F_* = g(z) Γ(θ)` with `g = α · 2z/(1+z)²/c(α)`), uses
`∫₀^{π/2} K Γ = c(α) ≠ 0` and the improper integral `∫_z^∞ F_*(s)/s ds = 2/(1+z)`
(`Work.FM.integral_Ioi_Fstar_div`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

/-- The angular density of `L₁₂` at the profile `F_*` is `α · F_*(s)/s`; the angular
integral contributes `∫₀^{π/2} K(θ)Γ(θ) dθ = c(α)` against the normalisation `1/c(α)` of
`F_*`. -/
theorem L12dens_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (s : ℝ) :
    L12dens (Fstar α) s = α * (Work.FM.Fstar s / s) := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0
    rw [h0] at h
    norm_num at h
  rw [L12dens, Work.FM.L12dens]
  have hpoint : ∀ θ : ℝ, Work.Spaces.K θ * Fstar α s θ / s
      = (α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α)
          * (Work.FM.Fstar s / s) := by
    intro θ
    simp only [Fstar]
    ring
  rw [setIntegral_congr_fun (s := Set.Icc 0 (Real.pi / 2)) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_mul_const]
  have hcint : (∫ θ in Set.Icc 0 (Real.pi / 2),
        α * (Work.Spaces.Gam α θ * Work.Spaces.K θ) / Work.Spaces.c α) = α := by
    rw [integral_div, integral_const_mul]
    have hval : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.Gam α θ * Work.Spaces.K θ) = Work.Spaces.c α := rfl
    rw [hval, mul_div_assoc, div_self hc, mul_one]
  rw [hcint]

theorem L12_Fstar_eq {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [L12, Work.FM.L12]
  rw [setIntegral_congr_fun (s := Set.Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Fstar α) s
            = α * (Work.FM.Fstar s / s) from L12dens_Fstar hα hα1 s)]
  rw [integral_const_mul, Work.FM.integral_Ioi_Fstar_div z hz]
  ring

end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.MufunS =====
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

/-! ## The corrected modulation constant -/

/-- **The corrected modulation constant `μ` of the modulation problem** (ruling
`FTS_MUFUN_SIGN.md` §5, option (a′)):

  `mufunS α N₀ N g = (1/(2α))(L₁₂(N₀)(0) + L₁₂(N)(0)) + (1/(2α)) L₁₂(3 D_θ g/(1+z))(0)`,

i.e. `2α · mufunS = μ̄ + L₁₂(Transport g)(0)` (`two_mul_mufunS`) — the sign forced by
`LGammaT_eq` and the paper's `gEquationFinal`.  It differs from `Construction.mufun` only in the
sign of the transport zero-mode (`mufunS_eq_mufun_neg`: `mufunS α N₀ N g = mufun α N₀ N (−g)`).

`mufunS` is the constant that `Galerkin.muDyn` and `Apriori.muOf` become in the coordinated
rebuild; `Construction.mufun` is retained (unchanged, so that its ~10⁴ importers keep building)
as the paper-display variant and is *superseded*. -/
def mufunS (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * α)) * (L12 N0v 0 + L12 Nv 0)
    + (1 / (2 * α)) * L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0

/-! ## Linearity of `L₁₂` in the profile, in the form used below -/

/-- `L₁₂` is odd in its profile argument: `L₁₂(−f)(ρ) = −L₁₂(f)(ρ)`, unconditionally.  The
Bochner integral is total and `L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`, so this is
`integral_neg` twice — no integrability hypothesis is needed. -/
theorem L12_neg (f : ℝ → ℝ → ℝ) (ρ : ℝ) : L12 (fun z θ => -f z θ) ρ = -L12 f ρ := by
  have hpoint : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun z θ => -f z θ) s
      = -Work.FM.L12dens Work.Spaces.K f s := by
    intro s
    rw [Work.FM.L12dens, Work.FM.L12dens, ← integral_neg]
    congr 1 with θ
    ring
  rw [L12, L12, Work.FM.L12, Work.FM.L12]
  simp only [hpoint, integral_neg]



/-- **The defining relation of the corrected modulation constant**:
`2α · mufunS α N₀ N g = μ̄ + L₁₂(Transport g)(0)`, where `μ̄ = mubar N₀ N` and
`Transport g = 3 D_θ g/(1+z)`.  This is the relation assumed by the paper's derivation
(`Construction/Equation.lean`, `gEquationFinal`) and the one that makes the dynamic profile
equation `(E)` hold *identically*, with no `L₁₂`-zero-mode hypothesis
(`Work.FTS.MeridianDyn.DynEqF_of_isDynEqOn` after the rebuild). -/
theorem two_mul_mufunS (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ) (hα : α ≠ 0) :
    2 * α * mufunS α N0v Nv g
      = mubar N0v Nv + L12 (Work.Coercivity.Transport g) 0 := by
  have hT : L12 (Work.Coercivity.Transport g) 0
      = L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 := rfl
  rw [hT, mufunS, mubar]
  field_simp


/-! ## The `|μ|`-bound -/

/-- **Design L-N4.8 for the corrected constant.**  Exactly the hypotheses of
`Work.FTS.Nonlin.mu_bound_mul` (the paper's three zero-mode estimates of Proposition
`muestimate`, each carrying a scaling constant `K`), with the conclusion for `mufunS`:

  `|mufunS α N₀ N g| ≤ 4K(α + α^{-1}X + α^{-5/2}X²)`.

Only the triangle inequality changes: `mufunS` is `(1/(2α))` times the **sum** (rather than the
signed sum) of the three `L₁₂`-values, and `|a + b + c| ≤ |a| + |b| + |c|` is the same bound.
The constant `4` is untouched, so every downstream consumer (`Nonlinear/Assembly`,
`OpenPkg/AssemblyOpen`, `Open2/Assembly2`) keeps its arithmetic. -/
theorem mu_bound_mulS {α X K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) (hK : 0 ≤ K)
    {N0v Nv g : ℝ → ℝ → ℝ}
    (h0 : |L12 N0v 0| ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |L12 Nv 0| ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ K * X) :
    |mufunS α N0v Nv g|
      ≤ 4 * (K * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := by
  set a := L12 N0v 0 with ha
  set b := L12 Nv 0 with hb
  set d := L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0 with hd
  set S := α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 with hS
  set T := α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 with hT
  have h0' : |a| ≤ K * S := by rw [ha, hS]; exact h0
  have h1' : |b| ≤ K * S := by rw [hb, hS]; exact h1
  have h2' : |d| ≤ K * X := by rw [hd]; exact h2
  have hmu : mufunS α N0v Nv g = (1 / (2 * α)) * ((a + b) + d) := by
    rw [mufunS, ha, hb, hd]; ring
  have htri : |(a + b) + d| ≤ K * (2 * S + X) := by
    have h12 : |(a + b) + d| ≤ |a + b| + |d| := abs_add_le (a + b) d
    have h3 : |a + b| ≤ |a| + |b| := abs_add_le a b
    linarith
  have hSle : S ≤ α * T := by
    rw [hS, hT]
    have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have h1_ : α * (α ^ (-(1 : ℝ)) * X) = X := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα, show (1 : ℝ) + (-(1 : ℝ)) = 0 by norm_num,
        Real.rpow_zero, one_mul]
    have h2_ : α * (α ^ (-(5 / 2 : ℝ)) * X ^ 2) = α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα,
        show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
    rw [mul_add, mul_add, h1_, h2_]
    have hαα : α * α = α ^ 2 := by ring
    rw [hαα]
    have hsx : Real.sqrt α * X ≤ X := by
      simpa using mul_le_mul_of_nonneg_right hsq hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ α ^ 2 := by positivity
    linarith
  have hXT : X ≤ α * T := by
    have h1_ : α * (α ^ (-(1 : ℝ)) * X) = X := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα, show (1 : ℝ) + (-(1 : ℝ)) = 0 by norm_num,
        Real.rpow_zero, one_mul]
    have h2_ : α * (α ^ (-(5 / 2 : ℝ)) * X ^ 2) = α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
      nth_rewrite 1 [← Real.rpow_one α]
      rw [← mul_assoc, ← Real.rpow_add hα,
        show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
    rw [hT, mul_add, mul_add, h1_, h2_]
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ α * α := by positivity
    nlinarith [hX]
  have hTnn : 0 ≤ T := by
    rw [hT]
    have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    have h1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) * X :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX
    linarith [hα.le]
  have hcoef : (0 : ℝ) < 1 / (2 * α) := by positivity
  have hST : 2 * S + X ≤ 3 * (α * T) := by linarith [hSle, hXT]
  have hmain : |mufunS α N0v Nv g| ≤ (1 / (2 * α)) * (K * (2 * S + X)) := by
    rw [hmu, abs_mul, abs_of_nonneg hcoef.le]
    exact mul_le_mul_of_nonneg_left htri hcoef.le
  have hkey : (1 / (2 * α)) * (K * (3 * (α * T))) = (3 / 2) * (K * T) := by
    field_simp
  calc |mufunS α N0v Nv g| ≤ (1 / (2 * α)) * (K * (2 * S + X)) := hmain
    _ ≤ (1 / (2 * α)) * (K * (3 * (α * T))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hST hK) hcoef.le
    _ = (3 / 2) * (K * T) := hkey
    _ ≤ 4 * (K * T) := by nlinarith [hK, hTnn]


end Work.Construction
end
end
-- ===== merged: Submission.Work.Construction.gronwall_exp_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction


end Work.Construction
end
-- ===== merged: Submission.Work.Construction.hasDerivAt_zvar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction


end Work.Construction
end
-- ===== merged: Submission.Work.Construction.le_of_deriv_le_of_cubic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cubic barrier lemma of the modulation chapter

This file proves the ODE-comparison ("barrier") estimate that bounds a continuously
differentiable function `φ` on `[0,∞)` from above by `y1`, given that on the right of the
origin its derivative is dominated by the cubic

`y ↦ -2 c y + C (α² + √α · y + α^{-3/2} y² + α^{-5/2} y³)`

which is *negative at* `y1`.  The point is that no sign hypothesis is needed away from `y1`:
if `φ` were to leave the region `(-∞, y1]` for the first time at a time `t`, then at that
instant `φ t = y1`, so the differential inequality forces `φ' t ≤ f (y1) < 0`, hence `φ`
strictly decreases just to the right of `t`, contradicting maximality of the crossing time.

The two auxiliary lemmas isolate the two real-analysis ingredients:

* `barrier_exists_right_lt_of_hasDerivAt_neg` — a strictly negative derivative at a point
  makes the function strictly decrease immediately to the right of it;
* `barrier_sSup_crossing_eq_y1` — the last time `φ ≤ y1` before a moment at which `φ > y1`
  is a genuine crossing point `φ t = y1`, lying strictly inside `(0, τ₀)`.
-/

open Set Filter Topology

namespace Work.Construction




end Work.Construction
end
-- ===== merged: Submission.Work.Cyl.FieldDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Derivatives of the no-swirl field `cylField ur uz`
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The two-variable chain rule -/

/-- The first slice of a differentiable two-variable function is differentiable. -/
theorem differentiableAt_slice_fst (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    DifferentiableAt ℝ (fun s : ℝ => f s z) r := by
  have hpair : HasFDerivAt (fun s : ℝ => ((s, z) : ℝ × ℝ))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) r :=
    (hasFDerivAt_id (x := r)).prodMk (hasFDerivAt_const (x := r) z)
  exact (hf.hasFDerivAt.comp r hpair).differentiableAt

/-- The second slice of a differentiable two-variable function is differentiable. -/
theorem differentiableAt_slice_snd (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    DifferentiableAt ℝ (fun s : ℝ => f r s) z := by
  have hpair : HasFDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) z :=
    (hasFDerivAt_const (x := z) r).prodMk (hasFDerivAt_id (x := z))
  exact (hf.hasFDerivAt.comp z hpair).differentiableAt

theorem fderiv_prod_apply_fst (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) (1, 0) = pdR f r z := by
  rw [fderiv_apply_eq_deriv_line _ _ _ hf]
  have hfun : (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) ((r, z) + t • (1, 0))) =
      fun t : ℝ => f (r + t) z := by
    funext t; simp
  rw [hfun, pdR]
  have hpair : HasFDerivAt (fun s : ℝ => ((s, z) : ℝ × ℝ))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) r :=
    (hasFDerivAt_id (x := r)).prodMk (hasFDerivAt_const (x := r) z)
  have hd : DifferentiableAt ℝ (fun s : ℝ => f s z) r :=
    (HasFDerivAt.comp (x := r) (f := fun s : ℝ => ((s, z) : ℝ × ℝ))
      (g := fun p : ℝ × ℝ => f p.1 p.2) hf.hasFDerivAt hpair).differentiableAt
  have hd' : DifferentiableAt ℝ (fun s : ℝ => f s z) (r + 0) := by simpa using hd
  have hshift : HasDerivAt (fun t : ℝ => r + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add r
  have h := hd'.hasFDerivAt.comp_hasDerivAt 0 hshift
  have hval : (fderiv ℝ (fun s : ℝ => f s z) (r + 0)) 1 = deriv (fun s : ℝ => f s z) r := by
    rw [show r + 0 = r from add_zero r]
    exact (hd.hasFDerivAt.hasDerivAt).deriv.symm
  change deriv ((fun s : ℝ => f s z) ∘ fun t : ℝ => r + t) 0 = deriv (fun r' : ℝ => f r' z) r
  rw [h.deriv, hval]

theorem fderiv_prod_apply_snd (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) (0, 1) = pdZ f r z := by
  rw [fderiv_apply_eq_deriv_line _ _ _ hf]
  have hfun : (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) ((r, z) + t • (0, 1))) =
      fun t : ℝ => f r (z + t) := by
    funext t; simp
  rw [hfun, pdZ]
  have hpair : HasFDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) z :=
    (hasFDerivAt_const (x := z) r).prodMk (hasFDerivAt_id (x := z))
  have hd : DifferentiableAt ℝ (fun s : ℝ => f r s) z :=
    (HasFDerivAt.comp (x := z) (f := fun s : ℝ => ((r, s) : ℝ × ℝ))
      (g := fun p : ℝ × ℝ => f p.1 p.2) hf.hasFDerivAt hpair).differentiableAt
  have hd' : DifferentiableAt ℝ (fun s : ℝ => f r s) (z + 0) := by simpa using hd
  have hshift : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add z
  have h := hd'.hasFDerivAt.comp_hasDerivAt 0 hshift
  have hval : (fderiv ℝ (fun s : ℝ => f r s) (z + 0)) 1 = deriv (fun s : ℝ => f r s) z := by
    rw [show z + 0 = z from add_zero z]
    exact (hd.hasFDerivAt.hasDerivAt).deriv.symm
  change deriv ((fun s : ℝ => f r s) ∘ fun t : ℝ => z + t) 0 = deriv (fun z' : ℝ => f r z') z
  rw [h.deriv, hval]

/-- Chain rule for the composition of a two-variable function with a pair of curves. -/
theorem hasDerivAt_comp_two (f : ℝ → ℝ → ℝ) (R Z : ℝ → ℝ) (r' z' t₀ : ℝ)
    (hf : DiffAt2 f (R t₀) (Z t₀)) (hR : HasDerivAt R r' t₀) (hZ : HasDerivAt Z z' t₀) :
    HasDerivAt (fun t => f (R t) (Z t))
      (pdR f (R t₀) (Z t₀) * r' + pdZ f (R t₀) (Z t₀) * z') t₀ := by
  have hpair : HasDerivAt (fun t : ℝ => (R t, Z t)) (r', z') t₀ := hR.prodMk hZ
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt t₀ hpair
  have hval : fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (R t₀, Z t₀) (r', z') =
      pdR f (R t₀) (Z t₀) * r' + pdZ f (R t₀) (Z t₀) * z' := by
    have h1 := fderiv_prod_apply_fst f (R t₀) (Z t₀) hf
    have h2 := fderiv_prod_apply_snd f (R t₀) (Z t₀) hf
    have hsplit : (r', z') = r' • ((1 : ℝ), (0 : ℝ)) + z' • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_smul, map_smul, h1, h2]
    ring
  rw [hval] at hcomp
  exact hcomp

/-! ## Coordinates of the shifted point -/

section LineFacts

variable (x : R3)

@[simp] lemma e0_apply_zero : (e0 : R3) 0 = 1 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e0_apply_one : (e0 : R3) 1 = 0 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e0_apply_two : (e0 : R3) 2 = 0 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_zero : (e1 : R3) 0 = 0 := by simp [e1, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_one : (e1 : R3) 1 = 1 := by simp [e1, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_two : (e1 : R3) 2 = 0 := by simp [e1, FiniteTimeSingularity.e]

@[simp] lemma add_smul_e0_apply_zero (t : ℝ) : (x + t • e0) 0 = x 0 + t := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e0_apply_one (t : ℝ) : (x + t • e0) 1 = x 1 := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e0_apply_two (t : ℝ) : (x + t • e0) 2 = x 2 := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_zero (t : ℝ) : (x + t • e1) 0 = x 0 := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_one (t : ℝ) : (x + t • e1) 1 = x 1 + t := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_two (t : ℝ) : (x + t • e1) 2 = x 2 := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_zero (t : ℝ) : (x + t • eZ) 0 = x 0 := by
  simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_one (t : ℝ) : (x + t • eZ) 1 = x 1 := by
  simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_two (t : ℝ) : (x + t • eZ) 2 = x 2 + t := by
  simp [eZ, FiniteTimeSingularity.e]

lemma radSq_add_smul_e0 (t : ℝ) : radSq (x + t • e0) = (x 0 + t) ^ 2 + x 1 ^ 2 := by
  change (x + t • e0) 0 ^ 2 + (x + t • e0) 1 ^ 2 = (x 0 + t) ^ 2 + x 1 ^ 2
  rw [add_smul_e0_apply_zero, add_smul_e0_apply_one]
lemma radSq_add_smul_e1 (t : ℝ) : radSq (x + t • e1) = x 0 ^ 2 + (x 1 + t) ^ 2 := by
  change (x + t • e1) 0 ^ 2 + (x + t • e1) 1 ^ 2 = x 0 ^ 2 + (x 1 + t) ^ 2
  rw [add_smul_e1_apply_zero, add_smul_e1_apply_one]
lemma radSq_add_smul_eZ (t : ℝ) : radSq (x + t • eZ) = radSq x := by
  change (x + t • eZ) 0 ^ 2 + (x + t • eZ) 1 ^ 2 = radSq x
  rw [add_smul_eZ_apply_zero, add_smul_eZ_apply_one]
  rfl

lemma radial_add_smul_e0 (t : ℝ) : radial (x + t • e0) = Real.sqrt ((x 0 + t) ^ 2 + x 1 ^ 2) := by
  rw [radial, radSq_add_smul_e0]
lemma radial_add_smul_e1 (t : ℝ) : radial (x + t • e1) = Real.sqrt (x 0 ^ 2 + (x 1 + t) ^ 2) := by
  rw [radial, radSq_add_smul_e1]
lemma radial_add_smul_eZ (t : ℝ) : radial (x + t • eZ) = radial x := by
  rw [radial, radSq_add_smul_eZ, ← radial]

@[simp] lemma axial_add_smul_e0 (t : ℝ) : axial (x + t • e0) = axial x := by
  simp [axial]
@[simp] lemma axial_add_smul_e1 (t : ℝ) : axial (x + t • e1) = axial x := by
  simp [axial]
lemma axial_add_smul_eZ (t : ℝ) : axial (x + t • eZ) = axial x + t := by
  simp [axial]

end LineFacts

/-! ## Derivatives of the coordinate functions along coordinate lines -/

theorem hasDerivAt_radial_line_e0 (x : R3) (hr : radial x ≠ 0) :
    HasDerivAt (fun t : ℝ => radial (x + t • e0)) (x 0 / radial x) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have hsq : HasDerivAt (fun t : ℝ => (x 0 + t) * (x 0 + t)) (2 * x 0) 0 := by
    have hm := hlin.mul hlin
    convert hm using 1
    ring
  have hinner : HasDerivAt (fun t : ℝ => (x 0 + t) ^ 2 + x 1 ^ 2) (2 * x 0) 0 := by
    have h2 : (fun t : ℝ => (x 0 + t) ^ 2 + x 1 ^ 2) =
        fun t : ℝ => (x 0 + t) * (x 0 + t) + x 1 ^ 2 := by
      funext t; ring
    rw [h2]
    simpa using hsq.add_const (x 1 ^ 2)
  have hx0 : (x 0 + (0 : ℝ)) ^ 2 + x 1 ^ 2 ≠ 0 := by
    rw [add_zero]
    change radSq x ≠ 0
    rw [← radial_sq]
    exact pow_ne_zero 2 hr
  have hsqrt := hinner.sqrt hx0
  rw [show (fun t : ℝ => radial (x + t • e0)) =
      fun t : ℝ => Real.sqrt ((x 0 + t) ^ 2 + x 1 ^ 2) from funext fun t => radial_add_smul_e0 x t]
  convert hsqrt using 1
  rw [add_zero, radial, radSq]
  field_simp

theorem hasDerivAt_radial_line_e1 (x : R3) (hr : radial x ≠ 0) :
    HasDerivAt (fun t : ℝ => radial (x + t • e1)) (x 1 / radial x) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
  have hsq : HasDerivAt (fun t : ℝ => (x 1 + t) * (x 1 + t)) (2 * x 1) 0 := by
    have hm := hlin.mul hlin
    convert hm using 1
    ring
  have hinner : HasDerivAt (fun t : ℝ => x 0 ^ 2 + (x 1 + t) ^ 2) (2 * x 1) 0 := by
    have h2 : (fun t : ℝ => x 0 ^ 2 + (x 1 + t) ^ 2) =
        fun t : ℝ => x 0 ^ 2 + (x 1 + t) * (x 1 + t) := by
      funext t; ring
    rw [h2]
    simpa using (hsq.const_add (x 0 ^ 2))
  have hx0 : x 0 ^ 2 + (x 1 + (0 : ℝ)) ^ 2 ≠ 0 := by
    rw [add_zero]
    change radSq x ≠ 0
    rw [← radial_sq]
    exact pow_ne_zero 2 hr
  have hsqrt := hinner.sqrt hx0
  rw [show (fun t : ℝ => radial (x + t • e1)) =
      fun t : ℝ => Real.sqrt (x 0 ^ 2 + (x 1 + t) ^ 2) from funext fun t => radial_add_smul_e1 x t]
  convert hsqrt using 1
  rw [add_zero, radial, radSq]
  field_simp

theorem hasDerivAt_radial_line_eZ (x : R3) :
    HasDerivAt (fun t : ℝ => radial (x + t • eZ)) 0 0 := by
  have h : (fun t : ℝ => radial (x + t • eZ)) = fun _ => radial x := by
    funext t; rw [radial_add_smul_eZ]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (radial x)

theorem hasDerivAt_axial_line_e0 (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • e0)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • e0)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_e0]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

theorem hasDerivAt_axial_line_e1 (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • e1)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • e1)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_e1]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

theorem hasDerivAt_axial_line_eZ (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • eZ)) 1 0 := by
  have h : (fun t : ℝ => axial (x + t • eZ)) = fun t => axial x + t := by
    funext t; rw [axial_add_smul_eZ]
  rw [h]
  simpa using (hasDerivAt_id (0 : ℝ)).const_add (axial x)

/-! ## The composite chain rule along coordinate lines -/

theorem hasDerivAt_comp_cyl_e0 (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • e0)) (axial (x + t • e0)))
      (pdR g (radial x) (axial x) * (x 0 / radial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • e0)) (axial (x + (0:ℝ) • e0)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • e0))
    (fun t : ℝ => axial (x + t • e0)) (x 0 / radial x) (0 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_e0 x (ne_of_gt hr)) (hasDerivAt_axial_line_e0 x)
  simpa using h

theorem hasDerivAt_comp_cyl_e1 (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • e1)) (axial (x + t • e1)))
      (pdR g (radial x) (axial x) * (x 1 / radial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • e1)) (axial (x + (0:ℝ) • e1)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • e1))
    (fun t : ℝ => axial (x + t • e1)) (x 1 / radial x) (0 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_e1 x (ne_of_gt hr)) (hasDerivAt_axial_line_e1 x)
  simpa using h

theorem hasDerivAt_comp_cyl_eZ (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (_hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • eZ)) (axial (x + t • eZ)))
      (pdZ g (radial x) (axial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • eZ)) (axial (x + (0:ℝ) • eZ)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • eZ))
    (fun t : ℝ => axial (x + t • eZ)) (0 : ℝ) (1 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_eZ x) (hasDerivAt_axial_line_eZ x)
  simpa using h


/-! ## The nine partial derivatives of `cylField ur uz` -/


lemma pdR_redR {ur : ℝ → ℝ → ℝ} {r z : ℝ} (hur : DiffAt2 ur r z) (hr : r ≠ 0) :
    pdR (redR ur) r z = pdR ur r z / r - ur r z / r ^ 2 := by
  have hf : DifferentiableAt ℝ (fun r' : ℝ => ur r' z) r := differentiableAt_slice_fst ur r z hur
  have hg : DifferentiableAt ℝ (fun r' : ℝ => r') r := differentiableAt_id
  have h2 : deriv ((fun r' : ℝ => ur r' z) / (fun r' : ℝ => r')) r =
      (deriv (fun r' : ℝ => ur r' z) r * r - ur r z * deriv (fun r' : ℝ => r') r) / r ^ 2 :=
    deriv_div hf hg hr
  have h3 : deriv (fun r' : ℝ => r') r = 1 := by simp
  rw [pdR, show (fun r' : ℝ => redR ur r' z) =
    ((fun r' : ℝ => ur r' z) / fun r' : ℝ => r') from rfl, h2, h3, pdR]
  field_simp

lemma pdZ_redR (ur : ℝ → ℝ → ℝ) (r z : ℝ) : pdZ (redR ur) r z = pdZ ur r z / r := by
  have hfun : (fun z' : ℝ => redR ur r z') = fun z' : ℝ => ur r z' / r := by funext z'; rfl
  rw [pdZ, hfun, pdZ, deriv_div_const]



lemma cylField_apply_two' (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 2 = uz (radial x) (axial x) := cylField_two ur uz x

theorem pd_cylField_00 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 0) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 ^ 2 / radial x)
        + redR ur (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e0 ur x hur hr
  have hlin : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have hnum := hcomp.mul hlin
  have hden := hasDerivAt_radial_line_e0 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e0)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 0) = fun t : ℝ =>
      ur (radial (x + t • e0)) (axial (x + t • e0)) * (x 0 + t) / radial (x + t • e0) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_zero]
    simp only [add_smul_e0_apply_zero, add_smul_e0_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e0)) (axial (x + t • e0))) *
      fun t : ℝ => x 0 + t) / fun t : ℝ => radial (x + t • e0)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_01 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 1) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 * x 1 / radial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e0 ur x hur hr
  have hconst : HasDerivAt (fun _ : ℝ => x 1) 0 0 := hasDerivAt_const (0 : ℝ) (x 1)
  have hnum := hcomp.mul hconst
  have hden := hasDerivAt_radial_line_e0 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e0)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 1) = fun t : ℝ =>
      ur (radial (x + t • e0)) (axial (x + t • e0)) * x 1 / radial (x + t • e0) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_one]
    simp only [add_smul_e0_apply_zero, add_smul_e0_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e0)) (axial (x + t • e0))) *
      fun _ : ℝ => x 1) / fun t : ℝ => radial (x + t • e0)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_02 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 2) x =
      pdR uz (radial x) (axial x) * (x 0 / radial x) := by
  have hcomp := hasDerivAt_comp_cyl_e0 uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 2) =
      fun t : ℝ => uz (radial (x + t • e0)) (axial (x + t • e0)) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

theorem pd_cylField_10 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 0) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 * x 1 / radial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e1 ur x hur hr
  have hconst : HasDerivAt (fun _ : ℝ => x 0) 0 0 := hasDerivAt_const (0 : ℝ) (x 0)
  have hnum := hcomp.mul hconst
  have hden := hasDerivAt_radial_line_e1 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e1)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 0) = fun t : ℝ =>
      ur (radial (x + t • e1)) (axial (x + t • e1)) * x 0 / radial (x + t • e1) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_zero]
    simp only [add_smul_e1_apply_zero, add_smul_e1_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e1)) (axial (x + t • e1))) *
      fun _ : ℝ => x 0) / fun t : ℝ => radial (x + t • e1)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_11 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 1) x =
      pdR (redR ur) (radial x) (axial x) * (x 1 ^ 2 / radial x)
        + redR ur (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e1 ur x hur hr
  have hlin : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
  have hnum := hcomp.mul hlin
  have hden := hasDerivAt_radial_line_e1 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e1)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 1) = fun t : ℝ =>
      ur (radial (x + t • e1)) (axial (x + t • e1)) * (x 1 + t) / radial (x + t • e1) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_one]
    simp only [add_smul_e1_apply_zero, add_smul_e1_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e1)) (axial (x + t • e1))) *
      fun t : ℝ => x 1 + t) / fun t : ℝ => radial (x + t • e1)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_12 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 2) x =
      pdR uz (radial x) (axial x) * (x 1 / radial x) := by
  have hcomp := hasDerivAt_comp_cyl_e1 uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 2) =
      fun t : ℝ => uz (radial (x + t • e1)) (axial (x + t • e1)) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

theorem pd_cylField_20 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 0) x =
      pdZ (redR ur) (radial x) (axial x) * x 0 := by
  have hcomp := hasDerivAt_comp_cyl_eZ ur x hur hr
  have hd : HasDerivAt (fun t : ℝ => ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x)
      (pdZ ur (radial x) (axial x) / radial x) 0 := hcomp.div_const (radial x)
  have h2 : HasDerivAt (fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 0)
      (pdZ ur (radial x) (axial x) / radial x * x 0) 0 := hd.mul_const (x 0)
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 0) = fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 0 := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_zero, radial_add_smul_eZ]
    simp only [add_smul_eZ_apply_zero]
    ring
  rw [pd, hfun, h2.deriv, pdZ_redR]

theorem pd_cylField_21 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 1) x =
      pdZ (redR ur) (radial x) (axial x) * x 1 := by
  have hcomp := hasDerivAt_comp_cyl_eZ ur x hur hr
  have hd : HasDerivAt (fun t : ℝ => ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x)
      (pdZ ur (radial x) (axial x) / radial x) 0 := hcomp.div_const (radial x)
  have h2 : HasDerivAt (fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 1)
      (pdZ ur (radial x) (axial x) / radial x * x 1) 0 := hd.mul_const (x 1)
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 1) = fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 1 := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_one, radial_add_smul_eZ]
    simp only [add_smul_eZ_apply_one]
    ring
  rw [pd, hfun, h2.deriv, pdZ_redR]

theorem pd_cylField_22 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 2) x = pdZ uz (radial x) (axial x) := by
  have hcomp := hasDerivAt_comp_cyl_eZ uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 2) =
      fun t : ℝ => uz (radial (x + t • eZ)) (axial (x + t • eZ)) := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

/-! ## Differentiability of the field -/

lemma differentiableAt_radial (x : R3) (hr : radial x ≠ 0) : DifferentiableAt ℝ radial x := by
  have h1 : DifferentiableAt ℝ (fun y : R3 => radSq y) x := by
    have h : (fun y : R3 => radSq y) = fun y : R3 => y 0 ^ 2 + y 1 ^ 2 := by
      funext y; rfl
    rw [h]
    fun_prop
  have h2 : (fun y : R3 => radSq y) x ≠ 0 := by
    have : radSq x ≠ 0 := by rw [← radial_sq]; exact pow_ne_zero 2 hr
    simpa using this
  have h3 := h1.sqrt h2
  convert h3 using 1
  funext y; rfl

lemma differentiableAt_axial (x : R3) : DifferentiableAt ℝ axial x := by
  have h : axial = fun y : R3 => y 2 := rfl
  rw [h]
  exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 2).differentiableAt

lemma differentiableAt_radialVec (x : R3) : DifferentiableAt ℝ radialVec x := by
  have hcoord : ∀ j : Fin 3, DifferentiableAt ℝ (fun y : R3 => y j) x := fun j =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x j).differentiableAt
  rw [show radialVec = fun y : R3 => (y 0) • e0 + (y 1) • e1 from by
    funext y
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [radialVec, e0, e1, FiniteTimeSingularity.e]]
  exact ((hcoord 0).smul_const e0).add ((hcoord 1).smul_const e1)

theorem differentiableAt_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    DifferentiableAt ℝ (cylField ur uz) x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hrad := differentiableAt_radial x hrne
  have hax := differentiableAt_axial x
  have hpair : DifferentiableAt ℝ (fun y : R3 => (radial y, axial y)) x :=
    (hrad.hasFDerivAt.prodMk hax.hasFDerivAt).differentiableAt
  have hur' : DifferentiableAt ℝ (fun y : R3 => ur (radial y) (axial y)) x := by
    have h := hur.comp x hpair
    convert h using 1
    funext y; rfl
  have huz' : DifferentiableAt ℝ (fun y : R3 => uz (radial y) (axial y)) x := by
    have h := huz.comp x hpair
    convert h using 1
    funext y; rfl
  have hinv : DifferentiableAt ℝ (fun y : R3 => (radial y)⁻¹) x :=
    hrad.inv (by simpa using hrne)
  have hA : DifferentiableAt ℝ (fun y : R3 => ur (radial y) (axial y) * (radial y)⁻¹) x :=
    hur'.mul hinv
  rw [show cylField ur uz = fun y : R3 =>
      (ur (radial y) (axial y) * (radial y)⁻¹) • radialVec y + uz (radial y) (axial y) • eZ from by
    funext y
    rw [cylField, div_eq_mul_inv]]
  exact (hA.smul (differentiableAt_radialVec x)).add
    (huz'.smul (differentiableAt_const eZ))

/-! ## The divergence of the field -/

theorem div_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    FiniteTimeSingularity.div (cylField ur uz) x =
      pdR ur (radial x) (axial x) + ur (radial x) (axial x) / radial x
        + pdZ uz (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [div_eq_sum_partials _ _ hd, Fin.sum_univ_three]
  change pd 0 (fun y => (cylField ur uz y) 0) x + pd 1 (fun y => (cylField ur uz y) 1) x
    + pd 2 (fun y => (cylField ur uz y) 2) x = _
  rw [pd_cylField_00 ur uz x hur hr, pd_cylField_11 ur uz x hur hr, pd_cylField_22 ur uz x huz hr,
    pdR_redR hur hrne]
  simp only [redR]
  have h2 : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  field_simp
  linear_combination
    (pdR ur (radial x) (axial x) * radial x - ur (radial x) (axial x)) * h2

/-! ## The curl of the field -/

theorem vorticity_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    FiniteTimeSingularity.vorticity (cylField ur uz) x =
      vortTheta ur uz (radial x) (axial x) • eTheta x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [vorticity_eq_coordinates]
  refine ext_coord ?_ ?_ ?_
  · show (fderiv ℝ (cylField ur uz) x (basisVec 1)) 2
        - (fderiv ℝ (cylField ur uz) x (basisVec 2)) 1
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 0
    rw [fderiv_apply_coord (cylField ur uz) x 1 2 hd,
      fderiv_apply_coord (cylField ur uz) x 2 1 hd,
      pd_cylField_12 ur uz x huz hr, pd_cylField_21 ur uz x hur hr, pdZ_redR]
    simp only [vortTheta, eTheta_apply_zero, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, redR]
    field_simp
    nlinarith [radial_sq x]
  · show (fderiv ℝ (cylField ur uz) x (basisVec 2)) 0
        - (fderiv ℝ (cylField ur uz) x (basisVec 0)) 2
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 1
    rw [fderiv_apply_coord (cylField ur uz) x 2 0 hd,
      fderiv_apply_coord (cylField ur uz) x 0 2 hd,
      pd_cylField_20 ur uz x hur hr, pd_cylField_02 ur uz x huz hr, pdZ_redR]
    simp only [vortTheta, eTheta_apply_one, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, redR]
    field_simp
  · show (fderiv ℝ (cylField ur uz) x (basisVec 0)) 1
        - (fderiv ℝ (cylField ur uz) x (basisVec 1)) 0
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 2
    rw [fderiv_apply_coord (cylField ur uz) x 0 1 hd,
      fderiv_apply_coord (cylField ur uz) x 1 0 hd,
      pd_cylField_01 ur uz x hur hr, pd_cylField_10 ur uz x hur hr]
    simp only [vortTheta, eTheta_apply_two, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    ring



end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.abs_inner_angularVec_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The inner product of two angular vectors `r e_θ` is bounded by the product of the distances
of the two points to the symmetry axis: this is Cauchy--Schwarz together with
`‖r e_θ‖ = r` (`norm_angularVec`). -/
theorem abs_inner_angularVec_le (x y : Work.Cyl.R3) :
    |inner ℝ (Work.Cyl.angularVec x) (Work.Cyl.angularVec y)|
      ≤ Work.Cyl.radial x * Work.Cyl.radial y := by
  have h := abs_real_inner_le_norm (angularVec x) (angularVec y)
  rwa [norm_angularVec x, norm_angularVec y] at h

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.dist_mid_neg_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl







/-- If `a` lies in the closed upper half space and `b` in the open lower half space, then both
`a` and the reflection `reflZ b` are at least as close to the orthogonal projection
`m = (b₀, b₁, 0)` of `b` onto the plane `x₃ = 0` as `a` and `b` are to each other. -/
theorem dist_mid_neg_le {a b : Work.Cyl.R3} (ha : 0 ≤ a 2) (hb : b 2 < 0) :
    dist a (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b ∧
      dist (Work.Cyl.reflZ b) (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b := by
  set m : Work.Cyl.R3 := !₂[b 0, b 1, (0:ℝ)] with hm
  have hm0 : m 0 = b 0 := by simp [hm]
  have hm1 : m 1 = b 1 := by simp [hm]
  have hm2 : m 2 = 0 := by simp [hm]
  have hr0 : (Work.Cyl.reflZ b) 0 = b 0 := by simp [Work.Cyl.reflZ]
  have hr1 : (Work.Cyl.reflZ b) 1 = b 1 := by simp [Work.Cyl.reflZ]
  have hr2 : (Work.Cyl.reflZ b) 2 = - b 2 := by simp [Work.Cyl.reflZ]
  constructor
  · -- `(a₂)² ≤ (a₂ - b₂)²` because `a₂ ≥ 0 > b₂`; the remaining coordinates are unchanged.
    have h1 : dist a m ^ 2 ≤ dist a b ^ 2 := by
      rw [Work.Cyl.dist_sq_coords, Work.Cyl.dist_sq_coords, hm0, hm1, hm2]
      nlinarith [ha, hb, sq_nonneg (b 2), sq_nonneg (a 2)]
    nlinarith [dist_nonneg (x := a) (y := m), dist_nonneg (x := a) (y := b), h1]
  · -- Here the distances to `m` only differ in the third coordinate: `(b₂)² ≤ (a₂ - b₂)²`.
    have h1 : dist (Work.Cyl.reflZ b) m ^ 2 ≤ dist a b ^ 2 := by
      rw [Work.Cyl.dist_sq_coords, Work.Cyl.dist_sq_coords, hr0, hr1, hr2, hm0, hm1, hm2]
      nlinarith [ha, hb, sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    nlinarith [dist_nonneg (x := Work.Cyl.reflZ b) (y := m), dist_nonneg (x := a) (y := b), h1]

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.dist_mid_pos_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSimpArgs false

namespace Work.Cyl

/-!
# The "positive-side" midpoint estimate

For `a` with `a 2 < 0` and `b` with `0 ≤ b 2`, the projection `m = (b 0, b 1, 0)` of `b` onto the
plane `x₃ = 0` is closer to `b` and to the reflection `reflZ a = (a 0, a 1, -a 2)` than `a` and `b`
are to each other:

`dist (reflZ a) m ≤ dist a b`  and  `dist b m ≤ dist a b`.

Both are pure coordinate inequalities.  Writing `u = a 0 - b 0`, `v = a 1 - b 1`,

* `dist (reflZ a) m ^ 2 = u ^ 2 + v ^ 2 + (a 2) ^ 2 ≤ u ^ 2 + v ^ 2 + (a 2 - b 2) ^ 2 = dist a b ^ 2`,
  since the difference of the right and left sides is `b 2 * (b 2 - 2 * a 2) ≥ 0` (`b 2 ≥ 0` and
  `b 2 - 2 * a 2 > 0` because `a 2 < 0`);
* `dist b m ^ 2 = (b 2) ^ 2 ≤ u ^ 2 + v ^ 2 + (a 2 - b 2) ^ 2 = dist a b ^ 2`, since the difference
  is `u ^ 2 + v ^ 2 + (a 2) ^ 2 - 2 * a 2 * b 2 ≥ 0` (`-2 * a 2 * b 2 ≥ 0` as `a 2 < 0 ≤ b 2`).

-/

private lemma dist_sq_reflZ_mid (a b : R3) :
    dist (reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ^ 2
      = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2) ^ 2 := by
  rw [dist_sq_coords]
  simp only [reflZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private lemma dist_sq_mid (b : R3) :
    dist b (!₂[b 0, b 1, (0:ℝ)]) ^ 2 = (b 2) ^ 2 := by
  rw [dist_sq_coords]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private lemma dist_sq_ab (a b : R3) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2 := by
  rw [dist_sq_coords]

theorem dist_mid_pos_le {a b : Work.Cyl.R3} (ha : a 2 < 0) (hb : 0 ≤ b 2) :
    dist (Work.Cyl.reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b ∧
      dist b (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b := by
  have h1 : dist (reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ^ 2 ≤ dist a b ^ 2 := by
    rw [dist_sq_reflZ_mid, dist_sq_ab]
    have hmul : 0 ≤ b 2 * (b 2 - 2 * a 2) := mul_nonneg hb (by linarith)
    nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
  have h2 : dist b (!₂[b 0, b 1, (0:ℝ)]) ^ 2 ≤ dist a b ^ 2 := by
    rw [dist_sq_mid, dist_sq_ab]
    have hmul : 0 ≤ 2 * (-a 2) * b 2 := mul_nonneg (by linarith) hb
    nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2)]
  constructor
  · have h := sq_le_sq.mp h1
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
  · have h := sq_le_sq.mp h2
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.dist_reflZ_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `reflZ` is the reflection of the axial coordinate, hence an isometry: it preserves distances
(of course even with equality). -/
theorem dist_reflZ_le (x y : Work.Cyl.R3) : dist (Work.Cyl.reflZ x) (Work.Cyl.reflZ y) ≤ dist x y := by
  have hsq : dist (reflZ x) (reflZ y) ^ 2 = dist x y ^ 2 := by
    rw [dist_sq_coords, dist_sq_coords]
    simp [reflZ]
    ring
  have h : dist (reflZ x) (reflZ y) = dist x y := by
    nlinarith [dist_nonneg (x := reflZ x) (y := reflZ y), dist_nonneg (x := x) (y := y)]
  rw [h]

end Work.Cyl
end
-- ===== merged: Submission.Work.Elliptic.DivSinIdentitySetup =====
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

/-! ## The four integrands and the primitive -/







/-! ## Elementary facts -/


theorem eta_pos' : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos

theorem eta_lt_one' : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one



theorem one_sub_eta_pos : (0 : ℝ) < 1 - Work.Spaces.eta := by linarith [eta_lt_one']

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) ≠ 0` on `(0, π/2)`. -/
theorem sin_two_ne_zero' {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (sin_two_pos hθ)





/-- Almost every point of `Iθ` is an interior point of `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  simp only [Work.Spaces.Iθ]
  rw [Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]
  exact self_mem_ae_restrict measurableSet_Ioo

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinL2Est =====
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

/-! ## Auxiliary lemmas for `DivSinL2Est`

`DivSinL2Est` bounds the weighted `L²`-norm `∫_{Iθ} h² sin(2θ)^{2-γ}` of a smooth slice
`h` vanishing at `θ = 0` and `θ = π/2` by the *more* singular quantity
`∫_{Iθ} (deriv h)² / sin(2θ)^η`, with `η = 99/100 < 1` and `γ = 1 + α/10 ≤ 11/10`.

The three ingredients (all one-dimensional, all elementary):

* `smoothSlice_contDiffOn_one` — a `SmoothSlice` is `C¹` on the closed interval `Iθ`;
* `integral_sq_mul_rpow_le` — on `Iθ` the base `sin(2θ)` lies in `[0,1]` and the exponent
  `2 - γ` is nonnegative, so the weight `sin(2θ)^{2-γ}` is `≤ 1` and may be dropped;
* `integrableOn_deriv_sq_div_sin` and `integral_deriv_sq_le_div_sin` — the weighted
  derivative integral is honest (`η < 1`) and dominates the unweighted one.

The Poincaré step `∫_{Iθ} h² ≤ K ∫_{Iθ} (deriv h)²` is the already-proved
`Work.Elliptic.sin_l2_weight_bound` at `η = 0`. -/


/-- On `Iθ`, `sin (2 * θ)` lies in `[0,1]`. -/
private lemma sin_two_nonneg_of_mem_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩





end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinL2EstUnif =====
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

/-! ## A uniform weighted `L²` estimate for angular slices

`DivSinL2EstUnif` is the *uniform-in-α* form of `DivSinL2Est`: a single constant `C`
works for every `α ∈ (0,1]`.  This is what is needed when `α` is not fixed in advance
(as in the construction of the self-similar profile).

The ingredients are exactly those of `DivSinL2Est`, and none of them depends on `α`:

* the weight `sin(2θ)^{2-γ(α)}` with `γ(α) = 1 + α/10 ≤ 11/10` is `≤ 1` on `Iθ`
  (`DivSinL2WtCmp`), so it may simply be dropped;
* the unweighted Poincaré/Hardy inequality `∫_{Iθ} h² ≤ K ∫_{Iθ} (deriv h)²` holds with
  the absolute constant `K = 50 π` (`sin_l2_weight_bound` at `η = 0`);
* since `η = 99/100 < 1`, `sin(2θ)^{-η} ≥ 1` on `Iθ`, so the weighted derivative integral
  dominates the unweighted one.

Thus `C = 50 π` works for all `α`. -/


/-- On `Iθ`, `sin (2 * θ) ≥ 0`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩




end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinPhiBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedSimpArgs false

/-! ## Auxiliary derivatives -/

private lemma deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have h3 := h2.pow 2
  have h4 : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 2 * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2) := h3.deriv
  rw [h4]; ring


/-! ## The first three iterates of `D_θ` applied to `θ ↦ 2 cos 2θ` -/




/-! ## The bound -/


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.DivSinRec =====
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

/-! ## `Lop = Dth1` as a derivation-like operator -/

/-- The class of functions that are `C^∞` on `U` is closed under the algebraic
operations of `Work.Spaces.FunClass`. -/
private lemma lop_funClass (U : Set ℝ) :
    Work.Spaces.FunClass (fun u : ℝ → ℝ => ContDiffOn ℝ ⊤ u U) where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hA.const_smul c

/-- `Work.Spaces.Lop = Dth1` is a derivation-like operator on the open set `U`. -/
private lemma lop_derivLike (U : Set ℝ) (hU : IsOpen U) :
    Work.Spaces.DerivLike U (fun u : ℝ → ℝ => ContDiffOn ℝ ⊤ u U) Work.Spaces.Lop where
  add := by
    intro A B hA hB θ hθ
    have dA : DifferentiableAt ℝ A θ :=
      (hA.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
    have dB : DifferentiableAt ℝ B θ :=
      (hB.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
    show Real.sin (2 * θ) * deriv (A + B) θ
        = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
    rw [show deriv (A + B) θ = deriv A θ + deriv B θ from by
      simpa only [Pi.add_apply] using deriv_add dA dB]
    ring
  mul := by
    intro A B hA hB θ hθ
    exact Work.Spaces.Lop_mul A B θ
      ((hA.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp))
      ((hB.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp))
  congr := by
    intro A B hAB θ hθ
    have hev : A =ᶠ[nhds θ] B := by
      filter_upwards [hU.mem_nhds hθ] with x hx
      exact hAB hx
    show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
    rw [hev.deriv_eq]
  preserve := by
    intro A hA
    have hderiv : ContDiffOn ℝ ⊤ (deriv A) U := hA.deriv_of_isOpen hU le_top
    have hsin : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
    exact hsin.mul hderiv
  smul := by
    intro c A hA θ hθ
    show Real.sin (2 * θ) * deriv (fun p => c * A p) θ
        = c * (Real.sin (2 * θ) * deriv A θ)
    rw [deriv_const_mul_field c]
    ring

/-- The iterates of `Lop` are linear on `C^∞`-functions of an open set. -/
private lemma lop_iter_sub {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ u U) (hv : ContDiffOn ℝ ⊤ v U) (n : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[n] (u - v))
      (fun θ => Work.Spaces.Lop^[n] u θ - Work.Spaces.Lop^[n] v θ) U := by
  have hD := lop_derivLike U hU
  have hP := lop_funClass U
  have hw : ContDiffOn ℝ ⊤ (fun p => (-1 : ℝ) * v p) U := hP.smul (-1) v hv
  have h1 := Work.Spaces.DerivLike.iterate_add hD n hu hw
  have h2 := Work.Spaces.DerivLike.iterate_smul hD n (-1) hv
  have hfun : (u - v) = (u + fun p => (-1 : ℝ) * v p) := by
    funext p; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, neg_one_mul]
  rw [hfun]
  refine h1.trans ?_
  intro θ hθ
  have h2θ := h2 hθ
  simp only [Pi.add_apply]
  rw [h2θ]
  ring

/-- `Dth1Iter n f` is the `n`-th iterate of `Work.Spaces.Lop` applied to `f`. -/
lemma Dth1Iter_eq_iterate_Lop (n : ℕ) (f : ℝ → ℝ) :
    Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Dth1Iter_succ, ih, Function.iterate_succ_apply']
      rfl

/-! ## Differentiating the angular quotient -/

/-- `D_θ(h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on `(0, π/2)`. -/
private lemma Lop_SinQ_eqOn {h : ℝ → ℝ} (hsm : SmoothSlice h) :
    Set.EqOn (Work.Spaces.Lop (SinQ h))
      (fun θ => deriv h θ - 2 * Real.cos (2 * θ) * SinQ h θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU hne
  have hneθ : ∀ᶠ x in nhds θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * SinQ h x) =ᶠ[nhds θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * SinQ h x) θ = deriv h θ := heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (SinQ h) θ :=
    (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * SinQ h θ
        + Real.sin (2 * θ) * deriv (SinQ h) θ :=
    deriv_mul dsin dg
  rw [deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (SinQ h) θ = deriv h θ - 2 * Real.cos (2 * θ) * SinQ h θ
  rw [← hdeq, hprod]
  ring

/-! ## The recursion -/

theorem DivSinRec (i : ℕ) (h : ℝ → ℝ) (hi : 1 ≤ i) (hsm : Work.Elliptic.SmoothSlice h)
    (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ l ∈ Finset.range i, (Nat.choose (i - 1) l : ℝ) *
            (Work.Elliptic.Dth1Iter (i - 1 - l) (fun θ => 2 * Real.cos (2 * θ)) θ) *
            (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU hne
  have hφU : ContDiffOn ℝ ⊤ (fun x : ℝ => 2 * Real.cos (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hderU : ContDiffOn ℝ ⊤ (deriv h) (Set.Ioo 0 (Real.pi / 2)) := hsmU.deriv_of_isOpen hU le_top
  have hφgU : ContDiffOn ℝ ⊤ ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := hφU.mul hgU
  have hD := lop_derivLike (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
  have hEq : Set.EqOn (Work.Spaces.Lop (SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ)
      (Set.Ioo 0 (Real.pi / 2)) := Lop_SinQ_eqOn hsm
  have h1 : Work.Spaces.Lop^[j + 1] (SinQ h) θ
      = Work.Spaces.Lop^[j]
          (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ) θ := by
    rw [Function.iterate_succ_apply]
    exact (Work.Spaces.DerivLike.iterate_congr hD j hEq) hθ
  have h2 : Work.Spaces.Lop^[j]
        (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - Work.Spaces.Lop^[j] ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h) θ :=
    (lop_iter_sub hU hderU hφgU j) hθ
  have h3 : Work.Spaces.Lop^[j] ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h) θ
      = ∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ)
          * (Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ)
          * (Work.Spaces.Lop^[l] (SinQ h) θ) := by
    have hL := Work.Spaces.Lop_iter_mul_eqOn (SinQ h) (fun x : ℝ => 2 * Real.cos (2 * x))
      (Set.Ioo 0 (Real.pi / 2)) hU hgU hφU j
    have hcomm : (SinQ h) * (fun x : ℝ => 2 * Real.cos (2 * x))
        = (fun x : ℝ => 2 * Real.cos (2 * x)) * (SinQ h) := by
      funext x; exact mul_comm _ _
    rw [hcomm] at hL
    rw [hL hθ]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hstep : Work.Spaces.Lop^[j + 1] (SinQ h) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - ∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ)
            * (Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ)
            * (Work.Spaces.Lop^[l] (SinQ h) θ) := by
    rw [h1, h2, h3]
  simp only [Dth1Iter_eq_iterate_Lop]
  exact hstep

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.Fstar_orthSource =====
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

/-- The angular weight `sinCos2` is continuous. -/
lemma continuous_sinCos2 : Continuous (fun θ : ℝ => sinCos2 θ) := by
  simp only [sinCos2]; fun_prop


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.Gsing_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- The algebraic identity solved by the singular term `G = Gstar + Gbar`:
`α²z²(Gstar + Gbar)'' + α(5+α)z(Gstar + Gbar)' = (15/4) F_*`.

Written out, `DDGstar`, `DDGbar` are the explicit second derivatives and `DGstar`,
`DGbar` the explicit first derivatives of `Gstar`, `Gbar` (`Work.Elliptic.GsingFuncs`).
The `Gstar`-part contributes `(3αz/4)·(F_*)'(z) + (15/4) F_*(z)` and the `Gbar`-part
contributes `-(3αz/4)·(F_*)'(z)`; the cancellation of the `(F_*)'`-terms and of the
homogeneous `J`-terms is exactly the content of the identity. -/
theorem Gsing_algebra (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (hα : 0 < α) (hz : 0 < z) :
    α ^ 2 * z ^ 2 * (DDGstar α F z + DDGbar α F z)
      + α * (5 + α) * z * (DGstar α F z + DGbar α F z)
      = (15 / 4) * Fstar F z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- `A := z ^ (-(5/α))` is the homogeneous factor of `Gbar`; it is nonzero.
  have hApos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hz _
  have hAne : z ^ (-(5 / α)) ≠ 0 := ne_of_gt hApos
  -- Reduction of all the `z`-powers occurring in the definitions to `A` and `z⁻¹`.
  have hp1 : z ^ (-(5 / α) - 1) = z ^ (-(5 / α)) * z⁻¹ := by
    rw [show -(5 / α) - 1 = -(5 / α) + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
  have hp2 : z ^ (-(5 / α) - 1 - 1) = z ^ (-(5 / α)) * z⁻¹ * z⁻¹ := by
    rw [show -(5 / α) - 1 - 1 = -(5 / α) + (-1) + (-1) by ring,
      Real.rpow_add hz, Real.rpow_add hz, Real.rpow_neg_one]
  have hpt : z ^ ((5 - α) / α) = z⁻¹ / z ^ (-(5 / α)) := by
    rw [eq_div_iff hAne, ← Real.rpow_add hz,
      show (5 - α) / α + -(5 / α) = -1 by field_simp; ring, Real.rpow_neg_one]
  have hpu : z ^ ((5 - α) / α - 1) = (z⁻¹ / z ^ (-(5 / α))) * z⁻¹ := by
    rw [show (5 - α) / α - 1 = (5 - α) / α + (-1) by ring, Real.rpow_add hz, hpt,
      Real.rpow_neg_one]
  unfold DDGstar DDGbar DGstar DGbar Abar DAbar DDAbar
  rw [hp1, hp2, hpt, hpu]
  field_simp
  ring

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.HardyLeftW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open scoped ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary algebraic facts about the weight `w` on `(0,1)` -/

private lemma w_sq_eq (z : ℝ) (_hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring

private lemma one_le_one_add_pow_four {z : ℝ} (hz : 0 ≤ z) : (1 : ℝ) ≤ (1 + z) ^ 4 := by
  have h0 : 0 ≤ 1 + z := by linarith
  calc (1 : ℝ) = 1 ^ 4 := by norm_num
    _ ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4

private lemma w_sq_le_inv_four (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    (Work.Spaces.w z) ^ 2 ≤ 16 * z ^ (-(4 : ℝ)) := by
  have hz0 : 0 < z := hz.1
  have h4 : (1 + z) ^ 4 ≤ 16 := by
    have h0 : 0 ≤ 1 + z := by linarith
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 (by linarith [hz.2]) 4
      _ = 16 := by norm_num
  have hz4 : 0 < z ^ 4 := by positivity
  have hrw : z ^ (-(4 : ℝ)) = (z ^ 4)⁻¹ := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hz0), Real.rpow_natCast]
  rw [w_sq_eq z (ne_of_gt hz0), hrw, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right h4 (le_of_lt hz4)


/-- The source localised to `(0,1)`: `z ↦ 1_{(0,1)}(z)·f z / z²`. -/
private def FL (f : ℝ → ℝ) (z : ℝ) : ℝ := (Set.Ioo (0 : ℝ) 1).indicator f z / z ^ 2

/-! ## Measurability and integrability of `f` and of `f t / t` -/

/-- On `(0,1)` one has `f t = -(deriv U t) · t`; this is the measurability source for `f`. -/
private lemma f_eq_slope {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = -(deriv U t) * t := by
  intro t ht
  have h1 : f t / t = -(deriv U t) := by
    have h := (hderiv t ht).deriv
    rw [h]; ring
  exact (div_eq_iff (ne_of_gt ht.1)).mp h1

private lemma aesm_f {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hfm : Measurable (fun t : ℝ => -(deriv U t) * t) :=
    ((measurable_deriv U).neg).mul measurable_id
  refine hfm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (f_eq_slope hderiv t ht).symm

/-- `f t / t` is integrable on `(0,1)`: it is dominated by `((f t)² w t² + 1)/2`. -/
private lemma integrable_div_self {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hint : IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1) := by
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := aesm_f hderiv
  have hgmeas : AEStronglyMeasurable (fun t : ℝ => f t / t)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hfmeas.mul measurable_id.inv.aestronglyMeasurable
  have hM : Integrable (fun t : ℝ => ((f t) ^ 2 * (Work.Spaces.w t) ^ 2 + 1) / 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : Integrable (fun t : ℝ => (f t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hint
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).div_const 2
  refine Integrable.mono' hM hgmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have hb : (f t / t) ^ 2 ≤ (f t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have ht4 : (0 : ℝ) < t ^ 4 := by positivity
    have hkey : (1 : ℝ) / t ^ 2 ≤ (Work.Spaces.w t) ^ 2 := by
      rw [w_sq_eq t (ne_of_gt ht0), div_le_div_iff₀ ht2 ht4]
      have h1 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_one_add_pow_four (le_of_lt ht0)
      have h2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith
    calc (f t / t) ^ 2 = (f t) ^ 2 * ((1 : ℝ) / t ^ 2) := by rw [div_pow]; ring
      _ ≤ (f t) ^ 2 * (Work.Spaces.w t) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
  rw [Real.norm_eq_abs]
  have h1 : 2 * |f t / t| ≤ (f t / t) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|f t / t| - 1), sq_abs (f t / t), abs_nonneg (f t / t)]
  linarith

/-- The fundamental theorem of calculus for `U`: `U z = -∫_0^z f t / t dt` on `(0,1)`. -/
private lemma ftc_U {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hdiv : IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1)) :
    ∀ z ∈ Set.Ioo (0 : ℝ) 1, U z = -∫ t in (0 : ℝ)..z, f t / t := by
  intro z hz
  have hz0 : 0 < z := hz.1
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioo (0 : ℝ) 1 :=
    fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hz.2⟩
  have hint : IntervalIntegrable (fun t : ℝ => -(f t / t)) volume 0 z :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hz0.le).mpr (hdiv.mono_set hsub)).neg
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) z, HasDerivAt U (-(f x / x)) x :=
    fun x hx => hderiv x ⟨hx.1, lt_trans hx.2 hz.2⟩
  have hccc : ContinuousOn U (Set.Icc 0 z) :=
    hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt hz.2)⟩)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz0.le hccc hder hint
  rw [intervalIntegral.integral_neg, h0, sub_zero] at h
  linarith [h]

/-! ## Integrability of the localised source -/

private lemma integrable_FL_sq {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hint : IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun z : ℝ => FL f z ^ 2) (Set.Ioi 0) := by
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := aesm_f hderiv
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (f z / z ^ 2) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => ((z ^ 2)⁻¹ : ℝ))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (measurable_id.pow_const 2).inv.aestronglyMeasurable
    exact (hfmeas.mul h1).pow 2
  have h1 : IntegrableOn (fun z : ℝ => (f z / z ^ 2) ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' hint hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have hbn : ‖(f z / z ^ 2) ^ 2‖ = (f z / z ^ 2) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hbn, div_pow]
    have hz4 : (0 : ℝ) < (z ^ 2) ^ 2 := by positivity
    have hkey : (1 : ℝ) / (z ^ 2) ^ 2 ≤ (Work.Spaces.w z) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_one_add_pow_four (le_of_lt hz0)
      have hzz : (z ^ 2) ^ 2 = z ^ 4 := by ring
      have hz4 : (0 : ℝ) < z ^ 4 := by positivity
      rw [hzz, w_sq_eq z (ne_of_gt hz0)]
      exact div_le_div_of_nonneg_right h1 hz4.le
    calc (f z) ^ 2 / (z ^ 2) ^ 2 = (f z) ^ 2 * ((1 : ℝ) / (z ^ 2) ^ 2) := by ring
      _ ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
  have h2 : Integrable ((Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr h1
  have h3 : (fun z : ℝ => FL f z ^ 2)
      = (Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2) := by
    funext z
    by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
    · simp only [FL, Set.indicator_of_mem hz]
    · simp only [FL, Set.indicator_of_notMem hz]
      simp
  rw [h3]
  exact h2.integrableOn

/-! ## The main theorem -/

/-- Weighted Hardy inequality on the left half-line: for `U` continuous on `[0,1]` with `U 0 = 0` and derivative `-(f z / z)` on `(0,1)`, and `f²w²` integrable on `(0,1)`, one has `U²w²` integrable on `(0,1)` with `∫_{(0,1)} U²w² ≤ 107 ∫_{(0,1)} f²w²`. Here `w z = (1+z)²/z²` is `Work.Spaces.w`. Intended route: `U z = -∫_0^z f t/t dt`, then `w² ≤ 16 z^{-4}` on `(0,1)`, the weighted Hardy inequality `∫ U²/z⁴ ≤ (2/3)∫ U'²/z²`, and `z^{-4} ≤ w²`; this gives the constant `32/3 ≤ 107`. -/
theorem HardyLeftW (f U : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) ∧
      ∫ z in Set.Ioo (0 : ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Set.Ioo (0 : ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  set J : ℝ := ∫ z in Set.Ioo (0 : ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2 with hJ
  have hJnn : 0 ≤ J := integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdiv : IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1) :=
    integrable_div_self hderiv hint
  have hftc := ftc_U hderiv hcont h0 hdiv
  have hFLsq : IntegrableOn (fun z : ℝ => FL f z ^ 2) (Set.Ioi 0) := integrable_FL_sq hderiv hint
  have hlib := Gbar_hardy_lintegral_ofReal 2 (by norm_num) (FL f) hFLsq
  -- Step 0: pointwise identification of the two integrands on `(0,1)`.
  have hA : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ENNReal.ofReal ((z ^ (-(2 : ℝ)) * ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s) ^ 2)
        = ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have key : ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s = -U z := by
      have e1 : ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s
          = ∫ s in (0 : ℝ)..z, f s / s := by
        rw [intervalIntegral.integral_of_le hz0.le, intervalIntegral.integral_of_le hz0.le]
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        have hs1 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_le_of_lt hs.2 hz.2⟩
        simp only [FL, Set.indicator_of_mem hs1, show (2 : ℝ) - 1 = 1 by norm_num,
          Real.rpow_one]
        field_simp
      rw [e1, hftc z hz]
      ring
    have key2 : (z ^ (-(2 : ℝ)) * (-U z)) ^ 2 = (U z) ^ 2 * z ^ (-(4 : ℝ)) := by
      have h1 : (z ^ (-(2 : ℝ))) ^ 2 = z ^ (-(4 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hz0)]
        congr 1
        norm_num
      rw [mul_neg, neg_sq, mul_pow, h1]
      ring
    rw [key, key2]
  -- Step 1: `w² ≤ 16 z^{-4}` on `(0,1)`.
  have step1 : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 16 * ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
    have h16 : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
      intro z hz
      have hle : (U z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 16 * ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
        have h1 := w_sq_le_inv_four z hz
        have h2 : (0 : ℝ) ≤ (U z) ^ 2 := sq_nonneg _
        nlinarith [h1, h2]
      calc ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ENNReal.ofReal (16 * ((U z) ^ 2 * z ^ (-(4 : ℝ)))) := ENNReal.ofReal_le_ofReal hle
        _ = 16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
            norm_num
    calc ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1,
            16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) :=
          setLIntegral_mono' measurableSet_Ioo h16
      _ = 16 * ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) :=
          lintegral_const_mul' 16 _ (by norm_num)
  -- Step 2: the localised Hardy inequality (proved in the workspace).
  have step2 : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ)))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((z ^ (-(2 : ℝ)) * ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s) ^ 2) := by
    rw [← lintegral_congr_ae hA]
    exact lintegral_mono_set Ioo_subset_Ioi_self
  -- The comparison of the sources.
  have hFLint : ∫ z in Set.Ioi (0 : ℝ), FL f z ^ 2 ≤ J := by
    have h_eq : (fun z : ℝ => FL f z ^ 2)
        = (Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2) := by
      funext z
      by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
      · simp only [FL, Set.indicator_of_mem hz]
      · simp only [FL, Set.indicator_of_notMem hz]
        simp
    rw [h_eq, integral_indicator measurableSet_Ioo]
    rw [Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr Ioo_subset_Ioi_self]
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        (f z / z ^ 2) ^ 2 ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hz4 : (0 : ℝ) < (z ^ 2) ^ 2 := by positivity
      have hkey : (1 : ℝ) / (z ^ 2) ^ 2 ≤ (Work.Spaces.w z) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_one_add_pow_four (le_of_lt hz0)
        have hzz : (z ^ 2) ^ 2 = z ^ 4 := by ring
        have hz4 : (0 : ℝ) < z ^ 4 := by positivity
        rw [hzz, w_sq_eq z (ne_of_gt hz0)]
        exact div_le_div_of_nonneg_right h1 hz4.le
      calc (f z / z ^ 2) ^ 2 = (f z) ^ 2 * ((1 : ℝ) / (z ^ 2) ^ 2) := by rw [div_pow]; ring
        _ ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    exact integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg (f z / z ^ 2)) hint hpt
  -- Step 3: assemble.
  have hconst : 4 / (2 * (3 * 2 - 2) : ℝ) = 1 / 2 := by norm_num
  have hmain : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ENNReal.ofReal (107 * J) := by
    refine (step1.trans (mul_le_mul_of_nonneg_left (step2.trans hlib) (by norm_num))).trans ?_
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hconst]
    linarith [hFLint, hJnn]
  -- Measurability of the integrand and the final conversions.
  have hUcont : ContinuousOn U (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hw2meas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    have h1 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ)) :=
      (measurable_const.add measurable_id).pow_const 2
    have h2 : Measurable (fun z : ℝ => ((z ^ 2)⁻¹ : ℝ)) := (measurable_id.pow_const 2).inv
    have h3 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) := h1.mul h2
    have h4 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = (fun z : ℝ => (((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) ^ 2) := by
      funext z
      rw [Work.Spaces.w, div_eq_mul_inv]
    rw [h4]
    exact h3.pow_const 2
  have hUmeas : AEStronglyMeasurable (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((hUcont.pow 2).aestronglyMeasurable measurableSet_Ioo).mul hw2meas.aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfin : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top)
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hUmeas hnn).mp hfin, ?_⟩
  have hconv : ∫ z in Set.Ioo (0 : ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      = (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hUmeas
  rw [hconv]
  calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal
      ≤ (ENNReal.ofReal (107 * J)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 107 * J := ENNReal.toReal_ofReal (by linarith)

end

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.L12densFacts =====
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

/-! ## Elementary rewrites -/

/-- The angular moment `∫_θ K(θ)·g(s,θ) dθ` which is `s` times the density `L12dens g s`. -/
def angMoment (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Ktheta θ * g z θ

/-- `L12dens g s = angMoment g s / s`. -/
theorem L12dens_eq_angMoment_div (g : ℝ → ℝ → ℝ) (s : ℝ) :
    L12dens g s = angMoment g s / s := by
  rw [L12dens, angMoment, MeasureTheory.integral_div]

/-- The set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
theorem integral_Iθ_eq_interval_aux (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π/2), f θ := by
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π/2)]
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π/2))]

/-- `Ktheta` is continuous. -/
theorem continuous_ktheta : Continuous Ktheta := by
  unfold Ktheta; fun_prop

/-- The `θ`-slice `θ ↦ g s θ` of a function smooth on a neighbourhood of the closed quadrant
is continuous on `Iθ`, for `s ∈ (-1,∞)`. -/
theorem continuousOn_slice_theta_Iθ (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    {s : ℝ} (hs : s ∈ Set.Ioi (-1)) :
    ContinuousOn (fun θ => g s θ) Work.Spaces.Iθ := by
  have hslice : ContDiffOn ℝ ⊤ (fun θ => g s θ) (Set.Ioo (-1) (π/2 + 1)) := by
    have h := hsm
    unfold Work.Spaces.SmoothNbhd at h
    have h2 : ContDiffOn ℝ ⊤ (fun θ : ℝ => (s, θ)) (Set.Ioo (-1) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h3 := h.comp h2 (fun θ hθ => ⟨hs, hθ⟩)
    have hfun : (Function.uncurry g ∘ fun θ : ℝ => (s, θ)) = fun θ => g s θ := rfl
    rwa [hfun] at h3
  exact hslice.continuousOn.mono
    (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- A.e. statement for the restricted measure on `Iθ`: it suffices to prove the statement on
the open interval, where the angular weight `sin(2θ)` does not vanish. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ, 0 < θ → θ < π/2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π/2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => h θ hθ.1 hθ.2)

/-! ## Continuity of the density -/

/-- The density `L12dens g` is continuous at every `z > 0`. -/
theorem L12dens_continuousAt_aux (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (z : ℝ) (hz : 0 < z) : ContinuousAt (L12dens g) z := by
  have hzn : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hbox : Set.Icc (z/2) (z+1) ×ˢ Work.Spaces.Iθ
      ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1) := by
    rintro ⟨x, θ⟩ ⟨hx, hθ⟩
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hx.1],
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hcpt : IsCompact (Set.Icc (z/2) (z+1) ×ˢ Work.Spaces.Iθ) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hsm.continuousOn.mono hbox)
  have hs_nhds : Set.Ioo (z/2) (z+1) ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have hA : ContinuousAt (fun x : ℝ => ∫ θ in Work.Spaces.Iθ, Ktheta θ * g x θ) z := by
    refine MeasureTheory.continuousAt_of_dominated (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun x θ => Ktheta θ * g x θ) (bound := fun θ => M * |Ktheta θ|) ?_ ?_ ?_ ?_
    · filter_upwards [hs_nhds] with x hx
      exact (continuous_ktheta.continuousOn.mul
        (continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith [hx.1]))).aestronglyMeasurable
        measurableSet_Icc
    · filter_upwards [hs_nhds] with x hx
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      have hbound : |g x θ| ≤ M := by
        have h := hM (x, θ) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hθ⟩
        simpa only [Real.norm_eq_abs, Function.uncurry] using h
      rw [Real.norm_eq_abs, abs_mul]
      calc |Ktheta θ| * |g x θ| ≤ |Ktheta θ| * M :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
        _ = M * |Ktheta θ| := by ring
    · exact (continuous_ktheta.abs.continuousOn.integrableOn_compact isCompact_Icc).const_mul M
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
      exact (Work.Spaces.hardyZ_contDiffOn_slice g hsm hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds hzn) |>.const_mul (Ktheta θ)
  refine (hA.div continuous_id.continuousAt (ne_of_gt hz)).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
  exact (L12dens_eq_angMoment_div g x).symm

/-- The density `L12dens g` is continuous on `(0,∞)`. -/
theorem L12dens_continuousOn_aux (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (L12dens g) (Set.Ioi 0) :=
  fun z hz => (L12dens_continuousAt_aux g hsm z hz).continuousWithinAt

/-! ## The pointwise bound on the density -/


/-! ## Integrability of the weight `s²/(1+s)⁴` -/

/-- The square of the weight `ψ(s) = s/(1+s)²` is integrable on `(0,∞)`. -/
theorem psi_sq_integrable_aux :
    MeasureTheory.IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi (-1)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
      ((continuousOn_const.add continuousOn_id).pow 2) ?_) 2
    intro x hx
    have hx1 : (0:ℝ) < 1 + x := by
      simp only [Set.mem_Ioi] at hx
      linarith
    exact pow_ne_zero 2 (ne_of_gt hx1)
  have hcont1 : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Icc (0:ℝ) 1) :=
    hcont.mono (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
  have h1 : IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioc 0 1) :=
    (hcont1.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun s : ℝ => s ^ (-(2:ℝ))) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine Integrable.mono' hbase ?_ ?_
    · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioi
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hs1 : 1 ≤ s := le_of_lt hs
      have hs0 : 0 < s := lt_trans zero_lt_one hs
      have hred : s ^ (-(2:ℝ)) = (s ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hs0)]; simp
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hred]
      have h4 : s ^ 4 ≤ (1 + s) ^ 4 := by nlinarith [hs1, sq_nonneg s]
      calc (s / (1 + s) ^ 2) ^ 2 = s ^ 2 / (1 + s) ^ 4 := by
            rw [div_pow, ← pow_mul]
        _ ≤ (s ^ 2)⁻¹ := by
            rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [h4]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact h1.union h2

/-! ## The main theorem -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.PsiStar_ode =====
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
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary rewritings of the angular integral

The angular interval `Iθ` of `Work.Spaces` and the interval of integration `0..π/2` of
`intervalIntegral` give the same integral, since they differ by the point `0`. -/

lemma Iθ_integral_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)).symm


/-! ## Slices of a smooth function -/

/-- The `θ`-slice of a function smooth on a neighbourhood of the closed quadrant is smooth
on the whole angular interval. -/
lemma contDiffOn_slice_of_smoothNbhd (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : -1 < z) : ContDiffOn ℝ ⊤ (fun θ : ℝ => g z θ) (Set.Icc 0 (π / 2)) := by
  have hsub : Set.Icc (0 : ℝ) (π / 2) ⊆ Set.Ioo (-1) (π / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hp : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2)) Work.Spaces.U :=
    fun θ hθ => ⟨hz, hsub hθ⟩
  have h := hg.comp hp hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The slice of a `SmoothNbhd` function, multiplied by a function continuous on the angular
interval, is integrable there. -/
lemma integrableOn_slice_mul (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ => g z θ * φ θ) Work.Spaces.Iθ := by
  have h : IntegrableOn (fun θ => g z θ * φ θ) (Set.Icc 0 (π / 2)) :=
    ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((contDiffOn_slice_of_smoothNbhd g hg hz).continuousOn.mul hφ)
  simpa [Work.Spaces.Iθ] using h

/-! ## Differentiation under the integral sign in the radial variable -/

/-- **Differentiation under the integral sign in `z`** (interval-integral form): if `g` is
smooth on a neighbourhood of the closed quadrant and `φ` is continuous on `[0,π/2]`, then
`z' ↦ ∫_0^{π/2} g(z',θ) φ(θ) dθ` has derivative `∫_0^{π/2} ∂_z g(z,θ) φ(θ) dθ` at every
`z ∈ (-1,∞)`.

The domination hypothesis of Mathlib's parametric-integral theorem is supplied by the
uniform bound on `∂_z g` over the compact box `closure s × [0,π/2]`, where `s` is a bounded
neighbourhood of `z`; since `∂_z g` is continuous on the closed quadrant, this box is
contained in the open set on which `g` is smooth. -/
lemma hasDerivAt_integral_interval (g : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hg : Work.Spaces.SmoothNbhd g) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) {z : ℝ}
    (hz : -1 < z) :
    HasDerivAt (fun z' => ∫ θ in (0 : ℝ)..(π / 2), g z' θ * φ θ)
      (∫ θ in (0 : ℝ)..(π / 2), Work.Spaces.pz g z θ * φ θ) z := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hsm_pz : Work.Spaces.SmoothNbhd (Work.Spaces.pz g) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hg
  -- a bounded neighbourhood `s` of `z`, contained in `(-1,∞)`
  set s : Set ℝ := Set.Ioo ((z - 1) / 2) (z + 1) with hs
  have hs_nhds : s ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have hsz : s ⊆ Set.Ioi (-1) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1]
  have hsub_u : Set.uIoc (0 : ℝ) (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  -- the box `closure s × [0,π/2]` is compact and lies in the smoothness set
  have hcl : closure s = Set.Icc ((z - 1) / 2) (z + 1) := by
    rw [hs]; exact closure_Ioo (by linarith)
  have hboxU : closure s ×ˢ Set.Icc (0 : ℝ) (π / 2) ⊆ Work.Spaces.U := by
    rw [hcl]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hx.1],
      ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩⟩
  have hcpt : IsCompact (closure s ×ˢ Set.Icc (0 : ℝ) (π / 2)) := by
    rw [hcl]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn
    (((Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hg).continuousOn).mono hboxU)
  have hC' : ∀ x ∈ s, ∀ t ∈ Set.uIoc (0 : ℝ) (π / 2), ‖Work.Spaces.pz g x t‖ ≤ C :=
    fun x hx t ht => hC (x, t) ⟨subset_closure hx, hsub_u ht⟩
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun t : ℝ => g x t * φ t)
      (volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    filter_upwards [hs_nhds] with x hx
    exact (((contDiffOn_slice_of_smoothNbhd g hg (hsz hx)).continuousOn.mul hφ).mono
      hsub_u).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun t : ℝ => g z t * φ t) volume (0 : ℝ) (π / 2) :=
    ((contDiffOn_slice_of_smoothNbhd g hg hz).continuousOn.mul hφ).intervalIntegrable_of_Icc hle
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => Work.Spaces.pz g z t * φ t)
      (volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) :=
    (((contDiffOn_slice_of_smoothNbhd (Work.Spaces.pz g) hsm_pz hz).continuousOn.mul hφ).mono
      hsub_u).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ x ∈ s, ‖Work.Spaces.pz g x t * φ t‖ ≤ C * ‖φ t‖ := by
    filter_upwards with t ht x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC' x hx t ht) (norm_nonneg _)
  have hbound_int : IntervalIntegrable (fun t : ℝ => C * ‖φ t‖) volume (0 : ℝ) (π / 2) :=
    ((hφ.intervalIntegrable_of_Icc hle).norm).const_mul C
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ x ∈ s, HasDerivAt (fun x' : ℝ => g x' t * φ t) (Work.Spaces.pz g x t * φ t) x := by
    filter_upwards with t ht x hx
    exact (Work.Spaces.hardyZ_hasDerivAt_slice g hg (hsub_u ht) (hsz hx)).mul_const (φ t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := π / 2) (bound := fun t => C * ‖φ t‖)
    (F := fun x t => g x t * φ t) (F' := fun x t => Work.Spaces.pz g x t * φ t)
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- **Differentiation under the integral sign in `z`**, in the form of the integral over the
angular interval `Iθ`. -/
lemma hasDerivAt_integral_Iθ (g : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hg : Work.Spaces.SmoothNbhd g) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) {z : ℝ}
    (hz : -1 < z) :
    HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, g z' θ * φ θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz g z θ * φ θ) z := by
  have h := hasDerivAt_integral_interval g φ hg hφ hz
  have hfun : (fun z' => ∫ θ in Work.Spaces.Iθ, g z' θ * φ θ)
      = (fun z' => ∫ θ in (0 : ℝ)..(π / 2), g z' θ * φ θ) :=
    funext fun z' => Iθ_integral_eq_interval (fun θ => g z' θ * φ θ)
  rw [hfun, Iθ_integral_eq_interval (fun θ => Work.Spaces.pz g z θ * φ θ)]
  exact h

/-! ## The right hand side `F` in terms of the solution -/

/-- The angular moment of `F = bslOp α Ψ` is the θ-integral of `bslOp α Ψ` against the
weight `sinθcos²θ`.  Since `sinθcos²θ` vanishes at the endpoints, the a.e. identity
`bslOp α Ψ = F` on the open quadrant gives a pointwise identity on the whole closed
interval. -/
lemma Fstar_bslOp (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hsol : IsBslSol α F Ψ) :
    Fstar F z = ∫ θ in Work.Spaces.Iθ, bslOp α Ψ z θ * sinCos2 θ := by
  obtain ⟨hEq, -, -, -⟩ := hsol
  rw [Fstar]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rcases eq_or_ne θ 0 with rfl | h0
  · simp [sinCos2]
  · rcases eq_or_ne θ (π / 2) with rfl | h1
    · simp [sinCos2, Real.cos_pi_div_two]
    · rw [hEq z hz θ (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 h1)]

/-! ## Integrability of the `θ`-piece -/

/-- The integrand `L₀(Ψ)(z,·) · sinθcos²θ`, which is singular at `θ = π/2`, is integrable on
the angular interval.  On the closed interval it agrees, except at the two endpoints, with
the derivative of the `C¹` function

  `H(θ) = -Ψ_θ(z,θ) sinθcos²θ + Ψ(z,θ) cosθ cos 2θ`,

whose `θ`-derivative is exactly `L₀(Ψ)(z,θ)·sinθcos²θ` (see `hasDerivAt_Lzero_antideriv`). -/
lemma integrableOn_Lzero_mul_sinCos2 (Ψ : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ => Lzero Ψ z θ * sinCos2 θ) Work.Spaces.Iθ := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hlt : (0 : ℝ) < π / 2 := by positivity
  set f : ℝ → ℝ := fun θ => Ψ z θ with hf
  set H : ℝ → ℝ := fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * sinCos2 θ
      + f θ * (Real.cos θ * Real.cos (2 * θ)) with hHdef
  have hsm_f : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) := by rw [hf]; exact hsm
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hlt
  have hHcd : ContDiffOn ℝ 1 H (Set.Icc 0 (π / 2)) := by
    rw [hHdef]
    have hdw : ContDiffOn ℝ 1 (derivWithin f (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
      hsm_f.derivWithin hu (by norm_num)
    have hsm1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) := hsm_f.of_le (by norm_num)
    have hsincos : ContDiffOn ℝ 1 sinCos2 (Set.Icc 0 (π / 2)) := by unfold sinCos2; fun_prop
    have hcc : ContDiffOn ℝ 1 (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (Set.Icc 0 (π / 2)) := by fun_prop
    exact (hdw.neg.mul hsincos).add (hsm1.mul hcc)
  have hcont : ContinuousOn (derivWithin H (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
    hHcd.continuousOn_derivWithin hu le_rfl
  have hint : IntegrableOn (derivWithin H (Set.Icc 0 (π / 2))) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  refine hint.congr ?_
  rw [Filter.EventuallyEq]
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      derivWithin H (Set.Icc 0 (π / 2)) θ = Lzero Ψ z θ * sinCos2 θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  -- the two endpoints are the only exceptions
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  have h2 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({π / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h1, h2] with θ hθ1 hθ2 hθmem
  have hpoint : derivWithin H (Set.Icc 0 (π / 2)) θ = Lzero Ψ z θ * sinCos2 θ := by
    have h2' : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) θ :=
      hsm.contDiffAt (Icc_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
        (lt_of_le_of_ne hθmem.2 hθ2))
    have hHF : H =ᶠ[𝓝 θ] (fun θ' : ℝ => -(deriv (fun θ'' : ℝ => Ψ z θ'') θ') * sinCos2 θ'
        + Ψ z θ' * (Real.cos θ' * Real.cos (2 * θ'))) := by
      filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
        (lt_of_le_of_ne hθmem.2 hθ2)] with y hy
      simp only [hHdef, hf, derivWithin_of_mem_nhds
        (Icc_mem_nhds hy.1 hy.2)]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
      (lt_of_le_of_ne hθmem.2 hθ2))).trans
      ((hasDerivAt_Lzero_antideriv Ψ z θ
        ⟨lt_of_le_of_ne hθmem.1 (Ne.symm hθ1), lt_of_le_of_ne hθmem.2 hθ2⟩ h2').congr_of_eventuallyEq
        hHF).deriv
  exact hpoint


/-! ## The ODE for the angular moment -/

theorem PsiStar_ode (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) (hα : 0 < α) (hz : 0 < z)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = - Work.Elliptic.Fstar F z := by
  have hsol0 : ∀ z' : ℝ, Ψ z' 0 = 0 := hsol.2.1
  have hsolpi : ∀ z' : ℝ, Ψ z' (π / 2) = 0 := hsol.2.2.1
  have hz1 : (-1 : ℝ) < z := by linarith
  have hφ : ContinuousOn sinCos2 (Set.Icc 0 (π / 2)) := by unfold sinCos2; fun_prop
  have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)) :=
    (contDiffOn_slice_of_smoothNbhd Ψ hsm hz1).of_le (by norm_num)
  have hsm_pz : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hsm_pz2 : Work.Spaces.SmoothNbhd (Work.Spaces.pz (Work.Spaces.pz Ψ)) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm_pz
  -- the two radial derivatives of the angular moment
  have hΦ1 : deriv (fun z' => Fstar Ψ z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ :=
    (hasDerivAt_integral_Iθ Ψ sinCos2 hsm hφ hz1).deriv
  have hΦ2 : deriv (fun z' => deriv (fun z'' => Fstar Ψ z'') z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ := by
    show deriv (deriv (fun z'' => ∫ θ in Work.Spaces.Iθ, Ψ z'' θ * sinCos2 θ)) z = _
    have hns : (deriv (fun z'' => ∫ θ in Work.Spaces.Iθ, Ψ z'' θ * sinCos2 θ))
        =ᶠ[𝓝 z] (fun y => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ y θ * sinCos2 θ) := by
      filter_upwards [Ioi_mem_nhds hz1] with y hy
      exact (hasDerivAt_integral_Iθ Ψ sinCos2 hsm hφ hy).deriv
    rw [Filter.EventuallyEq.deriv_eq hns]
    exact (hasDerivAt_integral_Iθ (Work.Spaces.pz Ψ) sinCos2 hsm_pz hφ hz1).deriv
  -- integrability of the three pieces of the right hand side
  have hI1 : IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_slice_mul (Work.Spaces.pz (Work.Spaces.pz Ψ)) hsm_pz2 hz1 sinCos2 hφ
  have hI2 : IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_slice_mul (Work.Spaces.pz Ψ) hsm_pz hz1 sinCos2 hφ
  have hI3 : IntegrableOn (fun θ => Lzero Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_Lzero_mul_sinCos2 Ψ z hslice
  have hL : (∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ) = 0 :=
    Lzero_orthogonal Ψ z hslice (hsol0 z) (hsolpi z)
  -- the main identity: `F`-moment in terms of the two radial derivatives
  have hmain : Fstar F z
      = -(α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
        - (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ)
        + ∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ := by
    rw [Fstar_bslOp α F Ψ z hz hsol]
    have hcongr : (fun θ => bslOp α Ψ z θ * sinCos2 θ)
        = (fun θ => ((-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
            + Lzero Ψ z θ * sinCos2 θ) := by
      funext θ
      rw [bslOp_apply]
      ring
    rw [hcongr]
    have e1 : (∫ θ in Work.Spaces.Iθ, ((-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
            + Lzero Ψ z θ * sinCos2 θ)
        = (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
          + ∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ :=
      MeasureTheory.integral_add
        ((hI1.const_mul (-(α ^ 2 * z ^ 2))).add (hI2.const_mul (-(α * (5 + α) * z)))) hI3
    have e2 : (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ))
          + ∫ θ in Work.Spaces.Iθ, (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_add (hI1.const_mul (-(α ^ 2 * z ^ 2)))
        (hI2.const_mul (-(α * (5 + α) * z)))
    have e3 : (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ))
        = (-(α ^ 2 * z ^ 2)) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_const_mul (-(α ^ 2 * z ^ 2))
        (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
    have e4 : (∫ θ in Work.Spaces.Iθ, (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
        = (-(α * (5 + α) * z)) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_const_mul (-(α * (5 + α) * z))
        (fun θ => Work.Spaces.pz Ψ z θ * sinCos2 θ)
    rw [e1, e2, e3, e4]
    ring
  rw [hΦ2, hΦ1]
  rw [hL] at hmain
  linarith [hmain]

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.abs_htPP_le_sin =====
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
-- ===== merged: Submission.Work.Elliptic.bslOp_sinG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- `L(Ψ + G sin 2θ) = L(Ψ) - (α²z²G'' + α(5+α)zG') sin 2θ` at every `(z,θ)` with
`cos θ ≠ 0`: the `sin 2θ`-direction of `L` is purely radial, so adding a multiple of
`sin 2θ` shifts `LΨ` by the one-dimensional operator
`α²z² d²/dz² + α(5+α)z d/dz` applied to `G`, times `sin 2θ`.  Together with
`Lzero_sin_two` this is the identity behind §'The singular term' of the paper. -/
lemma bslOp_sinG (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (G : ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ)) (hG : ContDiffAt ℝ 2 G z)
    (hθ : Real.cos θ ≠ 0) :
    bslOp α (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z θ
      = bslOp α Ψ z θ
        - (α ^ 2 * z ^ 2 * deriv (fun z' => deriv G z') z + α * (5 + α) * z * deriv G z)
            * Real.sin (2 * θ) := by
  -- the `sin 2θ`-part `(z,θ) ↦ G z · sin 2θ` is `C²` at `(z,θ)`
  have hΦ : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => G z * Real.sin (2 * θ))) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => G p.1) (z, θ) :=
      hG.comp (z, θ) contDiffAt_fst
    have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by fun_prop
    have hfun : Function.uncurry (fun z θ => G z * Real.sin (2 * θ))
        = fun p : ℝ × ℝ => G p.1 * Real.sin (2 * p.2) := rfl
    rw [hfun]
    exact h1.mul h2
  -- additivity of `L`, then the closed form of `L` on the `sin 2θ` direction
  rw [bslOp_add α Ψ (fun z θ => G z * Real.sin (2 * θ)) z θ hθ hΨ hΦ,
      bslOp_sin_two_mul α G z θ hθ]
  ring

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.continuousWithinAt_htPP_pi2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false



end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.hardy_operator_L2 =====
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
-- ===== merged: Submission.Work.Elliptic.htU_contDiffAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `htU f θ = f θ / sin (2θ)` is of class `C²` at every *interior* point `θ ∈ (0, π/2)`, where
`sin (2θ) ≠ 0`; note that on the closed interval the endpoints `0` and `π/2` are precisely the
zeros of the denominator, which is why only interior points are covered by the standing
hypothesis `hf`. -/
theorem htU_contDiffAt (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 (Work.Elliptic.htU f) θ := by
  -- `θ` is an interior point of `[0, π/2]`, so `f` is `C²` at `θ`.
  have hmem : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hθ) Ioo_subset_Icc_self
  have hfθ : ContDiffAt ℝ 2 f θ := hf.contDiffAt hmem
  -- the denominator `θ ↦ sin (2θ)` is smooth at `θ` and nonvanishing there.
  have hsin : ContDiffAt ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
  have hne : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < π := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  change ContDiffAt ℝ 2 (fun θ => f θ / Real.sin (2 * θ)) θ
  exact hfθ.div hsin hne

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.htU_near_pi2 =====
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
set_option maxHeartbeats 1600000

/-! ### Elementary endpoint facts -/









end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.htU_near_zero =====
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
-- ===== merged: Submission.Work.Elliptic.sharp_hardy_pi =====
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
set_option maxHeartbeats 2000000

/-! ## Elementary rpow algebra -/

private lemma two_div_pi_rpow_neg (η : ℝ) : (2 / Real.pi) ^ (-η) = (Real.pi / 2) ^ η := by
  have h : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [show (2 / Real.pi : ℝ) = (Real.pi / 2)⁻¹ by rw [inv_div]]
  rw [Real.inv_rpow h.le, Real.rpow_neg h.le, inv_inv]



/-! ## Integrability on `[0, π/2]` -/



/-! ## The weighted `L²` bound `∫ f² sin^{-η} ≤ K ∫ f'²` on `[0, π/2]` -/


/-! ## Reflection of interval integrability across `π/2 ↦ π` -/


/-! ## The main theorem -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.sharp_hardy_sin_two =====
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


theorem half_sharp_hardy {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
        ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ)^2 * (Real.sin (2*θ)) ^ (-η))
          + C * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sin_pow_compare (η := η) hη0 hη1
  refine ⟨C0, hC0pos, fun f hf hf0 hfpi => ?_⟩
  obtain ⟨hIL, hIN, hIP, hIM, hIQ⟩ := sin_weight_integrable hη0 hη1 hf hf0 hfpi
  have hπ4 : (0:ℝ) ≤ Real.pi/4 := by positivity
  have hsub : Set.uIcc (0:ℝ) (Real.pi/4) ⊆ Set.uIcc 0 (Real.pi/2) := by
    rw [Set.uIcc_of_le hπ4, Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)]
    exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hIL' := hIL.mono_set hsub
  have hIN' := hIN.mono_set hsub
  have hIP' := hIP.mono_set hsub
  have hIM' := hIM.mono_set hsub
  have hIQ' := hIQ.mono_set hsub
  -- pointwise comparison
  have hpoint : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi/4),
      f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η))
        ≤ f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0]; simp [hf0]
    · have h2 : 0 < 2*θ := by linarith
      have h3 : 2*θ ≤ Real.pi/2 := by linarith [hθ.2]
      have hc := hC0 (2*θ) h2 h3
      have : 0 ≤ f θ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hc this]
  have hmono : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4),
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) :=
    intervalIntegral.integral_mono_on hπ4 hIL'
      (hIM'.add (hIN'.const_mul C0)) hpoint
  -- split the RHS
  have hsplit : (∫ θ in (0:ℝ)..(Real.pi/4),
        (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))))
      = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
    rw [intervalIntegral.integral_add hIM' (hIN'.const_mul C0),
        intervalIntegral.integral_const_mul]
  -- power-Hardy comparison
  have hpw := power_hardy (a := Real.pi/4) (by positivity) hη0 hη1
      (hf.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))) hf0
  have hscal : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
      = 2 ^ (-(2+η)) * ∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * θ ^ (-(2+η)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπ4] at hθ
    show f θ ^ 2 * (2*θ) ^ (-(2+η)) = 2 ^ (-(2+η)) * (f θ ^ 2 * θ ^ (-(2+η)))
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.1]
    ring
  have hscal2 : (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * θ ^ (-η))
      = 2 ^ η * ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hπ4] at hθ
    show (deriv f θ) ^ 2 * θ ^ (-η) = 2 ^ η * ((deriv f θ) ^ 2 * (2*θ) ^ (-η))
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.1,
        show (2:ℝ) ^ (-η) = ((2:ℝ) ^ η)⁻¹ from Real.rpow_neg (by norm_num) η]
    field_simp
  have hQP : (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    refine intervalIntegral.integral_mono_on hπ4 hIQ' hIP' ?_
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0]; simp
    · have hsinpos : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, Real.pi_pos])
      have hle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith)
      have hr := Real.rpow_le_rpow_of_nonpos hsinpos hle (by linarith : -η ≤ 0)
      exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)
  have hMbound : (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
      ≤ 1/(1+η)^2 * ∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η) := by
    have hcoef : 2 ^ (-(2+η)) * (4 / (1+η)^2) * (2^η) = 1/(1+η)^2 := by
      rw [show (2:ℝ) ^ (-(2+η)) = (2 ^ (2+η))⁻¹ from Real.rpow_neg (by norm_num) (2+η)]
      have h2 : (2:ℝ) ^ (2+η) = 2^2 * 2^η := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]; norm_num
      rw [h2]
      have h2η : (2:ℝ)^η ≠ 0 := by positivity
      have h1η : (1:ℝ) + η ≠ 0 := by linarith
      field_simp
      ring
    rw [hscal]
    calc 2 ^ (-(2+η)) * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * θ ^ (-(2+η)))
        ≤ 2 ^ (-(2+η)) * (4 / (1+η)^2
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * θ ^ (-η))) :=
          mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = (2 ^ (-(2+η)) * (4 / (1+η)^2) * (2^η))
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η)) := by
          rw [hscal2]; ring
      _ = (1/(1+η)^2) * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (2*θ) ^ (-η)) := by
          rw [hcoef]
      _ ≤ (1/(1+η)^2)
            * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η)) :=
          mul_le_mul_of_nonneg_left hQP (by positivity)
  calc (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-(2+η)))
      ≤ ∫ θ in (0:ℝ)..(Real.pi/4),
          (f θ ^ 2 * (2*θ) ^ (-(2+η)) + C0 * (f θ ^ 2 * (Real.sin (2*θ)) ^ (-η))) := hmono
    _ = (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (2*θ) ^ (-(2+η)))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := hsplit
    _ ≤ 1/(1+η)^2 * (∫ θ in (0:ℝ)..(Real.pi/4), (deriv f θ) ^ 2 * (Real.sin (2*θ)) ^ (-η))
        + C0 * (∫ θ in (0:ℝ)..(Real.pi/4), f θ ^ 2 * (Real.sin (2*θ)) ^ (-η)) := by
          linarith [hMbound]



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.tendsto_abs_sin_two_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.SobChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Filter
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.EllipticEst.InteriorRegularity.Q0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The Schwartz-level `L²` estimate -/

/-- **The key estimate** (copy of `mms_Phi_estimate` with the proved `youngE`): the operator
`Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded for the `L²` norm. -/
theorem phiEstimate (s : ℝ) (γS k : SchwartzMap E ℂ) :
    ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      ≤ (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖) *
          ‖k.toLp 2 (volume : Measure E)‖ := by
  have hFnn : ∀ z : E, 0 ≤ ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖ := fun _ => norm_nonneg _
  have hun : ∀ y : E, 0 ≤ ‖FourierTransform.fourier k y‖ := fun _ => norm_nonneg _
  have hFi : Integrable (fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖) (volume : Measure E) := by
    have hSint : Integrable (fun z : E =>
        ‖⇑(SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) |s|)
          (FourierTransform.fourier γS : 𝓢(E, ℂ))) z‖) (volume : Measure E) :=
      (SchwartzMap.integrable _).norm
    refine (hSint.mul_const (2 ^ (|s| / 2))).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (E := E) |s|), smul_eq_mul,
      norm_mul, norm_mul, norm_mul, norm_ofReal_complex,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) (|s| / 2))]
    ring
  have huM : MemLp (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier k) 2 (volume : Measure E)).norm
  have hfm : AEStronglyMeasurable
      (⇑(FourierTransform.fourier (mms_Phi s γS k))) (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier (mms_Phi s γS k)) 2
      (volume : Measure E)).aestronglyMeasurable
  have hpt : ∀ ξ : E, ‖(⇑(FourierTransform.fourier (mms_Phi s γS k))) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal ((‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
          (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier γS (ξ - y))‖) *
          ‖FourierTransform.fourier k y‖) ∂(volume : Measure E) :=
    fun ξ => mms_Phi_enorm_le s γS k ξ
  have hmain := youngE
    (F := fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖)
    (u := fun y : E => ‖FourierTransform.fourier k y‖)
    (f := ⇑(FourierTransform.fourier (mms_Phi s γS k))) hFnn hun hFi huM hfm hpt
  have hPhi : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal := by
    have h1 : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier (mms_Phi s γS k)).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq ((mms_Phi s γS k).toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hk : ‖k.toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
    have h1 : ‖k.toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier k).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq (k.toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hnormu : eLpNorm (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E)
      = eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) :=
    eLpNorm_norm _ (SchwartzMap.memLp (FourierTransform.fourier k) 2
      (volume : Measure E)).aestronglyMeasurable
  have hne : ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
        (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
        * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (SchwartzMap.memLp
      (FourierTransform.fourier k) 2 (volume : Measure E)).eLpNorm_lt_top)
  rw [hPhi, hk]
  calc (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal
      ≤ (ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_mono hne (by rw [← hnormu]; exact hmain)
    _ = (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-! ## Extension from Schwartz functions to `L²` -/

/-- Multiplication by a compactly supported smooth function preserves `H^s` (copy of
`mul_memSobolev`/`mms_main`, using the proved `phiEstimate`). -/
theorem mulSobMain {s : ℝ} (γS : SchwartzMap E ℂ) (u : TemperedDistribution E ℂ)
    (U : Lp ℂ 2 (volume : Measure E))
    (hU : besselPotential E ℂ s u = (U : TemperedDistribution E ℂ)) :
    MemSobolev s 2 (smulLeftCLM ℂ (⇑γS) u) := by
  set C : ℝ := ∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| ξ * (FourierTransform.fourier γS) ξ)‖ with hCdef
  have hC_nonneg : 0 ≤ C := by
    rw [hCdef]
    exact integral_nonneg fun ξ => norm_nonneg _
  have hu_eq : u = besselPotential E ℂ (-s) (U : TemperedDistribution E ℂ) := by
    rw [← mms_bessel_neg_bessel s u, hU]
  let e : SchwartzMap E ℂ →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    SchwartzMap.toLpCLM ℂ ℂ 2 volume
  have hdense : DenseRange e := by
    show DenseRange fun f : SchwartzMap E ℂ => f.toLp 2 (volume : Measure E)
    have h := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := E) (p := 2)
      (μ := (volume : Measure E)) (by norm_num)
    have hfe : (fun f : SchwartzMap E ℂ => f.toLp 2 (volume : Measure E)) =
        ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) := by
      funext f
      rw [SchwartzMap.toLpCLM_apply]
    rw [hfe]
    exact h
  have hseq : ∀ n : ℕ, ∃ k : SchwartzMap E ℂ, dist U (e k) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.denseRange_iff.mp hdense) U _ (by positivity)
  choose f hf using hseq
  have hnorm : ∀ n : ℕ, ‖U - e (f n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h := hf n
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hzero : Tendsto (fun n : ℕ => U - e (f n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hh := Nat.add_le_add_right hn 1
      exact_mod_cast hh
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      have h3 : (1 : ℝ) < ((N : ℝ) + 1) * ε := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) + 1 := by
          have : (N : ℝ) < (N : ℝ) + 1 := by linarith
          linarith
        exact (div_lt_iff₀ hε).mp hN'
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [h3]
    calc dist (U - e (f n)) 0 = ‖U - e (f n)‖ := by rw [dist_zero_right]
      _ ≤ 1 / ((n : ℝ) + 1) := hnorm n
      _ ≤ 1 / ((N : ℝ) + 1) := h1
      _ < ε := h2
  have hftend : Tendsto (fun n : ℕ => e (f n)) atTop (𝓝 U) := by
    have h1 : Tendsto (fun n : ℕ => U - (U - e (f n))) atTop (𝓝 (U - 0)) := hzero.const_sub U
    simpa using h1
  let v : ℕ → Lp ℂ 2 (volume : Measure E) := fun n => (mms_Phi s γS (f n)).toLp 2 volume
  have hv_lip : ∀ m n : ℕ, dist (v m) (v n) ≤ C * dist (e (f m)) (e (f n)) := by
    intro m n
    have hL : mms_Phi s γS (f m) - mms_Phi s γS (f n) = mms_Phi s γS (f m - f n) := by
      simp only [mms_Phi, map_sub]
    have hA' : v m - v n = (mms_Phi s γS (f m - f n)).toLp 2 (volume : Measure E) := by
      rw [show v m = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f m))
            from rfl,
        show v n = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f n))
            from rfl,
        ← map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)), hL]
      rfl
    have hB' : e (f m) - e (f n) = (f m - f n).toLp 2 (volume : Measure E) := by
      show e (f m) - e (f n) = _
      rw [← map_sub e]
      rfl
    rw [dist_eq_norm, dist_eq_norm, hA', hB', hCdef]
    exact phiEstimate s γS (f m - f n)
  have hv_cauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hce : CauchySeq fun n : ℕ => e (f n) := hftend.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hce) (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hC1 : 0 < C + 1 := by linarith
    have h1 := hv_lip m n
    have h2 := hN m hm n hn
    have h3 : C * dist (e (f m)) (e (f n)) ≤ (C + 1) * dist (e (f m)) (e (f n)) := by
      have hd : 0 ≤ dist (e (f m)) (e (f n)) := dist_nonneg
      nlinarith
    have h4 : (C + 1) * dist (e (f m)) (e (f n)) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left h2 hC1
    have h5 : (C + 1) * (ε / (C + 1)) = ε := by
      field_simp
    linarith [h1, h3, h4, h5.le, h5.ge]
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  let A : Lp ℂ 2 (volume : Measure E) →L[ℂ] TemperedDistribution E ℂ :=
    (besselPotential E ℂ s).comp ((smulLeftCLM ℂ (⇑γS)).comp
      ((besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2)))
  have hAapply : ∀ W : Lp ℂ 2 (volume : Measure E), A W = besselPotential E ℂ s
      (smulLeftCLM ℂ (⇑γS) (besselPotential E ℂ (-s) (W : TemperedDistribution E ℂ))) := by
    intro W
    rfl
  have hA : ∀ n : ℕ, A (e (f n)) = (v n : TemperedDistribution E ℂ) := by
    intro n
    rw [hAapply]
    have h1 : ((e (f n) : Lp ℂ 2 (volume : Measure E)) : TemperedDistribution E ℂ)
        = (f n : TemperedDistribution E ℂ) :=
      Lp.toTemperedDistribution_toLp_eq (f n)
    rw [h1, ← mms_Phi_toTempered s γS (f n)]
    exact (Lp.toTemperedDistribution_toLp_eq (mms_Phi s γS (f n))).symm
  have hAU : A U = besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u) := by
    rw [hAapply, ← hU, mms_bessel_neg_bessel]
  have h1 : Tendsto (fun n : ℕ => (v n : TemperedDistribution E ℂ)) atTop
      (𝓝 (besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u))) := by
    have hcomp : Tendsto (fun n : ℕ => A (e (f n))) atTop (𝓝 (A U)) :=
      (A.continuous.tendsto U).comp hftend
    rw [← hAU]
    simpa only [hA] using hcomp
  have h2 : Tendsto (fun n : ℕ => (v n : TemperedDistribution E ℂ)) atTop
      (𝓝 (V : TemperedDistribution E ℂ)) :=
    ((Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2).continuous.tendsto V).comp hV
  exact ⟨V, tendsto_nhds_unique h1 h2⟩

/-- **Multiplication by a compactly supported `C^∞` function preserves `H^s = MemSobolev s 2`**
(for every real `s`). -/
theorem mulSob {s : ℝ} {γ : E → ℂ} (hγc : HasCompactSupport γ) (hγs : ∀ n : ℕ, ContDiff ℝ n γ)
    {u : TemperedDistribution E ℂ} (hu : TemperedDistribution.MemSobolev s 2 u) :
    TemperedDistribution.MemSobolev s 2 (TemperedDistribution.smulLeftCLM ℂ γ u) := by
  have hγS_smooth : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_infty.mpr hγs
  let γS : SchwartzMap E ℂ := hγc.toSchwartzMap hγS_smooth
  obtain ⟨U, hU⟩ := hu
  exact mulSobMain γS u U hU

/-- A compactly supported `C^∞` function, viewed as the distribution of its `L²` class, lies in
every Bessel potential space `H^s`. -/
theorem ccMemSobolev {s : ℝ} {f : E → ℂ} {hf : MemLp f 2 (volume : Measure E)}
    (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    TemperedDistribution.MemSobolev s 2
      (MeasureTheory.Lp.toTemperedDistribution (hf.toLp)) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  let fS : SchwartzMap E ℂ := hc.toSchwartzMap hfs
  have hcoe : (⇑fS : E → ℂ) = f := funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hLp : fS.toLp 2 (volume : Measure E) = hf.toLp := by
    refine Lp.ext ?_
    filter_upwards [SchwartzMap.coeFn_toLp (f := fS) 2 (volume : Measure E),
      hf.coeFn_toLp] with x h1 h2
    rw [h1, h2, hcoe]
  rw [← hLp, Lp.toTemperedDistribution_toLp_eq fS]
  -- the Bessel potential of a Schwartz function is a Schwartz function, hence `L²`
  refine ⟨(SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) s) fS).toLp 2 volume, ?_⟩
  rw [mms_bessel_schwartz s fS]
  exact (Lp.toTemperedDistribution_toLp_eq
    (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) s) fS)).symm

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

/-- The pointwise form of the cos-weighted self-pairing of `Lzero1`: on the open interval
the difference between `(Lzero1 v)·v·cos θ` and the quadratic form
`(v')² cos θ + (v/cos θ)² cos θ - 6 v² cos θ` is the derivative of the primitive
`θ ↦ -v θ · v' θ · cos θ` (whose endpoints values vanish when `v 0 = v (π/2) = 0`). -/
private theorem hasDerivAt_primitive {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t => -(v t * deriv v t * Real.cos t))
      (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
        - (deriv v θ) ^ 2 * Real.cos θ
        - (v θ / Real.cos θ) ^ 2 * Real.cos θ
        + 6 * (v θ ^ 2 * Real.cos θ)) θ := by
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hθ.1]
    · exact hθ.2
  have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
  have hdv : HasDerivAt v (deriv v θ) θ :=
    ((hv.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hUicc : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc (by positivity)
  have hg1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hUicc (by norm_num)
  have hg : HasDerivAt (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ) θ :=
    ((hg1.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hev : (deriv v) =ᶠ[𝓝 θ] (derivWithin v (Set.Icc 0 (Real.pi / 2))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have hddv : HasDerivAt (deriv v) (deriv (deriv v) θ) θ := by
    have h := hg.congr_of_eventuallyEq hev
    rwa [h.deriv]
  have htan : HasDerivAt (fun t => Real.tan t * v t)
      (1 / Real.cos θ ^ 2 * v θ + Real.tan θ * deriv v θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hdv
  have hprod : HasDerivAt (fun t => -(v t * deriv v t * Real.cos t))
      (-((deriv v θ * deriv v θ + v θ * deriv (deriv v) θ) * Real.cos θ
          + (v θ * deriv v θ) * (-Real.sin θ))) θ :=
    ((hdv.mul hddv).mul (Real.hasDerivAt_cos θ)).neg
  refine hprod.congr_deriv ?_
  have htan_d := htan.deriv
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [show deriv (fun t => deriv v t) θ = deriv (deriv v) θ from rfl, htan_d]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem Lzero1_energy_cos_correct (v : ℝ → ℝ) (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hL : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (v θ / Real.cos θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hC : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)
        + (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ)
        - 6 * ∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  -- the primitive `F` and the integrand `g` of the pointwise identity
  set F : ℝ → ℝ := fun t => -(v t * deriv v t * Real.cos t) with hF
  set g : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
      - (deriv v θ) ^ 2 * Real.cos θ
      - (v θ / Real.cos θ) ^ 2 * Real.cos θ
      + 6 * (v θ ^ 2 * Real.cos θ) with hg
  -- `F` is continuous on `[0, π/2]`: on the interior because `v` and `v'` are, at the
  -- endpoints because `v` vanishes there (`F = -v · (derivWithin v Icc) · cos` on all
  -- of `Icc`, a product of functions continuous on `Icc`).
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hlt
  have hg1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hdvW : ContinuousOn (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hg1.continuousOn
  have hWcont : ContinuousOn
      (fun t => -(v t * derivWithin v (Set.Icc 0 (Real.pi / 2)) t * Real.cos t))
      (Set.Icc 0 (Real.pi / 2)) :=
    (((hv.continuousOn.mul hdvW).mul Real.continuous_cos.continuousOn)).neg
  have hFcont : ContinuousOn F (Set.Icc 0 (Real.pi / 2)) := by
    refine hWcont.congr (fun t ht => ?_)
    simp only [hF]
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, h0]; simp
    · rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2, h1]; simp
      · rw [derivWithin_of_mem_nhds (Icc_mem_nhds h h2)]
  -- and its derivative is `g` on the interior
  have hderiv : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt F (g x) x := by
    intro x hx
    simpa only [hF, hg] using hasDerivAt_primitive hv hx
  have h6int : IntegrableOn (fun θ => (6 : ℝ) * (v θ ^ 2 * Real.cos θ)) Work.Spaces.Iθ :=
    hC.const_mul (6 : ℝ)
  have hgint : IntegrableOn g Work.Spaces.Iθ :=
    ((hL.sub hA).sub hB).add h6int
  have hint : IntervalIntegrable g volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
      (by simpa [Work.Spaces.Iθ] using hgint)
  -- fundamental theorem of calculus: the primitive vanishes at both endpoints
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFcont hderiv hint]
    simp [hF, h0, h1]
  have hIθ_g : (∫ θ in Work.Spaces.Iθ, g θ) = 0 := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, hFTC]
  -- rewrite the integral of `g` in the split form used below
  have hIθ : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ)
          + 6 * (v θ ^ 2 * Real.cos θ)) = 0 := by
    simpa only [hg, Pi.add_apply, Pi.sub_apply] using hIθ_g
  -- split the integral of the sum of the four terms
  have e1 : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ)
          + 6 * (v θ ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ))
        + (∫ θ in Work.Spaces.Iθ, 6 * (v θ ^ 2 * Real.cos θ)) :=
    MeasureTheory.integral_add ((hL.sub hA).sub hB) h6int
  have e2 : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ))
        - (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_sub (hL.sub hA) hB
  have e3 : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
        - (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_sub hL hA
  have e4 : (∫ θ in Work.Spaces.Iθ, 6 * (v θ ^ 2 * Real.cos θ))
      = 6 * (∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_const_mul 6 (fun θ => v θ ^ 2 * Real.cos θ)
  linarith [hIθ, e1, e2, e3, e4]

end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.EllipticEst.ModalSolution

/-- **Head piece.**  For `r ≥ 1`, `z > 0` and `c` with `∫_0^∞ c² < ∞`, the near-origin Green
integral is bounded by the `L²` mass of `c`: Cauchy–Schwarz for `√(c ²)` against `t ^ (r-1)` on
`(0,z)`, using `∫_0^z t ^ (2r-2) = z ^ (2r-1)/(2r-1)`. -/
theorem radGreen_head_bound (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {r z : ℝ} (hr : 1 ≤ r) (hz : 0 < z) :
    |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  -- ## step 1: `|∫ c · w| ≤ ∫ |c| · w` on `(0,z)`, with `w = t ^ (r-1) > 0`
  have hJ : |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| ≤
      ∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1) := by
    have h1 : |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| ≤
        ∫ t in Set.Ioc (0 : ℝ) z, ‖c t * t ^ (r - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) z))
          (f := fun t => c t * t ^ (r - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht.1 (r - 1))]
  -- ## step 2: Cauchy–Schwarz with `u t = √(c t ²)` and `v t = t ^ (r-1)`
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hc.1).mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (r - 1)) (Set.Ioc (0 : ℝ) z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (r - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioc
  have hptv : ∀ t : ℝ, 0 < t → t ^ (2 * r - 2) = (t ^ (r - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (r - 1)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (2 * r - 2)) (Set.Ioc (0 : ℝ) z) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hz0).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 * r - 2)
          (a := (0 : ℝ)) (b := z))
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hptv t ht.1
  have hv : MemLp (fun t : ℝ => t ^ (r - 1)) 2 (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := fun t => Real.sqrt (c t ^ 2)) (v := fun t : ℝ => t ^ (r - 1)) hu hv
  -- ## step 3: the values of the two `L²` integrals
  have hIntU : (∫ t in Set.Ioc (0 : ℝ) z, (Real.sqrt (c t ^ 2)) ^ 2) =
      ∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  have hVval : (∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * r - 2)) = z ^ (2 * r - 1) / (2 * r - 1) := by
    rw [← intervalIntegral.integral_of_le hz0]
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * r - 2))]
    rw [show (2 * r - 2 + 1 : ℝ) = 2 * r - 1 by ring]
    rw [Real.zero_rpow (by linarith : (2 * r - 1 : ℝ) ≠ 0), sub_zero]
  have hIntV : (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (r - 1)) ^ 2) = z ^ (2 * r - 1) / (2 * r - 1) := by
    have hcong : (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (r - 1)) ^ 2) =
        ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * r - 2) :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact (hptv t ht.1).symm)
    rw [hcong, hVval]
  have hCSp : (∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1)) ≤
      Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
        Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  have hW : Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) =
      z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
    have hzW : 0 ≤ z ^ (2 * r - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    rw [Real.sqrt_div hzW (2 * r - 1)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
    rw [show (2 * r - 1) * (1 / 2) = r - 1 / 2 by ring]
  have hUQ : (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioc (0 : ℝ) z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_le_sqrt hUQ
  calc |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)|
      = |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| := by
        rw [intervalIntegral.integral_of_le hz0]
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1) := hJ
    _ ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
          Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) := hCSp
    _ = Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
          (z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * (z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
        rw [mul_div_assoc]

theorem radGreen_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (m : ℝ) + 5) * Real.sqrt m) := by
  -- notation: `M = m`, `p = 2m/α`, `q = (2m+5)/α`
  set M : ℝ := (m : ℝ) with hMdef
  set p : ℝ := 2 * M / α with hpdef
  set q : ℝ := (2 * M + 5) / α with hqdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact_mod_cast hm
  have hM0 : 0 ≤ M := by linarith
  have hKpos : 0 < α * (4 * M + 5) := mul_pos hα (by linarith)
  have honeK : 0 ≤ 1 / (α * (4 * M + 5)) := le_of_lt (one_div_pos.mpr hKpos)
  have hp0 : 0 < p := by
    rw [hpdef]
    exact div_pos (by linarith : (0 : ℝ) < 2 * M) hα
  have hq1 : 1 ≤ q := by
    have h7 : (7 : ℝ) ≤ q := by
      rw [hqdef, le_div_iff₀ hα]
      nlinarith
    linarith
  have hdef : Work.FTS.PhiStar.Radial.radGreen α m c z = 1 / (α * (4 * M + 5)) *
      (z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))
        + z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) := by
    simp only [Work.FTS.PhiStar.Radial.radGreen]
    rw [neg_div, ← hMdef, ← hpdef, ← hqdef]
  -- ## the two Green pieces
  have hhead : |∫ t in (0 : ℝ)..z, c t * t ^ (q - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (q - 1 / 2) / Real.sqrt (2 * q - 1) :=
    radGreen_head_bound c hc (r := q) hq1 hz
  have htail : |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) :=
    radGreen_tail_bound c hc (p := p) hp0 hz
  have hzq : 0 < z ^ (-q) := Real.rpow_pos_of_pos hz _
  have hzA : z ^ (-q) * z ^ (q - 1 / 2) = z ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hhead' : |z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * q - 1) := by
    have key : z ^ (-q) * (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (q - 1 / 2)
          / Real.sqrt (2 * q - 1))
        = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / Real.sqrt (2 * q - 1) := by
      rw [← hzA]
      ring
    rw [abs_mul, abs_of_pos hzq]
    exact le_trans (mul_le_mul_of_nonneg_left hhead (le_of_lt hzq)) (le_of_eq key)
  -- ## the numeric side conditions
  have hq_eq : 2 * q - 1 = (2 * (2 * M + 5) - α) / α := by
    rw [hqdef]
    field_simp
  have h1 : 4 * M + 1 ≤ 2 * q - 1 := by
    rw [hq_eq, le_div_iff₀ hα]
    nlinarith
  have hp_eq : 2 * p + 1 = (4 * M + α) / α := by
    rw [hpdef]
    field_simp
    ring
  have h2 : 4 * M + 1 ≤ 2 * p + 1 := by
    rw [hp_eq, le_div_iff₀ hα]
    nlinarith
  have hnum := inv_sqrt_add_inv_sqrt_le hM1 h1 h2
  have hS : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_nonneg _
  have hpre : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
      / (α * (4 * M + 5)) :=
    div_nonneg (mul_nonneg hS (le_of_lt (Real.rpow_pos_of_pos hz _))) (le_of_lt hKpos)
  -- ## assembly
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = 1 / (α * (4 * M + 5)) *
          |z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))
            + z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| := by
        rw [hdef, abs_mul, abs_of_pos (one_div_pos.mpr hKpos)]
    _ ≤ 1 / (α * (4 * M + 5)) *
          (|z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))|
            + |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) honeK
    _ ≤ 1 / (α * (4 * M + 5)) *
          (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
              / Real.sqrt (2 * q - 1)
            + Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
              / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead' htail) honeK
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / (α * (4 * M + 5))
          * (1 / Real.sqrt (2 * q - 1) + 1 / Real.sqrt (2 * p + 1)) := by ring
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / (α * (4 * M + 5))
          * (1 / Real.sqrt M) :=
        mul_le_mul_of_nonneg_left hnum hpre
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt m) := by
        rw [← hMdef, div_mul_div_comm, mul_one]

end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.FM.Core3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## Monotonicity in `ρ` -/


/-! ## The energy identity `∫_ρ^∞ h V = V(ρ)²/2` behind the Riccati equation -/


/-! ## The substitution integral of the self-similar profile -/


/-! ## The evaluation of `L₁₂^K` on the self-similar family -/


end Work.FM
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

set_option autoImplicit false

/-- The hypotheses of the `L₁₂` zero-mode identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`, packaged. -/
structure L12Hyp (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  hα : 0 < α
  hα1 : α ≤ 1
  hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
    HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z
  hcont : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => Work.Spaces.pz f s θ) (Set.Ici 0)
  hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0)
  hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0
  hint : MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
    (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
  hintL : MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
      * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
  hintL2 : MeasureTheory.IntegrableOn (fun z => Work.Construction.L12dens f z) (Set.Ioi 0)
  hint3 : MeasureTheory.IntegrableOn
    (fun z => Work.Construction.L12dens (Work.Coercivity.LGamma α f) z) (Set.Ioi 0)

/-- `uOf f r = L₁₂dens f r`, the density of `L₁₂(f)`. -/
def uOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ := Work.Construction.L12dens f

/-- `GOf α f r = L₁₂dens(𝓛_Γ f) r`, the density of `L₁₂(𝓛_Γ f)`. -/
def GOf (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  Work.Construction.L12dens (Work.Coercivity.LGamma α f)

/-- `ROf f r = L₁₂f f r = ∫_r^∞ uOf f`, the tail integral of the density of `L₁₂(f)`. -/
def ROf (f : ℝ → ℝ → ℝ) : ℝ → ℝ := Work.Coercivity.L12f f

/-- `NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)`, the `z`-integral form of `-∫_{Iθ} K(θ) f(r,θ)`. -/
def NOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ, Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2

/-- `mdOf f r = ∫_{Iθ} K(θ) ∂_z f(r,θ) dθ`, the angular integral of `∂_z f`. -/
def mdOf (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ

@[simp] theorem uOf_eq (f : ℝ → ℝ → ℝ) : uOf f = Work.Construction.L12dens f := rfl
@[simp] theorem GOf_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    GOf α f = Work.Construction.L12dens (Work.Coercivity.LGamma α f) := rfl
@[simp] theorem ROf_eq (f : ℝ → ℝ → ℝ) : ROf f = Work.Coercivity.L12f f := rfl
@[simp] theorem NOf_eq (f : ℝ → ℝ → ℝ) : NOf f
    = fun r => ∫ p in (Set.Ioi r) ×ˢ Work.Spaces.Iθ,
        Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 := rfl
@[simp] theorem mdOf_eq (f : ℝ → ℝ → ℝ) : mdOf f
    = fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ := rfl

end Work.FTS.Apriori.ZeroMode
end
end
-- ===== merged: Submission.Work.FTS.Apriori.ZeroMode.L12_sum_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Additivity of the `L₁₂` zero mode over finite sums

The operator `L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds` is the composition of the
angular integral and the radial integral, both of which are additive over finite sums as soon as
the summands are integrable (`MeasureTheory.integral_finsetSum`).  The two families of
integrability hypotheses in the statement are precisely what is needed: the angular slices on
`Iθ` for `z > 0` (the only `z` for which the density is used, as `L₁₂(·)(0)` integrates over
`Ioi 0`) and the radial integrability of each density on `Ioi 0`.

Since the angular identity only holds for `z > 0`, the density of the sum is compared with the
sum of the densities *on* `Ioi 0` and transported to the radial integral by
`MeasureTheory.setIntegral_congr_fun` (a congruent integral needs no integrability).
-/

namespace Work.FTS.Apriori.ZeroMode

open MeasureTheory Set

theorem L12_sum_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℝ → ℝ → ℝ)
    (hθ : ∀ i ∈ s, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * F i z θ / z) Work.Spaces.Iθ)
    (hF : ∀ i ∈ s, MeasureTheory.IntegrableOn
      (fun z => Work.Construction.L12dens (F i) z) (Set.Ioi 0)) :
    Work.Construction.L12 (fun z θ => ∑ i ∈ s, F i z θ) 0
      = ∑ i ∈ s, Work.Construction.L12 (F i) 0 := by
  -- Unfold the two layer of definitions on the densities on the right-hand side.
  have hF' : ∀ i ∈ s, MeasureTheory.IntegrableOn
      (fun z => Work.FM.L12dens Work.Spaces.K (F i) z) (Set.Ioi 0) := by
    intro i hi
    simpa only [Work.Construction.L12dens] using hF i hi
  -- The angular density of the sum is the sum of the angular densities, for `z > 0`.
  have hdens : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FM.L12dens Work.Spaces.K (fun z θ => ∑ i ∈ s, F i z θ) z
        = ∑ i ∈ s, Work.FM.L12dens Work.Spaces.K (F i) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hcongr : (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (∑ i ∈ s, F i z θ) / z)
        = ∫ θ in Set.Icc 0 (Real.pi / 2),
            ∑ i ∈ s, Work.Spaces.K θ * F i z θ / z := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [Finset.mul_sum, Finset.sum_div]
    simp only [Work.FM.L12dens]
    rw [hcongr]
    exact MeasureTheory.integral_finsetSum s (fun i hi => hθ i hi z hzpos)
  -- The radial integral, written through the (unfolded) definition of `L₁₂`.
  have houter :
      (∫ z in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (fun z θ => ∑ i ∈ s, F i z θ) z)
        = ∑ i ∈ s, ∫ z in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (F i) z := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hdens]
    exact MeasureTheory.integral_finsetSum s hF'
  simpa only [Work.Construction.L12, Work.FM.L12] using houter

end Work.FTS.Apriori.ZeroMode
end
-- ===== merged: Submission.Work.FTS.ClassC.Fstar_bslOp_moment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `L(Ψ)`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates', Step 1 of `prop:L2`.

The `α = 0` part `L₀` of the elliptic operator (PolarBSL) is formally adjoint to the angular
weight `sin θ cos²θ` on `[0,π/2]` with Dirichlet conditions
(`Work.Elliptic.Lzero_orthogonal`), so the angular moment
`F_*(F)(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` of the full operator
`L(Ψ) = bslOp α Ψ` is the sum of the moments of the two radial terms only:

  `F_*(bslOp α Ψ)(z) = -(α²z²)·F_*(∂_zzΨ)(z) - α(5+α)z·F_*(∂_zΨ)(z)`.

The proof is linearity of the Bochner integral (`integral_add`, `integral_neg`,
`integral_const_mul`) applied to the definitional splitting
`bslOp α Ψ = -(α²z²)∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` together with `Lzero_orthogonal`; the three
`IntegrableOn` hypotheses are exactly the side conditions the splitting needs.

Note on notation: the statement below is written with the `π` notation of `Mathlib`, which
requires the scoped notation `Real` to be open (`open scoped Real` below); the lakefile sets
`autoImplicit = false`, so without it `π` would simply be an unknown identifier.
-/
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

theorem Fstar_bslOp_moment {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)))
    (h0 : Ψ z 0 = 0) (h1 : Ψ z (π / 2) = 0)
    (hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntL : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z := by
  -- `sin θ cos²θ` is annihilated by the adjoint of `L₀` on the Dirichlet slice
  have hL := Work.Elliptic.Lzero_orthogonal Ψ z hslice h0 h1
  -- the three summands of `bslOp α Ψ z θ * sinCos2 θ`
  set A : ℝ → ℝ :=
    fun θ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ with hAdef
  set B : ℝ → ℝ :=
    fun θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ with hBdef
  set L : ℝ → ℝ :=
    fun θ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ with hLdef
  have hAi : MeasureTheory.IntegrableOn A Work.Spaces.Iθ := by rw [hAdef]; exact hIntA
  have hBi : MeasureTheory.IntegrableOn B Work.Spaces.Iθ := by rw [hBdef]; exact hIntB
  have hLi : MeasureTheory.IntegrableOn L Work.Spaces.Iθ := by rw [hLdef]; exact hIntL
  -- the constants come out of the moment
  have hAeval : (∫ θ in Work.Spaces.Iθ, A θ)
      = (α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, A θ)
        = ∫ θ in Work.Spaces.Iθ,
            (α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      simp only [hAdef]
      ring
    rw [h1, MeasureTheory.integral_const_mul]
  have hBeval : (∫ θ in Work.Spaces.Iθ, B θ)
      = (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, B θ)
        = ∫ θ in Work.Spaces.Iθ,
            (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      simp only [hBdef]
      ring
    rw [h1, MeasureTheory.integral_const_mul]
  have hLeval : (∫ θ in Work.Spaces.Iθ, L θ) = 0 := hL
  -- linearity of the integral over the definitional splitting of `bslOp`
  have key : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ)
      = -(∫ θ in Work.Spaces.Iθ, A θ) - (∫ θ in Work.Spaces.Iθ, B θ)
        + (∫ θ in Work.Spaces.Iθ, L θ) := by
    have hpt : ∀ θ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ = -A θ - B θ + L θ := by
      intro θ
      simp only [hAdef, hBdef, hLdef, Work.Elliptic.bslOp_apply]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_add (f := fun θ => -A θ - B θ) (g := L)
      (hAi.neg.sub hBi) hLi]
    rw [MeasureTheory.integral_sub (f := fun θ => -A θ) (g := B) hAi.neg hBi]
    rw [MeasureTheory.integral_neg (f := A)]
  have hgoal : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ)
      = -(α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        - (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    rw [key, hAeval, hBeval, hLeval]
    ring
  simpa only [Work.Elliptic.Fstar] using hgoal

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.far_inner =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

theorem far_inner {p L a b : ℝ} (hp : 0 < p) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    {c : ℝ → ℝ} (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (hc : ∀ t ∈ Set.Icc a b, |c t| ≤ L) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioc a b) ∧
      |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)| ≤ L * a ^ (-p) / p := by
  have hp1 : -p - 1 < -1 := by linarith
  -- the majorant `t ↦ L * t ^ (-p - 1)` is integrable on `Ioc a b`
  have hpow_int : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioc a b) :=
    (integrableOn_Ioi_rpow_of_lt hp1 ha).mono_set Set.Ioc_subset_Ioi_self
  have hL_int : MeasureTheory.IntegrableOn (fun t : ℝ => L * t ^ (-p - 1)) (Set.Ioc a b) :=
    hpow_int.const_mul L
  -- measurability of the power function on `Ioc a b` (where it is continuous)
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioc a b) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-p - 1)
      (Or.inl (ne_of_gt (ha.trans ht.1)))).continuousWithinAt
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-p - 1))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hcm.mul (hcont.aestronglyMeasurable measurableSet_Ioc)
  -- pointwise domination on `Ioc a b`
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      ‖c t * t ^ (-p - 1)‖ ≤ L * t ^ (-p - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ha.trans ht.1
    have hpownn : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg htpos.le _
    have hct : |c t| ≤ L := hc t ⟨le_of_lt ht.1, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownn]
    exact mul_le_mul_of_nonneg_right hct hpownn
  have hintc : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioc a b) :=
    MeasureTheory.Integrable.mono' hL_int hmeas hbound
  refine ⟨hintc, ?_⟩
  -- `|∫ f| ≤ ∫ |f| ≤ ∫ L t^{-p-1} ≤ L a^{-p}/p`
  have h1 : |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, |c t * t ^ (-p - 1)| := by
    have := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b)) (fun t : ℝ => c t * t ^ (-p - 1))
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∫ t in Set.Ioc a b, |c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_mono_on ?_ hL_int measurableSet_Ioc ?_
    · exact hintc.norm
    · intro t ht
      have htpos : 0 < t := ha.trans ht.1
      have hpownn : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg htpos.le _
      have hct : |c t| ≤ L := hc t ⟨le_of_lt ht.1, ht.2⟩
      rw [abs_mul, abs_of_nonneg hpownn]
      exact mul_le_mul_of_nonneg_right hct hpownn
  have h3 : ∫ t in Set.Ioc a b, L * t ^ (-p - 1) = L * ∫ t in Set.Ioc a b, t ^ (-p - 1) :=
    MeasureTheory.integral_const_mul L (fun t : ℝ => t ^ (-p - 1))
  have h4 : ∫ t in Set.Ioc a b, t ^ (-p - 1) ≤ ∫ t in Set.Ioi a, t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt hp1 ha) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_trans ha.le (le_of_lt ht)) _
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have h5 : ∫ t in Set.Ioi a, t ^ (-p - 1) = a ^ (-p) / p := by
    rw [integral_Ioi_rpow_of_lt hp1 ha, show -p - 1 + 1 = -p from by ring, neg_div_neg_eq]
  calc |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (-p - 1) := le_trans h1 h2
    _ = L * ∫ t in Set.Ioc a b, t ^ (-p - 1) := h3
    _ ≤ L * (a ^ (-p) / p) := mul_le_mul_of_nonneg_left (le_trans h4 (le_of_eq h5)) hL
    _ = L * a ^ (-p) / p := by ring

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Hcoef.near_inner =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

theorem near_inner {q L a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    {c : ℝ → ℝ} (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (hc : ∀ t ∈ Set.Icc a b, |c t| ≤ L) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc a b) ∧
      |∫ t in Set.Ioc a b, c t * t ^ (q - 1)| ≤ L * b ^ q / q := by
  -- The pure power `t ↦ t ^ (q - 1)` is integrable on `Ioc a b` (`a > 0`, `q > 0`),
  -- and its integral is `(b ^ q - a ^ q) / q`.
  have hpow_int : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hpow_val : ∫ t in Set.Ioc a b, t ^ (q - 1) = (b ^ q - a ^ q) / q := by
    rw [← intervalIntegral.integral_of_le hab, integral_rpow (Or.inl (by linarith))]
    have : q - 1 + 1 = q := by ring
    rw [this]
  have hdom_int : MeasureTheory.IntegrableOn (fun t : ℝ => L * t ^ (q - 1)) (Set.Ioc a b) :=
    hpow_int.const_mul L
  -- Pointwise domination on `Ioc a b`.
  have hnorm : ∀ t ∈ Set.Ioc a b, ‖c t * t ^ (q - 1)‖ ≤ L * t ^ (q - 1) := by
    intro t ht
    have htpos : 0 < t := lt_trans ha ht.1
    have hle : 0 ≤ t ^ (q - 1) := Real.rpow_nonneg htpos.le _
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hle]
    exact mul_le_mul_of_nonneg_right (hc t htIcc) hle
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      ‖c t * t ^ (q - 1)‖ ≤ L * t ^ (q - 1) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun t ht => hnorm t ht)
  have hprod_int : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc a b) := by
    refine MeasureTheory.Integrable.mono' hdom_int ?_ hbound
    have haesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (q - 1))
        (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
      (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_trans ha hx.1)))).aestronglyMeasurable measurableSet_Ioc
    exact hcm.mul haesm
  refine ⟨hprod_int, ?_⟩
  have h1 : |∫ t in Set.Ioc a b, c t * t ^ (q - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) := by
    calc |∫ t in Set.Ioc a b, c t * t ^ (q - 1)|
        = ‖∫ t in Set.Ioc a b, c t * t ^ (q - 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t in Set.Ioc a b, ‖c t * t ^ (q - 1)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) :=
          MeasureTheory.integral_mono_ae hprod_int.norm hdom_int hbound
  have h2 : ∫ t in Set.Ioc a b, L * t ^ (q - 1) = L * ((b ^ q - a ^ q) / q) := by
    rw [MeasureTheory.integral_const_mul, hpow_val]
  have h3 : L * ((b ^ q - a ^ q) / q) ≤ L * b ^ q / q := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hq.le) hL
    have haq : 0 ≤ a ^ q := Real.rpow_nonneg ha.le q
    linarith
  calc |∫ t in Set.Ioc a b, c t * t ^ (q - 1)| ≤ ∫ t in Set.Ioc a b, L * t ^ (q - 1) := h1
    _ = L * ((b ^ q - a ^ q) / q) := h2
    _ ≤ L * b ^ q / q := h3

end Work.FTS.ClassCHon.Hcoef
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.SliceMassAux

/-- Pointwise weighted AM–GM: for `s > 0` and `θ ∈ Iθ`,

  `2 |ab| sin(2θ)^{-η} ≤ a² w(s)² sin(2θ)^{-η} + (s b)² w(s)² sin(2θ)^{-η}`,

i.e. `2 |a| |s b| ≤ a² + (s b)²` (plain AM–GM) multiplied by `w(s)² sin(2θ)^{-η}`,
using the elementary bound `1 ≤ s · w(s)² = (1+s)⁴/s³` valid for `s > 0`. -/
theorem pointwise_amgm {s θ a b : ℝ} (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    2 * |a * b| * Work.FTS.EllipticEst.sEta θ
      ≤ a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  -- nonnegativity of the angular weight on `Iθ`
  have hη : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    apply Real.rpow_nonneg
    have h2θ : (2 * θ) ∈ Set.Icc 0 Real.pi := by
      constructor
      · have := hθ.1; linarith
      · have := hθ.2; linarith
    exact Real.sin_nonneg_of_mem_Icc h2θ
  -- `1 ≤ s · w(s)² = (1+s)⁴/s³`
  have hsw : 1 ≤ s * (Work.Spaces.w s) ^ 2 := by
    have hw : s * (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 3 := by
      rw [Work.Spaces.w]
      field_simp
    rw [hw]
    rw [one_le_div (by positivity)]
    nlinarith [sq_nonneg s, sq_nonneg (1 + s), sq_nonneg (s - 1), hs]
  have hW2 : 0 ≤ (Work.Spaces.w s) ^ 2 := sq_nonneg _
  -- plain AM–GM for `|a|` and `|s b|`
  have hamgm : 2 * |a| * |s * b| ≤ a ^ 2 + (s * b) ^ 2 := by
    have h := two_mul_le_add_sq |a| |s * b|
    rw [sq_abs a, sq_abs (s * b)] at h
    exact h
  have habs : |s * b| = s * |b| := by rw [abs_mul, abs_of_pos hs]
  have hx : 0 ≤ 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ := by positivity
  have hWη : 0 ≤ (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_nonneg hW2 hη
  calc 2 * |a * b| * Work.FTS.EllipticEst.sEta θ
      = 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ := by rw [abs_mul]; ring
    _ ≤ 2 * |a| * |b| * Work.FTS.EllipticEst.sEta θ * (s * (Work.Spaces.w s) ^ 2) := by
        nlinarith [mul_nonneg hx (by linarith : (0:ℝ) ≤ s * (Work.Spaces.w s) ^ 2 - 1)]
    _ = 2 * |a| * |s * b| * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [habs]; ring
    _ ≤ (a ^ 2 + (s * b) ^ 2) * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        nlinarith [hamgm, hWη]
    _ = a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ := by ring

end Work.FTS.ClassCHon.SliceMassAux
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped ENNReal
open scoped Real

namespace Work.FTS.ClassCHon.SliceMassUpgrade


end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.WeightIntegrals

/-!
# The far-field weighted integral bound

We prove

  `∫_{t > z} t ^ (-2P-2) / w(t)^2 ≤ z ^ (-2P) / (2P - 3)`   for `z > 0`, `P > 3/2`,

where `w(t) = (1+t)^2/t^2`.  Since `w(t)^2 = (1+t)^4/t^4`, on `t > 0` the integrand equals
`t ^ (2 - 2 P) / (1 + t) ^ 4`, and the estimate follows by comparing with a pure power:

* if `0 < z ≤ 1`, one has `(1+t)^(-4) ≤ 1`, so the integrand is at most `t^(2-2P)`, and
  `∫_z^∞ t^(2-2P) = z^(3-2P)/(2P-3) ≤ z^(-2P)/(2P-3)`;
* if `1 ≤ z`, one has `t^4/(1+t)^4 ≤ 1`, so the integrand is at most `t^(-2P-2)`, and
  `∫_z^∞ t^(-2P-2) = z^(-2P-1)/(2P+1) ≤ z^(-2P)/(2P-3)`.
-/

/-- Reduction of the far-field integrand to a pure power over a positive denominator:
for `t > 0`, `t^(-2P-2) / w(t)^2 = t^(2-2P) / (1+t)^4`. -/
private lemma rpow_div_w_sq_eq {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 = t ^ (2 - 2 * P) / (1 + t) ^ 4 := by
  have hinv : ((Work.Spaces.w t) ^ 2)⁻¹ = t ^ 4 / (1 + t) ^ 4 := by
    rw [Work.Spaces.w, div_pow]; field_simp
  have hpow : t ^ (-2 * P - 2) * t ^ 4 = t ^ (2 - 2 * P) := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_add ht]
    ring_nf
  calc t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
      = t ^ (-2 * P - 2) * ((Work.Spaces.w t) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    _ = t ^ (-2 * P - 2) * (t ^ 4 / (1 + t) ^ 4) := by rw [hinv]
    _ = t ^ (-2 * P - 2) * t ^ 4 / (1 + t) ^ 4 := by rw [mul_div_assoc]
    _ = t ^ (2 - 2 * P) / (1 + t) ^ 4 := by rw [hpow]

/-- Nonnegativity of the far-field integrand at a nonnegative point. -/
private lemma rpow_div_w_sq_nonneg {P t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 :=
  div_nonneg (Real.rpow_nonneg ht _) (sq_nonneg _)

/-- Pointwise domination by the exponent `2 - 2P` (used for `z ≤ 1`). -/
private lemma rpow_div_w_sq_le_hi {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 ≤ t ^ (2 - 2 * P) := by
  rw [rpow_div_w_sq_eq ht, div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 + t) 4)]
  nth_rewrite 1 [← mul_one (t ^ (2 - 2 * P))]
  exact mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 4) (by linarith))
    (Real.rpow_nonneg ht.le _)

/-- Pointwise domination by the exponent `-2P - 2` (used for `1 ≤ z`). -/
private lemma rpow_div_w_sq_le_lo {P t : ℝ} (ht : 0 < t) :
    t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2 ≤ t ^ (-2 * P - 2) := by
  have hpow : t ^ (2 - 2 * P) = t ^ (-2 * P - 2) * t ^ 4 := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_add ht]
    ring_nf
  rw [rpow_div_w_sq_eq ht, hpow,
    div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 + t) 4)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le (by linarith) 4)
    (Real.rpow_nonneg ht.le _)

theorem far_weight_integral_le {z P : ℝ} (hz : 0 < z) (hP : 3 / 2 < P) :
    ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
      ≤ z ^ (-2 * P) / (2 * P - 3) := by
  have hz0 : (0:ℝ) < 2 * P - 3 := by linarith
  rcases le_total z 1 with hz1 | hz1
  · -- Case `z ≤ 1`: compare with `t ↦ t ^ (2 - 2P)`.
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 - 2 * P)) (Set.Ioi z) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    have hle : (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)] (fun t : ℝ => t ^ (2 - 2 * P)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_le_hi (lt_trans hz (Set.mem_Ioi.mp ht))
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_nonneg (le_of_lt (lt_trans hz (Set.mem_Ioi.mp ht)))
    calc ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi z, t ^ (2 - 2 * P) :=
          MeasureTheory.integral_mono_of_nonneg hnn hg hle
      _ = z ^ (3 - 2 * P) / (2 * P - 3) := by
          rw [integral_Ioi_rpow_of_lt (a := 2 - 2 * P) (c := z) (by linarith) hz]
          rw [show (2:ℝ) - 2 * P + 1 = 3 - 2 * P from by ring]
          rw [div_eq_div_iff (by linarith : (3:ℝ) - 2 * P ≠ 0) (ne_of_gt hz0)]
          ring
      _ ≤ z ^ (-2 * P) / (2 * P - 3) :=
          div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge (x := z) (y := 3 - 2 * P) (z := -2 * P)
              hz hz1 (by linarith)) hz0.le
  · -- Case `1 ≤ z`: compare with `t ↦ t ^ (-2P-2)`.
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-2 * P - 2)) (Set.Ioi z) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    have hle : (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)] (fun t : ℝ => t ^ (-2 * P - 2)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_le_lo (lt_trans hz (Set.mem_Ioi.mp ht))
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun t : ℝ => t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact rpow_div_w_sq_nonneg (le_of_lt (lt_trans hz (Set.mem_Ioi.mp ht)))
    calc ∫ t in Set.Ioi z, t ^ (-2 * P - 2) / (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi z, t ^ (-2 * P - 2) :=
          MeasureTheory.integral_mono_of_nonneg hnn hg hle
      _ = z ^ (-2 * P - 1) / (2 * P + 1) := by
          rw [integral_Ioi_rpow_of_lt (a := -2 * P - 2) (c := z) (by linarith) hz]
          rw [show -2 * P - 2 + 1 = -2 * P - 1 from by ring]
          rw [div_eq_div_iff (by linarith : (-2:ℝ) * P - 1 ≠ 0) (by linarith : (2:ℝ) * P + 1 ≠ 0)]
          ring
      _ ≤ z ^ (-2 * P) / (2 * P - 3) := by
          rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * P + 1) hz0]
          exact mul_le_mul
            (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by linarith)
            (by linarith) (Real.rpow_nonneg (le_of_lt hz) _)

end Work.FTS.ClassCHon.WeightIntegrals
end
-- ===== merged: Submission.Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.WeightIntegrals

open MeasureTheory Set

/-- **The near weight integral.**  For `0 < z` and `1 < Q`,

  `∫_{(0,z]} t^{2Q-2} / w(t)² dt ≤ z^{2Q} / (2Q-1)`,   `w(t) = (1+t)²/t²`.

The substitution `t^{2Q-2}/w(t)² = t^{2Q+2}/(1+t)⁴` (`near_pow_form`) turns the integrand into
a function that behaves like `t^{2Q-2}` for large `t` and like `t^{2Q+2}` for small `t`; the
elementary pointwise comparison

  `t^{2Q+2}/(1+t)⁴ ≤ (2Q/(2Q-1)) · t^{2Q-1}   (t > 0)`,

which only uses `t³ ≤ (1+t)⁴` and `1 ≤ 2Q/(2Q-1)`, dominates the integrand by a multiple of
`t^{2Q-1}`; integrating that over `(0,z]` gives exactly `z^{2Q}/(2Q-1)`.  No case distinction on
`z` is needed. -/
theorem near_weight_integral_le {z Q : ℝ} (hz : 0 < z) (hQ : 1 < Q) :
    ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2
      ≤ z ^ (2 * Q) / (2 * Q - 1) := by
  have hQ1 : (0 : ℝ) < 2 * Q - 1 := by linarith
  -- The pointwise domination by a multiple of `t^{2Q-1}`.
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) z,
      t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2 ≤ (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [Work.FTS.ClassCHon.near_pow_form ht0.le hQ]
    have h1t : (0 : ℝ) < 1 + t := by linarith
    rw [div_le_iff₀ (Real.rpow_pos_of_pos h1t 4)]
    have hc : (1 : ℝ) ≤ 2 * Q / (2 * Q - 1) := by
      rw [one_le_div (by linarith)]
      linarith
    have h3 : t ^ (3 : ℝ) ≤ (1 + t) ^ (4 : ℝ) := by
      have ha : t ^ (3 : ℝ) ≤ (1 + t) ^ (3 : ℝ) :=
        Real.rpow_le_rpow ht0.le (by linarith) (by norm_num : (0 : ℝ) ≤ 3)
      have hb : (1 + t) ^ (3 : ℝ) ≤ (1 + t) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (3 : ℝ) ≤ 4)
      linarith
    have hmain : t ^ (3 : ℝ) ≤ (2 * Q / (2 * Q - 1)) * (1 + t) ^ (4 : ℝ) :=
      le_trans h3 (le_mul_of_one_le_left (Real.rpow_nonneg h1t.le 4) hc)
    calc t ^ (2 * Q + 2) = t ^ (2 * Q - 1) * t ^ (3 : ℝ) := by
          rw [← Real.rpow_add ht0, show 2 * Q - 1 + 3 = 2 * Q + 2 by ring]
      _ ≤ t ^ (2 * Q - 1) * ((2 * Q / (2 * Q - 1)) * (1 + t) ^ (4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg ht0.le _)
      _ = (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) * (1 + t) ^ (4 : ℝ) := by ring
  -- Integrability of the dominating function on `(0,z]`.
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 * Q - 1)) (Set.Ioc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := z) (r := 2 * Q - 1)
        (by linarith : -1 < 2 * Q - 1))
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1)) (Set.Ioc 0 z) :=
    hbase.const_mul _
  -- The monotone comparison of the two set integrals.
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict (Set.Ioc (0 : ℝ) z))
    (f := fun t => t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2)
    (g := fun t => (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1))
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))
    hint
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpt t ht)
  -- Evaluation of the dominating integral.
  have hIntg : ∫ t in Set.Ioc (0 : ℝ) z, (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1)
      = z ^ (2 * Q) / (2 * Q - 1) := by
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.ClassCHon.integral_Ioc_rpow_eq hz (by linarith : -1 < 2 * Q - 1)]
    rw [show 2 * Q - 1 + 1 = 2 * Q by ring]
    have h1 : (2 * Q - 1 : ℝ) ≠ 0 := by linarith
    have h2 : (2 * Q : ℝ) ≠ 0 := by linarith
    field_simp
  calc ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2
      ≤ ∫ t in Set.Ioc (0 : ℝ) z, (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) := hmono
    _ = z ^ (2 * Q) / (2 * Q - 1) := hIntg

end Work.FTS.ClassCHon.WeightIntegrals
end
-- ===== merged: Submission.Work.FTS.ClassCHon.radGreen_size_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_size_bound`

The **mode-uniform size bound** for the radial Euler Green function
`radGreen α m c` on a *compactly supported* source, with an absolute constant `A`:

  `m² · |radGreen α m c z| ≤ A · M`

for every `α ∈ (0, 1/4]`, every `m ≥ 1`, every source `c` which is `C^∞` on `(0,∞)`,
bounded by `M ≥ 0` and vanishes off an interval `[a,b]` with `a > 0`, and every `z > 0`.
The single constant `A` is *independent* of `α`, `m`, `a`, `b`, `M`, `c` and `z`; we use
`A = 1/4` (which is essentially sharp, see the asymptotics below).

## The computation

With `q := (2m+5)/α > 0` and `p := 2m/α > 0`, the definition

  `radGreen α m c z = 1/(α(4m+5)) · ( z^{-q} ∫_0^z c t^{q-1} dt + z^{p} ∫_z^∞ c t^{-p-1} dt )`

gives, using only `|c| ≤ M` and the two elementary rpow integrals
(`∫_0^z t^{q-1} = z^q/q` for `q > 0`, `∫_z^∞ t^{-p-1} = z^{-p}/p` for `p > 0`, `z > 0`):

  `z^{-q} · |∫_0^z c t^{q-1}| ≤ z^{-q} · M z^q/q = M/q = Mα/(2m+5)`,
  `z^{p} · |∫_z^∞ c t^{-p-1}| ≤ z^{p} · M z^{-p}/p = M/p = Mα/(2m)`.

Hence

  `|radGreen α m c z| ≤ Mα/(α(4m+5)) · (1/(2m+5) + 1/(2m)) = M/(4m+5) · (1/(2m+5) + 1/(2m))`,

and since `1/(2m+5) ≤ 1/(2m)` for `m ≥ 1`,

  `m² |radGreen α m c z| ≤ M · m²/(4m+5) · (1/m) = M · m/(4m+5) ≤ M/4`.

(The bound is sharp: `m²/(4m+5)·(1/(2m+5)+1/(2m)) → 1/4` as `m → ∞`.)

Nothing beyond `|c| ≤ M` and `z > 0` is used: neither the continuity hypothesis, nor the
support hypothesis, nor `0 < a`, nor `0 ≤ M` is needed for the *inequality* itself (they are
part of the requested statement).  The two integral estimates are isolated in the private
lemmas `near_int_bound` and `far_int_bound`.

Note that the `a`-smallness is irrelevant here (unlike in the pointwise near-field and
far-field bounds `radGreen_near_pointwise_bound` / `radGreen_far_pointwise_bound` of
`FTS/ClassC/HonestCut/`): the *global* `m`-uniform `L^∞` bound uses only the size of the
source and the explicit form of the Green kernel.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassCHon




end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T

open scoped Real

/-- The angular coefficient `q(θ) = cos(2θ) - 1/3` of the paper's `Γ`-regularity lemma is
bounded by `4/3 ≤ 2` on the whole line. -/
lemma abs_qfun_le_two (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 2 := by
  rw [Work.Spaces.qfun_apply]
  have h : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  calc |Real.cos (2 * θ) - 1 / 3| ≤ |Real.cos (2 * θ)| + |(1 / 3 : ℝ)| := abs_sub _ _
    _ ≤ 1 + 1 / 3 := by
        have : |(1 / 3 : ℝ)| = 1 / 3 := abs_of_pos (by norm_num)
        linarith
    _ ≤ 2 := by norm_num

theorem gammaPointwiseBnd_fts (α : ℝ) (hα : 0 < α) :
    Work.Coercivity.GammaPointwiseBnd α := by
  intro θ hθ
  rcases hθ.1.eq_or_lt with h0 | h0
  · -- θ = 0: both sides vanish because `sin 0 = 0`
    subst h0
    rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul, abs_zero]
    have hG := (Work.Spaces.Gam_bounds α 0 hα hθ).1
    exact mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * α) hG
  rcases hθ.2.eq_or_lt with h1 | h1
  · -- θ = π/2: both sides vanish because `sin π = 0`
    subst h1
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul, abs_zero]
    have hG := (Work.Spaces.Gam_bounds α (Real.pi / 2) hα hθ).1
    exact mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * α) hG
  · -- interior: `D_θΓ = α q Γ`
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, h1⟩
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    have hbase : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
    have hGpos : 0 < Work.Spaces.Gam α θ := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_pos_of_pos hbase _
    have hkey : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
      rw [← Work.Spaces.dthU_apply]
      exact Work.Spaces.dthU_Gam α θ hα hθ'
    rw [hkey, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hGpos]
    have hq := abs_qfun_le_two θ
    have h1' : α * |Work.Spaces.qfun θ| ≤ α * 2 :=
      mul_le_mul_of_nonneg_left hq (le_of_lt hα)
    calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
        ≤ α * 2 * Work.Spaces.Gam α θ :=
          mul_le_mul_of_nonneg_right h1' (le_of_lt hGpos)
      _ = 2 * α * Work.Spaces.Gam α θ := by ring

end Work.FTS.CoercivityFix.Coer1T
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

/-- `Zop` is the one-dimensional operator `u ↦ (z ↦ z·u'(z))` (see
`Work.Spaces.Zop`).  Equality of two functions on an *open* set propagates to their
derivatives on that set (`Set.EqOn.deriv`), hence to every iterate of `Zop`. -/
theorem Zop_iterate_eqOn_of_eqOn (b : ℕ) {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (h : Set.EqOn f g s) :
    Set.EqOn (Work.Spaces.Zop^[b] f) (Work.Spaces.Zop^[b] g) s := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    intro z hz
    simp only [Function.iterate_succ', Function.comp_apply, Work.Spaces.Zop]
    rw [ih.deriv hs hz]

end Work.FTS.CoercivityFix.E2Bound.SlotMul
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound

/-- The Möbius chart `z ↦ (z - 1)/(z + 1)`, mapping `(0,∞)` onto `(-1,1)`. -/
def zchart (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- Evaluation of a polynomial in the chart variable: `z ↦ P.eval (zchart z)`. -/
def gpoly (P : Polynomial ℝ) : ℝ → ℝ := fun z => P.eval (zchart z)

/-- The polynomial map induced by `Zop` on the chart side: `P ↦ ½(1 - X²)·P'`. -/
def Tmul (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative P

/-- The polynomial whose chart-side evaluation is `φ(z) = z/(1+z)²`, namely `¼(1 - X²)`. -/
def Pphi : Polynomial ℝ := Polynomial.C (1 / 4) * (1 - Polynomial.X ^ 2)

@[simp] lemma zchart_apply (z : ℝ) : zchart z = (z - 1) / (z + 1) := rfl

@[simp] lemma gpoly_apply (P : Polynomial ℝ) (z : ℝ) : gpoly P z = P.eval (zchart z) := rfl

@[simp] lemma Tmul_apply (P : Polynomial ℝ) :
    Tmul P = Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative P := rfl

@[simp] lemma Pphi_eq : Pphi = Polynomial.C (1 / 4) * (1 - Polynomial.X ^ 2) := rfl

/-- For `z > 0` the chart variable lies in `(-1,1)`. -/
lemma abs_zchart_lt_one {z : ℝ} (hz : 0 < z) : |zchart z| < 1 := by
  have h1 : (0 : ℝ) < z + 1 := by linarith
  rw [zchart, abs_div, abs_of_pos h1, div_lt_one h1]
  rw [abs_lt]
  constructor <;> linarith

lemma abs_zchart_le_one {z : ℝ} (hz : 0 < z) : |zchart z| ≤ 1 :=
  le_of_lt (abs_zchart_lt_one hz)

lemma zchart_ne_neg_one {z : ℝ} (hz : 0 < z) : z ≠ -1 := by linarith

end Work.FTS.CoercivityFix.E2Bound
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1Endpoint.G1_sq_div_cube_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.G1Endpoint

/-- Elementary algebra behind `G1_sq_div_cube_le`: since `G1 α m c x = x ^ (-a) · G1A α m c x`
with `a = G1a α m`, the quotient `G1 x²/x³` is `G1A x²/x^{2a+3}`; no sign hypothesis on `a`
is needed because `x ` is positive and hence `x ^ (2a+3) > 0`. -/
private lemma sq_mul_rpow_neg_div (x a A : ℝ) (hx : 0 < x) :
    (x ^ (-a) * A) ^ 2 / x ^ 3 = A ^ 2 / x ^ (2 * a + 3) := by
  have h1 : (x ^ (-a)) ^ 2 = x ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    have : (-a) * ((2 : ℕ) : ℝ) = -(2 * a) := by ring
    rw [this]
  have h2 : x ^ (-(2 * a)) * x ^ (2 * a + 3) = x ^ 3 := by
    rw [← Real.rpow_add hx]
    have : -(2 * a) + (2 * a + 3) = (3 : ℝ) := by ring
    rw [this]
    exact Real.rpow_natCast x 3
  have hxA : (x ^ (-a) * A) ^ 2 = x ^ (-(2 * a)) * A ^ 2 := by
    rw [mul_pow, h1]
  have key : x ^ (-(2 * a)) = x ^ 3 / x ^ (2 * a + 3) := by
    rw [eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hx _))]
    exact h2
  rw [hxA, key]
  field_simp

theorem G1_sq_div_cube_le {α : ℝ} (m : ℕ) {c : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (h : Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3))) :
    Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
      ≤ Work.FTS.EllExist.Honesty.G1M0 c / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by
  have hxpow : 0 < x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) :=
    Real.rpow_pos_of_pos hx _
  have hG1 : Work.FTS.EllExist.Honesty.G1 α m c x ^ 2 / x ^ 3
      = Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
          / x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by
    rw [Work.FTS.EllExist.Honesty.G1_eq_zpow_mul_G1A,
      Work.FTS.EllExist.Honesty.G1s_eq_neg_G1a]
    exact sq_mul_rpow_neg_div x (Work.FTS.EllExist.Honesty.G1a α m)
      (Work.FTS.EllExist.Honesty.G1A α m c x) hx
  rw [hG1, div_le_iff₀ hxpow]
  calc Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)) := h
    _ = Work.FTS.EllExist.Honesty.G1M0 c / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
          * x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3) := by ring

end Work.FTS.EllExist.Honesty.G1Endpoint
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1Endpoint.g1A_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.G1Endpoint

open MeasureTheory Set Filter

theorem g1A_sq_le {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)) := by
  intro x hx0 hx1
  have ha : 0 < G1a α m := G1a_pos hα m
  have hsmeas : MeasurableSet (Ioo (0 : ℝ) x) := measurableSet_Ioo
  -- ### Continuity of the two Cauchy–Schwarz factors on `(0,x)`
  have hfc : ContinuousOn (fun t : ℝ => c t / t ^ 2) (Ioo (0 : ℝ) x) :=
    (hc.mono (fun t ht => ht.1)).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt ht.1))
  have hgc : ContinuousOn (fun t : ℝ => t ^ (G1a α m + 1)) (Ioo (0 : ℝ) x) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))
  -- ### Integrability of the squares on `(0,x)`
  have hf2 : Integrable (fun t : ℝ => (c t / t ^ 2) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) x)) := by
    have hInt1 : IntegrableOn (fun z : ℝ => c z ^ 2 / z ^ 4) (Ioo (0 : ℝ) x) :=
      h0.mono_set (fun z hz => ⟨hz.1, lt_trans hz.2 hx1⟩)
    refine hInt1.congr_fun ?_ hsmeas
    intro t _
    change c t ^ 2 / t ^ 4 = (c t / t ^ 2) ^ 2
    rw [div_pow, ← pow_mul]
  have hg2 : Integrable (fun t : ℝ => (t ^ (G1a α m + 1)) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) x)) := by
    have hr : IntegrableOn (fun t : ℝ => t ^ (2 * G1a α m + 2)) (Ioo (0 : ℝ) x) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hx0).mpr (by linarith)
    refine hr.congr_fun ?_ hsmeas
    intro t ht
    change t ^ (2 * G1a α m + 2) = (t ^ (G1a α m + 1)) ^ 2
    rw [pow_two, ← Real.rpow_add ht.1 (G1a α m + 1) (G1a α m + 1)]
    congr 1
    ring
  -- ### Cauchy–Schwarz
  have hcs : |∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)|
      ≤ Real.sqrt (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
        * Real.sqrt (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) :=
    Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Ioo (0 : ℝ) x))
      (hfc.aestronglyMeasurable hsmeas) (hgc.aestronglyMeasurable hsmeas) hf2 hg2
  -- ### The `D_z`-factor: `∫_0^x c t²/t⁴ ≤ M0`
  have hA : ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2 ≤ G1M0 c := by
    have h1 : ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2
        = ∫ t in Ioo (0 : ℝ) x, c t ^ 2 / t ^ 4 := by
      refine setIntegral_congr_fun hsmeas ?_
      intro t _
      change (c t / t ^ 2) ^ 2 = c t ^ 2 / t ^ 4
      rw [div_pow, ← pow_mul]
    rw [h1, G1M0]
    exact setIntegral_mono_set h0
      (Eventually.of_forall (fun t : ℝ => div_nonneg (sq_nonneg _) (by positivity)))
      (Eventually.of_forall (fun t ht => ⟨ht.1, lt_trans ht.2 hx1⟩))
  -- ### The power factor: `∫_0^x t^{2a+2} = x^{2a+3}/(2a+3)`
  have hC : ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2
      = x ^ (2 * G1a α m + 3) / (2 * G1a α m + 3) := by
    have h1 : ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2
        = ∫ t in Ioo (0 : ℝ) x, t ^ (2 * G1a α m + 2) := by
      refine setIntegral_congr_fun hsmeas ?_
      intro t ht
      change (t ^ (G1a α m + 1)) ^ 2 = t ^ (2 * G1a α m + 2)
      rw [pow_two, ← Real.rpow_add ht.1 (G1a α m + 1) (G1a α m + 1)]
      congr 1
      ring
    rw [h1, setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := x)),
      ← intervalIntegral.integral_of_le hx0.le,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * G1a α m + 2)),
      Real.zero_rpow (x := (2 * G1a α m + 2) + 1) (by intro hz; linarith [ha, hz]),
      sub_zero]
    have hexp : (2 * G1a α m + 2) + 1 = 2 * G1a α m + 3 := by ring
    rw [hexp]
  -- ### `G1A x` as a set integral of the product
  have hG1A : G1A α m c x
      = ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1) := by
    rw [G1A, intervalIntegral.integral_of_le hx0.le,
      ← setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := x))]
    refine setIntegral_congr_fun hsmeas ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    change c t * t ^ (G1a α m - 1) = c t / t ^ 2 * t ^ (G1a α m + 1)
    have key : t ^ (G1a α m - 1) * t ^ 2 = t ^ (G1a α m + 1) := by
      have h2 : t ^ 2 = t ^ (2 : ℝ) := (Real.rpow_two t).symm
      rw [h2, ← Real.rpow_add ht0 (G1a α m - 1) (2 : ℝ)]
      congr 1
      ring
    have hdiv : t ^ (G1a α m + 1) / t ^ 2 = t ^ (G1a α m - 1) := by
      rw [div_eq_iff (pow_ne_zero 2 (ne_of_gt ht0))]
      exact key.symm
    rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
  -- ### Assembly
  have hAnn : 0 ≤ ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2 :=
    setIntegral_nonneg hsmeas (fun t _ => sq_nonneg _)
  have hCnn : 0 ≤ ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2 :=
    setIntegral_nonneg hsmeas (fun t _ => sq_nonneg _)
  calc G1A α m c x ^ 2
      = (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)) ^ 2 := by rw [hG1A]
    _ = |∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.sqrt (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
          * Real.sqrt (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
    _ = (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
          * (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hCnn]
    _ ≤ G1M0 c * (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right hA hCnn
    _ = G1M0 c * (x ^ (2 * G1a α m + 3) / (2 * G1a α m + 3)) := by rw [hC]

end Work.FTS.EllExist.Honesty.G1Endpoint
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- `G1 α m c` is the product `z ↦ z^{s⁻} · G1A α m c z` (definitional). -/
theorem G1_as_product (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    G1 α m c = fun z => z ^ (G1s α m) * G1A α m c z :=
  funext fun _ => rfl

/-- **`G1A` is continuous on `(0,∞)`.**  It is in fact differentiable there, with derivative
`G1f α m c = t ↦ c t · t^{a-1}` (`G1A_hasDerivAt`), which needs only the continuity of `c` on
`(0,∞)` and the integrability of `G1f` on `(0,1)` (a consequence of `h0`). -/
theorem G1A_continuousOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ContinuousOn (G1A α m c) (Set.Ioi 0) := by
  have hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1) := G1f_integrableOn hα m hc h0
  exact fun z hz => (G1A_hasDerivAt hc hInt z hz).continuousAt.continuousWithinAt

theorem G1_continuousOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ContinuousOn (Work.FTS.EllExist.Honesty.G1 α m c) (Set.Ioo 0 1) := by
  have hA : ContinuousOn (G1A α m c) (Set.Ioi 0) := G1A_continuousOn hα m hc h0
  have hpow : ContinuousOn (fun z : ℝ => z ^ (G1s α m)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hprod : ContinuousOn (fun z : ℝ => z ^ (G1s α m) * G1A α m c z) (Set.Ioo 0 1) :=
    (hpow.mul hA).mono Ioo_subset_Ioi_self
  rw [G1_as_product]
  exact hprod

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_far_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set

namespace Work.FTS.EllExist.Honesty

-- Far-field pointwise bound for the `z^{s⁻}` Green term `G1 α m c`
-- (`s⁻ = -(2m+5)/α`) of `Work.FTS.EllExist.Honesty.G1`, defined as
-- `G1 α m c z = z ^ (-(2*(m:ℝ)+5)/α) * ∫ t in (0:ℝ)..z, c t * t ^ ((2*(m:ℝ)+5)/α - 1)`.
-- Route: `a := (2*(m:ℝ)+5)/α`, `b := 2*(m:ℝ)/α`, `f t := c t * t ^ (a - 1)`, note
-- `a - b = 5/α ≥ 20` (from `hα4` and `hα`), and case-split on
-- `Good := MeasureTheory.IntegrableOn f (Set.Icc 0 1)`.
-- * If `Good`: for `z ≥ 1` the integrand `f` is continuous on `Icc 1 z ⊆ Set.Ioi 0`, so
--   `intervalIntegral.integral_add_adjacent_intervals` splits `∫_0^z = ∫_0^1 + ∫_1^z`; the
--   second piece is `≤ M * ∫_1^z t ^ (a - b - 3) ≤ M * z ^ (a - b - 2) / (a - b - 2)` using
--   `hdec`, monotonicity of the integral and `integral_rpow` (the exponent `a - b - 3` is
--   `> -1`), while `∫_0^1 f` is a fixed real.  Multiply by `z ^ (-a)` (`Real.rpow_add`).
-- * If `¬ Good` then `f` is not interval integrable on `0..z` for any `z ≥ 1` (otherwise
--   `MeasureTheory.IntegrableOn.mono_set` would give `Good`), so
--   `intervalIntegral.integral_undef` makes `G1 α m c z = 0` there; take `A = B = 0`.

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1_far_measurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- `G1f α m c` is interval integrable on `1..z` for every `1 ≤ z`: it is continuous on the
open half line `(0,∞)`, and `[1,z] ⊆ (0,∞)`. -/
theorem G1f_intervalIntegrable_one {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) {z : ℝ} (hz : (1 : ℝ) ≤ z) :
    IntervalIntegrable (G1f α m c) volume 1 z :=
  ContinuousOn.intervalIntegrable_of_Icc hz
    ((G1f_continuousOn hc).mono fun _ ht => lt_of_lt_of_le zero_lt_one ht.1)

/-- On `Set.Ioi 1` the map `z ↦ ∫ t in 1..z, G1f α m c t` is a primitive of the continuous
function `G1f α m c`, hence differentiable there. -/
theorem G1f_hasDerivAt_primitive {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun u : ℝ => ∫ t in (1 : ℝ)..u, G1f α m c t) (G1f α m c z) z := by
  intro z hz
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hf : ContinuousOn (G1f α m c) (Set.Ioi 0) := G1f_continuousOn hc
  exact intervalIntegral.integral_hasDerivAt_right (G1f_intervalIntegrable_one m hc hz1)
    (hf.stronglyMeasurableAtFilter isOpen_Ioi z hz0)
    (hf.continuousAt (Ioi_mem_nhds hz0))

/-- If the integrand `G1f α m c` fails to be integrable on `(0,1]`, then `G1 α m c` vanishes on
`Set.Ioi 1`: for such `z` the integrand cannot be interval integrable on `0..z` either (otherwise
`IntegrableOn.mono_set` with `(0,1] ⊆ (0,z]` would give the forbidden integrability on `(0,1]`),
and the interval integral of a non-integrable function is `0`. -/
theorem G1_eq_zero_of_not_integrableOn {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (h : ¬ IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)) {z : ℝ} (hz : (1 : ℝ) < z) :
    G1 α m c z = 0 := by
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hnot : ¬ IntervalIntegrable (G1f α m c) volume 0 z := by
    intro hint
    have hInt : IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) z) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0 : ℝ) ≤ z)).1 hint
    exact h (hInt.mono_set fun t ht => ⟨ht.1, le_trans ht.2 hz1⟩)
  rw [G1_eq_zpow_mul_G1A]
  have hzero : G1A α m c z = 0 := intervalIntegral.integral_undef hnot
  rw [hzero, mul_zero]

-- Measurability on the far field of the `z^{s⁻}` Green term `G1 α m c`
-- (`s⁻ = -(2m+5)/α`):
-- `G1 α m c z = z ^ (-(2*(m:ℝ)+5)/α) * ∫ t in (0:ℝ)..z, c t * t ^ ((2*(m:ℝ)+5)/α - 1)`.
-- Route: `a := (2*(m:ℝ)+5)/α`, `f t := c t * t ^ (a - 1)`, case-split on
-- `Good := MeasureTheory.IntegrableOn f (Set.Icc 0 1)`.
-- * If `Good`, then for every `z ≥ 1` the integral splits as `∫_0^z f = ∫_0^1 f + ∫_1^z f`
--   (`intervalIntegral.integral_add_adjacent_intervals`), and `z ↦ ∫_1^z f` is a primitive of
--   the continuous (on `Set.Ioi 0`) function `f`; so `G1 α m c` agrees on `Set.Ioi 1` with a
--   continuous function and is `MeasureTheory.AEStronglyMeasurable`
--   (`MeasureTheory.AEStronglyMeasurable.congr` + `ContinuousOn.aestronglyMeasurable`).
-- * If `¬ Good`, `MeasureTheory.IntegrableOn.mono_set` shows `f` is not interval integrable on
--   `0..z` for any `z ≥ 1`, so `intervalIntegral.integral_undef` gives `G1 α m c z = 0` for
--   all `z ∈ Set.Ioi 1`, and `MeasureTheory.AEStronglyMeasurable.congr` with the (a.e. equal)
--   zero function finishes.  (Recall that `∫` of a non-integrable function is `0`.)
theorem G1_far_measurable (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0)) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllExist.Honesty.G1 α m c z)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
  by_cases hGood : IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)
  · -- Case 1: `G1f` is integrable on `(0,1]`.
    -- On `Set.Ioi 1`, `G1 α m c` agrees with the continuous function
    -- `z ↦ z^{s⁻}·(∫_0^1 G1f + ∫_1^z G1f)`.
    have hpow : ContinuousOn (fun z : ℝ => z ^ (G1s α m)) (Set.Ioi (1 : ℝ)) :=
      continuousOn_id.rpow_const fun x hx => Or.inl (by
        simp only [id_eq, mem_Ioi] at hx ⊢
        exact ne_of_gt (by linarith))
    have hprim : ContinuousOn (fun z : ℝ => ∫ t in (1 : ℝ)..z, G1f α m c t)
        (Set.Ioi (1 : ℝ)) :=
      fun z hz => (G1f_hasDerivAt_primitive m hc z hz).continuousAt.continuousWithinAt
    have hcont : ContinuousOn
        (fun z : ℝ => z ^ (G1s α m) *
          ((∫ t in (0 : ℝ)..1, G1f α m c t) + ∫ t in (1 : ℝ)..z, G1f α m c t))
        (Set.Ioi (1 : ℝ)) :=
      hpow.mul (ContinuousOn.add continuousOn_const hprim)
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have h01 : IntervalIntegrable (G1f α m c) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hGood
    have h1z : IntervalIntegrable (G1f α m c) volume 1 z :=
      G1f_intervalIntegrable_one m hc hz1
    have hsplit : G1A α m c z =
        (∫ t in (0 : ℝ)..1, G1f α m c t) + ∫ t in (1 : ℝ)..z, G1f α m c t := by
      show (∫ t in (0 : ℝ)..z, G1f α m c t) = _
      exact (intervalIntegral.integral_add_adjacent_intervals h01 h1z).symm
    rw [G1_eq_zpow_mul_G1A, hsplit]
  · -- Case 2: `G1f` is not integrable on `(0,1]`; then `G1 α m c` vanishes on `Set.Ioi 1`.
    have hconst : MeasureTheory.AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioi 1)) := MeasureTheory.aestronglyMeasurable_const
    refine hconst.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact (G1_eq_zero_of_not_integrableOn m hGood hz).symm

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.hasDerivAt_sq_div_cube =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-- If `g'(z) = (-a·g(z) + c(z))/z` with `z > 0`, then the expression `w ↦ g(w)²/w³`
has derivative `(2·c(z)·g(z) - (3 + 2a)·g(z)²)/z⁴` at `z`.

Indeed `(g²/w³)' = 2g·g'/w³ - 3g²/w⁴`, and substituting the ODE for `g'` at `w = z` gives
`(2g(z)(-a·g(z) + c(z)z) - 3g(z)²)/z⁴ = (2c(z)g(z) - (3+2a)g(z)²)/z⁴`. -/
theorem hasDerivAt_sq_div_cube {a : ℝ} {c g : ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (hg : HasDerivAt g ((-a * g z + c z) / z) z) :
    HasDerivAt (fun w : ℝ => g w ^ 2 / w ^ 3)
      ((2 * c z * g z - (3 + 2 * a) * g z ^ 2) / z ^ 4) z := by
  -- derivative of the numerator `w ↦ g w ^ 2`
  have hnum : HasDerivAt (fun w : ℝ => g w ^ 2)
      (2 * g z * ((-a * g z + c z) / z)) z := by
    simpa only [Pi.pow_def, Nat.cast_ofNat, Nat.reduceSub, pow_one] using hg.pow 2
  -- derivative of the denominator `w ↦ w ^ 3`
  have hden : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using (hasDerivAt_pow 3 z)
  have h := hnum.div hden (pow_ne_zero 3 (ne_of_gt hz))
  convert h using 1
  field_simp
  ring

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-
**`HkMem α k f` and `HkSq α k f ≤ C` from a pointwise `liminf` domination.**

The hypotheses say that, for every `z ∈ Iz`, the angular slice `θ ↦ HkIntegrand α k f z θ`
is dominated a.e. (in `θ`, w.r.t. `volume.restrict Iθ`) by the pointwise limit inferior of
the slices of a sequence `fs n` of `HkMem`-functions whose `z`-slices are bounded by a
`z`-dependent constant `B z` ("`hz`"), and whose global `HkSq`-norms are bounded by `C`
("`hb`").

The proof is Fatou's lemma, applied twice:

* **slice level.**  For each `z ∈ Iz` we apply
  `integrable_and_integral_le_liminf` to the sequence `n ↦ HkIntegrand α k (fs n) z ·`
  (integrable on `Iθ` by `hfs n`, nonnegative everywhere, with integrals bounded by `B z`)
  and the function `HkIntegrand α k f z ·` (a.e. strongly measurable by `hsl`, nonnegative
  everywhere, dominated a.e. by the `liminf` by `hae`).  This gives both the integrability
  of each angular slice of `f` — the first half of `HkMem α k f` — and the pointwise bound
  `∫_θ HkIntegrand α k f z θ ≤ liminf_n ∫_θ HkIntegrand α k (fs n) z θ`.

* **outer level.**  The same lemma applied to `u n := (z ↦ ∫_θ HkIntegrand α k (fs n) z θ)`
  (integrable by `hfs n`, nonnegative, with integrals `HkSq α k (fs n) ≤ C`) and
  `h := (z ↦ ∫_θ HkIntegrand α k f z θ)` (a.e. strongly measurable by `houter`,
  nonnegative, and dominated a.e. in `z` by the slice-level bound just proved) gives the
  integrability of the outer function — the second half of `HkMem α k f` — together with
  `HkSq α k f ≤ liminf_n HkSq α k (fs n) ≤ C`, the last step because every term of the
  sequence is `≤ C`.

The two applications are the content of `Work.FTS.EllExist.Honesty.integrable_and_integral_le_liminf`
(slice-level Fatou with an a.e. domination by a pointwise `liminf`, whose conclusion bundles
the integrability of the dominated function with the bound on its integral).
-/

theorem hkMem_of_liminf_slice {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {fs : ℕ → ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hfs : ∀ n, Work.Spaces.HkMem α k (fs n))
    (hb : ∀ n, Work.Spaces.HkSq α k (fs n) ≤ C)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (fs n) z θ) Filter.atTop)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ B : ℝ, ∀ n,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ) ≤ B) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkSq α k f ≤ C := by
  -- the per-slice bounds `B z` may be taken nonnegative, since they bound an integral of a
  -- pointwise nonnegative integrand
  have hB0 : ∀ z ∈ Work.Spaces.Iz, ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ) ≤ B := by
    intro z hz1
    obtain ⟨B, hB⟩ := hz z hz1
    exact ⟨B, le_trans (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (fs 0) z θ))
      (hB 0), hB⟩
  -- slice level: each angular slice of `HkIntegrand α k f` is integrable on `Iθ`, and it is
  -- bounded in integral by the `liminf` of the slices of the `fs n`
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz1
    obtain ⟨B, hB0', hB⟩ := hB0 z hz1
    exact (integrable_and_integral_le_liminf
      (u := fun n θ => Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun θ => Work.Spaces.HkIntegrand α k f z θ) (D := B)
      (fun n => (hfs n).1 z hz1)
      (fun n => Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ)
      hB hB0' (hsl z hz1)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hae z hz1)).1
  -- hence the same domination holds a.e. in `z` for the `θ`-integrals
  have hslice_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) z
        ≤ (fun a => Filter.liminf (fun n => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fs n) a θ) Filter.atTop) z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz1
    obtain ⟨B, hB0', hB⟩ := hB0 z hz1
    exact (integrable_and_integral_le_liminf
      (u := fun n θ => Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun θ => Work.Spaces.HkIntegrand α k f z θ) (D := B)
      (fun n => (hfs n).1 z hz1)
      (fun n => Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ)
      hB hB0' (hsl z hz1)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hae z hz1)).2
  -- outer level: the `θ`-integral of `HkIntegrand α k f` is integrable in `z`, and its
  -- integral is bounded by the `liminf` of the `HkSq`-norms of the `fs n`
  have hmain : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz)
      ∧ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ Filter.liminf (fun n => Work.Spaces.HkSq α k (fs n)) Filter.atTop := by
    refine integrable_and_integral_le_liminf
      (u := fun n z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) (D := C)
      (fun n => (hfs n).2)
      (fun n => Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ))
      (fun n => hb n) hC houter
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      hslice_le
  -- the liminf of a sequence bounded above by `C` is at most `C`
  have hlim : Filter.liminf (fun n => Work.Spaces.HkSq α k (fs n)) Filter.atTop ≤ C := by
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => Work.Spaces.HkSq_nonneg α k (fs n)
    · intro b hb''
      obtain ⟨n, hn⟩ := hb''.exists
      exact le_trans hn (hb n)
  exact ⟨⟨hslice, hmain.1⟩, le_trans hmain.2 hlim⟩

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllSol.HeavyFlat.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

noncomputable section

open MeasureTheory Set
open scoped Real Topology ENNReal

set_option autoImplicit false

/-- The logarithmic radial weight `Ω(t) = (1+e^t)^4 e^{-3t}`; under `z = e^t` it is exactly
`w(z)^2 · z`, i.e. `w(e^t)^2 dz`. -/
def omw (t : ℝ) : ℝ := (1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))

/-- The heavy angular weight `σ_η(θ) = sin(2θ)^{-η}`. -/
def sigE (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `omw t = w (exp t)^2 * exp t`. -/
theorem omw_eq_w_sq_mul (t : ℝ) :
    omw t = (Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t := by
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h3 : Real.exp (-(3 * t)) = (Real.exp t)⁻¹ ^ 3 := by
    rw [Real.exp_neg, show (3 : ℝ) * t = (((3 : ℕ) : ℝ)) * t by push_cast; ring, Real.exp_nat_mul,
      inv_pow]
  rw [omw, Work.Spaces.w, h3]
  field_simp [hpos.ne']


/-- **The flat shifted heavy-weight mixed-slot finiteness.** -/
def FlatHeavy : Prop :=
  ∀ (b : ℝ) (u : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, u t 0 = 0) → (∀ t : ℝ, u t (Real.pi / 2) = 0) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
      * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2
      - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * sigE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
      * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
        * sigE p.2) < ⊤

/-- **The `Ω`-weighted heavy-weight mixed-slot finiteness** (on the strip `ℝ × Iθ`). -/
def OmHeavy : Prop :=
  ∀ (g : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, g t 0 = 0) → (∀ t : ℝ, g t (Real.pi / 2) = 0) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz g p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) < ⊤

end

end Work.FTS.EllSol.HeavyFlat
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.traceAux.hardySinWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAux.traceAux

/-! ## Comparison tools -/

/-- Jordan's inequality in the form used below: `(4/π) t ≤ sin (2t)` for `t ∈ (0, π/4)`. -/
lemma sin_two_ge {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 4)) :
    (4 / Real.pi) * t ≤ Real.sin (2 * t) := by
  have h1 : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) :=
    Real.mul_le_sin (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have h3 : 2 / Real.pi * (2 * t) = (4 / Real.pi) * t := by ring
  rwa [h3] at h1

/-- `sin (2 (π/2 - t)) = sin (2t)`. -/
lemma sin_two_reflect (t : ℝ) : Real.sin (2 * (Real.pi / 2 - t)) = Real.sin (2 * t) := by
  rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t from by ring, Real.sin_pi_sub]

/-- Reflection of `IntegrableOn` about `π/2`: the map `t ↦ π/2 - t` carries `(0,ε)` onto
`(π/2 - ε, π/2)`. -/
lemma reflectIntegrableOn_iff (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn F (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) ↔
      IntegrableOn (fun t => F (Real.pi / 2 - t)) (Set.Ioo 0 ε) := by
  have h1 := intervalIntegrable_iff_integrableOn_Ioo_of_le (f := F) (μ := volume)
      (a := Real.pi / 2 - ε) (b := Real.pi / 2) (by linarith)
  have h2 := intervalIntegrable_iff_integrableOn_Ioo_of_le
      (f := fun t => F (Real.pi / 2 - t)) (μ := volume) (a := 0) (b := ε) (le_of_lt hε)
  have h3 : IntervalIntegrable (fun x => F (Real.pi / 2 - x)) volume ε 0 ↔
      IntervalIntegrable F volume (Real.pi / 2 - ε) (Real.pi / 2) := by
    have h := IntervalIntegrable.comp_sub_left_iff (f := F)
      (a := Real.pi / 2 - ε) (b := Real.pi / 2) (Real.pi / 2)
    rw [show Real.pi / 2 - (Real.pi / 2 - ε) = ε from by ring,
        show Real.pi / 2 - Real.pi / 2 = 0 from by ring] at h
    exact h
  rw [← h1, ← h2, ← h3]
  exact IntervalIntegrable.symm_iff


/-! ## The two `sin`-weighted Hardy inequalities -/



end Work.FTS.EllSol.VthAux.traceAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeStepOneAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux

set_option autoImplicit false



end Work.FTS.EllipticEst.AeStepOneAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs =====
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

/-- The angular weight `sin(2θ)^{-q}` of the weak first-order slice estimate. -/
def wq (q θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-q)

/-- The derivative of `wq q`:  `-2q cos(2θ) sin(2θ)^{-(q+1)}`. -/
def wqD (q θ : ℝ) : ℝ := -2 * q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(q + 1))



/-- The boundary flux `B θ = u'θ·u θ·σ θ - ½(u θ)²·σ'θ - ½(u θ)²·tan θ·σ θ` of the identity. -/
def Bfun (q : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv u θ * u θ * wq q θ - (1 / 2) * (u θ) ^ 2 * wqD q θ
    - (1 / 2) * (u θ) ^ 2 * Real.tan θ * wq q θ






end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.SliceSecondReflect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## Elementary symmetry facts about the reflection `θ ↦ π/2 - θ` -/





/-! ## The derivatives of a reflected function

Both identities hold *unconditionally*: `deriv` is junk-valued where the derivative does not
exist, and `deriv_comp_const_sub` is exactly the chain rule for the affine reflection. -/



/-! ## The reflection lemma -/


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.chiDefs =====
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





















end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.deriv_angPhiH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

/-- **Pointwise calculus for the weighted Hardy identity.**

If `G = angG h` has derivative `h θ · sin 2θ` at `θ ∈ (0, π/2)`, then the quotient
`V = angV h = G / sin 2θ` has derivative `h θ - 2 cot(2θ) V θ` there (quotient rule,
`(sin 2θ)' = 2 cos 2θ`), and consequently `angPhiH h = 6 V² cot 2θ` has derivative
`angF h θ = (h θ)² - 12 (V θ)² - (h θ - 6 cot(2θ) V θ)²` (product rule together with
`(cot 2θ)' = -2(1 + cot²2θ)`, then `ring`).

This is the identity `h² - 12 V² - (h - 6 cot 2θ V)² = (6 V² cot 2θ)'` of Elgindi's
weighted Hardy inequality, stated pointwise on the open interval.  Note that only `hg`
(and `Work.FTS.EllipticEst.AngGap.hasDerivAt_cot_two` from `Defs.lean`) is needed: no
continuity of `h` is required for the pointwise derivative. -/
theorem deriv_angPhiH (h : ℝ → ℝ)
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.FTS.EllipticEst.AngGap.angV h)
          (h θ - 2 * Real.cot (2 * θ) * Work.FTS.EllipticEst.AngGap.angV h θ) θ
      ∧ HasDerivAt (Work.FTS.EllipticEst.AngGap.angPhiH h)
          (Work.FTS.EllipticEst.AngGap.angF h θ) θ := by
  intro θ hθ
  have hsinpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsinpos
  -- `(sin 2θ)' = 2 cos 2θ`
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
  -- quotient rule: `V = G / sin 2θ`
  have hV0 := (hg θ hθ).div hsin hsinne
  have hV : HasDerivAt (angV h) (h θ - 2 * Real.cot (2 * θ) * angV h θ) θ := by
    refine hV0.congr_deriv ?_
    rw [Real.cot_eq_cos_div_sin, angV]
    field_simp
  refine ⟨hV, ?_⟩
  -- product rule for `Φ_H = 6 V² cot 2θ`
  have h2 := (hV.pow 2).const_mul 6
  have h3 := h2.mul (hasDerivAt_cot_two θ hθ)
  refine h3.congr_deriv ?_
  rw [angF, angFt]
  simp only [Pi.pow_apply]
  ring

end Work.FTS.EllipticEst.AngGap.PhiHCalc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.integrable_pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Interval-integrability of the three pieces of the Hardy integrand.**

With `h` of class `C²` on `[0, π/2]`, `|h θ| ≤ C sin 2θ`, `|angG h θ| ≤ C (sin 2θ)³`, and
`angG h` differentiable with derivative `h θ sin 2θ` on `(0, π/2)` (so that
`angV h = angG h / sin 2θ` is continuous there), the functions

* `θ ↦ (h θ)²`,
* `θ ↦ (angV h θ)²`,
* `angFt h = θ ↦ (h θ - 6 cot(2θ) angV h θ)²`

are all interval-integrable on `0..π/2`.  Each of them is continuous on `(0, π/2)` and
bounded there (`|h θ| ≤ C sin 2θ ≤ C`, `|V θ| ≤ C sin²2θ ≤ C`, and
`|6 cot(2θ) V θ| ≤ 6 C sin 2θ ≤ 6C`, so `|h - 6 cot 2θ V| ≤ 7C`), and `(0, π/2)` has finite
measure; alternatively `h²` is even continuous on the closed interval.  This is what
allows the integral of `angF h = (h² - 12 V²) - angFt h` to be split. -/
theorem integrable_pieces (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    IntervalIntegrable (fun θ => (h θ) ^ 2) MeasureTheory.volume 0 (Real.pi / 2)
      ∧ IntervalIntegrable (fun θ => (Work.FTS.EllipticEst.AngGap.angV h θ) ^ 2)
          MeasureTheory.volume 0 (Real.pi / 2)
      ∧ IntervalIntegrable (Work.FTS.EllipticEst.AngGap.angFt h)
          MeasureTheory.volume 0 (Real.pi / 2) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  -- Elementary consequences of the two bounds on `h` and `angG h`.
  have hbddC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h θ| ≤ C := by
    intro θ hθ
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsnn : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc hmem
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    calc |h θ| ≤ C * Real.sin (2 * θ) := hbdd θ (hsub hθ)
      _ ≤ C * 1 := by nlinarith
      _ = C := by ring
  have hVbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |angV h θ| ≤ C := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hV1 : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
      have hG := hCg θ (hsub hθ)
      rw [angV, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := hG
        _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsnn : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc hmem
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith
    nlinarith [hV1, hC]
  have hFtbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |angFt h θ| ≤ (7 * C) ^ 2 := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hmem : 2 * θ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hA : |h θ| ≤ C := hbddC θ hθ
    have hV1 : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
      have hG := hCg θ (hsub hθ)
      rw [angV, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := hG
        _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
    have hcot := abs_cot_two_le hθ
    have hcotV : |Real.cot (2 * θ) * angV h θ| ≤ C * Real.sin (2 * θ) := by
      rw [abs_mul]
      calc |Real.cot (2 * θ)| * |angV h θ|
            ≤ (1 / Real.sin (2 * θ)) * (C * (Real.sin (2 * θ)) ^ 2) :=
            mul_le_mul hcot hV1 (abs_nonneg _) (by positivity)
        _ = C * Real.sin (2 * θ) := by field_simp
    have hB : |6 * Real.cot (2 * θ) * angV h θ| ≤ 6 * C := by
      have h6 : |(6 : ℝ)| = 6 := by norm_num
      rw [show (6 : ℝ) * Real.cot (2 * θ) * angV h θ
            = 6 * (Real.cot (2 * θ) * angV h θ) by ring, abs_mul, h6]
      calc 6 * |Real.cot (2 * θ) * angV h θ| ≤ 6 * (C * Real.sin (2 * θ)) := by
            linarith [hcotV]
        _ = 6 * C * Real.sin (2 * θ) := by ring
        _ ≤ 6 * C * 1 := mul_le_mul_of_nonneg_left hs1 (by linarith)
        _ = 6 * C := by ring
    have hX : |h θ - 6 * Real.cot (2 * θ) * angV h θ| ≤ 7 * C := by
      have hsub' := abs_sub_le (h θ) 0 (6 * Real.cot (2 * θ) * angV h θ)
      simp only [sub_zero, zero_sub, abs_neg] at hsub'
      calc |h θ - 6 * Real.cot (2 * θ) * angV h θ|
            ≤ |h θ| + |6 * Real.cot (2 * θ) * angV h θ| := hsub'
        _ ≤ C + 6 * C := add_le_add hA hB
        _ = 7 * C := by ring
    rw [angFt, abs_of_nonneg (sq_nonneg _)]
    calc (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2
          = |h θ - 6 * Real.cot (2 * θ) * angV h θ| ^ 2 := by rw [sq_abs]
      _ ≤ (7 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hX 2
  -- Continuity on the open interval.
  have hcontG : ContinuousOn (angG h) (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontV : ContinuousOn (angV h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContinuousOn (fun θ => angG h θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2))
    exact hcontG.div hcontsin (fun θ hθ => ne_of_gt (sin_two_pos hθ))
  have hcontcot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    fun θ hθ => (hasDerivAt_cot_two θ hθ).continuousAt.continuousWithinAt
  have hcontFt : ContinuousOn (angFt h) (Set.Ioo 0 (Real.pi / 2)) := by
    have hprod : ContinuousOn (fun θ : ℝ => 6 * Real.cot (2 * θ) * angV h θ)
        (Set.Ioo 0 (Real.pi / 2)) := (continuousOn_const.mul hcontcot).mul hcontV
    show ContinuousOn (fun θ => (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))
    exact ((hh.continuousOn.mono hsub).sub hprod).pow 2
  refine ⟨?_, ?_, ?_⟩
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := fun θ => (h θ) ^ 2) hpi.le ((hh.continuousOn.mono hsub).pow 2) (C ^ 2)
      (fun θ hθ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (h θ)) (hbddC θ hθ) 2)
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := fun θ => angV h θ ^ 2) hpi.le (hcontV.pow 2) (C ^ 2)
      (fun θ hθ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (angV h θ)) (hVbdd θ hθ) 2)
  · exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound
      (g := angFt h) hpi.le hcontFt ((7 * C) ^ 2) hFtbdd

end Work.FTS.EllipticEst.AngGap.PhiHCalc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

/-- **The pointwise size bound behind the right endpoint limit.**

On `(0, π/2)`, where `sin 2θ > 0`, the bound `|angG h θ| ≤ C (sin 2θ)³` gives
`|V θ| = |angG h θ| / sin 2θ ≤ C (sin 2θ)²`, and with `|cot 2θ| ≤ 1/sin 2θ` this yields

  `|angPhiH h θ| = 6 (V θ)² |cot 2θ| ≤ 6 C² (sin 2θ)³`.

No positivity of `C` is needed (it is used only to make the bound decay). -/
theorem abs_angPhiH_le_left (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h1 := hCg θ (Set.Ioo_subset_Icc_self hθ)
  -- `|V θ| ≤ C (sin 2θ)²`
  have hV : |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
    rw [angV, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := h1
      _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring
  have hcot := abs_cot_two_le hθ
  have h2 : (angV h θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (angV h θ)) hV 2
  have h3 : 0 ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by positivity
  have hstep : 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)|
      ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hcot (abs_nonneg _) h3
  have heq : 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ))
      = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsp
    field_simp
  calc |angPhiH h θ| = 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)| := by
        simp only [angPhiH, abs_mul, abs_sq, abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
    _ ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) := hstep
    _ = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := heq

/-- **Right endpoint limit of the antiderivative `angPhiH h = 6 V² cot 2θ`.**

If `|angG h θ| ≤ C (sin 2θ)³` on `[0, π/2]`, then `angPhiH h → 0` as `θ → (π/2)⁻` inside
`(0, π/2)`: the squeeze `|6 V² cot 2θ| ≤ 6 C² (sin 2θ)³` (using `|V| ≤ C sin²2θ` and
`|cot 2θ| ≤ 1/sin 2θ` on the interval) has a continuous left-hand side vanishing at `π/2`.
This is one of the two boundary terms that must vanish in the fundamental identity of
calculus for the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²`. -/
theorem tendsto_angPhiH_left (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiH h)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  -- `(0, π/2)` is a left-neighbourhood of `π/2`, so the pointwise bound is available
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    filter_upwards [hsub] with θ hθ
    exact abs_angPhiH_le_left h C hCg θ hθ
  -- the majorant is continuous and vanishes at `π/2`
  have hgcont : Continuous (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3) := by fun_prop
  have hh : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhds (Real.pi / 2)) (nhds 0) := by
    have hthis := hgcont.tendsto (Real.pi / 2)
    have hval : 6 * C ^ 2 * (Real.sin (2 * (Real.pi / 2))) ^ 3 = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      ring
    rwa [hval] at hthis
  have hlim : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    hh.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)))
  -- squeeze, then replace `|angPhiH h|` by `angPhiH h`
  have habs : Filter.Tendsto (fun θ => |angPhiH h θ|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hev hlim
  exact (tendsto_zero_iff_abs_tendsto_zero (angPhiH h)).mpr
    (by simpa [Function.comp_def] using habs)

end Work.FTS.EllipticEst.AngGap.PhiHCalc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

/-- The size bound on `V = angV h` used for the endpoint limits: `|V| ≤ C sin²2θ`
on `(0, π/2)`, obtained by dividing `|G| ≤ C sin³2θ` by the positive `sin 2θ`. -/
theorem abs_angV_le' (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h1 := hCg θ (Set.Ioo_subset_Icc_self hθ)
  rw [angV, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
  calc |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3 := h1
    _ = C * (Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) := by ring

/-- The pointwise squeeze for `angPhiH h`: on `(0, π/2)`,
`|angPhiH h θ| = 6 V² |cot 2θ| ≤ 6 C² sin³2θ`. -/
theorem abs_angPhiH_le (h : ℝ → ℝ) (C : ℝ)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hV := abs_angV_le' h C hCg θ hθ
  have hcot := abs_cot_two_le hθ
  have hVnn : 0 ≤ |angV h θ| := abs_nonneg _
  have h2 : (angV h θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ hVnn hV 2
  have h3 : 0 ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 := by positivity
  have hstep1 : 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)|
      ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hcot (abs_nonneg _) h3
  have heq : 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ))
      = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsp
    field_simp
  calc |angPhiH h θ| = 6 * (angV h θ) ^ 2 * |Real.cot (2 * θ)| := by
        simp only [angPhiH, abs_mul, abs_sq,
          abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
    _ ≤ 6 * (C * (Real.sin (2 * θ)) ^ 2) ^ 2 * (1 / Real.sin (2 * θ)) := hstep1
    _ = 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := heq

/-- **Left endpoint limit of the antiderivative `angPhiH h = 6 V² cot 2θ`.**

If `|angG h θ| ≤ C (sin 2θ)³` on `[0, π/2]`, then `angPhiH h → 0` as `θ → 0⁺` inside
`(0, π/2)`: the squeeze `|6 V² cot 2θ| ≤ 6 C² (sin 2θ)³` (using `|V| ≤ C sin²2θ` and
`|cot 2θ| ≤ 1/sin 2θ` on the interval) has a continuous right-hand side vanishing at `0`.
This is one of the two boundary terms that must vanish in the fundamental identity of
calculus for the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²`. -/
theorem tendsto_angPhiH_right (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hCg : ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiH h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the bound `|angPhiH h θ| ≤ 6 C² sin³2θ` holds eventually at `0⁺`
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos])))
  have hev : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Work.FTS.EllipticEst.AngGap.angPhiH h θ| ≤ 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    filter_upwards [hsub] with θ hθ
    exact abs_angPhiH_le h C hCg θ hθ
  -- the majorant is continuous and vanishes at `0`
  have hgcont : Continuous (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3) := by fun_prop
  have hh : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhds (0 : ℝ)) (nhds 0) := by
    simpa using hgcont.tendsto 0
  have hlim : Filter.Tendsto (fun θ : ℝ => 6 * C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    hh.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have habs : Filter.Tendsto (fun θ => |Work.FTS.EllipticEst.AngGap.angPhiH h θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hev hlim
  exact (tendsto_zero_iff_abs_tendsto_zero (Work.FTS.EllipticEst.AngGap.angPhiH h)).mpr
    (by simpa [Function.comp_def] using habs)

end Work.FTS.EllipticEst.AngGap.PhiHCalc
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.angPhiC_integrand_intervalIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

theorem angPhiC_integrand_intervalIntegrable (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    IntervalIntegrable (fun θ => (h θ) ^ 2 + Work.FTS.EllipticEst.AngGap.angV h θ
        * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) ∧
    IntervalIntegrable (fun θ => (h θ) ^ 2) volume 0 (π / 2) ∧
    IntervalIntegrable (fun θ => Work.FTS.EllipticEst.AngGap.angV h θ
        * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  -- ## The square integrand
  have hsq : IntervalIntegrable (fun θ : ℝ => (h θ) ^ 2) volume 0 (π / 2) := by
    refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle ?_ (C ^ 2) ?_
    · exact ((hh.mono Set.Ioo_subset_Icc_self).continuousOn).pow 2
    · intro θ hθ
      have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
        pow_le_one₀ hspos.le (Real.sin_le_one (2 * θ))
      have hb := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
      have h1 : |h θ| ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : (C * Real.sin (2 * θ)) ^ 2 = C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
      calc |(h θ) ^ 2| = |h θ| ^ 2 := by rw [abs_pow]
        _ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by rw [← h2]; exact h1
        _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hsin1 (sq_nonneg C)
        _ = C ^ 2 := by ring
  -- ## Continuity and bound for `angV` and for `Q = angQ h` on the open interval (delegated)
  obtain ⟨hVcont, hVbdd⟩ := angV_cont_bound_Ioo h C hC hg hCg
  obtain ⟨hQcont, hQbdd⟩ := angQ_cont_bound_Ioo h hh C hC hbdd hbdd'
  have hVQcont : ContinuousOn
      (fun θ : ℝ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) (Set.Ioo 0 (π / 2)) :=
    hVcont.mul hQcont
  have hVQbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)| ≤ 3 * C ^ 2 := by
    intro θ hθ
    rw [abs_mul]
    have hv := hVbdd θ hθ
    have hq : |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ≤ 3 * C := hQbdd θ hθ
    have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ (sin_two_pos hθ).le (Real.sin_le_one (2 * θ))
    have h1 : |angV h θ| * |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ (C * (Real.sin (2 * θ)) ^ 2) * (3 * C) :=
      mul_le_mul hv hq (abs_nonneg _) (by positivity)
    have h2 : (C * (Real.sin (2 * θ)) ^ 2) * (3 * C) ≤ 3 * C ^ 2 := by
      nlinarith [sq_nonneg C, hC]
    linarith
  -- ## The product integrand, and the assembly
  have hVQ : IntervalIntegrable
      (fun θ : ℝ => angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ)) volume 0 (π / 2) :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hle hVQcont (3 * C ^ 2) hVQbdd
  exact ⟨hsq.add hVQ, hsq, hVQ⟩

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.Lzero_self_integrable_fts =====
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


end Work.FTS.EllipticEst.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.SliceThetaIbpDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

/-! ## The integrands -/

/-- `c·σ₁`, i.e. `cos(2θ)·sin(2θ)^{-(1+η)}`. -/
def sigc (θ : ℝ) : ℝ := Real.cos (2 * θ) * sig1 θ

/-- The LHS integrand `σ ψ v v''`. -/
def Lfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (v θ * deriv (deriv v) θ)

/-- The `∫ σψv²` integrand. -/
def Afun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (v θ) ^ 2

/-- The `∫ σψ(v')²` integrand. -/
def Bfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * ψ θ * (deriv v θ) ^ 2

/-- The `∫ σψ(v' - (1+η)v cos2θ/sin2θ)²` integrand (written with `sin(2θ)^{-1}`). -/
def Cfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sig θ * ψ θ * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
    * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2

/-- The `∫ σψ'' v²` integrand. -/
def Dfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := sig θ * deriv (deriv ψ) θ * (v θ) ^ 2

/-- The whole RHS integrand, `-2η σψv² - κ σψ(v')² - (2η/(1+η)) σψ(...)² + (1/2) σψ''v²`. -/
def RHSfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -2 * Work.Spaces.eta * Afun v ψ θ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * Bfun v ψ θ
    - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Cfun v ψ θ + (1 / 2) * Dfun v ψ θ

/-- The integrand of the total derivative: `L v ψ - RHS v ψ`. -/
def GderivFun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ := Lfun v ψ θ - RHSfun v ψ θ

/-- The boundary primitive of the θ-IBP. -/
def Gfun (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ψ θ * (sig θ * (v θ * deriv v θ) - Work.Spaces.eta * (sigc θ * (v θ) ^ 2))
    - (1 / 2) * (deriv ψ θ * (sig θ * (v θ) ^ 2))

/-- The derivative of `Gfun`, in the factored form that the product-rule chain produces
(see `hasDerivAt_Gfun`). -/
def Rawk (v ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Lfun v ψ θ
    + ψ θ * (sig θ * (deriv v θ) ^ 2
        - 4 * Work.Spaces.eta * (Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * sig2 θ
            * (v θ) ^ 2)
    + 2 * Work.Spaces.eta * sig θ * ψ θ * (v θ) ^ 2
    - (1 / 2) * sig θ * deriv (deriv ψ) θ * (v θ) ^ 2

/-! ## Elementary consequences of `slice_second_trunc` -/



/-- `(c σ₁)' = -2σ - 2(1+η)c²σ₂`. -/
lemma hasDerivAt_sigc {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sigc (-2 * sig θ - 2 * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
      * sig2 θ) θ := by
  have hc : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  refine ((hc.mul (sst_hasDerivAt_sig1 hθ)).congr_deriv ?_)
  rw [sst_sig_eq_sig1_mul_sin hθ]
  ring

/-! ## Vanishing near a point outside the topological support -/

lemma eventuallyEq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

lemma deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    deriv f x = 0 := by
  rw [(eventuallyEq_zero_of_notMem_tsupport hx).deriv_eq]
  simp [deriv_const]

lemma deriv_deriv_eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) :
    deriv (deriv f) x = 0 := by
  have h1 : deriv f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact deriv_eq_zero_of_notMem_tsupport hy
  rw [h1.deriv_eq]
  simp [deriv_const]

/-! ## Converting a `Set.Ioo 0 (π/2)`-integral of a compactly supported function -/

/-- If `f` vanishes on `(0, π/2) \ [a,b]`, then its integral over `(0, π/2)` is its interval
integral over `[a,b]`. -/
theorem setIntegral_Ioo_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hf : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → f θ = 0) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in a..b, f θ := by
  have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in Set.Icc a b, f θ :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
      (fun x hx => by
        have hx' : x ∉ Set.Icc a b := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hx'
        exact hf x hx.1.1 hx.1.2 hx')
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## The algebraic core -/

/-- **The algebraic core of the slice identity.**  For `θ ∈ (0, π/2)`,
`σ v'² - 4η (cσ₁) v v' + 2η(1+η) c² σ₂ v² = κ σ v'² + (2η/(1+η)) σ (v' - (1+η)v c/s)²`
with `σ = sin(2θ)^{-η}`, `σ₁ = sin(2θ)^{-(1+η)}`, `σ₂ = sin(2θ)^{-(2+η)}`,
`s = sin 2θ`, `c = cos 2θ` and `κ = (1-η)/(1+η)`. -/
theorem theta_alg {v : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig θ * (deriv v θ) ^ 2
        - 4 * Work.Spaces.eta * (Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * sig2 θ
            * (v θ) ^ 2
      = ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (sig θ * (deriv v θ) ^ 2)
        + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (sig θ * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2) := by
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sst_sin_two_pos hθ)
  have h1 : (1 + Work.Spaces.eta) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  rw [sst_sig_eq_sig1_mul_sin hθ, sst_sig1_eq_sig2_mul_sin hθ, Real.rpow_neg_one]
  field_simp
  ring

/-- `Rawk` is the derivative of `Gfun` and equals `Lfun - RHSfun`. -/
theorem Rawk_eq (v ψ : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Rawk v ψ θ = Lfun v ψ θ - RHSfun v ψ θ := by
  unfold Rawk RHSfun Afun Bfun Cfun Dfun
  rw [theta_alg hθ]
  ring

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_bad_case =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux
set_option autoImplicit false


end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.DzIter_eq_sum_scoef_diffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false

/-!
# The Stirling expansion of `D_z^n` from `DifferentiableOn`-hypotheses on an open set

The operators `D_z = z ∂_z` and `∂_z` satisfy the commutation relation
`∂_z ∘ D_z = D_z ∘ ∂_z + ∂_z`, so that

`D_z^n f = ∑_{k=0}^{n} S(n,k) z^k ∂_z^k f`

with `S(n,k) = Work.Spaces.scoef n k` the Stirling numbers of the second kind.  The
existing statements of this expansion (`Work.Spaces.DzIter_eq_sum_scoef`,
`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`, …) all require the `z`-slice to be
`C^∞` (or `C^∞` on a half-line).  This file proves the expansion in the minimal
form needed by the finite-order interior estimates: it suffices that the slices
`z ↦ pzIter k h z θ`, `k ≤ n`, are *differentiable on an open set* `U`, and the
identity then holds at every point of `U`.  The proof is the usual induction on
`n`: the induction hypothesis holds on a neighbourhood of the point (openness),
and the induction step differentiates the sum term by term with the product rule.
-/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step: the extra factor `z`
produced by `D_z` from the derivative of `z^k`. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- `deriv` of the `k`-th iterated `z`-derivative of the `z`-slice: this is the
definition of `pzIter`, so nothing has to be proved. -/
private theorem deriv_pzIter_slice (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` from `DifferentiableOn`-hypotheses on an open
set** (helper form, with `n` generalized so that the induction is clean). -/
private theorem DzIter_eq_sum_scoef_diffOn_aux {h : ℝ → ℝ → ℝ} {θ : ℝ} {U : Set ℝ}
    (hU : IsOpen U) :
    ∀ n : ℕ, (∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U) →
      ∀ z ∈ U, Work.Spaces.DzIter n h z θ
        = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
            * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro _ z _
    simp [Work.Spaces.DzIter, Work.Spaces.scoef]
  | succ n ih =>
    intro hd z hz
    -- the induction hypothesis applies with the hypotheses up to order `n`
    have hd' : ∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U :=
      fun k hk => hd k (Nat.le_succ_of_le hk)
    have hnhds : U ∈ 𝓝 z := hU.mem_nhds hz
    -- differentiability at the point `z`, which is interior to `U`
    have hdiff : ∀ k ≤ n + 1,
        DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z :=
      fun k hk => (hd k hk).differentiableAt hnhds
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ, k ≤ n →
        DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
      fun k hk => (hd1 k).mul (hdiff k (Nat.le_succ_of_le hk))
    -- the induction hypothesis, as an eventual equality near `z`
    have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
      filter_upwards [hnhds] with z' hz'
      exact ih hd' z' hz'
    -- the derivative of each summand
    have hterm : ∀ k : ℕ, k ≤ n →
        deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
            * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
        = (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
            + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      intro k hk
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
        (Work.Spaces.scoef n k : ℝ) (hd3 k hk)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k)
        (hdiff k (Nat.le_succ_of_le hk))
      have hmul' : deriv (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * Work.Spaces.pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow, deriv_pzIter_slice]
    -- differentiate the whole sum
    have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (Work.Spaces.scoef n k : ℝ)
                * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk =>
        (hd3 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul
          (Work.Spaces.scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk =>
        hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    calc Work.Spaces.DzIter (n + 1) h z θ
        = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
          simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
              + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
              + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : z * ((Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
              = (Work.Spaces.scoef n k : ℝ)
                * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term]
      _ = ∑ j ∈ Finset.range (n + 2),
            (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

theorem DzIter_eq_sum_scoef_diffOn {h : ℝ → ℝ → ℝ} {θ : ℝ} {U : Set ℝ} {n : ℕ}
    (hU : IsOpen U)
    (hd : ∀ k ≤ n, DifferentiableOn ℝ (fun y : ℝ => Work.Spaces.pzIter k h y θ) U) :
    ∀ z ∈ U, Work.Spaces.DzIter n h z θ
      = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k h z θ) :=
  DzIter_eq_sum_scoef_diffOn_aux hU n hd

end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dth1IterTwoCosBoundN =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

noncomputable section

/-! ## The recursion of `D_θ` on multiples of `sin(2θ)²` -/

/-- `(sin 2θ)²` has derivative `4 sin 2θ cos 2θ`. -/
private lemma deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have h3 := h2.pow 2
  have h4 : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 2 * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2) := h3.deriv
  rw [h4]; ring

/-- The recursion of `D_θ = sin(2θ) ∂_θ` on a function of the form `sin(2θ)² · g`: dividing by
`sin(2θ)²` transforms `g` by `g ↦ 4 cos(2θ) · g + sin(2θ) · g'`. -/
private lemma Dth1_sin_sq_mul (θ : ℝ) (g : ℝ → ℝ) (hg : DifferentiableAt ℝ g θ) :
    Work.Elliptic.Dth1 (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t) θ
      = Real.sin (2 * θ) ^ 2 *
          (4 * Real.cos (2 * θ) * g θ + Real.sin (2 * θ) * deriv g θ) := by
  have hsin : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t) ^ 2) θ := by fun_prop
  have hprod : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t) θ
      = deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ * g θ
        + Real.sin (2 * θ) ^ 2 * deriv g θ := by
    have hfun : (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t)
        = (fun t : ℝ => Real.sin (2 * t) ^ 2) * g := by
      funext t; rw [Pi.mul_apply]
    rw [hfun]
    exact deriv_mul hsin hg
  simp only [Work.Elliptic.Dth1]
  rw [hprod, deriv_sin_two_sq]
  ring

/-! ## The factorisation of the iterates -/

/-- `D_θ^{n+1}(2 cos 2θ) = sin(2θ)² · gSeq n`, as an identity of functions. -/
private lemma Dth1Iter_two_cos_factor_fun (n : ℕ) :
    Work.Elliptic.Dth1Iter (n + 1) (fun t : ℝ => 2 * Real.cos (2 * t))
      = fun θ => Real.sin (2 * θ) ^ 2 * gSeq n θ := by
  induction n with
  | zero =>
    funext θ
    simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1,
      gSeq_zero]
    rw [Work.Elliptic.deriv_two_cos_two]
    ring
  | succ n ih =>
    rw [Work.Elliptic.Dth1Iter_succ, ih]
    funext θ
    rw [Dth1_sin_sq_mul θ (gSeq n) ((gSeq_differentiable n).differentiableAt), gSeq_succ]

/-- `D_θ^{n+1}(2 cos 2θ) = sin(2θ)² · gSeq n`, pointwise. -/
private lemma Dth1Iter_two_cos_factor (n : ℕ) (θ : ℝ) :
    Work.Elliptic.Dth1Iter (n + 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
      = Real.sin (2 * θ) ^ 2 * gSeq n θ :=
  congrFun (Dth1Iter_two_cos_factor_fun n) θ

/-- For every `k ≥ 1` the `k`-th iterate `D_θ^k (2 cos 2θ)` of the angular operator
`D_θ = sin(2θ) ∂_θ` is bounded, uniformly over ALL real `θ`, by a constant times `sin(2θ)²`
(not merely on the interval `[0, π/2]`).

ROUTE. Prove globally (`∀ θ : ℝ`) the factorisation `D_θ^j (2 cos 2θ) θ = sin(2θ)^2 * g_j θ`,
where `g_1 := fun _ => -4` and `g_{j+1} := 4 cos(2θ) * g_j + sin(2θ) * deriv g_j`, from the
recursion `D_θ (sin(2θ)^2 g) = sin(2θ)^2 (4 cos(2θ) g + sin(2θ) g')`.  Each `g_j` is `C^∞` and
`π`-periodic (the derivative of a `π`-periodic function is `π`-periodic; `sin(2·)`, `cos(2·)`
are `π`-periodic), so it is bounded on `ℝ`: bound it on the compact `[0, π]`
(`isCompact_Icc.exists_bound_of_continuousOn`) and transport to any point with
`Function.Periodic.exists_mem_Ico₀`.  Compare `Work.Elliptic.DivSinPhiBound`
(`Submission/Work/Elliptic/DivSinPhiBound.lean`), which does the cases `k = 1,2,3` by explicit
formulas. -/
theorem Dth1IterTwoCosBoundN (k : ℕ) (hk : 1 ≤ k) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ,
      |Work.Elliptic.Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
        ≤ M * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨C, hCpos, hC⟩ := gSeq_bdd m
  refine ⟨C, hCpos, fun θ => ?_⟩
  rw [Dth1Iter_two_cos_factor m θ, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  calc Real.sin (2 * θ) ^ 2 * |gSeq m θ| ≤ Real.sin (2 * θ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hC θ) (sq_nonneg (Real.sin (2 * θ)))
    _ = C * Real.sin (2 * θ) ^ 2 := by ring

end

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.Lzero1_mul_sinCos2_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

theorem Lzero1_mul_sinCos2_eq {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hdu : DifferentiableAt ℝ u θ) :
    Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ
      = -(deriv (deriv u) θ) * Work.Elliptic.sinCos2 θ
        + Real.sin θ * u θ + (Real.sin θ) ^ 2 * Real.cos θ * deriv u θ
        - 6 * u θ * Work.Elliptic.sinCos2 θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    linarith
  have hdtan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.2 hcos
  -- product rule for `θ ↦ tan θ * u θ`
  have hdprod : deriv (fun t => Real.tan t * u t) θ
      = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ := by
    change deriv (Real.tan * u) θ = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ
    rw [deriv_mul hdtan hdu, Real.deriv_tan]
  rw [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.sinCos2, hdprod, Real.tan_eq_sin_div_cos]
  field_simp
  ring

end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

/-- Slicing a jointly `C^m` function in the second variable: if `uncurry Ψ` is `C^m` on the
open half-strip `(0,∞) × (0,π/2)` and `z > 0`, then every `θ`-slice `θ' ↦ Ψ z θ'` is `C^m`
on `(0,π/2)`.  (The corresponding Mathlib-free statement for the `z`-slice is
`Work.FTS.H2.contDiffOn_zslice_of_uncurry`.) -/
theorem contDiffOn_slice_of_uncurry {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (m : ℕ)
    (hsm : ContDiffOn ℝ m (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ m (fun θ' => Ψ z θ') (Set.Ioo 0 (Real.pi / 2)) := by
  have hphi : ContDiffOn ℝ m (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hcomp := hsm.comp hphi (fun θ' hθ' => ⟨hz, hθ'⟩)
  simpa [Function.comp_def, Function.uncurry] using hcomp

theorem slice_regularity_of_uncurry {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun θ' => Ψ z θ') (Set.Ioo 0 (Real.pi / 2))
      ∧ ContinuousOn (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2))
      ∧ ContinuousOn (deriv (deriv (fun θ' => Ψ z θ'))) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 := contDiffOn_slice_of_uncurry hz 2 (hsm 2)
  have h3 := contDiffOn_slice_of_uncurry hz 3 (hsm 3)
  refine ⟨h2, h2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num), ?_⟩
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

end Work.FTS.EllipticEst.Endpt
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gsing_deriv_rel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## The first-order relation satisfied by the singular term `Gsing`

`Gsing α F = Gstar α F + Gbar α F` is the singular term `G` of §'The singular term'
(tex 1027) of Elgindi's paper, with the two summands

* `Gstar α F = -(1/(4α)) L₁₂(F)`, and
* `Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds`

(the *pre*-integration-by-parts form of `\bar G`; see `Work.Elliptic.Defs`).

The paper's first integral of the ODE for `G` (tex 1026) is
`R^{(5+α)/α} ∂_R G = -(15/(4α²)) ∫_0^R s^{(5-α)/α} F_*(s) ds`.  Dividing by
`R^{(5+α)/α}` and using `-(15/(4α²)) = (5/(α R)) · (-(3/(4α))) · R^{5/α}` gives exactly

  `α z ∂_z(Gsing α F) z = -5 (Gbar α F) z`   (`z > 0`),

which is the relation proved below.  Written out, `deriv (Gsing α F) z` is the explicit
first-derivative value `DGstar α F z + DGbar α F z` of `Work.Elliptic.GsingFuncs`, and the
identity is purely algebraic: `α z DGstar = (3/4) F_*` while
`α z DGbar = -5 Gbar - (3/4) F_*`, the two `F_*`-terms cancelling.

The corresponding `HasDerivAt` facts live in `Work.Elliptic.Gsing_ode`, but they are
`private` there (and that module additionally proves the second-order ODE, which needs the
extra hypothesis `hFc`); they are re-derived here so that this module is self-contained. -/

/-- `Abar` has derivative `DAbar` at every `z > 0`. -/
private lemma hasDerivAt_Abar_ft (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul (-(3 / (4 * α)))
  convert h using 1
  · ext y; rfl
  · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
        = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
    ring

/-- `Gstar` has derivative `DGstar`. -/
private lemma hasDerivAt_Gstar_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hL12 : HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z := by
  have h := hL12.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F y)
      = Work.Elliptic.Gstar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGstar] using h

/-- `Gbar` has derivative `DGbar` at every `z > 0`. -/
private lemma hasDerivAt_Gbar_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z := by
  have hA : HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z :=
    hasDerivAt_Abar_ft α hz
  have h := hA.mul hJ
  have hfun : (Work.Elliptic.Abar α * Work.Elliptic.Jfun α F) = Work.Elliptic.Gbar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGbar] using h

/-- The algebraic content of `α z ∂_z Gsing = -5 Gbar`: `α = 0` and `z = 0` are the only
degeneracies, and they are excluded by the two hypotheses. -/
private lemma gsing_rel_algebra_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hα : 0 < α) (hz : 0 < z) :
    α * z * (Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z)
      = -5 * Work.Elliptic.Gbar α F z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- `A := z ^ (-(5/α))` and `z⁻¹` are the only two `z`-powers occurring; all the others
  -- are rewritten in terms of them, exactly as in `Work.Elliptic.Gsing_algebra`.
  have hApos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hz _
  have hAne : z ^ (-(5 / α)) ≠ 0 := ne_of_gt hApos
  have hp1 : z ^ (-(5 / α) - 1) = z ^ (-(5 / α)) * z⁻¹ := by
    rw [show -(5 / α) - 1 = -(5 / α) + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
  have hpt : z ^ ((5 - α) / α) = z⁻¹ / z ^ (-(5 / α)) := by
    rw [eq_div_iff hAne, ← Real.rpow_add hz,
      show (5 - α) / α + -(5 / α) = -1 by field_simp; ring, Real.rpow_neg_one]
  unfold Work.Elliptic.DGstar Work.Elliptic.DGbar Work.Elliptic.Abar Work.Elliptic.DAbar
    Work.Elliptic.Gbar Work.Elliptic.Jfun
  rw [hp1, hpt]
  field_simp
  ring

theorem Gsing_deriv_rel (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z') (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hJz : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        = Work.Elliptic.Jfun α F := rfl
    rw [hfun] at h
    exact h
  -- `Gsing` is differentiable at `z` with the explicit derivative `DGstar + DGbar`
  have hGsing : HasDerivAt (Work.Elliptic.Gsing α F)
      (Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z) z := by
    have h1 : HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z :=
      hasDerivAt_Gstar_ft α F (hL12 z hz)
    have h2 : HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z :=
      hasDerivAt_Gbar_ft α F hzpos hJz
    have h := h1.add h2
    have hfun : (Work.Elliptic.Gstar α F + Work.Elliptic.Gbar α F)
        = Work.Elliptic.Gsing α F := rfl
    rw [hfun] at h
    exact h
  rw [hGsing.deriv]
  exact gsing_rel_algebra_ft α F hα hzpos

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.Lzero1MulSelfIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open MeasureTheory Set Filter
open scoped Real Topology

/-- **`Lzero1 f · f` is integrable** on `(0, π/2)` as soon as `f` is `C²` there, bounded,
with bounded first derivative and bounded `f/cos θ`, and `f''` absolutely integrable.

Indeed `Lzero1 f θ = -f'' θ + (tan θ · f θ)' - 6 f θ`, and on `(0, π/2)` the product rule
gives `(tan θ · f θ)' = (1/cos²θ) f θ + tan θ f' θ`.  Hence `Lzero1 f · f` splits into the
three pieces

* `-f'' θ · f θ`, dominated by `B · |f'' θ|` (integrable by hypothesis),
* `(tan θ · f θ)' · f θ = (f θ / cos θ)² + (tan θ · f θ) · f' θ`, bounded by `K² + K·M`,
* `-6 f θ²`, bounded by `6 B²`,

each of which is integrable on the finite-measure interval `(0, π/2)`. -/
theorem Lzero1MulSelfIntegrable {f : ℝ → ℝ} {B M K : ℝ}
    (hsm : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B)
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hK : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ / Real.cos θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t : ℝ => deriv f t) θ|)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  set I : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2) with hI
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmem4 : (Real.pi / 4) ∈ I := ⟨by linarith, by linarith⟩
  have hIopen : IsOpen I := isOpen_Ioo
  have hImeas : MeasurableSet I := measurableSet_Ioo
  -- nonnegativity of the three constants
  have hBnn : 0 ≤ B := by
    have h := hB (Real.pi / 4) hmem4
    linarith [abs_nonneg (f (Real.pi / 4))]
  have hMnn : 0 ≤ M := by
    have h := hM (Real.pi / 4) hmem4
    linarith [abs_nonneg (deriv f (Real.pi / 4))]
  have hKnn : 0 ≤ K := by
    have h := hK (Real.pi / 4) hmem4
    linarith [abs_nonneg (f (Real.pi / 4) / Real.cos (Real.pi / 4))]
  -- the interval has finite measure
  have hvol : volume I < ⊤ := by
    have hsub : I ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    calc volume I ≤ volume (Set.Icc (0 : ℝ) (Real.pi / 2)) := measure_mono hsub
      _ < ⊤ := isCompact_Icc.measure_lt_top
  -- regularity of `f` and its derivatives
  have hcont : ContinuousOn f I := hsm.continuousOn
  have hcontd : ContinuousOn (deriv f) I := hsm.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hdiffOn : DifferentiableOn ℝ f I := hsm.differentiableOn (by norm_num)
  have hcd1 : ContDiffOn ℝ 1 (deriv f) I := hsm.deriv_of_isOpen hIopen (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv f)) I :=
    hcd1.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hcos_ne : ∀ θ ∈ I, Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], by linarith [hθ.2]⟩)
  -- ### the three pieces
  have hT1 : IntegrableOn (fun θ => -(deriv (fun t : ℝ => deriv f t) θ) * f θ) I := by
    refine Integrable.mono' (hint.const_mul B) ?_ ?_
    · exact ((hcont2.aestronglyMeasurable hImeas).neg).mul (hcont.aestronglyMeasurable hImeas)
    · filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc |deriv (fun t : ℝ => deriv f t) θ| * |f θ|
          ≤ |deriv (fun t : ℝ => deriv f t) θ| * B :=
            mul_le_mul_of_nonneg_left (hB θ hθ) (abs_nonneg _)
        _ = B * |deriv (fun t : ℝ => deriv f t) θ| := by ring
  have hT2eq : ∀ θ ∈ I, deriv (fun t : ℝ => Real.tan t * f t) θ
      = (1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr (hcos_ne θ hθ)
    have h2 : DifferentiableAt ℝ f θ := hdiffOn.differentiableAt (hIopen.mem_nhds hθ)
    have h := deriv_mul h1 h2
    rw [Real.deriv_tan] at h
    exact h
  have hT2 : IntegrableOn (fun θ => deriv (fun t : ℝ => Real.tan t * f t) θ * f θ) I := by
    have hgcont : ContinuousOn
        (fun θ => ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ) I := by
      have hc : ContinuousOn (fun θ : ℝ => (1 : ℝ) / Real.cos θ ^ 2) I :=
        continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
          (fun θ hθ => pow_ne_zero 2 (hcos_ne θ hθ))
      have ht : ContinuousOn (fun θ : ℝ => Real.tan θ) I :=
        Real.continuousOn_tan.mono (fun θ hθ => hcos_ne θ hθ)
      exact ((hc.mul hcont).add (ht.mul hcontd)).mul hcont
    have hbound : ∀ᵐ θ ∂volume.restrict I,
        ‖((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ‖ ≤ K ^ 2 + K * M := by
      filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs]
      have hcos := hcos_ne θ hθ
      have hsplit : ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ
          = (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ := by
        field_simp
      have hA : |(f θ / Real.cos θ) ^ 2| ≤ K ^ 2 := by
        have h1 : |f θ / Real.cos θ| ≤ K := hK θ hθ
        calc |(f θ / Real.cos θ) ^ 2| = (f θ / Real.cos θ) ^ 2 := abs_sq _
          _ = |f θ / Real.cos θ| ^ 2 := (sq_abs _).symm
          _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      have htan : |Real.tan θ * f θ| ≤ K := by
        have h2 : Real.tan θ * f θ = Real.sin θ * (f θ / Real.cos θ) := by
          rw [Real.tan_eq_sin_div_cos, div_mul_eq_mul_div]
          field_simp
        rw [h2, abs_mul]
        calc |Real.sin θ| * |f θ / Real.cos θ| ≤ 1 * K :=
              mul_le_mul (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩)
                (hK θ hθ) (abs_nonneg _) (by norm_num)
          _ = K := by ring
      have hB2 : |Real.tan θ * deriv f θ * f θ| ≤ K * M := by
        rw [show Real.tan θ * deriv f θ * f θ = (Real.tan θ * f θ) * deriv f θ by ring,
          abs_mul]
        exact mul_le_mul htan (hM θ hθ) (abs_nonneg _) hKnn
      rw [hsplit]
      calc |(f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ|
          ≤ |(f θ / Real.cos θ) ^ 2| + |Real.tan θ * deriv f θ * f θ| := abs_add_le _ _
        _ ≤ K ^ 2 + K * M := add_le_add hA hB2
    have hHg : IntegrableOn
        (fun θ => ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ) I :=
      IntegrableOn.of_bound hvol (hgcont.aestronglyMeasurable hImeas) (K ^ 2 + K * M) hbound
    exact hHg.congr_fun (fun θ hθ => by rw [hT2eq θ hθ]) hImeas
  have hT3 : IntegrableOn (fun θ => 6 * f θ ^ 2) I := by
    refine IntegrableOn.of_bound hvol ?_ (6 * B ^ 2) ?_
    · exact ((hcont.pow 2).const_mul 6).aestronglyMeasurable hImeas
    · filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hle : f θ ^ 2 ≤ B ^ 2 := by
        have h1 : |f θ| ≤ B := hB θ hθ
        calc f θ ^ 2 = |f θ| ^ 2 := by rw [sq_abs]
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      linarith
  -- ### assembly
  have hsum : IntegrableOn (fun θ => (-(deriv (fun t : ℝ => deriv f t) θ) * f θ)
      + deriv (fun t : ℝ => Real.tan t * f t) θ * f θ - 6 * f θ ^ 2) I :=
    (hT1.add hT2).sub hT3
  refine hsum.congr_fun ?_ hImeas
  intro θ hθ
  simp only [Work.FTS.EllipticEst.Lzero1]
  ring

end Work.FTS.EllipticEst.H2W.AeProof
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceA.Lzero1_order_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SliceA

open Filter Topology Set MeasureTheory

local notation "Lθ" => nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))







end Work.FTS.EllipticEst.H2W.SliceA
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.I1_z_ibp_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration by parts of `I₁` on the open half-strip

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.I1_z_ibp_honest`: the smoothness
hypothesis is `C³` on the **open** half-strip `qd = (0,∞) × (0,π/2)` (which is what the
almost-everywhere class `H2W.Ae.AeData` supplies, and which is *not* implied by the joint `C²`
of the original statement of `H2W.I1_z_ibp` — see `H2W/NOTES_I1_z_ibp_FALSE.md`).

With `W2 z = (w z)^2`, `Φ` of class `C³` on `qd`, `z`-support of `Φ` in a compact
`[a,b] ⊂ (0,∞)` (for every angle `θ`), and the four integrability hypotheses:

  `∫_z ∫_θ (z²∂_z²Φ)·∂_θ²Φ·W2·sin(2θ)^{-η}`
  `= - ∫_z ∫_θ z²∂_zΦ·∂_z∂_θ²Φ·W2·sin(2θ)^{-η}`
    `- ∫_z ∫_θ z²∂_zΦ·∂_θ²Φ·(W2)'·sin(2θ)^{-η}`
    `- 2 ∫_z ∫_θ z∂_zΦ·∂_θ²Φ·W2·sin(2θ)^{-η}`.

The proof is the one of the sibling file: the four integrands sum to `∂_z(z²∂_zΦ·W2·∂_θ²Φ)`
pointwise (on the open strip, by `radial_deriv_pointwise_open`), whose `z`-integral vanishes at
every angle in the open interval (by `radial_ibp_zero_open`); Fubini then gives the identity.  All
integrals are over the open strip; the passage between `θ ∈ Iθ` and `θ ∈ (0,π/2)` is by the
almost-everywhere equality of the two angular intervals (their difference is `{0, π/2}`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Fubini and the a.e. equality of the angular intervals -/






/-! ## The main statement -/


end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.thetaGrowth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-growth vocabulary for slices

To *state* the residual gap of `WeakPureAux/weakPhiPoleBound` (see
`NOTES_weakPhiPoleBound.md` §J) one needs a name for "the slice `f` grows at most like
`(π/2-θ)^{-R}` (resp. `θ^{-R}`) as `θ` approaches an endpoint".  Mathlib has no such notion
(asymptotic expansions of smooth functions at a point are not available), so it is introduced
here, together with the closure properties the index-descent argument uses.

`R` is the *pole order*: `RightGrowth f 1` is exactly "`f` grows no faster than the reciprocal
distance to `π/2`", i.e. the conclusion of the target at the right endpoint.  The predicates are
germ conditions (`∀ᶠ`), which is what makes them usable for a.e.-in-`z` statements.

## Contents

* the two predicates `RightGrowth`, `LeftGrowth` and their unfolding characterisations;
* `rpow_neg_mono` (`t^{-R}` is antitone in `R` on `t ∈ (0,1]`), the two one-sided neighbourhood
  lemmas (`π/2 - θ ≤ 1` near `π/2`, `θ ≤ 1` near `0`), the extraction lemmas
  `exists_pos_of_eventually_nhdsGT` / `exists_pos_of_eventually_nhdsLT_pi_div_two` that turn the
  germ statements into statements on `(0, δ)` / `(π/2-δ, π/2)`;
* the closure properties of the two predicates: `mono` (weakening the exponent), `rpow`,
  `const_mul`, `add`;
* **`poleBound_of_growth`**: `RightGrowth f 1` + `LeftGrowth f 1` + continuity in the middle
  gives the *shape of the target*, `|f θ| ≤ C(1/θ + 1/(π/2-θ))`.  This is what turns a pair of
  growth statements (the output of the index-descent argument) into the conclusion of
  `WeakPureAux.weakPhiPoleBound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-- `RightGrowth f R`: near `θ = π/2` the slice `f` grows at most like `(π/2-θ)^{-R}`. -/
def RightGrowth (f : ℝ → ℝ) (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
    |f θ| ≤ C * (Real.pi / 2 - θ) ^ (-R)

/-- `LeftGrowth f R`: near `θ = 0` the slice `f` grows at most like `θ^{-R}`. -/
def LeftGrowth (f : ℝ → ℝ) (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[>] (0 : ℝ), |f θ| ≤ C * θ ^ (-R)



/-- `t^{-R}` is antitone in the exponent on `t ∈ (0,1]`. -/
theorem rpow_neg_mono {t R R' : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hRR' : R ≤ R') :
    t ^ (-R) ≤ t ^ (-R') := by
  have h1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht1
  calc t ^ (-R) = (t ^ R)⁻¹ := Real.rpow_neg (le_of_lt ht0) R
    _ = (t⁻¹) ^ R := (Real.inv_rpow (le_of_lt ht0) R).symm
    _ ≤ (t⁻¹) ^ R' := Real.rpow_le_rpow_of_exponent_le h1 hRR'
    _ = (t ^ R')⁻¹ := Real.inv_rpow (le_of_lt ht0) R'
    _ = t ^ (-R') := (Real.rpow_neg (le_of_lt ht0) R').symm

/-- A neighbourhood of `π/2` on which `π/2 - θ ≤ 1` (frequently used below). -/
theorem eventually_pi_div_two_sub_le_one : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), Real.pi / 2 - θ ≤ 1 := by
  have hmem : ∀ᶠ θ in 𝓝 (Real.pi / 2 : ℝ),
      θ ∈ Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2 + 1) :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with θ hθ
  have h1 : Real.pi / 2 - 1 < θ := (Set.mem_Ioo.mp hθ).1
  linarith

/-- A neighbourhood of `0` on which `θ ≤ 1` (frequently used below). -/
theorem eventually_le_one_of_nhdsGT_zero :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ≤ 1 := by
  have hmem : ∀ᶠ θ in 𝓝 (0 : ℝ), θ ∈ Set.Ioo (-1 : ℝ) 1 :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by norm_num, by norm_num⟩
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with θ hθ
  have h2 : θ < 1 := (Set.mem_Ioo.mp hθ).2
  linarith



/-- **Monotonicity in the exponent**, right endpoint. -/
theorem RightGrowth.mono {f : ℝ → ℝ} {R R' : ℝ} (h : RightGrowth f R) (hRR' : R ≤ R') :
    RightGrowth f R' := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2)),
    eventually_pi_div_two_sub_le_one] with θ hle ht hlt
  have ht0 : 0 < Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  exact le_trans hle (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt hRR') hC)

/-- **Monotonicity in the exponent**, left endpoint. -/
theorem LeftGrowth.mono {f : ℝ → ℝ} {R R' : ℝ} (h : LeftGrowth f R) (hRR' : R ≤ R') :
    LeftGrowth f R' := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)),
    eventually_le_one_of_nhdsGT_zero] with θ hle ht hlt
  have ht0 : 0 < θ := Set.mem_Ioi.mp ht
  exact le_trans hle (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt hRR') hC)

/-- The pure power `θ ↦ (π/2-θ)^{-R}` has right growth `R`. -/
theorem RightGrowth.rpow {R : ℝ} :
    RightGrowth (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-R)) R := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [(self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2))] with θ ht
  have ht0 : 0 ≤ Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  rw [abs_of_nonneg (Real.rpow_nonneg ht0 _), one_mul]

/-- The pure power `θ ↦ θ^{-R}` has left growth `R`. -/
theorem LeftGrowth.rpow {R : ℝ} :
    LeftGrowth (fun θ : ℝ => θ ^ (-R)) R := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with θ hθ
  rw [abs_of_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp hθ).le _), one_mul]

/-- Multiplication by a scalar (weakening the exponent), right endpoint. -/
theorem RightGrowth.const_mul {f : ℝ → ℝ} {R : ℝ} (c : ℝ) (hf : RightGrowth f R)
    {R' : ℝ} (hRR' : R ≤ R') : RightGrowth (fun θ => c * f θ) R' := by
  obtain ⟨C, hC, hf'⟩ := hf.mono hRR'
  refine ⟨|c| * C, by positivity, ?_⟩
  filter_upwards [hf'] with θ hθ
  calc |c * f θ| = |c| * |f θ| := abs_mul _ _
    _ ≤ |c| * (C * (Real.pi / 2 - θ) ^ (-R')) := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = (|c| * C) * (Real.pi / 2 - θ) ^ (-R') := by ring

/-- Multiplication by a scalar (weakening the exponent), left endpoint. -/
theorem LeftGrowth.const_mul {f : ℝ → ℝ} {R : ℝ} (c : ℝ) (hf : LeftGrowth f R)
    {R' : ℝ} (hRR' : R ≤ R') : LeftGrowth (fun θ => c * f θ) R' := by
  obtain ⟨C, hC, hf'⟩ := hf.mono hRR'
  refine ⟨|c| * C, by positivity, ?_⟩
  filter_upwards [hf'] with θ hθ
  calc |c * f θ| = |c| * |f θ| := abs_mul _ _
    _ ≤ |c| * (C * θ ^ (-R')) := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = (|c| * C) * θ ^ (-R') := by ring

/-- Sums: the pole order of a sum is at most the larger of the two, right endpoint. -/
theorem RightGrowth.add {f g : ℝ → ℝ} {R S : ℝ} (hf : RightGrowth f R) (hg : RightGrowth g S) :
    RightGrowth (fun θ => f θ + g θ) (max R S) := by
  obtain ⟨Cf, hCf, hf'⟩ := hf
  obtain ⟨Cg, hCg, hg'⟩ := hg
  refine ⟨Cf + Cg, by positivity, ?_⟩
  filter_upwards [hf', hg', (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2)),
    eventually_pi_div_two_sub_le_one] with θ hfθ hgθ ht hlt
  have ht0 : 0 < Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  calc |f θ + g θ| ≤ |f θ| + |g θ| := abs_add_le _ _
    _ ≤ Cf * (Real.pi / 2 - θ) ^ (-R) + Cg * (Real.pi / 2 - θ) ^ (-S) := add_le_add hfθ hgθ
    _ ≤ Cf * (Real.pi / 2 - θ) ^ (-max R S) + Cg * (Real.pi / 2 - θ) ^ (-max R S) :=
        add_le_add (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_left R S)) hCf)
          (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_right R S)) hCg)
    _ = (Cf + Cg) * (Real.pi / 2 - θ) ^ (-max R S) := by ring

/-- Sums: the pole order of a sum is at most the larger of the two, left endpoint. -/
theorem LeftGrowth.add {f g : ℝ → ℝ} {R S : ℝ} (hf : LeftGrowth f R) (hg : LeftGrowth g S) :
    LeftGrowth (fun θ => f θ + g θ) (max R S) := by
  obtain ⟨Cf, hCf, hf'⟩ := hf
  obtain ⟨Cg, hCg, hg'⟩ := hg
  refine ⟨Cf + Cg, by positivity, ?_⟩
  filter_upwards [hf', hg', (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)),
    eventually_le_one_of_nhdsGT_zero] with θ hfθ hgθ ht hlt
  have ht0 : 0 < θ := Set.mem_Ioi.mp ht
  calc |f θ + g θ| ≤ |f θ| + |g θ| := abs_add_le _ _
    _ ≤ Cf * θ ^ (-R) + Cg * θ ^ (-S) := add_le_add hfθ hgθ
    _ ≤ Cf * θ ^ (-max R S) + Cg * θ ^ (-max R S) :=
        add_le_add (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_left R S)) hCf)
          (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_right R S)) hCg)
    _ = (Cf + Cg) * θ ^ (-max R S) := by ring


end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.eslDth2Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-- On the *open* interval `(0, π/2)` — where the second iterate of `D_θ = sin(2θ) ∂_θ`
can be computed by the product rule — the second iterate of the one-dimensional angular
operator `Dth1Iter 2` of an arbitrary `C²` function is

`D_θ²u = 2 sin(2θ)cos(2θ)·u' + sin(2θ)²·u''`.

Only two orders of regularity are needed (`ContDiffOn ℝ 2`), which is what the weak
`H²` estimate `eslDth2Bound` has at its disposal. -/
theorem Dth1Iter_two_expand (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Elliptic.Dth1Iter 2 u θ
      = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv u θ
        + (Real.sin (2 * θ)) ^ 2 * deriv (fun t => deriv u t) θ := by
  have hder : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := hu.deriv_of_isOpen isOpen_Ioo (m := 1) (n := 2) (by norm_num)
    simpa using h
  have hd1 : DifferentiableAt ℝ (deriv u) θ :=
    (hder.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * θ) * 2) θ := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id θ).const_mul (2 : ℝ))).sin
    convert h2 using 1
    ring
  have hprod : HasDerivAt (fun t : ℝ => Real.sin (2 * t) * deriv u t)
      (2 * Real.cos (2 * θ) * deriv u θ
        + Real.sin (2 * θ) * deriv (fun t => deriv u t) θ) θ :=
    hsin.mul hd1.hasDerivAt
  have hderiv := hprod.deriv
  show Real.sin (2 * θ) * deriv (fun t : ℝ => Real.sin (2 * t) * deriv u t) θ = _
  rw [hderiv]
  ring

/-- The pointwise algebraic (weighted) inequality behind `eslDth2Bound`: for `θ ∈ [0, π/2]`
and arbitrary reals `u₁ u₂`, the square of `2 sin(2θ)cos(2θ)u₁ + sin(2θ)²u₂` against the
mixed-angular weight `sin(2θ)^{-γ}` is dominated by the two pure weights `sin(2θ)^{-η}`.

The gain is exactly the factor `sin(2θ)^{η-γ}`: since `γ ≥ η` and `sin(2θ) ≤ 1` one has
`sin(2θ)^{-γ} ≤ sin(2θ)^{-η}·sin(2θ)^{η-γ}`, and `sin(2θ)^{η-γ} sin(2θ)^{2}` and
`sin(2θ)^{η-γ} sin(2θ)^{4}` are both `≤ 1`, which converts the two terms of the elementary
inequality `(A + B)² ≤ 2A² + 2B²` into the constants `8 = 2·4` and `2 = 2·1`. -/
theorem sGam_mul_sq_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u₁ u₂ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (2 * Real.sin (2 * θ) * Real.cos (2 * θ) * u₁ + (Real.sin (2 * θ)) ^ 2 * u₂) ^ 2
        * Work.FTS.EllipticEst.sGam α θ
      ≤ 8 * (u₁ ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 2 * (u₂ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  set s := Real.sin (2 * θ) with hs_def
  set c := Real.cos (2 * θ) with hc_def
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := hθ.2
  have hs0 : 0 ≤ s := by
    rw [hs_def]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs_def]; exact Real.sin_le_one _
  have hc2 : c ^ 2 ≤ 1 := by rw [hc_def]; exact Real.cos_sq_le_one _
  have hsGam : Work.FTS.EllipticEst.sGam α θ = s ^ (-(Work.Spaces.gam α)) := by
    simp only [Work.FTS.EllipticEst.sGam]; rw [← hs_def]
  have hsEta : Work.FTS.EllipticEst.sEta θ = s ^ (-(Work.Spaces.eta)) := by
    simp only [Work.FTS.EllipticEst.sEta]; rw [← hs_def]
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    simp only [Work.Spaces.eta, Work.Spaces.gam]; linarith
  have heta0 : 0 ≤ Work.Spaces.eta := by simp only [Work.Spaces.eta]; norm_num
  have hgam2 : Work.Spaces.gam α ≤ 2 := by
    simp only [Work.Spaces.gam]; linarith
  have hexp2 : 0 ≤ Work.Spaces.eta - Work.Spaces.gam α + 2 := by linarith
  have hexp4 : 0 ≤ Work.Spaces.eta - Work.Spaces.gam α + 4 := by linarith
  rcases eq_or_lt_of_le hs0 with hs_zero | hs_pos
  · have hsz : s = 0 := hs_zero.symm
    have hX : 2 * s * c * u₁ + s ^ 2 * u₂ = 0 := by rw [hsz]; ring
    have hsg : Work.FTS.EllipticEst.sGam α θ = 0 := by
      rw [hsGam, hsz,
        Real.zero_rpow (by simp only [Work.Spaces.gam]; linarith : -(Work.Spaces.gam α) ≠ 0)]
    have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
      rw [hsEta, hsz, Real.zero_rpow (by simp [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    rw [hX, hsg, hse]
    norm_num
  · have hX2 : (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2
        ≤ 2 * (2 * s * c * u₁) ^ 2 + 2 * (s ^ 2 * u₂) ^ 2 := by
      nlinarith [sq_nonneg (2 * s * c * u₁ - s ^ 2 * u₂)]
    set k := s ^ (Work.Spaces.eta - Work.Spaces.gam α) with hk_def
    have hk0 : 0 ≤ k := Real.rpow_nonneg hs0 _
    have hks2 : k * s ^ 2 ≤ 1 := by
      rw [hk_def, ← Real.rpow_natCast s 2, ← Real.rpow_add hs_pos]
      exact Real.rpow_le_one hs0 hs1 hexp2
    have hks4 : k * s ^ 4 ≤ 1 := by
      rw [hk_def, ← Real.rpow_natCast s 4, ← Real.rpow_add hs_pos]
      exact Real.rpow_le_one hs0 hs1 hexp4
    have hkey : k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 ≤ 8 * u₁ ^ 2 + 2 * u₂ ^ 2 := by
      calc k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2
          ≤ k * (2 * (2 * s * c * u₁) ^ 2 + 2 * (s ^ 2 * u₂) ^ 2) :=
            mul_le_mul_of_nonneg_left hX2 hk0
        _ = (k * s ^ 2) * (8 * c ^ 2 * u₁ ^ 2) + (k * s ^ 4) * (2 * u₂ ^ 2) := by ring
        _ ≤ 1 * (8 * c ^ 2 * u₁ ^ 2) + 1 * (2 * u₂ ^ 2) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hks2 (by positivity)
            · exact mul_le_mul_of_nonneg_right hks4 (by positivity)
        _ ≤ 8 * u₁ ^ 2 + 2 * u₂ ^ 2 := by nlinarith [sq_nonneg u₁, sq_nonneg u₂, sq_nonneg c]
    have hgEq : Work.FTS.EllipticEst.sGam α θ = Work.FTS.EllipticEst.sEta θ * k := by
      rw [hsGam, hsEta, hk_def, ← Real.rpow_add hs_pos]
      congr 1
      ring
    have hsk : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [hsEta]; exact Real.rpow_nonneg hs0 _
    calc (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        = Work.FTS.EllipticEst.sGam α θ * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2 := by ring
      _ = Work.FTS.EllipticEst.sEta θ * (k * (2 * s * c * u₁ + s ^ 2 * u₂) ^ 2) := by
            rw [hgEq]; ring
      _ ≤ Work.FTS.EllipticEst.sEta θ * (8 * u₁ ^ 2 + 2 * u₂ ^ 2) :=
            mul_le_mul_of_nonneg_left hkey hsk
      _ = 8 * (u₁ ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + 2 * (u₂ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

theorem eslDth2Bound (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter 2 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ 8 * ((deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  intro θ hθ
  by_cases hs : Real.sin (2 * θ) = 0
  · have hX : Work.Elliptic.Dth1Iter 2 u θ = 0 := by
      simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
      rw [hs]; ring
    have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
      simp only [Work.FTS.EllipticEst.sEta]
      rw [hs, Real.zero_rpow (by simp [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    rw [hX, hse]
    norm_num
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; exact hs (by rw [← h]; simp)
      · intro h
        exact hs (by rw [h]; norm_num [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])
    rw [Dth1Iter_two_expand u hu hθ']
    exact sGam_mul_sq_le α hα hα4 (deriv u θ) (deriv (fun t => deriv u t) θ) hθ

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HarOp_lintegral_swap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.FTS.EllipticEst

/-! ## The two weights, `Ioi 0`-truncated, and the region of integration -/

/-- The `Ioi 0`-truncated radial weight `z ↦ w(z)² z^{-β}`, as an `ℝ≥0∞`-valued function. -/
noncomputable def harSwapW (β : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))

/-- The `Ioi 0`-truncated Hardy weight `s ↦ s^{β-1} f(s)²`, as an `ℝ≥0∞`-valued function. -/
noncomputable def harSwapXi (β : ℝ) (f : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun s => ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))

/-- The region `{(z,s) | 0 < s ≤ z}` of the double integral. -/
def harSwapR : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}

theorem measurableSet_harSwapR : MeasurableSet harSwapR := by
  have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  exact h1.inter h2


theorem harSwapXi_ne_top (β : ℝ) (f : ℝ → ℝ) (s : ℝ) : harSwapXi β f s ≠ ⊤ := by
  unfold harSwapXi
  by_cases h : s ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-! ## Measurability -/

/-- The weight `z ↦ w(z)² z^{-β}` is continuous on `(0,∞)`. -/
theorem continuousOn_harSwapWeight (β : ℝ) :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z ^ (-β)) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun z hz => by
        simp only [Set.mem_Ioi] at hz
        positivity)
  exact (hw.pow 2).mul (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))

theorem aemeasurable_harSwapW (β : ℝ) : AEMeasurable (harSwapW β) volume := by
  unfold harSwapW
  refine Work.Elliptic.aemeasurable_indicator_restrict measurableSet_Ioi ?_
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (continuousOn_harSwapWeight β)).aemeasurable measurableSet_Ioi

theorem aemeasurable_harSwapXi {β : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    AEMeasurable (harSwapXi β f) volume := by
  unfold harSwapXi
  refine Work.Elliptic.aemeasurable_indicator_restrict measurableSet_Ioi ?_
  have h1 : AEMeasurable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioi 0)) :=
    hf.aestronglyMeasurable.aemeasurable
  have h2 : AEMeasurable (fun s : ℝ => s ^ (β - 1)) (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx))).aemeasurable
      measurableSet_Ioi
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h1)

/-! ## The Tonelli exchange -/

theorem HarOp_lintegral_swap (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := by
  have _hβpos : (0 : ℝ) < β - 1 := by linarith
  have huncurry : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * p.1 ^ (-β)) *
        (Set.Ioc 0 p.1).indicator (harSwapXi β f) p.2) (volume.prod volume) := by
    have hpt : (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.w p.1) ^ 2 * p.1 ^ (-β)) *
          (Set.Ioc 0 p.1).indicator (harSwapXi β f) p.2)
        = fun p : ℝ × ℝ =>
            harSwapW β p.1 * harSwapXi β f p.2 * harSwapR.indicator (fun _ => 1) p := by
      funext p
      obtain ⟨z, s⟩ := p
      dsimp only
      by_cases h : s ∈ Set.Ioc 0 z
      · have hz : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le h.1 h.2
        have hmem : (z, s) ∈ harSwapR := h
        unfold harSwapW harSwapXi
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem h,
          Set.indicator_of_mem hmem, mul_one]
      · have hmem : (z, s) ∉ harSwapR := h
        unfold harSwapW harSwapXi
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hmem]
        simp
    rw [hpt]
    exact ((aemeasurable_harSwapW β).comp_fst.mul
        (aemeasurable_harSwapXi hf).comp_snd).mul
      (measurable_const.indicator measurableSet_harSwapR).aemeasurable
  have hinner : ∀ z : ℝ, (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))
      = ∫⁻ s in Set.Ioc 0 z, harSwapXi β f s := by
    intro z
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    unfold harSwapXi
    exact (Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs.1)
      (fun s => ENNReal.ofReal (s ^ (β - 1) * f s ^ 2))).symm
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)))
      = ∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (Set.Ioc 0 z).indicator (harSwapXi β f) s := by
    have h1a : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2)))
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, harSwapXi β f s) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [hinner z]
    have h1b : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
          (∫⁻ s in Set.Ioc 0 z, harSwapXi β f s))
        = ∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hz, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Ioc]
      · rw [Set.indicator_of_notMem hz]
        have hz0 : Set.Ioc 0 z = ∅ := Set.Ioc_eq_empty hz
        rw [hz0]
        simp
    exact h1a.trans h1b
  have h2 : (∫⁻ z, ∫⁻ s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s)
      = ∫⁻ s, ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s :=
    lintegral_lintegral_swap huncurry
  have h3 : (∫⁻ s, ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
        (Set.Ioc 0 z).indicator (harSwapXi β f) s)
      = ∫⁻ s in Set.Ioi 0, harSwapXi β f s *
          ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hs]
      have hFeq : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s)
          = (Set.Ici s).indicator (fun z =>
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) * harSwapXi β f s) := by
        funext z
        by_cases hzs : s ≤ z
        · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 z from ⟨hs, hzs⟩),
              Set.indicator_of_mem (show z ∈ Set.Ici s from hzs)]
        · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hzs h.2),
              Set.indicator_of_notMem (show z ∉ Set.Ici s from hzs)]
          simp
      rw [hFeq, lintegral_indicator measurableSet_Ici]
      rw [show (∫⁻ z in Set.Ici s,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) * harSwapXi β f s)
            = ∫⁻ z in Set.Ici s,
              harSwapXi β f s * ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) from
          setLIntegral_congr_fun measurableSet_Ici (fun z _ => mul_comm _ _)]
      rw [lintegral_const_mul' (harSwapXi β f s)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
        (harSwapXi_ne_top β f s)]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)) *
            (Set.Ioc 0 z).indicator (harSwapXi β f) s) = fun _ => (0 : ℝ≥0∞) := by
        funext z
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hs h.1)]
        simp
      rw [hzero]
      simp
  have h4 : (∫⁻ s in Set.Ioi 0, harSwapXi β f s *
        ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β)))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) *
        (∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    unfold harSwapXi
    rw [Set.indicator_of_mem hs]
  exact h1.trans (h2.trans (h3.trans h4))

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Topology

/-- **The derivative of the singular term `L₁₂`.**  If the angular moment `F_*(r) = Fstar F r`
is smooth on `(0,∞)` and `r ↦ F_*(r)/r` is integrable there, then
`L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr` is differentiable at every `z > 0`, with derivative
`-3 F_*(z)/z` (the fundamental theorem of calculus for the improper integral `∫_z^∞`). -/
theorem HasDerivAt_L12_of_Fstar_facts (F : ℝ → ℝ → ℝ)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  set g : ℝ → ℝ := fun r => Work.Elliptic.Fstar F r / r with hg
  -- the density `g` is continuous on `(0,∞)`, hence at `z` (where `z ≠ 0`)
  have hgcontOn : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    rw [hg]
    exact ((hFsm 0).continuousOn).div continuousOn_id (fun x hx => ne_of_gt hx)
  have hgcont : ContinuousAt g z := hgcontOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hgmeas : StronglyMeasurableAtFilter g (𝓝 z) MeasureTheory.volume :=
    hgcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have hInt0 : MeasureTheory.IntegrableOn g (Set.Ioi 0) := hFint
  have hInt : IntervalIntegrable g MeasureTheory.volume 0 z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le]
    exact hInt0.mono_set (fun x hx => hx.1)
  -- fundamental theorem of calculus for the interval integral `u ↦ ∫_0^u g`
  have hFTC : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hgmeas hgcont
  have hC : HasDerivAt (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r)
      (-(g z)) z := by
    have h := hFTC.const_sub (∫ r in Set.Ioi (0 : ℝ), g r)
    simpa using h
  -- on `(0,∞)` (a neighbourhood of `z`), `∫_u^∞ g = ∫_0^∞ g - ∫_0^u g`
  have heq : (fun u => ∫ r in Set.Ioi u, g r)
      =ᶠ[𝓝 z] (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    have hIntu : MeasureTheory.IntegrableOn g (Set.Ioi u) :=
      hInt0.mono_set (Set.Ioi_subset_Ioi hu.le)
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (f := g) (a := (0 : ℝ)) (b := u) hInt0 hIntu
    linarith [h]
  have hcore : HasDerivAt (fun u => ∫ r in Set.Ioi u, g r) (-(g z)) z :=
    hC.congr_of_eventuallyEq heq
  -- `L12rad F u = ∫_u^∞ F_*(r)/r dr` is literally this function
  have hrad : HasDerivAt (Work.Elliptic.L12rad F) (-(Work.Elliptic.Fstar F z / z)) z := by
    rw [hg] at hcore
    exact hcore
  have h3 : HasDerivAt (fun u => 3 * Work.Elliptic.L12rad F u)
      (3 * (-(Work.Elliptic.Fstar F z / z))) z :=
    hrad.const_mul 3
  have hL12eq : Work.Elliptic.L12 F = fun u => 3 * Work.Elliptic.L12rad F u :=
    funext (Work.Elliptic.L12_eq_radial F)
  rw [hL12eq]
  exact h3.congr_deriv (by ring)

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceTendstoAntiderivZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Squeezing with a bounded factor.** If `g → 0` along `l` and `|f| ≤ c |g|` eventually then
`f → 0` along `l` (no sign hypothesis on `c`: `c |g| → c * 0 = 0` regardless). -/
lemma tendsto_zero_of_eventually_abs_le {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hg : Filter.Tendsto g l (nhds 0)) (h : ∀ᶠ x in l, |f x| ≤ c * |g x|) :
    Filter.Tendsto f l (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (f := fun x => ‖f x‖) (g := fun x => c * ‖g x‖) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [h] with x hx
    simpa only [Real.norm_eq_abs] using hx
  · simpa using hg.norm.const_mul c

/-- **The antiderivative `F θ = -(deriv u θ) * u θ + (1/2) * tan θ * (u θ)^2` tends to `0` at
both endpoints of `(0, π/2)`.**  Hypotheses: `u → 0` at `0⁺` and at `(π/2)⁻`, `|u'| ≤ M`,
`|u| ≤ B` and `|u / cos θ| ≤ K` on `(0, π/2)`.

Proof route, by squeezing (`squeeze_zero` + `tendsto_zero_iff_norm_tendsto_zero`):
* `(deriv u) * u → 0` at both endpoints since `|(deriv u θ) * u θ| ≤ M |u θ|`, `|u θ| → 0`, and
  `(0, π/2) ∈ 𝓝[>] 0` and `(0, π/2) ∈ 𝓝[<] (π/2)` make the pointwise bounds available eventually;
* `tan θ * (u θ)^2 → 0` at `0⁺` since `|Real.tan θ * (u θ)^2| ≤ |Real.tan θ| * B^2` and
  `Real.tan → 0` at `0` (`Real.continuous_tan`, `Real.tan_zero`);
* `tan θ * (u θ)^2 → 0` at `(π/2)⁻` since
  `|Real.tan θ * (u θ)^2| = |Real.sin θ| * |u θ| * |u θ / cos θ| ≤ 1 * K * |u θ|` and `u → 0`.
Then assemble with `Filter.Tendsto.neg.mul`, `Filter.Tendsto.add` and constants.

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceTendstoAntiderivZero`. -/
theorem SliceTendstoAntiderivZero (u : ℝ → ℝ) {B K M : ℝ}
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hK : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K) :
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- the pointwise bounds are available *eventually*, on both one-sided filters
  have hev0 : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), s ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hhalf),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs', hs⟩
  have hevpi : ∀ᶠ s in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      s ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hhalf),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs, hs'⟩
  -- the `-(deriv u) * u` term at both endpoints
  have hA0 : Filter.Tendsto (fun s => -(deriv u s) * u s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max M 0) h0 ?_
    filter_upwards [hev0] with s hs
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (le_trans (hM s hs) (le_max_left _ _)) (abs_nonneg (u s))
  have hApi : Filter.Tendsto (fun s => -(deriv u s) * u s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max M 0) hpi ?_
    filter_upwards [hevpi] with s hs
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (le_trans (hM s hs) (le_max_left _ _)) (abs_nonneg (u s))
  -- the `(1/2) * tan θ * (u θ)^2` term at `0⁺`: `tan → 0` and `|u| ≤ B`
  have htan0 : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have htan : Filter.Tendsto Real.tan (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt Real.tan 0 := Real.continuousAt_tan.mpr (by simp)
      simpa [Real.tan_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_zero_of_eventually_abs_le (c := (max B 0) ^ 2 / 2) htan ?_
    filter_upwards [hev0] with s hs
    have hBs : |u s| ≤ max B 0 := le_trans (hB s hs) (le_max_left _ _)
    have hsq : (u s) ^ 2 ≤ (max B 0) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (u s)) hBs 2
      simpa [sq_abs] using this
    have habs : |(1 / 2 : ℝ) * Real.tan s * (u s) ^ 2|
        = (1 / 2 : ℝ) * |Real.tan s| * (u s) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2), abs_sq]
    rw [habs]
    calc (1 / 2 : ℝ) * |Real.tan s| * (u s) ^ 2
        ≤ (1 / 2 : ℝ) * |Real.tan s| * (max B 0) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ((max B 0) ^ 2 / 2) * |Real.tan s| := by ring
  -- the same term at `(π/2)⁻`: `tan θ * (u θ)^2 = sin θ * u θ * (u θ / cos θ)`
  have htanpi : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max K 0 / 2) hpi ?_
    filter_upwards [hevpi] with s hs
    have hcos : Real.cos s ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hhalf, hs.1], hs.2⟩)
    have hid : (1 / 2 : ℝ) * Real.tan s * (u s) ^ 2
        = (1 / 2 : ℝ) * Real.sin s * u s * (u s / Real.cos s) := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have hstep : |(1 / 2 : ℝ) * Real.sin s * u s * (u s / Real.cos s)|
        = (1 / 2 : ℝ) * |Real.sin s| * |u s| * |u s / Real.cos s| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    rw [hid, hstep]
    have h1 : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
    have h2 : |u s / Real.cos s| ≤ max K 0 := le_trans (hK s hs) (le_max_left _ _)
    have h6 : |Real.sin s| * |u s / Real.cos s| ≤ max K 0 := by
      have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
      simpa using this
    calc (1 / 2 : ℝ) * |Real.sin s| * |u s| * |u s / Real.cos s|
        = (1 / 2 : ℝ) * |u s| * (|Real.sin s| * |u s / Real.cos s|) := by ring
      _ ≤ (1 / 2 : ℝ) * |u s| * max K 0 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (max K 0 / 2) * |u s| := by ring
  exact ⟨by simpa using hA0.add htan0, by simpa using hApi.add htanpi⟩

end Work.FTS.EllipticEst.Honest.SelfAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceUDivCosBdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **`u / cos θ` is bounded on `(0, π/2)`.**  If `|u| ≤ B` on `(0, π/2)` and
`|u θ| ≤ M (π/2 - θ)` there, then `u / cos θ` is bounded on `(0, π/2)`.

Proof route: on `(0, π/2)` one has `Real.cos θ > 0` (`Real.cos_pos_of_mem_Ioo`) and
`Real.cos θ = Real.sin (π/2 - θ) ≥ (2/π)(π/2 - θ)` (`Real.mul_le_sin`).  So for `θ ∈ (0, π/4]`,
`cos θ ≥ (2/π)(π/4) = 1/2` and `|u θ / cos θ| ≤ 2B`; for `θ ∈ [π/4, π/2)`,
`|u θ / cos θ| ≤ M (π/2 - θ) / ((2/π)(π/2 - θ)) = (π/2) M`.  Hence
`K = max (2B) ((π/2) M)` works (both `B ≥ 0` and `M ≥ 0` follow from the hypotheses and the
non-emptiness of `(0, π/2)`, and `Real.cos θ > 0` makes the division safe).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceUDivCosBdd`. -/
theorem SliceUDivCosBdd (u : ℝ → ℝ) {B M : ℝ}
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hlin : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ)) :
    ∃ K : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K := by
  -- `π/4` lies in `(0, π/2)`, so the bounds `B, M ≥ 0` follow from the hypotheses.
  have h4mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB _ h4mem)
  have hM0 : 0 ≤ M := by
    have h := hlin _ h4mem
    have h4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h2 : 0 ≤ M * (Real.pi / 4) := by
      have h3 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      rw [h3] at h
      exact le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right h4).mp h2
  refine ⟨max (2 * B) (Real.pi / 2 * M), fun θ hθ => ?_⟩
  -- `cos θ > 0` on `(0, π/2)`, so the division is safe.
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  rw [abs_div, abs_of_pos hcos]
  -- `cos θ = sin (π/2 - θ) ≥ (2/π)(π/2 - θ)`.
  have hcoslb : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have hx0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hxle : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have h := Real.mul_le_sin hx0 hxle
    rwa [Real.sin_pi_div_two_sub] at h
  rcases le_or_gt θ (Real.pi / 4) with hθ4 | hθ4
  · -- `θ ≤ π/4`: then `cos θ ≥ 1/2`, so `|u θ| / cos θ ≤ 2B`.
    have hcos12 : (1 : ℝ) / 2 ≤ Real.cos θ := by
      have hmono : (2 / Real.pi) * (Real.pi / 4) ≤ (2 / Real.pi) * (Real.pi / 2 - θ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h2 : (2 / Real.pi) * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith [hcoslb, hmono]
    calc |u θ| / Real.cos θ ≤ B / Real.cos θ := by
          apply div_le_div_of_nonneg_right (hB θ hθ) (le_of_lt hcos)
      _ ≤ B / (1 / 2) := by
          apply div_le_div_of_nonneg_left hB0 (by norm_num) hcos12
      _ = 2 * B := by ring
      _ ≤ max (2 * B) (Real.pi / 2 * M) := le_max_left _ _
  · -- `θ > π/4`: then `|u θ| / cos θ ≤ M(π/2 - θ) / ((2/π)(π/2 - θ)) = (π/2) M`.
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hden : 0 < (2 / Real.pi) * (Real.pi / 2 - θ) := by
      apply mul_pos (by positivity) hpos
    calc |u θ| / Real.cos θ ≤ M * (Real.pi / 2 - θ) / Real.cos θ := by
          apply div_le_div_of_nonneg_right (hlin θ hθ) (le_of_lt hcos)
      _ ≤ M * (Real.pi / 2 - θ) / ((2 / Real.pi) * (Real.pi / 2 - θ)) := by
          apply div_le_div_of_nonneg_left (by positivity) hden hcoslb
      _ = Real.pi / 2 * M := by
          rw [mul_div_mul_right _ _ (by linarith : Real.pi / 2 - θ ≠ 0)]
          field_simp
      _ ≤ max (2 * B) (Real.pi / 2 * M) := le_max_right _ _

end Work.FTS.EllipticEst.Honest.SelfAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceULinearRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Linear vanishing of `u` at the right endpoint.**  If `u` is `C¹` on `(0, π/2)` with
`|u'| ≤ M` there, and `u → 0` as `θ → (π/2)⁻`, then `|u θ| ≤ M (π/2 - θ)` on all of `(0, π/2)`.

Proof route: fix `θ ∈ (0, π/2)`; for `θ' ∈ (θ, π/2)` Newton–Leibniz on `[θ, θ']`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` on the closed segment, where `u' = deriv u` is
continuous) gives `|u θ - u θ'| ≤ M (θ' - θ)`; then `θ' ↦ u θ' + M (θ' - θ)` and
`θ' ↦ u θ' - M (θ' - θ)` tend to `M (π/2 - θ)` and `-M (π/2 - θ)` along `𝓝[<] (π/2)`, so
`Filter.le_of_tendsto` gives both `u θ ≤ M (π/2 - θ)` and `u θ ≥ -M (π/2 - θ)`, i.e. the claim.
Note `(0, π/2) ∈ 𝓝[<] (π/2)`, so the pointwise hypothesis `hM` is available eventually.

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceULinearRight`. -/
theorem SliceULinearRight (u : ℝ → ℝ) {M : ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ) := by
  intro θ hθ
  obtain ⟨hθ0, hθpi⟩ := hθ
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) := hsm.differentiableOn (by norm_num)
  -- Newton–Leibniz on `[θ, θ']`: the mean value inequality for a differentiable function whose
  -- derivative is bounded by `M` on the segment.
  have hkey : ∀ θ' ∈ Set.Ioo θ (Real.pi / 2), |u θ' - u θ| ≤ M * (θ' - θ) := by
    intro θ' hθ'
    obtain ⟨hθ'1, hθ'2⟩ := hθ'
    have hf : ∀ x ∈ Set.Icc θ θ', HasDerivWithinAt u (deriv u x) (Set.Icc θ θ') x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hθ'2⟩
      exact ((hdiff x hx').differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt.hasDerivWithinAt
    have hb : ∀ x ∈ Set.Ico θ θ', ‖deriv u x‖ ≤ M := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_lt_of_le hθ0 hx.1, lt_trans hx.2 hθ'2⟩
      simpa [Real.norm_eq_abs] using hM x hx'
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hf hb θ' (Set.right_mem_Icc.mpr hθ'1.le)
    simpa [Real.norm_eq_abs] using h
  -- `(θ, π/2)` is a neighbourhood of `π/2` within `(-∞, π/2)`.
  have hIoo : Set.Ioo θ (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [show Set.Ioo θ (Real.pi / 2) = Set.Ioi θ ∩ Set.Iio (Real.pi / 2) from rfl]
    exact Filter.inter_mem (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hθpi)) self_mem_nhdsWithin
  have hphi : Filter.Tendsto (fun θ' : ℝ => M * (θ' - θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (M * (Real.pi / 2 - θ))) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto (Real.pi / 2)).mono_left
      nhdsWithin_le_nhds
  have hupper : u θ ≤ M * (Real.pi / 2 - θ) := by
    have hlim1 : Filter.Tendsto (fun θ' : ℝ => u θ' + M * (θ' - θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (M * (Real.pi / 2 - θ))) := by
      have h := hpi.add hphi
      simpa using h
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim1 ?_
    filter_upwards [hIoo] with θ' hθ'
    have h2 := (abs_le.mp (hkey θ' hθ')).1
    linarith
  have hlower : -(M * (Real.pi / 2 - θ)) ≤ u θ := by
    have hlim3 : Filter.Tendsto (fun θ' : ℝ => u θ' - M * (θ' - θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-(M * (Real.pi / 2 - θ)))) := by
      have h := hpi.sub hphi
      simpa using h
    refine le_of_tendsto_of_tendsto hlim3 tendsto_const_nhds ?_
    filter_upwards [hIoo] with θ' hθ'
    have h2 := (abs_le.mp (hkey θ' hθ')).2
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

end Work.FTS.EllipticEst.Honest.SelfAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the angular weight `σ θ = sin(2θ)^{-η}` and the
constraint profile `ψ θ = sin θ cos²θ` -/

/-- The constraint profile `ψ θ = sin θ cos²θ` of the solvability condition. -/
private def psi (θ : ℝ) : ℝ := Real.sin θ * Real.cos θ ^ 2

private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

private lemma sEta_nonneg_prv {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

private lemma sEta_zero_left : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

private lemma sEta_zero_right : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

private lemma sEta_integrableOn_prv :
    Integrable (Work.FTS.EllipticEst.sEta) (volume.restrict Iθ) :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

private lemma psi_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ psi θ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  show 0 ≤ Real.sin θ * Real.cos θ ^ 2
  exact mul_nonneg hs (sq_nonneg _)

private lemma psi_zero_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Iθ)
    (h : θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : psi θ = 0 := by
  have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
    rcases lt_or_eq_of_le hθ.1 with hlt | heq
    · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt (fun hgt => h ⟨hlt, hgt⟩)))
    · exact Or.inl heq.symm
  rcases hcases with h0 | hpi
  · rw [h0]
    show Real.sin 0 * Real.cos 0 ^ 2 = 0
    simp
  · rw [hpi]
    show Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0
    rw [Real.cos_pi_div_two]
    ring

private lemma psi_continuous : Continuous psi := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

private lemma psi_integrableOn : Integrable (fun θ : ℝ => psi θ) (volume.restrict Iθ) :=
  psi_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- `∫₀^{π/2} sin θ cos²θ dθ = 1/3`, by the fundamental theorem of calculus
with the antiderivative `θ ↦ -cos³θ/3`. -/
private lemma psi_integral : (∫ θ in Iθ, psi θ) = 1 / 3 := by
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (psi θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * (Real.cos θ) ^ 2) (Real.cos θ) := by
      simpa using hasDerivAt_pow 3 (Real.cos θ)
    refine ((h2.comp θ h1).neg.div_const 3).congr_deriv ?_
    rw [psi]
    ring
  have hInt : IntervalIntegrable psi volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) (by linarith [Real.pi_pos])).mpr
      (MeasureTheory.IntegrableOn.mono_set psi_integrableOn
        (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  have hFTC : ∫ t in (0 : ℝ)..(Real.pi / 2), psi t
      = (fun t : ℝ => -((Real.cos t) ^ 3) / 3) (Real.pi / 2)
        - (fun t : ℝ => -((Real.cos t) ^ 3) / 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hInt
  calc (∫ θ in Iθ, psi θ) = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), psi θ := by
        rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0 : ℝ)..(Real.pi / 2), psi t :=
        (intervalIntegral.integral_of_le (by linarith [Real.pi_pos])).symm
    _ = 1 / 3 := by
        rw [hFTC]
        change -((Real.cos (Real.pi / 2)) ^ 3) / 3 - (-((Real.cos 0) ^ 3) / 3) = 1 / 3
        norm_num [Real.cos_pi_div_two, Real.cos_zero]

/-! ## The fundamental theorem of calculus on the open interval -/

/-- **Increment bound.**  A `C¹` function on the open interval has increments bounded by the
total mass of `|f'|` over `Iθ`. -/
private lemma abs_sub_le_integral_abs_deriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ))
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hab : a ≤ b) :
    |f a - f b| ≤ ∫ θ in Iθ, |deriv f θ| := by
  have hsub : Set.Icc a b ⊆ Iθ := fun x hx =>
    ⟨le_trans (le_of_lt ha.1) hx.1, le_trans hx.2 (le_of_lt hb.2)⟩
  have hIoo : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have h1 : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.IntegrableOn.mono_set hint hsub
  have h2 : Integrable (fun θ : ℝ => deriv f θ) (volume.restrict (Set.Icc a b)) :=
    h1.mono' (measurable_deriv f).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simp [Real.norm_eq_abs]))
  have hII : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume) hab).mpr
      (MeasureTheory.IntegrableOn.mono_set h2 (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hf.differentiableOn (by norm_num)).hasDerivAt
      (isOpen_Ioo.mem_nhds ⟨(hIoo x hx).1, (hIoo x hx).2⟩)
  have hFTC : ∫ x in a..b, deriv f x = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII
  rw [abs_sub_comm]
  calc |f b - f a| = |∫ x in a..b, deriv f x| := by rw [hFTC]
    _ ≤ ∫ x in a..b, |deriv f x| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume)
            (f := fun x : ℝ => deriv f x) hab
    _ = ∫ x in Set.Ioc a b, |deriv f x| := intervalIntegral.integral_of_le hab
    _ ≤ ∫ x in Iθ, |deriv f x| := by
        refine MeasureTheory.setIntegral_mono_set (μ := volume)
          (f := fun x : ℝ => |deriv f x|) (s := Set.Ioc a b) (t := Iθ) hint ?_ ?_
        · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x _ => abs_nonneg (deriv f x))
        · exact Filter.Eventually.of_forall (fun x hx => hsub ⟨le_of_lt hx.1, hx.2⟩)

/-! ## The constraint implies an `L¹` bound on the function -/

/-- **The constraint bounds `f` pointwise.**  If the moment `∫_θ f ψ` of a `C¹` function on the
open interval vanishes (`ψ = sin θ cos²θ` has `∫_θ ψ = 1/3 > 0`), then
`|f t| ≤ ∫_θ |f'|` for every interior `t`. -/
private lemma abs_le_integral_abs_deriv_of_constraint {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ))
    (hintf : Integrable (fun θ : ℝ => f θ * psi θ) (volume.restrict Iθ))
    (hzero : (∫ θ in Iθ, f θ * psi θ) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |f t| ≤ ∫ θ in Iθ, |deriv f θ| := by
  have hincr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f t - f θ| ≤ ∫ θ in Iθ, |deriv f θ| := by
    intro θ hθ
    rcases le_total t θ with hle | hle
    · exact abs_sub_le_integral_abs_deriv hf hint ht hθ hle
    · exact (abs_sub_comm (f t) (f θ)).trans_le (abs_sub_le_integral_abs_deriv hf hint hθ ht hle)
  have hftpsi : Integrable (fun θ : ℝ => f t * psi θ) (volume.restrict Iθ) :=
    psi_integrableOn.const_mul (f t)
  have hId : (∫ θ in Iθ, (f t * psi θ - f θ * psi θ)) = f t * (∫ θ in Iθ, psi θ) := by
    rw [MeasureTheory.integral_sub hftpsi hintf, MeasureTheory.integral_const_mul, hzero]
    ring
  have hpt : ∀ θ ∈ Iθ,
      |f t * psi θ - f θ * psi θ| ≤ (∫ θ in Iθ, |deriv f θ|) * psi θ := by
    intro θ hθ
    by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hnn : 0 ≤ psi θ := psi_nonneg hθ
      have habs : |psi θ| = psi θ := abs_of_nonneg hnn
      rw [show f t * psi θ - f θ * psi θ = (f t - f θ) * psi θ by ring, abs_mul, habs]
      exact mul_le_mul_of_nonneg_right (hincr θ hθo) hnn
    · rw [psi_zero_of_not_mem_Ioo hθ hθo]
      simp
  have hchain : |f t| * (1 / 3) ≤ (∫ θ in Iθ, |deriv f θ|) * (1 / 3) := by
    have h13 : |(1 : ℝ) / 3| = 1 / 3 := abs_of_pos (by norm_num)
    have h2 : |∫ θ in Iθ, (f t * psi θ - f θ * psi θ)| = |f t| * (1 / 3) := by
      rw [hId, psi_integral, abs_mul, h13]
    calc |f t| * (1 / 3) = |∫ θ in Iθ, (f t * psi θ - f θ * psi θ)| := h2.symm
      _ ≤ ∫ θ in Iθ, |f t * psi θ - f θ * psi θ| := by
          simpa only [Real.norm_eq_abs] using
            MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
              (f := fun θ : ℝ => f t * psi θ - f θ * psi θ)
      _ ≤ ∫ θ in Iθ, (∫ θ in Iθ, |deriv f θ|) * psi θ := by
          refine MeasureTheory.integral_mono_ae (hftpsi.sub hintf).abs
            (psi_integrableOn.const_mul _) ?_
          exact ae_restrict_of_forall_mem measurableSet_Icc hpt
      _ = (∫ θ in Iθ, |deriv f θ|) * (1 / 3) := by
          rw [MeasureTheory.integral_const_mul, psi_integral]
  nlinarith [hchain]

/-! ## The constrained σ-Poincaré inequality -/

theorem SigmaPoincare : ∃ C : ℝ, 0 < C ∧
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => f θ * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, f θ * Real.sin θ * Real.cos θ ^ 2) = 0 →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal C
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) := by
  -- the weight is integrable with positive mass
  have hSpos : 0 < ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := by
    have h3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ))
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_mono_ae
        (μ := volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
        (f := fun _ : ℝ => (1 : ℝ)) (g := Work.FTS.EllipticEst.sEta)
        (MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
          (C := (1 : ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp))
        (MeasureTheory.IntegrableOn.mono_set sEta_integrableOn_prv
          (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hz : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
      have h := Real.rpow_le_rpow_of_nonpos hpos hle hz
      simpa only [Work.FTS.EllipticEst.sEta, Real.one_rpow] using h
    have h4 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.setIntegral_mono_set (μ := volume)
        (f := Work.FTS.EllipticEst.sEta) (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (t := Iθ)
        sEta_integrableOn_prv ?_ ?_
      · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => sEta_nonneg_prv hx)
      · exact Filter.Eventually.of_forall (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have h5 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one, sub_zero]
    linarith [h3, h4, h5, Real.pi_pos]
  refine ⟨(Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ), ?_, ?_⟩
  · exact mul_pos (by linarith [Real.pi_pos]) hSpos
  · intro f hf hintf hzero
    -- rewrite the statement's integrands using `psi`
    have hintf' : Integrable (fun θ : ℝ => f θ * psi θ) (volume.restrict Iθ) := hintf
    have hzero' : (∫ θ in Iθ, f θ * psi θ) = 0 := by
      have h0 : (∫ θ in Iθ, f θ * psi θ) = ∫ θ in Iθ, f θ * Real.sin θ * Real.cos θ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by
          show f θ * psi θ = f θ * Real.sin θ * Real.cos θ ^ 2
          rw [psi]; ring))
      rw [h0, hzero]
    by_cases hQ : (∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) = ⊤
    · -- the right hand side is `⊤`
      rw [hQ, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
        (mul_pos (by linarith [Real.pi_pos]) hSpos))]
      exact le_top
    · -- the right hand side is finite
      have hmeas : AEStronglyMeasurable (fun θ : ℝ => (deriv f θ) ^ 2)
          (volume.restrict Iθ) :=
        ((measurable_deriv f).pow_const 2).aestronglyMeasurable
      have hnn : 0 ≤ᵐ[volume.restrict Iθ] (fun θ : ℝ => (deriv f θ) ^ 2) :=
        ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg _)
      have hQint : Integrable (fun θ : ℝ => (deriv f θ) ^ 2) (volume.restrict Iθ) :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := volume.restrict Iθ)
          hmeas hnn).mp hQ
      have hQeq : ENNReal.ofReal (∫ θ in Iθ, (deriv f θ) ^ 2)
          = ∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2) :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQint hnn
      -- `|f'|` is integrable
      have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Iθ) := by
        haveI : IsFiniteMeasure (volume.restrict Iθ) :=
          MeasureTheory.isFiniteMeasure_restrict.mpr
            (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        exact MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
      have hmaj : Integrable (fun θ : ℝ => (deriv f θ) ^ 2 + 1) (volume.restrict Iθ) :=
        hQint.add hconst
      have habsint : Integrable (fun θ : ℝ => |deriv f θ|) (volume.restrict Iθ) := by
        refine hmaj.mono'
          (by simpa only [Real.norm_eq_abs] using
            (measurable_deriv f).norm.aestronglyMeasurable) ?_
        exact Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (deriv f x))]
          nlinarith [sq_abs (deriv f x), sq_nonneg (|deriv f x| - 1 / 2)])
      -- Cauchy–Schwarz turns the `L¹` bound into an `L²` bound
      have hA2 : (∫ θ in Iθ, |deriv f θ|) ^ 2
          ≤ (Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2) := by
        have hvol : (∫ θ in Iθ, (1 : ℝ)) = Real.pi / 2 := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
            Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
            smul_eq_mul, mul_one, sub_zero]
        have hu : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Iθ) := by
          haveI : IsFiniteMeasure (volume.restrict Iθ) :=
            MeasureTheory.isFiniteMeasure_restrict.mpr
              (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          exact MeasureTheory.memLp_const (1 : ℝ)
        have hv : MemLp (fun θ : ℝ => |deriv f θ|) 2 (volume.restrict Iθ) := by
          rw [memLp_two_iff_integrable_sq (μ := volume.restrict Iθ)
            (f := fun θ : ℝ => |deriv f θ|)
            (by simpa only [Real.norm_eq_abs] using
              (measurable_deriv f).norm.aestronglyMeasurable)]
          simpa only [sq_abs] using hQint
        have hcs := Work.Spaces.cs_integral (s := Iθ) (u := fun _ : ℝ => (1 : ℝ))
          (v := fun θ : ℝ => |deriv f θ|) hu hv
        simp only [one_mul, one_pow, sq_abs] at hcs
        rw [hvol] at hcs
        exact hcs
      have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |f t| ≤ ∫ θ in Iθ, |deriv f θ| :=
        fun t ht => abs_le_integral_abs_deriv_of_constraint hf habsint hintf' hzero' ht
      -- pointwise comparison of the weighted integrands
      have hpt : ∀ θ ∈ Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
        intro θ hθ
        by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
        · have hSnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_prv hθ
          have hAnn : 0 ≤ ∫ θ in Iθ, |deriv f θ| :=
            MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg (deriv f x))
          have hAnn' : |(∫ θ in Iθ, |deriv f θ|)| = ∫ θ in Iθ, |deriv f θ| :=
            abs_of_nonneg hAnn
          have hft : (f θ) ^ 2 ≤ (∫ θ in Iθ, |deriv f θ|) ^ 2 := by
            refine (sq_le_sq).mpr ?_
            simpa only [hAnn'] using hbound θ hθo
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hft hSnn)
        · have hz : Work.FTS.EllipticEst.sEta θ = 0 := by
            have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
              rcases lt_or_eq_of_le hθ.1 with hlt | heq
              · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt (fun hgt => hθo ⟨hlt, hgt⟩)))
              · exact Or.inl heq.symm
            rcases hcases with h0 | hpi
            · rw [h0, sEta_zero_left]
            · rw [hpi, sEta_zero_right]
          rw [hz, mul_zero, mul_zero]
      have hstep1 : (∫⁻ θ in Iθ, ENNReal.ofReal ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ∫⁻ θ in Iθ,
              ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
                * Work.FTS.EllipticEst.sEta θ) :=
        MeasureTheory.lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hpt)
      have hint2 : Integrable
          (fun θ : ℝ => (∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          (volume.restrict Iθ) :=
        sEta_integrableOn_prv.const_mul _
      have hnn2 : 0 ≤ᵐ[volume.restrict Iθ]
          (fun θ : ℝ => (∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
        ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_prv hθ))
      have hstep2 : (∫⁻ θ in Iθ,
            ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2
              * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint2 hnn2,
          MeasureTheory.integral_const_mul]
      have hSnn : 0 ≤ ∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ := le_of_lt hSpos
      have hkey : (∫ θ in Iθ, |deriv f θ|) ^ 2 * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
          ≤ ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫ θ in Iθ, (deriv f θ) ^ 2) := by
        have h1 : (∫ θ in Iθ, |deriv f θ|) ^ 2 * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
            ≤ ((Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2))
                * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_right hA2 hSnn
        have h2 : ((Real.pi / 2) * (∫ θ in Iθ, (deriv f θ) ^ 2))
              * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ)
            = ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫ θ in Iθ, (deriv f θ) ^ 2) := by ring
        rw [h2] at h1
        exact h1
      have hstep3 : (∫⁻ θ in Iθ,
            ENNReal.ofReal ((∫ θ in Iθ, |deriv f θ|) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          ≤ ENNReal.ofReal ((Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ))
              * (∫⁻ θ in Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)) := by
        have hCnn : 0 ≤ (Real.pi / 2) * (∫ θ in Iθ, Work.FTS.EllipticEst.sEta θ) :=
          mul_nonneg (by linarith [Real.pi_pos]) hSnn
        rw [hstep2, ← hQeq, ← ENNReal.ofReal_mul hCnn]
        exact ENNReal.ofReal_le_ofReal hkey
      exact hstep1.trans hstep3

end

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.L12_tendsto_atTop_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F)(z) → 0` as `z → ∞` for `F ∈ L²(dz dθ)`

The singular part of Elgindi's §'The singular term' is built from the radial integral

  `L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} F(r,θ) K(θ)/r dθ dr`,  `K(θ) = 3 sin θ cos²θ`,

which after the angular integration only involves the angular moment `F_*`:

  `L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr = 3 · L12rad F z`  (`Work.Elliptic.L12_eq_radial`).

The mathematical content of this file is that **the tail integral of an `L²` function tends
to `0`**: the angular moment of `F` satisfies, by Cauchy--Schwarz (`Fstar_sq_le`),

  `|F_*(r)| ≤ √(π/2 · ∫_θ F(r,θ)² dθ)`,

so `|F_*(r)| / r` is dominated by the `L¹(Ioi 1)` function

  `L12Maj F r = (π/2 · ∫_θ F(r,θ)² dθ + r^{-2}) / 2`,

the second term coming from the elementary inequality `√(a)/r ≤ (a + r^{-2})/2` for
`a ≥ 0`, `r ≥ 1`.  Since the tail integrals of an `L¹` function vanish at `∞`
(`MeasureTheory.tendsto_integral_Ioi_zero`), `L₁₂(F)(z) → 0`.

Note that the hypothesis `Work.Spaces.L2Mem F` is used only through the Cauchy--Schwarz
majorant; the *conclusion* is a statement about the tail integrals of an `L¹` function.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular slice of `F` and the majorant of `F_*` -/

/-- The angular `L²` density `∫_θ F(r,θ)² dθ` of `F`, i.e. the `r`-slice of the `L²` norm. -/
def L12slice (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (F r θ) ^ 2

/-- The Cauchy--Schwarz majorant `√(π/2 · ∫_θ F(r,θ)²)` of the angular moment `|F_*|`. -/
def L12maj (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := Real.sqrt (Real.pi / 2 * L12slice F r)

/-- The `L¹(Ioi 1)` majorant of `|F_*(r)|/r`: AM–GM turns `√(π/2 · ∫_θ F²)/r` into
`(π/2 · ∫_θ F² + r^{-2})/2`. -/
def L12Maj (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  (Real.pi / 2 * L12slice F r + r ^ (-2 : ℝ)) / 2

lemma L12slice_nonneg (F : ℝ → ℝ → ℝ) (r : ℝ) : 0 ≤ L12slice F r :=
  integral_nonneg fun _ => sq_nonneg _

/-- `r^{-2} = (r⁻¹)²` for `r > 0`. -/
lemma rpow_neg_two_eq (r : ℝ) (hr : 0 < r) : r ^ (-2 : ℝ) = (r⁻¹) ^ 2 := by
  rw [Real.rpow_neg (le_of_lt hr), Real.rpow_two, inv_pow]

lemma L12Maj_nonneg (F : ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ L12Maj F r := by
  rw [L12Maj]
  exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (L12slice_nonneg F r))
    (Real.rpow_nonneg hr (-2))) (by norm_num)


lemma L12maj_sq (F : ℝ → ℝ → ℝ) (r : ℝ) : (L12maj F r) ^ 2 = Real.pi / 2 * L12slice F r := by
  rw [L12maj, Real.sq_sqrt (mul_nonneg (by positivity) (L12slice_nonneg F r))]

/-! ## The `L¹` properties of the majorant -/

/-- The angular slice of an `L2Mem` function is integrable on `(0,∞)`. -/
lemma integrableOn_L12slice_Ioi (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (L12slice F) (Set.Ioi 0) := by
  have h2 : IntegrableOn (L12slice F) (Set.Ici (0 : ℝ)) := hL2.2
  exact h2.mono_set Set.Ioi_subset_Ici_self

/-- The majorant is integrable on `(1,∞)`: the second term is `x^{-2}` and the first is the
angular slice of `F`, which is integrable by hypothesis. -/
lemma integrableOn_L12Maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (L12Maj F) (Set.Ioi 1) := by
  have hS : IntegrableOn (fun r : ℝ => Real.pi / 2 * L12slice F r) (Set.Ioi 1) :=
    ((integrableOn_L12slice_Ioi F hL2).mono_set (Set.Ioi_subset_Ioi (by norm_num))).const_mul _
  have hp : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hsum : IntegrableOn (fun r : ℝ => Real.pi / 2 * L12slice F r + r ^ (-2 : ℝ))
      (Set.Ioi 1) := hS.add hp
  exact hsum.div_const 2

/-! ## Cauchy--Schwarz for the angular moment, and the pointwise bound -/

/-- Cauchy--Schwarz (`Work.Elliptic.Fstar_sq_le`): `|F_*|` is dominated by `L12maj`. -/
lemma abs_Fstar_le_L12maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar F r| ≤ L12maj F r := by
  have h := Work.Elliptic.Fstar_sq_le F r (hL2.1 r (le_of_lt hr))
  calc |Work.Elliptic.Fstar F r| = Real.sqrt ((Work.Elliptic.Fstar F r) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Real.pi / 2 * L12slice F r) :=
        Real.sqrt_le_sqrt (by simpa [L12slice] using h)
    _ = L12maj F r := by rw [L12maj]

/-- `|F_*(r)|/r ≤ L12Maj F r` on `[1,∞)` (AM–GM applied to `√(π/2 ∫_θ F²)/r`). -/
lemma abs_Fstar_div_le_Maj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {r : ℝ} (hr : 1 ≤ r) :
    |Work.Elliptic.Fstar F r| / r ≤ L12Maj F r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  refine le_trans (div_le_div_of_nonneg_right (abs_Fstar_le_L12maj F hL2 hr0) (le_of_lt hr0)) ?_
  rw [L12Maj, rpow_neg_two_eq r hr0, div_eq_mul_inv, ← L12maj_sq F r]
  nlinarith [sq_nonneg (L12maj F r - r⁻¹)]

/-! ## The tail bound and the limit -/

/-- The radial integral defining `L₁₂` is bounded by the tail integral of the `L¹` majorant:
for `z ≥ 1`,

  `|∫_z^∞ F_*(r)/r dr| ≤ ∫_z^∞ L12Maj F r dr`.

(When `F_*/r` is not integrable the left hand side is `0` by the convention for the
totalised Bochner integral, and the claim is trivial since the majorant is nonnegative.) -/
lemma norm_L12rad_le (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {z : ℝ} (hz : 1 ≤ z) :
    ‖Work.Elliptic.L12rad F z‖ ≤ ∫ r in Set.Ioi z, L12Maj F r := by
  rw [Work.Elliptic.L12rad]
  by_cases hInt : IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi z)
  · refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (MeasureTheory.ae_of_all _ fun r => norm_nonneg _)
      ((integrableOn_L12Maj F hL2).mono_set (Set.Ioi_subset_Ioi hz)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : z < r := hr
    have hr1 : (1 : ℝ) ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    show ‖Work.Elliptic.Fstar F r / r‖ ≤ L12Maj F r
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (le_of_lt hr0)]
    exact abs_Fstar_div_le_Maj F hL2 hr1
  · rw [integral_undef hInt, norm_zero]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : z < r := hr
    exact L12Maj_nonneg F (by linarith)

/-- The tail integrals of the majorant vanish at `∞`. -/
lemma tendsto_tail_L12Maj (F : ℝ → ℝ → ℝ) :
    Filter.Tendsto (fun z : ℝ => ∫ r in Set.Ioi z, L12Maj F r) Filter.atTop
      (nhds (0 : ℝ)) :=
  MeasureTheory.tendsto_integral_Ioi_zero (μ := volume) (f := L12Maj F)
    (b := fun z : ℝ => z) tendsto_id

/-- `L₁₂(F)(z) → 0` as `z → ∞` for `F ∈ L²`: `L₁₂(F) = 3 ∫_z^∞ F_*(r)/r dr`
(`Work.Elliptic.L12_eq_radial`), the integrand is dominated by the `L¹(Ioi 1)` majorant
`L12Maj F` (`abs_Fstar_div_le_Maj`, using `L2Mem F` through `Fstar_sq_le`), and the tail of
an `L¹` function vanishes at `∞`. -/
theorem L12_tendsto_atTop_zero (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    Filter.Tendsto (Work.Elliptic.L12 F) Filter.atTop (nhds (0 : ℝ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun z => 3 * ∫ r in Set.Ioi z, L12Maj F r)
    (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    calc ‖Work.Elliptic.L12 F z‖ = ‖3 * Work.Elliptic.L12rad F z‖ := by
          rw [Work.Elliptic.L12_eq_radial]
      _ = 3 * ‖Work.Elliptic.L12rad F z‖ := by rw [norm_mul]; norm_num
      _ ≤ 3 * ∫ r in Set.Ioi z, L12Maj F r :=
          mul_le_mul_of_nonneg_left (norm_L12rad_le F hL2 hz) (by norm_num)
  · simpa using (tendsto_tail_L12Maj F).const_mul 3

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_moment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open Finset MeasureTheory Set

noncomputable section

namespace Work.FTS.EllipticEst.LevelOneAsm


















end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigLam_ne_of_ne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Injectivity of the angular eigenvalue `λ_n` on `n ≥ 1`

`eigLam n = 4(n-1)² + 10(n-1)` (`EigBasis.eigLamNat`), so on the index range `n ≥ 1`
it is the strictly increasing quadratic `k ↦ 4k² + 10k` evaluated at `k = n - 1`
(`λ_1 = 0 < λ_2 = 14 < λ_3 = 36 < …`).  Hence `λ_n = λ_m` forces `n = m`, which is what
the assembly needs: the eigenvalues of distinct angular modes are distinct.

The hypothesis `1 ≤ n` is essential: `eigLam 0 = eigLam 1 = 0` (because `0 - 1 = 0` in
`ℕ`), so `eigLam` is not injective on all of `ℕ`.
-/

namespace Work.FTS.EllipticEst.LevelOneAsm





end Work.FTS.EllipticEst.LevelOneAsm
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigPoly_spans_odd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

/-! ### The leading coefficient of the eigenpolynomial -/


/-! ### Two elementary facts about `eigPoly` -/



/-! ### The span predicate -/

/-- `OddSpan N p` says that the function `p` is a finite linear combination
`Σ_{k<N} a_k · p_{k+1}` of the first `N` eigenpolynomials. -/
def OddSpan (N : ℕ) (p : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ u : ℝ, p u = ∑ k ∈ Finset.range N, a k * eigPoly (k + 1) u

namespace OddSpan

protected lemma zero (N : ℕ) : OddSpan N (fun _ : ℝ => 0) :=
  ⟨fun _ => 0, fun u => by simp⟩

/-- Transport along a pointwise equal function. -/
protected lemma congr {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (h : ∀ u : ℝ, q u = p u) :
    OddSpan N q := by
  obtain ⟨a, ha⟩ := hp
  exact ⟨a, fun u => by rw [h u]; exact ha u⟩

protected lemma add {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (hq : OddSpan N q) :
    OddSpan N (fun u => p u + q u) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  refine ⟨fun k => a k + b k, fun u => ?_⟩
  show p u + q u = ∑ k ∈ Finset.range N, (a k + b k) * eigPoly (k + 1) u
  rw [ha u, hb u, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

protected lemma smul {N : ℕ} {p : ℝ → ℝ} (hp : OddSpan N p) (c : ℝ) :
    OddSpan N (fun u => c * p u) := by
  obtain ⟨a, ha⟩ := hp
  refine ⟨fun k => c * a k, fun u => ?_⟩
  show c * p u = ∑ k ∈ Finset.range N, (c * a k) * eigPoly (k + 1) u
  rw [ha u, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

protected lemma sub {N : ℕ} {p q : ℝ → ℝ} (hp : OddSpan N p) (hq : OddSpan N q) :
    OddSpan N (fun u => p u - q u) := by
  have h := hp.add (hq.smul (-1))
  exact h.congr (fun u => by ring)

/-- `OddSpan` is closed under finite sums. -/
protected lemma sum {N : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, OddSpan N (f i)) : OddSpan N (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using OddSpan.zero N
  | insert i s hi ih =>
      have h1 : OddSpan N (f i) := h i (Finset.mem_insert_self i s)
      have h2 : OddSpan N (fun u => ∑ j ∈ s, f j u) :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      refine (h1.add h2).congr (fun u => ?_)
      exact Finset.sum_insert hi

/-- A single eigenpolynomial `p_{k+1}` with `k < N` lies in the span. -/
protected lemma eigPoly {N k : ℕ} (hk : k < N) : OddSpan N (eigPoly (k+1)) := by
  refine ⟨fun j => if j = k then 1 else 0, fun u => ?_⟩
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjne; simp [hjne]
  · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot

/-- The span grows with `N`. -/
protected lemma mono {N M : ℕ} (hNM : N ≤ M) {p : ℝ → ℝ} (hp : OddSpan N p) :
    OddSpan M p := by
  obtain ⟨a, ha⟩ := hp
  refine ⟨fun j => if j < N then a j else 0, fun u => ?_⟩
  rw [ha u]
  have h1 : (∑ x ∈ Finset.range N, (if x < N then a x else 0) * eigPoly (x+1) u)
      = ∑ x ∈ Finset.range N, a x * eigPoly (x+1) u := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp [Finset.mem_range.mp hx]
  have h2 : (∑ x ∈ Finset.range N, (if x < N then a x else 0) * eigPoly (x+1) u)
      = ∑ x ∈ Finset.range M, (if x < N then a x else 0) * eigPoly (x+1) u := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr hNM) (fun x _ hxN => ?_)
    have hxN' : ¬ (x < N) := by simpa [Finset.mem_range] using hxN
    rw [ite_eq_right hxN', zero_mul]
  rw [← h1, h2]

end OddSpan

/-! ### The triangular induction -/



end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Lop_sin_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- `L (sin(2θ) · h) = sin(2θ) · (2 cos(2θ) h + sin(2θ) h')` at every point where `h`
is differentiable. -/
theorem Lop_sin_mul (h : ℝ → ℝ) (θ : ℝ) (hh : DifferentiableAt ℝ h θ) :
    Work.Spaces.Lop (fun θ : ℝ => Real.sin (2 * θ) * h θ) θ
      = Real.sin (2 * θ) * (2 * Real.cos (2 * θ) * h θ
          + Real.sin (2 * θ) * deriv h θ) := by
  have hsin : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
  have hfun : (fun θ : ℝ => Real.sin (2 * θ) * h θ)
      = (fun t : ℝ => Real.sin (2 * t)) * h := rfl
  rw [hfun, Work.Spaces.Lop_mul _ _ θ hsin hh]
  have hd : deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm] using h.deriv
  simp only [Work.Spaces.Lop, hd]
  ring

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroAux.sin_mul_integrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LzeroAux


end Work.FTS.EllipticEst.LzeroAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingAuxDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst







end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingWronskian =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst



end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.sinCos2_cs_sEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Weighted Cauchy–Schwarz for the angular moment `∫_θ |u|·sinθcos²θ`

The angular profile of the elliptic problem is `sinCos2 θ = sinθ·cos²θ` and the `i = 0`
angular weight is `sEta θ = sin(2θ)^{-η}` with `η = 99/100` (`Work.Spaces.Iθ = [0,π/2]`).

This file proves `sinCos2_cs_sEta`: for `u` whose weighted square `u²·sEta` is integrable on
`Iθ` and which is a.e. strongly measurable,

* `sinCos2²/sEta` is integrable on `Iθ` with nonnegative integral (it is bounded by `1`: on
  `(0,π/2)` it equals `sinCos2²·sin(2θ)^η ≤ 1`, and the two endpoints are null);
* `|u|·sinCos2` is integrable on `Iθ`;
* `(∫_θ |u|·sinCos2)² ≤ (∫_θ sinCos2²/sEta)·(∫_θ u²·sEta)`,

the last being the sharp weighted Cauchy–Schwarz inequality with the two `L²` factors
`√(u²·sEta)` and `√(sinCos2²/sEta)` (their product is `|u|·sinCos2`, since `sinCos2 ≥ 0` on
`Iθ` and `sEta > 0` on the open interval, which is co-null in `Iθ`).

Everything reduces to the open interval `(0,π/2)` through the equality of the restrictions
of Lebesgue measure, because there `sEta` is strictly positive.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts on the open interval and on `Iθ` -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sEta θ ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- `sEta θ > 0` on the open interval. -/
private theorem sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

/-- On the open interval, the reciprocal of `sEta θ` is `sin(2θ)^η`. -/
private theorem inv_sEta_eq_rpow_of_mem_Ioo {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)), inv_inv]

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private theorem sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
    (sq_nonneg _)

/-- On the open interval, `sinCos2²/sEta = sinCos2²·sin(2θ)^η`. -/
private theorem sinCos2_sq_div_sEta_eq_mul_rpow {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ
      = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  rw [div_eq_mul_inv, inv_sEta_eq_rpow_of_mem_Ioo hθ]

/-- The open interval `(0,π/2)` and `Iθ = [0,π/2]` carry the same restriction of Lebesgue
measure: they differ by the two null points `0` and `π/2`. -/
private theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2_fts : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop

/-- `θ ↦ sinCos2 θ²·sin(2θ)^η` is continuous on `Iθ` (where `η ≥ 0`). -/
private theorem continuousOn_sinCos2_sq_mul_rpow_Iθ :
    ContinuousOn (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) Work.Spaces.Iθ := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Work.Spaces.Iθ :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      Work.Spaces.Iθ :=
    hsin.rpow_const (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))
  exact ((continuous_sinCos2_fts.pow 2).continuousOn).mul hrpow

/-- `|sinCos2 θ²·sin(2θ)^η| ≤ 1` on the open interval. -/
private theorem abs_sinCos2_sq_mul_rpow_le_one {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ‖(Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hrpow_le : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) hs1 (by norm_num [Work.Spaces.eta])
  have hcabs : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    have ha : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hb : Real.cos θ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul ha hb (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  have hcsq : |(Work.Elliptic.sinCos2 θ) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr hcabs
  have hrpow_abs : |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 := by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) _)]
    exact hrpow_le
  calc |(Work.Elliptic.sinCos2 θ) ^ 2| * |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 * 1 :=
        mul_le_mul hcsq hrpow_abs (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-! ## Integrability of the `sinCos2²/sEta` factor -/

/-- `sinCos2²/sEta` is integrable on `Iθ`. -/
private theorem integrableOn_sinCos2_sq_div_sEta :
    IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hFin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  -- the auxiliary continuous function `sinCos2²·sin(2θ)^η`
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) (volume.restrict Work.Spaces.Iθ) :=
    continuousOn_sinCos2_sq_mul_rpow_Iθ.aestronglyMeasurable hIθ_meas
  have hint : Integrable (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.of_bound haesm 1 ?_
    filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [show (Work.Elliptic.sinCos2 0) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.sin_zero]; ring]
      simp
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      rw [show (Work.Elliptic.sinCos2 (Real.pi / 2)) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.cos_pi_div_two]; ring]
      simp
    · exact abs_sinCos2_sq_mul_rpow_le_one ⟨h0, h1⟩
  -- transfer to `sinCos2²/sEta`, equal a.e. (and everywhere on the open interval)
  refine hint.congr ?_
  filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [show (Work.Elliptic.sinCos2 0) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.sin_zero]; ring,
      show Work.FTS.EllipticEst.sEta 0 = 0 from by
        rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
          Real.zero_rpow (by norm_num [Work.Spaces.eta])]]
    simp
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    rw [show (Work.Elliptic.sinCos2 (Real.pi / 2)) = 0 from by
      rw [Work.Elliptic.sinCos2, Real.cos_pi_div_two]; ring]
    simp
  · exact (sinCos2_sq_div_sEta_eq_mul_rpow ⟨h0, h1⟩).symm

/-! ## The a.e. factorisation of the integrand -/

/-- The product of the two `L²` factors `√(u²·sEta)` and `√(sinCos2²/sEta)` is `|u|·sinCos2`
a.e. on `Iθ` (on the open interval `sEta > 0` and `sinCos2 ≥ 0`). -/
private theorem ae_sqrt_prod_eq_abs_mul {u : ℝ → ℝ} :
    (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  beta_reduce
  have hs : 0 < Work.FTS.EllipticEst.sEta θ := sEta_pos_of_mem_Ioo hθ
  have hu2 : 0 ≤ (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_nonneg (sq_nonneg _) hs.le
  have hc : 0 ≤ Work.Elliptic.sinCos2 θ :=
    sinCos2_nonneg_of_mem_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [← Real.sqrt_mul hu2]
  have hmul : (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      * ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      = (u θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
    field_simp
  rw [hmul, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hc]

/-! ## The main estimate -/

theorem sinCos2_cs_sEta {u : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hmeasu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
      ∧ 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ
      ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
            * ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- a.e. nonnegativity of the two `L²` squares
  have hnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    (ae_restrict_mem hIθ_meas).mono
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hnnC : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    (ae_restrict_mem hIθ_meas).mono
      (fun θ hθ => div_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  -- ## the first `L²` factor `√(u²·sEta)`
  have hA_mem : MemLp (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hu.aestronglyMeasurable
    · exact hu.congr (hnn.mono (fun θ hθ => (Real.sq_sqrt hθ).symm))
  -- ## the second `L²` factor `√(sinCos2²/sEta)`
  have hDiv_aesm : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ((continuousOn_sinCos2_sq_mul_rpow_Iθ.mono
      (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).aestronglyMeasurable
        measurableSet_Ioo).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => (sinCos2_sq_div_sEta_eq_mul_rpow hθ).symm)
  have hB_mem : MemLp
      (fun θ : ℝ => Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hDiv_aesm
    · exact (integrableOn_sinCos2_sq_div_sEta).congr
        (hnnC.mono (fun θ hθ => (Real.sq_sqrt hθ).symm))
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral hA_mem hB_mem
  have e1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      = ∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ :=
    integral_congr_ae ae_sqrt_prod_eq_abs_mul
  have e2 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    integral_congr_ae (hnn.mono (fun θ hθ => Real.sq_sqrt hθ))
  have e3 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    integral_congr_ae (hnnC.mono (fun θ hθ => Real.sq_sqrt hθ))
  have hmain : (∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
        * ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    rw [e1, e2, e3] at hcs
    rw [mul_comm (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)] at hcs
    exact hcs
  -- ## integrability of the moment integrand
  have hProd : Integrable (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iθ) := hA_mem.integrable_mul hB_mem
  have hAbsInt : IntegrableOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := hProd.congr ae_sqrt_prod_eq_abs_mul
  have hCnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    integral_nonneg_of_ae hnnC
  exact ⟨integrableOn_sinCos2_sq_div_sEta, hCnonneg, hAbsInt, hmain⟩

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped ContDiff Real Topology
open Filter

namespace Work.FTS.EllipticEst.RPFresh.DivSinOpen

/-- The finite order `C^n` as an element of the differentiability order type `ℕ∞ω`. -/
abbrev LopOrd (n : ℕ) : ℕ∞ω := ((n : ℕ) : ℕ∞ω)

/-- The order `n + 1` is the successor of the order `n`. -/
lemma LopOrd_succ (n : ℕ) : LopOrd (n + 1) = LopOrd n + 1 := by
  simp only [LopOrd]; push_cast; ring


/-- A positive finite order is a positive element of `ℕ∞ω`. -/
lemma LopOrd_pos {n : ℕ} (h : 0 < n) : 0 < LopOrd n := by
  simp only [LopOrd]; exact_mod_cast h

/-- A positive finite order is nonzero in `ℕ∞ω`. -/
lemma LopOrd_ne_zero_of_pos {n : ℕ} (h : 0 < n) : LopOrd n ≠ 0 :=
  ne_of_gt (LopOrd_pos h)

/-- Every finite order is strictly below the smooth order `∞` (`= ↑⊤ : ℕ∞`). -/
lemma LopOrd_lt_omega (n : ℕ) : LopOrd n < ∞ := by
  rw [show ∞ = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  simp only [LopOrd]
  exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)

/-- Applying `Lop = sin(2·) ∂` costs exactly one order of pointwise differentiability. -/
lemma Lop_contDiffAt (n : ℕ) {u : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ (LopOrd (n + 1)) u θ) :
    ContDiffAt ℝ (LopOrd n) (Work.Spaces.Lop u) θ := by
  have hd : ContDiffAt ℝ (LopOrd n) (deriv u) θ :=
    hu.derivWithin (le_of_eq (LopOrd_succ n).symm)
  have hsin : ContDiffAt ℝ (LopOrd n) (fun θ : ℝ => Real.sin (2 * θ)) θ := by
    have h : ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
    exact h.of_le le_top
  have heq : Work.Spaces.Lop u = (fun θ : ℝ => Real.sin (2 * θ)) * deriv u := rfl
  rw [heq]
  exact hsin.mul hd

/-- Iterating `Lop` costs one order of regularity per application: if `u` is `C^k` at `θ`
then `Lop^[a] u` is `C^{k-a}` at `θ` (for `a ≤ k`). -/
lemma Lop_iter_contDiffAt (a k : ℕ) (hak : a ≤ k) {u : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ (LopOrd k) u θ) :
    ContDiffAt ℝ (LopOrd (k - a)) (Work.Spaces.Lop^[a] u) θ := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
      have hak' : a ≤ k := le_trans (Nat.le_succ a) hak
      have hprev : ContDiffAt ℝ (LopOrd (k - a)) (Work.Spaces.Lop^[a] u) θ := ih hak'
      have hsucc : ContDiffAt ℝ (LopOrd (k - (a + 1) + 1)) (Work.Spaces.Lop^[a] u) θ := by
        have : k - (a + 1) + 1 = k - a := by omega
        rw [this]; exact hprev
      have hmain := Lop_contDiffAt (k - (a + 1)) hsucc
      rw [Function.iterate_succ_apply']
      exact hmain

/-- **Leibniz rule for iterates of `Lop`, finite order.**  On an open set `U` where `u` and
`v` are `C^j`, the `j`-th iterate of `Lop` applied to the pointwise product agrees on `U`
with the binomial convolution.  Unlike `Work.Spaces.Lop_iter_mul_eqOn` the regularity
hypothesis is of order `j`, not `⊤`: one order is spent at each induction step, exactly the
amount needed to differentiate the level-`(j-1)` identity and the individual summands. -/
theorem Lop_iter_mul_eqOn_fin : ∀ (j : ℕ) (k : ℕ) (u v : ℝ → ℝ) (U : Set ℝ), IsOpen U →
    ContDiffOn ℝ (LopOrd k) u U → ContDiffOn ℝ (LopOrd k) v U → j ≤ k →
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  intro j
  induction j with
  | zero =>
      intro k u v U hU hu hv hjk θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro k u v U hU hu hv hjk θ hθ
      have ihfun := ih k u v U hU hu hv (by omega)
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (ihfun.deriv hU) hθ
      have hdu : ∀ a ≤ j, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
        intro a haj
        exact (Lop_iter_contDiffAt a k (by omega)
          (hu.contDiffAt (hU.mem_nhds hθ))).differentiableAt
            (LopOrd_ne_zero_of_pos (by omega))
      have hdv : ∀ b ≤ j, DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := by
        intro b hbj
        exact (Lop_iter_contDiffAt b k (by omega)
          (hv.contDiffAt (hU.mem_nhds hθ))).differentiableAt
            (LopOrd_ne_zero_of_pos (by omega))
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact ((hdu a haj).mul (hdv (j - a) (by omega))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [Function.iterate_succ_apply', hkey]
      rw [Finset.sum_congr rfl
        (fun a ha => Work.Spaces.sin_deriv_term u v θ j a
          (hdu a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hdv (j - a) (by omega)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

theorem LopLeibnizPoint (k : ℕ) {u v : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) u θ)
    (hv : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) v θ) :
    Work.Spaces.Lop^[k] (u * v) θ
      = ∑ a ∈ Finset.range (k + 1),
          (k.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[k - a] v θ) := by
  -- pass to an open neighbourhood on which `u` and `v` are of class `C^k`
  obtain ⟨s, hs, hsu⟩ := hu.contDiffOn (le_refl (LopOrd k))
    (fun h => absurd h (ne_of_lt (LopOrd_lt_omega k)))
  obtain ⟨t, ht, htv⟩ := hv.contDiffOn (le_refl (LopOrd k))
    (fun h => absurd h (ne_of_lt (LopOrd_lt_omega k)))
  obtain ⟨W, hWst, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hs ht)
  exact Lop_iter_mul_eqOn_fin k k u v W hWopen (hsu.mono (fun x hx => (hWst hx).1))
    (htv.mono (fun x hx => (hWst hx).2)) le_rfl hθW

end Work.FTS.EllipticEst.RPFresh.DivSinOpen
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Dth1Iter_mul_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- `Work.Elliptic.Dth1Iter` is the `n`-fold iterate of the derivation
`Work.Spaces.Lop` — the two operators are the same function `θ ↦ sin(2θ)·f'(θ)`. -/
private lemma Dth1Iter_eq_Lop_iter (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.Dth1Iter_succ, Function.iterate_succ_apply', ih]
      rfl

/-- The iterated Leibniz rule for `Work.Elliptic.Dth1Iter` at a point of the
smoothness interval: the `m`-th iterate applied to a pointwise product expands
into the binomial convolution. -/
private lemma Dth1Iter_mul_eq (m : ℕ) {F G : ℝ → ℝ} (hF : Work.Elliptic.SmoothSlice F)
    (hG : Work.Elliptic.SmoothSlice G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    Work.Elliptic.Dth1Iter m (fun θ => F θ * G θ) θ =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) *
          (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ) := by
  have hleib := Work.Spaces.Lop_iter_mul_eqOn F G (Set.Ioo (-1) (Real.pi / 2 + 1))
    isOpen_Ioo hF hG m hθ
  rw [Dth1Iter_eq_Lop_iter]
  refine hleib.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [← Dth1Iter_eq_Lop_iter j F, ← Dth1Iter_eq_Lop_iter (m - j) G]

/-- Pointwise `L²`-type bound for the iterate of `D_θ` on a product: the square of
`Dth1Iter m (F·G)` at `θ` is controlled by the Cauchy–Schwarz sum of the squares of
the Leibniz terms. -/
theorem Dth1Iter_mul_sq_le (m : ℕ) {F G : ℝ → ℝ}
    (hF : Work.Elliptic.SmoothSlice F) (hG : Work.Elliptic.SmoothSlice G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    (Work.Elliptic.Dth1Iter m (fun θ => F θ * G θ) θ) ^ 2
      ≤ (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ)) ^ 2 * ((Work.Elliptic.Dth1Iter j F θ) ^ 2
            * (Work.Elliptic.Dth1Iter (m - j) G θ) ^ 2) := by
  rw [Dth1Iter_mul_eq m hF hG hθ]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
    (f := fun j => (m.choose j : ℝ) *
      (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ))
  have hcard : (((Finset.range (m + 1)).card : ℕ) : ℝ) = (m + 1 : ℝ) := by
    rw [Finset.card_range]
    norm_num
  calc (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2
      ≤ (((Finset.range (m + 1)).card : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) *
            (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2 := hcs
    _ = (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) *
            (Work.Elliptic.Dth1Iter j F θ * Work.Elliptic.Dth1Iter (m - j) G θ)) ^ 2 := by
          rw [hcard]
    _ = (m + 1 : ℝ) * ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
            ((Work.Elliptic.Dth1Iter j F θ) ^ 2
              * (Work.Elliptic.Dth1Iter (m - j) G θ) ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- `D2 u = u''`, the second derivative of the one-variable function `u`.  It is definitionally
the function whose `Ptheta` is the second summand of the statement of `slice_coercive`. -/
def D2 (u : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun t => deriv u t) θ


/-- `Fη u = ∫_θ (Lzero1 u)² sin(2θ)^{-η}`, the `η`-weighted energy of `Lzero1 u`. -/
def Fη (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Lzero1 u θ) ^ 2 * sEta θ





/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `sEta θ ≥ 0` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- `sGam α θ ≥ 0` on `Iθ`. -/
theorem sGam_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sGam α θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open Set

/-- Lagrange mean-value bound on an interval: if `u` is continuous on `[a, b]`, differentiable
on `(a, b)` and `|u'| ≤ M` on `(a, b)`, then `|u b - u a| ≤ (b - a) · M`.  No sign hypothesis on
`M` is needed: when `a = b` both sides vanish, and when `a < b` the mean value theorem gives a
point `c` with `u b - u a = (b - a) · u' c`, so the bound follows from `b - a > 0`. -/
private lemma abs_sub_le_mul_of_deriv_bound {u : ℝ → ℝ} {M a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b)) (hdiff : DifferentiableOn ℝ u (Set.Ioo a b))
    (hbd : ∀ x ∈ Set.Ioo a b, |deriv u x| ≤ M) :
    |u b - u a| ≤ (b - a) * M := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- Lagrange mean value theorem on `[a, b]`.
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt hcont hdiff
    have hcb : 0 < b - a := sub_pos.mpr hlt
    have h2 : u b - u a = (b - a) * deriv u c := by rw [hcd]; field_simp
    rw [h2, abs_mul, abs_of_pos hcb]
    exact mul_le_mul_of_nonneg_left (hbd c hc) (le_of_lt hcb)
  · -- Degenerate interval: `a = b`.
    rw [heq]; simp

/-- Two mean-value bounds for a Dirichlet slice: if `u` is differentiable on the open interval
`(0, π/2)`, continuous on `[0, π/2]`, vanishes at both endpoints, and `|u'| ≤ M` on `(0, π/2)`,
then `|u θ| ≤ θ·M` and `|u θ| ≤ (π/2 - θ)·M` for every `θ ∈ [0, π/2]`.  Declaration to be placed
in namespace `Work.FTS.EllipticEst` (module
`Submission.Work.FTS.EllipticEst.absLeMulOfDerivBoundOpen`).

Route: `exists_deriv_eq_slope` on `[0, θ]` (resp. `[θ, π/2]`) for `0 < θ < π/2` gives
`ξ` with `deriv u ξ = (u θ - u 0)/θ` (resp. `= (u (π/2) - u θ)/(π/2 - θ)`); combine with
`h0`, `h1`, `hbd`.  Note `0 ≤ M` follows from `hbd` at any interior point.  The endpoints
`θ = 0, π/2` are immediate from `h0`, `h1`. -/
theorem absLeMulOfDerivBoundOpen {u : ℝ → ℝ} {M : ℝ}
    (hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |deriv u x| ≤ M) :
    (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |u θ| ≤ θ * M) ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |u θ| ≤ (Real.pi / 2 - θ) * M) := by
  constructor
  · -- The left half of the interval: apply the mean-value bound on `[0, θ]`.
    intro θ hθ
    have key := abs_sub_le_mul_of_deriv_bound (u := u) (M := M) hθ.1
      (hcont.mono (Set.Icc_subset_Icc le_rfl hθ.2))
      (hdiff.mono (Set.Ioo_subset_Ioo le_rfl hθ.2))
      (fun x hx => hbd x (Set.Ioo_subset_Ioo le_rfl hθ.2 hx))
    rw [h0, sub_zero] at key
    simpa using key
  · -- The right half of the interval: apply the mean-value bound on `[θ, π/2]`.
    intro θ hθ
    have key := abs_sub_le_mul_of_deriv_bound (u := u) (M := M) hθ.2
      (hcont.mono (Set.Icc_subset_Icc hθ.1 le_rfl))
      (hdiff.mono (Set.Ioo_subset_Ioo hθ.1 le_rfl))
      (fun x hx => hbd x (Set.Ioo_subset_Ioo hθ.1 le_rfl hx))
    rw [h1, zero_sub, abs_neg] at key
    exact key

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ang_integrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The three elementary angular integrals

The set `Work.Spaces.Iθ` is `Set.Icc 0 (π/2)`, which differs from the interval `0..π/2` by the
null set `{0}` only; we first evaluate everything as an interval integral and transfer at the end.

The evaluations are

* `∫_0^{π/2} sin²(2θ) dθ = π/4`, via `sin²(2θ) = 4 sin²θ cos²θ` and
  `∫_0^{π/2} sin²θ cos²θ = (π/2)/8 = π/16`;
* `∫_0^{π/2} sin²θ cos⁴θ dθ = π/32`, via `sin²θ cos⁴θ = (1/8) sin²(2θ) (1 + cos 2θ)` together with
  the first evaluation and `∫_0^{π/2} sin²(2θ) cos(2θ) dθ = 0`;
* `∫_0^{π/2} sin θ cos²θ · sin(2θ) dθ = 4/15`, the substitution `u = sin θ`
  (`Work.Elliptic.integral_sin_two_mul_sinCos2`). -/

/-- A set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
private lemma setIntegral_Iθ_eq (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- `∫_0^{π/2} sin²(2θ) dθ = π/4`. -/
private lemma integral_sin_two_sq_pi2 :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2) = Real.pi / 4 := by
  have hpt : ∀ θ : ℝ, (Real.sin (2 * θ)) ^ 2 = 4 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) := by
    intro θ; rw [Real.sin_two_mul]; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_cos_sq]
  rw [show (4 : ℝ) * (π / 2) = 2 * π by ring, show (4 : ℝ) * 0 = 0 by ring]
  simp
  ring

/-- `∫_0^{π/2} sin²(2θ) cos(2θ) dθ = 0`: substitute `u = 2θ` and use
`∫_0^π sin²u cos u du = (sin³π - sin³0)/3 = 0`. -/
private lemma integral_sin_two_sq_mul_cos_two :
    (∫ θ in (0 : ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => Real.sin u ^ 2 * Real.cos u) (c := 2) (by norm_num)]
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * (π / 2) = π by ring]
  rw [integral_sin_sq_mul_cos]
  simp

/-- `∫_0^{π/2} sin²θ cos⁴θ dθ = π/32`. -/
private lemma integral_sinCos2_sq_pi2 :
    (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2) = Real.pi / 32 := by
  have hpt : ∀ θ : ℝ, (Work.Elliptic.sinCos2 θ) ^ 2
      = (1 / 8) * ((Real.sin (2 * θ)) ^ 2 + (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) := by
    intro θ
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul, Real.cos_two_mul]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)).intervalIntegrable _ _),
    integral_sin_two_sq_pi2, integral_sin_two_sq_mul_cos_two]
  ring

/-- The elementary angular integrals and the numerical inequality used by the Cauchy–Schwarz
bound on the first sine coefficient of a function orthogonal to `sinθcos²θ`
(`∫ sin²2θ = π/4`, `∫ sin²θcos⁴θ = π/32`, `∫ sinθcos²θ sin2θ = 4/15`, and
`π/32 - (4/15)²/(π/4) ≤ (1/4)(π/32)`, i.e. `675 π² ≤ 8192`). -/
theorem ang_integrals :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ 2) = Real.pi / 4 ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) = Real.pi / 32 ∧
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ)) = 4 / 15 ∧
    ((Real.pi / 32 : ℝ) - (4 / 15) ^ 2 / (Real.pi / 4) ≤ (1 / 4) * (Real.pi / 32)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [setIntegral_Iθ_eq]; exact integral_sin_two_sq_pi2
  · rw [setIntegral_Iθ_eq]; exact integral_sinCos2_sq_pi2
  · rw [← Work.Elliptic.integral_sin_two_mul_sinCos2]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
  · -- `π/32 - (4/15)²/(π/4) ≤ (1/4)(π/32)` is `675 π² ≤ 8192`, and `π < 3.15`.
    have hp : (0 : ℝ) < Real.pi := Real.pi_pos
    have key : (675 : ℝ) * Real.pi ^ 2 ≤ 8192 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h2 : (1 : ℝ) / 4 * (Real.pi / 32) - (Real.pi / 32 - (4 / 15) ^ 2 / (Real.pi / 4))
        = (8192 - 675 * Real.pi ^ 2) / (28800 * Real.pi) := by
      field_simp
      ring
    have h3 : (0 : ℝ) ≤ (1 : ℝ) / 4 * (Real.pi / 32)
        - (Real.pi / 32 - (4 / 15) ^ 2 / (Real.pi / 4)) := by
      rw [h2]
      exact div_nonneg (by linarith [key]) (by positivity)
    linarith [h3]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Integrability transfer on the angular slice: if `g` is continuous on the open interval
`(0, π/2)` and `g²·sin(2θ)^{-η}` is integrable on `Iθ = [0, π/2]`, then `|g|` is integrable on
`Iθ`.  Declaration to be placed in namespace `Work.FTS.EllipticEst` (module
`Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta`).

Route: `1 ≤ sEta θ` for `θ ∈ (0, π/2)` (`η = 99/100 > 0`, `0 < sin(2θ) ≤ 1`, so
`Real.rpow_le_rpow_of_exponent_ge` gives `sin(2θ)^{-η} ≤ sin(2θ)^0 = 1`), and the endpoints are
a null set, so `g² ≤ g²·sEta` a.e. on `Iθ` — hence `g²` is integrable on `Iθ`
(`Integrable.mono'`, with `AEStronglyMeasurable` of `g²` from
`hg.aestronglyMeasurable measurableSet_Ioo` transferred across the a.e.-equal sets
`Iθ =ᵐ Ioo 0 (π/2)`, e.g. via `Measure.restrict_congr_set` as in `slice_cs_weighted`), and
finally `|g| ≤ g² + 1` pointwise with `g² + 1` integrable on the finite measure space `Iθ`. -/
theorem integrableAbsOfSqSeta {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |g θ|) Work.Spaces.Iθ := by
  -- ## Step 0: the two endpoints `{0, π/2}` are a null set, so `Iθ = [0,π/2]` agrees with the
  -- open interval `(0, π/2)` almost everywhere, and the integrals coincide.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
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
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  have hint' : MeasureTheory.Integrable
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact hint
  -- ## Step 1: on `(0, π/2)` the weight satisfies `1 ≤ sEta`, so `g² ≤ g² · sEta` a.e.
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsaesm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint'.mono' (MeasureTheory.AEStronglyMeasurable.pow hsaesm 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      have h0 : 0 < Real.sin (2 * θ) := hsinpos θ hθ
      have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
        (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
      simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- ## Step 2: `|g| ≤ g² + 1` pointwise, and `g² + 1` is integrable (the slice has finite
  -- measure), so `|g|` is integrable on `(0, π/2)`.
  have habs_int : MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
    refine hmaj.mono' hsaesm.norm ?_
    filter_upwards with θ
    have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
    simpa only [Real.norm_eq_abs, abs_abs] using h1
  -- ## Step 3: transfer back to `Iθ`, which is `(0, π/2)` a.e.
  change MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hms]; exact habs_int

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.memLp_Lzero_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L²`-membership of the slice `θ ↦ a θ`, `θ ↦ a'θ` and `θ ↦ L₀(a)(0,θ)`

The elliptic estimates of §'Elliptic Regularity Estimates' of Elgindi's paper use the
angular operator `L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (see `Work.Elliptic.Lzero`).
When it is applied to a function which does not depend on `z`, the slice
`θ ↦ L₀(fun _ θ' => a θ') 0 θ` is a purely one dimensional expression in `a`; this file
proves that under the standing regularity assumption `a ∈ C²([0, π/2])` together with a
bound on `L₀ a` on the open interval, the three functions `a`, `a'` and `L₀ a` all belong
to `L²(Iθ)`, `Iθ = [0, π/2]`.

This is the `L²`-part of the hypothesis needed to make sense of the coercivity estimate
`∫_{Iθ} (a² + (a')²) ≤ (10/9) ∫_{Iθ} (L₀a)²` (see `Work.FTS.EllipticEst.Lzero_slice_coercive`),
which requires the three `L²`-integrals to be honest numbers rather than junk values.

The proofs are elementary: `volume.restrict Iθ` is a finite measure, so it suffices to
bound the functions almost everywhere on `Iθ`; the only subtlety is that the relevant
bounds are known on the *open* interval, the two endpoints `0` and `π/2` being null sets.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.style.haveILetI false

namespace Work.FTS.EllipticEst

/-- A property which holds on the open interval `(0, π/2)` holds almost everywhere for the
restriction of Lebesgue measure to `Iθ = [0, π/2]`: the only points lost are the two
endpoints `0` and `π/2`, a null set. -/
lemma ae_restrict_Iθ_of_Ioo_memLp {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))), p θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  suffices hsub : {x : ℝ | ¬(x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → p x)}
      ⊆ ({0, Real.pi / 2} : Set ℝ) by
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq, measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton _⟩
  intro x hx
  simp only [Set.mem_ofPred_eq, not_imp] at hx
  by_contra hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
  exact hx.2 (h x ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hc.1), lt_of_le_of_ne hx.1.2 hc.2⟩)




end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.deriv_tan_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux


end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.dthIter_abs_le_pthIter_sum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux

open scoped Real

/-- Reindexing helper: a `range (m+2)`-sum whose `0`-th term vanishes can be written as a
sum over `Icc 1 (m+1)`. -/
theorem sum_range_succ_eq_sum_Icc (m : ℕ) (g : ℕ → ℝ) (h0 : g 0 = 0) :
    ∑ r ∈ Finset.range (m + 2), g r = ∑ r ∈ Finset.Icc 1 (m + 1), g r := by
  have hset : Finset.Ico 1 (m + 2) = Finset.Icc 1 (m + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hIco : ∑ k ∈ Finset.Ico 1 (m + 2), g k = ∑ k ∈ Finset.range (m + 1), g (k + 1) := by
    rw [Finset.sum_Ico_eq_sum_range g 1 (m + 2)]
    have hsub : m + 2 - 1 = m + 1 := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  rw [Finset.sum_range_succ' g (m + 1), h0, add_zero, ← hIco, hset]


end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Iterated form of the slice ODE `Lzero1 u = g`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so the relation `g = Lzero1 u` on `(0, π/2)` is the
second order ODE `u'' = ∂_θ(tan θ · u) - 6u - g`.  Differentiating it `k` times and using the
Leibniz rule for the product `tan · u` gives the stated expansion

`u^{(k+2)} = ∑_{i=0}^{k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`

at every point of `(0, π/2)`. -/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

theorem Lzero1_iteratedDeriv_eq (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 2) u θ
        = (∑ i ∈ Finset.range (k + 2), (k + 1).choose i *
              iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the ODE, rewritten on `U` as an identity for the second derivative of `u`
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => deriv u s) t
        = deriv (fun s => Real.tan s * u s) t - 6 * u t - g t := by
    intro t ht
    have h := hg t ht
    simp only [Work.FTS.EllipticEst.Lzero1] at h
    linarith
  -- regularity facts at `θ`
  have huk2 : ContDiffAt ℝ (k + 2 : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huAt1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k + 1 : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have huk : ContDiffAt ℝ (k : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k ≤ k + 2 by omega))
  have htan1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := (k + 1 : WithTop ℕ∞))).mpr hcos
  have hA : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    (htan1.mul huAt1).derivWithin (m := (k : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hB : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => 6 * u t) θ := huk.const_smul (6 : ℝ)
  -- `g` agrees with `Lzero1 u` near `θ`, and `Lzero1 u` is `C^k` there
  have hLzero : ContDiffAt ℝ (k : WithTop ℕ∞) (Work.FTS.EllipticEst.Lzero1 u) θ := by
    have hdu : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) (fun s => deriv u s) θ :=
      huk2.derivWithin (m := (k + 1 : WithTop ℕ∞))
        (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
    have hddu : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => deriv (fun s => deriv u s) t) θ :=
      hdu.derivWithin (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
    exact ((hddu.neg).add hA).sub hB
  have hgev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hg t ht)
  have hC : ContDiffAt ℝ (k : WithTop ℕ∞) g θ := hLzero.congr_of_eventuallyEq hgev
  -- differentiate the ODE `k` times
  have step1 : iteratedDeriv (k + 2) u θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ := by
    rw [show k + 2 = (k + 1) + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
  have step2 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t) θ :=
    Set.EqOn.iteratedDeriv_of_isOpen hpt hU k hθ
  have step3 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
        - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
    have hAB : ContDiffAt ℝ (k : WithTop ℕ∞)
        ((fun t => deriv (fun s => Real.tan s * u s) t) - (fun t => 6 * u t)) θ := hA.sub hB
    rw [show (fun t => deriv (fun s => Real.tan s * u s) t - 6 * u t - g t)
        = ((fun t => deriv (fun s => Real.tan s * u s) t) - (fun t => 6 * u t)) - g from rfl]
    rw [iteratedDeriv_sub hAB hC, iteratedDeriv_sub hA hB, iteratedDeriv_const_mul_field]
  -- Leibniz for the product `tan · u`
  have step4 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = ∑ i ∈ Finset.range (k + 2), (k + 1).choose i *
            iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ := by
    rw [← iteratedDeriv_succ' (n := k) (f := fun s => Real.tan s * u s)]
    exact iteratedDeriv_mul htan1 huAt1
  rw [step1, step2, step3, step4]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SliceG2Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

/-- The angular weight `σ θ = sin(2θ)^{2-γ}` of the `∫g²σ`-estimate. -/
def sigG (γ : ℝ) : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ)

/-- Unfolding lemma (definitional). -/
theorem sigG_eq (γ θ : ℝ) : sigG γ θ = Real.rpow (Real.sin (2 * θ)) (2 - γ) := rfl

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterMulEqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov.SliceTopAux

/-! ## Auxiliary facts about the one-dimensional operator `Lop` -/

/-- `Dth1Iter` is the iterate of the derivation `Lop u θ = sin(2θ)·u'(θ)`. -/
private lemma Dth1Iter_eq_lop_iterate (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.Dth1Iter_succ, ih, Function.iterate_succ_apply']
      rfl

/-- Iterating `Lop` costs one order of regularity: if `u` is `C^n` on the open set `U` then
`Lop^[a] u = D_θ^a u` is `C^{n-a}` there (for `a ≤ n`). -/
private lemma contDiffOn_Lop_iterate {U : Set ℝ} (hU : IsOpen U) {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) u U) :
    ∀ a ≤ n, ContDiffOn ℝ (((n - a : ℕ) : WithTop ℕ∞)) (Work.Spaces.Lop^[a] u) U := by
  intro a ha
  induction a with
  | zero => simpa using hu
  | succ j ih =>
      have hj : j ≤ n := Nat.le_of_succ_le ha
      have ihj : ContDiffOn ℝ (((n - j : ℕ) : WithTop ℕ∞)) (Work.Spaces.Lop^[j] u) U := ih hj
      have hle1 : 1 ≤ n - j := by omega
      have hder : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (deriv (Work.Spaces.Lop^[j] u)) U := by
        refine ContDiffOn.deriv_of_isOpen ihj hU ?_
        have hcast : (((n - j - 1 : ℕ) : WithTop ℕ∞)) + 1 = ((n - j : ℕ) : WithTop ℕ∞) := by
          rw [← Nat.sub_add_cancel hle1]; push_cast; ring
        exact le_of_eq hcast
      have key : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (Work.Spaces.Lop (Work.Spaces.Lop^[j] u)) U := by
        show ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] u) θ) U
        exact (by fun_prop : ContDiffOn ℝ (((n - j - 1 : ℕ) : WithTop ℕ∞))
          (fun θ : ℝ => Real.sin (2 * θ)) U).mul hder
      have hns : n - (j + 1) = n - j - 1 := by omega
      rw [Function.iterate_succ_apply', hns]
      exact key

/-! ## The finite-order Leibniz rule for `Lop` -/

/-- **Leibniz rule for iterates of `Lop`, finite order.**  On an open set `U` where `u` and `v`
are `C^j`, the `j`-th iterate of `Lop` applied to the pointwise product agrees on `U` with the
binomial convolution.  The hypothesis is of order `j`, not `⊤`: one order of regularity is
spent at each induction step, exactly the amount needed to differentiate the level-`(j-1)`
identity and to differentiate the `Lop^[a] u` for `a ≤ j - 1`. -/
private theorem Lop_iter_mul_eqOn_fin (U : Set ℝ) (hU : IsOpen U) (j : ℕ) :
    ∀ (u v : ℝ → ℝ),
      ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) u U →
      ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) v U →
      Set.EqOn (Work.Spaces.Lop^[j] (u * v))
        (fun θ => ∑ a ∈ Finset.range (j + 1),
          (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro u v hu hv θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro u v hu hv θ hθ
      rw [Function.iterate_succ_apply']
      have hle : ((j : ℕ) : WithTop ℕ∞) ≤ ((j + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast Nat.le_succ j
      have hprev := ih u v (hu.of_le hle) (hv.of_le hle)
      -- `Lop^[a] u`, `Lop^[b] v` are differentiable at `θ` for `a, b ≤ j`
      have hFa : ∀ a, a ≤ j → DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
        intro a ha
        have hcont := contDiffOn_Lop_iterate hU hu a (le_trans ha (Nat.le_succ j))
        have hne : (((j + 1 - a : ℕ) : WithTop ℕ∞)) ≠ 0 := by
          rw [Nat.cast_ne_zero]; omega
        exact (hcont.differentiableOn hne).differentiableAt (hU.mem_nhds hθ)
      have hGb : ∀ b, b ≤ j → DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := by
        intro b hb
        have hcont := contDiffOn_Lop_iterate hU hv b (le_trans hb (Nat.le_succ j))
        have hne : (((j + 1 - b : ℕ) : WithTop ℕ∞)) ≠ 0 := by
          rw [Nat.cast_ne_zero]; omega
        exact (hcont.differentiableOn hne).differentiableAt (hU.mem_nhds hθ)
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        rw [Finset.mem_range] at ha
        exact (((hFa a (Nat.lt_succ_iff.mp ha)).mul (hGb (j - a) (Nat.sub_le j a))).const_mul _)
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (hprev.deriv hU) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a ha => Work.Spaces.sin_deriv_term u v θ j a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          (hGb (j - a) (Nat.sub_le j a)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

/-! ## The requested statement -/

theorem Dth1IterMulEqOn (N : ℕ) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N : WithTop ℕ∞) u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ (N : WithTop ℕ∞) v (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1Iter N (fun θ => u θ * v θ))
      (fun θ => ∑ a ∈ Finset.range (N + 1),
        (N.choose a : ℝ) * (Work.Elliptic.Dth1Iter a u θ * Work.Elliptic.Dth1Iter (N - a) v θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have h := (Lop_iter_mul_eqOn_fin (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo N u v hu hv)
    (x := θ) hθ
  simp only [Dth1Iter_eq_lop_iterate]
  rw [show (fun θ : ℝ => u θ * v θ) = u * v from rfl]
  exact h

end Work.FTS.EllipticEst.remov.SliceTopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Regularity of the slice operator `Lzero1`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` on the open interval `(0, π/2)`
(`Work.FTS.EllipticEst.Lzero1`).  Since `θ ↦ tan θ` is smooth on `(0, π/2)` (the cosine
never vanishes there) and `deriv` loses exactly one order of differentiability on an open
set, `Lzero1` loses two orders:

`ContDiffOn ℝ (m + 2) u s → ContDiffOn ℝ m (Lzero1 u) s`,  `s = (0, π/2)`.

The only Mathlib ingredient that is not available off the shelf is smoothness of `Real.tan`
on `(0, π/2)` (Mathlib has it only pointwise, `Real.contDiffAt_tan`); we record it first,
since it is useful in its own right for every slicewise computation in this chapter.
-/

namespace Work.FTS.EllipticEst.remov.SliceTopAux

/-- `Real.tan` is `C^n` on the open interval `(0, π/2)`: the cosine does not vanish there. -/
theorem contDiffOn_tan_Ioo (n : WithTop ℕ∞) :
    ContDiffOn ℝ n Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  exact (Real.contDiffAt_tan.mpr (ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))).contDiffWithinAt

theorem contDiffOnLzero1 (m : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (m + 2) u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ m (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hs : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  -- `tan · u` is `C^{m+2}`
  have htu : ContDiffOn ℝ (m + 2) (fun θ => Real.tan θ * u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_tan_Ioo (m + 2)).mul hu
  -- one `deriv` on `deriv u` and one on `tan · u`
  have hdu : ContDiffOn ℝ (m + 1) (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen hs (le_of_eq rfl)
  have hd2 : ContDiffOn ℝ m (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdu.deriv_of_isOpen hs le_rfl
  have hd1 : ContDiffOn ℝ (m + 1) (deriv (fun θ => Real.tan θ * u θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    htu.deriv_of_isOpen hs (le_of_eq rfl)
  have hA : ContDiffOn ℝ m (fun θ => -(deriv (fun t => deriv u t) θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    hd2.neg
  have hB : ContDiffOn ℝ m (fun θ => deriv (fun t => Real.tan t * u t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.of_le le_self_add
  have hC : ContDiffOn ℝ m (fun θ => (6 : ℝ) * u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.mul (hu.of_le le_self_add)
  show ContDiffOn ℝ m (fun θ => -(deriv (fun t => deriv u t) θ)
      + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) (Set.Ioo 0 (Real.pi / 2))
  exact (hA.add hB).sub hC

end Work.FTS.EllipticEst.remov.SliceTopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.absIntegrableOfSqMulSeta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is at least `1` on the open slice
`(0, π/2)`: there `0 < sin(2θ) ≤ 1` and `-η ≤ 0`, so `sin(2θ)^{-η} ≥ sin(2θ)^0 = 1`
(`Real.rpow_le_rpow_of_exponent_ge` run backwards). -/
private lemma one_le_sEta_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : -(Work.Spaces.eta) ≤ (0 : ℝ) := by
    have := Work.Spaces.eta_pos; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1 hη
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- Integrability transfer on the angular slice, weak-hypothesis form: if `g` is only
a.e.-strongly measurable on `(0, π/2)` (no continuity needed) and `g²·sin(2θ)^{-η}` is
integrable on the closed slice `Iθ = [0, π/2]`, then `|g|` is integrable on the open
interval `(0, π/2)`.

Since `η = 99/100 > 0` and `0 < sin(2θ) ≤ 1` on `(0,π/2)`, the weight satisfies `1 ≤ sEta`
there, so `g² ≤ g²·sEta` pointwise; hence `g²` is integrable on `(0,π/2)`.  The endpoints
`{0, π/2}` are a null set, so `Iθ` and `(0,π/2)` carry the same restricted measure and the
integrability hypothesis transports.  Finally `|g| ≤ g² + 1` pointwise and `g² + 1` is
integrable (the slice has finite measure). -/
theorem absIntegrableOfSqMulSeta {g : ℝ → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (h : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) (Set.Ioo 0 (Real.pi / 2)) := by
  -- ## Step 0: the two endpoints `{0, π/2}` are a null set, so `Iθ = [0,π/2]` agrees with the
  -- open interval `(0, π/2)` almost everywhere, and the restricted measures coincide.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro hmem
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne hmem.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne hmem.2 (fun hc => hx (Or.inr hc))⟩
    · intro hmem
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at hmem
      exact ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  have hint : MeasureTheory.Integrable
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact h
  -- ## Step 1: on `(0, π/2)` the weight satisfies `1 ≤ sEta`, so `g² ≤ g² · sEta` a.e.
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint.mono' (hgm.pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_of_mem hθ
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- ## Step 2: `|g| ≤ g² + 1` pointwise, and `g² + 1` is integrable (the slice has finite
  -- measure), so `|g|` is integrable on `(0, π/2)`.
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
  refine hmaj.mono' hgm.norm ?_
  filter_upwards with θ
  have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
  simpa only [Real.norm_eq_abs, abs_abs] using h1

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.chainZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## Elementary facts about the angular profile `sinCos2` -/

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

theorem sinCos2_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  unfold Work.Elliptic.sinCos2
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]))
    (pow_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) 2)




/-! ## Differentiating the partial derivative, and continuity of the slices -/

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_of_isOpen {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) U := by
  have hfd : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry G)) U :=
    h.fderiv_of_isOpen hU (by simp)
  have hcomp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) U :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))



/-- A.e. strong measurability on `Iθ` from continuity on the open interval. -/
theorem aesm_of_continuousOn_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  have h1 : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aestronglyMeasurable measurableSet_Ioo
  rwa [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc] at h1

/-- The `z`-slice is differentiable with derivative the partial `∂_z`. -/
theorem hasDerivAt_zslice {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry G) U) {s θ : ℝ}
    (hp : (s, θ) ∈ U) : HasDerivAt (fun r => G r θ) (Work.Spaces.pz G s θ) s := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (s, θ) :=
    (h.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [Work.Spaces.pz] using (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt



/-! ## The fundamental theorem of calculus along `z`, slice by slice -/






end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.tanuIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- **The single-integration identity for `Lzero1`.**

For `u` of class `C²` on the open interval `(0, π/2)` and `0 < ε < b < π/2`,

  `tan b · u b = ∫_ε^b Lzero1 u + u'(b) - u'(ε) + tan ε · u ε + 6 ∫_ε^b u`.

Indeed `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so two applications of the fundamental
theorem of calculus (for `u'` and for `tan θ · u`) give the claim. -/
theorem tanuIdentity {u : ℝ → ℝ} (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {ε b : ℝ} (hε : 0 < ε) (hεb : ε < b) (hb : b < Real.pi / 2) :
    Real.tan b * u b
      = (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ) + deriv u b - deriv u ε
        + Real.tan ε * u ε + 6 * (∫ θ in ε..b, u θ) := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsub : Set.Icc ε b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hcosU : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  -- regularity on the open interval
  have hu1U : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm.of_le (by norm_num)
  have hduU : ContDiffOn ℝ 1 (fun t => deriv u t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have htanU : ContDiffOn ℝ 1 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun x hx =>
    ((Real.contDiffAt_tan (n := 1)).2 (hcosU x hx)).contDiffWithinAt
  have hprodU : ContDiffOn ℝ 1 (fun θ => Real.tan θ * u θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htanU.mul hu1U
  -- the two fundamental-theorem-of-calculus applications
  have hFTCa : (∫ θ in ε..b, deriv (fun t => deriv u t) θ) = deriv u b - deriv u ε :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hduU.mono hsub) hεb.le
  have hFTCb : (∫ θ in ε..b, deriv (fun t => Real.tan t * u t) θ)
      = Real.tan b * u b - Real.tan ε * u ε :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hprodU.mono hsub) hεb.le
  -- integrability of the three pieces
  have hI1 : IntervalIntegrable (fun θ => deriv (fun t => deriv u t) θ) volume ε b := by
    have h0 : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hduU.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn)
    exact (h0.mono hsub).intervalIntegrable_of_Icc hεb.le
  have hI2 : IntervalIntegrable (fun θ => deriv (fun t => Real.tan t * u t) θ) volume ε b :=
    ContinuousOn.intervalIntegrable_of_Icc hεb.le
      ((hprodU.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub)
  have hI3 : IntervalIntegrable u volume ε b :=
    (hsm.continuousOn.mono hsub).intervalIntegrable_of_Icc hεb.le
  -- split the integral of `Lzero1`
  have hsplit : (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ)
      = -(∫ θ in ε..b, deriv (fun t => deriv u t) θ)
        + (∫ θ in ε..b, deriv (fun t => Real.tan t * u t) θ)
        - 6 * (∫ θ in ε..b, u θ) := by
    have hunfold : (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ)
        = ∫ θ in ε..b, (-(deriv (fun t => deriv u t) θ)
            + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) := by
      simp only [Work.FTS.EllipticEst.Lzero1]
    have hA : IntervalIntegrable (fun θ => -(deriv (fun t => deriv u t) θ)
        + deriv (fun t => Real.tan t * u t) θ) volume ε b := hI1.neg.add hI2
    have hB : IntervalIntegrable (fun θ => 6 * u θ) volume ε b := hI3.const_mul 6
    have hA1 : IntervalIntegrable (fun θ => -(deriv (fun t => deriv u t) θ)) volume ε b :=
      hI1.neg
    rw [hunfold, intervalIntegral.integral_sub hA hB, intervalIntegral.integral_add hA1 hI2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hsplit, hFTCa, hFTCb]
  ring

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Step4.abs_integral_mul_sigma_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Step4

open MeasureTheory

/-! ## A weighted Cauchy–Schwarz (Young) bound on the angular interval

This file proves the elementary "absorbing" inequality used in step 4 of the
elliptic estimates: for a *non-negative* angular weight `σ`, if `f²σ` and `h²σ`
are integrable on `Iθ = [0, π/2]` then `f·h·σ` is integrable there and

  `|∫ f h σ| ≤ ε ∫ f²σ + (1/(4ε)) ∫ h²σ`.

The pointwise input is Young's inequality `2ab ≤ a² + b²` applied to
`a = √ε |f| √σ`, `b = |h| √σ/(2√ε)`; the specific weight of the paper is
`σ θ = sin(2θ)^{2-γ}` (with `2 - γ > 0` for the relevant range of `γ`). -/

/-- Young's inequality in the form needed below: for `ε > 0`,
`|x*y| ≤ ε x² + (1/(4ε)) y²`.  (The constant `4` is the sharp one: it is
`(2√ε)²` from `2ab ≤ a² + b²` with `a = √ε x`, `b = y/√ε`.) -/
theorem abs_mul_le_eps_sq_add (ε : ℝ) (hε : 0 < ε) (x y : ℝ) :
    |x * y| ≤ ε * x ^ 2 + (1 / (4 * ε)) * y ^ 2 := by
  have h4 : (0 : ℝ) < 4 * ε := by positivity
  have key : 4 * ε * |x * y| ≤ 4 * ε ^ 2 * x ^ 2 + y ^ 2 := by
    have h5 := sq_nonneg (2 * ε * |x| - |y|)
    rw [abs_mul]
    nlinarith [sq_abs x, sq_abs y]
  have h6 : |x * y| ≤ (4 * ε ^ 2 * x ^ 2 + y ^ 2) / (4 * ε) := by
    rw [le_div_iff₀ h4]
    linarith [key]
  have h7 : (4 * ε ^ 2 * x ^ 2 + y ^ 2) / (4 * ε) = ε * x ^ 2 + (1 / (4 * ε)) * y ^ 2 := by
    field_simp
  linarith [h6, h7]

/-- Weighted Cauchy–Schwarz ("absorbing") inequality on the angular interval
`Iθ = [0,π/2]`: for a non-negative weight `σ`, if `f²σ` and `h²σ` are integrable
then so is `f·h·σ`, and the integral is bounded by
`ε ∫ f²σ + (1/(4ε)) ∫ h²σ`. -/
theorem integrableOn_mul_of_sq_integrableOn (ε : ℝ) (hε : 0 < ε) {σ f h : ℝ → ℝ}
    (hσm : AEStronglyMeasurable σ (volume.restrict Work.Spaces.Iθ))
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hfm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (hhm : AEStronglyMeasurable h (volume.restrict Work.Spaces.Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hh : IntegrableOn (fun θ => (h θ) ^ 2 * σ θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => f θ * h θ * σ θ) Work.Spaces.Iθ
      ∧ |∫ θ in Work.Spaces.Iθ, f θ * h θ * σ θ|
          ≤ ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
            + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := isClosed_Icc.measurableSet
  -- pointwise Young bound
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, |f θ * h θ * σ θ| ≤
      ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ) := by
    intro θ hθ
    have hσ0 : 0 ≤ σ θ := hσnn θ hθ
    have h1 : |f θ * h θ * σ θ| = |f θ * h θ| * σ θ := by
      rw [abs_mul, abs_of_nonneg hσ0]
    have h3 := mul_le_mul_of_nonneg_right (abs_mul_le_eps_sq_add ε hε (f θ) (h θ)) hσ0
    rw [h1]
    calc |f θ * h θ| * σ θ
        ≤ (ε * (f θ) ^ 2 + (1 / (4 * ε)) * (h θ) ^ 2) * σ θ := h3
      _ = ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ) := by ring
  -- the dominating function is integrable
  have hGint : IntegrableOn
      (fun θ => ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ))
      Work.Spaces.Iθ :=
    (hf.const_mul ε).add (hh.const_mul (1 / (4 * ε)))
  have hgm : AEStronglyMeasurable (fun θ => f θ * h θ * σ θ)
      (volume.restrict Work.Spaces.Iθ) := (hfm.mul hhm).mul hσm
  have hmain : IntegrableOn (fun θ => f θ * h θ * σ θ) Work.Spaces.Iθ := by
    refine Integrable.mono' hGint hgm ?_
    filter_upwards [ae_restrict_mem hIθ] with θ hθ
    simpa [Real.norm_eq_abs] using hpt θ hθ
  refine ⟨hmain, ?_⟩
  -- comparison of integrals
  have hmono : ∫ θ in Work.Spaces.Iθ, |f θ * h θ * σ θ|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ)) :=
    setIntegral_mono_ae_restrict hmain.abs hGint (by
      filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact hpt θ hθ)
  have hsplit : ∫ θ in Work.Spaces.Iθ,
        (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ))
      = ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
        + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := by
    rw [integral_add (hf.const_mul ε) (hh.const_mul (1 / (4 * ε))),
      integral_const_mul, integral_const_mul]
  calc |∫ θ in Work.Spaces.Iθ, f θ * h θ * σ θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |f θ * h θ * σ θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (ε * ((f θ) ^ 2 * σ θ) + (1 / (4 * ε)) * ((h θ) ^ 2 * σ θ)) := hmono
    _ = ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
        + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * σ θ) := hsplit

/-- The weight `σ θ = sin(2θ)^{2-γ}` of the elliptic estimates is measurable. -/
theorem measurable_sin_two_rpow (γ : ℝ) :
    Measurable fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  measurability

theorem abs_integral_mul_sigma_le (γ ε : ℝ) (hε : 0 < ε) {f h : ℝ → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hhm : MeasureTheory.AEStronglyMeasurable h
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => (h θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => f θ * h θ *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ |∫ θ in Work.Spaces.Iθ, f θ * h θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)|
          ≤ ε * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (1 / (4 * ε)) * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  have hσm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (measurable_sin_two_rpow γ).aestronglyMeasurable
  exact integrableOn_mul_of_sq_integrableOn ε hε hσm hσnn hfm hhm hf hh

end Work.FTS.EllipticEst.remov.Step4
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Definitions for the far region of the angular slice estimate (`remov/slice_ang_gen`)

The far region `θ ∈ [3π/8, π/2]` of the one-dimensional angular estimate of Elgindi's
§"General `ℋ^k` case" is handled by the paper's integration by parts, whose combined form is

```
  ∫_a^b [ top-order triple ] · q  =  - ∫_a^b B(θ)·(v^{(k+1)})²·q
                                       + ((k+1)/2)·∫_a^b (cos²θ·q)''·(v^{(k)})²
                                       + D(b) - D(a)
```

with `v = u/cos θ`, `q = sin(2θ)^{2k-γ}`, the room coefficient
`B = ((2k+1-γ)/2)cos2θ + (k+2)sin²θ + (k+1)cos²θ = ((4k+3-γ)/2)cos²θ + ((3+γ)/2)sin²θ ≥ (3+γ)/2 > 0`,
and the flux `D` defined below.  This file only *defines* the objects; the identity itself
(an immediate consequence of the two product-rule identities of `remov/slice_ang_room_ident`,
integrated over `(a,b)`) is `roomFluxIdentity`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The function `v = u / cos θ` of the paper's far-region computation. -/
def vF (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.cos θ

/-- The weight `q = sin(2θ)^{2k-γ}`. -/
def qW (k : ℕ) (γ θ : ℝ) : ℝ := Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)




end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.ang_ode_iterate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

/-- **The `k`-fold differentiated slice ODE, in the `∂^{k+1}(tan θ · u)` form.**

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so `g = Lzero1 u` on `(0,π/2)` says
`∂_θ(tan θ · u) = u'' + 6u + g` there; applying `∂_θ^k` to that identity gives, at every
`θ ∈ (0,π/2)`,

`∂_θ^{k+1}(tan θ · u)(θ) = u^{(k+2)}(θ) + 6 u^{(k)}(θ) + g^{(k)}(θ)`.

Route: the pointwise identity `deriv (fun t => Real.tan t * u t) θ = deriv (deriv u) θ + 6*u θ + g θ`
on `(0,π/2)` (from the definition of `Lzero1`), upgraded to an `=ᶠ[𝓝 θ]` statement, on which
`Filter.EventuallyEq.iteratedDeriv_eq k` applies; then `iteratedDeriv k` of the sum is the sum
(`iteratedDeriv_add` with the `ContDiffAt` regularity of the summands: for `u` from `hu`, for
`deriv (deriv u)` from `hu`, and for `g` from `g =ᶠ[𝓝 θ] Lzero1 u` together with the regularity of
`Lzero1 u`), and `iteratedDeriv k (deriv (deriv u)) = iteratedDeriv (k+2) u`,
`iteratedDeriv k (deriv f) = iteratedDeriv (k+1) f` (`iteratedDeriv_succ'`).  (The proved
`remov/Lzero1_iteratedDeriv_eq` gives the same content in expanded form with
`Σ_i C(k+1,i) (tan)^{(i)} u^{(k+1-i)}` on the left-hand side, so a proof can also be assembled from
it plus `iteratedDeriv_mul`.) -/
theorem ang_ode_iterate (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
        = iteratedDeriv (k + 2) u θ + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the ODE, solved for `∂_θ(tan θ · u)` and read as a pointwise identity on `(0, π/2)`
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun s => Real.tan s * u s) t
        = deriv (fun s => deriv u s) t + 6 * u t + g t := by
    intro t ht
    have h := hg t ht
    simp only [Work.FTS.EllipticEst.Lzero1] at h
    linarith
  have hev : deriv (fun s => Real.tan s * u s) =ᶠ[𝓝 θ]
      fun t => deriv (fun s => deriv u s) t + 6 * u t + g t :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hpt t ht)
  -- regularity facts at `θ`
  have huk2 : ContDiffAt ℝ (k + 2 : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huAt1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k + 1 : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have huk : ContDiffAt ℝ (k : WithTop ℕ∞) u θ :=
    huk2.of_le (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k ≤ k + 2 by omega))
  have htan1 : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := (k + 1 : WithTop ℕ∞))).mpr hcos
  have hA : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    (htan1.mul huAt1).derivWithin (m := (k : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hB : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => 6 * u t) θ := huk.const_smul (6 : ℝ)
  have hdu : ContDiffAt ℝ (k + 1 : WithTop ℕ∞) (fun s => deriv u s) θ :=
    huk2.derivWithin (m := (k + 1 : WithTop ℕ∞))
      (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
  have hddu : ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun t => deriv (fun s => deriv u s) t) θ :=
    hdu.derivWithin (m := (k : WithTop ℕ∞)) (by exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  have hLzero : ContDiffAt ℝ (k : WithTop ℕ∞) (Work.FTS.EllipticEst.Lzero1 u) θ :=
    ((hddu.neg).add hA).sub hB
  have hgev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hθ) (fun t ht => hg t ht)
  have hC : ContDiffAt ℝ (k : WithTop ℕ∞) g θ := hLzero.congr_of_eventuallyEq hgev
  -- differentiate the identity `k` times and expand
  have step1 : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ := by
    rw [iteratedDeriv_succ']
  have step2 : iteratedDeriv k (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t) θ :=
    hev.iteratedDeriv_eq k
  have step3 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t) θ
      = iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
        + 6 * iteratedDeriv k u θ + iteratedDeriv k g θ := by
    have hAB : ContDiffAt ℝ (k : WithTop ℕ∞)
        ((fun t => deriv (fun s => deriv u s) t) + (fun t => 6 * u t)) θ := hddu.add hB
    rw [show (fun t => deriv (fun s => deriv u s) t + 6 * u t + g t)
        = ((fun t => deriv (fun s => deriv u s) t) + (fun t => 6 * u t)) + g from rfl]
    rw [iteratedDeriv_add hAB hC, iteratedDeriv_add hddu hB,
      iteratedDeriv_const_mul_field]
  have step4 : iteratedDeriv k (fun t => deriv (fun s => deriv u s) t) θ
      = iteratedDeriv (k + 2) u θ := by
    rw [show k + 2 = (k + 1) + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
  rw [step1, step2, step3, step4]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.phi_slice_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slicewise primitive of `Lzero1 u · sinCos2`

`sinCos2 θ = sin θ cos²θ` is the kernel of the formal adjoint `LzeroAdj` of the angular
operator `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`.  The companion identity -- the one proved
here -- is that the function

  `Φ θ = -sinCos2 θ · u'(θ) + cos θ · cos 2θ · u(θ)`

is a primitive of `θ ↦ (Lzero1 u θ) · sinCos2 θ` on `(0, π/2)`: differentiating `Φ` and
matching coefficients turns the request into the two trigonometric identities

  `-sinCos2' + cos θ cos 2θ = sinCos2 θ · tan θ`,
  `(cos θ cos 2θ)' = sinCos2 θ · (1/cos²θ - 6)`,

which are the coefficient comparisons for `u'` and `u` respectively.
-/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov.coerc

theorem phi_slice_hasDerivAt {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun θ => -(Work.Elliptic.sinCos2 θ) * deriv u θ
          + Real.cos θ * Real.cos (2 * θ) * u θ)
        (Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) θ := by
  intro θ hθ
  -- the open interval is a neighbourhood of `θ`, so `u` is `C²` at `θ`
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hAt : ContDiffAt ℝ 2 u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- `u` and `u'` are differentiable at `θ`, with derivatives `u'` and `u''`
  have hu1 : HasDerivAt u (deriv u θ) θ := (hAt.differentiableAt (by norm_num)).hasDerivAt
  have hdu : ContDiffAt ℝ 1 (fun t => deriv u t) θ := hAt.derivWithin (m := 1) (by norm_num)
  have hu2 : HasDerivAt (deriv u) (deriv (fun t => deriv u t) θ) θ :=
    (hdu.differentiableAt (by norm_num)).hasDerivAt
  -- the derivative of `tan θ · u θ`
  have htanu : HasDerivAt (fun t => Real.tan t * u t)
      ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hu1
  -- the derivative of `sinCos2 = sin · cos²`
  have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hcossq : HasDerivAt (fun t => Real.cos t ^ 2) ((2 : ℝ) * Real.cos θ * (-Real.sin θ)) θ := by
    have h := (Real.hasDerivAt_cos θ).pow 2
    have hfun : (Real.cos ^ 2 : ℝ → ℝ) = fun t => Real.cos t ^ 2 := by funext t; simp
    rw [hfun] at h
    simpa using h
  have hsc : HasDerivAt Work.Elliptic.sinCos2
      (Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * ((2 : ℝ) * Real.cos θ * (-Real.sin θ))) θ := by
    have h := hsin.mul hcossq
    have hfun : (Real.sin * fun t => Real.cos t ^ 2 : ℝ → ℝ) = Work.Elliptic.sinCos2 := by
      funext t; simp [Work.Elliptic.sinCos2]
    rw [hfun] at h
    exact h
  have hnegsc : HasDerivAt (fun θ => -(Work.Elliptic.sinCos2 θ))
      (-(Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * ((2 : ℝ) * Real.cos θ * (-Real.sin θ)))) θ :=
    hsc.neg
  -- the derivative of `cos θ · cos 2θ`
  have hcos2θ : HasDerivAt (fun θ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
    have hlin : HasDerivAt (fun θ : ℝ => 2 * θ) (2 : ℝ) θ := by
      simpa using hasDerivAt_const_mul (x := θ) (2 : ℝ)
    have h' := (Real.hasDerivAt_cos (2 * θ)).comp θ hlin
    simpa only [Function.comp_def] using h'
  have hcc : HasDerivAt (fun θ => Real.cos θ * Real.cos (2 * θ))
      ((-Real.sin θ) * Real.cos (2 * θ) + Real.cos θ * (-Real.sin (2 * θ) * 2)) θ :=
    (Real.hasDerivAt_cos θ).mul hcos2θ
  -- assemble the derivative of the whole slice
  have hφ : HasDerivAt (fun θ => -(Work.Elliptic.sinCos2 θ) * deriv u θ
          + Real.cos θ * Real.cos (2 * θ) * u θ)
      ((-(Real.cos θ * Real.cos θ ^ 2 + Real.sin θ * ((2 : ℝ) * Real.cos θ * (-Real.sin θ)))) * deriv u θ
        + (-(Work.Elliptic.sinCos2 θ)) * deriv (fun t => deriv u t) θ
        + (((-Real.sin θ) * Real.cos (2 * θ) + Real.cos θ * (-Real.sin (2 * θ) * 2)) * u θ
            + (Real.cos θ * Real.cos (2 * θ)) * deriv u θ)) θ := by
    have h1 := hnegsc.mul hu2
    have h2 := hcc.mul hu1
    have h3 := h1.add h2
    have hfun : ((fun θ => -(Work.Elliptic.sinCos2 θ)) * deriv u
          + (fun θ => Real.cos θ * Real.cos (2 * θ)) * u : ℝ → ℝ)
        = fun θ => -(Work.Elliptic.sinCos2 θ) * deriv u θ
            + Real.cos θ * Real.cos (2 * θ) * u θ := by
      funext t; simp only [Pi.add_apply, Pi.mul_apply]
    rw [hfun] at h3
    exact h3
  -- it remains to identify the value with `Lzero1 u θ · sinCos2 θ`
  refine hφ.congr_deriv ?_
  rw [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.sinCos2, htanu.deriv,
      Real.tan_eq_sin_div_cos, Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  ring_nf
  linear_combination (Real.cos θ * deriv u θ) * Real.sin_sq_add_cos_sq θ

end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.cosBarIdents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ### Elementary facts about iterated derivatives -/

/-- A `C^n` function has a `C^{n-k}` `k`-th derivative. -/
lemma contDiffAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f x) (hk : k ≤ n) :
    ContDiffAt ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have h1 : n - k - 1 + 1 = n - k := by omega
      have hle : ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((n - k : ℕ) : WithTop ℕ∞) := by
        rw [show ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 = (((n - k - 1) + 1 : ℕ) : WithTop ℕ∞) from by
          push_cast; ring, h1]
      have hstep : ContDiffAt ℝ ((n - k - 1 : ℕ) : WithTop ℕ∞) (deriv (iteratedDeriv k f)) x :=
        (ih hk').derivWithin (m := ((n - k - 1 : ℕ) : WithTop ℕ∞)) hle
      convert hstep using 2
      exact iteratedDeriv_succ

/-- The second `iteratedDeriv` is the second `deriv`. -/
lemma itd_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The third `iteratedDeriv` is the third `deriv`. -/
lemma itd_three (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, itd_two]

/-- The fourth `iteratedDeriv` is the fourth `deriv`. -/
lemma itd_four (f : ℝ → ℝ) : iteratedDeriv 4 f = deriv (deriv (deriv (deriv f))) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, itd_three]

lemma itd_one_val (f : ℝ → ℝ) (x : ℝ) : iteratedDeriv 1 f x = deriv f x := by
  rw [iteratedDeriv_one]

lemma itd_two_val (f : ℝ → ℝ) (x : ℝ) : iteratedDeriv 2 f x = deriv (deriv f) x := by
  rw [itd_two]

lemma itd_three_val (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 3 f x = deriv (deriv (deriv f)) x := by rw [itd_three]

lemma itd_four_val (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 4 f x = deriv (deriv (deriv (deriv f))) x := by rw [itd_four]

/-- One `deriv` on top of a `k`-th `iteratedDeriv` is the `(k+1)`-st one. -/
lemma itd_comp_one (n : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) = iteratedDeriv (n + 1) f := by
  rw [show (iteratedDeriv n f : ℝ → ℝ) = fun t => iteratedDeriv n f t from rfl,
    iteratedDeriv_one, ← iteratedDeriv_succ]

/-- Two `deriv`s on top of a `k`-th `iteratedDeriv` is the `(k+2)`-nd one. -/
lemma itd_comp_two (n : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv 2 (iteratedDeriv n f) = iteratedDeriv (n + 2) f := by
  rw [itd_two, ← iteratedDeriv_one (f := iteratedDeriv n f), itd_comp_one,
    ← iteratedDeriv_succ]

lemma itd_comp_one_val (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) x = iteratedDeriv (n + 1) f x := by
  rw [itd_comp_one]

lemma itd_comp_two_val (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 (iteratedDeriv n f) x = iteratedDeriv (n + 2) f x := by
  rw [itd_comp_two]

/-! ### Leibniz expansions of `cos · g` and `sin · g` -/

lemma itd_cos_one (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (fun t => Real.cos t * g t) x
      = -Real.sin x * g x + Real.cos x * iteratedDeriv 1 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_two (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun t => Real.cos t * g t) x
      = -Real.cos x * g x - 2 * Real.sin x * iteratedDeriv 1 g x
        + Real.cos x * iteratedDeriv 2 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_three (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (fun t => Real.cos t * g t) x
      = Real.sin x * g x - 3 * Real.cos x * iteratedDeriv 1 g x
        - 3 * Real.sin x * iteratedDeriv 2 g x + Real.cos x * iteratedDeriv 3 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_four (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 4 g x) :
    iteratedDeriv 4 (fun t => Real.cos t * g t) x
      = Real.cos x * g x + 4 * Real.sin x * iteratedDeriv 1 g x
        - 6 * Real.cos x * iteratedDeriv 2 g x - 4 * Real.sin x * iteratedDeriv 3 g x
        + Real.cos x * iteratedDeriv 4 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_sin_one (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (fun t => Real.sin t * g t) x
      = Real.cos x * g x + Real.sin x * iteratedDeriv 1 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

lemma itd_sin_two (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun t => Real.sin t * g t) x
      = -Real.sin x * g x + 2 * Real.cos x * iteratedDeriv 1 g x
        + Real.sin x * iteratedDeriv 2 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

lemma itd_sin_three (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (fun t => Real.sin t * g t) x
      = -Real.cos x * g x - 3 * Real.sin x * iteratedDeriv 1 g x
        + 3 * Real.cos x * iteratedDeriv 2 g x + Real.sin x * iteratedDeriv 3 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

/-! ### The four identities -/

theorem cosBarIdents {u : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.Lzero1 u θ
          = - Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + 3 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 4 * Real.cos θ * (u θ / Real.cos θ)) ∧
      (deriv (deriv u) θ
          = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 5 * Real.cos θ * (u θ / Real.cos θ) - Work.FTS.EllipticEst.Lzero1 u θ) ∧
      (deriv (deriv (deriv u)) θ
          = Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            - 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + 5 * Real.sin θ * (u θ / Real.cos θ)
            - deriv (Work.FTS.EllipticEst.Lzero1 u) θ) ∧
      (deriv (deriv (deriv (deriv u))) θ
          = Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
            - 3 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + 9 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + 5 * Real.cos θ * (u θ / Real.cos θ)
            - deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  set ψ : ℝ → ℝ := fun t => u t / Real.cos t with hψdef
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have hψC : ContDiffOn ℝ 4 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 4 ψ θ := hψC.contDiffAt hIoo
  have hψOf : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 4 ψ t :=
    fun t ht => hψC.contDiffAt (isOpen_Ioo.mem_nhds ht)
  -- smoothness of the other functions involved
  have huC1 : ContDiffAt ℝ 1 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC3 : ContDiffAt ℝ 3 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have htanC2 : ContDiffAt ℝ 2 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htanC3 : ContDiffAt ℝ 3 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htuC2 : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ := htanC2.mul huC2
  have htuC3 : ContDiffAt ℝ 3 (fun s => Real.tan s * u s) θ := htanC3.mul huC3
  -- `u = cos · ψ` near every point of the interval
  have hu_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u =ᶠ[𝓝 t] fun s => Real.cos s * ψ s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show u s = Real.cos s * ψ s
    rw [hψdef, ← mul_div_assoc, mul_div_cancel_left₀ (u s) hc]
  -- `tan · u = sin · ψ` near every point of the interval
  have htan_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (fun s => Real.tan s * u s) =ᶠ[𝓝 t] fun s => Real.sin s * ψ s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show Real.tan s * u s = Real.sin s * ψ s
    rw [Real.tan_eq_sin_div_cos, hψdef, div_mul_eq_mul_div, mul_div_assoc]
  -- expansions of the derivatives of `u`
  have hu1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 1 u t = -Real.sin t * ψ t + Real.cos t * iteratedDeriv 1 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 (hu_eq t ht)]
    exact itd_cos_one ψ t ((hψOf t ht).of_le (by norm_num))
  have hu2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 u t = -Real.cos t * ψ t - 2 * Real.sin t * iteratedDeriv 1 ψ t
        + Real.cos t * iteratedDeriv 2 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 (hu_eq t ht)]
    exact itd_cos_two ψ t ((hψOf t ht).of_le (by norm_num))
  have hu3 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 3 u t = Real.sin t * ψ t - 3 * Real.cos t * iteratedDeriv 1 ψ t
        - 3 * Real.sin t * iteratedDeriv 2 ψ t + Real.cos t * iteratedDeriv 3 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 (hu_eq t ht)]
    exact itd_cos_three ψ t ((hψOf t ht).of_le (by norm_num))
  have hu4 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 4 u t = Real.cos t * ψ t + 4 * Real.sin t * iteratedDeriv 1 ψ t
        - 6 * Real.cos t * iteratedDeriv 2 ψ t - 4 * Real.sin t * iteratedDeriv 3 ψ t
        + Real.cos t * iteratedDeriv 4 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 4 (hu_eq t ht)]
    exact itd_cos_four ψ t ((hψOf t ht).of_le (by norm_num))
  -- expansions of the derivatives of `tan θ · u`
  have htu1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 1 (fun s => Real.tan s * u s) t
        = Real.cos t * ψ t + Real.sin t * iteratedDeriv 1 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 (htan_eq t ht)]
    exact itd_sin_one ψ t ((hψOf t ht).of_le (by norm_num))
  have htu2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (fun s => Real.tan s * u s) t
        = -Real.sin t * ψ t + 2 * Real.cos t * iteratedDeriv 1 ψ t
          + Real.sin t * iteratedDeriv 2 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 (htan_eq t ht)]
    exact itd_sin_two ψ t ((hψOf t ht).of_le (by norm_num))
  have htu3 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 3 (fun s => Real.tan s * u s) t
        = -Real.cos t * ψ t - 3 * Real.sin t * iteratedDeriv 1 ψ t
          + 3 * Real.cos t * iteratedDeriv 2 ψ t + Real.sin t * iteratedDeriv 3 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 (htan_eq t ht)]
    exact itd_sin_three ψ t ((hψOf t ht).of_le (by norm_num))
  -- the value of `Lzero1 u`
  have hLval : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Lzero1 u t = -4 * Real.cos t * ψ t + 3 * Real.sin t * iteratedDeriv 1 ψ t
        - Real.cos t * iteratedDeriv 2 ψ t := by
    intro t ht
    have h0 : u t = Real.cos t * ψ t := (hu_eq t ht).self_of_nhds
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
    unfold Lzero1
    rw [hd2, hd1, hu2 t ht, htu1 t ht, h0]
    ring
  -- `Lzero1 u` as a function
  have hL_eq : Lzero1 u = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
      - (fun t => 6 * u t) := by
    funext t
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
    unfold Lzero1
    rw [hd2, hd1]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  -- smoothness of the two pieces of `hL_eq`
  have hu2C2 : ContDiffAt ℝ 2 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv (f := u) (n := 4) (k := 2) (hu.contDiffAt hIoo) (by norm_num)
  have hu2C1 : ContDiffAt ℝ 1 (iteratedDeriv 2 u) θ := hu2C2.of_le (by norm_num)
  have htu1C1 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 2) (k := 1) htuC2 (by norm_num)
  have htu1C2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 3) (k := 1) htuC3 (by norm_num)
  -- first derivative of `Lzero1 u`
  have hL1 : iteratedDeriv 1 (Lzero1 u) θ
      = -iteratedDeriv 3 u θ + iteratedDeriv 2 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 1 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 1
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C1).add htu1C1
    have hB : ContDiffAt ℝ 1 (fun t => 6 * u t) θ := contDiffAt_const.mul huC1
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 1 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C1
    have hA2 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C1
    rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC1]
    rw [itd_comp_one_val 2 u θ, itd_comp_one_val 1 (fun s => Real.tan s * u s) θ]
  -- second derivative of `Lzero1 u`
  have hL2 : iteratedDeriv 2 (Lzero1 u) θ
      = -iteratedDeriv 4 u θ + iteratedDeriv 3 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 2 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 2
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C2).add htu1C2
    have hB : ContDiffAt ℝ 2 (fun t => 6 * u t) θ := contDiffAt_const.mul huC2
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 2 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C2
    have hA2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C2
    rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC2]
    rw [itd_comp_two_val 2 u θ, itd_comp_two_val 1 (fun s => Real.tan s * u s) θ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- identity 1
    rw [hLval θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 2
    rw [← itd_two_val u θ, hu2 θ hθ, hLval θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 3
    rw [← itd_three_val u θ, ← itd_one_val (Lzero1 u) θ, hL1, hu3 θ hθ, htu2 θ hθ,
      hu1 θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 4
    rw [← itd_four_val u θ, ← itd_two_val (Lzero1 u) θ, hL2, hu4 θ hθ, htu3 θ hθ,
      hu2 θ hθ, itd_one_val, itd_two_val, itd_three_val]
    ring

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.g_pointwise_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem g_pointwise_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = - deriv (deriv u) θ + Real.tan θ * deriv u θ
        + (Real.tan θ ^ 2 - 5) * u θ := by
  intro θ hθ
  -- `cos θ ≠ 0` on `(0, π/2)`, so `tan` is differentiable at `θ`.
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'
  -- `u` is differentiable at `θ` because `θ` is an interior point of the (open) domain.
  have hdu : DifferentiableAt ℝ u θ :=
    (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
  have hmtan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  -- `tan' = 1/cos² = tan² + 1`.
  have htrig : 1 / Real.cos θ ^ 2 = Real.tan θ ^ 2 + 1 := by
    rw [div_eq_iff (pow_ne_zero 2 hcos)]
    have h := Real.one_add_tan_sq_mul_cos_sq_eq_one hcos
    ring_nf
    linarith [h]
  -- Product rule for `∂_θ(tan θ · u θ)`.
  have hmul : deriv (fun t => Real.tan t * u t) θ
      = Real.tan θ * deriv u θ + (Real.tan θ ^ 2 + 1) * u θ := by
    change deriv (Real.tan * u) θ = _
    rw [deriv_mul hmtan hdu, Real.deriv_tan]
    rw [htrig]
    ring
  -- Unfold `Lzero1`, identifying `deriv (fun t => deriv u t) θ` with `deriv (deriv u) θ`.
  have h1 : Work.FTS.EllipticEst.Lzero1 u θ
      = -deriv (deriv u) θ + deriv (fun t => Real.tan t * u t) θ - 6 * u θ := rfl
  have hg' : g θ = -deriv (deriv u) θ + deriv (fun t => Real.tan t * u t) θ - 6 * u θ := by
    have h := (hg θ hθ).symm
    rwa [h1] at h
  rw [hg', hmul]
  ring

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_ang_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_bd_sup_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary one-dimensional tools for the slice estimate -/

/-- On the open slice `(0, π/2)` the weight `sEta = sin(2θ)^{-η}` is at least `1`. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
  · exact Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  · exact Real.sin_le_one _
  · have hη : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith

/-- On the slice `Iθ` the weight `sEta` is nonnegative. -/
private lemma sEta_nonneg_of_mem_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- The mean-value property of the integral: a continuous function on `[a,b]` takes its average
value at some point of `[a,b]`. -/
private lemma exists_eq_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = (∫ t in Set.Icc a b, f t) / (b - a) := by
  have h1 : ContinuousOn f (Set.uIcc a b) := by
    rwa [Set.uIcc_of_le hab.le]
  obtain ⟨c, hc, hcc⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := f) (g := fun _ : ℝ => (1 : ℝ)) (μ := volume) (a := a) (b := b) h1
    intervalIntegrable_const (fun x _ => zero_le_one)
  have hc' : c ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hc
  refine ⟨c, hc', ?_⟩
  have hL : (∫ x in a..b, f x * 1) = ∫ x in a..b, f x := by simp
  have hR : (∫ x in a..b, (1 : ℝ)) = b - a := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hset : (∫ x in a..b, f x) = ∫ x in Set.Icc a b, f x := by
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hL, hR, hset] at hcc
  rw [hcc, mul_div_cancel_right₀ _ (by linarith)]

/-- If `g²·sEta` is integrable on `Iθ` then so are `g²` and `|g|`, and `∫ g² ≤ ∫ g²·sEta`. -/
private lemma integrableOn_sq_of_sq_mul_sEta {g : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have hIoo : (volume.restrict (Set.Ioo 0 (Real.pi / 2)))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
    rw [← hIoo, MeasureTheory.ae_restrict_iff' isOpen_Ioo.measurableSet]
    exact Eventually.of_forall (fun x hx => one_le_sEta hx)
  have hsq_le : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g θ) ^ 2 ≤ (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [hae] with θ hθ
    simpa using mul_le_mul_of_nonneg_left hθ (sq_nonneg (g θ))
  have hint_sq : IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' h (hmeas.pow 2) ?_
    filter_upwards [hsq_le] with θ hθ
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g θ))]
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hint_abs : IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ := by
    refine (hint_sq.add (integrable_const (1 : ℝ))).mono' ?_ ?_
    · simpa only [Real.norm_eq_abs] using hmeas.norm
    · filter_upwards with θ
      have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|g θ| - 1), sq_abs (g θ), abs_nonneg (g θ)]
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_abs] using h1
  refine ⟨hint_sq, hint_abs, ?_⟩
  refine integral_mono_ae hint_sq h hsq_le

/-- Cauchy–Schwarz on the slice: `∫|f| ≤ √(π/2) √(∫ f²)`. -/
private lemma integral_abs_le_sqrt_pi_div_two {f : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (h : IntegrableOn (fun x => f x ^ 2) Work.Spaces.Iθ) :
    ∫ x in Work.Spaces.Iθ, |f x|
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ x in Work.Spaces.Iθ, f x ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmeas_abs : AEStronglyMeasurable (fun x => |f x|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using hmeas.norm
  have hmemLp_abs : MemLp (fun x => |f x|) 2 (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq hmeas_abs).mpr ?_
    refine h.congr (Eventually.of_forall (fun x => (sq_abs (f x)).symm))
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := memLp_const 1
  have hcs : |∫ x in Work.Spaces.Iθ, |f x| * 1|
      ≤ Real.sqrt (∫ x in Work.Spaces.Iθ, |f x| ^ 2)
        * Real.sqrt (∫ x in Work.Spaces.Iθ, (1 : ℝ) ^ 2) := by
    simpa only [mul_one] using Ebs.abs_integral_mul_le_sqrt hmemLp_abs hone
  have hInt1 : (∫ x in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, one_pow, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hsq : (∫ x in Work.Spaces.Iθ, |f x| ^ 2) = ∫ x in Work.Spaces.Iθ, f x ^ 2 :=
    integral_congr_ae (Eventually.of_forall (fun x => sq_abs (f x)))
  have hnonneg : 0 ≤ ∫ x in Work.Spaces.Iθ, |f x| :=
    integral_nonneg (fun x => abs_nonneg (f x))
  simp only [mul_one] at hcs
  rw [hsq, hInt1, abs_of_nonneg hnonneg, mul_comm] at hcs
  exact hcs

/-- A bound for `deriv u` on the *open* interval extends to the closed interval: at an endpoint
either `u` fails to be differentiable there (and Mathlib's `deriv` is `0`), or the two-sided
derivative agrees with the one-sided limit of the slopes, which the mean value theorem bounds by
the interior bound. -/
private lemma deriv_endpoint_bound {u : ℝ → ℝ} {K a b : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ u (Set.Ioo a b))
    (hbd : ∀ t ∈ Set.Ioo a b, |deriv u t| ≤ K) :
    ∀ x ∈ Set.Icc a b, |deriv u x| ≤ K := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rw [← hxa]
    by_cases hd : DifferentiableAt ℝ u a
    · have hev : ∀ᶠ θ in 𝓝[>] a, |slope u a θ| ≤ K := by
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hab)] with θ h1 h2
        obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u h1
          (hcont.mono (fun t ht => ⟨ht.1, le_trans ht.2 h2.le⟩))
          (hdiff.mono (fun t ht => ⟨ht.1, lt_trans ht.2 h2⟩))
        rw [slope_def_field, ← hcs]
        exact hbd c ⟨hc.1, lt_trans hc.2 h2⟩
      have hslope : Tendsto (slope u a) (𝓝[>] a) (𝓝 (deriv u a)) :=
        hd.hasDerivAt.tendsto_slope.mono_left
          (nhdsWithin_mono a (fun t ht => ne_of_gt ht))
      simpa using le_of_tendsto hslope.abs hev
    · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      exact hK
  · rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · rw [hxb]
      by_cases hd : DifferentiableAt ℝ u b
      · have hev : ∀ᶠ θ in 𝓝[<] b, |slope u b θ| ≤ K := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Ioi_mem_nhds hab)] with θ h1 h2
          obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u h1
            (hcont.mono (fun t ht => ⟨le_trans h2.le ht.1, ht.2⟩))
            (hdiff.mono (fun t ht => ⟨lt_trans h2 ht.1, ht.2⟩))
          have hθb : θ < b := h1
          have hne1 : θ - b ≠ 0 := sub_ne_zero.mpr (by linarith : θ ≠ b)
          have hne2 : b - θ ≠ 0 := sub_ne_zero.mpr (by linarith : b ≠ θ)
          have hsl : slope u b θ = (u b - u θ) / (b - θ) := by
            rw [slope_def_field, div_eq_div_iff hne1 hne2]
            ring
          rw [hsl, ← hcs]
          exact hbd c ⟨lt_trans h2 hc.1, hc.2⟩
        have hslope : Tendsto (slope u b) (𝓝[<] b) (𝓝 (deriv u b)) :=
          hd.hasDerivAt.tendsto_slope.mono_left
            (nhdsWithin_mono b (fun t ht => ne_of_lt ht))
        simpa using le_of_tendsto hslope.abs hev
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        exact hK
    · exact hbd x ⟨hxa, hxb⟩

/-- A pointwise inequality on the open interval extends to the closed interval when both sides
are continuous there. -/
private lemma le_on_Icc_of_le_on_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ x ∈ Set.Ioo a b, f x ≤ g x) : ∀ x ∈ Set.Icc a b, f x ≤ g x := by
  intro x hx
  have hxcl : x ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]; exact hx
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hxcl
  have hut' : Tendsto u atTop (𝓝[Set.Icc a b] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hut, Eventually.of_forall (fun n =>
      ⟨le_of_lt (hu n).1, le_of_lt (hu n).2⟩)⟩
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) :=
    Tendsto.comp (show Tendsto f (𝓝[Set.Icc a b] x) (𝓝 (f x)) from hf.continuousWithinAt hx)
      hut'
  have hgu : Tendsto (fun n => g (u n)) atTop (𝓝 (g x)) :=
    Tendsto.comp (show Tendsto g (𝓝[Set.Icc a b] x) (𝓝 (g x)) from hg.continuousWithinAt hx)
      hut'
  exact le_of_tendsto_of_tendsto hfu hgu (Eventually.of_forall (fun n => h (u n) (hu n)))

/-- Pointwise `L^∞` bounds on a slice from its weighted `L²` data.

For `u` of class `C³` on `(0, π/2)`, continuous on `[0, π/2]`, with `u (π/2) = 0` and
`(u'')²·sEta`, `(u')²` integrable on `Iθ = [0, π/2]` (here `sEta = sin(2θ)^{-η} ≥ 1`), one has
for every `θ ∈ Iθ`

`|u' θ| ≤ C (√(∫ (u'')² sEta) + √(∫ (u')²))`   and
`|u θ| ≤ (π/2 - θ) · C (√(∫ (u'')² sEta) + √(∫ (u')²))`.

Route: `(u'')² ≤ (u'')² sEta` is integrable, so `|u''|` is integrable; by the mean-value
property of the integral there is `x₀ ∈ [π/4, 3π/8]` with
`|u' x₀|² ≤ (∫_{[π/4,3π/8]} (u')²)/(π/8)`, and then for any `θ ∈ Iθ` the fundamental fact of
calculus gives `|u' θ| ≤ |u' x₀| + ∫_{Iθ} |u''|`, which Cauchy–Schwarz
(`Work.Spaces.cs_integral`) bounds by `C(√(∫(u')²) + √(∫(u'')² sEta))`.  The bound for `u`
follows from `u (π/2) = 0` and `|u θ| ≤ (π/2 - θ) · sup|u'|`. -/
theorem slice_bd_sup_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      (∀ θ ∈ Work.Spaces.Iθ,
          |deriv u θ| ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)))
        ∧ (∀ θ ∈ Work.Spaces.Iθ,
          |u θ| ≤ (Real.pi / 2 - θ) * C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro u h3 hcont hu_pi hInt2 hInt1
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    h3.differentiableOn (by norm_num)
  have h2 : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
  have h2cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := h2.continuousOn
  -- integrability of the second derivative and the `L¹` bound
  have hmeas2 : AEStronglyMeasurable (deriv (deriv u)) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv (deriv u)).aestronglyMeasurable
  obtain ⟨hInt2', hInt2abs, hInt2le⟩ := integrableOn_sq_of_sq_mul_sEta hmeas2 hInt2
  have hL1le : (∫ θ in Work.Spaces.Iθ, |deriv (deriv u) θ|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt A := by
    have hcs := integral_abs_le_sqrt_pi_div_two hmeas2 hInt2'
    have hmono : Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2)
        ≤ Real.sqrt A := by
      rw [hAdef]; exact Real.sqrt_le_sqrt hInt2le
    exact le_trans hcs (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _))
  -- the mean-value point in the middle of the slice
  have hderiv_cont : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) (3 * Real.pi / 8)) :=
    h2cont.mono (fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  obtain ⟨x0, hx0mem, hx0eq⟩ := exists_eq_average (f := fun θ => (deriv u θ) ^ 2)
    (by linarith [Real.pi_pos] : Real.pi / 4 < 3 * Real.pi / 8) (hderiv_cont.pow 2)
  have hx0Ioo : x0 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hx0mem.1, Real.pi_pos], by linarith [hx0mem.2, Real.pi_pos]⟩
  have hBsub : (∫ θ in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u θ) ^ 2) ≤ B := by
    rw [hBdef]
    refine MeasureTheory.setIntegral_mono_set hInt1
      (Eventually.of_forall (fun t => sq_nonneg _)) ?_
    exact Eventually.of_forall (fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hx0bd : |deriv u x0| ≤ Real.sqrt (8 / Real.pi) * Real.sqrt B := by
    have hsq : (deriv u x0) ^ 2 ≤ (8 / Real.pi) * B := by
      have hden : (3 * Real.pi / 8 - Real.pi / 4) = Real.pi / 8 := by ring
      rw [hx0eq, hden, div_eq_mul_inv, inv_div]
      have hcomm : (∫ t in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u t) ^ 2)
          * (8 / Real.pi)
          = (8 / Real.pi)
            * (∫ t in Set.Icc (Real.pi / 4) (3 * Real.pi / 8), (deriv u t) ^ 2) := by
        ring
      rw [hcomm]
      exact mul_le_mul_of_nonneg_left hBsub (by positivity)
    have h2' : Real.sqrt ((deriv u x0) ^ 2) ≤ Real.sqrt ((8 / Real.pi) * B) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 8 / Real.pi)] at h2'
    simpa only [Real.sqrt_sq_eq_abs] using h2'
  -- the estimate on the open interval
  have hmain : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv u θ| ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.uIcc x0 θ) := by
      refine (h2.mono ?_).of_le (by norm_num)
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hx0Ioo.1 h1, lt_of_le_of_lt h2 hθ.2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hx0Ioo.2⟩
    have hFTC : (∫ t in x0..θ, deriv (deriv u) t) = deriv u θ - deriv u x0 :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc h1
    have hstep : |deriv u θ - deriv u x0| ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv u) t| := by
      rw [← hFTC]
      rcases le_total x0 θ with hle | hle
      · have hb : |∫ t in x0..θ, deriv (deriv u) t|
            ≤ ∫ t in x0..θ, |deriv (deriv u) t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
        have he : (∫ t in x0..θ, |deriv (deriv u) t|)
            = ∫ t in Set.Icc x0 θ, |deriv (deriv u) t| := by
          rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [he] at hb
        exact le_trans hb (MeasureTheory.setIntegral_mono_set hInt2abs
          (Eventually.of_forall (fun t => abs_nonneg _))
          (Eventually.of_forall (fun t ht =>
            ⟨le_trans (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 4)
              (le_trans hx0mem.1 ht.1), le_trans ht.2 hθI.2⟩)))
      · have hsym : (∫ t in x0..θ, deriv (deriv u) t)
            = -(∫ t in θ..x0, deriv (deriv u) t) :=
          intervalIntegral.integral_symm θ x0
        rw [hsym, abs_neg]
        have hb : |∫ t in θ..x0, deriv (deriv u) t|
            ≤ ∫ t in θ..x0, |deriv (deriv u) t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
        have he : (∫ t in θ..x0, |deriv (deriv u) t|)
            = ∫ t in Set.Icc θ x0, |deriv (deriv u) t| := by
          rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
        rw [he] at hb
        exact le_trans hb (MeasureTheory.setIntegral_mono_set hInt2abs
          (Eventually.of_forall (fun t => abs_nonneg _))
          (Eventually.of_forall (fun t ht =>
            ⟨le_trans hθI.1 ht.1,
              le_trans (le_trans ht.2 hx0mem.2) (by linarith [Real.pi_pos])⟩)))
    have htri : |deriv u θ| ≤ |deriv u x0| + |deriv u θ - deriv u x0| := by
      have h := abs_add_le (deriv u x0) (deriv u θ - deriv u x0)
      have he : deriv u x0 + (deriv u θ - deriv u x0) = deriv u θ := by ring
      rwa [he] at h
    have hnum1 : Real.sqrt (8 / Real.pi) ≤ 2 := by
      have h4 : (8 : ℝ) / Real.pi ≤ 4 := by
        rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
      have h5 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h6] at h5
    have hnum2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
      have h4 : Real.pi / 2 ≤ 4 := by linarith [Real.pi_lt_four]
      have h5 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h6] at h5
    calc |deriv u θ| ≤ |deriv u x0| + |deriv u θ - deriv u x0| := htri
      _ ≤ Real.sqrt (8 / Real.pi) * Real.sqrt B + Real.sqrt (Real.pi / 2) * Real.sqrt A :=
          add_le_add hx0bd (le_trans hstep hL1le)
      _ ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
          have hA0 : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
          have hB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg _
          have h1' := mul_le_mul_of_nonneg_right hnum1 hB0
          have h2' := mul_le_mul_of_nonneg_right hnum2 hA0
          linarith
  -- the estimate on the closed interval
  have hK0 : (0 : ℝ) ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    have hA0 : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg _
    linarith
  have hderiv_bd : ∀ x ∈ Work.Spaces.Iθ, |deriv u x| ≤ 2 * (Real.sqrt A + Real.sqrt B) :=
    deriv_endpoint_bound hpi2 hK0 hcont hdiff hmain
  -- the estimate for `u` itself
  have hu_Ioo : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      |u x| ≤ (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) := by
    intro x hx
    obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope u hx.2
      (hcont.mono (fun t ht => ⟨le_trans hx.1.le ht.1, ht.2⟩))
      (hdiff.mono (fun t ht => ⟨lt_trans hx.1 ht.1, ht.2⟩))
    have hpos : 0 < Real.pi / 2 - x := by linarith [hx.2]
    have hcbd : |deriv u c| ≤ 2 * (Real.sqrt A + Real.sqrt B) :=
      hderiv_bd c ⟨le_trans hx.1.le hc.1.le, hc.2.le⟩
    have hid : deriv u c = -(u x) / (Real.pi / 2 - x) := by
      rw [hcs, hu_pi]; ring
    rw [hid, abs_div, abs_neg, abs_of_pos hpos] at hcbd
    rw [div_le_iff₀ hpos] at hcbd
    calc |u x| ≤ 2 * (Real.sqrt A + Real.sqrt B) * (Real.pi / 2 - x) := hcbd
      _ = (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) := by ring
  have hu_bd : ∀ x ∈ Work.Spaces.Iθ,
      |u x| ≤ (Real.pi / 2 - x) * (2 * (Real.sqrt A + Real.sqrt B)) :=
    le_on_Icc_of_le_on_Ioo hpi2 hcont.abs
      (((continuous_const.sub continuous_id).mul continuous_const).continuousOn) hu_Ioo
  constructor
  · simpa only [hAdef, hBdef] using hderiv_bd
  · simpa only [hAdef, hBdef, mul_assoc] using hu_bd

end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ### Two elementary bridges between `deriv` and `iteratedDeriv` -/

/-- A `C^n` function has a `C^{n-k}` `k`-th derivative (for the one-dimensional `deriv`). -/
private lemma contDiffAt_iteratedDeriv_aux {f : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f x) (hk : k ≤ n) :
    ContDiffAt ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have h1 : n - k - 1 + 1 = n - k := by omega
      have hle : ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((n - k : ℕ) : WithTop ℕ∞) := by
        rw [show ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 = (((n - k - 1) + 1 : ℕ) : WithTop ℕ∞) from by
          push_cast; ring, h1]
      have hstep : ContDiffAt ℝ ((n - k - 1 : ℕ) : WithTop ℕ∞) (deriv (iteratedDeriv k f)) x :=
        (ih hk').derivWithin (m := ((n - k - 1 : ℕ) : WithTop ℕ∞)) hle
      convert hstep using 2
      exact iteratedDeriv_succ

/-- The second `iteratedDeriv` is the second `deriv`. -/
private lemma itd_two_aux (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The third `iteratedDeriv` is the third `deriv`. -/
private lemma itd_three_aux (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, itd_two_aux]

/-- One `iteratedDeriv` on top of a `k`-th one is the `(k+1)`-st one. -/
private lemma itd_comp_one_val_aux (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) x = iteratedDeriv (n + 1) f x := by
  rw [iteratedDeriv_one, ← iteratedDeriv_succ]

/-- `deriv (deriv f)` written with an explicit `λ`, as `iteratedDeriv 2 f`. -/
private lemma itd_two_lambda_val (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun t => deriv f t) x = iteratedDeriv 2 f x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-! ### The identity -/

theorem slice_gprime_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = - deriv (deriv (deriv u)) θ
        + deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ - 6 * deriv u θ := by
  intro θ hθ
  -- `g` and `Lzero1 u` agree in a neighbourhood of `θ`, so their derivatives do too
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hg_ev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u := by
    filter_upwards [hIoo] with t ht
    exact (hg t ht).symm
  rw [hg_ev.deriv_eq]
  -- `tan` is smooth at `θ`
  have hcosθ : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [hθ.1, Real.pi_pos]
    · linarith [hθ.2, Real.pi_pos]
  have huC1 : ContDiffAt ℝ 1 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have htuC2 : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ :=
    (Real.contDiffAt_tan.mpr hcosθ).mul huC2
  -- `Lzero1 u` as a function, in terms of `iteratedDeriv`
  have hL_eq : Work.FTS.EllipticEst.Lzero1 u
      = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
        - (fun t => 6 * u t) := by
    funext t
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by
      rw [iteratedDeriv_one]
    unfold Work.FTS.EllipticEst.Lzero1
    rw [hd2, hd1]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  -- smoothness of the two pieces of `hL_eq`
  have hu2C1 : ContDiffAt ℝ 1 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv_aux (f := u) (n := 3) (k := 2) (hu.contDiffAt hIoo) (by norm_num)
  have htu1C1 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv_aux (f := fun s => Real.tan s * u s) (n := 2) (k := 1) htuC2
      (by norm_num)
  -- the first derivative of `Lzero1 u`, in `iteratedDeriv` form
  have hL1 : iteratedDeriv 1 (Work.FTS.EllipticEst.Lzero1 u) θ
      = -iteratedDeriv 3 u θ + iteratedDeriv 2 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 1 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 1
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C1).add htu1C1
    have hB : ContDiffAt ℝ 1 (fun t => 6 * u t) θ := contDiffAt_const.mul huC1
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 1 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C1
    rw [iteratedDeriv_add hA1 htu1C1, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC1]
    rw [itd_comp_one_val_aux 2 u θ, itd_comp_one_val_aux 1 (fun s => Real.tan s * u s) θ]
  -- transport the four `deriv` slots of the goal into `iteratedDeriv` form
  have h1 : deriv (Work.FTS.EllipticEst.Lzero1 u) θ
      = iteratedDeriv 1 (Work.FTS.EllipticEst.Lzero1 u) θ := by rw [iteratedDeriv_one]
  have h2 : deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv 2 (fun s => Real.tan s * u s) θ := itd_two_lambda_val _ _
  have h3 : deriv (deriv (deriv u)) θ = iteratedDeriv 3 u θ := by rw [← itd_three_aux u]
  have h4 : deriv u θ = iteratedDeriv 1 u θ := by rw [iteratedDeriv_one]
  rw [h1, h2, h3, h4]
  exact hL1

end Work.FTS.EllipticEst.remov
end
end
