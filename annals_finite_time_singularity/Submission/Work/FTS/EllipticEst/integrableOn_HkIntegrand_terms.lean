import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.Coercivity.Dz_alg =====
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

/-- **Algebraic identity.**  With `D_z f z θ = z ∂_z f z θ` and `w z = (1+z)²/z²`,
for `z ≠ 0`

  `z (D_z f z θ · w z)² = (∂_z f z θ)² (1+z)^4 / z`. -/
theorem zw_sq_factor (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ≠ 0) :
    z * (Spaces.Dz f z θ * Spaces.w z) ^ 2
      = (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z := by
  simp only [Spaces.Dz, Spaces.w]
  field_simp


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.EL12z_ae_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter

/-- If `(z,θ) ↦ (f z θ · w z)²` is integrable on `Iz ×ˢ Iθ`, then for almost every
`z ∈ (0,∞)` the `θ`-slice `θ ↦ f z θ` is square integrable on `Iθ`.

This is Fubini/Tonelli for the slice integral, together with the fact that the radial
weight `w z = (1+z)²/z²` is non-zero for every `z > 0` (so that the factor `w z` can be
divided out). -/
theorem EL12z_ae_slice (f : ℝ → ℝ → ℝ)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ := by
  set g : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) with hg
  -- `Iz ×ˢ Iθ` carries the product of the two restricted measures
  have hInt : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hfw
  -- Fubini: almost every `z`-slice is integrable
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable (fun θ => g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hInt.prod_right_ae
  -- `(0,∞)` and `Iz = [0,∞)` differ by the null point `0`
  have hmono : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ≤
      (MeasureTheory.volume.restrict Spaces.Iz) :=
    MeasureTheory.Measure.restrict_mono_set volume
      (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  have hs : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.Integrable (fun θ => g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    MeasureTheory.ae_mono hmono hslice
  filter_upwards [hs,
    MeasureTheory.ae_restrict_mem
      (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hzsl hzpos
  have hzpos' : (0 : ℝ) < z := hzpos
  -- the radial weight does not vanish on `(0,∞)`
  have hzw : Spaces.w z ≠ 0 := by
    have h1 : (1 + z) ≠ 0 := by linarith
    have h2 : z ≠ 0 := ne_of_gt hzpos'
    simp only [Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2)
  -- divide the slice integrand by `(w z)²`, which is legitimate as `w z ≠ 0`
  have h2 : MeasureTheory.Integrable
      (fun θ => ((Spaces.w z) ^ 2)⁻¹ * g (z, θ))
        (MeasureTheory.volume.restrict Spaces.Iθ) :=
    hzsl.const_mul _
  refine h2.congr ?_
  filter_upwards with θ
  simp only [hg, Function.uncurry_apply_pair]
  rw [mul_pow, inv_mul_eq_div]
  field_simp

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.EL12z_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter

/-- The plain `1/z²` piece of the weighted `L²` energy `Ef`:

`∫_{z>0} (∫_θ f(z,θ)² dθ)/z² ≤ ∫∫_{[0,∞)×[0,π/2]} (f(z,θ) w(z))² dθ dz`.

The point is simply that `1/z² ≤ w(z)²` on `(0,∞)`, where `w(z) = (1+z)²/z²`;
the hypothesis `hfw` (joint integrability of `(f w)²`) is used through Fubini to
make the right-hand side available as an integrable majorant. -/
theorem EL12z_weight (f : ℝ → ℝ → ℝ)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2 ≤ Ef f := by
  -- abbreviations for the two slice integrals
  set G : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (f z θ) ^ 2 with hGdef
  set H : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2 with hHdef
  set g : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2) with hgdef
  -- joint integrability of `(z,θ) ↦ (f z θ w z)²` on the product `Iz ×ˢ Iθ`
  have hInt : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hfw
  -- Fubini: the `θ`-slice integrals form an integrable function of `z`
  have hH_int : MeasureTheory.Integrable H (MeasureTheory.volume.restrict Spaces.Iz) := by
    have h := hInt.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgdef, Function.uncurry_apply_pair, hHdef]
  -- the slice integrals of `(f w)²` are the pointwise product `w² · G`
  have hHeq : H =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => (Spaces.w z) ^ 2 * G z) := by
    filter_upwards with z
    simp only [hHdef, hGdef]
    calc ∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2
        = ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * (f z θ) ^ 2 := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun θ => ?_)
          ring
      _ = (Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2 :=
          MeasureTheory.integral_const_mul _ _
  -- `(0,∞) ⊆ Iz = [0,∞)`, so integrability descends to the smaller measure
  have hle : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      ≤ MeasureTheory.volume.restrict Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set volume
      (fun x hx => le_of_lt (Set.mem_Ioi.mp hx))
  have hH_int' : MeasureTheory.Integrable H
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH_int.mono_measure hle
  have hGint : MeasureTheory.Integrable (fun z => (Spaces.w z) ^ 2 * G z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hH_int'.congr hHeq
  -- `G z ≥ 0`
  have hG_nonneg : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ G z := by
    intro z _
    simp only [hGdef]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- the pointwise comparison `1/z² ≤ w(z)²` on `(0,∞)`
  have hineq_all : ∀ z ∈ Set.Ioi (0 : ℝ), (z ^ 2)⁻¹ ≤ (Spaces.w z) ^ 2 := by
    intro z hz
    have hzpos : 0 < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    rw [Spaces.w]
    field_simp
    nlinarith [sq_nonneg z]
  -- main comparison, with `w² · G` as integrable majorant
  have hmain : ∫ z in Set.Ioi (0 : ℝ), G z / z ^ 2
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hz
      exact div_nonneg (hG_nonneg z hz) (sq_nonneg z)
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet (Set.Ioi (0 : ℝ)) from isOpen_Ioi.measurableSet)] with z hz
      have hGz := hG_nonneg z hz
      rw [div_eq_mul_inv]
      calc G z * (z ^ 2)⁻¹ ≤ G z * (Spaces.w z) ^ 2 :=
            mul_le_mul_of_nonneg_left (hineq_all z hz) hGz
        _ = (Spaces.w z) ^ 2 * G z := by ring
  -- identify the majorant integral with `Ef f`
  have hEq : ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z = Ef f := by
    have h6a : ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z
        = ∫ z in Set.Ioi (0 : ℝ), H z :=
      MeasureTheory.integral_congr_ae hHeq.symm
    have h6b : ∫ z in Set.Ioi (0 : ℝ), H z = ∫ z in Spaces.Iz, H z := by
      rw [Spaces.Iz]
      exact MeasureTheory.integral_Ici_eq_integral_Ioi.symm
    have h6c : ∫ z in Spaces.Iz, H z = Ef f := by
      simp only [Ef, Spaces.L2Sq, hHdef]
    rw [h6a, h6b, h6c]
  calc ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), G z / z ^ 2 := by simp only [hGdef]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), (Spaces.w z) ^ 2 * G z := hmain
    _ = Ef f := hEq

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.H1IP_homog =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory

/-! ## Elementary algebra of `deriv` and of the weighted pairing -/

/-- `deriv` is scalar homogeneous **unconditionally**: unlike `deriv_const_mul` there is
no differentiability hypothesis, because if `d` is not differentiable at `x` then neither
is `c * d` (for `c ≠ 0`), so both sides vanish. -/
theorem deriv_const_mul_uncond (c : ℝ) (d : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => c * d y) x = c * deriv d x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hd : DifferentiableAt ℝ d x
    · exact deriv_const_mul c hd
    · have hcd : ¬ DifferentiableAt ℝ (fun y => c * d y) x := by
        intro h
        have h2 : DifferentiableAt ℝ (fun y => c⁻¹ * (c * d y)) x := h.const_mul c⁻¹
        refine hd ?_
        refine h2.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [hc]
      rw [deriv_zero_of_not_differentiableAt hcd, deriv_zero_of_not_differentiableAt hd,
        mul_zero]

/-- Scalar homogeneity of the weighted `L²` pairing in its first argument.  No
integrability or measurability hypothesis is needed: the identity is pointwise in the
integrand, and the total Bochner integral is homogeneous under scalar multiplication. -/
theorem wip_smul_left {ρ A B : ℝ → ℝ → ℝ} {c : ℝ} :
    wip ρ (fun z θ => c * A z θ) B = c * wip ρ A B := by
  rw [wip, wip]
  have h : (fun z => ∫ θ in Spaces.Iθ, (c * A z θ) * B z θ * ρ z θ)
      = fun z => c * ∫ θ in Spaces.Iθ, A z θ * B z θ * ρ z θ := by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with θ
    ring
  simp only [h]
  rw [MeasureTheory.integral_const_mul]

/-- The radial derivative `D_z` is scalar homogeneous. -/
theorem Dz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Spaces.Dz f z θ := by
  funext z θ
  simp only [Spaces.Dz, Spaces.pz]
  rw [deriv_const_mul_uncond]
  ring

/-- The angular derivative `D_θ` is scalar homogeneous. -/
theorem Dth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Spaces.Dth f z θ := by
  funext z θ
  simp only [Spaces.Dth, Spaces.pth]
  rw [deriv_const_mul_uncond]
  ring

/-! ## Homogeneity of `H1IP` -/

theorem H1IP_homog (α : ℝ) (c : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α (fun z θ => c * f z θ) g = c * Work.Coercivity.H1IP α f g := by
  rw [H1IP, H1IP, Dz_smul, Dth_smul, wip_smul_left, wip_smul_left, wip_smul_left,
    wip_smul_left]
  ring

end

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.H1IP_nonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- Diagonal `wip`-inner products against a weight that is nonnegative on the angular
interval `Iθ` are nonnegative.  This is the only positivity input needed for
`H1IP_nonneg`: the integrand is `g z θ * g z θ * ρ z θ`, a square times the weight. -/
theorem wip_self_nonneg {ρ g : ℝ → ℝ → ℝ} (hρ : ∀ z θ, θ ∈ Spaces.Iθ → 0 ≤ ρ z θ) :
    0 ≤ wip ρ g g := by
  unfold wip
  refine setIntegral_nonneg ?_ ?_
  · simp only [Spaces.Iz]; exact measurableSet_Ici
  · intro z _
    refine setIntegral_nonneg ?_ ?_
    · simp only [Spaces.Iθ]; exact measurableSet_Icc
    · intro θ hθ
      exact mul_nonneg (mul_self_nonneg (g z θ)) (hρ z θ hθ)

theorem H1IP_nonneg (α : ℝ) (h : ℝ → ℝ → ℝ) : 0 ≤ Work.Coercivity.H1IP α h h := by
  have hsin : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2])
  have hDz : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz h) (Spaces.Dz h) :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hEta : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) h h :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hW : 0 ≤ wip (fun z _ => Spaces.w z ^ 2) h h :=
    wip_self_nonneg (fun z _ _ => sq_nonneg _)
  have hDth : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth h) (Spaces.Dth h) :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  unfold H1IP
  have e1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hDz
  have e2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 10) hEta
  have e3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 17) hW
  have e4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 21) hDth
  linarith

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.HkIntegrand_succ_le_sum =====
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

/-! ## Elementary one-dimensional sum lemmas -/

/-- The pure `D_z` family grows by one summand in the obvious way: the sum over
`range (k+2)` is dominated by the sum over `range (k+1)` of the same terms plus the
sum over `range (k+1)` of the shifted terms `te (i+1)`. -/
private lemma sum_range_succ_le_self_add_shift (te : ℕ → ℝ) (h : ∀ i, 0 ≤ te i) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 2), te i)
      ≤ (∑ i ∈ Finset.range (k + 1), te i) + ∑ i ∈ Finset.range (k + 1), te (i + 1) := by
  rw [Finset.sum_range_succ (f := te) (n := k + 1)]
  have h1 : te (k + 1) ≤ ∑ i ∈ Finset.range (k + 1), te (i + 1) :=
    Finset.single_le_sum (f := fun i => te (i + 1)) (fun i _ => h (i + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  linarith

/-- The `a = 1` row of a double sum restricted by `1 ≤ a ∧ a + b ≤ k` is the plain
sum `∑_{b<k} g b`: the extra index `b = k` of `range (k+1)` is killed by the bound. -/
private lemma row_one_ite_eq (g : ℕ → ℝ) (k : ℕ) :
    (∑ b ∈ Finset.range (k + 1), (if 1 ≤ (1 : ℕ) ∧ 1 + b ≤ k then g b else 0))
      = ∑ b ∈ Finset.range k, g b := by
  rw [Finset.sum_range_succ]
  have hz : (if 1 ≤ (1 : ℕ) ∧ 1 + k ≤ k then g k else 0) = 0 := by
    rw [ite_eq_right (by omega)]
  rw [hz, add_zero]
  exact Finset.sum_congr rfl (fun b hb => by
    rw [Finset.mem_range] at hb
    rw [ite_eq_left (by omega)])

/-- Splitting one term off a sum over `range (k+1)`: the head is bounded by the sum
over `range k` (the missing index `0` is present for `1 ≤ k`). -/
private lemma row_shift_union (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range (k + 1), g i)
      ≤ (∑ i ∈ Finset.range k, g i) + ∑ i ∈ Finset.range k, g (i + 1) := by
  rw [Finset.sum_range_succ']
  have h0 : g 0 ≤ ∑ i ∈ Finset.range k, g i :=
    Finset.single_le_sum (fun i _ => hg i) (Finset.mem_range.mpr (by omega))
  linarith

/-- The `a = 1` row (with `b < k` and the shift by one in the second index) is
dominated by the double triangle sum. -/
private lemma row_one_shift_le_double (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) (k : ℕ)
    (hk : 1 ≤ k) :
    (∑ b ∈ Finset.range k, G 1 (b + 1))
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0) := by
  have h1 : (1 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (f := fun a => ∑ j ∈ Finset.range (k + 1), (if 1 ≤ a ∧ a + j ≤ k then G a (j + 1) else 0))
    (fun a _ => Finset.sum_nonneg fun j _ => by split_ifs with h; exact hG a (j + 1); exact le_refl 0)
    h1
  have heq : (∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ (1 : ℕ) ∧ 1 + j ≤ k then G 1 (j + 1) else 0))
      = ∑ b ∈ Finset.range k, G 1 (b + 1) :=
    row_one_ite_eq (fun b => G 1 (b + 1)) k
  rw [← heq]
  exact hsingle

/-- The `a = 1` row (with `b < k`) is dominated by the double triangle sum. -/
private lemma row_one_le_double (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) (k : ℕ) (hk : 1 ≤ k) :
    (∑ b ∈ Finset.range k, G 1 b)
      ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
  have h1 : (1 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (f := fun a => ∑ b ∈ Finset.range (k + 1), (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
    (fun a _ => Finset.sum_nonneg fun b _ => by split_ifs with h; exact hG a b; exact le_refl 0) h1
  have heq : (∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ (1 : ℕ) ∧ 1 + b ≤ k then G 1 b else 0))
      = ∑ b ∈ Finset.range k, G 1 b :=
    row_one_ite_eq (fun b => G 1 b) k
  rw [← heq]
  exact hsingle

/-! ## The abstract mixed-index inequality -/

/-- **Combinatorial core.**  For a nonnegative double sequence `G` and `k ≥ 1`, the
triangle sum over `{(a,b) : 1 ≤ a, a+b ≤ k+1}` is dominated by the sum of the
unshifted triangle `{(a,b) : 1 ≤ a, a+b ≤ k}` and the two shifted triangles
obtained by raising one index by one (`G i (j+1)` and `G (i+1) j`).

This is exactly the index reshuffling needed to compare `M_{k+1}` with
`M_k + M_k(D_z f) + M_k(D_θ f)`: the old part `a+b ≤ k` is the unshifted triangle,
while the new part `a+b = k+1` splits according to whether `b ≥ 1` (covered by the
`G i (j+1)` sum, via `SumShiftZ_le`-style shifting) or `b = 0` (covered by the
`G (i+1) j` sum). -/
theorem mixed_index_sum_le (k : ℕ) (hk : 1 ≤ k) (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) :
    (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0))
    ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G (i + 1) j else 0)) := by
  -- the triangle splits exactly into the `a = 1` row plus the shifted-in-`a` triangle
  have hrow : (∑ i ∈ Finset.range (k + 1), G 1 i)
      ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) := by
    have hc := row_shift_union (fun i => G 1 i) (fun i => hG 1 i) k hk
    have ha := row_one_le_double G hG k hk
    have hb := row_one_shift_le_double G hG k hk
    linarith
  have hkey := SumRowShift_eq k G
  linarith

/-! ## The target lemma -/

/-- **Coercivity of the `H^k`-integrand.**  For `SmoothNbhd f` and `k ≥ 1`, the
`(k+1)`-st `H`-integrand is pointwise dominated by the sum of the `k`-th integrands of
`f`, `D_θ f` and `D_z f`. -/
theorem HkIntegrand_succ_le_sum (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α (k + 1) f z θ
      ≤ Work.Spaces.HkIntegrand α k f z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
        + Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ := by
  simp only [Work.Spaces.HkIntegrand]
  -- the two fixed weights, isolated so that the sums of squares are honest
  set A : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hA
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  -- the curvilinear derivatives pick up exactly one more factor
  have hDzIter : ∀ i, Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (i + 1) f z θ :=
    fun i => by
      show Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter i f) z θ
      rw [show Work.Spaces.DzIter i (Work.Spaces.Dz f)
            = Work.Spaces.Dz (Work.Spaces.DzIter i f) from by
          simpa using (Work.Spaces.DzIter_add_right i 1 f).symm]
  have hmixDz : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ :=
    fun j i => by simpa using Work.Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ
  have hmixDth : ∀ j i, Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ = Work.Spaces.mixed j (i + 1) f z θ :=
    fun j i => by simpa using Work.Spaces.mixed_comm f hsm j i 0 1 z θ hz hθ
  -- rewrite the three summands of the right-hand side into the common index form
  have hBpure : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * A) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * A) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [hDzIter i]
  have hBmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDz j i]
  have hCmixed : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hmixDth j i]
  rw [hBpure, hBmixed, hCmixed]
  -- pure part: two consecutive levels of `D_z` cover `P_{k+1}`
  have hI := sum_range_succ_le_self_add_shift
    (fun i => (Work.Spaces.DzIter i f z θ * A) ^ 2) (fun i => sq_nonneg _) k
  -- mixed part: the combinatorial triangle inequality
  have hII := mixed_index_sum_le k hk
    (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  -- the pure family of `D_θ f` only helps
  have hDthnonneg : 0 ≤ ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * A) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.K_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- On `Iθ = [0,π/2]` the sine is nonnegative. -/
lemma K_facts_sin_nonneg {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin θ := by
  rw [Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])

/-- `cos²θ ≤ 1` for every real `θ`. -/
lemma K_facts_cos_sq_le_one (θ : ℝ) : Real.cos θ ^ 2 ≤ 1 := by
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ - 1)]

/-- The angular weight `K` is continuous. -/
lemma K_facts_continuous : Continuous Spaces.K := by
  unfold Spaces.K
  fun_prop

/-- `K` is nonnegative on `Iθ`. -/
lemma K_facts_nonneg : ∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ := by
  intro θ hθ
  have h1 : 0 ≤ Real.sin θ := K_facts_sin_nonneg hθ
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
  simp only [Spaces.K]
  nlinarith

/-- `K` is bounded by `3` on `Iθ`. -/
lemma K_facts_le_three : ∀ θ ∈ Spaces.Iθ, Spaces.K θ ≤ 3 := by
  intro θ hθ
  have h1 : 0 ≤ Real.sin θ := K_facts_sin_nonneg hθ
  have h1' : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := K_facts_cos_sq_le_one θ
  have h2' : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
  simp only [Spaces.K]
  nlinarith

/-- `K ^ 2` is integrable on the compact interval `Iθ`. -/
lemma K_facts_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun θ => (Spaces.K θ) ^ 2) Spaces.Iθ := by
  rw [Spaces.Iθ]
  exact (K_facts_continuous.pow 2).integrableOn_Icc

/-- Elementary facts about the angular weight `K θ = 3 sin θ cos²θ` on `Iθ = [0, π/2]`:
it is nonnegative, `K θ ^ 2 ≤ 3 * K θ` pointwise (as `K ≤ 3` there), its integral is `1`
(antiderivative `-cos³θ`), and consequently `∫ K² ≤ 3`.

Intended proof: on `Iθ`, `0 ≤ sin θ` and `0 ≤ cos θ ^ 2`, hence `0 ≤ K θ`; `sin θ ≤ 1` and
`cos θ ^ 2 ≤ 1` give `K θ ≤ 3`; thus `K θ ^ 2 ≤ 3 * K θ`. For the integral value use the
calculus identity via `HasDerivAt (fun θ => -(Real.cos θ)^3) (K θ) θ` together with
`intervalIntegral` (after rewriting `∫ θ in Iθ, g θ = ∫ θ in (0:ℝ)..(π/2), g θ`), which
gives `∫ θ in Iθ, K θ = -cos(π/2)^3 + cos 0^3 = 1`. Finally `∫ K² ≤ ∫ 3 * K = 3 * ∫ K = 3`
by integral monotonicity on `Iθ` (`IntegrableOn` of both `K` and `K ^ 2` follows from
continuity on the compact `Iθ`), or directly by the pointwise bound `K ≤ 3`. -/
theorem K_facts :
    (∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ) ∧
      (∀ θ ∈ Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 3 * Spaces.K θ) ∧
        (∫ θ in Spaces.Iθ, Spaces.K θ) = 1 ∧
          (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3 := by
  have hKsq : ∀ θ ∈ Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 3 * Spaces.K θ := by
    intro θ hθ
    calc (Spaces.K θ) ^ 2 = Spaces.K θ * Spaces.K θ := by ring
      _ ≤ 3 * Spaces.K θ :=
          mul_le_mul_of_nonneg_right (K_facts_le_three θ hθ) (K_facts_nonneg θ hθ)
  have hInt3K : MeasureTheory.IntegrableOn (fun θ => 3 * Spaces.K θ) Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact (K_facts_continuous.const_mul 3).integrableOn_Icc
  have hIθmeas : MeasurableSet Spaces.Iθ := by
    rw [Spaces.Iθ]; exact measurableSet_Icc
  have hmono :
      (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ ∫ θ in Spaces.Iθ, 3 * Spaces.K θ :=
    MeasureTheory.setIntegral_mono_on K_facts_sq_integrableOn hInt3K hIθmeas hKsq
  have hconst : (∫ θ in Spaces.Iθ, 3 * Spaces.K θ) = 3 * ∫ θ in Spaces.Iθ, Spaces.K θ :=
    MeasureTheory.integral_const_mul 3 (fun θ => Spaces.K θ)
  have hlast : (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3 := by
    rw [hconst, integral_Itheta_K] at hmono
    linarith
  exact ⟨K_facts_nonneg, hKsq, integral_Itheta_K, hlast⟩

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.aesm_angAvg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.Coercivity

/-- The radial weight `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn (fun z : ℝ => Spaces.w z) (Set.Ioi 0) := by
  unfold Spaces.w
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)



end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.bd0_abs_div_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity



end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.contDiffOn_setIntegral_Itheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal NNReal ContDiff
open MeasureTheory Set Filter

namespace Work.Coercivity

/-! ### Auxiliary facts used in the proof below -/

-- (private helper)
-- (private helper)
-- (private helper)
-- (private helper)
-- (private helper)







end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.continuousOn_zw_sq_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity



end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.integrableOn_zw_sq_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.rpow_neg_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- For `x ≥ 0`, the square of `x ^ (-(γ/2))` is `x ^ (-γ)`. -/
theorem rpow_neg_sq (x γ : ℝ) (hx : 0 ≤ x) : (x ^ (-(γ / 2))) ^ 2 = x ^ (-γ) := by
  rw [← Real.rpow_natCast (x ^ (-(γ / 2))) 2]
  calc (x ^ (-(γ / 2))) ^ (2 : ℝ)
      = x ^ ((-(γ / 2)) * 2) := (Real.rpow_mul hx (-(γ / 2)) (2 : ℝ)).symm
    _ = x ^ (-γ) := by rw [show (-(γ / 2)) * 2 = -γ by ring]

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.slice_abs_le_sq_ftc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Coercivity


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.wip_eq_integral_prod =====
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

/-- The iterated integral defining `wip` agrees with the integral against the product
of the two restricted measures `(volume.restrict I_z) × (volume.restrict I_θ)`.

This is the Fubini bridge used to move between the two ways of writing the weighted
`L²` inner product `wip ρ g₁ g₂ = ∫∫ g₁ g₂ ρ`. -/
theorem wip_eq_integral_prod (ρ g₁ g₂ : ℝ → ℝ → ℝ)
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => g₁ z θ * g₂ z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ g₁ g₂
      = ∫ p : ℝ × ℝ, g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the product of the two restricted measures is the restriction of the product measure
  have hvol : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← hvol]
    exact h
  rw [MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => g₁ p.1 p.2 * g₂ p.1 p.2 * ρ p.1 p.2) hInt]
  rw [Work.Coercivity.wip]

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Construction.Defs =====
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

/-! ## The operator `L₁₂` and the angular moment `(F,K)` -/

/-- The paper's integral operator
`L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(r,θ)/r dθ dr` with `K = Spaces.K`.  This is
`Work.FM.L12 Spaces.K` (i.e. `Work.Elliptic.L12`, by `L12_eq_Elliptic`). -/
def L12 (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := Work.FM.L12 Work.Spaces.K f z

/-- The angular density `∫_0^{π/2} K(θ) f(s,θ)/s dθ` of `L₁₂`. -/
def L12dens (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := Work.FM.L12dens Work.Spaces.K f s

/-- The angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ` of the paper.  It is
`z ∂_z L₁₂(F)(z) = - (F,K)_{L²_θ}(z)` (see `mul_deriv_L12`). -/
def FK (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * Work.Spaces.K θ

/-- `s2 θ = sin(2θ)`, the angular factor of `D_θ` and of the transport term. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- `c2m θ = cos(2θ) - sin²θ`, the angular coefficient of the second and sixth terms of
`N₀` and of the transport term of `𝓛_Γ^T`. -/
def c2m (θ : ℝ) : ℝ := Real.cos (2 * θ) - Real.sin θ ^ 2

/-- The **open quadrant** `(0,∞) × (0,π/2)`: the set on which the identities of
§Modulation hold (the paper's identities involve `tan θ` and `1/cos θ`, which Lean
totalises at `θ = π/2`; the complement of the open quadrant is Lebesgue-null, so every
integral and every `ℋ^k`-norm is unaffected). -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

@[simp] theorem s2_eq (θ : ℝ) : s2 θ = Real.sin (2 * θ) := rfl
@[simp] theorem c2m_eq (θ : ℝ) : c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl

/-! ## The operators `U`, `V`, `ℛ` of the self-similar vorticity equation -/

/-- `U(Ψ) := -3Ψ - α z ∂_zΨ` (paper (Relations), tex 1320 / (PhitoU), tex 1378): the
coefficient of `∂_θΩ` in the self-similar vorticity equation.  (Same definition as
`Work.Elliptic.Uop`; see `Uop_eq`.) -/
def Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ

/-- `V(Ψ) := ∂_θΨ - tan θ · Ψ`: the coefficient of `α z ∂_zΩ`. -/
def Vop (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ

/-- `ℛ(Ψ) := (1/cos θ)(2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)`: the coefficient of
`Ω` in the self-similar vorticity equation. -/
def Rop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
    + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ

/-- The combination of the vorticity equation in which the coefficients `U, V, ℛ` are
evaluated at `Φ`, i.e. `2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F`. -/
def UVR (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Uop α Φ z θ * Work.Spaces.pth F z θ
    + 2 * α * Vop Φ z θ * Work.Spaces.Dz F z θ - 2 * Rop α Φ z θ * F z θ

/-! ## The self-similar ansatz -/







/-! ## The profile `F_*` and the singular part `Θ` -/

/-- The profile `F_*(z,θ) = α (Γ(θ)/c) 2z/(1+z)²` of the paper (tex 1334). -/
def Fstar (α : ℝ) (z θ : ℝ) : ℝ :=
  α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar z

/-- The profile `(Γ(θ)/c) 2z²/(1+z)³` which is the correction of the projector `𝕡` of
`𝓛_Γ^T`; it is the radial derivative combination `-(μ F_* - μ z∂_zF_*)/(2αμ)`. -/
def AK (α : ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)` of the stream function `Φ`; the
elliptic estimates are for `Φ - Θ` (`Work.Elliptic.EllResid = ΦTil`). -/
def Theta (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / (4 * α)) * s2 θ * L12 F z

/-- `Φ - Θ`: the quantity the elliptic estimates (Theorem `RemovingL12`) control. -/
def PhiTil (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Φ z θ - Theta α F z θ

/-- The full profile `F = F_* + g` of the modulation. -/
def Ftot (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Fstar α z θ + g z θ

/-! ## The nonlinear terms `N₀`, `N`, `N_*` (tex (N0)--(N*)) -/

/-- The term `N₀` of the paper (tex `\eqref{N0}`): everything that is quadratic in
`(F_*, g)`, with `F = F_* + g` the full profile and `g` the modulation.  Recall
`L₁₂(F_*) = 2α/(1+z)` (`L12_Fstar`). -/
def N0 (α : ℝ) (F g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth (Fstar α) z θ
    - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz (Fstar α) z θ
    + (1 / α) * L12 g z * g z θ
    + (3 / (2 * α)) * s2 θ * L12 g z * Work.Spaces.pth F z θ
    - c2m θ * L12 g z * Work.Spaces.Dz F z θ
    - c2m θ * L12 (Fstar α) z * Work.Spaces.Dz g z θ

/-- The term `N` of the paper (tex `\eqref{N}`): the elliptic correction
`Φ̃ = Φ - (1/(4α))sin(2θ)L₁₂(F)` transported by `U, V` and observed by `ℛ`, together with
the two angular-moment terms.  **Note**: the coefficients `-1/2` and `-1` of the last two
terms are the exact ones (the paper displays `-α` and `-2α`); see the module docstring and
`UVR_sub`. -/
def N (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Rop α (PhiTil α F Φ) z θ * F z θ
    - 2 * Uop α (PhiTil α F Φ) z θ * Work.Spaces.pth F z θ
    - 2 * α * Vop (PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ
    - (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
    - Real.sin θ ^ 2 * FK F z * F z θ

/-- The term `N_*` of the paper (tex `\eqref{N*}`): the linear part of
`-μF - (μ+lam+μλ)z∂_zF` in `g`, with the modulation constants `μ, lam` free.  With the paper's
choice `lam = -2μ/(1+μ)` this collapses to `-μ g` (`Nstar_at_lamfun`). -/
def Nstar (μ lam : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ

/-- The paper's `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` (tex 1366). -/
def mubar (N0v Nv : ℝ → ℝ → ℝ) : ℝ := L12 N0v 0 + L12 Nv 0


/-- The paper's choice `lam = -2μ/(1+μ)` of the second modulation constant (tex 1356). -/
def lamfun (μ : ℝ) : ℝ := -2 * μ / (1 + μ)

/-! ## The `g`-equation -/

/-- The right hand side of the `g`-equation `\eqref{gEquationFinal}` (tex 1369). -/
def gRHS (α μ lam : ℝ) (F Φ g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -mubar (N0 α F g) (N α F Φ) * AK α z θ
    + N0 α F g z θ + N α F Φ z θ + Nstar μ lam g z θ


/-- The left hand side display of tex line 1345,
`(1+μ)F + (1+μ)(1+lam)D_zF - (1/α)L₁₂(F)F - (3/(2α))sin(2θ)L₁₂(F)∂_θF
 + (cos 2θ - sin²θ)L₁₂(F)D_zF`. -/
def MainLHS (α μ lam : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
    - (1 / α) * L12 F z * F z θ
    - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
    + c2m θ * L12 F z * Work.Spaces.Dz F z θ

/-! ## The inner product on `ℋ⁴` consumed by the a-priori estimate -/

/-- An admissible inner product on `ℋ⁴` for the a-priori estimate of §Modulation: the
paper's inductively constructed `(·,·)_{ℋ⁴}` (`Work.Coercivity.IsHkIP`), together with the
Cauchy--Schwarz bound `|(f,g)_{ℋ⁴}| ≤ |f|_{ℋ⁴}|g|_{ℋ⁴}` which is used whenever the
estimate of a nonlinear term is paired with `g`. -/
structure IsH4IP (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- `IP` is an admissible inner product on `ℋ⁴` in the sense of the paper: it dominates
  the `ℋ⁴` norm squared and `𝓛_Γ^T` is coercive for it. -/
  isHkIP : Work.Coercivity.IsHkIP α 4 IP
  /-- Cauchy--Schwarz for `IP` against the `ℋ⁴` norm. -/
  cs : ∀ f g : ℝ → ℝ → ℝ,
    |IP f g| ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
  /-- `IP` is additive in its second argument. -/
  add_snd : ∀ (f g₁ g₂ : ℝ → ℝ → ℝ), IP f (g₁ + g₂) = IP f g₁ + IP f g₂
  /-- `IP` is additive in its first argument. -/
  add_fst : ∀ (f₁ f₂ g : ℝ → ℝ → ℝ), IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `IP` is `ℝ`-homogeneous in its first argument. -/
  smul_fst : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), IP (fun z θ => c * f z θ) g = c * IP f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`
  (which is co-null in the domain of integration `Iz × Iθ`). -/
  congr_qd : ∀ (f f' g : ℝ → ℝ → ℝ),
    (∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) → IP f g = IP f' g

/-! ## The "fake time" evolution equation -/

/-- The family `F(τ) = F_* + g(·,·,τ)` of full profiles along the fake-time flow. -/
def Ftau (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Fstar α z θ + g z θ τ

/-- The fake-time derivative `∂_τ g(·,·,τ)`. -/
def gdot (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => deriv (fun s => g z θ s) τ
end Work.Construction
end
end
-- ===== merged: Submission.Work.ConstructionInstance.A0_rho_pow_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The core case**: for `0 ≤ y ≤ x ≤ S` and `x - y ≤ d`, the difference of the `3β`-powers is
controlled by `3^β S^{2β} d^β`.  Ordering `s₁`, `s₂` reduces the general statement to this. -/
private lemma rho_core {β S x y d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxS : x ≤ S) (hxy : x - y ≤ d) (hd : 0 ≤ d) :
    x ^ (3 * β) - y ^ (3 * β) ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hx : 0 ≤ x := le_trans hy hyx
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- `x = 0`, hence also `y = 0`
    have hy0 : y = 0 := le_antisymm (by linarith) hy
    have hS0 : 0 ≤ S := by linarith
    rw [← hx0, hy0]
    simp only [Real.zero_rpow (by positivity : (3:ℝ) * β ≠ 0), sub_self]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) β) (Real.rpow_nonneg hS0 (2*β)))
      (Real.rpow_nonneg hd β)
  · -- `x > 0`: factor out the increment and use the one-variable inequality
    set u : ℝ := (x - y) / x with hu_def
    have hu0 : 0 ≤ u := by rw [hu_def]; exact div_nonneg (by linarith) hxpos.le
    have hu1 : u ≤ 1 := by rw [hu_def]; exact (div_le_one hxpos).mpr (by linarith)
    have hcrux := one_sub_one_sub_rpow_le hβ hβ1 hu0 hu1
    have hfac : x ^ (3*β) * (1 - (1 - u) ^ (3*β)) = x ^ (3*β) - y ^ (3*β) := by
      rw [hu_def]; exact mul_sub_mul_div_rpow hxpos hy
    have hmul := mul_le_mul_of_nonneg_left hcrux (Real.rpow_nonneg hxpos.le (3*β))
    have hdiv : x ^ (3*β) * (3*u)^β = 3^β * x^(2*β) * (x-y)^β := by
      rw [hu_def, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (div_nonneg (by linarith) hxpos.le)]
      rw [show x ^ (3*β) * (3^β * ((x-y)/x)^β) = 3^β * (x ^ (3*β) * ((x-y)/x)^β) by ring]
      rw [rpow_mul_div_rpow_eq hxpos hyx]
      ring
    have hfin : 3^β * x^(2*β) * (x-y)^β ≤ 3^β * S^(2*β) * d^β := by
      have hA : x ^ (2*β) ≤ S ^ (2*β) := Real.rpow_le_rpow hxpos.le hxS (by linarith)
      have hB : (x-y)^β ≤ d^β := Real.rpow_le_rpow (by linarith) hxy hβ.le
      have hAB : x^(2*β) * (x-y)^β ≤ S^(2*β) * d^β :=
        mul_le_mul hA hB (Real.rpow_nonneg (by linarith) β) (Real.rpow_nonneg (by linarith) (2*β))
      calc 3^β * x^(2*β) * (x-y)^β = 3^β * (x^(2*β) * (x-y)^β) := by ring
        _ ≤ 3^β * (S^(2*β) * d^β) := mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg (by norm_num) β)
        _ = 3^β * S^(2*β) * d^β := by ring
    calc x ^ (3*β) - y ^ (3*β) = x ^ (3*β) * (1 - (1 - u) ^ (3*β)) := hfac.symm
      _ ≤ x ^ (3*β) * (3*u)^β := hmul
      _ = 3^β * x^(2*β) * (x-y)^β := hdiv
      _ ≤ 3^β * S^(2*β) * d^β := hfin

lemma A0_rho_pow_diff {β s₁ s₂ S d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂) (hS1 : s₁ ≤ S) (hS2 : s₂ ≤ S) (hd : |s₁ - s₂| ≤ d) :
    |s₁ ^ (3 * β) - s₂ ^ (3 * β)| ≤ 3 ^ β * S ^ (2 * β) * d ^ β := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  rcases le_total s₂ s₁ with h | h
  · have hsub : s₁ - s₂ ≤ d := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s₁ - s₂)] at hd
      exact hd
    have hcore : s₁ ^ (3*β) - s₂ ^ (3*β) ≤ 3^β * S^(2*β) * d^β :=
      rho_core hβ hβ1 h2 h hS1 hsub hd0
    have hle : s₂ ^ (3*β) ≤ s₁ ^ (3*β) := Real.rpow_le_rpow h2 h (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s₁ ^ (3*β) - s₂ ^ (3*β))]
    exact hcore
  · have hsub : s₂ - s₁ ≤ d := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ - s₁)] at hd
      exact hd
    have hcore : s₂ ^ (3*β) - s₁ ^ (3*β) ≤ 3^β * S^(2*β) * d^β :=
      rho_core hβ hβ1 h1 h hS2 hsub hd0
    have hle : s₁ ^ (3*β) ≤ s₂ ^ (3*β) := Real.rpow_le_rpow h1 h (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ ^ (3*β) - s₁ ^ (3*β))]
    exact hcore

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.continuousAt_eTheta_of_radial_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The unit angular vector `x ↦ e_θ(x)` is continuous at every point off the axis.

`e_θ = (1/r) • angularVec` with `angularVec x = (-x₁, x₀, 0)` a continuous (indeed linear) map
and `r = √(x₀²+x₁²)` continuous and nonvanishing at `x`. -/
theorem continuousAt_eTheta_of_radial_ne_zero {x : Work.Cyl.R3}
    (hx : Work.Cyl.radial x ≠ 0) : ContinuousAt Work.Cyl.eTheta x := by
  have hrad : ContinuousAt (fun y : Work.Cyl.R3 => Work.Cyl.radial y) x := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have hang : ContinuousAt (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x := by
    rw [show Work.Cyl.angularVec =
        fun y : Work.Cyl.R3 => (-y 1) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 from by
      funext y
      apply Work.Cyl.ext_coord <;>
        simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hinv : ContinuousAt (fun y : Work.Cyl.R3 => (Work.Cyl.radial y)⁻¹) x :=
    hrad.inv₀ hx
  have hsmul : ContinuousAt (fun y : Work.Cyl.R3 =>
      (Work.Cyl.radial y)⁻¹ • Work.Cyl.angularVec y) x := hinv.smul hang
  convert hsmul using 1
  funext y
  rw [Work.Cyl.eTheta, one_div]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.Cyl.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Calculus glue for the cylindrical layer

General-purpose lemmas: the bridge between `fderiv` and one-dimensional derivatives along coordinate
lines, the coordinate form of the trace and of the curl, and the basic API of the partial derivative
`pd`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The standard basis -/

lemma basisVec_eq_basisFun (i : Fin 3) :
    basisVec i = EuclideanSpace.basisFun (Fin 3) ℝ i := by
  fin_cases i <;>
    simp [basisVec, e0, e1, eZ, FiniteTimeSingularity.e, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single]

/-! ## `fderiv` along coordinate lines -/

/-- `fderiv` applied to a vector is the derivative of the restriction of `f` to the corresponding
line. -/
theorem fderiv_apply_eq_deriv_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x v : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  have h3 : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
    h2.comp_hasDerivAt 0 h1
  exact h3.deriv.symm

/-- Partial derivative of a scalar field on `ℝ³` along the coordinate direction `i`, as a `deriv` of
a line. -/
theorem pd_eq_deriv_line (g : R3 → ℝ) (i : Fin 3) (x : R3) :
    pd i g x = deriv (fun t : ℝ => g (x + t • basisVec i)) 0 := rfl

/-! ## Coordinates of derivatives -/

lemma differentiableAt_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => (u y) j) x :=
  ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (u x) j).comp x hd.hasFDerivAt).differentiableAt

lemma hasFDerivAt_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    HasFDerivAt (fun y => (u y) j)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp (fderiv ℝ u x)) x :=
  (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (u x) j).comp x hd.hasFDerivAt

lemma fderiv_coord (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) (j : Fin 3) :
    fderiv ℝ (fun y => (u y) j) x =
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp (fderiv ℝ u x) :=
  (hasFDerivAt_coord u x hd j).fderiv

/-- Coordinates of `fderiv` are the partial derivatives in the corresponding directions. -/
theorem fderiv_apply_coord (u : R3 → R3) (x : R3) (i j : Fin 3)
    (hd : DifferentiableAt ℝ u x) :
    (fderiv ℝ u x (basisVec i)) j = pd i (fun y => (u y) j) x := by
  have h1 : (fderiv ℝ u x (basisVec i)) j = fderiv ℝ (fun y => (u y) j) x (basisVec i) := by
    rw [fderiv_coord u x hd j, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  rw [h1, pd, fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_coord u x hd j)]

/-! ## Trace and divergence in coordinates -/

/-- The trace of the derivative of a field is the sum of the diagonal entries of its Jacobian in the
standard basis. -/
theorem trace_fderiv_eq_sum (u : R3 → R3) (x : R3) :
    (fderiv ℝ u x).trace ℝ R3 = ∑ i, (fderiv ℝ u x (basisVec i)) i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_inner, ← basisVec_eq_basisFun]
  rfl

/-- The divergence as a sum of one-dimensional derivatives. -/
theorem div_eq_sum_partials (u : R3 → R3) (x : R3) (hd : DifferentiableAt ℝ u x) :
    FiniteTimeSingularity.div u x = ∑ i, deriv (fun t : ℝ => (u (x + t • basisVec i)) i) 0 := by
  rw [FiniteTimeSingularity.div, trace_fderiv_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_coord u x i i hd, pd_eq_deriv_line]

/-! ## The curl in coordinates -/


/-- The curl of a vector field in coordinates. -/
theorem vorticity_eq_coordinates (u : R3 → R3) (x : R3) :
    FiniteTimeSingularity.vorticity u x =
      !₂[(fderiv ℝ u x (basisVec 1)) 2 - (fderiv ℝ u x (basisVec 2)) 1,
          (fderiv ℝ u x (basisVec 2)) 0 - (fderiv ℝ u x (basisVec 0)) 2,
          (fderiv ℝ u x (basisVec 0)) 1 - (fderiv ℝ u x (basisVec 1)) 0] := by
  rw [FiniteTimeSingularity.vorticity, Fin.sum_univ_three]
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [basisVec, FiniteTimeSingularity.e, cross_apply] <;> ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.abs_radial_sub_le_dist =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `r` is 1-Lipschitz: `|r x - r y| ≤ dist x y`

The distance `radial x = √(x₀² + x₁²)` to the axis is the norm of the "radial vector"
`radialVec x = (x₀, x₁, 0)`, and the map `x ↦ radialVec x` does not increase distances (it
forgets the coordinate `x₂`).  Composing the reverse triangle inequality for the norm with this
observation gives the claim.
-/

namespace Work.Cyl

/-- The radial coordinate is the norm of the radial vector `r e_r = (x₀, x₁, 0)`. -/
lemma radial_eq_norm_radialVec' (x : R3) : radial x = ‖radialVec x‖ := by
  have h : radSq x = ‖radialVec x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_radialVec_self]
  rw [radial, h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The map `x ↦ (x₀, x₁, 0)` does not increase distances: it is the orthogonal projection onto
the plane spanned by the first two coordinates. -/
lemma norm_radialVec_sub_le_dist (x y : R3) : ‖radialVec x - radialVec y‖ ≤ ‖x - y‖ := by
  have h : ‖radialVec x - radialVec y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq]
    simp only [PiLp.sub_apply, radialVec_apply_zero, radialVec_apply_one, radialVec_apply_two]
    nlinarith [sq_nonneg (x 2 - y 2)]
  have := sq_le_sq.mp h
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem abs_radial_sub_le_dist (x y : Work.Cyl.R3) :
    |Work.Cyl.radial x - Work.Cyl.radial y| ≤ dist x y := by
  rw [radial_eq_norm_radialVec' x, radial_eq_norm_radialVec' y, dist_eq_norm]
  exact le_trans (abs_norm_sub_norm_le _ _) (norm_radialVec_sub_le_dist x y)

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.fderiv_angularVec_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `angularVec y = (-y₁, y₀, 0)` is the continuous linear map
`(proj 1).smulRight (-e₀) + (proj 0).smulRight e₁`, hence its Fréchet derivative at any point is
itself. -/
theorem fderiv_angularVec_apply (x v : Work.Cyl.R3) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x v = Work.Cyl.angularVec v := by
  have hL : (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) =
      ⇑((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).smulRight (-Work.Cyl.e0)
        + (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).smulRight
            Work.Cyl.e1 : Work.Cyl.R3 →L[ℝ] Work.Cyl.R3) := by
    funext y
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e,
        ContinuousLinearMap.smulRight_apply]
  rw [hL, ContinuousLinearMap.fderiv]
  exact (congrFun hL v).symm

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.inner_angularVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The angular vector `angularVec x = (-x₁, x₀, 0) = r e_θ` is orthogonal to the axis, so the
inner product of two angular vectors is the inner product of their projections onto the
`(x₀,x₁)`-plane. -/
theorem inner_angularVec (x y : Work.Cyl.R3) :
    inner ℝ (Work.Cyl.angularVec x) (Work.Cyl.angularVec y) = x 0 * y 0 + x 1 * y 1 := by
  rw [inner_eq]
  simp
  ring

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.norm_angularVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- `‖r e_θ‖ = r`: the length of the angular vector `angularVec x = (-x₁, x₀, 0)` is the
distance `radial x` of `x` to the symmetry axis. -/
theorem norm_angularVec (x : Work.Cyl.R3) : ‖Work.Cyl.angularVec x‖ = Work.Cyl.radial x := by
  have h : ‖angularVec x‖ ^ 2 = radSq x := by
    rw [← real_inner_self_eq_norm_sq, inner_angularVec_self]
  have h2 : radial x ^ 2 = radSq x := radial_sq x
  nlinarith [norm_nonneg (angularVec x), radial_nonneg x]

end Work.Cyl
end
-- ===== merged: Submission.Work.Cyl.radial_sq_sub_coord_le_dist_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The squared distance in coordinates: `‖x - y‖²` is the sum of the squares of the coordinate
differences. -/
lemma dist_sq_coords (x y : R3) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_three, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

theorem radial_sq_sub_coord_le_dist_sq (x y : Work.Cyl.R3) :
    Work.Cyl.radial x ^ 2 + Work.Cyl.radial y ^ 2 - 2 * (x 0 * y 0 + x 1 * y 1)
      ≤ dist x y ^ 2 := by
  have hx : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [radial_sq, radSq]
  have hy : radial y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [radial_sq, radSq]
  rw [hx, hy, dist_sq_coords]
  nlinarith [sq_nonneg (x 2 - y 2)]

end Work.Cyl
end
-- ===== merged: Submission.Work.Elliptic.Algebra =====
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
set_option linter.unusedSimpArgs false

/-! ## Derivatives of the elementary angular functions -/

lemma deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]; ring

lemma deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -2 * Real.sin (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  rw [h2.deriv]; ring

/-- `(2 cos 2θ)' = -4 sin 2θ`. -/
lemma deriv_two_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ = -4 * Real.sin (2 * θ) := by
  rw [deriv_const_mul_field, deriv_cos_two]
  ring

/-- The double `θ`-derivative of `sin 2θ`. -/
lemma pthIter_sin_two (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ
      = -4 * Real.sin (2 * θ) := by
  have h1 : (fun θ' : ℝ => deriv (fun θ'' : ℝ => Real.sin (2 * θ'')) θ')
      = fun θ' => 2 * Real.cos (2 * θ') := by
    funext θ'; exact deriv_sin_two θ'
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
    Function.comp_apply]
  rw [h1, deriv_two_cos_two]

/-- `∂_θ(tan θ · sin 2θ) = 2 sin 2θ` (for `cos θ ≠ 0`). -/
lemma deriv_tan_mul_sin_two (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ')) θ = 2 * Real.sin (2 * θ) := by
  have hne : ∀ᶠ θ' in 𝓝 θ, Real.cos θ' ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hθ
  have heq : (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ'))
      =ᶠ[𝓝 θ] fun θ' => 2 * Real.sin θ' ^ 2 := by
    filter_upwards [hne] with θ' h'
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  rw [heq.deriv_eq]
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * Real.sin θ' ^ 2) (4 * Real.sin θ * Real.cos θ) θ := by
    have h : HasDerivAt (fun x : ℝ => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h0 := (Real.hasDerivAt_sin θ).pow 2
      convert h0 using 1 <;> ring
    convert h.const_mul 2 using 1 <;> ring
  calc deriv (fun θ' : ℝ => 2 * Real.sin θ' ^ 2) θ
      = 4 * Real.sin θ * Real.cos θ := h2.deriv
    _ = 2 * Real.sin (2 * θ) := by rw [Real.sin_two_mul]; ring

/-! ## The kernel identity -/

/-- `L₀(sin 2θ) = 0`. -/
lemma Lzero_sin_two (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Lzero (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ = 0 := by
  rw [Lzero, pthIter_sin_two]
  have h : Work.Spaces.pth (fun z θ => Real.tan θ * Real.sin (2 * θ)) z θ
      = deriv (fun θ' : ℝ => Real.tan θ' * Real.sin (2 * θ')) θ := by
    simp only [Work.Spaces.pth, Function.comp_apply]
  rw [h, deriv_tan_mul_sin_two θ hθ]
  ring

/-- `L₀(g(z)·sin 2θ) = 0` for any `g`: the `sin 2θ` direction of the kernel survives
multiplication by a `z`-dependent factor. -/
lemma Lzero_sin_two_mul (g : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Lzero (fun z θ => g z * Real.sin (2 * θ)) z θ = 0 := by
  have h1 : Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = g z * Work.Spaces.pthIter 2 (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) z θ := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
      Function.comp_apply, deriv_const_mul_field]
  have h3 : Work.Spaces.pth (fun z θ => Real.tan θ * (g z * Real.sin (2 * θ))) z θ
      = g z * Work.Spaces.pth (fun z θ => Real.tan θ * Real.sin (2 * θ)) z θ := by
    simp only [Work.Spaces.pth, Function.comp_apply]
    rw [show (fun θ' : ℝ => Real.tan θ' * (g z * Real.sin (2 * θ')))
        = fun θ' : ℝ => g z * (Real.tan θ' * Real.sin (2 * θ')) from by
      funext θ'; ring]
    rw [deriv_const_mul_field]
  rw [Lzero, h1, h3]
  have hL := Lzero_sin_two z θ hθ
  rw [Lzero] at hL
  linear_combination g z * hL

/-! ## The action of `L` on `G(z) sin 2θ` -/

/-- `L(G(z)·sin 2θ) = -(α²z²G'' + α(5+α)zG')·sin 2θ`: the radial and angular parts decouple on the
`sin 2θ` direction, which is what makes the singular term computable in closed form. -/
lemma bslOp_sin_two_mul (α : ℝ) (g : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    bslOp α (fun z θ => g z * Real.sin (2 * θ)) z θ
      = -(α ^ 2 * z ^ 2 * deriv (fun z' : ℝ => deriv g z') z + α * (5 + α) * z * deriv g z)
          * Real.sin (2 * θ) := by
  have hpz1 : Work.Spaces.pz (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv g z * Real.sin (2 * θ) := by
    simp only [Work.Spaces.pz, Function.comp_apply, deriv_mul_const_field]
  have hpz2 : Work.Spaces.pzIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv (fun z' : ℝ => deriv g z') z * Real.sin (2 * θ) := by
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz,
      Function.comp_apply, deriv_mul_const_field]
  have hL : Lzero (fun z θ => g z * Real.sin (2 * θ)) z θ = 0 :=
    Lzero_sin_two_mul g z θ hθ
  rw [bslOp_apply, hpz2, hpz1, hL]
  ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinBddDefs =====
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
-- ===== merged: Submission.Work.Elliptic.DivSinDthDerivBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinHardy =====
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
set_option maxHeartbeats 1000000

/-! ## Small measure/integral helpers -/



private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]

private lemma restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc

/-! ## The reflected weighted Hardy inequality on `Iθ` -/


/-! ## Integrability of the three weighted integrands -/


/-! ## The weighted Hardy inequality for `sin(2θ)` -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinL2WtCmp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.DivSinSliceIdent =====
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
set_option linter.unusedVariables false

/-! ## Iterated `D_θ` of a function of `θ` alone

`D_θ f = sin(2θ) ∂_θ f` (`Work.Spaces.Dth`), where `∂_θ` differentiates the second
variable while the first (`z`) is held fixed.  If `f z θ = g θ` does not depend on `z`,
then `D_θ f z θ = sin(2θ) · g'(θ) = Dth1 g θ`; iterating gives the identity below.
It is the observation that makes `h ↦ h / sin(2θ)` a legitimate "angular quotient":
the one-dimensional operator `Dth1` of `DivisionBySin` computes exactly the iterated
`D_θ`-derivatives of the two-variable function `(z,θ) ↦ h θ / sin(2θ)`. -/

/-- Iterated `D_θ` of a function of `θ` alone agrees with the iterated one-dimensional
operator `Dth1`. -/
theorem DthIter_const (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') z θ = Dth1Iter i g θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, Dth1Iter_succ, Dth1]
      congr 1
      exact congrArg (fun f => deriv f θ) (funext fun θ' => ih z θ')


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinWPDefs =====
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

/-- The first integrand `cos(2θ)² sin(2θ)^{2-γ} (u')²` of `DivSinIBPWeight`, where
`u = SinQ h`. -/
def W1 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2

/-- The second integrand `sin(2θ)^{4-γ} (u')²` of `DivSinIBPWeight`, where `u = SinQ h`. -/
def W2 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2

/-- The third integrand `sin(2θ)^{3-γ} cos(2θ) u' u''` of `DivSinIBPWeight`, where
`u = SinQ h`. -/
def W3 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ) * deriv (SinQ h) θ
    * deriv (deriv (SinQ h)) θ



end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DthIter_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.Fstar_sq_le =====
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

/-- Cauchy--Schwarz in discriminant form: if the real quadratic `A - 2tB + t²C` is
nonnegative for every `t`, then `B² ≤ A·C`. -/
lemma sq_le_mul_of_quadratic_nonneg {A B C : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  have hq : ∀ x : ℝ, 0 ≤ C * (x * x) + (-2 * B) * x + A := by
    intro x
    have := h x
    nlinarith [this]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

theorem Fstar_sq_le (F : ℝ → ℝ → ℝ) (z : ℝ)
    (h : MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ) :
    (Work.Elliptic.Fstar F z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The angular weight is continuous.
  have hw_cont : Continuous (fun θ : ℝ => sinCos2 θ) := by
    unfold sinCos2
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  -- Its square is integrable on the compact interval `Iθ`.
  have hw2_int : IntegrableOn (fun θ : ℝ => (sinCos2 θ) ^ 2) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (hw_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  -- Pointwise, `sinCos2 θ ^ 2 ≤ 1` on `Iθ`.
  have hpt_le : ∀ θ ∈ Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ (1 : ℝ) := by
    intro θ hθ
    obtain ⟨hθ0, hθ2⟩ := hθ
    have hpi : 0 < π := Real.pi_pos
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith⟩
    have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hcos_nn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ2⟩
    have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcos2_nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    have hcos2_le : Real.cos θ ^ 2 ≤ 1 := by nlinarith
    have hw_nn : 0 ≤ sinCos2 θ := by
      rw [sinCos2]
      exact mul_nonneg hsin_nn hcos2_nn
    have hw_le : sinCos2 θ ≤ 1 := by
      rw [sinCos2]
      calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
            mul_le_mul hsin_le hcos2_le hcos2_nn zero_le_one
        _ = 1 := by ring
    nlinarith
  -- Consequently `∫_{Iθ} sinCos2² ≤ vol(Iθ) = π/2`.
  have hw2_le : ∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ π / 2 := by
    have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hle : ∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hInt1
        (by filter_upwards [ae_restrict_mem hIθ] with θ hθ; exact hpt_le θ hθ)
    have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hconst : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = π / 2 := by
      have h1 : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = volume.real Work.Spaces.Iθ := by
        rw [MeasureTheory.setIntegral_const]
        simp
      rw [h1, hvol]
    linarith
  -- Main argument: unfold `F_*` and argue with the discriminant of
  -- `t ↦ ∫_{Iθ} (F(z,θ) - t sin θ cos²θ)²`.
  rw [Fstar]
  have hA0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 : ℝ) :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hkey : (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
    by_cases huw : IntegrableOn (fun θ => F z θ * sinCos2 θ) Work.Spaces.Iθ
    · -- `F sinθcos²θ` is integrable: use the nonnegative quadratic in `t`.
      have hexpand : ∀ t : ℝ, ∫ θ in Work.Spaces.Iθ, (F z θ - t * sinCos2 θ) ^ 2
          = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
            - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
            + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
        intro t
        have h1 : IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ := h
        have h2 : IntegrableOn (fun θ => F z θ * sinCos2 θ) Work.Spaces.Iθ := huw
        have h3 : IntegrableOn (fun θ => (sinCos2 θ) ^ 2) Work.Spaces.Iθ := hw2_int
        have h12 : IntegrableOn
            (fun θ => (F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)) Work.Spaces.Iθ :=
          h1.sub (h2.const_mul (2 * t))
        have hstep2 : (∫ θ in Work.Spaces.Iθ,
              ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)))
            = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
              - ∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ) :=
          integral_sub h1 (h2.const_mul (2 * t))
        have hstep3 : (∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ))
            = (2 * t) * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) :=
          integral_const_mul (2 * t) (fun θ => F z θ * sinCos2 θ)
        have hstep4 : (∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2)
            = t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) :=
          integral_const_mul (t ^ 2) (fun θ => (sinCos2 θ) ^ 2)
        calc ∫ θ in Work.Spaces.Iθ, (F z θ - t * sinCos2 θ) ^ 2
            = ∫ θ in Work.Spaces.Iθ, ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)
                + t ^ 2 * (sinCos2 θ) ^ 2) := by
              exact setIntegral_congr_fun hIθ (fun θ _ => by ring)
          _ = (∫ θ in Work.Spaces.Iθ, ((F z θ) ^ 2 - (2 * t) * (F z θ * sinCos2 θ)))
                + ∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2 :=
              integral_add h12 (h3.const_mul (t ^ 2))
          _ = ((∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - ∫ θ in Work.Spaces.Iθ, (2 * t) * (F z θ * sinCos2 θ))
                + ∫ θ in Work.Spaces.Iθ, t ^ 2 * (sinCos2 θ) ^ 2 := by
              rw [hstep2]
          _ = ((∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - (2 * t) * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ))
                + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
              rw [hstep3, hstep4]
          _ = (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
                - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
                + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
              ring
      have hq : ∀ t : ℝ, 0 ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
          - 2 * t * (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ)
          + t ^ 2 * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := by
        intro t
        rw [← hexpand t]
        exact integral_nonneg (fun θ => sq_nonneg _)
      exact sq_le_mul_of_quadratic_nonneg hq
    · -- Otherwise the integral of the product vanishes.
      have hB0 : (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) = 0 := integral_undef huw
      rw [hB0]
      have hC0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2 : ℝ) :=
        integral_nonneg (fun θ => sq_nonneg _)
      simpa using mul_nonneg hA0 hC0
  calc (∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (sinCos2 θ) ^ 2) := hkey
    _ ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) * (π / 2) :=
        mul_le_mul_of_nonneg_left hw2_le hA0
    _ = (π / 2) * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2) := by ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.Gbar_hardy_lintegral_ofReal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

theorem Gbar_hardy_lintegral_ofReal (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2) := by
  have hb0 : (0 : ℝ) < β := by linarith
  have hb2 : (0 : ℝ) < 3 * β - 2 := by linarith
  have hJ : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 :=
    integral_nonneg (fun z => sq_nonneg (f z))
  -- Pointwise (weighted Cauchy--Schwarz) bound, at the level of `ℝ≥0∞`.
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)
        ≤ ENNReal.ofReal (2 / β) * (ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    intro z hz
    have hzpos : 0 < z := hz
    have hrz : (z ^ (-β)) ^ 2 = z ^ (-(2 * β)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
      congr 1
      ring
    have hc3 : z ^ (-(2 * β)) * z ^ (β / 2) = z ^ (-(3 * β / 2)) := by
      rw [← Real.rpow_add hzpos]
      congr 1
      ring
    have hp := hardy_op_L2_pointwise β hβ f hf hzpos
    have hle : (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
        ≤ (2 / β) * z ^ (-(3 * β / 2)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
      rw [mul_pow, hrz]
      calc z ^ (-(2 * β)) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
          ≤ z ^ (-(2 * β)) * ((2 * z ^ (β / 2) / β) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hzpos.le _)
        _ = (2 / β) * z ^ (-(3 * β / 2)) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
            rw [← hc3]; ring
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [show (2 / β) * z ^ (-(3 * β / 2)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal
        = (2 / β) * (z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) by ring]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hzpos.le _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le (bot_le)) (bot_le)
  -- Integrate the pointwise bound and pull out the constant `2/β`.
  have hstep : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (2 / β)) _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ioi hpoint
  have hT := hardy_op_L2_tonelli β hβ f hf
  rw [hT] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 / β)]
  congr 1
  have hb0ne : β ≠ 0 := ne_of_gt hb0
  have hb2ne : 3 * β - 2 ≠ 0 := ne_of_gt hb2
  field_simp
  ring

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.GsingFuncs =====
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

/-- The homogeneous factor `-(3/(4α)) z^{-5/α}` of `Gbar`. -/
def Abar (α : ℝ) (z : ℝ) : ℝ := -(3 / (4 * α)) * z ^ (-(5 / α))

/-- The derivative of `Abar`, with respect to `z`. -/
def DAbar (α : ℝ) (z : ℝ) : ℝ := (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)

/-- The second derivative of `Abar`, with respect to `z`. -/
def DDAbar (α : ℝ) (z : ℝ) : ℝ :=
  (-(3 / (4 * α)) * (-(5 / α))) * ((-(5 / α) - 1) * z ^ (-(5 / α) - 1 - 1))

/-- The inner integral `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds` of `Gbar`. -/
def Jfun (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Fstar F s

/-- The value of `(Gstar α F)'` at `z`, as a function of `z`. -/
def DGstar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (-(1 / (4 * α))) * (-(3 * Fstar F z / z))

/-- The value of `(Gbar α F)'` at `z`, as a function of `z`. -/
def DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  DAbar α z * Jfun α F z + Abar α z * (z ^ ((5 - α) / α) * Fstar F z)

/-- The value of `(Gstar α F)''` at `z`, as a function of `z`. -/
def DDGstar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (-(1 / (4 * α))) * (-(((3 * deriv (Fstar F) z) * z - 3 * Fstar F z) / z ^ 2))

/-- The value of `(Gbar α F)''` at `z`, as a function of `z`. -/
def DDGbar (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  DDAbar α z * Jfun α F z
    + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
    + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
    + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
        + z ^ ((5 - α) / α) * deriv (Fstar F) z)

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.HardyRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.HardyRightW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary bounds for the weight `w z = (1+z)² / z²` on `(1,∞)`

On `(1,∞)` one has `1 ≤ w z ≤ 4`: indeed `w z = (1 + 1/z)²` and `1 < 1 + 1/z < 2`
for `z > 1`.  Consequently `w z ² ≤ 16` there. -/

/-- On `(1,∞)` the weight `w z = (1+z)²/z²` is at least `1`. -/
theorem one_le_w_of_one_lt {z : ℝ} (hz : 1 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  nlinarith

/-- On `(1,∞)` the weight `w z = (1+z)²/z²` is at most `4`. -/
theorem w_le_four_of_one_lt {z : ℝ} (hz : 1 < z) : Work.Spaces.w z ≤ 4 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, div_le_iff₀ hz2]
  have h1 : 1 + z ≤ 2 * z := by linarith
  have h2 : (0 : ℝ) ≤ 1 + z := by linarith
  nlinarith [mul_self_le_mul_self h2 h1]

/-- On `(1,∞)` the square of the weight is at most `16`. -/
theorem w_sq_le_sixteen_of_one_lt {z : ℝ} (hz : 1 < z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have h := w_le_four_of_one_lt hz
  nlinarith [one_le_w_of_one_lt hz]

/-- Weighted Hardy inequality on the right half-line: for `U` differentiable on `(1,∞)` with derivative `-(f z / z)`, tending to `0` at `+∞`, and with `f²w²` integrable on `(1,∞)`, one has `U²w²` integrable on `(1,∞)` with `∫_{(1,∞)} U²w² ≤ 107 ∫_{(1,∞)} f²w²`. Here `w z = (1+z)²/z²` is `Work.Spaces.w`. Intended route: `(z U' z)² = (f z)²`, the dual Hardy inequality `∫_{(1,∞)} U² ≤ 6 ∫_{(1,∞)} (zU')²`, the pointwise bounds `1 ≤ w ≤ 4` on `(1,∞)` (so `w² ≤ 16`), giving the constant `96 ≤ 107`. -/
theorem HardyRightW (f U : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (-(f z / z)) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  -- `f²` is integrable on `(1,∞)` and `∫ f² ≤ ∫ f² w²`.
  obtain ⟨hf2int, hf2le⟩ := IntegrableSqMulW hint
  -- The pointwise bounds for the weight.
  have hw1 : ∀ z ∈ Set.Ioi (1 : ℝ), 1 ≤ Work.Spaces.w z := fun z hz => one_le_w_of_one_lt hz
  have hw4sq : ∀ z ∈ Set.Ioi (1 : ℝ), (Work.Spaces.w z) ^ 2 ≤ 16 :=
    fun z hz => w_sq_le_sixteen_of_one_lt hz
  -- The derivative prescribed by the hypotheses.
  set U' : ℝ → ℝ := fun z => -(f z / z) with hU'def
  -- On `(1,∞)` one has `(z U' z)² = (f z)²`.
  have hzeq : EqOn (fun z : ℝ => (z * U' z) ^ 2) (fun z : ℝ => (f z) ^ 2) (Set.Ioi 1) := by
    intro z hz
    simp only [hU'def]
    have hz0 : z ≠ 0 := ne_of_gt (lt_trans one_pos hz)
    have h : z * (-(f z / z)) = -(f z) := by field_simp
    rw [h]; ring
  have hzeq_int : ∫ z in Set.Ioi (1 : ℝ), (z * U' z) ^ 2 = ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi hzeq
  -- Hence `(z U' z)²` is integrable on `(1,∞)`.
  have hU'int : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1) :=
    hf2int.congr_fun hzeq.symm measurableSet_Ioi
  -- The dual Hardy inequality on `(1,∞)`.
  obtain ⟨hU2int, hU2le⟩ := HardyRightNoCont U U' hderiv htend hU'int
  have hU2le' : ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 ≤ 6 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 := by
    rw [hzeq_int] at hU2le
    exact hU2le
  -- Nonnegativity of the right-hand side.
  have hF2nn : 0 ≤ ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- `U² w²` is integrable, being `U²` times the bounded function `w²`.
  have hU2w2int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
    have hg : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi 1)) := by
      have hcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
        apply ContinuousOn.pow
        apply ContinuousOn.div
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · exact continuousOn_id.pow 2
        · intro z hz
          have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
          positivity
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    rw [MeasureTheory.IntegrableOn] at hU2int ⊢
    exact hU2int.mul_bdd hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hw4sq z hz)
  -- `∫ U² w² ≤ 16 ∫ U²`.
  have hS : ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 16 * ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 := by
    rw [MeasureTheory.IntegrableOn] at hU2int
    have h16 : IntegrableOn (fun z : ℝ => 16 * (U z) ^ 2) (Set.Ioi (1 : ℝ)) := hU2int.const_mul 16
    have hmono := setIntegral_mono_on hU2w2int h16 measurableSet_Ioi
      (fun z hz => by have h := hw4sq z hz; nlinarith [sq_nonneg (U z)])
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  refine ⟨hU2w2int, ?_⟩
  calc ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 16 * ∫ z in Set.Ioi (1 : ℝ), (U z) ^ 2 := hS
    _ ≤ 16 * (6 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2) := by linarith [hU2le']
    _ = 96 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 := by ring
    _ ≤ 96 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by linarith [hf2le]
    _ ≤ 107 * ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by nlinarith [hF2nn]

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.HardyTwoDefs =====
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

/-- The function `u θ = f θ / sin(2θ)` whose derivative is estimated by `hardy_two`.
At `θ = 0, π/2` it takes the (irrelevant) default value `0`. -/
def htU (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ / Real.sin (2 * θ)








end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.L12_eq_radial =====
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

/-- The angular density of `L₁₂` is `3/r` times the angular moment `F_*`:
`∫_0^{π/2} K(θ) F(r,θ)/r dθ = 3/r ∫_0^{π/2} F(r,θ) sin θ cos²θ dθ`, because
`K(θ) = 3 sin θ cos²θ`.  No integrability is needed (the Bochner integral is total). -/
lemma L12dens_eq_three_Fstar_div (F : ℝ → ℝ → ℝ) (r : ℝ) :
    L12dens F r = 3 * (Fstar F r / r) := by
  rw [L12dens, Fstar]
  have h1 : (fun θ => Ktheta θ * F r θ / r)
      = fun θ => 3 * (F r θ * sinCos2 θ / r) := by
    funext θ; simp only [Ktheta, sinCos2]; ring
  rw [h1, MeasureTheory.integral_const_mul, MeasureTheory.integral_div]

theorem L12_eq_radial (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 F z = 3 * Work.Elliptic.L12rad F z := by
  rw [L12, L12rad]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => L12dens_eq_three_Fstar_div F r)]
  rw [MeasureTheory.integral_const_mul]

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.LzeroAdj_sinCos2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.Elliptic

set_option autoImplicit false





end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.Lzero_orthogonal =====
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

/-! ## Two elementary rewritings of `L₀` -/

/-- `L₀` written with the one-variable derivatives of `f = Ψ z`:
`L₀(Ψ)(z,θ) = -(deriv (deriv f)) θ + deriv (tan · f) θ - 6 f θ`. -/
lemma Lzero_eq_deriv (Ψ : ℝ → ℝ → ℝ) (z x : ℝ) :
    Lzero Ψ z x = -(deriv (deriv (fun θ : ℝ => Ψ z θ)) x)
      + deriv (fun θ : ℝ => Real.tan θ * Ψ z θ) x - 6 * Ψ z x := by
  unfold Lzero
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- `deriv sinCos2 θ = cos θ ^ 3 - 2 sin θ ^ 2 cos θ`. -/
lemma deriv_sinCos2 (x : ℝ) :
    deriv sinCos2 x = Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x := by
  unfold sinCos2
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Real.cos x * Real.cos x ^ 2
        + Real.sin x * (2 * Real.cos x ^ (2-1) * (-Real.sin x))) x :=
    (Real.hasDerivAt_sin x).mul ((Real.hasDerivAt_cos x).pow 2)
  have h' : Real.cos x * Real.cos x ^ 2
      + Real.sin x * (2 * Real.cos x ^ (2-1) * (-Real.sin x))
      = Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x := by ring
  exact (h.congr_deriv h').deriv

/-- `deriv (fun θ ↦ cos θ · cos 2θ) x = sin x - 6 sin x cos²x`. -/
lemma deriv_cos_mul_cos_two (x : ℝ) :
    deriv (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) x
      = Real.sin x - 6 * Real.sin x * Real.cos x ^ 2 := by
  have h : HasDerivAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
      ((-Real.sin x) * Real.cos (2*x) + Real.cos x * (-Real.sin (2*x) * 2)) x := by
    have h₂ : HasDerivAt (fun θ : ℝ => Real.cos (2*θ)) (-Real.sin (2*x) * 2) x := by
      have := (Real.hasDerivAt_cos (2*x)).comp x (hasDerivAt_const_mul (x := x) 2)
      simpa [Function.comp_def, mul_comm] using this
    exact (Real.hasDerivAt_cos x).mul h₂
  have h' : (-Real.sin x) * Real.cos (2*x) + Real.cos x * (-Real.sin (2*x) * 2)
      = Real.sin x - 6 * Real.sin x * Real.cos x ^ 2 := by
    rw [Real.cos_two_mul, Real.sin_two_mul]; ring
  exact (h.congr_deriv h').deriv

/-! ## The antiderivative of the integrand -/

/-- `sinCos2` is differentiable. -/
lemma differentiableAt_sinCos2 (x : ℝ) : DifferentiableAt ℝ sinCos2 x := by
  unfold sinCos2; fun_prop

/-- `θ ↦ cos θ · cos 2θ` is differentiable. -/
lemma differentiableAt_cosCosTwo (x : ℝ) :
    DifferentiableAt ℝ (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) x := by
  fun_prop

/-- **The pointwise identity behind the orthogonality.**  For `x` in the *open* interval, where
`tan` is differentiable and all the `deriv`'s in `Lzero` are honest derivatives, the function

  `F(θ) = -(deriv f) θ · sinCos2 θ + f θ · cos θ cos 2θ`  (with `f = Ψ z`)

has derivative `L₀(Ψ)(z,x) · sinCos2 x`: the two identities
`φ'' + tan θ φ' + 6φ = 0` and `(tan θ · φ)' = φ'` conspire so that the `(cos θ cos 2θ)`
correction absorbs the `tan`-singularity. -/
lemma hasDerivAt_Lzero_antideriv (Ψ : ℝ → ℝ → ℝ) (z x : ℝ) (hx : x ∈ Set.Ioo 0 (π / 2))
    (h2 : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) x) :
    HasDerivAt (fun θ : ℝ => -(deriv (fun θ : ℝ => Ψ z θ) θ) * sinCos2 θ
        + Ψ z θ * (Real.cos θ * Real.cos (2 * θ)))
      (Lzero Ψ z x * sinCos2 x) x := by
  have hcos : Real.cos x ≠ 0 := by
    have : x ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) :=
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo this)
  have hfd : HasDerivAt (fun θ : ℝ => Ψ z θ) (deriv (fun θ : ℝ => Ψ z θ) x) x :=
    (h2.differentiableAt (by norm_num)).hasDerivAt
  have hd : ContDiffAt ℝ 1 (deriv (fun θ : ℝ => Ψ z θ)) x :=
    h2.derivWithin (by norm_num)
  have hfd2 : HasDerivAt (deriv (fun θ : ℝ => Ψ z θ))
      (deriv (deriv (fun θ : ℝ => Ψ z θ)) x) x :=
    (hd.differentiableAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt (fun θ : ℝ => Real.tan θ * Ψ z θ)
      ((1/Real.cos x^2) * Ψ z x + Real.tan x * deriv (fun θ : ℝ => Ψ z θ) x) x :=
    (Real.hasDerivAt_tan hcos).mul hfd
  have hφ : HasDerivAt sinCos2 (Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x) x :=
    (differentiableAt_sinCos2 x).hasDerivAt.congr_deriv (deriv_sinCos2 x)
  have hψ : HasDerivAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
      (Real.sin x - 6 * Real.sin x * Real.cos x ^ 2) x :=
    (differentiableAt_cosCosTwo x).hasDerivAt.congr_deriv (deriv_cos_mul_cos_two x)
  have hF := ((hfd2.neg).mul hφ).add (hfd.mul hψ)
  refine hF.congr_deriv ?_
  rw [Lzero_eq_deriv, htan.deriv]
  unfold sinCos2
  simp only [Pi.neg_apply]
  rw [Real.tan_eq_sin_div_cos, Real.cos_two_mul]
  field_simp
  linear_combination (Real.cos x * deriv (fun θ : ℝ => Ψ z θ) x) * Real.sin_sq_add_cos_sq x

/-! ## The orthogonality -/

theorem Lzero_orthogonal (Ψ : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)))
    (h0 : Ψ z 0 = 0) (h1 : Ψ z (π / 2) = 0) :
    ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ = 0 := by
  have hle : (0:ℝ) ≤ π/2 := by positivity
  have hlt : (0:ℝ) < π/2 := by positivity
  -- the antiderivative `H`, built from `derivWithin` so that it is `C¹` on the closed interval
  set f : ℝ → ℝ := fun θ => Ψ z θ with hf
  set H : ℝ → ℝ := fun θ => -(derivWithin f (Set.Icc 0 (π/2)) θ) * sinCos2 θ
      + f θ * (Real.cos θ * Real.cos (2 * θ)) with hHdef
  have hsm_f : ContDiffOn ℝ 2 f (Set.Icc 0 (π/2)) := by rw [hf]; exact hsm
  have hHcd : ContDiffOn ℝ 1 H (Set.Icc 0 (π/2)) := by
    rw [hHdef]
    have hu : UniqueDiffOn ℝ (Set.Icc (0:ℝ) (π/2)) := uniqueDiffOn_Icc hlt
    have hdw : ContDiffOn ℝ 1 (derivWithin f (Set.Icc 0 (π/2))) (Set.Icc 0 (π/2)) :=
      hsm_f.derivWithin hu (by norm_num)
    have hsm1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π/2)) := hsm_f.of_le (by norm_num)
    have hsincos : ContDiffOn ℝ 1 sinCos2 (Set.Icc 0 (π/2)) := by
      unfold sinCos2; fun_prop
    have hcc : ContDiffOn ℝ 1 (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (Set.Icc 0 (π/2)) := by fun_prop
    exact (hdw.neg.mul hsincos).add (hsm1.mul hcc)
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc hHcd hle
  -- on the open interval `H` is the `deriv`-version of the antiderivative, hence computes `Lzero·φ`
  have hpoint : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      Lzero Ψ z θ * sinCos2 θ = deriv H θ := by
    intro θ hθ
    have h2 : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) θ :=
      hsm.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hHF : H =ᶠ[𝓝 θ] (fun θ : ℝ => -(deriv (fun θ : ℝ => Ψ z θ) θ) * sinCos2 θ
        + Ψ z θ * (Real.cos θ * Real.cos (2 * θ))) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      simp only [hHdef, hf, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact ((hasDerivAt_Lzero_antideriv Ψ z θ hθ h2).congr_of_eventuallyEq hHF).deriv.symm
  -- they agree almost everywhere on `(0, π/2]`
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc (0:ℝ) (π/2) →
      Lzero Ψ z θ * sinCos2 θ = deriv H θ := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (π/2))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    obtain ⟨hθu, hθne⟩ := hθ
    rw [Set.mem_singleton_iff]
    by_contra hne
    rw [Set.uIoc_of_le hle] at hθu
    exact hθne (hpoint θ ⟨hθu.1, lt_of_le_of_ne hθu.2 hne⟩)
  have hH0 : H 0 = 0 := by simp [hHdef, hf, h0, sinCos2]
  have hHpi : H (π/2) = 0 := by simp [hHdef, hf, h1, sinCos2]
  change ∫ θ in Set.Icc (0:ℝ) (π/2), Lzero Ψ z θ * sinCos2 θ = 0
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr_ae hae, hFTC, hHpi, hH0]
  ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoW_g_coeff_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic



end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoW_g_coeff_rec =====
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
-- ===== merged: Submission.Work.Elliptic.WtoW_g_coeff_self =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic



end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoW_pzIter_sum_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.bslOp_add =====
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

/-! ## Slices of a `C^n` function are `C^n` -/

/-- The `z`-slice `z' ↦ Ψ z' θ` of a function which is `C^n` at `(z,θ)` is `C^n` at `z`. -/
lemma contDiffAt_uncurry_slice_fst (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) {n : WithTop ℕ∞}
    (h : ContDiffAt ℝ n (Function.uncurry Ψ) (z, θ)) :
    ContDiffAt ℝ n (fun z' => Ψ z' θ) z := by
  have hg : ContDiffAt ℝ n (fun z' : ℝ => (z', θ)) z := by
    have h1 : ContDiffAt ℝ n (fun z' : ℝ => (ContinuousLinearMap.inl ℝ ℝ ℝ) z') z :=
      ((ContinuousLinearMap.inl ℝ ℝ ℝ).contDiff (n := n)).contDiffAt
    have h2 : ContDiffAt ℝ n (fun _ : ℝ => (((0 : ℝ), θ) : ℝ × ℝ)) z := contDiffAt_const
    have h3 := h1.add h2
    convert h3 using 2
    simp [ContinuousLinearMap.inl_apply]
  exact h.comp z hg

/-- The `θ`-slice `θ' ↦ Ψ z θ'` of a function which is `C^n` at `(z,θ)` is `C^n` at `θ`. -/
lemma contDiffAt_uncurry_slice_snd (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) {n : WithTop ℕ∞}
    (h : ContDiffAt ℝ n (Function.uncurry Ψ) (z, θ)) :
    ContDiffAt ℝ n (fun θ' => Ψ z θ') θ := by
  have hg : ContDiffAt ℝ n (fun θ' : ℝ => (z, θ')) θ := by
    have h1 : ContDiffAt ℝ n (fun θ' : ℝ => (ContinuousLinearMap.inr ℝ ℝ ℝ) θ') θ :=
      ((ContinuousLinearMap.inr ℝ ℝ ℝ).contDiff (n := n)).contDiffAt
    have h2 : ContDiffAt ℝ n (fun _ : ℝ => (((z : ℝ), (0 : ℝ)) : ℝ × ℝ)) θ := contDiffAt_const
    have h3 := h1.add h2
    convert h3 using 2
    simp [ContinuousLinearMap.inr_apply]
  exact h.comp θ hg

/-! ## Additivity of the one-variable first and second derivatives -/

/-- `iteratedDeriv 1` is additive on functions differentiable at the point. -/
lemma iteratedDeriv_one_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (f + g) x = iteratedDeriv 1 f x + iteratedDeriv 1 g x := by
  simp only [iteratedDeriv_one]
  exact deriv_add (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))

/-- `iteratedDeriv 2 f = (deriv ∘ deriv) f`. -/
lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- `iteratedDeriv 2` is additive on functions which are `C²` at the point. -/
lemma iteratedDeriv_two_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (f + g) x = iteratedDeriv 2 f x + iteratedDeriv 2 g x := by
  rw [iteratedDeriv_two_eq, iteratedDeriv_two_eq, iteratedDeriv_two_eq]
  have hfeq : deriv (f + g) =ᶠ[nhds x] deriv f + deriv g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    rw [deriv_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))]
    rfl
  rw [Filter.EventuallyEq.deriv_eq hfeq]
  rw [deriv_add]
  · exact (ContDiffAt.derivWithin hf (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · exact (ContDiffAt.derivWithin hg (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-! ## The curried iterated partials as one-variable iterated derivatives -/

/-- `∂_z^k Ψ z θ` is the `k`-th iterated derivative of the `z`-slice. -/
lemma pzIter_eq_iteratedDeriv (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter k Ψ z θ = iteratedDeriv k (fun z' => Ψ z' θ) z := by
  induction k generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, iteratedDeriv_succ]
    simp only [Work.Spaces.pz]
    congr 1
    funext z'
    exact ih z'

/-- `∂_θ^k Ψ z θ` is the `k`-th iterated derivative of the `θ`-slice. -/
lemma pthIter_eq_iteratedDeriv (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k Ψ z θ = iteratedDeriv k (fun θ' => Ψ z θ') θ := by
  induction k generalizing θ with
  | zero => simp
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, iteratedDeriv_succ]
    simp only [Work.Spaces.pth]
    congr 1
    funext θ'
    exact ih θ'

/-- `∂_z Ψ z θ` is the first iterated derivative of the `z`-slice. -/
lemma pz_eq_iteratedDeriv_one (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz F z θ = iteratedDeriv 1 (fun z' => F z' θ) z := by
  have h := pzIter_eq_iteratedDeriv 1 F z θ
  simpa using h

/-! ## Additivity of the individual derivatives appearing in `bslOp` -/

/-- `∂_z` is additive on `C²` functions. -/
lemma pz_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pz (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pz Ψ z θ + Work.Spaces.pz Φ z θ := by
  rw [pz_eq_iteratedDeriv_one (fun z θ => Ψ z θ + Φ z θ) z θ,
      pz_eq_iteratedDeriv_one Ψ z θ, pz_eq_iteratedDeriv_one Φ z θ]
  exact iteratedDeriv_one_add (contDiffAt_uncurry_slice_fst Ψ z θ (hΨ.of_le (m := 1) (by norm_num)))
    (contDiffAt_uncurry_slice_fst Φ z θ (hΦ.of_le (m := 1) (by norm_num)))

/-- `∂_zz` is additive on `C²` functions. -/
lemma pzIter_two_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pzIter 2 Ψ z θ + Work.Spaces.pzIter 2 Φ z θ := by
  rw [pzIter_eq_iteratedDeriv 2 (fun z θ => Ψ z θ + Φ z θ) z θ,
      pzIter_eq_iteratedDeriv 2 Ψ z θ, pzIter_eq_iteratedDeriv 2 Φ z θ]
  exact iteratedDeriv_two_add (contDiffAt_uncurry_slice_fst Ψ z θ hΨ)
    (contDiffAt_uncurry_slice_fst Φ z θ hΦ)

/-- `∂_θθ` is additive on `C²` functions. -/
lemma pthIter_two_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Φ z θ) z θ
      = Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pthIter 2 Φ z θ := by
  rw [pthIter_eq_iteratedDeriv 2 (fun z θ => Ψ z θ + Φ z θ) z θ,
      pthIter_eq_iteratedDeriv 2 Ψ z θ, pthIter_eq_iteratedDeriv 2 Φ z θ]
  exact iteratedDeriv_two_add (contDiffAt_uncurry_slice_snd Ψ z θ hΨ)
    (contDiffAt_uncurry_slice_snd Φ z θ hΦ)

/-- `∂_θ(tan θ · ·)` is additive on `C²` functions (at `θ` with `cos θ ≠ 0`). -/
lemma pth_tan_mul_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Work.Spaces.pth (fun z θ => Real.tan θ * (Ψ z θ + Φ z θ)) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Φ z θ) z θ := by
  have h1 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (contDiffAt_uncurry_slice_snd Ψ z θ (hΨ.of_le (m := 1) (by norm_num)))).differentiableAt
        (by norm_num)
  have h2 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * Φ z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (contDiffAt_uncurry_slice_snd Φ z θ (hΦ.of_le (m := 1) (by norm_num)))).differentiableAt
        (by norm_num)
  simp only [Work.Spaces.pth]
  have key : (fun θ' : ℝ => Real.tan θ' * (Ψ z θ' + Φ z θ'))
      = (fun θ' : ℝ => Real.tan θ' * Ψ z θ' + Real.tan θ' * Φ z θ') := by
    funext θ'; ring
  rw [key]
  exact deriv_add h1 h2

/-! ## Additivity of `L₀` and of `bslOp` -/

/-- `L₀` is additive: `L₀(Ψ + Φ) = L₀Ψ + L₀Φ` at every `(z,θ)` with `cos θ ≠ 0`. -/
lemma Lzero_add (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    Lzero (fun z θ => Ψ z θ + Φ z θ) z θ = Lzero Ψ z θ + Lzero Φ z θ := by
  have h2 := pthIter_two_add Ψ Φ z θ hΨ hΦ
  have ht := pth_tan_mul_add Ψ Φ z θ hθ hΨ hΦ
  simp only [Lzero, h2, ht]
  ring

/-- `bslOp α` is additive. -/
lemma bslOp_add (α : ℝ) (Ψ Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ)) :
    bslOp α (fun z θ => Ψ z θ + Φ z θ) z θ = bslOp α Ψ z θ + bslOp α Φ z θ := by
  have h2 := pzIter_two_add Ψ Φ z θ hΨ hΦ
  have h1 := pz_add Ψ Φ z θ hΨ hΦ
  have hL := Lzero_add Ψ Φ z θ hθ hΨ hΦ
  simp only [bslOp_apply, h2, h1, hL]
  ring

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.half_pi_sin_hardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Elementary comparisons for `θ ∈ (0, π/2]` -/



/-! ## Integrability of the five weighted integrands -/




/-! ## The target theorem -/


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.hardy_op_L2_tonelli =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.Elliptic

set_option autoImplicit false

/-- The `Ioi 0`-truncated weight `s ↦ s ^ a * f s ^ 2` as an `ℝ≥0∞`-valued function. -/
noncomputable def hardyXi (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun s => ENNReal.ofReal (s ^ a * f s ^ 2))

/-- The `Ioi 0`-truncated Hardy weight `z ↦ z ^ (-c)`. -/
noncomputable def hardyA (c : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun z => ENNReal.ofReal (z ^ (-c)))

/-- The region `{(z,s) | 0 < s ≤ z}` of the double integral. -/
def hardyR : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}

theorem measurableSet_hardyR : MeasurableSet hardyR := by
  have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  exact h1.inter h2

theorem hardyXi_ne_top (a : ℝ) (f : ℝ → ℝ) (s : ℝ) : hardyXi a f s ≠ ⊤ := by
  unfold hardyXi
  by_cases h : s ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-- If `g` is a.e. measurable for the measure restricted to `s`, then the `s`-indicator of `g`
is a.e. measurable for the ambient measure. -/
theorem aemeasurable_indicator_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Zero β] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {g : α → β}
    (hg : AEMeasurable g (μ.restrict s)) : AEMeasurable (s.indicator g) μ := by
  obtain ⟨g', hg'm, hg'eq⟩ := hg
  refine ⟨s.indicator g', hg'm.indicator hs, ?_⟩
  have hg'eq' : ∀ᵐ x ∂(μ.restrict s), g x = g' x := hg'eq
  rw [MeasureTheory.ae_restrict_iff' hs] at hg'eq'
  filter_upwards [hg'eq'] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]; exact hx hxs
  · simp only [Set.indicator_of_notMem hxs]

theorem aemeasurable_hardyA (c : ℝ) : AEMeasurable (hardyA c) volume := by
  unfold hardyA
  refine aemeasurable_indicator_restrict measurableSet_Ioi ?_
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx)))).aemeasurable
      measurableSet_Ioi

theorem aemeasurable_hardyXi {a : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    AEMeasurable (hardyXi a f) volume := by
  unfold hardyXi
  refine aemeasurable_indicator_restrict measurableSet_Ioi ?_
  have h1 : AEMeasurable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioi 0)) :=
    hf.aestronglyMeasurable.aemeasurable
  have h2 : AEMeasurable (fun s : ℝ => s ^ a) (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx))).aemeasurable
      measurableSet_Ioi
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h1)

theorem ofReal_hardy_algebra {a c s y : ℝ} (hc : 1 < c) (ha : a = c - 1) (hs : 0 < s) :
    ENNReal.ofReal (s ^ a * y ^ 2) * ENNReal.ofReal (s ^ (1 - c) / (c - 1))
      = ENNReal.ofReal (1 / (c - 1)) * ENNReal.ofReal (y ^ 2) := by
  subst ha
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hp1 : (0 : ℝ) ≤ s ^ (c - 1) * y ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg y)
  have hp2 : (0 : ℝ) ≤ 1 / (c - 1) := (one_div_pos.mpr hc1).le
  have hrpow : s ^ (c - 1) * s ^ (1 - c) = 1 := by
    rw [← Real.rpow_add hs]
    have h : c - 1 + (1 - c) = 0 := by ring
    rw [h, Real.rpow_zero]
  rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hp2]
  congr 1
  rw [show s ^ (c - 1) * y ^ 2 * (s ^ (1 - c) / (c - 1))
        = (s ^ (c - 1) * s ^ (1 - c)) * y ^ 2 / (c - 1) by ring, hrpow, one_mul]
  ring

/-- The Tonelli (double integral) computation in general form. -/
theorem hardy_tonelli_swap (c a : ℝ) (hc : 1 < c) (ha : a = c - 1) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
      = ENNReal.ofReal (1 / (c - 1) * ∫ z in Set.Ioi 0, f z ^ 2) := by
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hΞ : AEMeasurable (hardyXi a f) volume := aemeasurable_hardyXi hf
  have hA : AEMeasurable (hardyA c) volume := aemeasurable_hardyA c
  have huncurry : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-c)) *
        (Set.Ioc 0 p.1).indicator (hardyXi a f) p.2) (volume.prod volume) := by
    have hpt : (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-c)) *
          (Set.Ioc 0 p.1).indicator (hardyXi a f) p.2)
        = fun p : ℝ × ℝ => hardyA c p.1 * hardyXi a f p.2 * hardyR.indicator (fun _ => 1) p := by
      funext p
      obtain ⟨z, s⟩ := p
      dsimp only
      by_cases h : s ∈ Set.Ioc 0 z
      · have hz : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le h.1 h.2
        have hmem : (z, s) ∈ hardyR := h
        unfold hardyA
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem h, Set.indicator_of_mem hmem, mul_one]
      · have hmem : (z, s) ∉ hardyR := h
        unfold hardyA hardyXi
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hmem]
        simp
    rw [hpt]
    exact ((hA.comp_fst).mul (hΞ.comp_snd)).mul
      (measurable_const.indicator measurableSet_hardyR).aemeasurable
  have hinner : ∀ z : ℝ, (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2))
      = ∫⁻ s in Set.Ioc 0 z, hardyXi a f s := by
    intro z
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    unfold hardyXi
    exact (Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs.1)
      (fun s => ENNReal.ofReal (s ^ a * f s ^ 2))).symm
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
      = ∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
          (Set.Ioc 0 z).indicator (hardyXi a f) s := by
    have h1a : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, hardyXi a f s) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [hinner z]
    have h1b : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, hardyXi a f s))
        = ∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s := by
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
  have h2 : (∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s)
      = ∫⁻ s, ∫⁻ z, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s :=
    lintegral_lintegral_swap huncurry
  have h3 : (∫⁻ s, ∫⁻ z, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s)
      = ∫⁻ s in Set.Ioi 0,
          hardyXi a f s * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hs]
      have hFeq : (fun z => ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s)
          = (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-c)) *
              hardyXi a f s) := by
        funext z
        by_cases hzs : s ≤ z
        · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 z from ⟨hs, hzs⟩),
              Set.indicator_of_mem (show z ∈ Set.Ici s from hzs)]
        · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hzs h.2),
              Set.indicator_of_notMem (show z ∉ Set.Ici s from hzs)]
          simp
      rw [hFeq, lintegral_indicator measurableSet_Ici]
      rw [show (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)) * hardyXi a f s)
            = ∫⁻ z in Set.Ici s, hardyXi a f s * ENNReal.ofReal (z ^ (-c)) from
          setLIntegral_congr_fun measurableSet_Ici (fun z _ => mul_comm _ _)]
      rw [lintegral_const_mul' (hardyXi a f s) (fun z => ENNReal.ofReal (z ^ (-c)))
        (hardyXi_ne_top a f s)]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun z => ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s) = fun _ => (0 : ℝ≥0∞) := by
        funext z
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hs h.1)]
        simp
      rw [hzero]
      simp
  have h4 : (∫⁻ s in Set.Ioi 0,
          hardyXi a f s * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - c) / (c - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    unfold hardyXi
    rw [lintegral_Ici_ofReal_rpow hc hs, Set.indicator_of_mem hs]
  have h5 : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
        ENNReal.ofReal (s ^ (1 - c) / (c - 1)))
      = ENNReal.ofReal (1 / (c - 1) * ∫ z in Set.Ioi 0, f z ^ 2) := by
    have h5a : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - c) / (c - 1)))
        = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (1 / (c - 1)) * ENNReal.ofReal (f s ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      exact ofReal_hardy_algebra hc ha hs
    rw [h5a, lintegral_const_mul' (ENNReal.ofReal (1 / (c - 1))) _ ENNReal.ofReal_ne_top]
    rw [show (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (f s ^ 2))
          = ENNReal.ofReal (∫ s in Set.Ioi 0, f s ^ 2) from
        (ofReal_integral_eq_lintegral_ofReal hf
          (Filter.Eventually.of_forall (fun z => sq_nonneg (f z)))).symm]
    rw [← ENNReal.ofReal_mul (one_div_pos.mpr hc1).le]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.integral_sinCos2_mul_sin_two =====
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

/-! ## Auxiliary trigonometric evaluations

We compute `∫_0^{π/2} sin θ cos²θ · sin(2nθ) dθ` by writing `sin θ cos²θ = (sin θ + sin 3θ)/4`
and expanding the product of two sines with the product-to-sum identity.  The building blocks
below are the antiderivative of `cos (aθ)` on `[0, π/2]` and the values of `sin` at odd
half-integer multiples of `π`. -/

/-- `sin ((2m+1)π/2) = (-1)^m`. -/
lemma sin_odd_pi_half (m : ℕ) : Real.sin ((2*(m:ℝ)+1) * π/2) = (-1:ℝ)^m := by
  rw [show (2*(m:ℝ)+1)*π/2 = (m:ℝ)*π + π/2 by ring]
  rw [Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  ring

/-- `sin ((2m-1)π/2) = -(-1)^m`. -/
lemma sin_two_m_sub_one (m : ℕ) : Real.sin ((2*(m:ℝ)-1)*π/2) = -(-1:ℝ)^m := by
  have h : (2*(m:ℝ)-1)*π/2 = ((2*(m:ℝ)+1)*π/2) - π := by ring
  rw [h, Real.sin_sub, Real.cos_pi, Real.sin_pi, sin_odd_pi_half]
  ring

/-- `sin ((2m+3)π/2) = -(-1)^m`. -/
lemma sin_two_m_add_three (m : ℕ) : Real.sin ((2*(m:ℝ)+3)*π/2) = -(-1:ℝ)^m := by
  have h : (2*(m:ℝ)+3)*π/2 = (2*((m+1:ℕ):ℝ)+1)*π/2 := by push_cast; ring
  rw [h, sin_odd_pi_half (m+1), pow_succ]
  ring

/-- `sin ((2m+5)π/2) = (-1)^m`. -/
lemma sin_two_m_add_five (m : ℕ) : Real.sin ((2*(m:ℝ)+5)*π/2) = (-1:ℝ)^m := by
  have h : (2*(m:ℝ)+5)*π/2 = (2*((m+2:ℕ):ℝ)+1)*π/2 := by push_cast; ring
  rw [h, sin_odd_pi_half (m+2), pow_add]
  ring

/-- The product-to-sum rewriting of the integrand: writing `sin θ cos²θ = (sin θ + sin 3θ)/4`
and expanding `sin x sin y = (cos (x-y) - cos (x+y))/2` gives
`sin θ cos²θ · sin (2bθ) = ((cos ((2b-1)θ) - cos ((2b+1)θ)) + (cos ((2b-3)θ) - cos ((2b+3)θ)))/8`. -/
lemma sinCos2_mul_sin_eq (b θ : ℝ) :
    sinCos2 θ * Real.sin (2*b*θ)
      = (1/8) * ((Real.cos ((2*b-1)*θ) - Real.cos ((2*b+1)*θ))
          + (Real.cos ((2*b-3)*θ) - Real.cos ((2*b+3)*θ))) := by
  have hs : sinCos2 θ = (1/4)*(Real.sin θ + Real.sin (3*θ)) := by
    have h : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [sinCos2, Real.sin_three_mul, h]; ring
  have e1 : Real.cos (θ - 2*b*θ) = Real.cos ((2*b-1)*θ) := by
    rw [show θ - 2*b*θ = -((2*b-1)*θ) by ring, Real.cos_neg]
  have e2 : Real.cos (θ + 2*b*θ) = Real.cos ((2*b+1)*θ) := by
    rw [show θ + 2*b*θ = (2*b+1)*θ by ring]
  have e3 : Real.cos (3*θ - 2*b*θ) = Real.cos ((2*b-3)*θ) := by
    rw [show 3*θ - 2*b*θ = -((2*b-3)*θ) by ring, Real.cos_neg]
  have e4 : Real.cos (3*θ + 2*b*θ) = Real.cos ((2*b+3)*θ) := by
    rw [show 3*θ + 2*b*θ = (2*b+3)*θ by ring]
  have h2 : Real.sin θ * Real.sin (2*b*θ)
      = (1/2)*(Real.cos ((2*b-1)*θ) - Real.cos ((2*b+1)*θ)) := by
    have := Real.two_mul_sin_mul_sin θ (2*b*θ)
    rw [e1, e2] at this
    linarith
  have h3 : Real.sin (3*θ) * Real.sin (2*b*θ)
      = (1/2)*(Real.cos ((2*b-3)*θ) - Real.cos ((2*b+3)*θ)) := by
    have := Real.two_mul_sin_mul_sin (3*θ) (2*b*θ)
    rw [e3, e4] at this
    linarith
  rw [hs, mul_assoc, add_mul, h2, h3]
  ring

/-- `∫_0^{π/2} cos (aθ) dθ = sin (aπ/2)/a` for `a ≠ 0`. -/
lemma integral_cos_mul (a : ℝ) (ha : a ≠ 0) :
    ∫ θ in (0:ℝ)..(π/2), Real.cos (a * θ) = Real.sin (a * π/2) / a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => Real.sin (a*θ)/a)
    (f' := fun θ => Real.cos (a*θ))]
  · rw [mul_div_assoc]; simp
  · intro x _
    have h1 : HasDerivAt (fun θ : ℝ => Real.sin (a*θ)) (Real.cos (a*x) * a) x :=
      (Real.hasDerivAt_sin (a*x)).comp x (hasDerivAt_const_mul (x := x) a)
    refine (h1.div_const a).congr_deriv ?_
    field_simp
  · exact (by fun_prop : Continuous fun θ : ℝ => Real.cos (a*θ)).intervalIntegrable _ _

/-- Linearity of the interval integral applied to the four-cosine combination produced by
`sinCos2_mul_sin_eq`. -/
lemma integral_cos_sub_sum (a1 a2 a3 a4 : ℝ) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (h4 : a4 ≠ 0) :
    ∫ θ in (0:ℝ)..(π/2),
        ((Real.cos (a1*θ) - Real.cos (a2*θ)) + (Real.cos (a3*θ) - Real.cos (a4*θ)))
      = Real.sin (a1*π/2)/a1 - Real.sin (a2*π/2)/a2
        + Real.sin (a3*π/2)/a3 - Real.sin (a4*π/2)/a4 := by
  have i1 : IntervalIntegrable (fun θ => Real.cos (a1*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => Real.cos (a2*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ => Real.cos (a3*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun θ => Real.cos (a4*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) (i3.sub i4),
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i3 i4,
      integral_cos_mul a1 h1, integral_cos_mul a2 h2, integral_cos_mul a3 h3,
      integral_cos_mul a4 h4]
  ring

theorem integral_sinCos2_mul_sin_two (n : ℕ) (hn : 1 ≤ n) :
    ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * (n : ℝ) * θ)
      = (-1 : ℝ) ^ n * (4 * (n : ℝ)) / ((4 * (n : ℝ) ^ 2 - 1) * (4 * (n : ℝ) ^ 2 - 9)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  push_cast
  have hIθ : (∫ θ in Work.Spaces.Iθ, sinCos2 θ * Real.sin (2 * ((m:ℝ)+1) * θ))
      = ∫ θ in (0:ℝ)..(π/2), sinCos2 θ * Real.sin (2 * ((m:ℝ)+1) * θ) := by
    change ∫ θ in Set.Icc 0 (π/2), sinCos2 θ * Real.sin (2*((m:ℝ)+1)*θ) = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  rw [hIθ]
  have hpoint : ∀ θ : ℝ, sinCos2 θ * Real.sin (2*((m:ℝ)+1)*θ)
      = (1/8) * ((Real.cos ((2*(m:ℝ)+1)*θ) - Real.cos ((2*(m:ℝ)+3)*θ))
          + (Real.cos ((2*(m:ℝ)-1)*θ) - Real.cos ((2*(m:ℝ)+5)*θ))) := by
    intro θ
    have h := sinCos2_mul_sin_eq ((m:ℝ)+1) θ
    have e1 : (2*((m:ℝ)+1)-1)*θ = (2*(m:ℝ)+1)*θ := by ring
    have e2 : (2*((m:ℝ)+1)+1)*θ = (2*(m:ℝ)+3)*θ := by ring
    have e3 : (2*((m:ℝ)+1)-3)*θ = (2*(m:ℝ)-1)*θ := by ring
    have e4 : (2*((m:ℝ)+1)+3)*θ = (2*(m:ℝ)+5)*θ := by ring
    rw [h, e1, e2, e3, e4]
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
  rw [intervalIntegral.integral_const_mul]
  have ha3 : (2*(m:ℝ)-1) ≠ 0 := by
    intro h
    have h2 : (2 * m : ℕ) = 1 := by
      have h' : ((2 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      exact_mod_cast h'
    omega
  rw [integral_cos_sub_sum (2*(m:ℝ)+1) (2*(m:ℝ)+3) (2*(m:ℝ)-1) (2*(m:ℝ)+5)
      (by positivity) (by positivity) ha3 (by positivity)]
  rw [sin_odd_pi_half m, sin_two_m_add_three m, sin_two_m_sub_one m, sin_two_m_add_five m]
  rw [show (-1:ℝ)^m.succ = -(-1:ℝ)^m by rw [pow_succ]; ring]
  set p : ℝ := (-1:ℝ)^m with hp
  have key : (1/8) * (p/(2*(m:ℝ)+1) - (-p)/(2*(m:ℝ)+3) + (-p)/(2*(m:ℝ)-1)
        - p/(2*(m:ℝ)+5))
      = -p * (4*((m:ℝ)+1)) / ((4*((m:ℝ)+1)^2-1)*(4*((m:ℝ)+1)^2-9)) := by
    have h5 : (4*((m:ℝ)+1)^2-1) ≠ 0 := by
      have : 4*((m:ℝ)+1)^2-1 = (2*(m:ℝ)+1)*(2*(m:ℝ)+3) := by ring
      rw [this]; exact mul_ne_zero (by positivity) (by positivity)
    have h6 : (4*((m:ℝ)+1)^2-9) ≠ 0 := by
      have : 4*((m:ℝ)+1)^2-9 = (2*(m:ℝ)-1)*(2*(m:ℝ)+5) := by ring
      rw [this]; exact mul_ne_zero ha3 (by positivity)
    field_simp
    ring
  exact key

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.integral_sin_two_mul_sinCos2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.Elliptic

/-- `∫_0^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15`.

Substituting `u = sin θ` turns the integrand `sin 2θ · sin θ cos²θ = 2 sin²θ cos³θ`
into `(2u² - 2u⁴) du`, so the integral is `∫_0^1 (2u² - 2u⁴) du = 2/3 - 2/5 = 4/15`. -/
theorem integral_sin_two_mul_sinCos2 :
    ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ = 4 / 15 := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  -- rewrite the integrand in the form `(g ∘ sin) θ * cos θ` with `g u = 2u² - 2u⁴`
  have hpt : ∀ θ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ
      = ((fun u : ℝ => 2 * u ^ 2 - 2 * u ^ 4) ∘ Real.sin) θ * Real.cos θ := by
    intro θ
    simp only [Function.comp_apply]
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul]
    linear_combination (2 * Real.sin θ ^ 2 * Real.cos θ) * Real.sin_sq_add_cos_sq θ
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  -- change of variables `u = sin θ`
  rw [intervalIntegral.integral_comp_mul_deriv
      (f := Real.sin) (f' := Real.cos) (g := fun u : ℝ => 2 * u ^ 2 - 2 * u ^ 4)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn (by fun_prop)]
  simp only [Real.sin_zero, Real.sin_pi_div_two]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => 2 * u ^ 2).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun u : ℝ => 2 * u ^ 4).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
  norm_num

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.pth_DzIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pth` commutes with the iterates of `D_z`

For a function `Φ` that is smooth on an open neighbourhood of the closed quadrant
(`Work.Spaces.SmoothNbhd Φ`) the plain angular derivative `pth = ∂_θ` commutes with
every iterate of `D_z = z ∂_z` on that neighbourhood:

  `∂_θ (D_z^j Φ) = D_z^j (∂_θ Φ)`  on `Iz × Iθ`.

The point is that `∂_θ` commutes with multiplication by the radial variable `z` (the
factor `z` does not depend on `θ`) and with `∂_z` (Clairaut/Schwarz, available because
`Φ` is `C^∞` on an open neighbourhood of the quadrant).  The iteration is organized as
an equality on the open set `nbhU`, where both sides are honest derivatives, because the
inductive step needs to differentiate the two sides with respect to `z` (`pz_congr`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

/-- One step of the commutation: at a point of the neighbourhood where `g` is smooth,
`∂_θ (D_z g) = D_z (∂_θ g)`. -/
lemma pth_Dz_apply {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ} (hy : y ∈ Work.Spaces.nbhU)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry g) y :=
    (ContDiffOn.contDiffAt hg (Work.Spaces.isOpen_nbhU.mem_nhds hy)).of_le (by norm_num)
  -- `∂_θ (z · ∂_z g) = z · ∂_θ ∂_z g`
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  -- Clairaut: `∂_θ ∂_z g = ∂_z ∂_θ g`
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) h2).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

/-- On `nbhU` the angular derivative of the `j`-th `D_z`-iterate of `Φ` is the
`j`-th `D_z`-iterate of its angular derivative. -/
lemma pth_DzIter_eqOn (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) Work.Spaces.nbhU := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j Φ) :=
      Work.Spaces.SmoothNbhd.DzIter hΦ j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y :=
      pth_Dz_apply hy hs
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) y :=
      Work.Spaces.Dz_congr ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) Φ)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)) y
    rw [show Work.Spaces.DzIter (j+1) Φ = Work.Spaces.Dz (Work.Spaces.DzIter j Φ) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) from rfl]
    exact hstep.trans hcongr


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.sin_l2_weight_bound =====
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
-- ===== merged: Submission.Work.Elliptic.sin_weight_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory
open Set

namespace Work.Elliptic

/-- `sin(2θ)^{-p}` is dominated by the endpoint majorant for every `0 ≤ p`
(the case `p = 0` is trivial, the rest is Jordan's inequality). -/
private lemma sin_rpow_le_majorant0 {p θ : ℝ} (hp : 0 ≤ p) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-p) ≤
      (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) := by
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    simp only [neg_zero, Real.rpow_zero]
    norm_num
  · exact Work.Spaces.sin_rpow_le_majorant_pi p θ h hθ

/-- `min θ (π/2-θ)² · θ^{-(2+η)} ≤ θ^{-η}`. -/
private lemma min_sq_mul_rpow_le_left {η θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) ≤ θ ^ (-η) := by
  have hφ0 : 0 < Real.pi / 2 - θ := by linarith
  have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
  have hle : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hm0 (min_le_left _ _) 2
  have hw : 0 ≤ θ ^ (-(2 + η)) := Real.rpow_nonneg hθ0.le _
  calc (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η))
      ≤ θ ^ 2 * θ ^ (-(2 + η)) := mul_le_mul_of_nonneg_right hle hw
    _ = θ ^ (-η) := by
        rw [show θ ^ 2 = θ ^ (2 : ℝ) by norm_num [Real.rpow_two],
          ← Real.rpow_add hθ0 (2 : ℝ) (-(2 + η))]
        ring_nf

/-- `min θ (π/2-θ)² · (π/2-θ)^{-(2+η)} ≤ (π/2-θ)^{-η}`. -/
private lemma min_sq_mul_rpow_le_right {η θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) ≤
      (Real.pi / 2 - θ) ^ (-η) := by
  have hφ0 : 0 < Real.pi / 2 - θ := by linarith
  have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
  have hle : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
    pow_le_pow_left₀ hm0 (min_le_right _ _) 2
  have hw : 0 ≤ (Real.pi / 2 - θ) ^ (-(2 + η)) := Real.rpow_nonneg hφ0.le _
  calc (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η))
      ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) := mul_le_mul_of_nonneg_right hle hw
    _ = (Real.pi / 2 - θ) ^ (-η) := by
        rw [show (Real.pi / 2 - θ) ^ 2 = (Real.pi / 2 - θ) ^ (2 : ℝ) by
              norm_num [Real.rpow_two],
          ← Real.rpow_add hφ0 (2 : ℝ) (-(2 + η))]
        ring_nf

/-- The five pointwise majorant estimates. -/
theorem sin_weight_pointwise_majorants {η C C' : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') {f : ℝ → ℝ}
    (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ))
    (hf' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C') :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (2 * θ) ^ (-(2 + η))|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(deriv f θ) ^ 2 * (2 * θ) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
  have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hK1 : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hpi4 _)
  have hK2 : 0 ≤ C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η :=
    mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) (Real.rpow_nonneg hpi4 _)
  have hK3 : 0 ≤ C' ^ 2 * (Real.pi / 4) ^ η :=
    mul_nonneg (sq_nonneg C') (Real.rpow_nonneg hpi4 _)
  have hK4 : 0 ≤ C ^ 2 * (2 : ℝ) ^ (-(2 + η)) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg h2 _)
  have hK5 : 0 ≤ C' ^ 2 * (2 : ℝ) ^ (-η) :=
    mul_nonneg (sq_nonneg C') (Real.rpow_nonneg h2 _)
  set K : ℝ := C ^ 2 * (Real.pi / 4) ^ (2 + η) + C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η
    + C' ^ 2 * (Real.pi / 4) ^ η + C ^ 2 * (2 : ℝ) ^ (-(2 + η)) + C' ^ 2 * (2 : ℝ) ^ (-η)
    with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKnn, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hsinb : (Real.sin (2 * θ)) ^ (-(2 + η)) ≤
        (Real.pi / 4) ^ (2 + η) * (θ ^ (-(2 + η)) + (Real.pi / 2 - θ) ^ (-(2 + η))) :=
      sin_rpow_le_majorant0 (p := 2 + η) (by linarith) hIcc
    have hmn : 0 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by positivity
    calc |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((Real.pi / 4) ^ (2 + η) *
              (θ ^ (-(2 + η)) + (Real.pi / 2 - θ) ^ (-(2 + η)))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 hsinb hw hmn
      _ = (C ^ 2 * (Real.pi / 4) ^ (2 + η)) *
            ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) +
              (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η))) := by ring
      _ ≤ (C ^ 2 * (Real.pi / 4) ^ (2 + η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (min_sq_mul_rpow_le_left hθ0 hθ.2) (min_sq_mul_rpow_le_right hθ0 hθ.2))
            hK1
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK2, hK3, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
    have hmle : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 := le_trans (min_le_left _ _) hθ.2.le
    have hm2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2) ^ 2 :=
      pow_le_pow_left₀ hm0 hmle 2
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hsinb : (Real.sin (2 * θ)) ^ (-η) ≤
        (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      sin_rpow_le_majorant0 (p := η) hη0 hIcc
    have hcoef : 0 ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      mul_nonneg (Real.rpow_nonneg hpi4 _) hG
    calc |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 hsinb hw (by positivity)
      _ ≤ (C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η) *
            (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
          have h1 : C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 ≤ C ^ 2 * (Real.pi / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hm2 (sq_nonneg C)
          have h2 := mul_le_mul_of_nonneg_right h1 hcoef
          calc C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
              = (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by ring
            _ ≤ (C ^ 2 * (Real.pi / 2) ^ 2) *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := h2
            _ = (C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η) *
                (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK3, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hd2 : (deriv f θ) ^ 2 ≤ C' ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf' θ hθ) 2
    have hsinb : (Real.sin (2 * θ)) ^ (-η) ≤
        (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      sin_rpow_le_majorant0 (p := η) hη0 hIcc
    calc |(deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
        ≤ C' ^ 2 * ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hw]
          exact mul_le_mul hd2 hsinb hw (by positivity)
      _ = (C' ^ 2 * (Real.pi / 4) ^ η) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hmm : (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) ≤ θ ^ (-η) :=
      min_sq_mul_rpow_le_left hθ0 hθ.2
    have hmul : (2 * θ) ^ (-(2 + η)) = (2 : ℝ) ^ (-(2 + η)) * θ ^ (-(2 + η)) :=
      Real.mul_rpow h2 hθ0.le
    have hw : 0 ≤ (2 * θ) ^ (-(2 + η)) :=
      Real.rpow_nonneg (mul_nonneg (by norm_num) hθ0.le) _
    calc |f θ ^ 2 * (2 * θ) ^ (-(2 + η))|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((2 : ℝ) ^ (-(2 + η)) * θ ^ (-(2 + η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 (le_of_eq hmul) hw (by positivity)
      _ = (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) *
            ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η))) := by ring
      _ ≤ (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) * θ ^ (-η) :=
          mul_le_mul_of_nonneg_left hmm hK4
      _ ≤ (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hφ0.le _)) hK4
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK3, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hd2 : (deriv f θ) ^ 2 ≤ C' ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf' θ hθ) 2
    have hmul : (2 * θ) ^ (-η) = (2 : ℝ) ^ (-η) * θ ^ (-η) := Real.mul_rpow h2 hθ0.le
    have hw : 0 ≤ (2 * θ) ^ (-η) :=
      Real.rpow_nonneg (mul_nonneg (by norm_num) hθ0.le) _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    calc |(deriv f θ) ^ 2 * (2 * θ) ^ (-η)|
        ≤ C' ^ 2 * ((2 : ℝ) ^ (-η) * θ ^ (-η)) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hw]
          exact mul_le_mul hd2 (le_of_eq hmul) hw (by positivity)
      _ = (C' ^ 2 * (2 : ℝ) ^ (-η)) * θ ^ (-η) := by ring
      _ ≤ (C' ^ 2 * (2 : ℝ) ^ (-η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hφ0.le _)) hK5
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK3, hK4]) hG

/-- Continuity on the open interval of the five integrands. -/
theorem continuousOn_sin_weight_integrals {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) {η : ℝ} (hη0 : 0 ≤ η) :
    ContinuousOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => f θ ^ 2 * (2 * θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => (deriv f θ) ^ 2 * (2 * θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  have hfd : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : ContinuousOn (derivWithin f (Set.Icc 0 (Real.pi / 2)))
        (Set.Icc 0 (Real.pi / 2)) :=
      hf.continuousOn_derivWithin (uniqueDiffOn_Icc h2) le_rfl
    refine (hd.mono hIoo).congr ?_
    intro θ hθ
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  have hf2 : ContinuousOn (fun θ => f θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.continuousOn.mono hIoo).pow 2
  have hd2 : ContinuousOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := hfd.pow 2
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have htwo : ContinuousOn (fun θ : ℝ => 2 * θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuous_const.mul continuous_id).continuousOn
  have hsinne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have htwone : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (by linarith [hθ.1])
  have hs1 : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const fun θ hθ => Or.inl (hsinne θ hθ)
  have hs2 : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const fun θ hθ => Or.inl (hsinne θ hθ)
  have ht1 : ContinuousOn (fun θ => (2 * θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) :=
    htwo.rpow_const fun θ hθ => Or.inl (htwone θ hθ)
  have ht2 : ContinuousOn (fun θ => (2 * θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
    htwo.rpow_const fun θ hθ => Or.inl (htwone θ hθ)
  exact ⟨hf2.mul hs1, hf2.mul hs2, hd2.mul hs2, hf2.mul ht1, hd2.mul ht2⟩

/-- **Target lemma.** All five weighted integrals are interval integrable on `[0, π/2]`. -/
theorem sin_weight_integrable {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) (hpi : f (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (2 * θ) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (2 * θ) ^ (-η)) volume 0 (Real.pi / 2) := by
  obtain ⟨C, hC, hfC, hdC⟩ := contDiffOn_one_bounds hf h0 hpi
  have hfIoo : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ) :=
    fun θ hθ => hfC θ (Set.Ioo_subset_Icc_self hθ)
  have hdIoo : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := by
    intro θ hθ
    rw [← Real.norm_eq_abs]
    exact hdC θ hθ
  obtain ⟨K, hK, hm1, hm2, hm3, hm4, hm5⟩ :=
    sin_weight_pointwise_majorants hη0 hη1 hC hC hfIoo hdIoo
  obtain ⟨c1, c2, c3, c4, c5⟩ := continuousOn_sin_weight_integrals hf hη0
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := Real.pi_div_two_pos.le
  have key : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) →
      IntervalIntegrable g volume 0 (Real.pi / 2) := by
    intro g hgc hb
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2).mpr
      (integrableOn_of_rpow_majorant hη0 hη1 hK hgc hb)
  have e1 := key _ c1 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm1 θ hθ)
  have e2 := key _ c2 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm2 θ hθ)
  have e3 := key _ c3 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm3 θ hθ)
  have e4 := key _ c4 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm4 θ hθ)
  have e5 := key _ c5 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm5 θ hθ)
  exact ⟨e1, e2, e3, e4, e5⟩

end Work.Elliptic
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.twoIbpEtaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Topology Interval
open Filter Set MeasureTheory

set_option autoImplicit false
-- `haveI` is genuinely needed below (to register `NeBot l` for `tendsto_nhds_unique`)
set_option linter.style.haveILetI false

/-- The set integral over `Ioo a b` is the interval integral over `a..b`. -/
theorem setIntegral_Ioo_eq_intervalIntegral (g : ℝ → ℝ) {a b : ℝ} (h : a ≤ b) :
    ∫ x in Ioo a b, g x = ∫ x in a..b, g x := by
  rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b)),
    ← intervalIntegral.integral_of_le h]

/-- The interval integral over `ε..t` tends to the one over `0..t` as `ε ↓ 0`. -/
theorem tendsto_intervalIntegral_left (g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg : IntegrableOn g (Ioo 0 t)) :
    Tendsto (fun ε : ℝ => ∫ x in ε..t, g x) (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫ x in (0 : ℝ)..t, g x)) := by
  have h_int : IntegrableOn g (uIcc 0 t) := by
    rw [uIcc_of_le ht.le]
    exact hg.congr_set_ae Ioo_ae_eq_Icc.symm
  have hcont : ContinuousOn (fun x : ℝ => ∫ s in x..t, g s) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval_left h_int
  have hmem : uIcc (0 : ℝ) t ∈ 𝓝[Ioi (0 : ℝ)] 0 := by
    rw [uIcc_of_le ht.le, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Iio t, isOpen_Iio.mem_nhds ht,
      fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hle : 𝓝[Ioi (0 : ℝ)] 0 ≤ 𝓝[uIcc (0 : ℝ) t] 0 := nhdsWithin_le_iff.mpr hmem
  exact (hcont.continuousWithinAt left_mem_uIcc).mono_left hle

/-- The two-integration-by-parts identity on `[ε,t]`, `0 < ε < t`. -/
theorem ibpEtaTEpsilon (f : ℝ → ℝ) (t ε : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2) (hε : 0 < ε) (hεt : ε < t)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 (Real.pi / 2))) :
    etaT' t ε * f ε
      = (∫ x in ε..t, etaT t x * deriv (deriv f) x)
        - (∫ x in ε..t, etaT'' t x * f x)
        + etaT t ε * deriv f ε := by
  have hsub : uIcc ε t ⊆ Ioo 0 (Real.pi / 2) := by
    rw [uIcc_of_le hεt.le]
    intro x hx
    exact ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 hta⟩
  have hm1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdη : ∀ x ∈ uIcc ε t, HasDerivAt (etaT t) (etaT' t x) x :=
    fun x _ => etaT_hasDerivAt t x
  have hdη' : ∀ x ∈ uIcc ε t, HasDerivAt (etaT' t) (etaT'' t x) x :=
    fun x _ => etaT'_hasDerivAt t x
  have hdf : ∀ x ∈ uIcc ε t, HasDerivAt f (deriv f x) x := fun x hx =>
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by decide)).hasDerivAt
  have hdf' : ∀ x ∈ uIcc ε t, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    ((hm1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by decide)).hasDerivAt
  have hcont_df : ContinuousOn (deriv f) (uIcc ε t) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcont_df' : ContinuousOn (deriv (deriv f)) (uIcc ε t) :=
    (hm1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hint_df : IntervalIntegrable (deriv f) volume ε t := hcont_df.intervalIntegrable
  have hint_df' : IntervalIntegrable (deriv (deriv f)) volume ε t := hcont_df'.intervalIntegrable
  have hint_η' : IntervalIntegrable (etaT' t) volume ε t :=
    (continuous_etaT' t).continuousOn.intervalIntegrable
  have hint_η'' : IntervalIntegrable (etaT'' t) volume ε t :=
    (continuous_etaT'' t).continuousOn.intervalIntegrable
  have h₁ : ∫ x in ε..t, etaT t x * deriv (deriv f) x
      = etaT t t * deriv f t - etaT t ε * deriv f ε - ∫ x in ε..t, etaT' t x * deriv f x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hdη hdf' hint_η' hint_df'
  have h₂ : ∫ x in ε..t, etaT' t x * deriv f x
      = etaT' t t * f t - etaT' t ε * f ε - ∫ x in ε..t, etaT'' t x * f x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hdη' hdf hint_η'' hint_df
  rw [h₁, h₂, etaT_at_t t ht.ne', etaT'_at_t t ht.ne']
  ring

theorem twoIbpEtaT (f : ℝ → ℝ) (F t : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (hbdd : ∃ M, ∀ x ∈ Set.Ioo 0 t, |deriv f x| ≤ M)
    (h1 : MeasureTheory.IntegrableOn (fun x : ℝ => f x) (Set.Ioo 0 t))
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => deriv (deriv f) x) (Set.Ioo 0 t)) :
    F = (∫ x in Set.Ioo 0 t, Work.EllipticEst.Core.i0Aux.etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, Work.EllipticEst.Core.i0Aux.etaT'' t x * f x := by
  set l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0) with hl
  -- the two products are integrable on `(0,t)`
  have hintA : IntegrableOn (fun x : ℝ => etaT t x * deriv (deriv f) x) (Ioo 0 t) :=
    ((h2.congr_set_ae Ioo_ae_eq_Icc.symm).continuousOn_mul
      ((continuous_etaT t).continuousOn (s := Icc 0 t)) isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hintB : IntegrableOn (fun x : ℝ => etaT'' t x * f x) (Ioo 0 t) :=
    ((h1.congr_set_ae Ioo_ae_eq_Icc.symm).continuousOn_mul
      ((continuous_etaT'' t).continuousOn (s := Icc 0 t)) isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  -- `(0,t)` is an eventual neighbourhood of `0` for the one-sided filter
  have hev : ∀ᶠ ε : ℝ in l, ε ∈ Ioo 0 t := by
    rw [hl]
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht)]
      with ε hε hεt
    exact ⟨hε, hεt⟩
  -- the three limits of the right-hand side
  have hlimA : Tendsto (fun ε : ℝ => ∫ x in ε..t, etaT t x * deriv (deriv f) x) l
      (𝓝 (∫ x in (0 : ℝ)..t, etaT t x * deriv (deriv f) x)) :=
    tendsto_intervalIntegral_left _ t ht hintA
  have hlimB : Tendsto (fun ε : ℝ => ∫ x in ε..t, etaT'' t x * f x) l
      (𝓝 (∫ x in (0 : ℝ)..t, etaT'' t x * f x)) :=
    tendsto_intervalIntegral_left _ t ht hintB
  have hlimC : Tendsto (fun ε : ℝ => etaT t ε * deriv f ε) l (𝓝 0) := by
    have hη : Tendsto (fun ε : ℝ => etaT t ε) l (𝓝 0) := by
      have h0 := ((continuous_etaT t).continuousAt (x := 0)).tendsto
      rw [etaT_zero t] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine hη.zero_mul_isBoundedUnder_le ?_
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, hev.mono fun ε hε => by simpa [Real.norm_eq_abs] using hM ε hε⟩
  -- the limit of the left-hand side
  have hlimE : Tendsto (fun ε : ℝ => etaT' t ε * f ε) l (𝓝 F) := by
    have hderiv : Tendsto (fun ε : ℝ => etaT' t ε) l (𝓝 1) := by
      have h0 := ((continuous_etaT' t).continuousAt (x := 0)).tendsto
      rw [etaT'_zero t] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    simpa [mul_comm] using hlim.mul hderiv
  -- the two sides agree eventually
  have heq : (fun ε : ℝ => etaT' t ε * f ε) =ᶠ[l]
      (fun ε : ℝ => (∫ x in ε..t, etaT t x * deriv (deriv f) x)
        - (∫ x in ε..t, etaT'' t x * f x) + etaT t ε * deriv f ε) := by
    filter_upwards [hev] with ε hε
    exact ibpEtaTEpsilon f t ε ht hta hε.1 hε.2 hf
  have hNeBot : NeBot l := by
    rw [hl, nhdsWithin_neBot]
    intro u hu
    rcases Metric.mem_nhds_iff.mp hu with ⟨δ, hδ, hsub⟩
    exact ⟨δ / 2,
      hsub (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
        linarith),
      half_pos hδ⟩
  haveI := hNeBot
  have hR : Tendsto (fun ε : ℝ => (∫ x in ε..t, etaT t x * deriv (deriv f) x)
      - (∫ x in ε..t, etaT'' t x * f x) + etaT t ε * deriv f ε) l
      (𝓝 ((∫ x in (0 : ℝ)..t, etaT t x * deriv (deriv f) x)
        - (∫ x in (0 : ℝ)..t, etaT'' t x * f x) + 0)) := (hlimA.sub hlimB).add hlimC
  have huniq := tendsto_nhds_unique hlimE (hR.congr' heq.symm)
  rw [huniq]
  rw [setIntegral_Ioo_eq_intervalIntegral (fun x => etaT t x * deriv (deriv f) x) ht.le,
    setIntegral_Ioo_eq_intervalIntegral (fun x => etaT'' t x * f x) ht.le]
  ring

end Work.EllipticEst.Core.i0Aux.EndpointValues
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.youngE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory

/-- Young's convolution inequality in the form needed for the interior-regularity gain step:
if `f` is dominated pointwise (`‖f x‖ₑ ≤ ∫⁻ y, F (x - y) * u y`) by the convolution of an
integrable nonnegative `F` with a nonnegative `u ∈ L²`, then `‖f‖₂ ≤ ‖F‖₁ ‖u‖₂`.

The analytic content is `conv_l2_lintegral`: the squared `L²` mass of the lintegral
convolution `x ↦ ∫⁻ y, F (x - y) * u y` is bounded by `‖F‖₁² ‖u‖₂²`; the rest is
monotonicity of `eLpNorm` together with the computation of `eLpNorm` as
`(∫⁻ ‖·‖ₑ ^ p) ^ (1/p)`. -/
theorem youngE {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : MeasureTheory.Integrable F MeasureTheory.volume)
    (huM : MeasureTheory.MemLp u 2 MeasureTheory.volume)
    {f : E → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hpt : ∀ x : E, ‖f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u 2 MeasureTheory.volume := by
  -- the analytic core: the `L²` mass of the convolution integrand
  have hcore : (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
        ∂(volume : Measure E))
      ≤ (∫⁻ z, ENNReal.ofReal (F z)) * ((∫⁻ z, ENNReal.ofReal (F z))
          * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := conv_l2_lintegral hF hu hFi huM
  -- `∫⁻ ofReal F = ofReal (∫ F)`
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  -- `eLpNorm u 2` in lintegral form
  have hunorm : MeasureTheory.eLpNorm u (2:ENNReal) (volume : Measure E)
      = (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ENNReal)) (by norm_num) (by norm_num)
        huM.aestronglyMeasurable, eLpNorm'_eq_lintegral_enorm]
    norm_num
    congr 1
    refine lintegral_congr (fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu y)]
    exact (ENNReal.ofReal_pow (hu y) 2).symm
  -- `eLpNorm f 2` in lintegral form
  have hfE : MeasureTheory.eLpNorm f (2:ENNReal) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume : Measure E)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num)
      (by norm_num) hf]
    norm_num
  calc MeasureTheory.eLpNorm f (2:ENNReal) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume : Measure E)) ^ ((1:ℝ)/2) := hfE
    _ ≤ (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
          ∂(volume : Measure E)) ^ ((1:ℝ)/2) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono (fun x => ?_)) (by norm_num)
        exact ENNReal.rpow_le_rpow (hpt x) (by norm_num)
    _ ≤ ((∫⁻ z, ENNReal.ofReal (F z)) * ((∫⁻ z, ENNReal.ofReal (F z))
          * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
        ENNReal.rpow_le_rpow hcore (by norm_num)
    _ = ENNReal.ofReal (∫ z, F z) * MeasureTheory.eLpNorm u (2:ENNReal)
          (volume : Measure E) := by
        rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
          ← ENNReal.rpow_mul]
        norm_num
        rw [← hAeq, ← hunorm]

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.mms_Phi_estimate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform MeasureTheory Filter
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Elementary norm facts -/

/-- The `ℝ≥0∞`-valued norm of a complex number is `ofReal` of its norm. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, show (↑(‖z‖₊) : ℝ) = ‖z‖ from rfl]

/-- The norm of a real number seen as a complex number is its absolute value. -/
lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  have h1 : (0 : ℝ) ≤ ‖((r : ℝ) : ℂ)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ |r| := abs_nonneg r
  nlinarith [h, sq_abs r]

/-- Peetre's inequality, in the form used for the Fourier multiplier estimate:
`⟨ξ⟩^s ⟨y⟩^{-s} ≤ 2^{|s|/2} ⟨ξ - y⟩^{|s|}`. -/
lemma mms_weight_le (s : ℝ) (ξ y : E) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      ≤ 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) := by
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  have h := peetre s ξ y
  have hnp : 0 ≤ (1 + ‖y‖ ^ 2) ^ (-s / 2) := le_of_lt (Real.rpow_pos_of_pos hp _)
  have hde : (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) = 1 := by
    rw [← Real.rpow_add hp, show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right h hnp
  refine h2.trans_eq ?_
  calc 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2)
        * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)
          * ((1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)) := by ring
    _ = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) := by rw [hde, mul_one]

/-! ## The Fourier side of `mms_Phi` -/

/-- Pointwise formula for the Fourier transform of `mms_Phi s γS k`. -/
lemma mms_fourier_Phi_eq (s : ℝ) (γS k : 𝓢(E, ℂ)) (ξ : E) :
    FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ
      = mms_wfun (E := E) s ξ * ∫ η, FourierTransform.fourier (⇑γS) η *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η)) := by
  rw [← SchwartzMap.fourier_coe (mms_Phi s γS k)]
  have h1 : (FourierTransform.fourier (mms_Phi s γS k) : 𝓢(E, ℂ))
      = SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) s)
          (FourierTransform.fourier (SchwartzMap.smulLeftCLM ℂ (⇑γS)
            (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k))) := by
    rw [mms_Phi,
      mms_fourier_fourierMultiplier (mms_wfun (E := E) s) (mms_wfun_temperate s)]
  have h2 : ⇑(FourierTransform.fourier (SchwartzMap.smulLeftCLM ℂ (⇑γS)
        (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k)) : 𝓢(E, ℂ))
      = fun ζ => ∫ η, FourierTransform.fourier (⇑γS) η *
        ⇑(FourierTransform.fourier (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k)
          : 𝓢(E, ℂ)) (ζ - η) :=
    fourier_smulLeftCLM_eq_convolution γS _
  have h3 : ⇑(FourierTransform.fourier
        (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k) : 𝓢(E, ℂ))
      = fun ζ => mms_wfun (-s) ζ * FourierTransform.fourier (⇑k) ζ := by
    rw [mms_fourier_fourierMultiplier (mms_wfun (E := E) (-s)) (mms_wfun_temperate (-s))]
    funext ζ
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (-s)), smul_eq_mul,
      SchwartzMap.fourier_coe k]
  rw [h1, SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate s), h2, h3]
  rw [smul_eq_mul]

/-! ## The pointwise `ℝ≥0∞`-bound -/

/-- Pointwise domination of `‖𝓕(mms_Phi s γS k)(ξ)‖` by the `ℝ≥0∞`-integral of the
convolution kernel against `‖𝓕k‖`. -/
lemma mms_Phi_enorm_le (s : ℝ) (γS k : 𝓢(E, ℂ)) (ξ : E) :
    ‖FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal
          (‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖ *
            ‖FourierTransform.fourier (⇑k) y‖) ∂(volume : Measure E) := by
  have hkey : FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ
      = ∫ η, (mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η)) := by
    rw [mms_fourier_Phi_eq s γS k ξ, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun η => by ring)
  rw [hkey]
  calc ‖∫ η, (mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
      ≤ ∫⁻ η, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
            ∂(volume : Measure E) :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ η, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η)‖ₑ *
          ‖(mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
            ∂(volume : Measure E) := by
        refine lintegral_congr fun η => ?_
        rw [enorm_mul]
    _ = ∫⁻ y, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) (ξ - y))‖ₑ *
          ‖(mms_wfun (E := E) (-s) y * FourierTransform.fourier (⇑k) y)‖ₑ
            ∂(volume : Measure E) := by
        rw [← lintegral_sub_left_eq_self (fun η =>
          ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η)‖ₑ *
          ‖(mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ) ξ]
        refine lintegral_congr fun y => ?_
        simp only [sub_sub_cancel]
    _ ≤ ∫⁻ y, ENNReal.ofReal
          (‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖ *
            ‖FourierTransform.fourier (⇑k) y‖) ∂(volume : Measure E) := by
        refine lintegral_mono fun y => ?_
        have h1 : ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) (ξ - y))‖ₑ
            = ENNReal.ofReal
                (‖mms_wfun (E := E) s ξ‖ * ‖FourierTransform.fourier (⇑γS) (ξ - y)‖) := by
          rw [enorm_mul, enorm_complex_eq_ofReal, enorm_complex_eq_ofReal,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
        have h2 : ‖(mms_wfun (E := E) (-s) y * FourierTransform.fourier (⇑k) y)‖ₑ
            = ENNReal.ofReal
                (‖mms_wfun (E := E) (-s) y‖ * ‖FourierTransform.fourier (⇑k) y‖) := by
          rw [enorm_mul, enorm_complex_eq_ofReal, enorm_complex_eq_ofReal,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
        rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hFs : ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖
            = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
              ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ := by
          rw [norm_mul, norm_ofReal_complex, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _),
            norm_mul, mms_norm_wfun]
          ring
        rw [hFs, mms_norm_wfun s ξ, mms_norm_wfun (-s) y]
        have hle := mms_weight_le s ξ y
        have hB : 0 ≤ ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ := norm_nonneg _
        have hD : 0 ≤ ‖FourierTransform.fourier (⇑k) y‖ := norm_nonneg _
        have hmain : (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖)
            ≤ (2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hB hD)
        calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
              ((1 + ‖y‖ ^ 2) ^ (-s / 2) * ‖FourierTransform.fourier (⇑k) y‖)
            = (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) := by ring
          _ ≤ (2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) := hmain
          _ = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
              ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
              ‖FourierTransform.fourier (⇑k) y‖ := by ring

/-! ## The estimate -/


end Work.EllipticEst.InteriorRegularity
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.Lneg_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

theorem Lneg_rpow (α : ℝ) (m : ℕ) {s z : ℝ} (hz : 0 < z)
    (hs : α ^ 2 * s ^ 2 + 5 * α * s = Work.FTS.PhiStar.Radial.lamR m) :
    Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α (fun t => t ^ s) z
      = - Work.FTS.PhiStar.Radial.lamR m * z ^ s := by
  have hz' : z ≠ 0 := ne_of_gt hz
  rw [Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg]
  -- the first two derivatives of `t ↦ t ^ s` at `z`
  have hd1 : deriv (fun t : ℝ => t ^ s) z = s * z ^ (s - 1) := Real.deriv_rpow_const z s
  have hd2 : deriv (deriv (fun t : ℝ => t ^ s)) z = s * ((s - 1) * z ^ (s - 1 - 1)) := by
    rw [Real.deriv_rpow_const' s]
    rw [deriv_const_mul s (Real.differentiableAt_rpow_const_of_ne (s - 1) hz')]
    rw [Real.deriv_rpow_const z (s - 1)]
  rw [hd2, hd1]
  -- `z ^ 2 * z ^ (s - 2) = z ^ s` and `z * z ^ (s - 1) = z ^ s`
  have hp1 : z ^ (2 : ℝ) * z ^ (s - 1 - 1) = z ^ s := by
    rw [← Real.rpow_add hz]; congr 1; ring
  have hp2 : z ^ (1 : ℝ) * z ^ (s - 1) = z ^ s := by
    rw [← Real.rpow_add hz]; congr 1; ring
  have hfac : α ^ 2 * z ^ 2 * (s * ((s - 1) * z ^ (s - 1 - 1)))
      + α * (5 + α) * z * (s * z ^ (s - 1))
      = α ^ 2 * s * (s - 1) * (z ^ 2 * z ^ (s - 1 - 1))
        + α * (5 + α) * s * (z * z ^ (s - 1)) := by ring
  rw [hfac]
  rw [show z ^ 2 * z ^ (s - 1 - 1) = z ^ s from by rw [← Real.rpow_natCast z 2]; exact hp1]
  rw [show z * z ^ (s - 1) = z ^ s from by
        nth_rewrite 1 [← Real.rpow_one z]; exact hp2]
  rw [show α ^ 2 * s * (s - 1) * z ^ s + α * (5 + α) * s * z ^ s
        = (α ^ 2 * s * (s - 1) + α * (5 + α) * s) * z ^ s from by ring]
  rw [show α ^ 2 * s * (s - 1) + α * (5 + α) * s = α ^ 2 * s ^ 2 + 5 * α * s from by ring]
  rw [hs]
  ring

end Work.EllipticEst.ModalSolution.RGW
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.final_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW


end Work.EllipticEst.ModalSolution.RGW
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.lagrange_ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.EllipticEst.ModalSolution.RGW

open Work.EllipticEst.ModalSolution.RadGreenWeak (Lneg pwt wgt qW)

/-!
# The Lagrange identity (Green's formula) for the radial operator `Lneg`

`Lneg α u z = -(α²z²u''(z) + α(5+α)zu'(z))` is, on `(0,∞)`, in divergence form with respect to
the weight `wgt α z = z^q`, `q = (5-α)/α`:

`(v · Lneg ψ - Lneg v · ψ) · z^q = (pwt · (v'ψ - vψ'))'`   with  `pwt α z = α²z²z^q`.

The key algebraic fact is `α²(q + 2) = α(5 + α)`, which is exactly the choice `q = (5-α)/α`.
Integrating over `[c,d] ⊂ (0,∞)` gives the stated boundary formula.
-/

/-- The Lagrange coefficient `pwt α z = α²z²z^q` is differentiable on `(0,∞)`, with derivative
`α(5+α) z z^q`.  (This is where `q = (5-α)/α` enters: `α²(q+2) = α(5+α)`.) -/
theorem pwt_hasDerivAt (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (pwt α) (α * (5 + α) * z * wgt α z) z := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hq : HasDerivAt (fun t : ℝ => t ^ (qW α)) (qW α * z ^ (qW α - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz')
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hmul : HasDerivAt (fun t : ℝ => t ^ 2 * t ^ (qW α))
      (2 * z * z ^ qW α + z ^ 2 * (qW α * z ^ (qW α - 1))) z := hp.mul hq
  have hcm := hmul.const_mul (α ^ 2)
  have hfun : (fun y : ℝ => α ^ 2 * (y ^ 2 * y ^ (qW α))) = pwt α := by
    funext y; simp [pwt, wgt]
  rw [hfun] at hcm
  have h2'' : z * z ^ (qW α - 1) = z ^ qW α := by
    calc z * z ^ (qW α - 1) = z ^ (1:ℝ) * z ^ (qW α - 1) := by rw [Real.rpow_one]
      _ = z ^ ((1:ℝ) + (qW α - 1)) := by rw [Real.rpow_add hz]
      _ = z ^ qW α := by congr 1; ring
  have hsq : z ^ 2 * z ^ (qW α - 1) = z * z ^ qW α := by
    rw [pow_two, mul_assoc, h2'']
  have hkey : α ^ 2 * (qW α + 2) = α * (5 + α) := by
    rcases eq_or_ne α 0 with h | h
    · subst h; norm_num [qW]
    · rw [qW]; field_simp; ring
  have heq : α ^ 2 * (2 * z * z ^ qW α + z ^ 2 * (qW α * z ^ (qW α - 1)))
      = α * (5 + α) * z * wgt α z := by
    have h2 : z ^ 2 * (qW α * z ^ (qW α - 1)) = z ^ 2 * z ^ (qW α - 1) * qW α := by ring
    rw [h2, hsq, wgt]
    have h3 : α ^ 2 * (2 * z * z ^ qW α + z * z ^ qW α * qW α)
        = (α ^ 2 * (qW α + 2)) * (z * z ^ qW α) := by ring
    rw [h3, hkey]
    ring
  rwa [heq] at hcm

/-- A `C²` function on `(0,∞)` has a differentiable first derivative there, with derivative given
by `deriv (deriv u)`. -/
theorem hasDerivAt_deriv_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (deriv u) (deriv (deriv u) z) z := by
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioi 0) := hu.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((h1.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt

/-- A `C²` function on `(0,∞)` is differentiable there, with derivative `deriv u`. -/
theorem hasDerivAt_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt u (deriv u z) z :=
  ((hu.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt

/-- `Lneg α u` is continuous on `(0,∞)` as soon as `u` is `C²` there. -/
theorem Lneg_continuousOn (α : ℝ) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0)) :
    ContinuousOn (fun z => Lneg α u z) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioi 0) := hu.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hddu : ContinuousOn (deriv (deriv u)) (Set.Ioi 0) :=
    h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdu : ContinuousOn (deriv u) (Set.Ioi 0) :=
    hu.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  unfold Lneg
  fun_prop

/-- Pointwise form of the Lagrange identity: on `(0,∞)` the function `pwt · (v'ψ - vψ')` is an
antiderivative of `(v · Lneg ψ - Lneg v · ψ) · wgt`. -/
theorem hasDerivAt_lagrange (α : ℝ) {v ψ : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
        ((v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z) z := by
  intro z hz
  have hP : HasDerivAt (fun y => deriv v y * ψ y - v y * deriv ψ y)
      (deriv (deriv v) z * ψ z - v z * deriv (deriv ψ) z) z := by
    have h1 : HasDerivAt (fun y => deriv v y * ψ y)
        (deriv (deriv v) z * ψ z + deriv v z * deriv ψ z) z :=
      (hasDerivAt_deriv_of_contDiffOn hv hz).mul (hasDerivAt_of_contDiffOn hψ hz)
    have h2 : HasDerivAt (fun y => v y * deriv ψ y)
        (deriv v z * deriv ψ z + v z * deriv (deriv ψ) z) z :=
      (hasDerivAt_of_contDiffOn hv hz).mul (hasDerivAt_deriv_of_contDiffOn hψ hz)
    exact (h1.sub h2).congr_deriv (by ring)
  have hm : HasDerivAt (fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
      (α * (5 + α) * z * wgt α z * (deriv v z * ψ z - v z * deriv ψ z)
        + pwt α z * (deriv (deriv v) z * ψ z - v z * deriv (deriv ψ) z)) z :=
    (pwt_hasDerivAt α hz).mul hP
  refine hm.congr_deriv ?_
  simp only [Lneg, pwt, wgt]
  ring


end Work.EllipticEst.ModalSolution.RGW
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.srcM_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the lower source kernel `srcM` near `0`

For `0 < α ≤ 1` the kernel `srcM α m c t = c t · t^{(2m+5)/α - 1}` of the lower
(the harmless) end of the radial Green's function is integrable on `(0, b]`, whenever
`c²` is integrable on `(0, ∞)` and `c` is a.e. strongly measurable there.

Indeed the exponent `p = (2m+5)/α - 1` satisfies `p ≥ 4 > 0` (because `α ≤ 1`), so
`t ↦ t^p` is bounded by `b^p` on `(0,b]`; and the `L²` hypothesis on `c` gives the
pointwise `L¹` bound `‖c t‖ ≤ (c t ^ 2 + 1)/2`, the constant `1` being integrable on
the finite measure space `(0,b]`.
-/

set_option linter.unusedVariables false

namespace Work.EllipticEst.ModalSolution.RGW

theorem srcM_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c)
      (Set.Ioc 0 b) := by
  -- unfold `srcM` and abbreviate its exponent
  change MeasureTheory.Integrable (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
    (MeasureTheory.volume.restrict (Set.Ioc 0 b))
  set p : ℝ := (2 * (m : ℝ) + 5) / α - 1 with hp
  have hsubset : Set.Ioc (0 : ℝ) b ⊆ Set.Ioi (0 : ℝ) := fun t ht => ht.1
  -- the exponent is at least `4`
  have h5 : (5 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hone : (1 : ℝ) ≤ 1 / α := by
    have h := one_div_le_one_div_of_le hα hα1
    simpa using h
  have hdiv : (5 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    have h2 : (5 : ℝ) ≤ 5 / α := by
      have h := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 5)
      simpa only [div_eq_mul_inv, mul_one, one_mul] using h
    have h1 : (5 : ℝ) / α ≤ (2 * (m : ℝ) + 5) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h5 (inv_nonneg.mpr hα.le)
    linarith
  have hp4 : (4 : ℝ) ≤ p := by
    rw [hp]
    linarith
  have hp0 : (0 : ℝ) ≤ p := by linarith
  -- the dominating function and its integrability
  have hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioc 0 b) :=
    hc.mono_set hsubset
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 b) :=
    MeasureTheory.integrableOn_const
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2 + 1) (Set.Ioc 0 b) :=
    hc2.add h1
  have hdom : MeasureTheory.Integrable
      (fun t : ℝ => b ^ p / 2 * (c t ^ 2 + 1)) (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    MeasureTheory.Integrable.const_mul hsum (b ^ p / 2)
  -- a.e. strong measurability of `srcM α m c`
  have hcm' : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    hcm.mono_measure (MeasureTheory.Measure.restrict_mono hsubset le_rfl)
  have hpfun : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ p)
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    (Real.continuous_rpow_const hp0).aestronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * t ^ p)
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    MeasureTheory.AEStronglyMeasurable.mul hcm' hpfun
  -- the pointwise bound on `(0, b]`
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc 0 b)),
      ‖c t * t ^ p‖ ≤ b ^ p / 2 * (c t ^ 2 + 1) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have htp : t ^ p ≤ b ^ p := Real.rpow_le_rpow ht0.le ht.2 hp0
    have htp0 : (0 : ℝ) ≤ t ^ p := Real.rpow_nonneg ht0.le p
    have hcb : ‖c t‖ ≤ (c t ^ 2 + 1) / 2 := by
      have hsq : ‖c t‖ ^ 2 = c t ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      have hq : (0 : ℝ) ≤ (‖c t‖ - 1) ^ 2 := sq_nonneg _
      nlinarith [hsq, hq]
    have hcb0 : (0 : ℝ) ≤ (c t ^ 2 + 1) / 2 := by positivity
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htp0]
    calc ‖c t‖ * t ^ p ≤ ((c t ^ 2 + 1) / 2) * t ^ p :=
          mul_le_mul_of_nonneg_right hcb htp0
      _ ≤ ((c t ^ 2 + 1) / 2) * b ^ p := mul_le_mul_of_nonneg_left htp hcb0
      _ = b ^ p / 2 * (c t ^ 2 + 1) := by ring
  exact MeasureTheory.Integrable.mono' hdom hmeas hbound

end Work.EllipticEst.ModalSolution.RGW
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.srcP_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

open MeasureTheory Set

/-- For `a > 0` the function `t ↦ t ^ e` is continuous on `(a, ∞)`. -/
private lemma continuousOn_rpow_Ioi (e a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ e) (Set.Ioi a) :=
  fun t ht =>
    (Real.continuousAt_rpow_const t e (Or.inl (ne_of_gt (lt_trans ha ht)))).continuousWithinAt

/-- For `a > 0` the function `t ↦ t ^ e` is almost everywhere strongly measurable for the
restricted measure. -/
private lemma aestronglyMeasurable_rpow_Ioi (e a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (fun t : ℝ => t ^ e) (volume.restrict (Set.Ioi a)) :=
  ContinuousOn.aestronglyMeasurable (continuousOn_rpow_Ioi e a ha) measurableSet_Ioi

/-- For `a > 0` and any real exponent `e`, the restriction of `t ↦ t ^ e` to `(a, ∞)` is in
`L²` iff `2e < -1`; here we only need one direction, via the explicit integrability of
`t ↦ t ^ (2e)` on `(a, ∞)` and the identity `(t^e)^2 = t^(2e)` valid for `t > 0`. -/
private lemma memLp_two_rpow_Ioi (e a : ℝ) (ha : 0 < a) (h : 2 * e < -1) :
    MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi a)) := by
  refine (memLp_two_iff_integrable_sq (aestronglyMeasurable_rpow_Ioi e a ha)).mpr ?_
  have hbase : IntegrableOn (fun t : ℝ => t ^ (2 * e)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt h ha
  have hg2 : IntegrableOn (fun t : ℝ => (t ^ e) ^ 2) (Set.Ioi a) :=
    hbase.congr_fun (fun t ht => by
      show t ^ (2 * e) = (t ^ e) ^ 2
      have htpos : 0 < t := lt_trans ha ht
      rw [show (2 : ℝ) * e = e * 2 by ring]
      rw [Real.rpow_mul (x := t) htpos.le e 2, Real.rpow_two]) measurableSet_Ioi
  exact hg2

theorem srcP_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c)
      (Set.Ioi a) := by
  set e : ℝ := -(2 * (m : ℝ) / α) - 1 with he
  have h2e : 2 * e < -1 := by
    rw [he]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hx : (0 : ℝ) ≤ 2 * (m : ℝ) / α := div_nonneg (by linarith) hα.le
    nlinarith [hx]
  have hsub : Set.Ioi a ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi ha.le
  have hae : AEStronglyMeasurable c (volume.restrict (Set.Ioi a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hc2 : Integrable (fun t : ℝ => c t ^ 2) (volume.restrict (Set.Ioi a)) :=
    hc.mono_set hsub
  have hcL2 : MemLp c 2 (volume.restrict (Set.Ioi a)) :=
    (memLp_two_iff_integrable_sq hae).mpr hc2
  have hgL2 : MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi a)) :=
    memLp_two_rpow_Ioi e a ha h2e
  have hprod : Integrable (fun t : ℝ => c t * t ^ e) (volume.restrict (Set.Ioi a)) :=
    hcL2.integrable_mul hgL2
  rw [he] at hprod
  show Integrable (Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c)
    (volume.restrict (Set.Ioi a))
  exact hprod

end Work.EllipticEst.ModalSolution.RGW
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

open MeasureTheory Set intervalIntegral

/-- **One-dimensional Sobolev `L∞`–`L²` bound on a closed interval.**  For a function `v` of
class `C¹` on `[c,d]` (`c < d`) and any `θ ∈ [c,d]`,
`|v θ| ≤ ‖v‖_{L²(c,d)}/√(d-c) + √(d-c)·‖v'‖_{L²(c,d)}`.

The proof picks a point `y₀` where `|v|` is minimal on `[c,d]` (so `|v y₀|` is at most the mean of
`|v|`, hence controlled by `∫ v²`), writes `v θ - v y₀ = ∫_{y₀}^{θ} deriv v` (FTC), and bounds the
latter by Cauchy–Schwarz against `∫ (deriv v)²` over the whole interval.

Derivatives are handled through `derivWithin v (Icc c d)`, which is continuous on `[c,d]`, and which
agrees with `deriv v` on the interior. -/
theorem abs_le_of_l2_Icc (v : ℝ → ℝ) {c d : ℝ} (hcd : c < d) {θ : ℝ} (hθ : θ ∈ Set.Icc c d)
    (hv : ContDiffOn ℝ 1 v (Set.Icc c d)) :
    |v θ| ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
  have hle : c ≤ d := hcd.le
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hLnonneg : 0 ≤ d - c := hLpos.le
  have hcont : ContinuousOn v (Set.Icc c d) := hv.continuousOn
  -- the continuous representative of the derivative
  set g : ℝ → ℝ := derivWithin v (Set.Icc c d) with hgdef
  have hgcont : ContinuousOn g (Set.Icc c d) := by
    rw [hgdef]
    exact hv.continuousOn_derivWithin (uniqueDiffOn_Icc hcd) le_rfl
  haveI hfinIcc : IsFiniteMeasure (volume.restrict (Set.Icc c d)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- `g` agrees with `deriv v` a.e.
  have hbad : volume {x : ℝ | x ∈ Set.Icc c d ∧ g x ≠ deriv v x} = 0 := by
    have hsub : {x : ℝ | x ∈ Set.Icc c d ∧ g x ≠ deriv v x} ⊆ ({c, d} : Set ℝ) := by
      intro x hx
      by_contra hxc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxc
      have hx1 : c < x := lt_of_le_of_ne hx.1.1 (Ne.symm hxc.1)
      have hx2 : x < d := lt_of_le_of_ne hx.1.2 hxc.2
      refine hx.2 ?_
      rw [hgdef]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hx1 hx2)
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton c) (measure_singleton d)
  have hae_restrict : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc c d →
      g =ᵐ[volume.restrict s] deriv v := by
    intro s hs hsub
    change ∀ᵐ x ∂volume.restrict s, g x = deriv v x
    rw [MeasureTheory.ae_restrict_iff' hs, MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬(x ∈ s → g x = deriv v x)} = {x : ℝ | x ∈ s ∧ g x ≠ deriv v x} := by
      ext x
      simp only [not_imp]
    rw [hset]
    exact measure_mono_null
      (fun x hx => (⟨hsub hx.1, hx.2⟩ : x ∈ {y : ℝ | y ∈ Set.Icc c d ∧ g y ≠ deriv v y})) hbad
  -- boundedness/MemLp of `g` and `deriv v` on `[c,d]`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgcont
  have hgM : MemLp g 2 (volume.restrict (Set.Icc c d)) := by
    refine MemLp.of_bound (hgcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Icc subset_rfl) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact hC x hx
  have hdvM : MemLp (deriv v) 2 (volume.restrict (Set.Icc c d)) :=
    MemLp.ae_eq (hae_restrict measurableSet_Icc subset_rfl) hgM
  have hdvInt : IntegrableOn (fun x => (deriv v x) ^ 2) (Set.Icc c d) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hdvM.aestronglyMeasurable).mp hdvM
  -- minimal point of `|v|`
  obtain ⟨y₀, hy₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨c, ⟨le_rfl, hle⟩⟩ hcont.abs
  -- interval inclusions
  have huIcc_sub : Set.uIcc y₀ θ ⊆ Set.Icc c d := by
    intro x hx
    simp only [Set.uIcc, Set.mem_Icc] at hx
    exact ⟨le_trans (le_min hy₀.1 hθ.1) hx.1, le_trans hx.2 (max_le hy₀.2 hθ.2)⟩
  have huIoc_sub : Set.uIoc y₀ θ ⊆ Set.Icc c d := by
    intro x hx
    simp only [Set.uIoc, Set.mem_Ioc] at hx
    exact ⟨le_trans (le_min hy₀.1 hθ.1) hx.1.le, le_trans hx.2 (max_le hy₀.2 hθ.2)⟩
  have huIoc_meas : MeasurableSet (Set.uIoc y₀ θ) := measurableSet_uIoc
  -- the `L²` bound on `|v|`
  have hIntV2 : IntervalIntegrable (fun x => v x ^ 2) volume c d :=
    (hcont.pow 2).intervalIntegrable_of_Icc hle
  have hpt : ∀ x ∈ Set.Icc c d, (|v y₀| ^ 2 : ℝ) ≤ v x ^ 2 := by
    intro x hx
    have h1 : |v y₀| ≤ |v x| := hmin hx
    have h2 : |v y₀| ^ 2 ≤ |v x| ^ 2 := sq_le_sq.mpr (by simpa using h1)
    rwa [sq_abs (v x)] at h2
  have hconst_eq : (∫ x in c..d, (|v y₀| ^ 2 : ℝ)) = |v y₀| ^ 2 * (d - c) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hcv : (|v y₀| ^ 2) * (d - c) ≤ ∫ x in c..d, v x ^ 2 := by
    rw [← hconst_eq]
    exact integral_mono_on hle (intervalIntegrable_const (c := |v y₀| ^ 2)) hIntV2 hpt
  have hsqrt_y0 : |v y₀| ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c) := by
    have hsq : (|v y₀| * Real.sqrt (d - c)) ^ 2 ≤ ∫ x in c..d, v x ^ 2 := by
      have hrew : (|v y₀| * Real.sqrt (d - c)) ^ 2 = |v y₀| ^ 2 * (d - c) := by
        rw [mul_pow, Real.sq_sqrt hLnonneg]
      rw [hrew]
      exact hcv
    have hle2 : |v y₀| * Real.sqrt (d - c) ≤ Real.sqrt (∫ x in c..d, v x ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    rw [le_div_iff₀ (Real.sqrt_pos_of_pos hLpos)]
    exact hle2
  -- Cauchy–Schwarz over the subinterval, against `g`
  haveI hfinU : IsFiniteMeasure (volume.restrict (Set.uIoc y₀ θ)) := by
    rw [isFiniteMeasure_restrict]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono huIoc_sub)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hMemLp_absg : MemLp (fun x => |g x|) 2 (volume.restrict (Set.uIoc y₀ θ)) := by
    refine MemLp.of_bound (hgcont.abs.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      huIoc_meas huIoc_sub) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem huIoc_meas] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hC x (huIoc_sub hx)
  have hMemLp_one : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.uIoc y₀ θ)) :=
    memLp_const 1
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := fun x => |g x|) (v := fun _ : ℝ => (1 : ℝ)) (s := Set.uIoc y₀ θ)
    hMemLp_absg hMemLp_one
  have hCS : ∫ x in Set.uIoc y₀ θ, |g x| ≤
      Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) * Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) := by
    have hL : |∫ x in Set.uIoc y₀ θ, |g x| * 1| = ∫ x in Set.uIoc y₀ θ, |g x| := by
      simp only [mul_one]
      exact abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae
        (μ := volume.restrict (Set.uIoc y₀ θ))
        (Filter.Eventually.of_forall (fun x => abs_nonneg (g x))))
    have hR1 : (∫ x in Set.uIoc y₀ θ, |g x| ^ 2) = ∫ x in Set.uIoc y₀ θ, g x ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [sq_abs]
    have hR2 : (∫ x in Set.uIoc y₀ θ, ((1 : ℝ)) ^ 2) = (volume (Set.uIoc y₀ θ)).toReal := by
      simp only [one_pow, MeasureTheory.setIntegral_one_eq_measureReal,
        MeasureTheory.Measure.real_def]
    rw [← hL, ← hR1, ← hR2]
    exact hcs
  -- comparison with the full-interval quantities
  have hsvol : (volume (Set.uIoc y₀ θ)).toReal ≤ d - c := by
    have h1 : volume (Set.uIoc y₀ θ) ≤ volume (Set.Icc c d) := measure_mono huIoc_sub
    have h2 : volume (Set.Icc c d) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono h2 h1).trans_eq ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal hLnonneg]
  have hsg : ∫ x in Set.uIoc y₀ θ, g x ^ 2 = ∫ x in Set.uIoc y₀ θ, (deriv v x) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hae_restrict huIoc_meas huIoc_sub] with x hx
    rw [hx]
  have hsB : ∫ x in Set.uIoc y₀ θ, (deriv v x) ^ 2 ≤ ∫ x in c..d, (deriv v x) ^ 2 := by
    have hmono := MeasureTheory.setIntegral_mono_set
      (s := Set.uIoc y₀ θ) (t := Set.Icc c d) (f := fun x => (deriv v x) ^ 2) hdvInt
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => huIoc_sub hx))
    rwa [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle] at hmono
  -- FTC and the derivative bound
  have hFTC : ∫ x in y₀..θ, deriv v x = v θ - v y₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hv.mono huIcc_sub)
  have hB : |v θ - v y₀| ≤
      Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
    calc |v θ - v y₀|
        = |∫ x in y₀..θ, deriv v x| := by simp only [hFTC]
      _ = |∫ x in Set.uIoc y₀ θ, deriv v x| :=
            intervalIntegral.abs_integral_eq_abs_integral_uIoc (deriv v)
      _ ≤ ∫ x in Set.uIoc y₀ θ, |deriv v x| := by
            simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm
                (μ := volume.restrict (Set.uIoc y₀ θ)) (fun x => deriv v x))
      _ = ∫ x in Set.uIoc y₀ θ, |g x| := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hae_restrict huIoc_meas huIoc_sub] with x hx
            rw [hx]
      _ ≤ Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) *
            Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) := hCS
      _ ≤ Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) * Real.sqrt (d - c) := by
            have h3 : Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) ≤
                Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
              rw [hsg]
              exact Real.sqrt_le_sqrt hsB
            have h4 : Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) ≤ Real.sqrt (d - c) :=
              Real.sqrt_le_sqrt hsvol
            exact mul_le_mul h3 h4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by ring
  -- assembly
  have hsplit : |v θ| ≤ |v y₀| + |v θ - v y₀| := by
    calc |v θ| = |v y₀ + (v θ - v y₀)| := by congr 1; ring
      _ ≤ |v y₀| + |v θ - v y₀| := abs_add_le _ _
  calc |v θ| ≤ |v y₀| + |v θ - v y₀| := hsplit
    _ ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) :=
          add_le_add hsqrt_y0 hB

end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.radGreen_tail_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.EllipticEst.ModalSolution

theorem radGreen_tail_bound (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h2p1 : 0 < 2 * p + 1 := by linarith
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz0
  -- ## the factor `u t = |c t| = √(c t ^ 2)`
  have hu_ae : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hc.1
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi z)) :=
    hu_ae.mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  -- ## the weight `v t = t ^ (-p-1)`
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioi
  have hptv : ∀ t : ℝ, 0 < t → t ^ (-2 * p - 2) = (t ^ (-p - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (-p - 1)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hptv t (lt_trans hz ht)
  have hv : MemLp (fun t => t ^ (-p - 1)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  -- ## the value of `∫_z^∞ t ^ (-2p-2)`
  have hVval : (∫ t in Set.Ioi z, t ^ (-2 * p - 2)) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -2 * p - 2) (c := z) (by linarith) hz
    have h' : -z ^ ((-2 * p - 2 : ℝ) + 1) / ((-2 * p - 2 : ℝ) + 1)
        = z ^ (-2 * p - 1) / (2 * p + 1) := by
      rw [show ((-2 * p - 2 : ℝ) + 1) = -(2 * p + 1) by ring]
      rw [neg_div_neg_eq]
      rw [show -(2 * p + 1 : ℝ) = -2 * p - 1 by ring]
    rw [h, h']
  have hIntV : (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    rw [show (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Set.Ioi z, t ^ (-2 * p - 2) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hptv t (lt_trans hz ht)).symm)]
    exact hVval
  have hIntU : (∫ t in Set.Ioi z, (Real.sqrt (c t ^ 2)) ^ 2) = ∫ t in Set.Ioi z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  -- ## Cauchy–Schwarz
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt hu hv
  have hCS' : (∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1)) ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  -- ## the tail integral itself, bounded by the `L²` pairing
  have hJ : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      ∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1) := by
    have h1 : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
        ∫ t in Set.Ioi z, ‖c t * t ^ (-p - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
          (f := fun t => c t * t ^ (-p - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1))]
  have hmain : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) :=
    le_trans hJ hCS'
  -- ## monotonicity of the `L²` mass in the domain
  have hUQ : (∫ t in Set.Ioi z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioi z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => lt_trans hz ht)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) :=
    Real.sqrt_le_sqrt hUQ
  -- ## the weight computation
  have hW : z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) =
      z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
    have hzW : 0 ≤ z ^ (-2 * p - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    have hsq : Real.sqrt (z ^ (-2 * p - 1)) = z ^ (-p - (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
      rw [show (-2 * p - 1) * (1 / 2) = -p - (1 / 2) by ring]
    rw [Real.sqrt_div hzW (2 * p + 1), hsq]
    rw [← mul_div_assoc, ← Real.rpow_add hz]
    rw [show p + (-p - (1 / 2)) = -(1 / 2 : ℝ) by ring]
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      = z ^ p * |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| := by
        rw [abs_mul, abs_of_pos hzp]
    _ ≤ z ^ p * (Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hzp)
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) := by ring
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
        rw [mul_div_assoc]

end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.FM.Core2 =====
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

/-! ## `∂_ρ L₁₂^K(f) = - L12dens K f` -/

theorem hasDerivAt_L12 {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a ρ : ℝ}
    (hint : IntegrableOn (L12dens K f) (Ioi a))
    (hcont : ContinuousAt (L12dens K f) ρ) (ha : a < ρ) :
    HasDerivAt (fun ρ => L12 K f ρ) (-(L12dens K f ρ)) ρ := by
  have hInt : IntervalIntegrable (L12dens K f) volume a ρ := by
    rw [intervalIntegrable_iff, uIoc_of_le ha.le]
    exact hint.mono_set Ioc_subset_Ioi_self
  have hmeas : StronglyMeasurableAtFilter (L12dens K f) (𝓝 ρ) volume :=
    ⟨Ioi a, Ioi_mem_nhds ha, hint.aestronglyMeasurable⟩
  have hd := intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont
  have hc : HasDerivAt (fun _ : ℝ => ∫ s in Ioi a, L12dens K f s) 0 ρ :=
    hasDerivAt_const ρ _
  have hsub := hc.sub hd
  have hev : (fun u : ℝ => L12 K f u)
      =ᶠ[𝓝 ρ] (fun u => (∫ s in Ioi a, L12dens K f s) - ∫ s in a..u, L12dens K f s) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    rw [L12]
    have h1 : IntegrableOn (L12dens K f) (Ioi u) := hint.mono_set (Ioi_subset_Ioi hu.le)
    have hgoal : (∫ s in a..u, L12dens K f s) + (∫ s in Ioi u, L12dens K f s)
        = ∫ s in Ioi a, L12dens K f s :=
      intervalIntegral.integral_interval_add_Ioi (f := L12dens K f) (a := a) (b := u) hint h1
    linarith
  have hfun : ((fun x : ℝ => ∫ s in Ioi a, L12dens K f s) - fun u => ∫ x in a..u, L12dens K f x)
      = fun u : ℝ => (∫ s in Ioi a, L12dens K f s) - ∫ s in a..u, L12dens K f s := by
    funext u; simp [Pi.sub_apply]
  rw [hev.hasDerivAt_iff, ← hfun]
  convert hsub using 1 <;> (first | ring_nf | (funext u; simp))

/-! ## The self-similar profile as a function of `t` -/








end Work.FM
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.hasDerivAt_thetaP_fst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  -- `θ = arctan (z/r)`, so `∂_r θ = (1 + (z/r)²)⁻¹ · (-z/r²) = -z/(r²+z²) = -z/ρ²`.
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun _ : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

end Work.FTS.BSIdent.Cyl.DecayAux
end
-- ===== merged: Submission.Work.FTS.ClassC.euler_weak_eq_zero_of_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiTrunc_uncurry_smooth` — the truncated mode series is `C^∞` on the open quadrant

`Work.FTS.PhiStar.Series.psiTrunc α F N` is the finite partial sum

  `psiTrunc α F N z θ = ∑_{m ≤ N} acoeff α m F z · eFam m θ`

of the mode series of the solution of `bslOp α Ψ = F` (`Series/Defs.lean`).  Its `z`-dependence
enters only through the radial coefficients `acoeff α m F` and its `θ`-dependence only through
the *fixed* angular eigenfunctions `eFam m` (`Gegenbauer/Defs.lean`); consequently the joint
smoothness of `psiTrunc α F N` on the open quadrant `Q0 = (0,∞) × (0,π/2)` is exactly the
smoothness of the finite list of radial functions `acoeff α m F` (`m ≤ N`) on `(0,∞)`, since
the angular factors are smooth everywhere.

This file records the two ingredients:

* `contDiff_gC_nat` / `contDiff_eFam_nat`: the Gegenbauer polynomials `gC k` (defined by the
  three-term recurrence) and hence the eigenfunctions `eFam m = cos θ · gC (2m+1)(sin θ)` are
  smooth of *every* finite order.  (`contDiff_gC` of `Gegenbauer/gC_ode.lean` only supplies
  order `3`; the recurrence argument gives all orders at once.)
* `contDiffOn_uncurry_fst` / `contDiffOn_uncurry_snd`: the two separable one-variable factors
  `(z,θ) ↦ g z` resp. `(z,θ) ↦ χ θ` are smooth on a product of sets as soon as `g` resp. `χ`
  is smooth on the corresponding factor (composition with `Prod.fst` / `Prod.snd`).

The target `psiTrunc_uncurry_smooth` is then the closure of `ContDiffOn` under the finite sum
`Finset.range (N+1)` of such separable products (`ContDiffOn.sum`, `ContDiffOn.mul`).
-/

namespace Work.FTS.ClassC

/-- The Gegenbauer polynomials `gC k` of `Gegenbauer/Defs.lean` are smooth of every finite
order: the three-term recurrence `(n+2)C_{n+2} = (2n+5)x·C_{n+1} - (n+3)C_n` is built from
products and linear combinations, which preserve `ContDiff ℝ n` at each fixed order `n`. -/
lemma contDiff_gC_nat : ∀ k n : ℕ, ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more k ih1 ih2 =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) = (fun x =>
        (2 * ((k : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) x
          - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k x)
            / ((k : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul (ih2 n)).sub
      (contDiff_const.mul (ih1 n))).div_const _

/-- The Dirichlet eigenfunctions `eFam m θ = cos θ · gC (2m+1)(sin θ)` are smooth of every
finite order. -/
lemma contDiff_eFam_nat (m n : ℕ) : ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        from rfl]
  exact Real.contDiff_cos.mul ((contDiff_gC_nat (2 * m + 1) n).comp Real.contDiff_sin)

/-- The radial factor `(z,θ) ↦ g z` of a separable function is smooth of order `n` on a product
set as soon as `g` is smooth of order `n` on the first factor. -/
lemma contDiffOn_uncurry_fst {g : ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) (s ×ˢ t) := by
  exact hg.comp (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (n : WithTop ℕ∞))
    (s := s ×ˢ t)) (fun p hp => hp.1)

/-- The angular factor `(z,θ) ↦ χ θ` of a separable function is smooth of order `n` on a product
set as soon as `χ` is smooth of order `n` everywhere. -/
lemma contDiffOn_uncurry_snd {χ : ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hχ : ContDiff ℝ n χ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => χ p.2) (s ×ˢ t) := by
  exact (hχ.contDiffOn (s := Set.univ)).comp
    (contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (n : WithTop ℕ∞)) (s := s ×ˢ t))
    (fun p hp => Set.mem_univ _)


end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.rgA_growth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "rgQ" => Work.FTS.EllExist.rgQ
local notation "rgF1" => Work.FTS.EllExist.rgF1

/-- **Interval-integral comparison with a pointwise majorant.**  If `|f| ≤ g` on `Ioc a b` and
`g` is interval integrable there, then `|∫_a^b f| ≤ ∫_a^b g`. -/
private theorem abs_intervalIntegral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioc a b, |f t| ≤ g t) (hg : IntervalIntegrable g volume a b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  have h' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t :=
    Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := intervalIntegral.norm_integral_le_of_norm_le hab h' hg
  simpa [Real.norm_eq_abs] using h2

theorem rgA_growth {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.EllExist.rgA α m c z| ≤ CA * z ^ (Work.FTS.EllExist.rgQ α m - 1) := by
  obtain ⟨K, hKpos, hKdec⟩ := hdec
  -- the exponent `q - 1` is positive
  have hq1 : 1 < rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, lt_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hqm : 0 < rgQ α m - 1 := by linarith
  have hKq : 0 ≤ K / (rgQ α m - 1) := le_of_lt (div_pos hKpos hqm)
  have h0' : MeasureTheory.IntegrableOn (rgF1 α m c) (Set.Ioo 0 1) := h0
  have hcontF : ContinuousOn (rgF1 α m c) (Set.Ioi 0) :=
    hcont.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- the pointwise bound on `[1,∞)` coming from `|c t| ≤ K/t`
  have hpt : ∀ t : ℝ, 1 ≤ t → |rgF1 α m c t| ≤ K * t ^ (rgQ α m - 2) := by
    intro t ht1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hp1 : 0 < t ^ (rgQ α m - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Work.FTS.EllExist.rgF1, abs_mul, abs_of_pos hp1]
    calc |c t| * t ^ (rgQ α m - 1) ≤ (K / t) * t ^ (rgQ α m - 1) :=
          mul_le_mul_of_nonneg_right (hKdec t ht1) (le_of_lt hp1)
      _ = K * t ^ (rgQ α m - 2) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one t, mul_assoc,
            ← Real.rpow_add ht0, show (-1 : ℝ) + (rgQ α m - 1) = rgQ α m - 2 from by ring]
  refine ⟨|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1,
      add_nonneg (add_nonneg (abs_nonneg _) hKq) zero_le_one, ?_⟩
  intro z hz1
  have hzp : 1 ≤ z ^ (rgQ α m - 1) := Real.one_le_rpow hz1 (le_of_lt hqm)
  -- interval integrability of the two pieces of the split
  have hII01 : IntervalIntegrable (rgF1 α m c) volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h0'.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
  have hII1z : IntervalIntegrable (rgF1 α m c) volume (1:ℝ) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz1]
    refine Integrable.mono' (g := fun t => K * t ^ (rgQ α m - 2)) ?_ ?_ ?_
    · exact ((intervalIntegral.intervalIntegrable_rpow' (r := rgQ α m - 2)
        (by linarith : (-1:ℝ) < rgQ α m - 2)).const_mul K).1
    · exact (hcontF.mono
        (fun t ht => lt_of_lt_of_le zero_lt_one (le_of_lt ht.1))).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpt t (le_of_lt ht.1)
  -- the tail piece `∫_1^z`
  have htail : |∫ t in (1:ℝ)..z, rgF1 α m c t| ≤ K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by
    have hgII : IntervalIntegrable (fun t => K * t ^ (rgQ α m - 2)) volume (1:ℝ) z :=
      (intervalIntegral.intervalIntegrable_rpow' (r := rgQ α m - 2)
        (by linarith : (-1:ℝ) < rgQ α m - 2)).const_mul K
    have hb := abs_intervalIntegral_le hz1 (f := rgF1 α m c)
      (g := fun t => K * t ^ (rgQ α m - 2)) (fun t ht => hpt t (le_of_lt ht.1)) hgII
    have hval : ∫ t in (1:ℝ)..z, K * t ^ (rgQ α m - 2)
        = K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1) := by
      rw [intervalIntegral.integral_const_mul]
      have h := integral_rpow (a := (1:ℝ)) (b := z) (r := rgQ α m - 2)
        (Or.inl (by linarith : (-1:ℝ) < rgQ α m - 2))
      rw [show rgQ α m - 2 + 1 = rgQ α m - 1 from by ring, Real.one_rpow] at h
      rw [h]
      ring
    calc |∫ t in (1:ℝ)..z, rgF1 α m c t| ≤ ∫ t in (1:ℝ)..z, K * t ^ (rgQ α m - 2) := hb
      _ = K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1) := hval
      _ ≤ K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by
          have h2 : (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)
              ≤ z ^ (rgQ α m - 1) / (rgQ α m - 1) :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hqm)
          calc K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)
              = K * ((z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)) := by ring
            _ ≤ K * (z ^ (rgQ α m - 1) / (rgQ α m - 1)) :=
                mul_le_mul_of_nonneg_left h2 (le_of_lt hKpos)
            _ = K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by ring
  have hsplit : (∫ t in (0:ℝ)..1, rgF1 α m c t) + (∫ t in (1:ℝ)..z, rgF1 α m c t)
      = ∫ t in (0:ℝ)..z, rgF1 α m c t :=
    intervalIntegral.integral_add_adjacent_intervals hII01 hII1z
  have hfin : |∫ t in (0:ℝ)..z, rgF1 α m c t|
      ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := by
    have h1 : |(∫ t in (0:ℝ)..1, rgF1 α m c t) + ∫ t in (1:ℝ)..z, rgF1 α m c t|
        ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t| :=
      abs_add_le _ _
    have h2 : |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t|
        ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1) :=
      add_le_add le_rfl htail
    have h3 : |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1)
        ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := by
      have hAz : |∫ t in (0:ℝ)..1, rgF1 α m c t|
          ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| * z ^ (rgQ α m - 1) :=
        le_mul_of_one_le_right (abs_nonneg _) hzp
      have hKz : K / (rgQ α m - 1) ≤ K / (rgQ α m - 1) * z ^ (rgQ α m - 1) :=
        le_mul_of_one_le_right hKq hzp
      have hEq : K * z ^ (rgQ α m - 1) / (rgQ α m - 1)
          = (K / (rgQ α m - 1)) * z ^ (rgQ α m - 1) := by ring
      rw [hEq]
      nlinarith [hAz, hKz]
    calc |∫ t in (0:ℝ)..z, rgF1 α m c t|
        = |(∫ t in (0:ℝ)..1, rgF1 α m c t) + ∫ t in (1:ℝ)..z, rgF1 α m c t| := by
          rw [← hsplit]
      _ ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t| := h1
      _ ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := h2
      _ ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := h3
  rw [Work.FTS.EllExist.rgA]
  exact hfin

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.rgB_far_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC

/-- **The tail primitive decays like `z^{-p-1}`.**

`rgB α m c z = ∫_t∈(z,∞) c t · t^{-p-1}` with `p = rgP α m = 2m/α`, and the decay hypothesis
`|c t| ≤ K/t` for `t ≥ 1` makes the tail integrand dominated by `K · t^{-p-2}`, whose integral
over `(z,∞)` is exactly `K · z^{-p-1}/(p+1)` (the exponent `-p-2 < -1` because `p ≥ 0`).

No measurability of `c` is needed: if `rgF2` is not a.e. strongly measurable Mathlib's junk
integral vanishes and the bound is trivial, while in the measurable case the majorant
`K · t^{-p-2}` is integrable on `(z,∞)` for `z > 0` by `integrableOn_Ioi_rpow_of_lt`. -/
private lemma rgB_abs_le {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t) {z : ℝ} (hz : 1 ≤ z) :
    |Work.FTS.EllExist.rgB α m c z|
      ≤ K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  have hlt : -(Work.FTS.EllExist.rgP α m) - 2 < (-1 : ℝ) := by linarith
  -- triangle inequality for the Bochner integral
  have hstep1 : |Work.FTS.EllExist.rgB α m c z|
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
      (Work.FTS.EllExist.rgF2 α m c)
    rw [Work.FTS.EllExist.rgB]
    simpa only [Real.norm_eq_abs] using h
  -- the pointwise domination of the tail integrand by the majorant
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioi z)), ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    have ht1 : 1 ≤ t := le_trans hz (le_of_lt ht)
    have hc : |c t| ≤ K / t := hK t ht1
    have hpow : 0 < t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Work.FTS.EllExist.rgF2, Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
    calc |c t| * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
        ≤ (K / t) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hpow)
      _ = K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one t,
            show K * t ^ (-1 : ℝ) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
              = K * (t ^ (-1 : ℝ) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) from by ring,
            ← Real.rpow_add ht0,
            show (-1 : ℝ) + (-(Work.FTS.EllExist.rgP α m) - 1)
              = -(Work.FTS.EllExist.rgP α m) - 2 from by ring]
  -- the majorant is integrable on `(z,∞)`
  have hint : Integrable (fun t => K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2))
      (volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt hlt hz0).const_mul K
  have hstep2 : ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hint hpoint
  -- the value of the majorant integral
  have hval : ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2)
      = K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hz0,
      show -(Work.FTS.EllExist.rgP α m) - 2 + 1 = -(Work.FTS.EllExist.rgP α m) - 1 from by ring,
      show -(Work.FTS.EllExist.rgP α m) - 1 = -(Work.FTS.EllExist.rgP α m + 1) from by ring,
      neg_div_neg_eq]
    ring
  calc |Work.FTS.EllExist.rgB α m c z|
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ := hstep1
    _ ≤ ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := hstep2
    _ = K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := hval

theorem rgB_far_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ z : ℝ, 1 ≤ z →
      z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z| ≤ C2 / z := by
  obtain ⟨K, hKpos, hK⟩ := hdec
  have hp1 : 0 < Work.FTS.EllExist.rgP α m + 1 := by
    have := Work.FTS.EllExist.rgP_nonneg hα m
    linarith
  refine ⟨K / (Work.FTS.EllExist.rgP α m + 1),
    div_nonneg (le_of_lt hKpos) (le_of_lt hp1), fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hzp : 0 < z ^ (Work.FTS.EllExist.rgP α m) := Real.rpow_pos_of_pos hz0 _
  have hmul : z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z|
      ≤ z ^ (Work.FTS.EllExist.rgP α m)
        * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
            / (Work.FTS.EllExist.rgP α m + 1)) :=
    mul_le_mul_of_nonneg_left (rgB_abs_le hα m hK hz) (le_of_lt hzp)
  calc z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z|
      ≤ z ^ (Work.FTS.EllExist.rgP α m)
        * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
            / (Work.FTS.EllExist.rgP α m + 1)) := hmul
    _ = K / (Work.FTS.EllExist.rgP α m + 1) / z := by
        rw [show z ^ (Work.FTS.EllExist.rgP α m)
              * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
                  / (Work.FTS.EllExist.rgP α m + 1))
            = K * (z ^ (Work.FTS.EllExist.rgP α m)
                * z ^ (-(Work.FTS.EllExist.rgP α m) - 1))
              / (Work.FTS.EllExist.rgP α m + 1) from by ring,
          ← Real.rpow_add hz0,
          show Work.FTS.EllExist.rgP α m + (-(Work.FTS.EllExist.rgP α m) - 1) = -1 from by ring,
          Real.rpow_neg_one]
        ring

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.rgG1_near_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.ClassC

/-- Near `0` the decaying branch `g₁ = z^{-q} ∫_0^z c t^{q-1} dt` (with `q = rgQ α m > 0`) is
dominated by `Kc z^{pc}/(pc+q)` whenever `|c t| ≤ Kc t^{pc}` for `0 < t ≤ 1`: the exponent
`pc + q - 1 > -1` makes the primitive integrate to exactly `z^{pc+q}/(pc+q)`.

No measurability of `c` is needed: if `t ↦ c t · t^{q-1}` is not a.e. strongly measurable then
Mathlib's (junk) integral vanishes and the bound is trivial, while in the measurable case the
`norm_integral_le_of_norm_le` majorant `Kc t^{pc+q-1}` is integrable. -/
theorem rgG1_near_bound {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {pc Kc : ℝ}
    (hKc : 0 < Kc) (hpc : 0 < pc)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ Kc * t ^ pc) :
    ∀ z : ℝ, 0 < z → z ≤ 1 →
      |Work.FTS.EllExist.rgG1 α m c z|
        ≤ Kc * z ^ pc / (pc + Work.FTS.EllExist.rgQ α m) := by
  intro z hz hz1
  have hqpos : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hA : |Work.FTS.EllExist.rgA α m c z|
      ≤ Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m) := by
    have hbound : ‖∫ t in (0:ℝ)..z, Work.FTS.EllExist.rgF1 α m c t‖
        ≤ ∫ t in (0:ℝ)..z, Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hz.le ?_ ?_
      · refine Filter.Eventually.of_forall (fun t ht => ?_)
        obtain ⟨ht0, htz⟩ := ht
        have ht1 : t ≤ 1 := le_trans htz hz1
        have hq1 : (0:ℝ) < t ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_pos_of_pos ht0 _
        simp only [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul, abs_of_pos hq1]
        calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
            ≤ Kc * t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1) :=
              mul_le_mul_of_nonneg_right (hvy t ht0 ht1) (le_of_lt hq1)
          _ = Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1) := by
              rw [show Kc * t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1)
                    = Kc * (t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1)) from by ring,
                ← Real.rpow_add ht0,
                show pc + (Work.FTS.EllExist.rgQ α m - 1)
                    = pc + Work.FTS.EllExist.rgQ α m - 1 from by ring]
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul Kc
    have hval : ∫ t in (0:ℝ)..z, Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1)
        = Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : (-1:ℝ) < pc + Work.FTS.EllExist.rgQ α m - 1))]
      rw [Real.zero_rpow (by linarith : pc + Work.FTS.EllExist.rgQ α m - 1 + 1 ≠ 0),
        show pc + Work.FTS.EllExist.rgQ α m - 1 + 1 = pc + Work.FTS.EllExist.rgQ α m from by ring]
      ring
    rw [Work.FTS.EllExist.rgA, ← hval]
    simpa only [Real.norm_eq_abs] using hbound
  rw [Work.FTS.EllExist.rgG1, abs_mul]
  have hpos : 0 < z ^ (-(Work.FTS.EllExist.rgQ α m)) := Real.rpow_pos_of_pos hz _
  rw [abs_of_pos hpos]
  calc z ^ (-(Work.FTS.EllExist.rgQ α m)) * |Work.FTS.EllExist.rgA α m c z|
      ≤ z ^ (-(Work.FTS.EllExist.rgQ α m))
          * (Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m)) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt hpos)
    _ = Kc * z ^ pc / (pc + Work.FTS.EllExist.rgQ α m) := by
        rw [show z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m))
            = Kc * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (pc + Work.FTS.EllExist.rgQ α m))
              / (pc + Work.FTS.EllExist.rgQ α m) from by ring]
        rw [← Real.rpow_add hz,
          show (-(Work.FTS.EllExist.rgQ α m)) + (pc + Work.FTS.EllExist.rgQ α m) = pc from by ring]

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.rgG2_near_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

theorem rgG2_near_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (h2 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      |Work.FTS.EllExist.rgG2 α m c z|
        ≤ (∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖)
          * z ^ (Work.FTS.EllExist.rgP α m) := by
  intro z hz
  -- `z ^ p > 0`
  have hzp : 0 < z ^ (Work.FTS.EllExist.rgP α m) := Real.rpow_pos_of_pos hz _
  -- `(z,∞) ⊆ (0,∞)` as an a.e. inclusion, since `z > 0`
  have hle : Set.Ioi z ≤ᵐ[volume] Set.Ioi 0 :=
    ae_of_all _ (fun x hx => lt_trans hz hx)
  -- the triangle inequality for the Bochner integral
  have hint1 : ‖∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
    norm_integral_le_integral_norm _
  -- monotonicity of the set integral: enlarging `(z,∞)` to `(0,∞)`
  have hint2 : ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
    setIntegral_mono_set h2.norm (ae_of_all _ (fun t => norm_nonneg _)) hle
  calc |Work.FTS.EllExist.rgG2 α m c z|
      = z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z| := by
        rw [Work.FTS.EllExist.rgG2, abs_mul, abs_of_pos hzp]
    _ = z ^ (Work.FTS.EllExist.rgP α m)
          * ‖∫ t in Set.Ioi z, Work.FTS.EllExist.rgF2 α m c t‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ z ^ (Work.FTS.EllExist.rgP α m)
          * ∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖ :=
        mul_le_mul_of_nonneg_left (le_trans hint1 hint2) (le_of_lt hzp)
    _ = (∫ t in Set.Ioi 0, ‖Work.FTS.EllExist.rgF2 α m c t‖)
          * z ^ (Work.FTS.EllExist.rgP α m) := by ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.RgL2Pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/RgL2Pointwise` — the pointwise bound for `radGreen` in terms of the
weighted `L²`-norm of the source

The existing mode-uniform bound `Work.FTS.ClassCHon.radGreen_size_bound`,
`m² |radGreen α m c z| ≤ A · sup_t |c t|`, consumes a *pointwise* bound on the source `c`.
That is exactly what is unavailable for a source given only by an `ℋ^k`-membership hypothesis
(`HkMem` controls `c` only through *integrated* weighted `L²` quantities, and its mode
coefficients `cmode m F` are not bounded uniformly in the radial variable).

This file proves the companion bound in which the role of `sup_t |c t|` is played by the
weighted `L²`-norm `‖c‖_{w²} = (∫_{t>0} c t² · w t²)^{1/2}`:

  `|z^{-q} ∫_0^z c t^{q-1}| ≤ ‖c‖_{w²} / √(2 q − 1)`   (`q = (2m+5)/α`),
  `|z^{p} ∫_z^∞ c t^{-p-1}| ≤ ‖c‖_{w²} / √(2 p − 3)`    (`p = 2m/α`),

hence `|radGreen α m c z| ≤ (1/(α(4m+5)))·(1/√(2q-1) + 1/√(2p-3))·‖c‖_{w²}`, and since
`q ≥ 8m`, `p ≥ 8m` on the standing range `α ≤ 1/4`, `m ≥ 1`, also

  `|radGreen α m c z| ≤ ‖c‖_{w²} / (4 α m^{3/2})`.

The proof is Cauchy–Schwarz against the weight `w`: the two kernels are split as
`c t · t^{q-1} = (c t · w t) · (t^{q-1} / w t)` (resp. `c t · t^{-p-1}`), so the two `L²`-factors
are the source norm and the explicit weight integrals
`∫_{(0,z)} t^{2q-2}/w² = ∫_{(0,z)} t^{2q+2}/(1+t)⁴` and `∫_{(z,∞)} t^{-2p-2}/w²`, which are
pinned by `1/w(t)² = t⁴/(1+t)⁴ ≤ t⁴` resp. `≤ 1`:

  `∫_{(0,z)} t^{2q-2}/w² ≤ z^{2q}/(2q-1)`,   `∫_{(z,∞)} t^{-2p-2}/w² ≤ z^{-2p}/(2p-3)`.

Nothing here uses regularity, support or sign hypotheses on `c`: only the weighted
`L²`-integrability `∫_{t>0} c²w² < ∞` (which `HkMem` supplies through its slicewise conjunct)
and the a.e. strong measurability of `c·w` on `(0,∞)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon

local notation "w" => Work.Spaces.w

/-- The weight `w` is positive at `t > 0`. -/
theorem w_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < w t := by
  rw [Work.Spaces.w]
  positivity

/-- `1 / w(t)² = t⁴/(1+t)⁴`. -/
theorem one_div_w_sq_eq {t : ℝ} (ht : 0 < t) :
    1 / (w t) ^ 2 = t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ) := by
  have hw : (w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
    rw [Work.Spaces.w, div_pow]
    ring
  rw [hw, one_div, inv_div]
  rw [Real.rpow_ofNat, Real.rpow_ofNat]

/-- `t^{2Q-2}/w(t)² = t^{2Q+2}/(1+t)⁴` for `0 ≤ t`, `Q > 1`. -/
theorem near_pow_form {Q t : ℝ} (ht : 0 ≤ t) (hQ : 1 < Q) :
    t ^ (2 * Q - 2) / (w t) ^ 2 = t ^ (2 * Q + 2) / (1 + t) ^ (4 : ℝ) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    have h1 : w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [h1, Real.zero_rpow (by linarith : 2 * Q - 2 ≠ 0),
      Real.zero_rpow (by linarith : 2 * Q + 2 ≠ 0)]
    norm_num
  · have hsplit : t ^ (2 * Q - 2) * t ^ (4 : ℝ) = t ^ (2 * Q + 2) := by
      rw [← Real.rpow_add h]; ring_nf
    calc t ^ (2 * Q - 2) / (w t) ^ 2
        = t ^ (2 * Q - 2) * (1 / (w t) ^ 2) := by ring
      _ = t ^ (2 * Q - 2) * (t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ)) := by rw [one_div_w_sq_eq h]
      _ = t ^ (2 * Q + 2) / (1 + t) ^ (4 : ℝ) := by rw [← hsplit]; ring

/-- `t^{-2P-2}/w(t)² = t^{-2P+2}/(1+t)⁴` for `0 ≤ t`. -/
theorem far_pow_form {P t : ℝ} (ht : 0 ≤ t) (hP : 3 / 2 < P) :
    t ^ (-2 * P - 2) / (w t) ^ 2 = t ^ (-2 * P + 2) / (1 + t) ^ (4 : ℝ) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    have h1 : w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [h1, Real.zero_rpow (by linarith : -2 * P - 2 ≠ 0),
      Real.zero_rpow (by linarith : -2 * P + 2 ≠ 0)]
    norm_num
  · have hsplit : t ^ (-2 * P - 2) * t ^ (4 : ℝ) = t ^ (-2 * P + 2) := by
      rw [← Real.rpow_add h]; ring_nf
    calc t ^ (-2 * P - 2) / (w t) ^ 2
        = t ^ (-2 * P - 2) * (1 / (w t) ^ 2) := by ring
      _ = t ^ (-2 * P - 2) * (t ^ (4 : ℝ) / (1 + t) ^ (4 : ℝ)) := by rw [one_div_w_sq_eq h]
      _ = t ^ (-2 * P + 2) / (1 + t) ^ (4 : ℝ) := by rw [← hsplit]; ring

/-! ## The pointwise dominations -/


/-- `t^{-2P-2}/w(t)² ≤ t^{-2P+2}` for `t > 0`. -/
theorem far_div_w_sq_le_rpow {P t : ℝ} (ht : 0 < t) (hP : 3 / 2 < P) :
    t ^ (-2 * P - 2) / (w t) ^ 2 ≤ t ^ (-2 * P + 2) := by
  rw [far_pow_form ht.le hP, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  exact le_mul_of_one_le_right (Real.rpow_nonneg ht.le _) (Real.one_le_rpow (by linarith) (by norm_num))

/-- `t^{2Q-2}/w(t)² ≤ t^{2Q-2}` for `t > 0`. -/
theorem near_div_w_sq_le_self {Q t : ℝ} (ht : 0 < t) (hQ : 1 < Q) :
    t ^ (2 * Q - 2) / (w t) ^ 2 ≤ t ^ (2 * Q - 2) := by
  rw [near_pow_form ht.le hQ, div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) 4)]
  rw [show t ^ (2 * Q + 2) = t ^ (2 * Q - 2) * t ^ (4 : ℝ) by
    rw [← Real.rpow_add ht]; ring_nf]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
    (Real.rpow_nonneg ht.le _)


/-! ## The elementary rpow integrals and the two weight integrals -/

/-- The elementary rpow integral `∫_{(0,z)} t^{r} = z^{r+1}/(r+1)` for `-1 < r`. -/
theorem integral_Ioc_rpow_eq {z r : ℝ} (hz : 0 < z) (hr : -1 < r) :
    ∫ t in Set.Ioc (0 : ℝ) z, t ^ r = z ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hz.le, integral_rpow (Or.inl hr)]
  rw [Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]


end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false

/-- The angular weight `φ_m(θ) = e_m(θ)·cos θ` of the `m`-th mode. -/
def phiW (m : ℕ) (θ : ℝ) : ℝ :=
  Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-- The numerator of the mode coefficient `cmode m F z`, written as a set integral over the
closed angular interval `Iθ = [0,π/2]`. -/
def numW (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, F z θ * phiW m θ

/-- The `θ`-integral of `∂_z F · φ_m`: the numerator of `cmode m (∂_z F) z`, i.e. the function
whose value at `z` is the derivative of `numW m F` at `z`. -/
def pwF (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * phiW m θ


end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter

/-- The real-power identity `(t * d t) * t ^ (q - 1) = d t * t ^ q` for `t > 0`. -/
private lemma rgMulRpowSubOne (d : ℝ → ℝ) {q t : ℝ} (ht : 0 < t) :
    (t * d t) * t ^ (q - 1) = d t * t ^ q := by
  have h1 : t ^ q = t ^ ((1 : ℝ) + (q - 1)) := by congr 1; ring
  rw [h1, Real.rpow_add ht, Real.rpow_one]
  ring

/-- `t ↦ c t * t ^ q` has derivative `deriv c t * t ^ q + q * (c t * t ^ (q - 1))` at `t > 0`. -/
private lemma rgHasDerivAt_mul_rpow {q : ℝ} {c : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hcd : HasDerivAt c (deriv c t) t) :
    HasDerivAt (fun s : ℝ => c s * s ^ q)
      (deriv c t * t ^ q + q * (c t * t ^ (q - 1))) t := by
  have hp : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
  refine (hcd.mul hp).congr_deriv ?_
  ring

/-- **Integration by parts at the lower end, in `rgA`-form** (intended namespace
`Work.FTS.ClassCHon.Zpz`, module `Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower`).

With `q = rgQ α m = (2*m+5)/α > 0`, `rgA α m c z = ∫ t in (0)..z, c t * t ^ (q - 1)`, and `hlim`
the (requested separately) statement that `t ↦ c t * t ^ q → 0` at `0⁺`: the `t`-weighted source
`t ↦ t * deriv c t` satisfies
`rgA α m (fun t => t * deriv c t) z = c z * z ^ q - q * rgA α m c z` for every `z > 0`.

This is the integration by parts
`∫ x in (0)..z, deriv c x * x ^ q = c z * z ^ q - q * ∫ x in (0)..z, c x * x ^ (q - 1)`
(whose boundary term at `0⁺` vanishes by `hlim`), transported to `rgA` through the a.e. identity
`(t * deriv c t) * t ^ (q - 1) = deriv c t * t ^ q` on `t > 0`, via
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` applied to `F t = c t * t ^ q` with
`a = 0`, `b = z`, `fa = 0`, `fb = F z`.
Local integrability of `deriv c` (needed for the `IntervalIntegrable` hypothesis of that result on
`(0,z)`) follows from `hd0` on `(0,1)` (`|deriv c t| ≤ z0 ^ (-q) * |t * deriv c t * t ^ (q - 1)|`
for `t ≥ z0 > 0`) and from `hdinf` on `(1,z)` (`|deriv c t| ≤ z ^ p * |t * deriv c t * t ^ (-p-1)|`).
Note `hdinf` is genuinely needed (the interval of integration reaches past `1` when `z > 1`). -/
theorem radGreen_ibp_lower {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hlim : Filter.Tendsto (fun t => c t * t ^ (Work.FTS.EllExist.rgQ α m))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.rgA α m (fun t => t * deriv c t) z
        = c z * z ^ (Work.FTS.EllExist.rgQ α m)
          - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgA α m c z := by
  intro z hz
  have hqpos : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hpnn : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- `c` is continuous on `(0,∞)` because it is differentiable there
  have hcont : ContinuousOn c (Ioi 0) :=
    fun t ht => (hcd t ht).continuousAt.continuousWithinAt
  -- local integrability of the two summands of the derivative of `t ↦ c t * t ^ q`
  have hA : IntervalIntegrable
      (fun t : ℝ => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume 0 z :=
    RgIbl.intervalIntegrable_mul_deriv_rpow hqpos hpnn hd0 hdinf hz
  have hB : IntervalIntegrable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume 0 z :=
    RgIbl.intervalIntegrable_rpow_mul_contOn hcont h0 hz
  have hG : IntervalIntegrable
      (fun t : ℝ => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)))
      volume 0 z :=
    hA.add (hB.const_mul (Work.FTS.EllExist.rgQ α m))
  -- the derivative of `F t = c t * t ^ q`, in the `rgA`-compatible form
  have hder : ∀ t ∈ Ioo (0 : ℝ) z,
      HasDerivAt (fun s : ℝ => c s * s ^ (Work.FTS.EllExist.rgQ α m))
        (t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h := rgHasDerivAt_mul_rpow (q := Work.FTS.EllExist.rgQ α m) ht0 (hcd t ht0)
    refine h.congr_deriv ?_
    rw [rgMulRpowSubOne (deriv c) ht0]
  have hFz : Tendsto (fun s : ℝ => c s * s ^ (Work.FTS.EllExist.rgQ α m))
      (nhdsWithin z (Iio z)) (nhds (c z * z ^ (Work.FTS.EllExist.rgQ α m))) :=
    ((rgHasDerivAt_mul_rpow (q := Work.FTS.EllExist.rgQ α m) hz (hcd z hz)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  -- the fundamental theorem of calculus on `(0, z)`, with the boundary term at `0` killed by `hlim`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz hder hG hlim hFz
  have hsplit : ∫ t in (0 : ℝ)..z, (t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)))
      = (∫ t in (0 : ℝ)..z, t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        + Work.FTS.EllExist.rgQ α m
          * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
    rw [intervalIntegral.integral_add hA (hB.const_mul _), intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  have hFTC' : (∫ t in (0 : ℝ)..z, t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        + Work.FTS.EllExist.rgQ α m
          * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
      = c z * z ^ (Work.FTS.EllExist.rgQ α m) := by
    simpa using hFTC
  simp only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1]
  linarith [hFTC']

end Work.FTS.ClassCHon.Zpz
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_upper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

/-! The three integrability inputs for the integration by parts at the upper end are proved
separately (and in a general form, for arbitrary real exponents) in the sibling modules
`radGreen_up_loc_deriv`, `radGreen_up_loc_c` and `radGreen_up_tail`. -/

/-- Gluing: integrability on `(z,1)` and on `(1,∞)` gives integrability on `(z,∞)` when `z < 1`.
(The two pieces overlap at `t = 1`, and `(z,1) ∪ [1,∞) = (z,∞)` exactly when `z < 1`; the
singleton `{1}` is added by hand because `[1,∞) = (1,∞) ∪ {1}` whereas `hdinf` gives `(1,∞)`.) -/
private lemma upAux_union {f : ℝ → ℝ} {z : ℝ} (hz1 : z < 1)
    (h1 : IntegrableOn f (Set.Ioo z 1)) (h2 : IntegrableOn f (Set.Ioi 1)) :
    IntegrableOn f (Set.Ioi z) := by
  have hsing : IntegrableOn f ({1} : Set ℝ) :=
    integrableOn_singleton (f := f) (x := 1) (by finiteness) (by simp)
  have hIci : IntegrableOn f (Set.Ici (1 : ℝ)) := by
    have h4 : IntegrableOn f (Set.Ioi (1 : ℝ) ∪ {1}) := h2.union hsing
    rwa [show (Set.Ioi (1 : ℝ) ∪ {1} : Set ℝ) = Set.Ici 1 from by
      ext t
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff, Set.mem_Ici]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'.symm] at h4
  have h5 : IntegrableOn f (Set.Ioo z 1 ∪ Set.Ici (1 : ℝ)) := h1.union hIci
  rwa [show (Set.Ioo z 1 ∪ Set.Ici (1 : ℝ) : Set ℝ) = Set.Ioi z from by
    ext t
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      rcases lt_or_ge t 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'] at h5

/-- **Integration by parts at the upper end, in `rgB`-form** (intended namespace
`Work.FTS.ClassCHon.Zpz`, module `Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_upper`).

With `p = rgP α m = 2*m/α ≥ 0`, `rgB α m c z = ∫ t in Set.Ioi z, c t * t ^ (-p - 1)`, and `hlim`
the (requested separately) statement that `t ↦ c t * t ^ (-p) → 0` at `∞`: the `t`-weighted source
`t ↦ t * deriv c t` satisfies
`rgB α m (fun t => t * deriv c t) z = p * rgB α m c z - c z * z ^ (-p)` for every `z > 0`.

This is the integration by parts
`∫ x in Set.Ioi z, deriv c x * x ^ (-p) = - c z * z ^ (-p) + p * ∫ x in Set.Ioi z, c x * x ^ (-p-1)`
(whose boundary term at `∞` vanishes by `hlim`), transported to `rgB` through the a.e. identity
`(t * deriv c t) * t ^ (-p - 1) = deriv c t * t ^ (-p)` on `t > 0`, via
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'` applied to `F t = c t * t ^ (-p)` with
`a = z`, `m = 0` (so the integral of `F'` over `Ioi z` is `-F z`).
The hypotheses `hinf`/`hdinf` give integrability on `(1,∞)`; `hd0` gives local integrability of
`deriv c` on `(z,1)` when `z < 1` (`|deriv c t| ≤ z ^ (-q) * |t * deriv c t * t ^ (q - 1)|` for
`t ≥ z`, `q = rgQ α m`), so that the integral of `F'` over `Ioi z` is finite (that is,
`MeasureTheory.IntegrableOn F' (Set.Ioi z)`). -/
theorem radGreen_ibp_upper {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hlim : Filter.Tendsto (fun t => c t * t ^ (-(Work.FTS.EllExist.rgP α m)))
      Filter.atTop (nhds 0))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.rgB α m (fun t => t * deriv c t) z
        = Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgB α m c z
          - c z * z ^ (-(Work.FTS.EllExist.rgP α m)) := by
  intro z hz
  dsimp only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
  set p : ℝ := Work.FTS.EllExist.rgP α m with hp
  set q : ℝ := Work.FTS.EllExist.rgQ α m with hq
  have hp0 : 0 ≤ p := by rw [hp]; exact Work.FTS.EllExist.rgP_nonneg hα m
  have hq0 : 0 < q := by rw [hq]; exact Work.FTS.EllExist.rgQ_pos hα m
  -- the pointwise derivative of `F t = c t * t ^ (-p)`
  have hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c s * s ^ (-p))
        (deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s ^ (-p)) ((-p) * t ^ (-p - 1)) t :=
      Real.hasDerivAt_rpow_const (x := t) (p := -p) (Or.inl (ne_of_gt ht))
    refine ((hcd t ht).mul h1).congr_deriv ?_
    ring
  -- integrability inputs: local (`(z,1)`) and tail (`(1,∞)`)
  have hF1_loc : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioo z 1) :=
    radGreen_up_loc_deriv hp0 hq0 hz hd0
  have hF2_loc : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioo z 1) :=
    radGreen_up_loc_c hz hcd
  have hF1_tail : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioi 1) :=
    radGreen_up_tail hdinf
  have hF2_tail : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi 1) := hinf
  have hF1 : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioi z) := by
    by_cases hz1 : z < 1
    · exact upAux_union hz1 hF1_loc hF1_tail
    · exact hF1_tail.mono_set (Set.Ioi_subset_Ioi (not_lt.mp hz1))
  have hF2 : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi z) := by
    by_cases hz1 : z < 1
    · exact upAux_union hz1 hF2_loc hF2_tail
    · exact hF2_tail.mono_set (Set.Ioi_subset_Ioi (not_lt.mp hz1))
  have hpF2 : IntegrableOn (fun t => p * (c t * t ^ (-p - 1))) (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn] at hF2 ⊢
    exact hF2.const_mul p
  let F : ℝ → ℝ := fun t => c t * t ^ (-p)
  let F' : ℝ → ℝ := fun t => deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))
  have hF'deriv : ∀ t : ℝ, 0 < t → HasDerivAt F (F' t) t := hderiv
  have hF'int : IntegrableOn F' (Set.Ioi z) := hF1.sub hpF2
  have hlimF : Tendsto F Filter.atTop (nhds 0) := hlim
  -- the fundamental theorem of calculus on `(z, ∞)`
  have hftc : ∫ t in Set.Ioi z, F' t = 0 - F z :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := z) (f := F) (f' := F')
      (m := 0) (fun x hx => hF'deriv x (lt_of_lt_of_le hz hx)) hF'int hlimF
  -- splitting the integral
  have hsplit : (∫ t in Set.Ioi z, F' t)
      = (∫ t in Set.Ioi z, deriv c t * t ^ (-p))
        - p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) := by
    rw [MeasureTheory.integral_sub hF1 hpF2,
      MeasureTheory.integral_const_mul p (fun t : ℝ => c t * t ^ (-p - 1))]
  -- the a.e. identity `(t * deriv c t) * t ^ (-p - 1) = deriv c t * t ^ (-p)` on `(z, ∞)`
  have hcongr : (∫ t in Set.Ioi z, deriv c t * t ^ (-p))
      = ∫ t in Set.Ioi z, (t * deriv c t) * t ^ (-p - 1) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    have h1 : t ^ (-p) = t ^ (1 + (-p - 1)) :=
      congrArg (fun r : ℝ => t ^ r) (by ring)
    have h2 : t ^ (-p) = t * t ^ (-p - 1) := by
      rw [h1, Real.rpow_add ht0 1 (-p - 1), Real.rpow_one]
    rw [h2]
    ring
  have hmain : (∫ t in Set.Ioi z, (t * deriv c t) * t ^ (-p - 1))
      = p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) - c z * z ^ (-p) := by
    have h := hftc
    rw [hsplit, hcongr] at h
    have hFz : F z = c z * z ^ (-p) := rfl
    rw [hFz] at h
    linarith
  exact hmain

end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.ClassCHon.Zpz

/-- **Left-endpoint limit** (intended namespace `Work.FTS.ClassCHon.Zpz`, module
`Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower`).

If `c` is differentiable on `(0,∞)` and both `c t * t ^ (q - 1)` and its `t`-weighted derivative
`t * deriv c t * t ^ (q - 1)` are integrable on `(0,1)`, then `t ↦ c t * t ^ q` tends to `0` at
`0⁺`.  No hypothesis on the real exponent `q` is needed.

Route (tools available in Mathlib): `F t := c t * t ^ q` satisfies
`F' t = deriv c t * t ^ q + q * (c t * t ^ (q - 1))` on `(0,∞)`, which is `L¹` on `(0,1)` (because
`deriv c t * t ^ q = t * deriv c t * t ^ (q - 1)` for `t > 0`); so `t ↦ ∫ x in (0)..t, F' x` tends
to `0` at `0⁺` (`MeasureTheory.tendsto_setIntegral_of_antitone` applied to `s n = Set.Ioc 0 (1/(n+1))`,
whose intersection is empty, plus an `ε`-squeeze), and since
`F z - F t = ∫ x in t..z, F' x = ∫ x in (0)..z, F' x - ∫ x in (0)..t, F' x` for `0 < t < z`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` plus additivity of interval integrals), `F` has
the finite limit `C := F z - ∫ x in (0)..z, F' x` at `0⁺`.  Finally `C = 0`: if `C ≠ 0` then
`|c t * t ^ (q - 1)| = |F t| / t ≥ |C| / (2 * t)` for all small `t`, contradicting `h0` because
`∫ x in a..b, 1/x = Real.log (b / a) → ∞` as `a → 0⁺` (`integral_one_div_of_pos`). -/
theorem rpow_mul_tendsto_zero_lower {q : ℝ} {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ (q - 1)) (Set.Ioo 0 1))
    (hd0 : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (q - 1))
      (Set.Ioo 0 1)) :
    Filter.Tendsto (fun t => c t * t ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set F : ℝ → ℝ := fun t => c t * t ^ q with hFdef
  -- `t ^ q = t ^ (q - 1) * t` for `t > 0`
  have hrpow : ∀ t : ℝ, 0 < t → t ^ q = t ^ (q - 1) * t := by
    intro t ht
    have h := Real.rpow_add ht (q - 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  -- the pointwise formula for `deriv F` on `(0,1)`
  have hderiv_eq : ∀ t ∈ Set.Ioo 0 1, deriv F t
      = t * deriv c t * t ^ (q - 1) + q * (c t * t ^ (q - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h2 : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have h : HasDerivAt F (deriv c t * t ^ q + c t * (q * t ^ (q - 1))) t := by
      rw [hFdef]
      exact (hcd t ht0).mul h2
    rw [h.deriv, hrpow t ht0]
    ring
  -- `F` is differentiable on `(0,∞)` with derivative `deriv F`
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt F (deriv F t) t := by
    intro t ht
    have h2 : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.ne')
    have h : HasDerivAt F (deriv c t * t ^ q + c t * (q * t ^ (q - 1))) t := by
      rw [hFdef]
      exact (hcd t ht).mul h2
    rw [h.deriv]
    exact h
  -- `deriv F` is integrable on `(0,1)`
  have hint : MeasureTheory.IntegrableOn (deriv F) (Set.Ioo 0 1) := by
    have hg : MeasureTheory.IntegrableOn
        (fun t => t * deriv c t * t ^ (q - 1) + q * (c t * t ^ (q - 1))) (Set.Ioo 0 1) :=
      hd0.add (h0.const_mul q)
    refine hg.congr_fun ?_ measurableSet_Ioo
    intro t ht
    exact (hderiv_eq t ht).symm
  -- the primitive of `deriv F` tends to `0` at `0⁺`
  have hA : Filter.Tendsto (fun t => ∫ x in (0)..t, deriv F x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
    tendsto_intervalIntegral_zero_right hint
  -- the fundamental theorem of calculus on `[t, 1/2]`
  have hFTC : ∀ t ∈ Set.Ioo 0 (1/2 : ℝ),
      F (1/2) - F t = (∫ x in (0)..(1/2 : ℝ), deriv F x) - ∫ x in (0)..t, deriv F x := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htz : t < 1/2 := ht.2
    have hi_t : IntervalIntegrable (deriv F) volume (0:ℝ) t := by
      rw [intervalIntegrable_iff]
      refine hint.mono_set ?_
      rw [Set.uIoc_of_le ht0.le]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hi_z : IntervalIntegrable (deriv F) volume t (1/2 : ℝ) := by
      rw [intervalIntegrable_iff]
      refine hint.mono_set ?_
      rw [Set.uIoc_of_le htz.le]
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi_t hi_z
    have hftc : F (1/2) - F t = ∫ x in t..(1/2:ℝ), deriv F x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := deriv F) ?_ hi_z
      · linarith [h]
      · intro x hx
        rw [Set.uIcc_of_le htz.le] at hx
        exact hder x (by linarith [hx.1])
    linarith [hadd, hftc]
  -- the limit of `F` at `0⁺`
  set C : ℝ := F (1/2) - ∫ x in (0)..(1/2 : ℝ), deriv F x with hCdef
  have hev : (fun t => C + ∫ x in (0)..t, deriv F x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] F := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1/2 by norm_num)] with t ht
    have h := hFTC t ht
    rw [hCdef]
    linarith [h]
  have hlim : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
    have hA' : Filter.Tendsto (fun t => C + ∫ x in (0)..t, deriv F x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
      simpa using hA.const_add C
    exact Filter.Tendsto.congr' hev hA'
  -- the limit can only be `0`
  have hC0 : C = 0 :=
    tendsto_limit_eq_zero_of_rpow (F := F) (c := c) (q := q) (fun t _ => by rw [hFdef]) h0 hlim
  have hfin : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [hC0] at hlim
    exact hlim
  rw [hFdef] at hfin
  exact hfin

end Work.FTS.ClassCHon.Zpz
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_upper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter
open scoped Topology

/-- Key auxiliary step: if `F` has a limit `L` at `+∞` and `G` is integrable on `(1,∞)` with
`‖G t‖ = ‖F t‖ / t` for all sufficiently large `t`, then `L = 0`.

Indeed, if `‖L‖ ≠ 0` then `‖G t‖ ≥ ‖L‖/(2t) ≥ ‖L‖/(4R)` for `t ∈ [R, 2R]` and `R` large, so
`∫ x in Ioi R, ‖G x‖ ≥ |L| / 4` for all large `R`; but this integral tends to `0` because `G`
is integrable on `(1,∞)` (`MeasureTheory.tendsto_integral_Ioi_zero`). -/
private lemma tendsto_eq_zero_of_div_integrable {F G : ℝ → ℝ} {L : ℝ}
    (hF : Filter.Tendsto F Filter.atTop (nhds L))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1))
    (hrel : ∀ᶠ t in Filter.atTop, ‖G t‖ = ‖F t‖ / t) :
    L = 0 := by
  have hev : ∀ᶠ x in Filter.atTop, ‖L‖ / 2 ≤ ‖F x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg L) with h0 | h0
    · filter_upwards with x
      rw [← h0]
      simp
    · have hL := (tendsto_order.1 hF.norm).1 (‖L‖ / 2) (by linarith)
      filter_upwards [hL] with x hx using le_of_lt hx
  have hKey : ∀ᶠ R in Filter.atTop, ‖L‖ / 4 ≤ ∫ x in Set.Ioi R, ‖G x‖ := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hev.and hrel)
    refine Filter.eventually_atTop.2 ⟨max T 1, fun R hR => ?_⟩
    have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
    have hRT : T ≤ R := le_trans (le_max_left _ _) hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hR2 : R ≤ 2 * R := by linarith
    have hpt : ∀ x ∈ Set.Icc R (2 * R), ‖L‖ / (4 * R) ≤ ‖G x‖ := by
      intro x hx
      have hxR : R ≤ x := hx.1
      have hx2R : x ≤ 2 * R := hx.2
      have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans hR1 hxR)
      obtain ⟨hFb, hGx⟩ := hT x (le_trans hRT hxR)
      rw [hGx, show ‖L‖ / (4 * R) = (‖L‖ / 2) / (2 * R) by field_simp; ring]
      exact le_trans (div_le_div_of_nonneg_left (by positivity) hx0 hx2R)
        (div_le_div_of_nonneg_right hFb (le_of_lt hx0))
    have hlow : ‖L‖ / 4 ≤ ∫ x in R..(2 * R), ‖G x‖ := by
      have hconst : (∫ x in R..(2 * R), (‖L‖ / (4 * R) : ℝ)) = ‖L‖ / 4 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show (2 : ℝ) * R - R = R by ring]
        field_simp
      rw [← hconst]
      have hint : IntervalIntegrable (fun x => ‖G x‖) volume R (2 * R) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR2]
        have h1 : IntegrableOn (fun x => ‖G x‖) (Set.Ioi 1) := hG.norm
        exact h1.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hR1))
      exact intervalIntegral.integral_mono_on hR2 intervalIntegrable_const hint hpt
    have hup : (∫ x in R..(2 * R), ‖G x‖) ≤ ∫ x in Set.Ioi R, ‖G x‖ := by
      rw [intervalIntegral.integral_of_le hR2]
      refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
      · have h1 : IntegrableOn (fun x => ‖G x‖) (Set.Ioi 1) := hG.norm
        exact h1.mono_set (Set.Ioi_subset_Ioi hR1)
      · filter_upwards with x using norm_nonneg (G x)
      · filter_upwards with x hx using hx.1
    linarith
  have hAbsT : Filter.Tendsto (fun R : ℝ => ∫ x in Set.Ioi R, ‖G x‖) Filter.atTop (nhds 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero (b := fun R : ℝ => R) (f := fun x : ℝ => ‖G x‖)
      tendsto_id
  have hle : ‖L‖ / 4 ≤ 0 := ge_of_tendsto hAbsT hKey
  have hz : ‖L‖ = 0 := le_antisymm (by linarith) (norm_nonneg L)
  exact norm_eq_zero.1 hz

/-- **Right-endpoint limit** (intended namespace `Work.FTS.ClassCHon.Zpz`, module
`Submission.Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_upper`).

If `c` is differentiable on `(0,∞)` and both `c t * t ^ (-p - 1)` and its `t`-weighted derivative
`t * deriv c t * t ^ (-p - 1)` are integrable on `(1,∞)`, then `t ↦ c t * t ^ (-p)` tends to `0`
at `∞`.  No hypothesis on the real exponent `p` is needed.

Route (tools available in Mathlib): `F t := c t * t ^ (-p)` satisfies
`F' t = deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))` on `(0,∞)`, which is `L¹` on `(1,∞)`
(because `deriv c t * t ^ (-p) = t * deriv c t * t ^ (-p - 1)`); moreover
`∫ x in Ioi R, F' x → 0` as `R → ∞` (`MeasureTheory.tendsto_integral_Ioi_zero`), and
`F R - F 1 = ∫ x in (1)..R, F' x = ∫ x in Ioi 1, F' x - ∫ x in Ioi R, F' x` for `1 < R`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` plus `intervalIntegral.integral_interval_add_Ioi`),
so `F` has the finite limit `C := F 1 + ∫ x in Ioi 1, F' x` at `∞`.  Finally `C = 0`: if `C ≠ 0`
then `|c t * t ^ (-p - 1)| = |F t| / t ≥ |C| / (2 * t)` for all large `t`, contradicting `hinf`
because `∫ x in R..S, 1/x = Real.log (S / R) → ∞` as `S → ∞` (`integral_one_div_of_pos`). -/
theorem rpow_mul_tendsto_zero_upper {p : ℝ} {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi 1))
    (hdinf : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (-p - 1))
      (Set.Ioi 1)) :
    Filter.Tendsto (fun t => c t * t ^ (-p)) Filter.atTop (nhds 0) := by
  -- `t ^ (-p) = t * t ^ (-p - 1)` for `t > 0`
  have hrpow : ∀ t : ℝ, 0 < t → t ^ (-p) = t * t ^ (-p - 1) := by
    intro t ht
    have h : (1 : ℝ) + (-p - 1) = -p := by ring
    calc t ^ (-p) = t ^ ((1 : ℝ) + (-p - 1)) := by rw [h]
      _ = t ^ (1 : ℝ) * t ^ (-p - 1) := Real.rpow_add ht _ _
      _ = t * t ^ (-p - 1) := by rw [Real.rpow_one]
  -- the derivative of `F t = c t * t ^ (-p)`
  have hderiv : ∀ t ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun s : ℝ => c s * s ^ (-p))
        (deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have h2 : HasDerivAt (fun s : ℝ => s ^ (-p)) ((-p) * t ^ (-p - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht0))
    have h3 := (hcd t ht0).mul h2
    convert h3 using 1
    ring
  -- this derivative is integrable on `(1,∞)`
  have hF'int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) (Set.Ioi 1) := by
    have hA : MeasureTheory.IntegrableOn (fun t : ℝ => deriv c t * t ^ (-p)) (Set.Ioi 1) := by
      refine MeasureTheory.IntegrableOn.congr_fun hdinf (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := lt_trans one_pos ht
      show t * deriv c t * t ^ (-p - 1) = deriv c t * t ^ (-p)
      rw [show t * deriv c t * t ^ (-p - 1) = deriv c t * (t * t ^ (-p - 1)) by ring,
        hrpow t ht0]
    exact hA.sub (hinf.const_mul p)
  have hlim := MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 1)
    hderiv hF'int
  -- `‖c t * t ^ (-p - 1)‖ = ‖c t * t ^ (-p)‖ / t` for large `t`
  have hrel : ∀ᶠ t in Filter.atTop, ‖c t * t ^ (-p - 1)‖ = ‖c t * t ^ (-p)‖ / t := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have hmul : t ^ (-p - 1) * t = t ^ (-p) := by
      have h := Real.rpow_add ht0 (-p - 1) (1 : ℝ)
      rw [Real.rpow_one] at h
      rw [show (-p - 1) + 1 = -p by ring] at h
      exact h.symm
    rw [eq_div_iff_mul_eq (ne_of_gt ht0), norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1)),
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p))]
    rw [mul_assoc, hmul]
  have hkey : Filter.atTop.limUnder (fun t : ℝ => c t * t ^ (-p)) = 0 :=
    tendsto_eq_zero_of_div_integrable hlim hinf hrel
  rw [hkey] at hlim
  exact hlim

end Work.FTS.ClassCHon.Zpz
end
-- ===== merged: Submission.Work.FTS.ClassCHon.radGreen_compact_source_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_compact_source_interval`

The source facts needed by the per-mode weighted `L²` bound for the radial Green function
`radGreen α m c`, for a source `c` which is `C^∞` on `(0,∞)`, bounded, and supported in an
**arbitrary** interval `[a,b]` with `0 < a` (rather than in `[1,2]`, the case treated by the
sibling `Work.FTS.ClassC.HonestCut.radGreen_compact_source`):

* `c` is continuous on `(0,∞)`;
* `|c t| ≤ K/t` for `t ≥ 1`;
* `|c t| ≤ K t^p` on `(0,1]` for some `p > 3/2`;
* the four weighted integrals `∫_{0}^{1} c t^{(2m+5)/α-1}`, `∫_{0}^{1} c t^{-2m/α-1}`,
  `∫_{1}^{∞} c t^{-2m/α-1}` and `∫_{0}^{∞} c² w²` (with `w(z) = (1+z)²/z²`) are finite.

The mathematical content is elementary.  The observation needed beyond the sibling's proof is that
a function continuous on `(0,∞)` and vanishing off `[a,b] ⊂ (0,∞)` is **compactly supported**,
hence integrable on `(0,∞)` (`integrableOn_Ioi_of_contOn_of_support_prv` below, which splits
`(0,∞) = (0,a) ∪ [a,b] ∪ (b,∞)` when `a ≤ b` and is trivial when `b < a`, because then
`Icc a b = ∅` and `f ≡ 0`), together with the two pointwise bounds `decay_of_support_prv` (with
`K = M · max b 1 + 1`) and `vanishing_of_support_prv` (with `K = M/a² + 1`, `p = 2`).  No hypothesis
comparing `a` and `b` is needed, since membership in `Icc a b` always forces `a ≤ z`.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassCHon

/-- **Integrability on `(0,∞)` from continuity and compact support.**

If `f` is continuous on `(0,∞)` and vanishes off an interval `[a,b]` with `0 < a` (so that
`[a,b] ⊆ (0,∞)`), then `f` is integrable on `(0,∞)`.  The proof splits
`(0,∞) = (0,a) ∪ [a,b] ∪ (b,∞)`; on the two open pieces `f ≡ 0`, and on `[a,b]` it is continuous
on a compact set. -/
private theorem integrableOn_Ioi_of_contOn_of_support_prv {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Set.Ioi 0)) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  by_cases hab : a ≤ b
  swap
  · -- if `b < a` then `Icc a b = ∅`, so `f ≡ 0`
    rw [show f = fun _ => (0 : ℝ) from funext fun z =>
      hsupp z (fun h => hab (le_trans (Set.mem_Icc.mp h).1 (Set.mem_Icc.mp h).2))]
    exact MeasureTheory.integrableOn_zero
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha (Set.mem_Icc.mp hz).1
  have hIcc : MeasureTheory.IntegrableOn f (Set.Icc a b) :=
    (hf.mono hsub).integrableOn_compact isCompact_Icc
  have hleft : MeasureTheory.IntegrableOn f (Set.Ioo 0 a) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hz.2))])
      measurableSet_Ioo
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi b) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hz))])
      measurableSet_Ioi
  have hU : MeasureTheory.IntegrableOn f (Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b) :=
    (hleft.union hIcc).union hright
  have hset : Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro ((⟨h1, _⟩ | ⟨h2, _⟩) | h3) <;> linarith
    · intro hx
      rcases lt_or_ge x a with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · rcases le_or_gt x b with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
  rwa [hset] at hU

/-- **The decay of a source supported in `[a,b]` at `∞`:** `|c t| ≤ K/t` for `t ≥ 1`. -/
private theorem decay_of_support_prv {c : ℝ → ℝ} {a b : ℝ} {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t := by
  refine ⟨M * max b 1 + 1, by positivity, ?_⟩
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rcases lt_or_ge b t with hbt | hbt
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hbt)), abs_zero]
    positivity
  · have htle : t ≤ max b 1 := le_trans hbt (le_max_left b 1)
    have h1 : M ≤ (M * max b 1) / t := by
      rw [le_div_iff₀ ht0]
      linarith [mul_le_mul_of_nonneg_left htle hMnn]
    have h2 : (M * max b 1) / t ≤ (M * max b 1 + 1) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    linarith [hMb t]

/-- **The vanishing rate of a source supported in `[a,b]` near `0`:** `|c t| ≤ K t^p` on `(0,1]`
for some `p > 3/2`.  Since `c` vanishes on `(0,a)`, `p = 2` and `K = M/a² + 1` suffice. -/
private theorem vanishing_of_support_prv {c : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p := by
  refine ⟨M / a ^ 2 + 1, 2, by positivity, by norm_num, ?_⟩
  intro t _ht0 ht1
  by_cases hta : t < a
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hta)), abs_zero]
    positivity
  · have hge : a ≤ t := le_of_not_gt hta
    have hcoef : 0 ≤ M / a ^ 2 + 1 := by positivity
    have hK : (M / a ^ 2 + 1) * a ^ 2 = M + a ^ 2 := by field_simp
    rw [Real.rpow_two]
    calc |c t| ≤ M := hMb t
      _ ≤ M + a ^ 2 := by linarith [sq_nonneg a]
      _ = (M / a ^ 2 + 1) * a ^ 2 := hK.symm
      _ ≤ (M / a ^ 2 + 1) * t ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hge 2) hcoef


end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.radGreen_sup_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_sup_le`

The **sup-based sharp bound** for the radial Euler Green function `radGreen α m c`,
with *two* source bounds: one on the near field `(0,z]` and one on the far field `[z,∞)`.

## The computation

With

  `q := (2m+5)/α > 0`,   `p := 2m/α > 0`,   `K := 1/(α(4m+5))`,

the definition is

  `radGreen α m c z = K · ( z^{-q} · ∫_0^z c t · t^{q-1} dt + z^{p} · ∫_z^∞ c t · t^{-p-1} dt )`.

If `|c t| ≤ M₁` for `0 < t ≤ z` and `|c t| ≤ M₂` for `t ≥ z`, then using the two elementary
rpow integrals (`∫_0^z t^{q-1} = z^q/q` for `q > 0`, `∫_z^∞ t^{-p-1} = z^{-p}/p` for `p > 0`,
`z > 0`):

  `z^{-q} · |∫_0^z c t^{q-1}| ≤ z^{-q} · M₁ z^q/q = M₁/q = M₁ α/(2m+5)`,
  `z^{p} · |∫_z^∞ c t^{-p-1}| ≤ z^{p} · M₂ z^{-p}/p = M₂/p = M₂ α/(2m)`,

whence

  `|radGreen α m c z| ≤ K · (M₁ α/(2m+5) + M₂ α/(2m))`
    `= M₁/((4m+5)(2m+5)) + M₂/((4m+5)(2m))`,

which is exactly the claimed bound.  Nothing beyond the two pointwise bounds on `c` and
`z > 0` is used.  (In particular the statement is insensitive to the junk-integral
convention: if either integrand of the Green formula is not integrable, the corresponding
Bochner integral is `0`, and the estimate still holds.)

The two integral estimates are the private lemmas `near_int_bound_sup` and `far_int_bound_sup`;
they are the half-line-(`(0,z]` / `[z,∞)`) refinements of the global-bound lemmas
`near_int_bound` / `far_int_bound` of `FTS/ClassCHon/radGreen_size_bound.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon




end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_sq_w_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-- Continuity on `(0,∞)` of the function under consideration, in the generic shape
`(z² P(z)/(1+z)^k)² · ((1+z)²/z²)²` in which the five cases of `rB` present themselves. -/
private theorem rB_contOn_generic (P : ℝ → ℝ) (k : ℕ) (hP : Continuous P) :
    ContinuousOn (fun z : ℝ => (z ^ 2 * P z / (1 + z) ^ k) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2)
      (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun z : ℝ => z ^ 2 * P z / (1 + z) ^ k) (Set.Ioi 0) := by
    apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero k (by linarith [Set.mem_Ioi.mp hx])
  have h2 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt hx)
  exact (h1.pow 2).mul (h2.pow 2)

/-- `z ↦ (rB j z)² w(z)²` is continuous on `(0,∞)` for `j ≤ 4`. -/
private theorem rB_contOn (j : ℕ) (hj : j ≤ 4) :
    ContinuousOn (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  interval_cases j
  · simpa only [rB_zero, Work.Spaces.w, mul_one] using
      rB_contOn_generic (fun _ => (1 : ℝ)) 3 continuous_const
  · simpa only [rB_one, Work.Spaces.w] using
      rB_contOn_generic (fun z => (2 : ℝ) - z) 4 (by fun_prop)
  · simpa only [rB_two, Work.Spaces.w] using
      rB_contOn_generic (fun z => (4 : ℝ) - 7 * z + z ^ 2) 5 (by fun_prop)
  · simpa only [rB_three, Work.Spaces.w] using
      rB_contOn_generic (fun z => (8 : ℝ) - 33 * z + 18 * z ^ 2 - z ^ 3) 6 (by fun_prop)
  · simpa only [rB_four, Work.Spaces.w] using
      rB_contOn_generic (fun z => (16 : ℝ) - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) 7
        (by fun_prop)

/-- Pointwise domination of `(rB j z)² w(z)²` by `40000/(1+z)²` for `z > 0` and `j ≤ 4`.
The constant `40000 = 200²` dominates the square of the largest coefficient (`171`) occurring
in the five numerators, and `200 (1+z)^j` dominates the corresponding `N_j`. -/
private theorem rB_case_le (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 40000 * (1 / (1 + z) ^ 2) := by
  interval_cases j <;>
    simp only [rB_zero, rB_one, rB_two, rB_three, rB_four, Work.Spaces.w] <;>
    field_simp <;>
    nlinarith [sq_nonneg z, sq_nonneg (z * z), sq_nonneg (z ^ 3)]

theorem rB_sq_w_integrable : ∀ j ≤ 4, MeasureTheory.IntegrableOn
    (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  intro j hj
  change MeasureTheory.IntegrableOn
    (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ici 0)
  refine (integrableOn_Ici_iff_integrableOn_Ioi
    (f := fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (b := 0)).mpr ?_
  -- the dominating function `40000/(1+z)²` is integrable on `(0,∞)`
  have hdom : MeasureTheory.Integrable (fun z : ℝ => 40000 * (1 / (1 + z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
      have hpow : MeasureTheory.IntegrableOn (fun z : ℝ => (z + 1) ^ (-2 : ℝ)) (Set.Ioi 0) :=
        integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
      refine hpow.congr_fun (fun z hz => ?_) measurableSet_Ioi
      have hz1 : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
      show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
      rw [Real.rpow_neg (le_of_lt hz1), Real.rpow_two, inv_eq_one_div]
      ring_nf
    exact MeasureTheory.Integrable.const_mul h1 40000
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (rB_contOn j hj).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : (0 : ℝ) < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact rB_case_le j hj hz'

end Work.FTS.CoercivityFix.Transfer.E2pkg
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G1Aux =====
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

set_option autoImplicit false

/-- The exponent `s⁻ = -(2m+5)/α` of the singular Green term `G1`. -/
def G1s (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The positive exponent `a = (2m+5)/α = -s⁻`. -/
def G1a (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The integrand `t ↦ c t · t^{a-1}` of the inner integral of `G1`. -/
def G1f (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The inner integral `z ↦ ∫₀^z c t t^{a-1} dt` of `G1`. -/
def G1A (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, G1f α m c t

/-- `M0 = ∫_{(0,1)} c z²/z⁴`. -/
def G1M0 (c : ℝ → ℝ) : ℝ := ∫ z in Set.Ioo 0 1, c z ^ 2 / z ^ 4

/-- The endpoint constant `C0 = M0/2 + 1/(2(2a+3))`. -/
def G1C0 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ := G1M0 c / 2 + 1 / (2 * (2 * G1a α m + 3))

/-- The endpoint bound `CΦ = C0²` for `G1 z²/z³`. -/
def G1CPhi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ := G1C0 α m c ^ 2

/-- The AM–GM parameter `η = 2/(3+2a)`. -/
def G1eta (α : ℝ) (m : ℕ) : ℝ := 2 / (3 + 2 * G1a α m)

/-- The uniform bound `M = 2(η M0 + CΦ)/(3+2a)`. -/
def G1M (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  2 * (G1eta α m * G1M0 c + G1CPhi α m c) / (3 + 2 * G1a α m)

/-- `G1` is `z^{s⁻}` times the inner integral `G1A` (definitional). -/
theorem G1_eq_zpow_mul_G1A (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    G1 α m c z = z ^ (G1s α m) * G1A α m c z := rfl

/-- `s⁻ = -a`. -/
theorem G1s_eq_neg_G1a (α : ℝ) (m : ℕ) : G1s α m = -G1a α m := by
  simp only [G1s, G1a, neg_div]

/-- `a > 0` when `α > 0`. -/
theorem G1a_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < G1a α m := by
  rw [G1a]; positivity

/-- Young's inequality `2|XY| ≤ X² + Y²`. -/
theorem G1_two_mul_abs_mul_le (X Y : ℝ) : 2 * |X * Y| ≤ X ^ 2 + Y ^ 2 := by
  have h := sq_nonneg (|X| - |Y|)
  rw [sub_sq, sq_abs, sq_abs] at h
  rw [abs_mul]
  nlinarith [h]

/-- The weighted Young inequality `2|XY| ≤ λX² + Y²/λ` for `λ > 0`. -/
theorem G1_two_mul_abs_mul_le_mul {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + Y ^ 2 / l := by
  have h := G1_two_mul_abs_mul_le (l * X) Y
  rw [abs_mul, abs_mul, abs_of_pos hl, mul_pow] at h
  have h' : l * (2 * |X * Y|) ≤ l * (l * X ^ 2 + Y ^ 2 / l) := by
    have e : l * (l * X ^ 2 + Y ^ 2 / l) = l ^ 2 * X ^ 2 + Y ^ 2 := by
      field_simp
    rw [e, abs_mul]
    nlinarith [h]
  exact le_of_mul_le_mul_left h' hl

/-- `M0` is nonnegative (the integrand `c z²/z⁴` is pointwise nonnegative). -/
theorem G1M0_nonneg (c : ℝ → ℝ) : 0 ≤ G1M0 c := by
  rw [G1M0]
  exact setIntegral_nonneg measurableSet_Ioo
    (fun z _ => div_nonneg (sq_nonneg _) (by positivity))


/-- `CΦ ≥ 0`. -/
theorem G1CPhi_nonneg (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G1CPhi α m c := by
  rw [G1CPhi]; exact sq_nonneg _

/-- `η > 0`. -/
theorem G1eta_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < G1eta α m := by
  rw [G1eta]
  have := G1a_pos hα m
  positivity

/-- `M ≥ 0`. -/
theorem G1M_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) : 0 ≤ G1M α m c := by
  rw [G1M]
  have h1 := G1M0_nonneg c
  have h2 := G1eta_pos hα m
  have h3 := G1CPhi_nonneg α m c
  have h4 : (0 : ℝ) < 3 + 2 * G1a α m := by
    have := G1a_pos hα m; linarith
  refine div_nonneg (mul_nonneg (by norm_num) ?_) (le_of_lt h4)
  exact add_nonneg (mul_nonneg (le_of_lt h2) h1) h3

/-- `G1f` is continuous on `(0,∞)`. -/
theorem G1f_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (G1f α m c) (Set.Ioi 0) := by
  exact hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

/-- **Integrability of the inner integrand.**  The standing hypothesis `h0`
(`c z²/z⁴` integrable on `(0,1)`) makes `t ↦ c t t^{a-1}` integrable on `(0,1)`: pointwise,
`|c t| t^{a-1} ≤ |c t|/t² ≤ (c t²/t⁴ + 1)/2` for `0 < t ≤ 1`. -/
theorem G1f_integrableOn {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    IntegrableOn (G1f α m c) (Set.Ioo 0 1) := by
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 1) :=
    (continuousOn_const.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have hmaj : IntegrableOn (fun t : ℝ => c t ^ 2 / t ^ 4 + 1) (Set.Ioo 0 1) := h0.add h2
  refine Integrable.mono' hmaj
    (((G1f_continuousOn hc).mono Set.Ioo_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioo) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have ha : 0 < (2 * (m : ℝ) + 5) / α := by positivity
  calc ‖G1f α m c t‖ = |c t| * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
        rw [G1f, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    _ ≤ |c t| * t ^ (-2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_ge ht0 ht1 ?_
        linarith
    _ = |c t| / t ^ 2 := by
        rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two, div_eq_mul_inv]
    _ ≤ c t ^ 2 / t ^ 4 + 1 := by
        have hx : (0 : ℝ) ≤ |c t| / t ^ 2 := div_nonneg (abs_nonneg _) (by positivity)
        have h := G1_two_mul_abs_mul_le (|c t| / t ^ 2) 1
        rw [mul_one, one_pow, abs_of_nonneg hx,
          div_pow, sq_abs, ← pow_mul] at h
        norm_num at h
        linarith [h]

/-- **Fundamental theorem of calculus for `G1A`.** -/
theorem G1A_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (G1A α m c) (G1f α m c z) z := by
  intro z hz
  have hF : ContinuousOn (G1f α m c) (Set.Ioi 0) := G1f_continuousOn hc
  exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := z)
    (Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo hz hF hInt)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF z hz)
    (hF.continuousAt (Ioi_mem_nhds hz))

/-- **Monotonicity of `∫ c z²/z⁴`**: on any `(x,y) ⊆ (0,1)` the integral is at most `M0`
(the integrand is nonnegative and `Ioc x y ⊆ Ioo 0 1`). -/
theorem G1_csq_mono {c : ℝ → ℝ}
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x y : ℝ, 0 < x → x < y → y < 1 → ∫ z in x..y, c z ^ 2 / z ^ 4 ≤ G1M0 c := by
  intro x y hx hxy hy1
  rw [intervalIntegral.integral_of_le hxy.le, G1M0]
  refine setIntegral_mono_set h0 (Filter.Eventually.of_forall (fun z => ?_)) ?_
  · exact div_nonneg (sq_nonneg _) (by positivity)
  · exact Filter.Eventually.of_forall
      (fun z hz => ⟨lt_trans hx hz.1, lt_of_le_of_lt hz.2 hy1⟩)

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G2_est =====
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

set_option autoImplicit false

/-! ## Elementary estimates for the constants of the `z^{s⁺}` estimate

Nothing here is specific to `G2`: we only need `η = 2/(2b-3) > 0` (from `b = 2m/α ≥ 8`), the
nonnegativity of the two integrals `M0 = ∫_{(0,1)} c z²/z⁴` and `H = ∫_1^∞ |c t| t^{-b-1}`, and the
weighted AM–GM inequality `2|XY| ≤ η X² + η⁻¹ Y²`. -/

/-- The AM–GM parameter `η = 2/(2b-3)`, where `b = 2m/α`. -/
private def G2eta (α : ℝ) (m : ℕ) : ℝ := 2 / (2 * (2 * (m : ℝ) / α) - 3)

/-- `H = ∫_{(1,∞)} |c t| · t^{-b-1} dt`, the constant controlling the endpoint `z = 1`. -/
private def G2H (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi 1, |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)

/-- `M0 = ∫_{(0,1)} c z²/z⁴`, the total mass of the density appearing in the hypothesis `h0`. -/
private def G2M0 (c : ℝ → ℝ) : ℝ := ∫ z in Set.Ioo 0 1, c z ^ 2 / z ^ 4

/-- The uniform bound `M = η (η M0 + H²)` of the estimate. -/
private def G2M (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ :=
  G2eta α m * (G2eta α m * G2M0 c + G2H α m c ^ 2)

/-- Young's inequality `2|XY| ≤ X² + Y²`. -/
private lemma G2_two_mul_abs_mul_le (X Y : ℝ) : 2 * |X * Y| ≤ X ^ 2 + Y ^ 2 := by
  have h := sq_nonneg (|X| - |Y|)
  rw [sub_sq, sq_abs, sq_abs] at h
  rw [abs_mul]
  nlinarith [h]

/-- The weighted Young inequality `2|XY| ≤ λ X² + Y²/λ` for `λ > 0` (the AM–GM step). -/
private lemma G2_two_mul_abs_mul_le_mul {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + Y ^ 2 / l := by
  have h := G2_two_mul_abs_mul_le (l * X) Y
  rw [abs_mul, abs_mul, abs_of_pos hl, mul_pow] at h
  have h' : l * (2 * |X * Y|) ≤ l * (l * X ^ 2 + Y ^ 2 / l) := by
    have e : l * (l * X ^ 2 + Y ^ 2 / l) = l ^ 2 * X ^ 2 + Y ^ 2 := by
      field_simp
    rw [e, abs_mul]
    nlinarith [h]
  exact le_of_mul_le_mul_left h' hl

/-- `M0 ≥ 0` (the integrand `c z²/z⁴` is a square over a square). -/
private lemma G2M0_nonneg (c : ℝ → ℝ) : 0 ≤ G2M0 c := by
  rw [G2M0]
  exact setIntegral_nonneg measurableSet_Ioo
    (fun z _ => div_nonneg (sq_nonneg _) (by positivity))


/-- `η = 2/(2b-3) > 0`, since `b = 2m/α ≥ 8` (`eight_le_two_m_div`). -/
private lemma G2eta_pos (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) :
    0 < G2eta α m := by
  have h8 := eight_le_two_m_div α hα hα4 m hm
  rw [G2eta]
  have : (0 : ℝ) < 2 * (2 * (m : ℝ) / α) - 3 := by linarith
  positivity

/-- `M ≥ 0`. -/
private lemma G2M_nonneg (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    (c : ℝ → ℝ) : 0 ≤ G2M α m c := by
  have hη : 0 < G2eta α m := G2eta_pos α hα hα4 m hm
  rw [G2M]
  exact mul_nonneg (le_of_lt hη)
    (add_nonneg (mul_nonneg (le_of_lt hη) (G2M0_nonneg c)) (by positivity))

/-! ## The tail integral, its derivative, and the scaled derivative of `G2` -/

/-- `t ↦ c t · t^{-s-1}` is continuous on `(0,∞)` when `c` is. -/
private lemma f2_contOn (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun _ ht => Or.inl (ne_of_gt ht)))

/-- The tail integrand `t ↦ c t · t^{-s-1}` is integrable on `(1,∞)` as soon as
`t ↦ |c t| · t^{-s-1}` is: the rpow factor is positive there, so the absolute values agree.  This
is the only use of the decay hypothesis `hinf` in the differentiability statements below. -/
private lemma f2_intOn (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1)) :
    IntegrableOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi 1) := by
  have hmeas : AEStronglyMeasurable (fun t => c t * t ^ (-s - 1))
      (volume.restrict (Set.Ioi 1)) :=
    ((f2_contOn s hc).mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
      measurableSet_Ioi
  have hnorm : IntegrableOn (fun t => ‖c t * t ^ (-s - 1)‖) (Set.Ioi 1) :=
    hinf.congr_fun (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _)])
      measurableSet_Ioi
  exact (integrable_norm_iff hmeas).mp hnorm

/-- **FTC for the tail integral** (with the moving base point `z/2`, which avoids any global
integrability assumption on `(0,∞)`): `z ↦ ∫_{t>z} c t t^{-s-1} dt` has derivative
`-c z · z^{-s-1}` for `z > 0`. -/
private lemma tail_deriv (s : ℝ) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (fun u => ∫ t in Set.Ioi u, c t * t ^ (-s - 1)) (-(c z * z ^ (-s - 1))) z := by
  intro z hz
  have hz2 : 0 < z / 2 := by linarith
  have hc' : ContinuousOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi (z / 2)) :=
    (f2_contOn s hc).mono (Set.Ioi_subset_Ioi (le_of_lt hz2))
  have hi' : IntegrableOn (fun t => c t * t ^ (-s - 1)) (Set.Ioi (z / 2)) :=
    Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hz2 (f2_contOn s hc)
      (f2_intOn s hc hinf)
  exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (by linarith) hc' hi'

/-- Scalar algebra for the product rule: for `z > 0` and real `B, C`,
`z·(s z^{s-1} B - z^s C z^{-s-1}) = s z^s B - C`. -/
private lemma scaled_alg {z s : ℝ} (hz : 0 < z) (B C : ℝ) :
    z * (s * z ^ (s - 1) * B + z ^ s * (-(C * z ^ (-s - 1)))) = s * (z ^ s * B) - C := by
  have hA : z * z ^ (s - 1) = z ^ s := by
    have h := Real.rpow_add hz (s - 1) 1
    rw [Real.rpow_one, show s - 1 + 1 = s from by ring] at h
    rw [mul_comm z (z ^ (s - 1))]
    exact h.symm
  have hC : z * z ^ s * z ^ (-s - 1) = 1 := by
    have h := Real.rpow_add hz s (-s - 1)
    rw [show z * z ^ s * z ^ (-s - 1) = z * (z ^ s * z ^ (-s - 1)) from by ring, ← h,
      show s + (-s - 1) = -1 from by ring, Real.rpow_neg_one]
    exact mul_inv_cancel₀ (ne_of_gt hz)
  have e1 : z * (s * z ^ (s - 1) * B) = s * (z ^ s * B) := by
    rw [show z * (s * z ^ (s - 1) * B) = s * (z * z ^ (s - 1)) * B from by ring, hA]
    ring
  have e2 : z * (z ^ s * (-(C * z ^ (-s - 1)))) = -C := by
    rw [show z * (z ^ s * (-(C * z ^ (-s - 1))))
        = -(C * (z * z ^ s * z ^ (-s - 1))) from by ring, hC]
    ring
  rw [mul_add, e1, e2]
  ring

/-- **The (scaled) logarithmic derivative of the `z^{s⁺}` Green term**: `z · Ψ'(z) = s⁺ Ψ(z) - c z`
at every `z > 0`, `s⁺ = 2m/α`, equivalently `HasDerivAt Ψ ((s⁺ Ψ z - c z)/z) z`. -/
private lemma G2_scaled_deriv (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → HasDerivAt (fun w => G2 α m c w)
      ((2 * (m : ℝ) / α * G2 α m c z - c z) / z) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  set s : ℝ := 2 * (m : ℝ) / α with hs
  have hinf' : IntegrableOn (fun t => |c t| * t ^ (-s - 1)) (Set.Ioi 1) := by
    rw [hs]; exact hinf
  have hB := tail_deriv s hc hinf' z hz
  have hp : HasDerivAt (fun u : ℝ => u ^ s) (s * z ^ (s - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have hprod := hp.mul hB
  change HasDerivAt (fun w : ℝ => w ^ s * (∫ t in Set.Ioi w, c t * t ^ (-s - 1)))
    ((s * (G2 α m c z) - c z) / z) z
  have hval : s * z ^ (s - 1) * (∫ t in Set.Ioi z, c t * t ^ (-s - 1))
      + z ^ s * (-(c z * z ^ (-s - 1)))
      = (s * G2 α m c z - c z) / z := by
    have hG : G2 α m c z = z ^ s * (∫ t in Set.Ioi z, c t * t ^ (-s - 1)) := rfl
    rw [hG, eq_div_iff hzne]
    simpa [mul_comm] using scaled_alg hz (∫ t in Set.Ioi z, c t * t ^ (-s - 1)) (c z)
  exact hprod.congr_deriv hval

/-- `G2 α m c` is continuous on `(0,∞)` (it is differentiable there, by `G2_scaled_deriv`). -/
private lemma G2_continuousOn (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ContinuousOn (fun z => G2 α m c z) (Set.Ioi 0) :=
  fun z hz => ((G2_scaled_deriv α m hc hinf z hz).continuousAt).continuousWithinAt

/-! ## The energy identity on `[x,1]` and the endpoint bound at `z = 1` -/

/-- The quotient `z ↦ Ψ z²/z³` has derivative `((2b-3) Ψ z² - 2 c z Ψ z)/z⁴` whenever
`Ψ'(z) = (b Ψ z - c z)/z`. -/
private lemma u_deriv (b : ℝ) {Ψ : ℝ → ℝ} {c : ℝ → ℝ}
    (hΨ : ∀ z : ℝ, 0 < z → HasDerivAt Ψ ((b * Ψ z - c z) / z) z) :
    ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Ψ z ^ 2 / z ^ 3)
      (((2 * b - 3) * Ψ z ^ 2 - 2 * c z * Ψ z) / z ^ 4) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have h1 : HasDerivAt (fun w : ℝ => Ψ w ^ 2)
      (2 * Ψ z ^ (2 - 1) * ((b * Ψ z - c z) / z)) z := (hΨ z hz).pow 2
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ (3 - 1) * 1) z :=
    (hasDerivAt_id z).pow 3
  have h3 := h1.div h2 (pow_ne_zero 3 hzne)
  refine h3.congr_deriv ?_
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hzne
  field_simp
  ring

/-- **Energy identity** for `Ψ = G2 α m c` on `[x,1]`, `0 < x < 1`:
`(2b-3) ∫_x^1 Ψ²/z⁴ = 2 ∫_x^1 c z Ψ/z⁴ + Ψ(1)² - Ψ(x)²/x³`. -/
private lemma G2_energy (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
          + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := by
  intro x hx hx1
  set b : ℝ := 2 * (m : ℝ) / α with hb
  have hscaled := G2_scaled_deriv α m hc hinf
  have hscaled' : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => G2 α m c w) ((b * G2 α m c z - c z) / z) z := by
    intro z hz
    have hval : (b * G2 α m c z - c z) / z
        = (2 * (m : ℝ) / α * G2 α m c z - c z) / z := by rw [hb]
    rw [hval]
    exact hscaled z hz
  have hderiv := u_deriv b hscaled'
  have hsub : Set.Icc x 1 ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hx hz.1
  have hΨc : ContinuousOn (fun z => G2 α m c z) (Set.Icc x 1) := fun z hz =>
    ((hscaled z (hsub hz)).continuousAt).continuousWithinAt
  have hcc : ContinuousOn c (Set.Icc x 1) := hc.mono hsub
  have hz4ne : ∀ z ∈ Set.Icc x 1, z ^ 4 ≠ 0 := fun z hz =>
    pow_ne_zero 4 (ne_of_gt (hsub hz))
  have hinteg : IntervalIntegrable
      (fun z => ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (ContinuousOn.sub
      (continuousOn_const.mul (hΨc.pow 2)) ((continuousOn_const.mul hcc).mul hΨc))
      (continuousOn_id.pow 4) hz4ne
  have hpoint : ∀ z ∈ Set.uIcc x 1,
      HasDerivAt (fun z => G2 α m c z ^ 2 / z ^ 3)
        (((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4) z := by
    intro z hz
    rw [Set.uIcc_of_le hx1.le] at hz
    exact hderiv z (hsub hz)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hpoint hinteg
  have hI1 : IntervalIntegrable (fun z => G2 α m c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (hΨc.pow 2) (continuousOn_id.pow 4) hz4ne
  have hI2 : IntervalIntegrable (fun z => c z * G2 α m c z / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx1.le]
    exact ContinuousOn.div (hcc.mul hΨc) (continuousOn_id.pow 4) hz4ne
  have hsplit : (∫ z in x..1, ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4)
      = (2 * b - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        - 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4) := by
    have hfun : (fun z => ((2 * b - 3) * G2 α m c z ^ 2 - 2 * c z * G2 α m c z) / z ^ 4)
        = fun z => (2 * b - 3) * (G2 α m c z ^ 2 / z ^ 4)
            - 2 * (c z * G2 α m c z / z ^ 4) := by
      funext z; ring
    rw [hfun, intervalIntegral.integral_sub (hI1.const_mul (2 * b - 3)) (hI2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hfinal : (2 * b - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
        + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := by
    have h1 : G2 α m c 1 ^ 2 / 1 ^ 3 = G2 α m c 1 ^ 2 := by norm_num
    rw [hsplit] at hFTC
    linarith [hFTC, h1]
  rw [hb] at hfinal
  exact hfinal

/-- **Endpoint bound at `z = 1`**: `|G2 α m c 1| ≤ H`, because at `z = 1` the prefactor `z^{s⁺}`
equals `1` and the value is the tail integral, which the triangle inequality bounds by `H`. -/
private lemma G2_one_le (α : ℝ) (m : ℕ) {c : ℝ → ℝ}
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    |G2 α m c 1| ≤ G2H α m c := by
  rw [G2H, G2, Real.one_rpow, one_mul]
  refine le_trans (MeasureTheory.abs_integral_le_integral_abs)
    (le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_))
  intro t ht
  show |c t * t ^ (-(2 * (m : ℝ) / α) - 1)| = |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one ht) _)]

/-- **Monotonicity of the mass integral**: `∫_x^1 c z²/z⁴ ≤ M0` for `0 < x < 1` (the integrand is
nonnegative and `(x,1] ⊆ᵃᵉ (0,1)`). -/
private lemma G2_csq_mono {c : ℝ → ℝ}
    (h0 : IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      (∫ z in x..1, c z ^ 2 / z ^ 4) ≤ G2M0 c := by
  intro x hx hx1
  have hf : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun z => c z ^ 2 / z ^ 4) :=
    Filter.Eventually.of_forall (fun z => div_nonneg (sq_nonneg _) (by positivity))
  have hsub : Set.Ioc x 1 \ Set.Ioo (0 : ℝ) 1 ⊆ ({1} : Set ℝ) := by
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff] at ht ⊢
    by_cases h : t ≤ 0
    · linarith [ht.1.1, hx, h]
    · have h1 : 0 < t := lt_of_not_ge h
      by_contra hne
      exact ht.2 ⟨h1, lt_of_le_of_ne ht.1.2 hne⟩
  have hst : Set.Ioc x 1 ≤ᵐ[volume] Set.Ioo (0 : ℝ) 1 := by
    rw [ae_le_set]
    exact measure_mono_null hsub (measure_singleton 1)
  rw [G2M0, intervalIntegral.integral_of_le hx1.le]
  exact MeasureTheory.setIntegral_mono_set h0 hf hst


-- ROUTE (the `z → 0` half of the weighted `L²`-honesty of the `z^{s⁺}` Green term of `radGreen`).
-- Let `b := 2*(m:ℝ)/α` (so `b ≥ 8` by `Work.FTS.EllExist.Honesty.eight_le_two_m_div`, from `hα`, `hα4`, `hm`),
-- `f2 t := c t * t^(-b-1)`, `B z := ∫ t in Ioi z, f2 t`, `Ψ := Work.FTS.EllExist.Honesty.G2 α m c`
-- (so `Ψ z = z^b * B z`), `M0 := ∫ z in Ioo 0 1, c z^2/z^4` (a nonnegative real, finite by `h0`), and
-- `H := ∫ t in Ioi 1, |c t| * t^(-b-1)` (a nonnegative real, finite by `hinf`).
--
-- TWO TRAPS: (i) do NOT try to bound `∫ z in z₀..1, t^(2-2b)` by `1/(2b-3)`: since `2-2b ≤ -14 < -1` the
-- true value is `(z₀^(3-2b)-1)/(2b-3) → ∞`, and `|B z|` is indeed unbounded as `z → 0` (e.g. `c t = t²` gives
-- `B z = z^{-6}/6`, yet `Ψ z = z²/6` is perfectly bounded).  (ii) `f2` need NOT be in `L¹(0,∞)` (same
-- example), so `Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi` must be applied with a base point `a < z`,
-- e.g. `a := z/2` (its hypotheses then only need `f2` continuous on `(z/2,∞)` and integrable on
-- `Ioi (z/2)`, which holds because `f2` is continuous on the compact `[z/2,1]` and integrable on `Ioi 1`
-- by `hinf`).
--
-- The uniform bound comes from the energy identity on `[x,1]`:
-- (1) `B` is differentiable on `(0,∞)` with `B' z = -f2 z`, hence `z * deriv Ψ z = b*Ψ z - c z` for `z > 0`
--     (use `b * z^(b-1) * B z + z^b * (-f2 z) = (b*Ψ z - c z)/z`, since `z^(b+1) * f2 z = c z`).
-- (2) `u z := Ψ z^2 / z^3` has `u' z = ((2b-3)*Ψ z^2 - 2*c z*Ψ z)/z^4`; the FTC on `[x,1]` (`0 < x < 1`) gives
--       `(2b-3) * ∫ z in x..1, Ψ z^2/z^4 = 2 * ∫ z in x..1, c z * Ψ z/z^4 + Ψ 1^2 - Ψ x^2/x^3`.
--     Both endpoint terms are harmless: `Ψ x^2/x^3 ≥ 0` is SUBTRACTED, and `|Ψ 1| = |B 1| ≤ H`.
-- (3) AM-GM `2*|c z * Ψ z|/z^4 ≤ η*c z^2/z^4 + η^{-1}*Ψ z^2/z^4` with `η := 2/(2b-3)`, together with
--     `∫ z in x..1, c z^2/z^4 ≤ M0`, gives `((2b-3)/2) * ∫ z in x..1, Ψ^2/z^4 ≤ η*M0 + H^2`, i.e.
--     `∫ z in x..1, Ψ z^2/z^4 ≤ M := 2*(η*M0 + H^2)/(2b-3)` for every `x ∈ (0,1)`.  For the requested
--     interval `(x,y)`, `y < 1`, monotonicity of the integral of the nonnegative integrand gives
--     `∫ z in x..y, Ψ z^2/z^4 ≤ ∫ z in x..1, Ψ z^2/z^4 ≤ M`.
-- (4) Continuity of `Ψ` on `(0,∞)`: product of the continuous `z ↦ z^b` and the differentiable `B`.
theorem G2_est (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, 0 < x → x < y → y < 1 →
        (∫ z in x..y, Work.FTS.EllExist.Honesty.G2 α m c z ^ 2 / z ^ 4) ≤ M) ∧
      ContinuousOn (fun z => Work.FTS.EllExist.Honesty.G2 α m c z) (Set.Ioi 0) := by
  have hη : 0 < G2eta α m := G2eta_pos α hα hα4 m hm
  refine ⟨⟨G2M α m c, G2M_nonneg α hα hα4 m hm c, ?_⟩, G2_continuousOn α m hc hinf⟩
  intro x y hx hxy hy1
  have hx1 : x < 1 := lt_trans hxy hy1
  have hIn : ∀ z ∈ Set.Icc x 1, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le hx hz.1
  have hsub : Set.Icc x 1 ⊆ Set.Ioi (0 : ℝ) := fun z hz => hIn z hz
  have hΦc : ContinuousOn (fun z => G2 α m c z) (Set.Icc x 1) :=
    (G2_continuousOn α m hc hinf).mono hsub
  have hcc : ContinuousOn c (Set.Icc x 1) := hc.mono hsub
  have hpow : ContinuousOn (fun z : ℝ => z ^ 4) (Set.Icc x 1) := continuousOn_id.pow 4
  have hz4ne : ∀ z ∈ Set.Icc x 1, z ^ 4 ≠ 0 := fun z hz => pow_ne_zero 4 (ne_of_gt (hIn z hz))
  -- the pointwise AM–GM inequality `2|c Ψ|/z⁴ ≤ η c²/z⁴ + η⁻¹ Ψ²/z⁴`
  have hpt : ∀ z ∈ Set.Icc x 1,
      2 * |c z * G2 α m c z / z ^ 4|
        ≤ G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4) := by
    intro z _
    have h1 : 2 * |c z * G2 α m c z| ≤ G2eta α m * c z ^ 2 + (G2eta α m)⁻¹ * (G2 α m c z) ^ 2 := by
      have h := G2_two_mul_abs_mul_le_mul (hl := hη) (X := c z) (Y := G2 α m c z)
      have e : (G2 α m c z) ^ 2 / G2eta α m = (G2eta α m)⁻¹ * (G2 α m c z) ^ 2 := by
        rw [div_eq_mul_inv, mul_comm]
      linarith [h, e]
    have h2 : 2 * |c z * G2 α m c z / z ^ 4| = 2 * |c z * G2 α m c z| / z ^ 4 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 4)]
      ring
    have h3 : (G2eta α m * c z ^ 2 + (G2eta α m)⁻¹ * (G2 α m c z) ^ 2) / z ^ 4
        = G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4) := by
      ring
    rw [h2, ← h3]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  -- continuity of the two comparison integrands on `[x,1]`
  have huIcc : Set.uIcc x 1 = Set.Icc x 1 := Set.uIcc_of_le hx1.le
  have hcont1 : ContinuousOn (fun z : ℝ => 2 * |c z * G2 α m c z / z ^ 4|) (Set.uIcc x 1) := by
    rw [huIcc]
    exact continuousOn_const.mul (ContinuousOn.abs (ContinuousOn.div (hcc.mul hΦc) hpow hz4ne))
  have hcont2 : ContinuousOn
      (fun z : ℝ => G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      (Set.uIcc x 1) := by
    rw [huIcc]
    exact ContinuousOn.add (continuousOn_const.mul (ContinuousOn.div (hcc.pow 2) hpow hz4ne))
      (continuousOn_const.mul (ContinuousOn.div (hΦc.pow 2) hpow hz4ne))
  have hI1 : IntervalIntegrable (fun z : ℝ => 2 * |c z * G2 α m c z / z ^ 4|) volume x 1 :=
    ContinuousOn.intervalIntegrable hcont1
  have hI2 : IntervalIntegrable
      (fun z : ℝ => G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      volume x 1 := ContinuousOn.intervalIntegrable hcont2
  have hIc : IntervalIntegrable (fun z : ℝ => c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact ContinuousOn.div (hcc.pow 2) hpow hz4ne
  have hIg : IntervalIntegrable (fun z : ℝ => G2 α m c z ^ 2 / z ^ 4) volume x 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact ContinuousOn.div (hΦc.pow 2) hpow hz4ne
  have hlin : (∫ z in x..1,
        G2eta α m * (c z ^ 2 / z ^ 4) + (G2eta α m)⁻¹ * (G2 α m c z ^ 2 / z ^ 4))
      = G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    rw [intervalIntegral.integral_add (hIc.const_mul (G2eta α m)) (hIg.const_mul (G2eta α m)⁻¹),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hmono_int := intervalIntegral.integral_mono_on hx1.le hI1 hI2 hpt
  have h2I2 : 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
      ≤ ∫ z in x..1, 2 * |c z * G2 α m c z / z ^ 4| := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun z : ℝ => c z * G2 α m c z / z ^ 4) hx1.le
    have hle : (∫ z in x..1, c z * G2 α m c z / z ^ 4)
        ≤ ∫ z in x..1, |c z * G2 α m c z / z ^ 4| := le_trans (le_abs_self _) habs
    have hmul : 2 * (∫ z in x..1, |c z * G2 α m c z / z ^ 4|)
        = ∫ z in x..1, 2 * |c z * G2 α m c z / z ^ 4| := by
      rw [intervalIntegral.integral_const_mul]
    linarith
  have hA : 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
      ≤ G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) :=
    le_trans h2I2 (le_trans hmono_int (le_of_eq hlin))
  have hB : G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4) ≤ G2eta α m * G2M0 c :=
    mul_le_mul_of_nonneg_left (G2_csq_mono h0 x hx hx1) (le_of_lt hη)
  have hei := G2_energy α m hc hinf x hx hx1
  have hH2 : G2 α m c 1 ^ 2 ≤ G2H α m c ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (G2_one_le α m hinf) 2
  have hxend : 0 ≤ G2 α m c x ^ 2 / x ^ 3 := div_nonneg (sq_nonneg _) (by positivity)
  have h3 : (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      ≤ G2eta α m * G2M0 c + G2H α m c ^ 2
        + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    calc (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4)
          + G2 α m c 1 ^ 2 - G2 α m c x ^ 2 / x ^ 3 := hei
      _ ≤ 2 * (∫ z in x..1, c z * G2 α m c z / z ^ 4) + G2H α m c ^ 2 := by
          linarith [hH2, hxend]
      _ ≤ (G2eta α m * (∫ z in x..1, c z ^ 2 / z ^ 4)
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) + G2H α m c ^ 2 := by
          linarith [hA]
      _ ≤ (G2eta α m * G2M0 c
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) + G2H α m c ^ 2 := by
          linarith [hB]
      _ = G2eta α m * G2M0 c + G2H α m c ^ 2
            + (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by ring
  have heta : 2 * (2 * (m : ℝ) / α) - 3 - (G2eta α m)⁻¹ = (G2eta α m)⁻¹ := by
    rw [G2eta, inv_div]; ring
  have hcoef : (2 * (2 * (m : ℝ) / α) - 3) * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        - (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      = (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) := by
    rw [← sub_mul, heta]
  have key : (G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
      ≤ G2eta α m * G2M0 c + G2H α m c ^ 2 := by linarith [h3, hcoef]
  have hA1 : (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4) ≤ G2M α m c := by
    rw [G2M]
    calc (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)
        = G2eta α m * ((G2eta α m)⁻¹ * (∫ z in x..1, G2 α m c z ^ 2 / z ^ 4)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), one_mul]
      _ ≤ G2eta α m * (G2eta α m * G2M0 c + G2H α m c ^ 2) :=
          mul_le_mul_of_nonneg_left key (le_of_lt hη)
  have hmono' : (∫ z in x..y, G2 α m c z ^ 2 / z ^ 4)
      ≤ ∫ z in x..1, G2 α m c z ^ 2 / z ^ 4 := by
    refine intervalIntegral.integral_mono_interval (μ := volume) le_rfl hxy.le hy1.le ?_ hIg
    exact Filter.Eventually.of_forall (fun z => div_nonneg (sq_nonneg _) (by positivity))
  linarith [hA1, hmono']

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G2_far_bound =====
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


-- Far-field pointwise bound for the `z^{s⁺}` Green term `G2 α m c` (`s⁺ = 2m/α`) of
-- `Work.FTS.EllExist.Honesty.G2`, defined as
-- `G2 α m c z = z ^ (2*(m:ℝ)/α) * ∫ t in Set.Ioi z, c t * t ^ (-(2*(m:ℝ)/α) - 1)`.
-- Route: for `z ≥ 1` (so `z > 0` and every `t ∈ Ioi z` satisfies `t ≥ 1`), dominate the
-- integrand by `M * t ^ (-2*(2*(m:ℝ)/α) - 3)` with `hdec`, use `integrableOn_Ioi_rpow_of_lt`
-- (the exponent is `< -1`) plus `Integrable.mono'` for integrability, then
-- `MeasureTheory.norm_integral_le_integral_norm` and `integral_Ioi_rpow_of_lt` to get
-- `|∫| ≤ M * z ^ (-2*(2*(m:ℝ)/α) - 2) / (2*(2*(m:ℝ)/α) + 2)`, and finally
-- `Real.rpow_add` to turn `z ^ (2*(m:ℝ)/α) * z ^ (-2*(2*(m:ℝ)/α) - 2)` into
-- `z ^ (-(2*(m:ℝ)/α) - 2)`.

end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.G2_far_measurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- Measurability on the far field of the `z^{s⁺}` Green term `G2 α m c` (`s⁺ = 2m/α`):
-- `G2 α m c z = z ^ (2*(m:ℝ)/α) * ∫ t in Set.Ioi z, c t * t ^ (-(2*(m:ℝ)/α) - 1)`.
-- Route: put `g t := c t * t ^ (-(2*(m:ℝ)/α) - 1)`.  `g` is continuous on `Set.Ioi (1/2)` (as
-- `c` is, and `t ↦ t ^ q` is continuous at every `t ≠ 0`) and integrable on `Set.Ioi (1/2)`
-- (`(1/2, 1]` is compact, and on `Set.Ioi 1` the function is dominated by the integrable
-- `t ↦ M * t ^ (-2*(2*(m:ℝ)/α) - 3)` by `hdec`), so
-- `Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi` (base point `1/2`) gives that
-- `u ↦ ∫ t in Set.Ioi u, g t` is differentiable, hence continuous, on `Set.Ioi 1`; multiply by
-- the smooth `z ↦ z ^ (2*(m:ℝ)/α)` for differentiability of `G2`, then `ContinuousOn` gives
-- `MeasureTheory.AEStronglyMeasurable` (`MeasurableSet` `Set.Ioi 1`).

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.HkMem_of_majorant_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory

/-
`HkMem α k f` from a majorant `M` known to have integrable slices and an integrable
`θ`-integral, where the domination `HkIntegrand α k f ≤ M` is only required *a.e. in `θ`*
on each slice (rather than at every `θ ∈ Iθ`).

This is the a.e. form of `Work.Blocks.HkMem_of_majorant_aesm`: the same `Integrable.mono'`
argument, with the pointwise domination replaced by the a.e. one in the `θ`-integral bound
(`integral_mono_of_nonneg` accepts an a.e. hypothesis directly).  The only structural input
on `HkIntegrand` is its nonnegativity.
-/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · -- every angular slice of the integrand is integrable on `Iθ`
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [hle z hz] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono' hMz houter ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      ((hle z hz).mono fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hMslice z hz) (hle z hz)

end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.dzu_differentiableAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- `Dzu` (in `Work.FTS.EllExist.Honesty.RadGreenDzuDefs`) is the univariate operator
-- `(z ∂_z)^i` on `ℝ → ℝ`.  Claim: if `c` is `C^{n+1}` on `(0,∞)` then each `Dzu t c` with
-- `t ≤ n` is differentiable at every point of `(0,∞)`.
-- ROUTE: prove the stronger uniform statement `ContDiffOn ℝ m (Dzu t c) (Ioi 0)` whenever
-- `ContDiffOn ℝ (t+m) c (Ioi 0)`, by induction on `t`: `Dzu (t+1) c = fun z => z * deriv (Dzu t c) z`,
-- and `ContDiffOn.deriv_of_isOpen isOpen_Ioi` lowers the order by one, `contDiffOn_id` gives
-- `z ↦ z`, `ContDiffOn.mul` multiplies the two.

/-- The uniform form of the claim, in the sharp shape needed by the induction: if `c` is
`C^{m+t}` on `(0,∞)` (the order `m` being an element of `WithTop ℕ∞`, so that it can be
lowered by one at each step) then `Dzu t c = (z ∂_z)^t c` is `C^m` there.

The induction is on `t`; the step uses
`Dzu (t+1) c = fun z => z * deriv (Dzu t c) z` together with `ContDiffOn.deriv_of_isOpen`
and `ContDiffOn.mul` (`z ↦ z` is smooth on `(0,∞)`). -/
theorem contDiffOn_Dzu (c : ℝ → ℝ) (t : ℕ) (m : WithTop ℕ∞)
    (hc : ContDiffOn ℝ (m + t) c (Set.Ioi 0)) :
    ContDiffOn ℝ m (Dzu t c) (Set.Ioi 0) := by
  induction t generalizing m with
  | zero => simpa using hc
  | succ n ih =>
      have h2 : ContDiffOn ℝ (m + 1) (Dzu n c) (Set.Ioi 0) :=
        ih (m + 1) (by
          have hh : ((m + 1 : WithTop ℕ∞) + (n : WithTop ℕ∞)) = (m + ↑(Nat.succ n)) := by
            push_cast
            abel
          exact hh.symm ▸ hc)
      have h3 : ContDiffOn ℝ m (deriv (Dzu n c)) (Set.Ioi 0) :=
        h2.deriv_of_isOpen isOpen_Ioi le_rfl
      have h4 : ContDiffOn ℝ m (id : ℝ → ℝ) (Set.Ioi 0) := contDiffOn_id
      have h5 : ContDiffOn ℝ m (fun z : ℝ => z * deriv (Dzu n c) z) (Set.Ioi 0) :=
        h4.mul h3
      simpa [Dzu_succ] using h5


end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.dzu_recursion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- `Dzu` (in `Work.FTS.EllExist.Honesty.RadGreenDzuDefs`) is `(z ∂_z)^i` on `ℝ → ℝ`.
-- If `f` satisfies the first-order relation `z f'(z) = lam * f(z) + A(z)` for all `z > 0`
-- (phrased as `HasDerivAt f ((lam * f z + A z) / z) z`), then for every `i`
--   `Dzu i f z = lam^i * f z + ∑_{t<i} lam^{i-1-t} * Dzu t A z`     (`z > 0`).
-- ROUTE: induction on `i`; at the step use `Dzu (i+1) f z = z * deriv (Dzu i f) z`, rewrite
-- `deriv (Dzu i f) z` by `Filter.EventuallyEq.deriv_eq` using the induction hypothesis on a
-- neighbourhood of `z` (only `z > 0` is needed), then `deriv_sum`/`deriv_const_mul`/`deriv_add`
-- (which need `DifferentiableAt` of `f` — from the hypothesis — and of the `Dzu t A`, which is
-- exactly `hA`), and `deriv (Dzu t A) z = Dzu (t+1) A z / z` for `z ≠ 0`, which is definitional.
-- The arithmetic at the end is `Finset.sum_range_succ` + `ring`.


end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.radGreen_psiEnvelope =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Measurability of the tail integral -/



/-- `w z ^ 2 ≥ 1` for `z > 0`. -/
lemma w_sq_ge_one {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz0 : (0:ℝ) < (z ^ 2) ^ 2 := by positivity
  have hle : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
  have h2 : (z ^ 2) ^ 2 ≤ ((1 + z) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
  simp only [Work.Spaces.w]
  rw [div_pow, one_le_div hz0]
  exact h2


/-- `w` is continuous on `(0,∞)`. -/
lemma continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuous_const.continuousOn.add continuous_id.continuousOn).pow 2)
    (continuous_id.continuousOn.pow 2) (fun x hx => ?_)
  exact pow_ne_zero 2 (ne_of_gt hx)



end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollAux

open MeasureTheory

/-- `sin (2θ)` is nonnegative on `[0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- For a nonnegative base `sin (2s)`, the inverse of the weight `sin (2s)^{-99/100}` is the
weight `sin (2s)^{99/100}` of the opposite exponent. -/
private lemma inv_sin_two_rpow_neg_eq {s : ℝ} (hs : 0 ≤ Real.sin (2 * s)) :
    (((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) = (Real.sin (2 * s)) ^ (99 / 100 : ℝ) := by
  rw [Real.rpow_neg hs (99 / 100 : ℝ), inv_inv]

/-- On `[0, π/2]` the reciprocal weight `sin (2θ)^{99/100}` is bounded by `1`. -/
private lemma sigma_inv_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ((Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))⁻¹ ≤ 1 := by
  rw [inv_sin_two_rpow_neg_eq (sin_two_nonneg_of_mem_Icc hx)]
  exact Real.rpow_le_one (sin_two_nonneg_of_mem_Icc hx) (Real.sin_le_one _) (by norm_num)

/-- `θ ↦ sin (2θ)^p` is integrable on `[0, π/2]` for every `p ≥ 0` (it is bounded by `1`
there and the interval has finite measure). -/
private lemma integrableOn_sin_two_rpow_of_nonneg (p : ℝ) (hp : 0 ≤ p) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ p) (Set.Icc 0 (Real.pi / 2)) := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (s := Set.Icc (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ)) ?_) ?_ ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hθ) p)]
    exact Real.rpow_le_one (sin_two_nonneg_of_mem_Icc hθ) (Real.sin_le_one _) hp

/-- Weighted Cauchy–Schwarz (Bunyakovsky) in the form needed for the `L¹`–`L²` interpolation:
if `∫_{[0,π/2]} h² sin(2θ)^{-99/100}` is finite, then
`∫_{[0,π/2]} |h| ≤ √(π/2) · √(∫_{[0,π/2]} h² sin(2θ)^{-99/100})`.

The proof writes `|h| = √(h²σ)·√(σ⁻¹)` with `σ = sin(2θ)^{-99/100}`, applies the
Cauchy–Schwarz inequality `interval_integral_sq_le_mul`, and uses that on `[0, π/2]` the
reciprocal weight `σ⁻¹ = sin(2θ)^{99/100}` is bounded by `1`, so its integral is at most
`π/2`.  No measurability of `h` is needed: only `h²σ` appears, and the two factors are
exhibited as genuine `L²` functions. -/
theorem integralAbsLeSqrtWeighted {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in Set.Icc 0 (Real.pi / 2), |h θ|) ≤ Real.sqrt (Real.pi / 2) *
      Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
        h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- Move everything to interval integrals over `0..π/2`.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  have hσ : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    intro s hs
    exact Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])) _
  have hf : MeasureTheory.IntegrableOn
      (fun s : ℝ => |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioc 0 (Real.pi / 2)) := by
    have h := hint.mono_set Set.Ioc_subset_Icc_self
    simpa only [sq_abs] using h
  have hσi : MeasureTheory.IntegrableOn
      (fun s : ℝ => ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) (Set.Ioc 0 (Real.pi / 2)) := by
    have hb := (integrableOn_sin_two_rpow_of_nonneg (99 / 100) (by norm_num)).mono_set
      Set.Ioc_subset_Icc_self
    exact hb.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => (inv_sin_two_rpow_neg_eq (sin_two_nonneg_of_mem_Icc
        ⟨le_of_lt hs.1, hs.2⟩)).symm))
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul hab hσ hf hσi
  -- `|h|² = h²`.
  have hA1 : (∫ s in (0 : ℝ)..(Real.pi / 2),
        |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))
      = ∫ s in (0 : ℝ)..(Real.pi / 2), h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [sq_abs]
  -- The reciprocal weight contributes at most `π/2`.
  have hB' : (∫ s in (0 : ℝ)..(Real.pi / 2),
        ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) ≤ Real.pi / 2 := by
    have hint' : IntervalIntegrable
        (fun s : ℝ => ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hσi
    have hcone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
          (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
    have h := intervalIntegral.integral_mono_on hab hint' hcone (fun x hx => sigma_inv_le_one hx)
    simpa [intervalIntegral.integral_const, sub_zero] using h
  have hA1_nonneg : 0 ≤ ∫ s in (0 : ℝ)..(Real.pi / 2),
      |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hu) _)
  have hA_nonneg : 0 ≤ ∫ s in (0 : ℝ)..(Real.pi / 2),
      h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Icc hu) _)
  have hkey : (∫ s in (0 : ℝ)..(Real.pi / 2), |h s|) ^ 2 ≤
      (∫ s in (0 : ℝ)..(Real.pi / 2), h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) *
        (Real.pi / 2) := by
    calc (∫ s in (0 : ℝ)..(Real.pi / 2), |h s|) ^ 2
        ≤ (∫ s in (0 : ℝ)..(Real.pi / 2),
              |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) *
            (∫ s in (0 : ℝ)..(Real.pi / 2), ((Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)))⁻¹) := hcs
      _ ≤ (∫ s in (0 : ℝ)..(Real.pi / 2),
              |h s| ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) * (Real.pi / 2) :=
            mul_le_mul_of_nonneg_left hB' hA1_nonneg
      _ = (∫ s in (0 : ℝ)..(Real.pi / 2),
              h s ^ 2 * (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ))) * (Real.pi / 2) := by
            rw [hA1]
  have h1 := Real.le_sqrt_of_sq_le hkey
  rw [Real.sqrt_mul hA_nonneg] at h1
  simpa [mul_comm] using h1

end Work.FTS.EllSol.EllPkgAux.MollAux
end
-- ===== merged: Submission.Work.FTS.EllSol.SpecAux.timFlipIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set

/-- The time reversal `(t, θ) ↦ (-t, θ)` preserves the restricted Lebesgue measure
`(dz ⊗ dθ)|_{univ ×ˢ Iθ}`: it is the product of the (measure preserving) negation on `ℝ`
with the identity on `Iθ`, and `univ ×ˢ Iθ` is invariant under it. -/
private theorem map_timFlip_restrict (t : Set ℝ) :
    Measure.map (Prod.map Neg.neg id)
        ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t))
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t) := by
  -- `univ ×ˢ t` with the product measure is `volume ⊗ (volume|_{t})`.
  have hkey : (volume : Measure ℝ).prod (volume.restrict t)
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (univ : Set ℝ) t
    rwa [Measure.restrict_univ] at h
  -- the negation on `ℝ` and the identity on `Iθ` are measure preserving
  have hmap' : Measure.map (Prod.map Neg.neg id)
        ((volume : Measure ℝ).prod (volume.restrict t))
      = (volume : Measure ℝ).prod (volume.restrict t) := by
    have h := (MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (MeasurePreserving.id (volume.restrict t)))
    simpa using h.map_eq
  rw [← hkey]
  exact hmap'

theorem timFlipIntegral (F : ℝ × ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F (-p.1, p.2))
        ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F (-p.1, p.2))
        = ∫ p in (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := by
  -- the flip is a measurable embedding
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
    MeasurableEmbedding.prodMap (measurableEmbedding_neg)
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hmeas : Measurable (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) := hemb.measurable
  -- it preserves the restricted measure
  have hmp : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
      ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) :=
    ⟨hmeas, map_timFlip_restrict Work.Spaces.Iθ⟩
  -- the flipped function, written as a composition
  have hfun : (fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
      = fun p : ℝ × ℝ => F (-p.1, p.2) := by
    funext p
    simp [Prod.map_apply', id_eq]
  constructor
  · have h := (hmp.integrable_comp_emb hemb).mpr hF
    have h' : Integrable (fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
        (volume.restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) := h
    rw [hfun] at h'
    exact h'
  · have h := hmp.integral_comp hemb F
    have h' : (∫ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ,
          F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
        = ∫ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := h
    rw [hfun] at h'
    exact h'

end Work.FTS.EllSol.SpecAux
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.traceAux.hardySecondPow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal Interval



end Work.FTS.EllSol.VthAux.traceAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBdd.primDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux.HardyBdd


end Work.FTS.EllipticEst.AeStepOneAux.HardyBdd
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBdd.primPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux.HardyBdd

/-- The flux `hbPrim f θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` of the weighted Hardy
inequality has, at every interior point `θ ∈ (0, π/2)`, the explicit derivative `hbDeriv f θ`
(see `Submission/Work/FTS/EllipticEst/AeStepOneAux/HardyBddDefs.lean`).  Only
`ContDiffOn ℝ 1 f (Ioo 0 (π/2))` is assumed, so this also holds without any closed-interval
smoothness or integrability hypothesis. -/
theorem hbPrim_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (hbPrim f) (hbDeriv f θ) θ := by
  intro θ hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds θ := IsOpen.mem_nhds isOpen_Ioo hθ
  have hfd : DifferentiableAt ℝ f θ := (hf.differentiableOn (by norm_num)).differentiableAt hmem
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hSne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hS
  have hint : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hint
    exact h.congr_deriv (by ring)
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
    have h := (Real.hasDerivAt_cos (2 * θ)).comp θ hint
    exact h.congr_deriv (by ring)
  have hpow := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ))
    (p := -(1 + Work.Spaces.eta)) (Or.inl hSne)).comp θ hsin
  have hf2 : HasDerivAt (fun θ' : ℝ => (f θ') ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hfd.hasDerivAt.pow 2
    refine h.congr_deriv ?_
    norm_num
  have hmain := (((hasDerivAt_const θ (2 * ((1 + Work.Spaces.eta) / 2))).mul hcos).mul hf2).mul hpow
  refine hmain.congr_deriv ?_
  rw [hbDeriv, hbA]
  simp only [Pi.mul_apply, Function.comp_apply]
  ring_nf

/-- The `deriv` form of `hbPrim_hasDerivAt`. -/
theorem hbPrim_deriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (hbPrim f) θ = hbDeriv f θ :=
  fun θ hθ => (hbPrim_hasDerivAt hf θ hθ).deriv

/-- The pointwise form of the sharp weighted Hardy inequality: on the open interval,
`(1+η)² f² sin(2θ)^{-(2+η)} ≤ (f')² sin(2θ)^{-η} - (hbDeriv f) θ`, where `hbDeriv f` is the
explicit derivative of the flux `hbPrim f` (see
`Submission/Work/FTS/EllipticEst/AeStepOneAux/HardyBddDefs.lean`).  It is the completed-square
identity `Work.FTS.EllipticEst.H2W.sliceSigmaPointwise` with its two nonnegative terms
`(∂_θ(f·sin(2θ)^{-a}))² sin(2θ)^{2a-η}` and `4a(1-a)f²sin(2θ)^{-η}` (`a = (1+η)/2`, so
`2a - η = 1`) dropped.  Only `ContDiffOn ℝ 1 f (Ioo 0 (π/2))` is assumed. -/
theorem primPointwise {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (1 + Work.Spaces.eta) ^ 2 * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) - hbDeriv f θ := by
  intro θ hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds θ := IsOpen.mem_nhds isOpen_Ioo hθ
  have hfd : DifferentiableAt ℝ f θ := (hf.differentiableOn (by norm_num)).differentiableAt hmem
  have hSpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- the completed-square identity of `sliceSigmaPointwise`, with the flux derivative evaluated
  have hfluxFun : (fun θ' : ℝ => 2 * ((1 + Work.Spaces.eta) / 2) * Real.cos (2 * θ') * (f θ') ^ 2
      * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta))) = hbPrim f := rfl
  have hid := Work.FTS.EllipticEst.H2W.sliceSigmaPointwise (u := f) hθ hfd
  rw [hfluxFun, hbPrim_deriv hf θ hθ] at hid
  -- the two terms that are being dropped are nonnegative
  have hsq_nn : 0 ≤ (deriv (fun θ' : ℝ => f θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hSpos _))
  have hext_nn : 0 ≤ 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    have h1 : 0 ≤ 4 * ((1 + Work.Spaces.eta) / 2) := by linarith [Work.Spaces.eta_pos]
    have h2 : 0 ≤ 1 - (1 + Work.Spaces.eta) / 2 := by linarith [Work.Spaces.eta_lt_one]
    have hU : 0 ≤ (f θ) ^ 2 := sq_nonneg _
    have hS : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := le_of_lt (Real.rpow_pos_of_pos hSpos _)
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hU) hS
  -- solve the identity for the difference of the two terms on the left
  have hkey : (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) - hbDeriv f θ
      = (deriv (fun θ' : ℝ => f θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta)
        + 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 * (f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    linarith [hid]
  have hcoef : (1 + Work.Spaces.eta) ^ 2 = 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 := by ring
  rw [hcoef, hkey]
  linarith [hsq_nn, hext_nn]

end Work.FTS.EllipticEst.AeStepOneAux.HardyBdd
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.tendstoThetaIntervalAbsPzIter2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Filter
open scoped Topology

/-- **Fubini identity for the sliding window.**

For `0 < hh ≤ z/2` the angular integral of the sliding window equals the sliding-window
integral of the angular slice:

  `∫_θ (∫_{z-hh}^{z} |∂_z²u(x,θ)|) |sinθcos²θ| = ∫_{z-hh}^{z} ∫_θ |∂_z²u(x,θ)|·|sinθcos²θ|`.

The inner product is pulled out of the `x`-integral with the (hypothesis-free)
`intervalIntegral.integral_mul_const`, and the two iterated interval integrals are exchanged with
`MeasureTheory.intervalIntegral_integral_swap`, whose integrability hypothesis comes from `hbox`
on the larger box `[z/2,z] × Iθ` (legitimate because `0 < hh ≤ z/2` puts `[z-hh,z] ⊆ [z/2,z]`). -/
private lemma slidingWindow_swap {u : ℝ → ℝ → ℝ}
    (hbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {z hh : ℝ} (hhpos : 0 < hh) (hhz : hh ≤ z / 2) :
    (∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      = ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ| := by
  have hz2 : 0 < z / 2 := by linarith
  have hz2z : z / 2 < z := by linarith
  have hbox' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z / 2) z ×ˢ Work.Spaces.Iθ) := hbox (z / 2) z hz2 hz2z
  have hsub : Set.Ioc (z - hh) z ×ˢ Work.Spaces.Iθ ⊆ Set.Icc (z / 2) z ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun y hy => ⟨by linarith [hy.1], hy.2⟩) (fun _ h => h)
  have hint0 : MeasureTheory.Integrable
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Set.Ioc (z - hh) z ×ˢ Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono_measure hbox'
      (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have hint : MeasureTheory.Integrable
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (z - hh) z)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [Set.uIoc_of_le (by linarith : z - hh ≤ z)]
    rw [MeasureTheory.Measure.prod_restrict]
    exact hint0
  have hswap := MeasureTheory.intervalIntegral_integral_swap (a := z - hh) (b := z)
    (f := fun x θ : ℝ => |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) hint
  calc (∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      = (∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)) := by
          simp only [intervalIntegral.integral_mul_const]
    _ = ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ| := hswap.symm

/-- **The sliding-window integral of the angular slice tends to `0`.**

This is absolute continuity of the Lebesgue integral: the slice function
`x ↦ ∫_θ |∂_z²u(x,θ)|·|sinθcos²θ|` is integrable on `[z/2,z]` by `hsec`, so its primitive is
continuous on `[z/2,z]` (`intervalIntegral.continuousOn_primitive_interval_left`); evaluating at the
right endpoint `z` gives `0`, and `hh ↦ z - hh` lands in `[z/2,z]` for `hh ∈ (0,z/2)`. -/
private lemma slidingWindow_tendsto {u : ℝ → ℝ → ℝ}
    (hsec : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (Set.Icc a b))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun hh : ℝ => ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hz2 : 0 < z / 2 := by linarith
  have hz2z : z / 2 < z := by linarith
  have hFint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) :=
    hsec (z / 2) z hz2 hz2z
  have hcont' : ContinuousOn (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.uIcc (z / 2) z) := by
    refine intervalIntegral.continuousOn_primitive_interval_left (a := z / 2) (b := z) ?_
    rwa [Set.uIcc_of_le hz2z.le]
  have hcont : ContinuousOn (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) := by
    rwa [Set.uIcc_of_le hz2z.le] at hcont'
  have hz_mem : z ∈ Set.Icc (z / 2) z := ⟨hz2z.le, le_refl z⟩
  have hcw : ContinuousWithinAt (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) z :=
    hcont z hz_mem
  have hzn : (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) z = 0 := by
    simp [intervalIntegral.integral_same]
  have hmem : ∀ᶠ hh in nhdsWithin (0 : ℝ) (Set.Ioi 0), z - hh ∈ Set.Icc (z / 2) z := by
    have hI : Set.Ioo (0 : ℝ) (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio (z / 2), isOpen_Iio, hz2, fun x hx => ⟨hx.2, hx.1⟩⟩
    filter_upwards [hI] with hh hhh using ⟨by linarith [hhh.2], by linarith [hhh.1]⟩
  have htend : Filter.Tendsto (fun hh : ℝ => z - hh) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin z (Set.Icc (z / 2) z)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hmem⟩
    have h1 : Filter.Tendsto (fun hh : ℝ => z - hh) (𝓝 (0 : ℝ)) (𝓝 (z - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    have h2 : Filter.Tendsto (fun hh : ℝ => z - hh) (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa using h1
    exact Filter.Tendsto.mono_left h2 inf_le_left
  have hfin := Filter.Tendsto.comp hcw htend
  rw [hzn] at hfin
  simpa [Function.comp_def] using hfin

theorem tendstoThetaIntervalAbsPzIter2 {u : ℝ → ℝ → ℝ}
    (hbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsec : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (Set.Icc a b))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun hh : ℝ => ∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hkey := slidingWindow_tendsto hsec hz
  have heq : (fun hh : ℝ => ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun hh : ℝ => ∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|) := by
    have hz2 : 0 < z / 2 := by linarith
    have hI : Set.Ioo (0 : ℝ) (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio (z / 2), isOpen_Iio, hz2, fun x hx => ⟨hx.2, hx.1⟩⟩
    filter_upwards [hI] with hh hhh
    exact (slidingWindow_swap hbox hhh.1 hhh.2.le).symm
  exact Filter.Tendsto.congr' heq hkey

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeakFts.amgmG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeakFts

/-- The two-variable weighted AM–GM inequality: `|A·B| ≤ (t/2)A² + (1/(2t))B²` for `t > 0`.
It is `2uv ≤ t u² + v²/t` with `u = |A|`, `v = |B|`, read off the square `(t u - v)² ≥ 0`. -/
lemma amgm_abs_mul (t A B : ℝ) (ht : 0 < t) :
    |A * B| ≤ t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hmain : 2 * |A| * |B| ≤ t * A ^ 2 + B ^ 2 / t := by
    have h2 : 2 * |A| * |B| * t ≤ t ^ 2 * A ^ 2 + B ^ 2 := by
      have h := two_mul_le_add_sq (t * |A|) |B|
      have hA : |A| * |A| = A * A := by rw [← pow_two, sq_abs, pow_two]
      have hB : |B| * |B| = B * B := by rw [← pow_two, sq_abs, pow_two]
      nlinarith [h, hA, hB]
    have h3 : (t ^ 2 * A ^ 2 + B ^ 2) / t = t * A ^ 2 + B ^ 2 / t := by field_simp
    rw [← h3]
    exact (le_div_iff₀ ht).mpr h2
  calc |A * B| = |A| * |B| := abs_mul A B
    _ ≤ t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2 := by
        have key : 2 * (t / 2 * A ^ 2 + 1 / (2 * t) * B ^ 2) = t * A ^ 2 + B ^ 2 / t := by
          field_simp
        linarith [hmain, key]

/-- The pointwise weighted AM–GM bound, in the raw variables
`s = sin(2θ)`, `c = cos(2θ)`, `x = f θ`, `y = f' θ`:

  `|y x c s^{-(1+η)}| ≤ ((1+η)/2) x² c² s^{-(2+η)} + (1/(2(1+η))) y² s^{-η}`

for `η ≥ 0` and `s ≥ 0`.  The square roots of the two summands are
`u = |x c| s^{-(1+η/2)}` and `v = |y| s^{-η/2}`. -/
lemma amgmG_aux (η s x y c : ℝ) (hη : 0 ≤ η) (hs : 0 ≤ s) :
    |y * x * c * s ^ (-(1 + η))|
      ≤ ((1 + η) / 2) * (x ^ 2 * c ^ 2 * s ^ (-(2 + η)))
        + (1 / (2 * (1 + η))) * (y ^ 2 * s ^ (-η)) := by
  have ht : 0 < 1 + η := by linarith
  set A := |x| * |c| * s ^ (-(1 + η / 2)) with hA
  set B := |y| * s ^ (-(η / 2)) with hB
  have hAn : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.rpow_nonneg hs _)
  have hBn : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs _)
  have hsa : |s ^ (-(1 + η / 2))| = s ^ (-(1 + η / 2)) := abs_of_nonneg (Real.rpow_nonneg hs _)
  have hsb : |s ^ (-(η / 2))| = s ^ (-(η / 2)) := abs_of_nonneg (Real.rpow_nonneg hs _)
  have hsum1 : s ^ (-(1 + η / 2) + -(η / 2)) = s ^ (-(1 + η / 2)) * s ^ (-(η / 2)) :=
    Real.rpow_add' hs (by linarith)
  have hG : |y * x * c * s ^ (-(1 + η))| = A * B := by
    have harg : -(1 + η) = -(1 + η / 2) + -(η / 2) := by ring
    rw [harg, hsum1, hA, hB]
    simp only [abs_mul, hsa, hsb]
    ring
  have hq : (s ^ (-(1 + η / 2))) ^ (2 : ℕ) = s ^ (-(2 + η)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hA2 : A ^ 2 = x ^ 2 * c ^ 2 * s ^ (-(2 + η)) := by
    rw [hA, mul_pow, mul_pow, hq, sq_abs, sq_abs]
  have hq2 : (s ^ (-(η / 2))) ^ (2 : ℕ) = s ^ (-η) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  have hB2 : B ^ 2 = y ^ 2 * s ^ (-η) := by
    rw [hB, mul_pow, hq2, sq_abs]
  have hAB := amgm_abs_mul (1 + η) A B ht
  calc |y * x * c * s ^ (-(1 + η))| = A * B := hG
    _ = |A * B| := (abs_of_nonneg (mul_nonneg hAn hBn)).symm
    _ ≤ (1 + η) / 2 * A ^ 2 + 1 / (2 * (1 + η)) * B ^ 2 := hAB
    _ = ((1 + η) / 2) * (x ^ 2 * c ^ 2 * s ^ (-(2 + η)))
          + (1 / (2 * (1 + η))) * (y ^ 2 * s ^ (-η)) := by rw [hA2, hB2]

theorem amgmG (η : ℝ) (hη0 : 0 ≤ η) (f : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f θ|
        ≤ ((1 + η) / 2) * Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * Work.FTS.EllipticEst.AngAWeak.hardyFtsD η f θ := by
  intro θ hθ
  unfold Work.FTS.EllipticEst.AngAWeak.hardyFtsG Work.FTS.EllipticEst.AngAWeak.hardyFtsL
    Work.FTS.EllipticEst.AngAWeak.hardyFtsD
  exact amgmG_aux η (Real.sin (2 * θ)) (f θ) (deriv f θ) (Real.cos (2 * θ))
    hη0 (Work.FTS.EllipticEst.AngAWeak.hardyFts_sin_nonneg hθ)

end Work.FTS.EllipticEst.AngAWeakFts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxDeriv =====
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

/-- The flux `Φ` has derivative `2G - 2B - 2(1+η)L` on the open angular interval. -/
theorem fluxDeriv (η : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (2 * Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f θ
          - 2 * Work.FTS.EllipticEst.AngAWeak.hardyFtsB η f θ
          - 2 * (1 + η) * Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f θ) θ := by
  intro θ hθ
  have hsin : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  -- `f` is differentiable at the interior point `θ`
  have hf_diff : DifferentiableAt ℝ f θ :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
  have hfd : HasDerivAt f (deriv f θ) θ := hf_diff.hasDerivAt
  -- the two trigonometric chains
  have hsin2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hcos2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-2 * Real.sin (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm, mul_neg] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  -- the three factors of the flux and their derivatives
  have hA := hfd.pow 2
  have hC : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) ^ (-(1 + η)))
      ((2 * Real.cos (2 * θ)) * (-(1 + η)) * Real.sin (2 * θ) ^ (-(1 + η) - 1)) θ :=
    hsin2.rpow_const (Or.inl hsin.ne')
  have hD := (hA.mul hcos2).mul hC
  -- the two `rpow` rewrites identifying the terms of the target
  have hsub : Real.sin (2 * θ) ^ (-η) = Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := by
    rw [show (-η : ℝ) = 1 + (-(1 + η)) by ring, Real.rpow_add hsin, Real.rpow_one]
  have hsub2 : Real.sin (2 * θ) ^ (-(2 + η)) = Real.sin (2 * θ) ^ (-(1 + η) - 1) := by
    rw [show (-(2 + η) : ℝ) = -(1 + η) - 1 by ring]
  refine hD.congr_deriv ?_
  unfold hardyFtsG hardyFtsB hardyFtsL
  rw [hsub, hsub2]
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

end Work.FTS.EllipticEst.AngAWeakFts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxTendsto =====
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

/-! ## The two elementary endpoint limits -/

/-- `θ ↦ sin(2θ)^p → 0` as `θ → 0⁺`, for `p > 0`.  The proof composes the two facts that
`sin(2θ) → 0` through *positive* values and that `x ↦ x^p` is continuous at `0` with value
`0`. -/
theorem tendsto_sin_two_rpow_zero_right (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h2 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 (0 : ℝ)) (𝓝 (2 * (0 : ℝ))) :=
        tendsto_const_nhds.mul tendsto_id
      have h3 : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
          (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
        Real.continuous_sin.continuousAt.tendsto.comp h2
      simpa using h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hr : Tendsto (fun x : ℝ => x ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ p) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ p)) :=
      (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow (ne_of_gt hp)] using h
  exact hr.comp hsin

/-- `θ ↦ sin(2θ)^p → 0` as `θ → (π/2)⁻`, for `p > 0`, by transport along `θ ↦ π/2 - θ`
and `sin(π - x) = sin x`. -/
theorem tendsto_sin_two_rpow_zero_left (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hcomp : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝[<] (Real.pi / 2))
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
      simpa using h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0 : ℝ) < Real.pi / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  refine ((tendsto_sin_two_rpow_zero_right p hp).comp hcomp).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ _
  simp only [Function.comp_apply]
  rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-! ## The pointwise bound -/

/-- The pointwise estimate behind the flux vanishing: `|Φ θ| ≤ M² sin(2θ)^{1-η}` on the open
angular interval.  Only `|f θ| ≤ M sin(2θ)` and `|cos| ≤ 1` are used, together with the `rpow`
addition rule `sin(2θ)² · sin(2θ)^{-(1+η)} = sin(2θ)^{1-η}`. -/
theorem hardyFtsFlux_abs_le {η M : ℝ} (_hM : 0 ≤ M) {f : ℝ → ℝ}
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |hardyFtsFlux η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (1 - η) := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  have hspos : 0 ≤ Real.sin (2 * θ) := hs.le
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hf : |f θ| ≤ M * Real.sin (2 * θ) := hMf θ hθ
  have hf2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hf 2
    rwa [sq_abs] at h
  have hrpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + η)) := Real.rpow_nonneg hspos _
  have hkey : (Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(1 + η))
      = (Real.sin (2 * θ)) ^ (1 - η) := by
    rw [← Real.rpow_add hs, show (2 : ℝ) + (-(1 + η)) = 1 - η by ring]
  calc |hardyFtsFlux η f θ|
      = (f θ) ^ 2 * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η)) := by
        rw [hardyFtsFlux, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
          abs_of_nonneg hrpow_nn]
    _ ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hf2 hcos (abs_nonneg _) (sq_nonneg _)) hrpow_nn
    _ = M ^ 2 * ((Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(1 + η))) := by
        rw [mul_pow, Real.rpow_two]; ring
    _ = M ^ 2 * (Real.sin (2 * θ)) ^ (1 - η) := by rw [hkey]

/-- The flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` tends to `0` at `0⁺` and at `(π/2)⁻`,
for `η < 1` and `|f θ| ≤ M sin(2θ)` on the open angular interval. -/
theorem fluxTendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp : 0 < 1 - η := by linarith
  have hhalf : (0 : ℝ) < Real.pi / 2 := by positivity
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun t => M ^ 2 * (Real.sin (2 * t)) ^ (1 - η))
      (Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hhalf] with θ hθ
      rw [Real.norm_eq_abs]
      exact hardyFtsFlux_abs_le hM hMf θ hθ
    · simpa using ((tendsto_sin_two_rpow_zero_right (1 - η) hp).const_mul (M ^ 2))
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun t => M ^ 2 * (Real.sin (2 * t)) ^ (1 - η))
      (Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hhalf] with θ hθ
      rw [Real.norm_eq_abs]
      exact hardyFtsFlux_abs_le hM hMf θ hθ
    · simpa using ((tendsto_sin_two_rpow_zero_left (1 - η) hp).const_mul (M ^ 2))

end Work.FTS.EllipticEst.AngAWeakFts

end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.HardySetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

/-- The "completed square" term `(h θ - 6 cot(2θ) V θ)²`, where `V = angV h`. -/
def angFt (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2

/-- The integrand of the weighted Hardy identity:
`angF h θ = (h θ)² - 12 (V θ)² - (h θ - 6 cot(2θ) V θ)²`, i.e. the function whose
derivative on `(0, π/2)` is `angPhiH h = 6 V² cot 2θ`. -/
def angF (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (h θ) ^ 2 - 12 * (angV h θ) ^ 2 - angFt h θ


/-- `angF` split as the difference of `h² - 12 V²` and `angFt`. -/
theorem angF_eq_sub (h : ℝ → ℝ) (θ : ℝ) :
    angF h θ = ((h θ) ^ 2 - 12 * (angV h θ) ^ 2) - angFt h θ := rfl

theorem angFt_nonneg (h : ℝ → ℝ) (θ : ℝ) : 0 ≤ angFt h θ := sq_nonneg _

end Work.FTS.EllipticEst.AngGap
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.angPhiC_tendsto_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- `angPhiC h = V · h = (G / sin 2θ) · h` tends to `0` at the two endpoints of `(0, π/2)`.

The bounds `hbdd : |h θ| ≤ C sin 2θ` and `hCg : |G θ| ≤ C sin³2θ` give, on the open
interval where `sin 2θ > 0`,

`|angPhiC h θ| = |G θ| / sin 2θ · |h θ| ≤ (C sin³2θ)/sin 2θ · (C sin 2θ) = C² sin³2θ`,

and `sin (2θ) → 0` at `θ = 0` and at `θ = π/2`, so the squeeze lemma `squeeze_zero_norm'`
finishes both limits.  This is the endpoint-limit component of the integration-by-parts
identity `∫ h² = -∫ V Q` in the angular gap-Wirtinger development. -/
theorem angPhiC_tendsto_zero (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiC h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (Work.FTS.EllipticEst.AngGap.angPhiC h)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- ## the pointwise bound on the open interval
  have hphi_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖angPhiC h θ‖ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hg := hCg θ (hsub hθ)
    have hh := hbdd θ (hsub hθ)
    have habs : |angPhiC h θ| = |angG h θ| / Real.sin (2 * θ) * |h θ| := by
      rw [show angPhiC h θ = (angG h θ / Real.sin (2 * θ)) * h θ from rfl]
      rw [abs_mul, abs_div, abs_of_pos hs]
    rw [Real.norm_eq_abs, habs]
    calc |angG h θ| / Real.sin (2 * θ) * |h θ|
        ≤ (C * (Real.sin (2 * θ)) ^ 3) / Real.sin (2 * θ) * (C * Real.sin (2 * θ)) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hg hs.le
          · exact hh
          · exact abs_nonneg _
          · positivity
      _ = C ^ 2 * (Real.sin (2 * θ)) ^ 3 := by
          field_simp
  -- ## the two comparison sequences `C² sin³2θ → 0`
  have hsin0 : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
          (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using (h1'.pow 3).const_mul (C ^ 2)
  have hsinpi : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ 3)
      (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (π / 2))
          (𝓝 (Real.sin (2 * (π / 2)))) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
      rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi]] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using (h1'.pow 3).const_mul (C ^ 2)
  -- ## the two squeezed limits
  constructor
  · refine squeeze_zero_norm' ?_ hsin0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hphi_le θ hθ
  · refine squeeze_zero_norm' ?_ hsinpi
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hphi_le θ hθ

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.angQ_cont_bound_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

theorem angQ_cont_bound_Ioo (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) :
    ContinuousOn (Work.FTS.EllipticEst.AngGap.angQ h) (Set.Ioo 0 (π / 2)) ∧
    ∀ θ ∈ Set.Ioo 0 (π / 2), |Work.FTS.EllipticEst.AngGap.angQ h θ| ≤ 3 * C := by
  constructor
  · -- ## Continuity of `Q = h' - 2 cot(2θ) h` on `(0, π/2)`
    have hIoo : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) := Set.Ioo_subset_Icc_self
    have hdcont : ContinuousOn (deriv h) (Set.Ioo 0 (π / 2)) :=
      (hh.mono hIoo).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hhcont : ContinuousOn h (Set.Ioo 0 (π / 2)) := (hh.mono hIoo).continuousOn
    have hcotcont : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (π / 2)) := by
      have hfun : (fun θ : ℝ => Real.cot (2 * θ))
          = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
        funext θ; rw [Real.cot_eq_cos_div_sin]
      rw [hfun]
      exact (by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ))
          (Set.Ioo 0 (π / 2))).div (by fun_prop)
        (fun θ hθ => ne_of_gt (sin_two_pos hθ))
    exact hdcont.sub ((hcotcont.const_mul 2).mul hhcont)
  · -- ## The pointwise bound `|Q θ| ≤ 3 C`
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hcot := abs_cot_two_le hθ
    have hb := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
    have hd := hbdd' θ hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      have habs : |2 * Real.cot (2 * θ) * h θ| = 2 * (|Real.cot (2 * θ)| * |h θ|) := by
        rw [show 2 * Real.cot (2 * θ) * h θ = 2 * (Real.cot (2 * θ) * h θ) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      rw [habs]
      have hmul : |Real.cot (2 * θ)| * |h θ|
          ≤ (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
        mul_le_mul hcot hb (abs_nonneg _) (by positivity)
      have h3 : (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) = C := by field_simp
      linarith [hmul.trans_eq h3]
    have hsplit : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      have := abs_add_le (deriv h θ) (-(2 * Real.cot (2 * θ) * h θ))
      simpa only [sub_eq_add_neg, abs_neg] using this
    rw [angQ]
    linarith

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.angV_cont_bound_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst.AngGap

theorem angV_cont_bound_Ioo (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ContinuousOn (Work.FTS.EllipticEst.AngGap.angV h) (Set.Ioo 0 (π / 2)) ∧
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.EllipticEst.AngGap.angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  constructor
  · -- `angG h` is differentiable (hence continuous) on the open interval, `sin (2·)` too,
    -- and the denominator does not vanish there.
    have hcontSin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hcontG : ContinuousOn (angG h) (Set.Ioo 0 (π / 2)) :=
      fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
    have hq := hcontG.div hcontSin (fun θ hθ => ne_of_gt (sin_two_pos hθ))
    have hfun : (angG h / fun θ : ℝ => Real.sin (2 * θ)) = angV h := by
      funext θ; simp only [Pi.div_apply, angV]
    rwa [hfun] at hq
  · intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
    have h1 := div_le_div_of_nonneg_right (hCg θ (Set.Ioo_subset_Icc_self hθ)) hs.le
    have h2 : C * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ) = C * (Real.sin (2 * θ)) ^ 2 := by
      field_simp
    rw [angV, abs_div, abs_of_pos hs]
    linarith [h1, h2]

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

/-- The open interval `(0,π/2)` and `Iθ` carry the same restricted Lebesgue measure, since
they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- On the open interval, `sin (2θ) ≠ 0`. -/
theorem sin_two_ne_zero_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- **Elementary arithmetic core.**  Given `A² ≤ W·Z`, `12W ≤ A`, `Z = B - 4A`, all of
`A, B, Z` nonnegative, one has `16 A ≤ B` (the case `A = 0` is trivial; otherwise
`A ≤ Z/12` and `Z = B - 4A`). -/
theorem arith_core {A B W Z : ℝ} (hAnn : 0 ≤ A) (hZnn : 0 ≤ Z) (hBnn : 0 ≤ B)
    (hcs : A ^ 2 ≤ W * Z) (hH : 12 * W ≤ A) (hZeq : Z = B - 4 * A) : 16 * A ≤ B := by
  have hWZ : W * Z ≤ (A / 12) * Z := mul_le_mul_of_nonneg_right (by linarith) hZnn
  have hkey : A ^ 2 ≤ (A / 12) * Z := le_trans hcs hWZ
  rcases eq_or_lt_of_le hAnn with h | h
  · rw [← h]; nlinarith [hBnn]
  · have h12 : 12 * A ≤ Z := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hkey, h, hcon]
    linarith

/-- **Assembly.**  If `h` satisfies the bounds and if the three analytic identities hold,
then the gap-Wirtinger inequality follows. -/
theorem assembly (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C)
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
    (Cg : ℝ) (hCgpos : 0 < Cg) (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |angG h θ| ≤ Cg * (Real.sin (2 * θ)) ^ 3)
    (hD : (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2))
    (hH : 12 * (∫ θ in Work.Spaces.Iθ, (angV h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
    (hI : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
        = - (∫ θ in Work.Spaces.Iθ, angV h θ * (deriv h θ - 2 * Real.cot (2 * θ) * h θ))) :
    16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Real.isFiniteMeasure_restrict_Icc 0 (π / 2)
  set Q : ℝ → ℝ := fun θ => deriv h θ - 2 * Real.cot (2 * θ) * h θ with hQdef
  set V : ℝ → ℝ := fun θ => angV h θ with hVdef
  -- ## Continuity on the open interval
  have hScont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) := by fun_prop
  have hSne : ∀ θ ∈ Set.Ioo 0 (π / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => sin_two_ne_zero_of_mem hθ
  have hGcont : ContinuousOn (angG h) (Set.Ioo 0 (π / 2)) :=
    fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
  have hVcont : ContinuousOn V (Set.Ioo 0 (π / 2)) := by
    rw [hVdef]
    exact hGcont.div hScont hSne
  have hdcont : ContinuousOn (deriv h) (Set.Ioo 0 (π / 2)) :=
    (hh.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcotcont : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo 0 (π / 2)) := by
    have hfun : (fun θ : ℝ => Real.cot (2 * θ))
        = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
      funext θ; rw [Real.cot_eq_cos_div_sin]
    rw [hfun]
    exact (by fun_prop : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2))).div
      (by fun_prop) hSne
  have hhcont : ContinuousOn h (Set.Ioo 0 (π / 2)) :=
    (hh.mono Set.Ioo_subset_Icc_self).continuousOn
  have hQcont : ContinuousOn Q (Set.Ioo 0 (π / 2)) := by
    rw [hQdef]
    have h2c : ContinuousOn (fun θ : ℝ => 2 * Real.cot (2 * θ) * h θ) (Set.Ioo 0 (π / 2)) :=
      (hcotcont.const_mul 2).mul hhcont
    exact hdcont.sub (by simpa only [mul_assoc] using h2c)
  -- ## A.e. strong measurability on `Iθ`
  have hVmeas : AEStronglyMeasurable V (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hVcont.aestronglyMeasurable measurableSet_Ioo
  have hQmeas : AEStronglyMeasurable Q (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hQcont.aestronglyMeasurable measurableSet_Ioo
  -- ## A.e. bounds on `Iθ`
  have hVbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |V θ| ≤ Cg := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hspos
    have hsin1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
      pow_le_one₀ hsnn (Real.sin_le_one (2 * θ))
    have hG := hCg θ ⟨hθ.1.le, hθ.2.le⟩
    simp only [hVdef, angV]
    rw [abs_div, abs_of_pos hspos]
    have h1 : |angG h θ| / Real.sin (2 * θ)
        ≤ Cg * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ) :=
      div_le_div_of_nonneg_right hG hspos.le
    have h2 : Cg * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ)
        = Cg * (Real.sin (2 * θ)) ^ 2 := by
      field_simp
    have h3 : Cg * (Real.sin (2 * θ)) ^ 2 ≤ Cg := by nlinarith [hCgpos, hsin1]
    linarith
  have hQbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |Q θ| ≤ 3 * C := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hcot := abs_cot_two_le hθ
    have hhθ := hbdd θ ⟨hθ.1.le, hθ.2.le⟩
    have hd := hbdd' θ hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      have habs : |2 * Real.cot (2 * θ) * h θ| = 2 * (|Real.cot (2 * θ)| * |h θ|) := by
        rw [show 2 * Real.cot (2 * θ) * h θ = 2 * (Real.cot (2 * θ) * h θ) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      rw [habs]
      have hmul : |Real.cot (2 * θ)| * |h θ|
          ≤ (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
        mul_le_mul hcot hhθ (abs_nonneg _) (by positivity)
      have h3 : (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) = C := by field_simp
      linarith [hmul.trans_eq h3]
    have hsplit : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      have := abs_add_le (deriv h θ) (-(2 * Real.cot (2 * θ) * h θ))
      simpa only [sub_eq_add_neg, abs_neg] using this
    simp only [hQdef]
    linarith
  -- ## `MemLp`
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound hVmeas Cg (by
      filter_upwards [hVbdd] with θ hθ
      simpa only [Real.norm_eq_abs] using hθ)
  have hQmem : MemLp Q 2 (volume.restrict Work.Spaces.Iθ) :=
    MemLp.of_bound hQmeas (3 * C) (by
      filter_upwards [hQbdd] with θ hθ
      simpa only [Real.norm_eq_abs] using hθ)
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral hVmem hQmem
  have hsgn : (∫ θ in Work.Spaces.Iθ, V θ * Q θ)
      = - (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
    rw [hVdef, hQdef]
    linarith [hI]
  have hcs' : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2) := by
    rw [hsgn, neg_sq] at hcs
    exact hcs
  -- ## Arithmetic
  have hAnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hZnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2 := integral_nonneg (fun θ => sq_nonneg _)
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hZeq : (∫ θ in Work.Spaces.Iθ, (Q θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
    rw [hQdef]; exact hD
  have hWle : 12 * (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
    rw [hVdef]; exact hH
  exact arith_core hAnn hZnn hBnn hcs' hWle hZeq

end Work.FTS.EllipticEst.AngGap
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.hBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- On `[0, π/2]` we have `min θ (π/2 - θ) ≤ (π/4) * sin (2θ)`.

This is Jordan's inequality on the two halves of the interval: on the left half
`sin (2θ) ≥ (2/π)(2θ)`, on the right half `sin (2θ) = sin (2(π/2 - θ)) ≥ (2/π)(2(π/2 - θ))`. -/
theorem min_le_quarter_pi_mul_sin_two {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    min θ (π / 2 - θ) ≤ π / 4 * Real.sin (2 * θ) := by
  rcases le_or_gt θ (π / 4) with hl | hr
  · have hmin : min θ (π / 2 - θ) = θ := by
      apply min_eq_left
      linarith [Real.pi_pos]
    rw [hmin]
    have hj := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1]) (by linarith)
    calc θ = π / 4 * (2 / π * (2 * θ)) := by field_simp; ring
      _ ≤ π / 4 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hj (by positivity)
  · have hmin : min θ (π / 2 - θ) = π / 2 - θ := by
      apply min_eq_right
      linarith [Real.pi_pos]
    rw [hmin]
    have hj := Real.mul_le_sin (x := 2 * (π / 2 - θ)) (by linarith [hθ.2]) (by linarith)
    have hsin : Real.sin (2 * (π / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin] at hj
    calc π / 2 - θ = π / 4 * (2 / π * (2 * (π / 2 - θ))) := by field_simp; ring
      _ ≤ π / 4 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hj (by positivity)

theorem hBounds (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) := by
  have hpi : 0 < π / 2 := by positivity
  have hIu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpi
  have hcderiv : ContinuousOn (derivWithin h (Set.Icc (0 : ℝ) (π / 2))) (Set.Icc (0 : ℝ) (π / 2)) :=
    hh.continuousOn_derivWithin hIu (by norm_num)
  -- a uniform bound `C₀` for the derivative
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcderiv
  have hC0nn : 0 ≤ C0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_rfl, hpi.le⟩
    have h := hC0 0 hmem
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hderiv_eq : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv h x = derivWithin h (Set.Icc (0 : ℝ) (π / 2)) x :=
    fun x hx => (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm
  have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv h x| ≤ C0 := by
    intro x hx
    rw [hderiv_eq x hx]
    simpa [Real.norm_eq_abs] using hC0 x ⟨hx.1.le, hx.2.le⟩
  -- the mean value inequality on the convex interval
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (π / 2)) := convex_Icc _ _
  have hdiff : DifferentiableOn ℝ h (Set.Icc (0 : ℝ) (π / 2)) := hh.differentiableOn (by norm_num)
  have hnorm : ∀ c : ℝ, ‖ContinuousLinearMap.toSpanSingleton ℝ c‖ = |c| := by
    intro c
    have h := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).norm_map c
    simpa [Real.norm_eq_abs] using h
  have hfdb : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖fderivWithin ℝ h (Set.Icc (0 : ℝ) (π / 2)) x‖ ≤ C0 := by
    intro x hx
    rw [← toSpanSingleton_derivWithin, hnorm]
    simpa [Real.norm_eq_abs] using hC0 x hx
  have hmvt : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), ∀ y ∈ Set.Icc (0 : ℝ) (π / 2),
      ‖h y - h x‖ ≤ C0 * ‖y - x‖ :=
    fun x hx y hy => Convex.norm_image_sub_le_of_norm_fderivWithin_le hdiff hfdb hconv hx hy
  have hmain : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |h θ| ≤ C0 * min θ (π / 2 - θ) := by
    intro θ hθ
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_rfl, hpi.le⟩
    have hpimem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hpi.le, le_rfl⟩
    have hl := hmvt 0 h0mem θ hθ
    have hr := hmvt (π / 2) hpimem θ hθ
    have hl' : |h θ| ≤ C0 * θ := by
      simpa [Real.norm_eq_abs, h0, abs_of_nonneg hθ.1] using hl
    have hr' : |h θ| ≤ C0 * (π / 2 - θ) := by
      have h2 : |θ - π / 2| = π / 2 - θ := by
        rw [abs_of_nonpos (by linarith [hθ.2])]; ring
      simpa [Real.norm_eq_abs, h1, h2] using hr
    rw [mul_min_of_nonneg θ (π / 2 - θ) hC0nn]
    exact le_min hl' hr'
  have hθb : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), |h θ| ≤ C0 * Real.sin (2 * θ) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    calc |h θ| ≤ C0 * min θ (π / 2 - θ) := hmain θ hθ
      _ ≤ C0 * (π / 4 * Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (min_le_quarter_pi_mul_sin_two hθ) hC0nn
      _ ≤ C0 * Real.sin (2 * θ) := by
          apply mul_le_mul_of_nonneg_left _ hC0nn
          exact mul_le_of_le_one_left hsin (by linarith [Real.pi_lt_four])
  refine ⟨max C0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_⟩
  · intro θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    calc |h θ| ≤ C0 * Real.sin (2 * θ) := hθb θ hθ
      _ ≤ max C0 1 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hsin
  · intro θ hθ
    exact le_trans (hbound θ hθ) (le_max_left _ _)

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.stepD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

/-- Hints: the integrand `F θ = (deriv h θ - 2 cot(2θ) h θ)² - (deriv h θ)² + 4 (h θ)²`
is the derivative on `(0,π/2)` of `angPhiD h θ = -2 (h θ)² cot(2θ)` (product rule with
`hasDerivAt_cot_two` from `Defs.lean`, then `ring`).  `angPhiD h` tends to `0` at both
endpoints by `squeeze_zero'`: `|angPhiD h θ| ≤ 2 C² sin(2θ)` using `hbdd` and
`abs_cot_two_le`.  `F` is continuous on `Ioo 0 (π/2)` and bounded there by `hbdd`,`hbdd'`,
so `IntervalIntegrable F volume 0 (π/2)` (`Integrable.of_bound` on `Ioo`, moved to `uIcc` by
`MeasureTheory.Ioo_ae_eq_Icc`).  Then
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` gives `∫ F = 0` over `0..π/2`;
transfer to the set integral over `Iθ` with `MeasureTheory.integral_Icc_eq_integral_Ioc` and
`intervalIntegral.integral_of_le`, and split with `integral_add`/`integral_sub`. -/
theorem stepD (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hbdd' : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ C) :
    (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) - 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- ## continuity of the ingredients on the open interval
  have hcontH : ContinuousOn h (Set.Ioo (0 : ℝ) (π / 2)) := (hh.mono hsub).continuousOn
  have hcontD : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hh.mono hsub).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontCot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) := by
    have hfun : (fun θ : ℝ => Real.cot (2 * θ))
        = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
      funext θ; rw [Real.cot_eq_cos_div_sin]
    rw [hfun]
    exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).div
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
      (fun θ hθ => ne_of_gt (sin_two_pos hθ))
  -- ## elementary pointwise bounds
  have hhbd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |h θ| ≤ C := by
    intro θ hθ
    have h1' := hbdd θ (hsub hθ)
    have h2' : C * Real.sin (2 * θ) ≤ C :=
      mul_le_of_le_one_right (le_of_lt hC) (Real.sin_le_one (2 * θ))
    linarith
  have hderiv_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ≤ 3 * C := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hcot := abs_cot_two_le hθ
    have h2 : |2 * Real.cot (2 * θ) * h θ| ≤ 2 * C := by
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      calc 2 * |Real.cot (2 * θ)| * |h θ|
          ≤ 2 * (1 / Real.sin (2 * θ)) * (C * Real.sin (2 * θ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hcot (by norm_num))
              (hbdd θ (hsub hθ)) (by positivity) (by positivity)
        _ = 2 * C := by
            have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
            field_simp
    have htri : |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [le_abs_self (deriv h θ),
                neg_abs_le (2 * Real.cot (2 * θ) * h θ)],
             by linarith [neg_abs_le (deriv h θ),
                le_abs_self (2 * Real.cot (2 * θ) * h θ)]⟩
    calc |deriv h θ - 2 * Real.cot (2 * θ) * h θ|
        ≤ |deriv h θ| + |2 * Real.cot (2 * θ) * h θ| := htri
      _ ≤ C + 2 * C := add_le_add (hbdd' θ hθ) h2
      _ = 3 * C := by ring
  -- ## squared bounds
  have hAsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 ≤ 9 * C ^ 2 := by
    intro θ hθ
    calc (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2
        = |deriv h θ - 2 * Real.cot (2 * θ) * h θ| ^ 2 := (sq_abs _).symm
      _ ≤ (3 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hderiv_le θ hθ) 2
      _ = 9 * C ^ 2 := by ring
  have hBsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), (deriv h θ) ^ 2 ≤ C ^ 2 := by
    intro θ hθ
    calc (deriv h θ) ^ 2 = |deriv h θ| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbdd' θ hθ) 2
  have hCsq : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 4 * (h θ) ^ 2 ≤ 4 * C ^ 2 := by
    intro θ hθ
    have h2 : (h θ) ^ 2 ≤ C ^ 2 := by
      calc (h θ) ^ 2 = |h θ| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hhbd θ hθ) 2
    linarith
  -- ## the pointwise bound for the integrand `F`
  have hboundF : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2‖
        ≤ 14 * C ^ 2 := by
    intro θ hθ
    have hA := hAsq θ hθ
    have hB := hBsq θ hθ
    have hD := hCsq θ hθ
    rw [Real.norm_eq_abs]
    have hA0 : 0 ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 := sq_nonneg _
    have hB0 : 0 ≤ (deriv h θ) ^ 2 := sq_nonneg _
    have hD0 : 0 ≤ 4 * (h θ) ^ 2 := by positivity
    have htri : |(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
          + 4 * (h θ) ^ 2|
        ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 + (deriv h θ) ^ 2 + 4 * (h θ) ^ 2 := by
      rw [abs_le]
      constructor <;> linarith
    calc |(deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
          + 4 * (h θ) ^ 2|
        ≤ (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 + (deriv h θ) ^ 2 + 4 * (h θ) ^ 2 :=
          htri
      _ ≤ 9 * C ^ 2 + C ^ 2 + 4 * C ^ 2 := by linarith
      _ = 14 * C ^ 2 := by ring
  -- ## endpoint limits of the primitive
  have hphi_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ‖angPhiD h θ‖ ≤ 2 * C ^ 2 * Real.sin (2 * θ) := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsq : (h θ) ^ 2 ≤ (C * Real.sin (2 * θ)) ^ 2 := by
      calc (h θ) ^ 2 = |h θ| ^ 2 := (sq_abs _).symm
        _ ≤ (C * Real.sin (2 * θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hbdd θ (hsub hθ)) 2
    have habs : |angPhiD h θ| = 2 * (h θ) ^ 2 * |Real.cot (2 * θ)| := by
      rw [show angPhiD h θ = -2 * (h θ) ^ 2 * Real.cot (2 * θ) from rfl,
        abs_mul, abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (sq_nonneg (h θ))]
    rw [Real.norm_eq_abs, habs]
    calc 2 * (h θ) ^ 2 * |Real.cot (2 * θ)|
        ≤ 2 * (C * Real.sin (2 * θ)) ^ 2 * |Real.cot (2 * θ)| :=
          mul_le_mul_of_nonneg_right (by linarith [hsq]) (abs_nonneg _)
      _ ≤ 2 * (C * Real.sin (2 * θ)) ^ 2 * (1 / Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (abs_cot_two_le hθ) (by positivity)
      _ = 2 * C ^ 2 * Real.sin (2 * θ) := by
          have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
          field_simp
  have htend0 : Tendsto (angPhiD h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsin0 : Tendsto (fun θ : ℝ => 2 * C ^ 2 * Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
            (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
        rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      simpa using Tendsto.const_mul (2 * C ^ 2) h1'
    refine squeeze_zero_norm' ?_ hsin0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hphi_le θ hθ
  have htendπ : Tendsto (angPhiD h) (𝓝[<] (π / 2)) (𝓝 0) := by
    have hsinπ : Tendsto (fun θ : ℝ => 2 * C ^ 2 * Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
      have h1' : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[<] (π / 2)) (𝓝 0) := by
        have hc : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (π / 2))
            (𝓝 (Real.sin (2 * (π / 2)))) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
        rw [show Real.sin (2 * (π / 2)) = 0 by
              rw [show 2 * (π / 2) = π by ring, Real.sin_pi]] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      simpa using Tendsto.const_mul (2 * C ^ 2) h1'
    refine squeeze_zero_norm' ?_ hsinπ
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hphi_le θ hθ
  -- ## derivative of the primitive
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivAt (angPhiD h)
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2) θ := by
    intro θ hθ
    have hhAt : HasDerivAt h (deriv h θ) θ :=
      ((hh.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)).differentiableAt (by norm_num)).hasDerivAt
    have hprod := ((hhAt.pow 2).const_mul (-2)).mul (hasDerivAt_cot_two θ hθ)
    refine hprod.congr_deriv ?_
    simp only [Pi.pow_apply]
    ring
  -- ## a general integrability criterion on `Iθ`
  have int_bdd : ∀ (g : ℝ → ℝ) (M : ℝ), ContinuousOn g (Set.Ioo (0 : ℝ) (π / 2)) →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ‖g θ‖ ≤ M) →
      Integrable g (volume.restrict Work.Spaces.Iθ) := by
    intro g M hcont hbnd
    have hIoo : Integrable g (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine Integrable.of_bound (hcont.aestronglyMeasurable measurableSet_Ioo) M ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hbnd θ hθ
    have hIcc : Integrable g (volume.restrict (Set.Icc (0 : ℝ) (π / 2))) := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
      exact hIoo
    exact hIcc
  -- ## integrability of the pieces
  have hcontA : ContinuousOn (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontD.sub ((hcontCot.const_mul 2).mul hcontH)).pow 2
  have hcontB : ContinuousOn (fun θ : ℝ => (deriv h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hcontD.pow 2
  have hcontCc : ContinuousOn (fun θ : ℝ => 4 * (h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontH.pow 2).const_mul 4
  have hAint : Integrable (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2) (9 * C ^ 2) hcontA
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hAsq θ hθ)
  have hBint : Integrable (fun θ : ℝ => (deriv h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => (deriv h θ) ^ 2) (C ^ 2) hcontB
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hBsq θ hθ)
  have hCint : Integrable (fun θ : ℝ => 4 * (h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd (fun θ : ℝ => 4 * (h θ) ^ 2) (4 * C ^ 2) hcontCc
      (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hCsq θ hθ)
  have hcontF : ContinuousOn
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (hcontA.sub hcontB).add hcontCc
  have hFint : Integrable
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    int_bdd _ (14 * C ^ 2) hcontF hboundF
  -- ## interval integrability on `0..π/2`
  have hIntF : IntervalIntegrable
      (fun θ : ℝ => (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2
        + 4 * (h θ) ^ 2) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpi2.le]
    show Integrable _ (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
    exact hFint
  -- ## the fundamental theorem of calculus
  have hFTC : (∫ θ in (0 : ℝ)..(π / 2),
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi2 hderiv hIntF
      htend0 htendπ
    simpa using h
  have hzero : (∫ θ in Work.Spaces.Iθ,
      ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2)) = 0 := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hpi2.le]
    exact hFTC
  -- ## splitting the integral
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2 + 4 * (h θ) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
        - (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2) := by
    have e1 : (∫ θ in Work.Spaces.Iθ,
          ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2) + 4 * (h θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2) :=
      integral_add (hAint.sub hBint) hCint
    have e2 : (∫ θ in Work.Spaces.Iθ,
            ((deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2 - (deriv h θ) ^ 2))
        = (∫ θ in Work.Spaces.Iθ, (deriv h θ - 2 * Real.cot (2 * θ) * h θ) ^ 2)
          - (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) :=
      integral_sub hAint hBint
    linarith [e1, e2]
  have hCmul : (∫ θ in Work.Spaces.Iθ, 4 * (h θ) ^ 2)
      = 4 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) :=
    integral_const_mul 4 (fun θ : ℝ => (h θ) ^ 2)
  linarith [hzero, hsplit, hCmul]

end Work.FTS.EllipticEst.AngGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.setIntegral_w_mul_sqrt_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- **Weighted Cauchy–Schwarz for `∫_s m·√A·√B`.**

If `m`, `A`, `B` are nonnegative and the *products* `m·A`, `m·B` are integrable on `s`, then the
weighted pairing `m·√A·√B` is integrable on `s` and

  `∫_s m·√A·√B ≤ √(∫_s m·A) · √(∫_s m·B)`.

The point is that no measurability of `m`, `A`, `B` themselves is assumed — only of the products
`m·A`, `m·B` (through their integrability).  Indeed `m·√A·√B = √(m·A)·√(m·B)` pointwise (all three
factors being nonnegative), and the right-hand side is a product of two functions that are
a.e. strongly measurable *because* `m·A` and `m·B` are integrable.  Integrability of the product
follows from the AM–GM domination `√(m·A)·√(m·B) ≤ ((m·A) + (m·B))/2`
(`Work.Coercivity.integrable_sqrt_mul_sqrt`), and the inequality is the ordinary Cauchy–Schwarz in
the weighted `L²` space (`Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt`), the
nonnegativity replacing the absolute value on the left. -/
theorem setIntegral_w_mul_sqrt_le {s : Set ℝ} {m A B : ℝ → ℝ}
    (hm : ∀ z, 0 ≤ m z) (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z)
    (hAi : MeasureTheory.IntegrableOn (fun z => m z * A z) s)
    (hBi : MeasureTheory.IntegrableOn (fun z => m z * B z) s) :
    MeasureTheory.IntegrableOn (fun z => m z * Real.sqrt (A z) * Real.sqrt (B z)) s
      ∧ ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)
        ≤ Real.sqrt (∫ z in s, m z * A z) * Real.sqrt (∫ z in s, m z * B z) := by
  have hmA : ∀ z, 0 ≤ m z * A z := fun z => mul_nonneg (hm z) (hA z)
  have hmB : ∀ z, 0 ≤ m z * B z := fun z => mul_nonneg (hm z) (hB z)
  have hnonneg : ∀ z, 0 ≤ m z * Real.sqrt (A z) * Real.sqrt (B z) :=
    fun z => mul_nonneg (mul_nonneg (hm z) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- `m·√A·√B = √(m·A)·√(m·B)`, pointwise, for nonnegative `m`, `A`, `B`
  have hkey : ∀ z, Real.sqrt (m z * A z) * Real.sqrt (m z * B z)
      = m z * Real.sqrt (A z) * Real.sqrt (B z) := by
    intro z
    rw [Real.sqrt_mul (hm z) (A z), Real.sqrt_mul (hm z) (B z)]
    have hsq : Real.sqrt (m z) * Real.sqrt (m z) = m z := by
      rw [← sq, Real.sq_sqrt (hm z)]
    calc (Real.sqrt (m z) * Real.sqrt (A z)) * (Real.sqrt (m z) * Real.sqrt (B z))
        = (Real.sqrt (m z) * Real.sqrt (m z)) * (Real.sqrt (A z) * Real.sqrt (B z)) := by ring
      _ = m z * Real.sqrt (A z) * Real.sqrt (B z) := by rw [hsq]; ring
  -- integrability of the product, by AM–GM domination
  have hprod : Integrable (fun z => Real.sqrt (m z * A z) * Real.sqrt (m z * B z))
      (volume.restrict s) :=
    Work.Coercivity.integrable_sqrt_mul_sqrt (volume.restrict s)
      (fun z => m z * A z) (fun z => m z * B z) hAi hBi hmA hmB
  have hCint : MeasureTheory.IntegrableOn
      (fun z => m z * Real.sqrt (A z) * Real.sqrt (B z)) s :=
    hprod.congr (Filter.Eventually.of_forall hkey)
  refine ⟨hCint, ?_⟩
  -- the pointwise domination needed for the abstract Cauchy–Schwarz step
  have hslice : ∀ z ∈ s, |m z * Real.sqrt (A z) * Real.sqrt (B z)|
      ≤ Real.sqrt (m z * A z) * Real.sqrt (m z * B z) := by
    intro z _
    rw [abs_of_nonneg (hnonneg z)]
    exact (hkey z).symm.le
  have hbound := abs_setIntegral_le_sqrt_mul_sqrt (s := s)
    (A := fun z => m z * A z) (B := fun z => m z * B z)
    (C := fun z => m z * Real.sqrt (A z) * Real.sqrt (B z))
    hAi hBi hCint (fun z _ => hmA z) (fun z _ => hmB z) hslice
  have hpos : 0 ≤ ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z) :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hnonneg)
  calc ∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)
      = |∫ z in s, m z * Real.sqrt (A z) * Real.sqrt (B z)| := (abs_of_nonneg hpos).symm
    _ ≤ Real.sqrt (∫ z in s, m z * A z) * Real.sqrt (∫ z in s, m z * B z) := hbound

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.pureHardySinTwo_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Aux

/-! ## Elementary trigonometric comparisons

Both endpoints of `Iθ = [0, π/2]` are singular for the weight `sin(2θ)^{-2}`.  On the halves
`[0,π/4]` and `[π/4,π/2]` Jordan's inequality `sin x ≥ (2/π) x` gives the comparison with a
power weight, and `Work.Elliptic.power_hardy` supplies the sharp power Hardy inequality. -/

/-- Jordan's inequality on the left half: `(4/π) θ ≤ sin (2θ)` for `0 ≤ θ ≤ π/4`. -/
private lemma four_div_pi_mul_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h2 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) h2
  calc (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) := by ring
    _ ≤ Real.sin (2 * θ) := h



/-! ## Two elementary algebraic identities -/



/-! ## The power-weight Hardy inequality in division form -/



/-! ## The two halves of `Iθ` -/



/-! ## Interval integrability of the four integrands -/


/-! ## The target -/


end Work.FTS.EllipticEst.Aux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.GbarSin.Gbar_congr_of_fstar_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GbarSin


end Work.FTS.EllipticEst.Cert.GbarSin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_Dz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise domination of the `H^k`-integrand of `D_z Ψ`

This module proves the pure index-bookkeeping statement `HkIntegrand_Dz_le`: the sum of
squares making up the `H^k`-integrand of `D_z Ψ` is dominated by the `H^k`-integrands of
`Ψ` and of `D_θ Ψ` together with the two "top order" summands they do not contain.

Write `H = w/√sin(2θ)^η` and `W = Wt α` for the two weights, so that

`HkIntegrand α k f = Σ_{i≤k} (D_z^i f·H)² + Σ_{1≤i, i+j≤k} (D_z^j D_θ^i f·W)²`.

Since `D_z^i (D_z Ψ) = D_z^{i+1} Ψ` and (by commutativity of `D_z` and `D_θ` on the closed
quadrant, `Work.Spaces.mixed_comm`, available from `SmoothNbhd Ψ`)

`D_z^j D_θ^i (D_z Ψ) = D_z^{j+1} D_θ^i Ψ` on `[0,∞) × [0,π/2]`,

the radial summands of `HkIntegrand α k (D_z Ψ)` are the radial summands of `Ψ` of order
`1 ≤ i ≤ k+1`, and the mixed summands are `(D_z^{j+1}D_θ^iΨ·W)²` with `1 ≤ i`, `i+j ≤ k`.
The latter are covered as follows:

* `i ≥ 2`: they are the mixed summands of `HkIntegrand α k (D_θΨ)` under the index shift
  `(i,j) ↦ (i-1,j+1)`, since `D_z^{j+1}D_θ^{i-1}(D_θΨ) = D_z^{j+1}D_θ^iΨ`;
* `i = 1` and `j + 2 ≤ k`: they are the `(1, j+1)`-mixed summands of `HkIntegrand α k Ψ`;
* `i = 1` and `j + 1 = k`: this single summand is `(D_z^kD_θΨ·W)²`, added on the right.

The radial summand `D_z^{k+1}Ψ·H` (order `k+1`) is the other summand added on the right.
No weight comparison is needed: matching summands carry literally the same weight.

The combinatorial content of the mixed part is `Coercivity.SumShiftZ_le` (the shift
`j ↦ j+1` inside the triangle `1 ≤ i`, `i+j ≤ k+1`, valid for nonnegative terms) and
`Coercivity.SumRowShift_eq` (splitting off the row `i = 1` of that triangle).  Everything
else is the algebra of `D_z`, `D_θ` iterates.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Index identities for iterated derivatives -/

/-- The pure family of the `H^k`-integrand of `D_z f` is the pure family of `f` shifted by
one: `D_z^i (D_z f) = D_z^{i+1} f`. -/
private lemma DzIter_Dz (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter i (Spaces.Dz f) = Spaces.DzIter (i + 1) f := by
  rw [Spaces.DzIter_add_right]
  rfl

/-- The mixed family of the `H^k`-integrand of `D_z f` is the mixed family of `f` with the
`D_z`-order raised by one: `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` on the closed quadrant,
by commutation of `D_z` and `D_θ`. -/
private lemma mixed_Dz (j i : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed j i (Spaces.Dz f) z θ = Spaces.mixed (j + 1) i f z θ := by
  simpa using Spaces.mixed_comm f hsm j i 1 0 z θ hz hθ

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with the
`D_θ`-order raised by one: `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
private lemma mixed_Dth (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth f) = Spaces.mixed j (i + 1) f := by
  simp only [Spaces.mixed]
  have h : Spaces.Dth f = Spaces.DthIter 1 f := rfl
  rw [h, Spaces.DthIter_add_right]

/-- `D_z^k (D_θ f) = mixed k 1 f`. -/
private lemma DzIter_Dth_eq_mixed (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Spaces.DzIter k (Spaces.Dth f) = Spaces.mixed k 1 f := by
  simp only [Spaces.mixed, Spaces.DthIter_succ, Spaces.DthIter_zero]

/-! ## Combinatorial lemmas -/

/-- A conditionally defined summand with nonnegative values is nonnegative. -/
private lemma ite_cond_nonneg {G : ℕ → ℕ → ℝ} (hG : ∀ a b, 0 ≤ G a b) (a b k : ℕ) :
    0 ≤ (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
  split_ifs with h
  · exact hG a b
  · exact le_refl 0

/-- The shifted version of `ite_cond_nonneg`: the condition still refers to the indices
`(a,b)`, but the summand is `G (a+1) b`. -/
private lemma ite_cond_nonneg_shift {G : ℕ → ℕ → ℝ} (hG : ∀ a b, 0 ≤ G a b) (a b k : ℕ) :
    0 ≤ (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0) := by
  split_ifs with h
  · exact hG (a + 1) b
  · exact le_refl 0

/-- Shifting the radial index by one: `Σ_{i≤k} R(i+1) ≤ Σ_{i≤k} R i + R(k+1)` when the
missed term `R 0` is nonnegative. -/
private lemma radial_le (k : ℕ) (R : ℕ → ℝ) (hR : 0 ≤ R 0) :
    (∑ i ∈ Finset.range (k + 1), R (i + 1))
      ≤ (∑ i ∈ Finset.range (k + 1), R i) + R (k + 1) := by
  have h1 : (∑ x ∈ Finset.range (k + 1 + 1), R x)
      = (∑ i ∈ Finset.range (k + 1), R (i + 1)) + R 0 :=
    Finset.sum_range_succ' R (k + 1)
  have h2 : (∑ x ∈ Finset.range (k + 1 + 1), R x)
      = (∑ i ∈ Finset.range (k + 1), R i) + R (k + 1) :=
    Finset.sum_range_succ R (k + 1)
  linarith

/-- The mixed-index bookkeeping.  For a nonnegative `G`, the double sum over the triangle
`1 ≤ i`, `i + j ≤ k` with the term `G i (j+1)` is dominated by the sum of

* the same triangle with the term `G a b`,
* the same triangle with the term `G (a+1) b`,
* the single term `G 1 k`.

Indeed, `SumShiftZ_le` puts the left-hand side inside the triangle `1 ≤ a`, `a + b ≤ k+1`
with term `G a b`; `SumRowShift_eq` splits off the row `a = 1` of that triangle, leaving
exactly the second sum; and the row `a = 1` itself is `Σ_{i<k} G 1 i + G 1 k`. -/
private lemma mixed_le (k : ℕ) (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      ≤ (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
        + (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0))
        + G 1 k := by
  by_cases hk : k = 0
  · rw [hk]
    have h1 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (0 + 1),
        (if 1 ≤ i ∧ i + j ≤ 0 then G i (j + 1) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (by omega)
    rw [h1]
    refine add_nonneg (add_nonneg ?_ ?_) (hG 1 0)
    · exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ite_cond_nonneg hG a b 0
    · exact Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ite_cond_nonneg_shift hG a b 0
  · set A : ℝ := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) with hA
    set B : ℝ := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
        (if 1 ≤ a ∧ a + b ≤ k then G (a + 1) b else 0) with hB
    set T : ℝ := ∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0) with hT
    have hshift : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) ≤ T := by
      rw [hT]
      exact Work.Coercivity.SumShiftZ_le k G hG
    have hrow : (∑ i ∈ Finset.range (k + 1), G 1 i) + B = T := by
      rw [hB, hT]
      exact Work.Coercivity.SumRowShift_eq k G
    have hrow1 : (∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ (1 : ℕ) ∧ (1 : ℕ) + b ≤ k then G 1 b else 0))
        = ∑ i ∈ Finset.range k, G 1 i := by
      rw [Finset.sum_range_succ]
      have hz : (if 1 ≤ (1 : ℕ) ∧ (1 : ℕ) + k ≤ k then G 1 k else 0) = 0 := by
        rw [ite_eq_right (by omega)]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mem_range] at hb
      rw [ite_eq_left (by omega)]
    have hArow : (∑ i ∈ Finset.range (k + 1), G 1 i) ≤ A + G 1 k := by
      rw [Finset.sum_range_succ (fun i => G 1 i) k, hA]
      have hsub : (∑ i ∈ Finset.range k, G 1 i)
          ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
              (if 1 ≤ a ∧ a + b ≤ k then G a b else 0) := by
        have hmem : (1 : ℕ) ∈ Finset.range (k + 1) := by
          rw [Finset.mem_range]
          omega
        refine le_trans (le_of_eq hrow1.symm) ?_
        exact Finset.single_le_sum
          (f := fun a => ∑ b ∈ Finset.range (k + 1),
            (if 1 ≤ a ∧ a + b ≤ k then G a b else 0))
          (s := Finset.range (k + 1))
          (fun a _ => Finset.sum_nonneg fun b _ => ite_cond_nonneg hG a b k) hmem
      linarith
    have hmain : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0)) ≤ A + B + G 1 k := by
      linarith [hshift, hrow, hArow]
    rwa [hA, hB] at hmain

/-! ## The main statement -/

/-- **Pointwise domination of the `H^k`-integrand of `D_z Ψ`.**  This is a pure index
bookkeeping statement (summands of `HkIntegrand`), using only that `D_z` and `D_θ` commute for a
function smooth on a neighbourhood of the closed quadrant (`Work.Spaces.mixed_comm`).  Writing
`H = w/sin(2θ)^{η/2}` and `W = Wt α z θ = w/sin(2θ)^{γ/2}`,

`HkIntegrand α k (D_zΨ) = Σ_{i≤k} (D_z^{i+1}Ψ·H)² + Σ_{1≤i, i+j≤k} (D_z^{j+1}D_θ^iΨ·W)²`,

and since `mixed j i (Dz Ψ) = D_z^{j+1}D_θ^iΨ` on the quadrant, the summands split as follows:
the radial summands with `i+1 ≤ k` are radial summands of `HkIntegrand α k Ψ`; the mixed
summands with `i ≥ 2` are mixed summands of `HkIntegrand α k (D_θΨ)` (index shift
`(i,j) ↦ (i-1,j+1)`); the mixed summands with `i = 1` and `j+1 ≤ k-1` are mixed summands of
`HkIntegrand α k Ψ` (index `(1,j+1)`); and exactly two summands are *not* covered, namely
`(D_z^{k+1}Ψ·H)²` and `(D_z^kD_θΨ·W)²`, which are added on the right.  No weight comparison is
needed (the weights of matching summands are literally equal); at the boundary points `z = 0`,
`θ ∈ {0, π/2}` every term vanishes.  Template for the Finset bookkeeping:
`Submission/Work/Spaces/HkSq_mixed_le.lean`. -/
theorem HkIntegrand_Dz_le (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hα : 0 < α) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.Dz Ψ) z θ
      ≤ Work.Spaces.HkIntegrand α k Ψ z θ + Work.Spaces.HkIntegrand α k (Work.Spaces.Dth Ψ) z θ
        + (Work.Spaces.DzIter (k + 1) Ψ z θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (Work.Spaces.DzIter k (Work.Spaces.Dth Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
  set W : ℝ := Spaces.Wt α z θ with hW
  -- Unfolding the integrand in the two weights `H` and `W`.
  have hunfold : ∀ f : ℝ → ℝ → ℝ, Spaces.HkIntegrand α k f z θ
      = (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i f z θ * H) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i f z θ * W) ^ 2 else 0) := by
    intro f
    simp only [Spaces.HkIntegrand, ← hH, ← hW]
  -- The radial (pure) part of `D_z Ψ`.
  have hPL : (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dz Ψ) z θ * H) ^ 2)
      ≤ (∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i Ψ z θ * H) ^ 2)
        + (Spaces.DzIter (k + 1) Ψ z θ * H) ^ 2 := by
    have hcongr : (∑ i ∈ Finset.range (k + 1),
          (Spaces.DzIter i (Spaces.Dz Ψ) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Spaces.DzIter (i + 1) Ψ z θ * H) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz i Ψ])
    rw [hcongr]
    exact radial_le k (fun a => (Spaces.DzIter a Ψ z θ * H) ^ 2)
      (sq_nonneg (Spaces.DzIter 0 Ψ z θ * H))
  -- The mixed part of `D_z Ψ`: push `D_θ` past `D_z`.
  have hmixedcongr : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz Ψ) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed (j + 1) i Ψ z θ * W) ^ 2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dz j i hsm hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  -- The mixed part of the `D_θ Ψ`-integrand, with the `D_θ`-order reduced by one.
  have hBcongr : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth Ψ) z θ * W) ^ 2 else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j (i + 1) Ψ z θ * W) ^ 2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dth j i Ψ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hML : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dz Ψ) z θ * W) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i Ψ z θ * W) ^ 2 else 0))
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Spaces.mixed j i (Spaces.Dth Ψ) z θ * W) ^ 2 else 0))
        + (Spaces.DzIter k (Spaces.Dth Ψ) z θ * W) ^ 2 := by
    rw [hmixedcongr, hBcongr]
    rw [show (Spaces.DzIter k (Spaces.Dth Ψ) z θ * W) ^ 2
        = (Spaces.mixed k 1 Ψ z θ * W) ^ 2 by
      rw [show Spaces.DzIter k (Spaces.Dth Ψ) = Spaces.mixed k 1 Ψ from
        DzIter_Dth_eq_mixed k Ψ]]
    exact mixed_le k (fun p q => (Spaces.mixed q p Ψ z θ * W) ^ 2)
      (fun p q => sq_nonneg _)
  have hPB : 0 ≤ ∑ i ∈ Finset.range (k + 1), (Spaces.DzIter i (Spaces.Dth Ψ) z θ * H) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hunfold (Spaces.Dz Ψ), hunfold Ψ, hunfold (Spaces.Dth Ψ)]
  linarith [hPL, hML, hPB]

end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux.hasDerivAt_J =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux


end Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false






end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-! ## Elementary facts about the weight -/

/-- `sin (2θ) > 0` on the open interval `(0, π/2)`. -/
lemma sst_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- `σ = σ₁ · sin(2θ)`, i.e. `sin(2θ)^{-η} = sin(2θ)^{-(1+η)}·sin(2θ)`. -/
lemma sst_sig_eq_sig1_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig θ = sig1 θ * Real.sin (2 * θ) := by
  have hs := sst_sin_two_pos hθ
  simp only [sig, sig1]
  rw [show -(Work.Spaces.eta) = -(1 + Work.Spaces.eta) + 1 by ring,
    Real.rpow_add hs, Real.rpow_one]

/-- `σ₁ = σ₂ · sin(2θ)`, i.e. `sin(2θ)^{-(1+η)} = sin(2θ)^{-(2+η)}·sin(2θ)`. -/
lemma sst_sig1_eq_sig2_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    sig1 θ = sig2 θ * Real.sin (2 * θ) := by
  have hs := sst_sin_two_pos hθ
  simp only [sig1, sig2]
  rw [show -(1 + Work.Spaces.eta) = -(2 + Work.Spaces.eta) + 1 by ring,
    Real.rpow_add hs, Real.rpow_one]

/-! ## The derivatives of the weights -/

/-- `(σ)' = -2η cos(2θ) σ₁`. -/
lemma sst_hasDerivAt_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sig (-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) θ := by
  have hs := sst_sin_two_pos hθ
  have hinner : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(Work.Spaces.eta)))
      (-(Work.Spaces.eta) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1))
      (Real.sin (2 * θ)) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs))
  refine (houter.comp θ hinner).congr_deriv ?_
  rw [show (-(Work.Spaces.eta) - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
  simp only [sig1]
  ring

/-- `(σ₁)' = -2(1+η) cos(2θ) σ₂`. -/
lemma sst_hasDerivAt_sig1 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt sig1 (-2 * (1 + Work.Spaces.eta) * Real.cos (2 * θ) * sig2 θ) θ := by
  have hs := sst_sin_two_pos hθ
  have hinner : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(1 + Work.Spaces.eta)))
      (-(1 + Work.Spaces.eta) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta) - 1))
      (Real.sin (2 * θ)) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs))
  refine (houter.comp θ hinner).congr_deriv ?_
  rw [show (-(1 + Work.Spaces.eta) - 1 : ℝ) = -(2 + Work.Spaces.eta) by ring]
  simp only [sig2]
  ring

/-! ## The pointwise identity -/



/-! ## The truncated integral identity -/


end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.powerHardyNeg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Hardy inequality `∫ x^{a-2} v² ≤ (4/(1-a)²) ∫ x^a (v')²` on `[lo,hi]`

For `0 < a < 1`, `0 < lo < hi < π/2` and `v` of class `C¹` on `(0, π/2)` with `v lo = 0`:

  `∫_{lo}^{hi} x^{a-2} v(x)² dx ≤ (4/(1-a)²) ∫_{lo}^{hi} x^a v'(x)² dx`.

This is the sharp weighted (power) Hardy inequality, with the anchor at the *left* endpoint `lo`
and with the exponent `a - 2` on the mass term ranging in `(-2,-1)` (equivalently the exponent `a`
on the derivative term ranges in `(0,1)`), so that `Work.Elliptic.power_hardy` and
`Work.FTS.EllipticEst.TT.powerHardy_at` do not apply directly: both require the derivative
exponent `-η` to be `≤ 0`, i.e. `η ≥ 0`.  The purpose of this file is the complementary range.

The proof is the standard completion of squares, exactly as in `powerHardy_at` (whose proof uses
`0 ≤ η < 1` only through `-1 < η`):

* `0 ≤ t^{-η} (g'(t) - (1+η)/2 · g(t)/t)²` rewrites as
  `(1+η)²/4 · g(t)² t^{-(2+η)} ≤ g'(t)² t^{-η} - ((1+η)/2) · Φ'(t)` with
  `Φ(t) = g(t)² t^{-(1+η)}`;
* integrating over `[ε,A]` and applying the fundamental theorem of calculus, the left boundary
  term `-((1+η)/2)Φ(ε)` vanishes because `g ε = 0`, while the right one `-((1+η)/2)Φ(A) ≤ 0`
  has the favourable sign (this is where `η > -1` is used), giving
  `(1+η)²/4 ∫ g² t^{-(2+η)} ≤ ∫ g'² t^{-η}`.

The tool lemma `powerHardy_at_gen` is stated for a general exponent `η > -1` (and is proved with
`derivWithin` on the closed interval so that every integrand is continuous there); the target
`powerHardyNeg` is its instance `η = -a` on `[lo,hi]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 1000000



end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dth1IterTwoCosDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.EllipticEst

noncomputable section

/-- The quotient sequence `gSeq n` of `D_θ^{n+1}(2 cos 2θ)` by `sin(2θ)²`. -/
def gSeq : ℕ → ℝ → ℝ
  | 0 => fun _ => -4
  | n + 1 => fun θ => 4 * Real.cos (2 * θ) * gSeq n θ + Real.sin (2 * θ) * deriv (gSeq n) θ

theorem gSeq_zero : gSeq 0 = fun _ => (-4 : ℝ) := rfl

theorem gSeq_succ (n : ℕ) :
    gSeq (n + 1) = fun θ => 4 * Real.cos (2 * θ) * gSeq n θ
      + Real.sin (2 * θ) * deriv (gSeq n) θ := rfl

/-- Every `gSeq n` is `C^∞`. -/
theorem gSeq_contDiff : ∀ n : ℕ, ContDiff ℝ ∞ (gSeq n) := by
  intro n
  induction n with
  | zero => rw [gSeq_zero]; exact contDiff_const
  | succ n ih =>
    have hd : ContDiff ℝ ∞ (deriv (gSeq n)) := (contDiff_infty_iff_deriv.mp ih).2
    have hcos : ContDiff ℝ ∞ (fun θ : ℝ => 4 * Real.cos (2 * θ)) :=
      contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
    have hsin : ContDiff ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    have h : ContDiff ℝ ∞ (fun θ : ℝ => 4 * Real.cos (2 * θ) * gSeq n θ
        + Real.sin (2 * θ) * deriv (gSeq n) θ) := (hcos.mul ih).add (hsin.mul hd)
    rw [gSeq_succ]
    exact h

/-- Every `gSeq n` is differentiable. -/
theorem gSeq_differentiable (n : ℕ) : Differentiable ℝ (gSeq n) :=
  (contDiff_infty_iff_deriv.mp (gSeq_contDiff n)).1

/-- The derivative of a `c`-periodic function is `c`-periodic. -/
theorem periodic_deriv {f : ℝ → ℝ} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  rw [← deriv_comp_add_const f c x, show (fun y => f (y + c)) = f from funext fun y => h y]


theorem periodic_sin_two : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ)) Real.pi := by
  intro θ
  show Real.sin (2 * (θ + Real.pi)) = Real.sin (2 * θ)
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring, Real.sin_add_two_pi]

theorem periodic_four_cos_two : Function.Periodic (fun θ : ℝ => 4 * Real.cos (2 * θ)) Real.pi := by
  intro θ
  show 4 * Real.cos (2 * (θ + Real.pi)) = 4 * Real.cos (2 * θ)
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring, Real.cos_add_two_pi]

/-- Every `gSeq n` is `π`-periodic. -/
theorem gSeq_periodic : ∀ n : ℕ, Function.Periodic (gSeq n) Real.pi := by
  intro n
  induction n with
  | zero =>
    rw [gSeq_zero]
    intro x
    simp
  | succ n ih =>
    have h1 : Function.Periodic (fun θ : ℝ => 4 * Real.cos (2 * θ) * gSeq n θ) Real.pi :=
      periodic_four_cos_two.mul ih
    have h2 : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ) * deriv (gSeq n) θ) Real.pi :=
      periodic_sin_two.mul (periodic_deriv ih)
    have h := h1.add h2
    rw [gSeq_succ]
    exact h

/-- Each `gSeq n` is bounded on `ℝ`: it is continuous and `π`-periodic, hence bounded on the
compact `[0, π]`, and every point is `π`-periodically transported into `[0, π)`. -/
theorem gSeq_bdd (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |gSeq n θ| ≤ C := by
  have hcont : Continuous (gSeq n) := (gSeq_contDiff n).continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc 0 Real.pi) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h0 : |gSeq n 0| ≤ C := by
      simpa [Real.norm_eq_abs] using hC 0 (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
    exact le_trans (abs_nonneg _) h0
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), fun θ => ?_⟩
  obtain ⟨y, hy, hyθ⟩ := (gSeq_periodic n).exists_mem_Ico₀ Real.pi_pos θ
  rw [hyθ]
  have hyI : y ∈ Set.Icc (0 : ℝ) Real.pi := Set.mem_Icc.mpr ⟨hy.1, le_of_lt hy.2⟩
  have h1 : |gSeq n y| ≤ C := by
    simpa [Real.norm_eq_abs] using hC y hyI
  exact le_trans h1 (le_max_left C 1)

end

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false

/-- **Lebesgue differentiation, interval form.** A function whose integral over every interval
`[s,t] ⊂ (0,∞)` vanishes, vanishes almost everywhere on `(0,∞)`. -/
theorem ae_eq_zero_of_forall_intervalIntegral_eq_zero {V : ℝ → ℝ}
    (hzero : ∀ s t : ℝ, 0 < s → 0 < t → ∫ r in s..t, V r = 0)
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), V z = 0 := by
  -- the compact exhaustion `(0,∞) = ⋃_n [1/(n+1), n+2]`
  have hcover : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / z) z)
      refine ⟨n, ?_, ?_⟩
      · have h1 : 1 / z ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
        rw [div_le_iff₀ hz] at h1
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith
      · have h2 : z ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
        linarith
    · rintro ⟨n, h1, h2⟩
      exact lt_of_lt_of_le (by positivity) h1
  rw [hcover, MeasureTheory.ae_restrict_iUnion_iff]
  intro n
  set a : ℝ := 1 / ((n : ℝ) + 1) with ha
  set b : ℝ := (n : ℝ) + 2 with hb
  have hpos : 0 < a := by rw [ha]; positivity
  have hlt : a < b := by
    rw [ha, hb]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hle : a ≤ b := hlt.le
  have hldt := IntervalIntegrable.ae_hasDerivAt_integral (hInt a b hpos hlt)
  rw [Set.uIcc_of_le (α := ℝ) hle] at hldt
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hldt] with x hx
  intro hxmem
  have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
  have hder : HasDerivAt (fun y : ℝ => ∫ t in a..y, V t) (V x) x :=
    hx hxmem a ⟨le_rfl, hle⟩
  have hev : (fun y : ℝ => ∫ t in a..y, V t) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
    exact hzero a y hpos hy
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (V x) x := hev.hasDerivAt_iff.mp hder
  exact h0.unique (hasDerivAt_const x 0)

/-- Interval integrability on `(0,∞)` does not depend on the order of the two endpoints. -/
theorem intervalIntegrable_pos_of_lt {V : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable V volume a b := by
  intro a b ha hb
  rcases le_total a b with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact IntervalIntegrable.refl
    · exact hInt a b ha hlt
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact IntervalIntegrable.refl
    · exact (hInt b a hb hlt).symm

/-- **The integrated moment chain propagates a.e. vanishing.** If `W t - W s = ∫_s^t V` for
all `0 < s ≤ t`, `W` vanishes a.e. on `(0,∞)` and `V` is interval integrable on `(0,∞)`, then
`V` vanishes a.e. on `(0,∞)`. -/
theorem ae_eq_zero_of_moment_chain {W V : ℝ → ℝ}
    (hchain : ∀ s t : ℝ, 0 < s → s ≤ t → W t - W s = ∫ r in s..t, V r)
    (hW : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), W z = 0)
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), V z = 0 := by
  have hInt' := intervalIntegrable_pos_of_lt hInt
  -- the primitive from `1` is `W · - W 1`
  have hP : ∀ z : ℝ, 0 < z → (∫ r in (1 : ℝ)..z, V r) = W z - W 1 := by
    intro z hz
    rcases le_total 1 z with h | h
    · exact (hchain 1 z one_pos h).symm
    · have h' := hchain z 1 hz h
      rw [intervalIntegral.integral_symm]
      linarith
  -- hence it is a.e. constant
  have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (∫ r in (1 : ℝ)..z, V r) = -(W 1) := by
    filter_upwards [hW, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
    rw [hP z hzpos, hz, zero_sub]
  -- and it is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => ∫ r in (1 : ℝ)..z, V r) (Set.Ioi 0) := by
    intro x hx
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
        1 / ((n : ℝ) + 1) < x ∧ x < (n : ℝ) + 2 := by
      obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / x) x)
      have h1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      have h2 : x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      refine ⟨n, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        rw [div_le_iff₀ hx] at h1
        nlinarith
      · linarith
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 0 < (n : ℝ) + 2 := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 := lt_trans hn1 hn2
    have hmem : (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
      rw [Set.uIcc_of_le (α := ℝ) hlt.le]
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]; linarith
      · linarith
    have hc := intervalIntegral.continuousOn_primitive_interval' (hInt' _ _ ha hb) hmem
    rw [Set.uIcc_of_le (α := ℝ) hlt.le] at hc
    exact (hc.continuousAt (Icc_mem_nhds hn1 hn2)).continuousWithinAt
  have hconst : Set.EqOn (fun z : ℝ => ∫ r in (1 : ℝ)..z, V r) (fun _ => -(W 1)) (Set.Ioi 0) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
      (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  -- hence every interval integral vanishes
  refine ae_eq_zero_of_forall_intervalIntegral_eq_zero (fun s t hs ht => ?_) hInt
  have hs1 : IntervalIntegrable V volume (1 : ℝ) t := hInt' 1 t one_pos ht
  have hs2 : IntervalIntegrable V volume (1 : ℝ) s := hInt' 1 s one_pos hs
  have h1 : ∫ r in (1 : ℝ)..t, V r = -(W 1) := hconst ht
  have h2 : ∫ r in (1 : ℝ)..s, V r = -(W 1) := hconst hs
  have h := intervalIntegral.integral_interval_sub_left (a := (1 : ℝ)) (b := t) (c := s) hs1 hs2
  rw [h1, h2] at h
  linarith [h]

end Work.FTS.EllipticEst.H2W.PsiSlices
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceMassExternal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `SliceMassExternal` — the external input the Ψ-side honesty chain needs

The Ψ-side honesty of the elliptic chapter (`shiftWeakClass` clause 5, `psiSliceHonest`,
`pzIterSliceGrowth3Loc`, `pzIterSliceIntegrableInput`, `SliceSourceMassBound`) is one open
problem under four namings: the tower `Lzero U_j = D_z^j F + α²U_{j+2} + 5αU_{j+1}`
(`U_j = ∂_z^jΨ`) is upward in `j` and never closes from within the classes `WeakPos2` / `Hon`.

The correctly-strengthened hypothesis is the paper's `R²Ψ → 0` at `R = 0`, carried here in the
*ψ-weighted slice-mass* form (`ψ = sinθcos²θ`) that the reduction consumes: the masses of the
radial shifts of `Ψ` up to `∂_z⁵Ψ`, and of the source shifts up to `∂_z³F`, are locally
uniformly bounded in `z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceMomentLinear =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- The angular energy of `g`: `E = ∫_θ (g'')² · sin(2θ)^{-η}`. -/
def SliceEnergy (g : ℝ → ℝ) : ℝ :=
  ∫ θ in Iθ, (deriv (deriv g) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `0 ≤ sin(2θ)` on `Iθ`. -/
theorem sin_two_nonneg' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `0 ≤ sinθ cos²θ` on `Iθ`. -/
theorem sg_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  show 0 ≤ Real.sin θ * Real.cos θ ^ 2
  exact mul_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)

/-- `sinθ cos²θ ≤ 1` on `Iθ`. -/
theorem sg_le_one {θ : ℝ} (hθ : θ ∈ Iθ) : sg θ ≤ 1 := by
  show Real.sin θ * Real.cos θ ^ 2 ≤ 1
  have hs := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul hs hc (sq_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- **Taylor's formula with integral remainder** at a point `a ∈ (0,π/2)`. -/
theorem sliceTaylor {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    {a θ : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    g θ - g a - (θ - a) * deriv g a
      = ∫ t in a..θ, (θ - t) * deriv (deriv g) t := by
  have hsub : Set.uIcc a θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rcases le_total a θ with h | h
    · rw [Set.uIcc_of_le h]
      rintro x hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    · rw [Set.uIcc_of_ge h]
      rintro x hx
      exact ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 ha.2⟩
  have hd1 := hg.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)
  have hd2 := hd1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (fun t => (θ - t) * deriv (deriv g) t) (Set.uIcc a θ) :=
    ((continuousOn_const.sub continuousOn_id).mul (hd2.continuousOn.mono hsub))
  have hderiv : ∀ t ∈ Set.uIcc a θ,
      HasDerivAt (fun t => g t + (θ - t) * deriv g t) ((θ - t) * deriv (deriv g) t) t := by
    intro t ht
    have htI := hsub ht
    have h1 : HasDerivAt g (deriv g t) t :=
      (hg.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds htI.1 htI.2)
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) t) t :=
      (hd1.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds htI.1 htI.2)
    have h3 : HasDerivAt (fun t : ℝ => θ - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub θ
    have h4 : HasDerivAt (fun t => (θ - t) * deriv g t)
        (-1 * deriv g t + (θ - t) * deriv (deriv g) t) t := h3.mul h2
    have h5 := h1.add h4
    convert h5 using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have hfin : (fun t : ℝ => g t + (θ - t) * deriv g t) θ
        - (fun t : ℝ => g t + (θ - t) * deriv g t) a
      = g θ - g a - (θ - a) * deriv g a := by
    show g θ + (θ - θ) * deriv g θ - (g a + (θ - a) * deriv g a)
        = g θ - g a - (θ - a) * deriv g a
    ring
  rw [hfin] at h
  exact h.symm

/-- The second derivative of a `C²` function on `(0,π/2)` is continuous there. -/
theorem sliceContDiff2 {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
  ((hg.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).deriv_of_isOpen (m := 0) isOpen_Ioo
    (by norm_num)).continuousOn

/-- On a subinterval `(u,v]` of the open quadrant the weight `sin(2θ)^{-η}` is at least `1`. -/
theorem one_le_rpow_sin {u v t : ℝ} (hu : 0 < u) (hv : v < Real.pi / 2)
    (ht : t ∈ Set.Ioc u v) : 1 ≤ (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
  have h1 : 0 < Real.sin (2 * t) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu, ht.1]) (by linarith [ht.2, hv, Real.pi_pos])
  have h2 : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
  have h3 := Real.rpow_le_rpow_of_nonpos h1 h2
    (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at h3

/-- **Energy monotonicity.**  On a subinterval `(u,v] ⊆ (0,π/2)`, the unweighted energy
`∫_u^v (g'')²` is at most the weighted energy `SliceEnergy g` over all of `Iθ`. -/
theorem sliceEnergy_mono {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.pi / 2) :
    ∫ t in u..v, (deriv (deriv g) t) ^ 2 ≤ SliceEnergy g := by
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Icc u v) :=
    (sliceContDiff2 hg).mono fun t ht =>
      ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
  have hsinpos : ∀ t ∈ Set.Icc u v, 0 < Real.sin (2 * t) := fun t ht =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu, ht.1]) (by linarith [ht.2, hv, Real.pi_pos])
  have hcontw : ContinuousOn (fun t => (deriv (deriv g) t) ^ 2
      * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) (Set.Icc u v) :=
    (hcont2.pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun t ht => Or.inl (ne_of_gt (hsinpos t ht))))
  have huniv : IntegrableOn (fun t => (deriv (deriv g) t) ^ 2) (Set.Ioc u v) :=
    ((hcont2.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hweighted : IntegrableOn (fun t => (deriv (deriv g) t) ^ 2
      * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) (Set.Ioc u v) :=
    (hcontw.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le huv]
  calc ∫ t in Set.Ioc u v, (deriv (deriv g) t) ^ 2
      ≤ ∫ t in Set.Ioc u v, (deriv (deriv g) t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_mono_ae huniv hweighted ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
        have h1 := one_le_rpow_sin hu hv ht
        nlinarith [sq_nonneg (deriv (deriv g) t)]
    _ ≤ ∫ t in Iθ, (deriv (deriv g) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' ht) _)
        · exact Filter.Eventually.of_forall fun t ht =>
            ⟨le_of_lt (lt_trans hu ht.1), le_of_lt (lt_of_le_of_lt ht.2 hv)⟩

/-- **The `L¹`-bound for the second derivative on a subinterval.** -/
theorem sliceAbsDeriv_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.pi / 2) :
    ∫ t in u..v, |deriv (deriv g) t| ≤ SliceEnergy g / 2 + Real.pi / 4 := by
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Icc u v) :=
    (sliceContDiff2 hg).mono fun t ht =>
      ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
  have hcu : ContinuousOn (deriv (deriv g)) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]; exact hcont2
  have hI1 : IntervalIntegrable (fun t => |deriv (deriv g) t|) volume u v :=
    hcu.abs.intervalIntegrable
  have hI2 : IntervalIntegrable (fun t => (1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2) volume u v :=
    (hcu.pow 2).const_mul (1 / 2) |>.add continuousOn_const |>.intervalIntegrable
  have h1 : ∫ t in u..v, |deriv (deriv g) t|
      ≤ ∫ t in u..v, ((1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2) := by
    refine intervalIntegral.integral_mono_on huv hI1 hI2 fun t ht => ?_
    have h2 : 2 * |deriv (deriv g) t| ≤ (deriv (deriv g) t) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|deriv (deriv g) t| - 1), sq_abs (deriv (deriv g) t)]
    linarith
  have hI2a : IntervalIntegrable (fun t => (1 / 2) * (deriv (deriv g) t) ^ 2) volume u v :=
    (hcu.pow 2).const_mul (1 / 2) |>.intervalIntegrable
  have hI2b : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume u v :=
    continuousOn_const.intervalIntegrable
  have h2 : ∫ t in u..v, ((1 / 2) * (deriv (deriv g) t) ^ 2 + 1 / 2)
      = (1 / 2) * (∫ t in u..v, (deriv (deriv g) t) ^ 2) + (1 / 2) * (v - u) := by
    rw [intervalIntegral.integral_add hI2a hI2b, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    ring
  have h3 : ∫ t in u..v, (deriv (deriv g) t) ^ 2 ≤ SliceEnergy g :=
    sliceEnergy_mono hg hE hu huv hv
  have h4 : v - u ≤ Real.pi / 2 := by linarith [hu, hv]
  rw [h2] at h1
  have h5 : (1 / 2) * (∫ t in u..v, (deriv (deriv g) t) ^ 2) + (1 / 2) * (v - u)
      ≤ SliceEnergy g / 2 + Real.pi / 4 := by
    have h6 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 1 / 2)
    have h7 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith
  linarith [h1, h5]

/-- The remainder estimate: the integral defining the Taylor remainder is bounded by
`(π/2) (E/2 + π/4)` in either order. -/
theorem sliceRemainder_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {a θ : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |∫ t in a..θ, (θ - t) * deriv (deriv g) t|
      ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
  have hstep : ∀ u v : ℝ, 0 < u → u ≤ v → v < Real.pi / 2 →
      ∫ t in Set.Ioc u v, |(θ - t) * deriv (deriv g) t|
        ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
    intro u v hu huv hv
    have hcu : ContinuousOn (deriv (deriv g)) (Set.uIcc u v) := by
      rw [Set.uIcc_of_le huv]
      exact (sliceContDiff2 hg).mono fun t ht =>
        ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hv⟩
    calc ∫ t in Set.Ioc u v, |(θ - t) * deriv (deriv g) t|
        = ∫ t in Set.Ioc u v, |θ - t| * |deriv (deriv g) t| := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
          rw [abs_mul]
      _ = ∫ t in u..v, |θ - t| * |deriv (deriv g) t| :=
          (intervalIntegral.integral_of_le huv).symm
      _ ≤ ∫ t in u..v, (Real.pi / 2) * |deriv (deriv g) t| := by
          refine intervalIntegral.integral_mono_on huv ?_ ?_ fun t ht => ?_
          · exact (((continuousOn_const.sub continuousOn_id).abs).mul hcu.abs).intervalIntegrable
          · exact (continuousOn_const.mul hcu.abs).intervalIntegrable
          · have ht' : t ∈ Set.Icc 0 (Real.pi / 2) :=
              ⟨by linarith [hu, ht.1], by linarith [ht.2, hv, Real.pi_pos]⟩
            have hb : |θ - t| ≤ Real.pi / 2 := by
              rw [abs_sub_le_iff]
              exact ⟨by linarith [ht'.1, hθ.2, Real.pi_pos],
                by linarith [ht'.2, hθ.1, Real.pi_pos]⟩
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = Real.pi / 2 * ∫ t in u..v, |deriv (deriv g) t| :=
          intervalIntegral.integral_const_mul (Real.pi / 2) _
      _ ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) :=
          mul_le_mul_of_nonneg_left (sliceAbsDeriv_le hg hE hu huv hv)
            (by linarith [Real.pi_pos])
  rcases le_total a θ with h | h
  · rw [intervalIntegral.integral_of_le h]
    refine le_trans ?_ (hstep a θ ha.1 h hθ.2)
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a θ))
        (f := fun t => (θ - t) * deriv (deriv g) t))
  · rw [intervalIntegral.integral_of_ge h]
    have h1 : |∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t|
        ≤ ∫ t in Set.Ioc θ a, |(θ - t) * deriv (deriv g) t| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc θ a))
          (f := fun t => (θ - t) * deriv (deriv g) t))
    calc |-(∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t)|
        = |∫ t in Set.Ioc θ a, (θ - t) * deriv (deriv g) t| := by rw [abs_neg]
      _ ≤ ∫ t in Set.Ioc θ a, |(θ - t) * deriv (deriv g) t| := h1
      _ ≤ Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := hstep θ a hθ.1 h ha.2

/-- **The pointwise slice estimate.** -/
theorem sliceAbs_le {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |g θ| ≤ |g (Real.pi / 4)| + Real.pi / 2 * |deriv g (Real.pi / 4)|
      + Real.pi / 2 * (SliceEnergy g / 2 + Real.pi / 4) := by
  have ha : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hT := sliceTaylor hg ha hθ
  have hT' : g θ = g (Real.pi / 4) + (θ - Real.pi / 4) * deriv g (Real.pi / 4)
      + ∫ t in Real.pi / 4..θ, (θ - t) * deriv (deriv g) t := by linarith [hT]
  have h1 : |g θ| ≤ |g (Real.pi / 4)| + |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
      + |∫ t in Real.pi / 4..θ, (θ - t) * deriv (deriv g) t| := by
    rw [hT']
    exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  have h2 : |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
      ≤ Real.pi / 2 * |deriv g (Real.pi / 4)| := by
    rw [abs_mul]
    have hb : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      have hb' : |θ - Real.pi / 4| < Real.pi / 4 := by
        rw [abs_lt]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      linarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have h3 := sliceRemainder_le hg hE ha hθ
  linarith [h1, h2, h3]

/-- The energy is nonnegative under the integrability hypothesis. -/
theorem SliceEnergy_nonneg {g : ℝ → ℝ}
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) : 0 ≤ SliceEnergy g := by
  rw [SliceEnergy]
  exact integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)))

/-- **The `θ`-slice bound.**  For `g` of class `C²` on `(0,π/2)` with finite weighted energy,
`θ ↦ g θ · sinθcos²θ` is integrable on `Iθ`, and
`∫_θ |g θ| sinθcos²θ dθ ≤ 4 + 4|g(π/4)| + 4|g'(π/4)| + 2 E` with
`E = ∫_θ (g'')² sin(2θ)^{-η}`. -/
theorem sliceMomentLinear {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) :
    IntegrableOn (fun θ => g θ * sg θ) Iθ ∧
      ∫ θ in Iθ, |g θ| * sg θ ≤ 4 + 4 * |g (Real.pi / 4)| + 4 * |deriv g (Real.pi / 4)|
        + 2 * SliceEnergy g := by
  have hσcont : Continuous sg := by unfold Work.Elliptic.sinCos2; fun_prop
  have hσint : IntegrableOn sg Iθ :=
    hσcont.continuousOn.integrableOn_compact isCompact_Icc
  -- the `θ`-mass of `Iθ` is `π/2`
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : ∫ θ in Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    simp
  have hσmass : ∫ θ in Iθ, sg θ ≤ Real.pi / 2 := by
    rw [← hvol]
    exact MeasureTheory.integral_mono_ae hσint hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => sg_le_one hθ))
  -- almost everywhere interior on `Iθ`
  have hae : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      rw [Set.mem_setOf_eq] at hθ
      push_neg at hθ
      obtain ⟨hmem, hnot⟩ := hθ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases h0 : θ = 0
      · exact Or.inl h0
      · refine Or.inr ?_
        by_contra hpi
        exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hpi⟩
    · have hset : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      rw [hset]
      exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton _)
  set E := SliceEnergy g with hEdef
  set A := |g (Real.pi / 4)| with hAdef
  set B := |deriv g (Real.pi / 4)| with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hB0 : 0 ≤ B := by rw [hBdef]; exact abs_nonneg _
  have hE0 : 0 ≤ E := SliceEnergy_nonneg hE
  -- the pointwise estimate, and its `sg`-weighted version
  have hbound : ∀ᵐ θ ∂(volume.restrict Iθ),
      |g θ| ≤ A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4) := by
    filter_upwards [hae] with θ hθ
    simpa only [hAdef, hBdef, hEdef] using sliceAbs_le hg hE hθ
  have hbounded : ∀ᵐ θ ∂(volume.restrict Iθ),
      ‖g θ * sg θ‖ ≤ (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ := by
    filter_upwards [hbound, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
      with θ hb hm
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sg_nonneg hm)]
    exact mul_le_mul_of_nonneg_right hb (sg_nonneg hm)
  have hC : IntegrableOn
      (fun θ : ℝ => (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ) Iθ :=
    hσint.const_mul _
  have hmeas : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      ((MeasureTheory.Ioo_ae_eq_Icc' (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton _)).symm)
  have haesm : AEStronglyMeasurable (fun θ => g θ * sg θ) (volume.restrict Iθ) := by
    rw [hmeas]
    exact (hg.continuousOn.mul hσcont.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hsl : IntegrableOn (fun θ => g θ * sg θ) Iθ :=
    Integrable.mono' hC haesm hbounded
  refine ⟨hsl, ?_⟩
  have hsl' : Integrable (fun θ => |g θ| * sg θ) (volume.restrict Iθ) :=
    hsl.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hm => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sg_nonneg hm)]))
  have hmono : ∫ θ in Iθ, |g θ| * sg θ
      ≤ ∫ θ in Iθ, (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * sg θ :=
    MeasureTheory.integral_mono_ae hsl' hC
      (by filter_upwards [hbound, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
            with θ hb hm
          exact mul_le_mul_of_nonneg_right hb (sg_nonneg hm))
  rw [MeasureTheory.integral_const_mul] at hmono
  have hC0 : 0 ≤ A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4) := by positivity
  have hmm : (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (∫ θ in Iθ, sg θ)
      ≤ (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left hσmass hC0
  have hexp : (A + Real.pi / 2 * B + Real.pi / 2 * (E / 2 + Real.pi / 4)) * (Real.pi / 2)
      = (Real.pi / 2) * A + (Real.pi ^ 2 / 4) * B + (Real.pi ^ 2 / 8) * E + Real.pi ^ 3 / 16 := by
    ring
  have h1 : (Real.pi / 2) * A ≤ 4 * A := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    linarith [Real.pi_lt_four]
  have h2 : (Real.pi ^ 2 / 4) * B ≤ 4 * B := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h3 : (Real.pi ^ 2 / 8) * E ≤ 2 * E := by
    refine mul_le_mul_of_nonneg_right ?_ hE0
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h4 : Real.pi ^ 3 / 16 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  rw [hexp] at hmm
  rw [hAdef, hBdef, hEdef]
  linarith [hmono, hmm, h1, h2, h3, h4]

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.radialIbpZeroOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration-by-parts identity on the open half-strip

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.radial_ibp_zero`: the smoothness
hypothesis is `C³` on the **open** half-strip `qd = (0,∞) × (0,π/2)` (only the open quadrant, as
in the almost-everywhere class `H2W.Ae.AeData`) instead of on a neighbourhood of the closed
quadrant, and the conclusion is stated for `θ ∈ (0,π/2)` — which is an almost-everywhere subset
of the full angular interval `Iθ = [0,π/2]`.

For a `C³` function `Φ` on the open half-strip whose `z`-support is contained in a compact
interval `[a,b] ⊂ (0,∞)` (for **every** angle `θ`, hypothesis `hsupp`), and for every
`θ ∈ (0,π/2)`, the integral over `z > 0` of

  `∂_z [ z² · ∂_z Φ(z,θ) · w(z)² · ∂_θ²Φ(z,θ) ] · sin(2θ)^{-η}`

vanishes (with `w(z) = (1+z)²/z²`, `η > 0` arbitrary).

The proof is the one of the sibling file, with the two open sets replaced: the pointwise
identifications `∂_zΦ = ribpPz`, `∂_θ²Φ = ribpPth2` hold on `qd`, which is all the support and
smoothness arguments use.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false

/-! ## The partial derivatives of `Φ` as Fréchet-derivative directions -/





/-! ## Elementary helpers -/


/-! ## The smoothness of `pz Φ`, `pth Φ` and `pth² Φ` from the joint `C³` hypothesis -/




/-! ## The pointwise identifications of the iterated partial derivatives -/



/-! ## The main statement -/


end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.hardy_sinWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-!
# Weighted Hardy inequality on `Iθ` with the weight `sin(2θ)^{-η}`

For `0 < η ≤ 2` and `u : ℝ → ℝ` of class `C¹` on `[0,π/2]` vanishing at both endpoints,

  `∫_{Iθ} u(θ)² sin(2θ)^{-η} dθ ≤ π²/4 ∫_{Iθ} (u')(θ)² dθ  ≤ 10 ∫_{Iθ} (u')(θ)² dθ`.

The proof splits `Iθ` at `π/4`.  On each half the weight `sin(2θ)^{-η}` is dominated by
`(π²/16) t^{-2}`, where `t = θ` on the left and `t = π/2 - θ` on the right (Jordan's
inequality `sin x ≥ (2/π)x` together with `η ≤ 2`), and the sharp power Hardy inequality
`Work.Elliptic.power_hardy` at `η = 0` (constant `4`) on each half gives the result with the
constant `π²/4 ≈ 2.467`.
-/

/-! ## Elementary trigonometric bounds -/

/-- Jordan's inequality on the left half: `(4/π) θ ≤ sin (2θ)` for `0 ≤ θ ≤ π/4`. -/
private lemma four_div_pi_mul_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h2 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) h2
  calc (4 / Real.pi) * θ = (2 / Real.pi) * (2 * θ) := by ring
    _ ≤ Real.sin (2 * θ) := h



/-! ## Comparison of the weight with the power weight on each half -/



/-! ## The Hardy estimate on the left half -/


/-! ## Interval integrability of the two integrands on both halves -/



/-! ## The Hardy estimate on the right half, by reflection -/


/-! ## The target -/


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `z²∂_z²` commutes with the iterated `D_z = z∂_z`

The identity `z²∂_z² = D_z² − D_z` shows that `z²∂_z²` is a polynomial in `D_z = z∂_z`,
hence commutes with every power of `D_z`:

`z²·pzIter 2 (DzIter j f) = DzIter j (z²·pzIter 2 f)`   (pointwise, when the iterates
are differentiable at the point under consideration).

This is the observation `(op)` of `Submission/Work/FTS/EllipticEst/H2W/NOTES_mixedA.md`: it
identifies the pure (radial) part of the `ℋ²`-norm of `z²∂_z²Ψ` and hence turns
`H2W/mixedA` into a statement about the three *mixed* slots of `A = z²∂_z²Ψ`.

The statement holds for a *fixed* angle `θ` at *every* `z ∈ ℝ` (also `z ≤ 0`; at `z = 0`
both sides vanish), the only input being that each iterate `∂_z^i f(·,θ)` is differentiable
at every point (hypothesis `h1`; `h2` is its own `i+1` case — `deriv (fun z'' => pzIter i f
z'' θ) = fun z'' => pzIter (i+1) f z'' θ` definitionally — and is therefore redundant).
Under `h1` the angle slice `z ↦ f z θ` is `C^∞`, which is all the proof needs: the
`C^∞`-slices of the iterates `D_z^j f` are differentiable, so the pointwise operator
identity `z²∂_z² = D_z² − D_z` holds at every point and the induction on `j` goes through.

The file is deliberately self-contained: its whole import closure is verified (the pointwise
operator identity is reproved here under the local name `zsq_pzIter2_slice_eq` rather than
imported from `H2W/mixedA`).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology ContDiff
open Set Filter

set_option autoImplicit false

/-! ## The angle slice is `C^∞` -/



/-! ## The pointwise operator identity `z²∂_z² = D_z² − D_z` -/




/-! ## The commutation -/


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonAuxIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts on the open interval `Iθo = (0, π/2)` -/

private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sub_pi_div_two_pos {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.pi / 2 - θ := by
  linarith [hθ.2, Real.pi_pos]

/-- Jordan's inequality in the form `(4/π) min θ (π/2 - θ) ≤ sin (2θ)` on `Iθo`. -/
private lemma four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Iθo) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]
    exact sin_two_ge_four_div_pi_mul θ hθ.1.le (by linarith [hθ.2, h])
  · rw [min_eq_right h]
    exact sin_two_ge_four_div_pi_mul_sub θ (by linarith [hθ.1, h]) hθ.2

/-- The singular weight is dominated by the `min` of the two endpoint powers. -/
private lemma sin_two_rpow_le_min {p θ : ℝ} (hp : 0 < p) (hθ : θ ∈ Iθo) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (Real.pi / 4) ^ p * (min θ (Real.pi / 2 - θ)) ^ (-p) := by
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 (sub_pi_div_two_pos hθ)
  have hbase : 0 < 4 / Real.pi * min θ (Real.pi / 2 - θ) := mul_pos (by positivity) hm0
  have key : (Real.sin (2 * θ)) ^ (-p) ≤ (4 / Real.pi * min θ (Real.pi / 2 - θ)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hbase (four_div_pi_mul_min_le_sin_two hθ) (by linarith)
  have hcoef : (4 / Real.pi : ℝ) ^ (-p) = (Real.pi / 4) ^ p := by
    have hp4 : (0 : ℝ) < 4 / Real.pi := by positivity
    rw [Real.rpow_neg (le_of_lt hp4), ← Real.inv_rpow (le_of_lt hp4), inv_div]
  rwa [Real.mul_rpow (le_of_lt (by positivity : (0 : ℝ) < 4 / Real.pi)) (le_of_lt hm0),
    hcoef] at key

/-- `sig η θ ≤ (π/4)^η (θ^{-η} + (π/2 - θ)^{-η})` on `Iθo` for `η ≥ 0`. -/
private lemma sig_le_majorant {η : ℝ} (hη0 : 0 ≤ η) {θ : ℝ} (hθ : θ ∈ Iθo) :
    sig η θ ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hd0 := sub_pi_div_two_pos hθ
  have hminle : (min θ (Real.pi / 2 - θ)) ^ (-η)
      ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hd0.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
  rcases eq_or_lt_of_le hη0 with h0 | hpos
  · rw [← h0]
    have hsig0 : sig 0 θ = 1 := by simp only [sig, neg_zero, Real.rpow_zero]
    have hrhs : (Real.pi / 4) ^ (0 : ℝ)
        * (θ ^ (-(0 : ℝ)) + (Real.pi / 2 - θ) ^ (-(0 : ℝ))) = 2 := by
      simp only [neg_zero, Real.rpow_zero]
      norm_num
    rw [hsig0, hrhs]
    norm_num
  · calc sig η θ = (Real.sin (2 * θ)) ^ (-η) := rfl
      _ ≤ (Real.pi / 4) ^ η * (min θ (Real.pi / 2 - θ)) ^ (-η) :=
          sin_two_rpow_le_min hpos hθ
      _ ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left hminle (Real.rpow_nonneg (by positivity) _)

/-! ## The pointwise bounds for the two integrands -/

/-- Bound for the first integrand: only the right-hand endpoint hypothesis is used, together
with `cos θ = sin (π/2 - θ) ≥ (2/π)(π/2 - θ)`. -/
private lemma F1_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (_hC : 0 ≤ C)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)| ≤
      (1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η)
        * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have ha : 0 ≤ 1 / 2 * (1 - η) := by linarith
  have hsg : 0 ≤ sig η θ := Real.rpow_nonneg (le_of_lt (sin_two_pos_Iθo hθ)) _
  -- `u² ≤ C² δ²`
  have hu2 : (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb2 θ hθ) 2
    rw [sq_abs] at h
    calc (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := h
      _ = C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by ring
  -- `δ ≤ (π/2) cos θ`
  have hδle : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
    have hmul : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
      have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (le_of_lt hδ0)
        (by linarith [Real.pi_pos, hθ.1])
      rwa [Real.sin_pi_div_two_sub] at h
    have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by
      have h2 : (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ := (inv_div Real.pi 2).symm
      rw [h2, mul_inv_cancel₀ (by positivity : (Real.pi / 2) ≠ 0)]
    have h1 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    rwa [← mul_assoc, hpi, one_mul] at h1
  have hδsq : (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2) ^ 2 * Real.cos θ ^ 2 := by
    have h := pow_le_pow_left₀ hδ0.le hδle 2
    rwa [mul_pow] at h
  -- `u² / cos²θ ≤ C² (π/2)²`
  have hcq : (u θ) ^ 2 / Real.cos θ ^ 2 ≤ C ^ 2 * (Real.pi / 2) ^ 2 := by
    rw [div_le_iff₀ (pow_pos hcos 2)]
    calc (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := hu2
      _ ≤ C ^ 2 * ((Real.pi / 2) ^ 2 * Real.cos θ ^ 2) :=
          mul_le_mul_of_nonneg_left hδsq (sq_nonneg C)
      _ = C ^ 2 * (Real.pi / 2) ^ 2 * Real.cos θ ^ 2 := by ring
  have hstep : (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2)
      ≤ (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) := by
    calc (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2)
        = (1 / 2 * (1 - η)) * ((u θ) ^ 2 / Real.cos θ ^ 2) := by ring
      _ ≤ (1 / 2 * (1 - η)) * (C ^ 2 * (Real.pi / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hcq ha
      _ = (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) := by ring
  have hnn : 0 ≤ (C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)) :=
    mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) ha
  have habs : |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)|
      = (u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2) :=
    abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hsg)
      (div_nonneg ha (pow_pos hcos 2).le))
  calc |(u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)|
      = (u θ) ^ 2 * (1 / 2 * (1 - η) / Real.cos θ ^ 2) * sig η θ := by
        rw [habs]; ring
    _ ≤ ((C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η))) * sig η θ :=
        mul_le_mul_of_nonneg_right hstep hsg
    _ ≤ ((C ^ 2 * (Real.pi / 2) ^ 2) * (1 / 2 * (1 - η)))
          * ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) :=
        mul_le_mul_of_nonneg_left (sig_le_majorant hη0 hθ) hnn
    _ = (1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η)
          * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring

/-- Bound for the second integrand, using the `min` form of both endpoint bounds. -/
private lemma F2_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2| ≤
      (C ^ 2 * (Real.pi / 4) ^ (η + 2)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_Iθo hθ
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 hδ0
  -- `u² ≤ C² min(θ, δ)²`
  have hu2 : (u θ) ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
    have h1 : (u θ) ^ 2 ≤ C ^ 2 * θ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb1 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * θ) ^ 2 := h
        _ = C ^ 2 * θ ^ 2 := by ring
    have h2 : (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb2 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := h
        _ = C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by ring
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2
  have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_le_one (2 * θ), Real.neg_one_le_cos (2 * θ)]
  have hsinp : (Real.sin (2 * θ)) ^ (-(η + 2))
      ≤ (Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2)) :=
    sin_two_rpow_le_min (by linarith) hθ
  have hdiv : sig η θ / (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (-(η + 2)) := by
    rw [div_eq_iff (by positivity : (Real.sin (2 * θ)) ^ 2 ≠ 0), sig]
    rw [← Real.rpow_natCast (Real.sin (2 * θ)) 2, ← Real.rpow_add hs0]
    congr 1
    ring
  have hmpow : (min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))
      = (min θ (Real.pi / 2 - θ)) ^ (-η) := by
    rw [← Real.rpow_natCast (min θ (Real.pi / 2 - θ)) 2, ← Real.rpow_add hm0]
    congr 1
    ring
  have hmle : (min θ (Real.pi / 2 - θ)) ^ (-η)
      ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hδ0.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
  have hstep : (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))
      ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1
        * ((Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := by
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(η + 2)) := Real.rpow_nonneg hs0.le _
    have h2 : 0 ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1 :=
      mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) zero_le_one
    exact mul_le_mul
      (mul_le_mul hu2 hcos2 (sq_nonneg _) (mul_nonneg (sq_nonneg C) (sq_nonneg _)))
      hsinp h1 h2
  have hsg : 0 ≤ sig η θ := Real.rpow_nonneg hs0.le _
  have hnn : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have habs : |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2|
      = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2 :=
    abs_of_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsg) (pow_pos hs0 2).le)
  calc |(u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2|
      = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2 := habs
    _ = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (sig η θ / (Real.sin (2 * θ)) ^ 2) := by
        ring
    _ = (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2)) := by
        rw [hdiv]
    _ ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) * 1
          * ((Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := hstep
    _ = C ^ 2 * (Real.pi / 4) ^ (η + 2)
          * ((min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(η + 2))) := by
        ring
    _ = C ^ 2 * (Real.pi / 4) ^ (η + 2) * (min θ (Real.pi / 2 - θ)) ^ (-η) := by rw [hmpow]
    _ ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
        mul_le_mul_of_nonneg_left hmle hnn

/-! ## Continuity of the two integrands -/

private lemma continuousOn_F1 (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2))
      Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsig : ContinuousOn (sig η) Iθo :=
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Iθo from
      hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  have hden : ContinuousOn (fun θ : ℝ => (1 / 2 * (1 - η)) / Real.cos θ ^ 2) Iθo :=
    continuous_const.continuousOn.div (Real.continuous_cos.continuousOn.pow 2)
      (fun θ hθ => by
        have hc : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
        exact (pow_pos hc 2).ne')
  exact ((hu.pow 2).mul hsig).mul hden

private lemma continuousOn_F2 (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ
      / (Real.sin (2 * θ)) ^ 2) Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Iθo :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hsig : ContinuousOn (sig η) Iθo :=
    show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Iθo from
      hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  have hnum : ContinuousOn
      (fun θ : ℝ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ) Iθo :=
    ((hu.pow 2).mul (hcos2.pow 2)).mul hsig
  exact hnum.div (hsin2.pow 2) (fun θ hθ => (pow_pos (sin_two_pos_Iθo hθ) 2).ne')

/-! ## The theorem -/

theorem HonAuxIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousOn u Work.FTS.EllipticEst.Honest.Iθo)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ
          * (1 / 2 * (1 - η) / Real.cos θ ^ 2)) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ
          / (Real.sin (2 * θ)) ^ 2) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume := by
  have hK1 : 0 ≤ 1 / 2 * (1 - η) * C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η := by
    have ha : 0 ≤ 1 / 2 * (1 - η) := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg ha (sq_nonneg C)) (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  have hK2 : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (η + 2) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  constructor
  · have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK1
      (continuousOn_F1 u η hu) (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact F1_bound u η C hη0 hη1 hC hb2 hθ)
    simpa [Iθo] using h.mono_set Ioo_subset_Icc_self
  · have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK2
      (continuousOn_F2 u η hu) (fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact F2_bound u η C hη0 hC hb1 hb2 hθ)
    simpa [Iθo] using h.mono_set Ioo_subset_Icc_self

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonPrimitiveTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-!
# The primitive `θ ↦ -(u'·u·σ + η·u²·ρ) + ½ tan θ·u²·σ` vanishes at both endpoints

`Work.FTS.EllipticEst.Honest.SliceBoundary` already shows that

* `sig η θ * u θ * deriv u θ → 0`   (i.e. `u' u σ → 0`) and
* `rho η θ * u θ ^ 2 → 0`           (i.e. `η u² ρ → 0`, since `sigD η = -2η ρ`)

at `θ → 0⁺` and at `θ → π/2⁻`, for a slice bound `|u θ| ≤ min (C θ) (C (π/2 - θ))` and a
bounded derivative `|u' θ| ≤ C`, when `0 ≤ η < 1`.  The remaining third summand is the
`tan`-weighted one, `½ tan θ · u² · σ η θ`, and that is what this file bounds: near `0` we
have `tan θ ≤ 1`, while near `π/2` we have `tan θ ≤ (π/2 - θ)⁻¹` (`tan (π/2 - t) = 1/tan t`
and `tan t ≥ t`).  So on the appropriate half of the interval,

`|tan θ · u² · σ η θ| ≤ C² (4/π)^{-η} · t^{1-η}`  with `t = θ` resp. `t = π/2 - θ`,

using `sin (2θ) ≥ (4/π) t` (`sin_two_ge_four_div_pi_mul` / `sin_two_ge_four_div_pi_mul_sub`)
and `η < 1` for `t^{1-η} → 0`.
-/

/-- Two `rpow` bookkeeping identities used below (for `x > 0`):

`x^{-η} · x² = x^{1-η} · x` and `x⁻¹ · (x^{1-η} · x) = x^{1-η}`. -/
theorem rpow_neg_mul_sq (x : ℝ) (hx : 0 < x) (η : ℝ) : x ^ (-η) * x ^ 2 = x ^ (1 - η) * x := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
  conv_rhs => enter [2]; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- For `x > 0`, `x⁻¹ · (x^{1-η} · x) = x^{1-η}`. -/
theorem inv_mul_rpow_mul_self (x : ℝ) (hx : 0 < x) (η : ℝ) :
    x⁻¹ * (x ^ (1 - η) * x) = x ^ (1 - η) := by
  rw [show x⁻¹ * (x ^ (1 - η) * x) = x ^ (1 - η) * (x⁻¹ * x) by ring,
    inv_mul_cancel₀ (ne_of_gt hx), mul_one]

/-- On `(0, π/4)`, `tan θ ≤ 1` (equivalently `tan θ < 1`, `tan` being increasing). -/
theorem abs_tan_le_one_of_lt_pi_div_four {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 4) :
    |Real.tan θ| ≤ 1 := by
  have hpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two h0 (by linarith [Real.pi_pos])
  rw [abs_of_pos hpos]
  have h := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two (x := θ) (y := Real.pi / 4)
    (le_of_lt h0) (by linarith [Real.pi_pos]) h1
  rw [Real.tan_pi_div_four] at h
  exact le_of_lt h

/-- On `[π/4, π/2)`, `tan θ ≤ (π/2 - θ)⁻¹`. -/
theorem abs_tan_le_inv_of_le_pi_div_four {θ : ℝ} (h0 : Real.pi / 4 ≤ θ)
    (h1 : θ < Real.pi / 2) : |Real.tan θ| ≤ (Real.pi / 2 - θ)⁻¹ := by
  have hpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [Real.pi_pos]) h1
  rw [abs_of_pos hpos]
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have htl : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have heq : Real.tan θ = (Real.tan (Real.pi / 2 - θ))⁻¹ := by
    conv_lhs => rw [show θ = Real.pi / 2 - (Real.pi / 2 - θ) by ring, Real.tan_pi_div_two_sub]
  rw [heq]
  have h := one_div_le_one_div_of_le ht0 (le_of_lt (Real.lt_tan ht0 htl))
  simpa [one_div] using h

/-- `|sig η θ| ≤ (4/π)^{-η} t^{-η}` whenever `0 < t`, `0 < sin (2θ)` and `(4/π) t ≤ sin (2θ)`
(the pointwise form of the bound via `Real.rpow_le_rpow_of_nonpos`). -/
theorem abs_sig_le_rpow {η θ t : ℝ} (hη0 : 0 ≤ η) (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) :
    |sig η θ| ≤ (4 / Real.pi) ^ (-η) * t ^ (-η) := by
  simp only [sig]
  rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
  calc Real.sin (2 * θ) ^ (-η) ≤ ((4 / Real.pi) * t) ^ (-η) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hge (by linarith)
    _ = (4 / Real.pi) ^ (-η) * t ^ (-η) := Real.mul_rpow (by positivity) (le_of_lt ht0)

/-! ## The `tan`-weighted term tends to `0` at the two endpoints -/

/-- `tan θ · u θ² · σ η θ → 0` as `θ → 0⁺`, under `|u θ| ≤ C θ` and `0 ≤ η < 1`. -/
theorem tendsto_tan_mul_sig_mul_sq_nhdsGT_zero (η C : ℝ) (u : ℝ → ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (_hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ) :
    Filter.Tendsto (fun θ => Real.tan θ * sig η θ * u θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4) * θ ^ (1 - η))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ < Real.pi / 4 := Set.mem_Iio.mp hθ1
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  have htan := abs_tan_le_one_of_lt_pi_div_four h0 h1
  have hsig := abs_sig_le_rpow (η := η) (θ := θ) (t := θ) hη0 h0 hsin
    (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) (le_of_lt h1))
  have hu2 : |u θ| ^ 2 ≤ (C * θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb1 θ hθI) 2
  have hq := rpow_neg_mul_sq θ h0 η
  calc |Real.tan θ * sig η θ * u θ ^ 2|
      = |Real.tan θ| * |sig η θ| * |u θ| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
    _ ≤ 1 * ((4 / Real.pi) ^ (-η) * θ ^ (-η)) * (C * θ) ^ 2 := by
        refine mul_le_mul (mul_le_mul htan hsig (abs_nonneg _) (by positivity)) hu2
          (by positivity) (by positivity)
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (-η) * θ ^ 2) := by ring
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (1 - η) * θ) := by rw [hq]
    _ ≤ C ^ 2 * (4 / Real.pi) ^ (-η) * (θ ^ (1 - η) * (Real.pi / 4)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_of_lt h1) ?_) ?_
        · exact Real.rpow_nonneg (le_of_lt h0) _
        · positivity
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 4) * θ ^ (1 - η) := by ring

/-- `tan θ · u θ² · σ η θ → 0` as `θ → π/2⁻`, under `|u θ| ≤ C (π/2 - θ)` and `0 ≤ η < 1`. -/
theorem tendsto_tan_mul_sig_mul_sq_nhdsLT_pi_div_two (η C : ℝ) (u : ℝ → ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (_hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    Filter.Tendsto (fun θ => Real.tan θ * sig η θ * u θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have htan := abs_tan_le_inv_of_le_pi_div_four h0 h1
  have hsig := abs_sig_le_rpow (η := η) (θ := θ) (t := Real.pi / 2 - θ) hη0 ht0 hsin
    (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
  have hu2 : |u θ| ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hb2 θ hθI) 2
  have hq := rpow_neg_mul_sq (Real.pi / 2 - θ) ht0 η
  have hinv := inv_mul_rpow_mul_self (Real.pi / 2 - θ) ht0 η
  calc |Real.tan θ * sig η θ * u θ ^ 2|
      = |Real.tan θ| * |sig η θ| * |u θ| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]
    _ ≤ (Real.pi / 2 - θ)⁻¹ * ((4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (-η))
          * (C * (Real.pi / 2 - θ)) ^ 2 := by
        refine mul_le_mul (mul_le_mul htan hsig (abs_nonneg _) (by positivity)) hu2
          (by positivity) (by positivity)
    _ = C ^ 2 * (4 / Real.pi) ^ (-η)
          * ((Real.pi / 2 - θ)⁻¹ * ((Real.pi / 2 - θ) ^ (-η) * (Real.pi / 2 - θ) ^ 2)) := by
        ring
    _ = C ^ 2 * (4 / Real.pi) ^ (-η)
          * ((Real.pi / 2 - θ)⁻¹ * ((Real.pi / 2 - θ) ^ (1 - η) * (Real.pi / 2 - θ))) := by
        rw [hq]
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η) := by rw [hinv]

/-! ## The main statement -/

theorem HonPrimitiveTendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv u θ| ≤ C) :
    Filter.Tendsto (fun θ => - deriv u θ * u θ * Work.FTS.EllipticEst.Honest.sig η θ
        + (1 / 2) * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => - deriv u θ * u θ * Work.FTS.EllipticEst.Honest.sig η θ
        + (1 / 2) * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * Work.FTS.EllipticEst.Honest.sig η θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨hA1, hA2, hB1, hB2⟩ := SliceBoundary u η C hη0 hη1 hC hb1 hb2 hb3
  have hG1 := tendsto_tan_mul_sig_mul_sq_nhdsGT_zero η C u hη0 hη1 hC hb1
  have hG2 := tendsto_tan_mul_sig_mul_sq_nhdsLT_pi_div_two η C u hη0 hη1 hC hb2
  constructor
  · have hc := (hA1.neg.sub (hB1.const_mul η)).add (hG1.const_mul (1 / 2))
    simp only [neg_zero, mul_zero, sub_zero, add_zero] at hc
    refine Filter.Tendsto.congr' ?_ hc
    filter_upwards with θ
    simp only [sigD_eq_neg_two_mul_rho]
    ring
  · have hc := (hA2.neg.sub (hB2.const_mul η)).add (hG2.const_mul (1 / 2))
    simp only [neg_zero, mul_zero, sub_zero, add_zero] at hc
    refine Filter.Tendsto.congr' ?_ hc
    filter_upwards with θ
    simp only [sigD_eq_neg_two_mul_rho]
    ring

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

/-- `λ_n = 4(n-1)² + 10(n-1)`, the `n`-th eigenvalue of the angular operator (in `ℕ`, cast to `ℝ`). -/
def eigLamNat (n : ℕ) : ℕ := 4 * (n - 1) ^ 2 + 10 * (n - 1)

/-- The eigenvalue `λ_n` as a real number. -/
def eigLam (n : ℕ) : ℝ := (eigLamNat n : ℝ)

/-- The coefficients of the eigenpolynomial: `c_{k+1}/c_k = (4k²+10k-λ_n)/((2k+3)(2k+2))`,
`c_0 = 1`. -/
def eigCoef (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => eigCoef n k * ((4 * (k : ℝ) ^ 2 + 10 * (k : ℝ) - eigLam n)
      / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)))

@[simp] theorem eigCoef_zero (n : ℕ) : eigCoef n 0 = 1 := rfl

/-- `p_n(u) = Σ_{k<n} c_k u^{2k+1}`. -/
def eigPoly (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, eigCoef n k * u ^ (2 * k + 1)


@[simp] theorem eigLam_one : eigLam 1 = 0 := by
  simp [eigLam, eigLamNat]








end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LzeroSingDefs =====
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



/-- The **regular solution of `Lzero`**: `θ ↦ sin 2θ`. -/
def LzeroReg (θ : ℝ) : ℝ := Real.sin (2 * θ)

@[simp] theorem LzeroReg_apply (θ : ℝ) : LzeroReg θ = Real.sin (2 * θ) := rfl



/-! ## The two Dirichlet values of the singular solution

The class of `Work.FTS.EllipticEst.l2etaWeakFts` prescribes the *values* `Ψ(·,0) = 0` and
`Ψ(·,π/2) = 0` (and smoothness only on the **open** quadrant), so a function may vanish at both
angular endpoints as a value while blowing up like `1/t` in the limit `θ → π/2⁻`.  `LzeroSing`
is exactly such a function: this is what makes the class genuinely bigger than the class of the
paper's estimates, and it is why the "pole coefficient" (the coefficient of `LzeroSing` in a
solution) is the right singular datum. -/



/-! ## `LzeroSing` in the vocabulary of the project

`Work.Elliptic.Lzero` is stated for two-variable functions; applied to the `z`-independent
extension `fun _ τ => LzeroSing τ` it is the one-variable expression of the companion modules.
This unfolding is definitional, and lets consumers (`Work.Elliptic.Lzero`, the pole-coefficient
split, the elliptic estimates) use `LzeroSingODE` directly. -/


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.SmoothIntSliceDifferentiableAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.CutoffPieces


end Work.FTS.EllipticEst.Mine.CutoffPieces
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.SliceMomentTaylor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The slice moment/Taylor estimate `∫_{Iθ} |g| sinθcos²θ ≤ 3|g(π/4)| + 9|g'(π/4)| + 9√(∫|g''|²sin(2θ)^{-η})`

For `g` of class `C²` on the open angular interval `(0, π/2)` whose weighted second
derivative `g'' · sin(2θ)^{-η/2}` is square integrable on `Iθ = [0, π/2]`
(`η = 99/100`), the slice `g` is integrable against the solvability weight
`sin θ cos²θ`, and

`∫_{Iθ} |g θ| sinθcos²θ ≤ 3 |g(π/4)| + 9 |g'(π/4)| + 9 √(∫_{Iθ} g''(θ)² sin(2θ)^{-η})`.

## Route

* **Taylor with integral remainder** (`TaylorRemainderIoo`): for `g` of class `C²` on an open
  interval and `a, θ` in it, `g θ = g a + (θ-a)g'(a) + ∫_a^θ (θ-s) g''(s) ds` (FTC applied to
  `s ↦ (θ-s)g'(s) + g(s)`, whose derivative is `(θ-s)g''(s)`; no orientation split is needed
  because Mathlib's interval integral is oriented).
* **Weighted Cauchy–Schwarz** (`abs_intervalIntegral_mul_le`): on a compact subinterval
  `[c,d] ⊆ (0,π/2)` where `sin(2s) > 0`, split `(θ-s)h(s)` as
  `(|θ-s| sin(2s)^{η/2}) · (|h(s)| sin(2s)^{-η/2})` and apply Cauchy–Schwarz
  (`Work.Blocks.IMC.cs_integral_mul_le`) over `Icc c d`; monotonicity of the set integral
  (`setIntegral_mono_set`) replaces `Icc c d` by `Iθ` in both factors.
* **Kernel bound** (`integral_sq_mul_sin_two_rpow_le_eight`): since `|θ - s| ≤ π/2` and
  `sin(2s)^η ≤ 1` on `Iθ`,
  `∫_{Iθ} (θ-s)² sin(2s)^η ≤ (π/2)² · (π/2) = (π/2)³ ≤ 8` (using `π < 4`).
* **Assembly**: `|g θ| ≤ M := |g(π/4)| + (π/2)|g'(π/4)| + √8·√N` on `(0,π/2)`, where
  `N = ∫_{Iθ} g''² sin(2θ)^{-η}`; multiplying by `sinθcos²θ ≥ 0` and integrating gives
  `∫|g| sinθcos²θ ≤ M/3 ≤ 3|g(π/4)| + 9|g'(π/4)| + 9√N` (the constants `3, 9, 9` are extremely
  loose).  Integrability of `g · sinθcos²θ` follows by dominated convergence against the
  integrable majorant `M · sinθcos²θ`, the a.e. statements being transferred from the open
  interval via `Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo`.
-/


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 Taylor's formula with integral remainder on an open interval -/

private theorem TaylorRemainderIoo {g : ℝ → ℝ} {l u a θ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo l u)) (ha : a ∈ Set.Ioo l u) (hθ : θ ∈ Set.Ioo l u) :
    g θ = g a + (θ - a) * deriv g a + ∫ s in a..θ, (θ - s) * deriv (deriv g) s := by
  have hsub : Set.uIcc a θ ⊆ Set.Ioo l u := ordConnected_Ioo.uIcc_subset ha hθ
  have hca : ∀ s ∈ Set.uIcc a θ, ContDiffAt ℝ 2 g s := fun s hs =>
    hg.contDiffAt (isOpen_Ioo.mem_nhds (hsub hs))
  have hH : ∀ s ∈ Set.uIcc a θ,
      HasDerivAt (fun s : ℝ => (θ - s) * deriv g s + g s)
        ((θ - s) * deriv (deriv g) s) s := by
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have hd2 : HasDerivAt (deriv g) (deriv (deriv g) s) s :=
      (h1.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hd0 : HasDerivAt g (deriv g s) s := (h2.differentiableAt (by norm_num)).hasDerivAt
    have hd1 : HasDerivAt (fun s : ℝ => θ - s) (-1) s := by
      have h : HasDerivAt (fun s : ℝ => θ - s) (0 - 1) s :=
        (hasDerivAt_const s θ).sub (hasDerivAt_id s)
      simpa using h
    have h := (hd1.mul hd2).add hd0
    have hA : (-1 * deriv g s + (θ - s) * deriv (deriv g) s + deriv g s)
        = (θ - s) * deriv (deriv g) s := by ring
    rw [hA] at h
    exact h
  have hint : IntervalIntegrable (fun s : ℝ => (θ - s) * deriv (deriv g) s)
      MeasureTheory.volume a θ := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have h0 : ContinuousAt (deriv (deriv g)) s :=
      (h1.derivWithin (m := 0) (by norm_num)).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul h0).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint
  have hz : (∫ s in a..θ, (θ - s) * deriv (deriv g) s)
      = ((θ - θ) * deriv g θ + g θ) - ((θ - a) * deriv g a + g a) := hFTC
  rw [hz]
  ring

/-! ## §2 Elementary angular facts -/

private lemma eta_pos : 0 < Work.Spaces.eta := by norm_num [Work.Spaces.eta]

private lemma sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma cont_sin_two_rpow :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ := by
  refine ContinuousOn.rpow_const ?_ (fun x _ => Or.inr (le_of_lt eta_pos))
  exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)

private lemma integrableOn_sin_two_rpow_prv :
    MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc cont_sin_two_rpow

private lemma integral_sin_two_rpow_le :
    (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 := by
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (C := (1 : ℝ)) (ne_of_lt isCompact_Icc.measure_lt_top)
  calc (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ ∫ s in Work.Spaces.Iθ, (1 : ℝ) :=
        setIntegral_mono_on integrableOn_sin_two_rpow_prv hone measurableSet_Icc
          (fun s hs => Real.rpow_le_one (sin_two_nonneg_Iθ_prv hs) (Real.sin_le_one _)
            (le_of_lt eta_pos))
    _ = Real.pi / 2 := by
        rw [MeasureTheory.setIntegral_const]
        simp [Work.Spaces.Iθ,
          Real.volume_real_Icc_of_le (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))]

private lemma integrableOn_sq_mul_sin_two_rpow {θ : ℝ} :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)) Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((show Continuous fun s : ℝ => (θ - s) ^ 2 by fun_prop).continuousOn).mul cont_sin_two_rpow)

private lemma integral_sq_mul_sin_two_rpow_le_eight {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta)) ≤ 8 := by
  have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Real.pi / 2) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      Work.Spaces.Iθ :=
    integrableOn_sin_two_rpow_prv.const_mul _
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  calc (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ ∫ s in Work.Spaces.Iθ, (Real.pi / 2) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
        refine setIntegral_mono_on integrableOn_sq_mul_sin_two_rpow hmaj measurableSet_Icc
          (fun s hs => ?_)
        have hs' : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hs
        have h1 : -(Real.pi / 2) ≤ θ - s := by linarith [hs'.2, hθ'.1]
        have h2 : θ - s ≤ Real.pi / 2 := by linarith [hθ'.2, hs'.1]
        have h3 : (θ - s) ^ 2 ≤ (Real.pi / 2) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hs) _)
    _ = (Real.pi / 2) ^ 2 * (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (Real.pi / 2) ^ 2 * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left integral_sin_two_rpow_le (by positivity)
    _ ≤ 8 := by
        have h2 : Real.pi / 2 ≤ 2 := by linarith
        have h3 : (Real.pi / 2) ^ 3 ≤ 8 := by
          calc (Real.pi / 2) ^ 3 ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
            _ = 8 := by norm_num
        nlinarith [h3]

/-! ## §3 The two Cauchy–Schwarz factors -/

private def facA (θ s : ℝ) : ℝ := |θ - s| * (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)

private def facB (h : ℝ → ℝ) (s : ℝ) : ℝ := |h s| * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))

private lemma rpow_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (Work.Spaces.eta / 2) * x ^ (Work.Spaces.eta / 2) = x ^ Work.Spaces.eta := by
  rw [← Real.rpow_add hx, show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]

private lemma rpow_neg_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ (-(Work.Spaces.eta / 2)) * x ^ (-(Work.Spaces.eta / 2)) = x ^ (-(Work.Spaces.eta)) := by
  rw [← Real.rpow_add hx,
    show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]

private lemma rpow_half_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (Work.Spaces.eta / 2)) ^ 2 = x ^ Work.Spaces.eta := by
  rw [sq, rpow_half_mul_self hx]

private lemma rpow_neg_half_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(Work.Spaces.eta / 2))) ^ 2 = x ^ (-(Work.Spaces.eta)) := by
  rw [sq, rpow_neg_half_mul_self hx]

private lemma facA_mul_facB {h : ℝ → ℝ} {θ s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    facA θ s * facB h s = |(θ - s) * h s| := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  have hrp : (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
      * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2)) = 1 := by
    rw [← Real.rpow_add hsp, show Work.Spaces.eta / 2 + -(Work.Spaces.eta / 2) = 0 by ring,
      Real.rpow_zero]
  rw [facA, facB, abs_mul]
  calc |θ - s| * (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
        * (|h s| * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2)))
      = |θ - s| * |h s|
        * ((Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)
          * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))) := by ring
    _ = |θ - s| * |h s| := by rw [hrp, mul_one]

private lemma facA_sq {θ s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    (facA θ s) ^ 2 = (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  rw [facA, mul_pow, sq_abs, rpow_half_sq hsp]

private lemma facB_sq {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    (facB h s) ^ 2 = (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) := by
  have hsp : 0 < Real.sin (2 * s) := sin_two_pos_of_Ioo hs
  rw [facB, mul_pow, sq_abs, rpow_neg_half_sq hsp]

private lemma contOn_sin_two_rpow_half {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (Work.Spaces.eta / 2)) (Set.Icc c d) := by
  refine ContinuousOn.rpow_const ?_ (fun x hx => Or.inl ?_)
  · exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  · exact ne_of_gt (sin_two_pos_of_Ioo ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)

private lemma contOn_sin_two_rpow_neg_half {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (-(Work.Spaces.eta / 2))) (Set.Icc c d) := by
  refine ContinuousOn.rpow_const ?_ (fun x hx => Or.inl ?_)
  · exact Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  · exact ne_of_gt (sin_two_pos_of_Ioo ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)

private lemma contOn_facA {θ c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (facA θ) (Set.Icc c d) := by
  have h1 : Continuous (fun s : ℝ => |θ - s|) := by fun_prop
  exact h1.continuousOn.mul (contOn_sin_two_rpow_half hc hd)

private lemma contOn_facB {h : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2)
    (hcont : ContinuousOn h (Set.Icc c d)) :
    ContinuousOn (facB h) (Set.Icc c d) :=
  hcont.abs.mul (contOn_sin_two_rpow_neg_half hc hd)

/-! ## §4 Cauchy–Schwarz on a compact subinterval of the open angular interval -/

private lemma abs_intervalIntegral_mul_le {h : ℝ → ℝ} {θ c d : ℝ} (hcd : c ≤ d)
    (hc : 0 < c) (hd : d < Real.pi / 2) (hcont : ContinuousOn h (Set.Icc c d))
    (hint : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2
        * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    |∫ s in c..d, (θ - s) * h s|
      ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
            * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := by
  have hsub : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun s hs => ⟨le_trans (le_of_lt hc) hs.1, le_trans hs.2 (le_of_lt hd)⟩
  have hsuboo : Set.Icc c d ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun s hs => ⟨lt_of_lt_of_le hc hs.1, lt_of_le_of_lt hs.2 hd⟩
  have hmIcc : MeasurableSet (Set.Icc c d) := measurableSet_Icc
  have hnnA : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv ⟨le_of_lt hs.1, le_of_lt hs.2⟩) _))
  have hnnB : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ_prv ⟨le_of_lt hs.1, le_of_lt hs.2⟩) _))
  have h1 : |∫ s in c..d, (θ - s) * h s| ≤ ∫ s in c..d, |(θ - s) * h s| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (f := fun s : ℝ => (θ - s) * h s) hcd
  have h2 : (∫ s in c..d, |(θ - s) * h s|)
      = ∫ s in Set.Icc c d, facA θ s * facB h s := by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun hmIcc (fun s hs => ?_)
    rw [facA_mul_facB (h := h) (θ := θ) (hsuboo hs)]
  have hFaesm : AEStronglyMeasurable (facA θ) (volume.restrict (Set.Icc c d)) :=
    (contOn_facA (θ := θ) hc hd).aestronglyMeasurable hmIcc
  have hGaesm : AEStronglyMeasurable (facB h) (volume.restrict (Set.Icc c d)) :=
    (contOn_facB hc hd hcont).aestronglyMeasurable hmIcc
  have hF2 : Integrable (fun s => (facA θ s) ^ 2) (volume.restrict (Set.Icc c d)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc ((contOn_facA (θ := θ) hc hd).pow 2)
  have hG2 : Integrable (fun s => (facB h s) ^ 2) (volume.restrict (Set.Icc c d)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc ((contOn_facB hc hd hcont).pow 2)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Icc c d))
    hFaesm hGaesm hF2 hG2
  have hF2' : (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      = ∫ s in Set.Icc c d, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) :=
    setIntegral_congr_fun hmIcc (fun s hs => facA_sq (hsuboo hs))
  have hG2' : (∫ s in Set.Icc c d, (facB h s) ^ 2)
      = ∫ s in Set.Icc c d, (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) :=
    setIntegral_congr_fun hmIcc (fun s hs => facB_sq (hsuboo hs))
  have hF2le : (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      ≤ ∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta) := by
    rw [hF2']
    exact setIntegral_mono_set integrableOn_sq_mul_sin_two_rpow hnnA
      (Eventually.of_forall (fun s hs => hsub hs))
  have hG2le : (∫ s in Set.Icc c d, (facB h s) ^ 2)
      ≤ ∫ s in Work.Spaces.Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta)) := by
    rw [hG2']
    exact setIntegral_mono_set hint hnnB (Eventually.of_forall (fun s hs => hsub hs))
  have hFGnn : 0 ≤ ∫ s in Set.Icc c d, facA θ s * facB h s :=
    setIntegral_nonneg hmIcc (fun s hs => by
      rw [facA_mul_facB (h := h) (θ := θ) (hsuboo hs)]; exact abs_nonneg _)
  have h3 : (∫ s in Set.Icc c d, facA θ s * facB h s)
      ≤ Real.sqrt (∫ s in Set.Icc c d, (facA θ s) ^ 2)
        * Real.sqrt (∫ s in Set.Icc c d, (facB h s) ^ 2) := by
    calc (∫ s in Set.Icc c d, facA θ s * facB h s)
        = |∫ s in Set.Icc c d, facA θ s * facB h s| := (abs_of_nonneg hFGnn).symm
      _ ≤ _ := hcs
  have h4 : Real.sqrt (∫ s in Set.Icc c d, (facA θ s) ^ 2)
      * Real.sqrt (∫ s in Set.Icc c d, (facB h s) ^ 2)
      ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
        * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
            * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
    mul_le_mul (Real.sqrt_le_sqrt hF2le) (Real.sqrt_le_sqrt hG2le)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∫ s in c..d, (θ - s) * h s| ≤ ∫ s in c..d, |(θ - s) * h s| := h1
    _ = ∫ s in Set.Icc c d, facA θ s * facB h s := h2
    _ ≤ _ := h3
    _ ≤ _ := h4

/-! ## §5 The Taylor remainder at `π/4` -/

private theorem intervalRemainder_le {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioo 0 (Real.pi / 2)))
    (hh : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2
        * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |∫ s in (Real.pi / 4)..θ, (θ - s) * h s|
      ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
          * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by positivity
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hC : Real.sqrt (∫ s in Work.Spaces.Iθ, (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
      ≤ Real.sqrt 8 :=
    Real.sqrt_le_sqrt (integral_sq_mul_sin_two_rpow_le_eight ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hNN : 0 ≤ Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
      * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := Real.sqrt_nonneg _
  rcases le_total (Real.pi / 4) θ with hle | hle
  · have hc1 : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      exact ⟨lt_of_lt_of_le h4pos hs.1, lt_of_le_of_lt hs.2 hθ.2⟩
    have hkey := abs_intervalIntegral_mul_le (h := h) (θ := θ) hle h4pos hθ.2
      (hcont.mono hc1) hh
    calc |∫ s in (Real.pi / 4)..θ, (θ - s) * h s|
        ≤ Real.sqrt (∫ s in Work.Spaces.Iθ,
              (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
          * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := hkey
      _ ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hC hNN
  · have hsym : (∫ s in (Real.pi / 4)..θ, (θ - s) * h s)
        = -(∫ s in θ..(Real.pi / 4), (θ - s) * h s) :=
      intervalIntegral.integral_symm θ (Real.pi / 4)
    have hc1 : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      exact ⟨lt_of_lt_of_le hθ.1 hs.1, lt_of_le_of_lt hs.2 h4lt⟩
    have hkey := abs_intervalIntegral_mul_le (h := h) (θ := θ) hle hθ.1 h4lt
      (hcont.mono hc1) hh
    rw [hsym, abs_neg]
    calc |∫ s in θ..(Real.pi / 4), (θ - s) * h s|
        ≤ Real.sqrt (∫ s in Work.Spaces.Iθ,
              (θ - s) ^ 2 * (Real.sin (2 * s)) ^ (Work.Spaces.eta))
          * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) := hkey
      _ ≤ Real.sqrt 8 * Real.sqrt (∫ s in Work.Spaces.Iθ, (h s) ^ 2
              * (Real.sin (2 * s)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hC hNN

/-! ## §6 The angular weight `sinθcos²θ` -/

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

private lemma sinCos2_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  positivity

private lemma integrableOn_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc continuous_sinCos2.continuousOn

private lemma integral_Iθ_sinCos2 :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) = 1 / 3 := by
  have hderiv : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3 / 3) (Work.Elliptic.sinCos2 θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => Real.cos θ) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h3 := h1.pow 3
    have h4 := h3.neg.div_const 3
    refine h4.congr_deriv ?_
    simp only [Work.Elliptic.sinCos2]
    ring
  have hint : IntervalIntegrable (fun θ : ℝ => Work.Elliptic.sinCos2 θ) volume 0 (π / 2) :=
    continuous_sinCos2.intervalIntegrable 0 (π / 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := π / 2)
    (fun θ _ => hderiv θ) hint
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [h]
  simp [Real.cos_pi_div_two, Real.cos_zero]
  norm_num

private lemma aesm_of_contDiffOn_Ioo {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)) := hg.continuousOn
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hms : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))
  rwa [hms] at h1

/-! ## §7 The main estimate -/

theorem SliceMomentTaylor {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => g θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, |g θ| * Work.Elliptic.sinCos2 θ
        ≤ 3 * |g (Real.pi / 4)| + 9 * |deriv g (Real.pi / 4)|
          + 9 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have h4mem : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hder1 : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv g)) (Set.Ioo 0 (Real.pi / 2)) :=
    (hder1.deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn
  set NN : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hNNdef
  set M : ℝ := |g (Real.pi / 4)| + (Real.pi / 2) * |deriv g (Real.pi / 4)|
      + Real.sqrt 8 * Real.sqrt NN with hMdef
  -- the pointwise bound on the open interval
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ M := by
    intro θ hθ
    have hT := TaylorRemainderIoo hg h4mem hθ
    have hb := intervalRemainder_le hcont2 hint hθ
    have hθa : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hθb : |θ - Real.pi / 4| * |deriv g (Real.pi / 4)|
        ≤ (Real.pi / 2) * |deriv g (Real.pi / 4)| :=
      mul_le_mul_of_nonneg_right hθa (abs_nonneg _)
    rw [hMdef]
    calc |g θ| = |g (Real.pi / 4) + (θ - Real.pi / 4) * deriv g (Real.pi / 4)
            + ∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := by rw [hT]
      _ ≤ |g (Real.pi / 4)| + |(θ - Real.pi / 4) * deriv g (Real.pi / 4)|
            + |∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := abs_add_three ..
      _ = |g (Real.pi / 4)| + |θ - Real.pi / 4| * |deriv g (Real.pi / 4)|
            + |∫ s in (Real.pi / 4)..θ, (θ - s) * deriv (deriv g) s| := by rw [abs_mul]
      _ ≤ |g (Real.pi / 4)| + (Real.pi / 2) * |deriv g (Real.pi / 4)|
            + Real.sqrt 8 * Real.sqrt NN := by
          have := hb
          rw [← hNNdef] at this
          linarith [hθb, this]
  -- integrability of the majorant
  have hMsc : Integrable (fun θ => M * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sinCos2.const_mul M
  have hscnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.Elliptic.sinCos2 θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
      sinCos2_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haebound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |g θ| * Work.Elliptic.sinCos2 θ ≤ M * Work.Elliptic.sinCos2 θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
      mul_le_mul_of_nonneg_right (hpt θ hθ)
        (sinCos2_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have haesm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ) :=
    aesm_of_contDiffOn_Ioo hg
  have hscaesm : AEStronglyMeasurable (fun θ => Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    continuous_sinCos2.continuousOn.aestronglyMeasurable measurableSet_Icc
  have hIntAbs : Integrable (fun θ => |g θ| * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have haesmA : AEStronglyMeasurable (fun θ => |g θ| * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      fun_prop
    refine Integrable.mono' hMsc haesmA ?_
    filter_upwards [haebound, hscnn] with θ h hnn
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hnn)]
  have hIntG : Integrable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have haesmG : AEStronglyMeasurable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      fun_prop
    refine Integrable.mono' hMsc haesmG ?_
    filter_upwards [haebound, hscnn] with θ h hnn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact h
  refine ⟨hIntG, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, |g θ| * Work.Elliptic.sinCos2 θ)
      ≤ ∫ θ in Work.Spaces.Iθ, M * Work.Elliptic.sinCos2 θ :=
        integral_mono_ae hIntAbs hMsc haebound
    _ = M * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ = M * (1 / 3) := by rw [integral_Iθ_sinCos2]
    _ ≤ 3 * |g (Real.pi / 4)| + 9 * |deriv g (Real.pi / 4)| + 9 * Real.sqrt NN := by
        rw [hMdef]
        have h8 : Real.sqrt 8 ≤ 27 := by
          have h : Real.sqrt 8 ≤ Real.sqrt (27 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
          rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 27)] at h
        have hp : Real.pi ≤ 54 := by linarith [Real.pi_lt_four]
        nlinarith [abs_nonneg (g (Real.pi / 4)), abs_nonneg (deriv g (Real.pi / 4)),
          Real.sqrt_nonneg NN]

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

/-- At `z = 0` the `ℋ^k`-integrand vanishes identically: the radial weight `w` is a factor of
every summand and `w 0 = 0`. -/
private lemma HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
  simp

/-- **`ℋ^k`-membership only depends on the open quadrant.**  If `f` and `g` agree on
`(0,∞) × (0,π/2)` then `f ∈ ℋ^k` implies `g ∈ ℋ^k`. -/
theorem HkMem_of_agreeOnQ {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.AgreeOnQ f g) (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k g := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    show Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2)
    exact MeasureTheory.Ioo_ae_eq_Icc
  -- the two `θ`-slice integrals agree at every `z ∈ Iz`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k g θ
      have h2 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k f θ
      rw [h1, h2]
    · rw [MeasureTheory.setIntegral_congr_set hIoo.symm,
        MeasureTheory.setIntegral_congr_set hIoo.symm]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => (HkIntegrand_congr h z θ hz0 hθ.1 hθ.2).symm)
  constructor
  · -- integrability of each `θ`-slice
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k g θ
      rw [h1]
      exact MeasureTheory.integrableOn_zero
    · have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        MeasureTheory.IntegrableOn.congr_set_ae (hf.1 z hz) hIoo
      have h2 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
          (Set.Ioo 0 (π / 2)) :=
        MeasureTheory.IntegrableOn.congr_fun h1
          (fun θ hθ => HkIntegrand_congr h z θ hz0 hθ.1 hθ.2) measurableSet_Ioo
      exact MeasureTheory.IntegrableOn.congr_set_ae h2 hIoo.symm
  · -- integrability of the `z`-integral
    exact MeasureTheory.IntegrableOn.congr_fun hf.2
      (fun z hz => (hinner z hz).symm) measurableSet_Ici

end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.StraightDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The one-dimensional angular operator `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` of the elliptic
section, acting on functions of `θ` alone.  It is the `θ`-slice of
`Work.Elliptic.Lzero`. -/
def Lzero1 (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ

/-- The angular weight of the `i = 0` (pure radial) group: `sin(2θ)^{-η}` with `η = 99/100`. -/
def sEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight of the mixed (`i ≥ 1`) groups: `sin(2θ)^{-γ}` with `γ = 1 + α/10`. -/
def sGam (α : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))



/-- `Lzero1` is the `θ`-slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_eq_Lzero (u : ℝ → ℝ) (z : ℝ) :
    Lzero1 u = fun θ => Work.Elliptic.Lzero (fun _ θ' => u θ') z θ := by
  funext θ
  simp only [Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Dth1Iter_add_of_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- A `SmoothSlice` function stays smooth under every iterate of `D_θ = sin(2θ) ∂_θ`
on the interval `Iθ = (-1, π/2 + 1)`: the derivative of a `C^∞` function is again
`C^∞` on an open set, and multiplication by `sin(2θ)` preserves that. -/
private theorem Dth1Iter_contDiffOn_of_smoothSlice (n : ℕ) {f : ℝ → ℝ}
    (hf : Work.Elliptic.SmoothSlice f) :
    ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter n f) (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
  induction n with
  | zero => simpa [Work.Elliptic.Dth1Iter, Work.Elliptic.SmoothSlice] using hf
  | succ n ih =>
    have hd : ContDiffOn ℝ ⊤ (deriv (Work.Elliptic.Dth1Iter n f))
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := ih.deriv_of_isOpen isOpen_Ioo le_top
    simp only [Work.Elliptic.Dth1Iter_succ]
    unfold Work.Elliptic.Dth1
    fun_prop

theorem Dth1Iter_add_of_smooth (m : ℕ) {F G : ℝ → ℝ}
    (hF : Work.Elliptic.SmoothSlice F) (hG : Work.Elliptic.SmoothSlice G)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)) :
    Work.Elliptic.Dth1Iter m (fun θ => F θ + G θ) θ
      = Work.Elliptic.Dth1Iter m F θ + Work.Elliptic.Dth1Iter m G θ := by
  -- `Dth1Iter n` is additive on the open interval `Iθ`, where all smoothness holds.
  have key : ∀ n : ℕ, ∀ θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1),
      Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ) θ
        = Work.Elliptic.Dth1Iter n F θ + Work.Elliptic.Dth1Iter n G θ := by
    intro n
    induction n with
    | zero => intro θ hθ; simp [Work.Elliptic.Dth1Iter]
    | succ n ih =>
      intro θ hθ
      -- both pieces are differentiable at `θ`, so `deriv` splits over the sum
      have hdiffF : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n F) θ :=
        ((Dth1Iter_contDiffOn_of_smoothSlice n hF).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hdiffG : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n G) θ :=
        ((Dth1Iter_contDiffOn_of_smoothSlice n hG).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      -- the two sides of the induction hypothesis agree near `θ`
      have heq : Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ) =ᶠ[𝓝 θ]
          (Work.Elliptic.Dth1Iter n F + Work.Elliptic.Dth1Iter n G) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
        exact ih y hy
      calc Work.Elliptic.Dth1Iter (n + 1) (fun θ => F θ + G θ) θ
          = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n (fun θ => F θ + G θ)) θ := rfl
        _ = Real.sin (2 * θ)
              * deriv (Work.Elliptic.Dth1Iter n F + Work.Elliptic.Dth1Iter n G) θ := by
              rw [heq.deriv_eq]
        _ = Real.sin (2 * θ)
              * (deriv (Work.Elliptic.Dth1Iter n F) θ + deriv (Work.Elliptic.Dth1Iter n G) θ) := by
              rw [deriv_add hdiffF hdiffG]
        _ = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n F) θ
              + Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n G) θ := by
              rw [mul_add]
        _ = Work.Elliptic.Dth1Iter (n + 1) F θ + Work.Elliptic.Dth1Iter (n + 1) G θ := rfl

  exact key m θ hθ

end

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Dth1Iter_eventuallyEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- `D_θ = sin(2θ) ∂_θ` respects eventual equality of the underlying functions. -/
theorem Dth1_eventuallyEq {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1 F =ᶠ[nhds θ] Work.Elliptic.Dth1 G := by
  filter_upwards [h.deriv] with y hy
  simp only [Work.Elliptic.Dth1, hy]

/-- The iterates `Dth1Iter n` respect eventual equality of the underlying functions. -/
theorem Dth1Iter_eventuallyEq_aux (m : ℕ) {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1Iter m F =ᶠ[nhds θ] Work.Elliptic.Dth1Iter m G := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
      simpa using Dth1_eventuallyEq (F := Work.Elliptic.Dth1Iter n F)
        (G := Work.Elliptic.Dth1Iter n G) (θ := θ) ih

theorem Dth1Iter_eventuallyEq (m : ℕ) {F G : ℝ → ℝ} {θ : ℝ} (h : F =ᶠ[nhds θ] G) :
    Work.Elliptic.Dth1Iter m F θ = Work.Elliptic.Dth1Iter m G θ :=
  (Dth1Iter_eventuallyEq_aux m h).eq_of_nhds

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Dth1Iter_sin_sq_bdd =====
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
set_option maxHeartbeats 1000000

/-- The derivative of `θ ↦ sin(2θ)²`. -/
private lemma hasDerivAt_sin_two_sq (θ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.sin (2 * τ) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    have hval : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rw [hval] at h
    exact h
  have h2 : HasDerivAt (fun τ : ℝ => Real.sin (2 * τ) ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h1.pow 2
  have h3 : 2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    norm_num
    ring
  rw [h3] at h2
  exact h2





end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.dth1Iter_smooth_bound =====
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

local notation "U" => Set.Ioo (-1) (Real.pi / 2 + 1)

/-- `D_θ = sin(2θ) ∂_θ` preserves `C^∞` on an open set (the derivative of a smooth function is
smooth on an open set, and `θ ↦ sin(2θ)` is smooth). -/
private lemma contDiffOn_Dth1 {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1 f) s :=
  ((show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) s by fun_prop)).mul
    (hf.deriv_of_isOpen hs le_top)

/-- Iterates of `D_θ` preserve `C^∞` on an open set. -/
private lemma contDiffOn_Dth1Iter {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ∀ m : ℕ, ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter m f) s
  | 0 => by simpa using hf
  | (m + 1) => by
      have h : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter m f) s := contDiffOn_Dth1Iter hs hf m
      simpa only [Work.Elliptic.Dth1Iter_succ] using contDiffOn_Dth1 hs h


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.lightDerivIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.EllipticEst.TT.step2Ae

/-- **Clairaut for the slice `θ ↦ ∂_z f (z,·)`.**
If `f` is `C²` at the point `(z,θ)` then the slice `θ' ↦ ∂_z f (z,θ')` is differentiable at `θ`
with derivative `∂_z ∂_θ f (z,θ) = ∂_z(∂_θ f)(z,θ)`.

The proof identifies the slice with `θ' ↦ (fderiv ℝ (uncurry f) (z,θ')) (1,0)`, which is the
composition of the linear map `L ↦ L (1,0)` with the (differentiable, since `f` is `C²`)
function `fderiv ℝ (uncurry f)`, and then converts the value of the derivative with
`Work.Spaces.deriv_deriv_snd_fst` and `Work.Spaces.pz_pth_comm`. -/
theorem hasDerivAt_pz_theta {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    HasDerivAt (fun θ' => Work.Spaces.pz f z θ') (Work.Spaces.pz (Work.Spaces.pth f) z θ) θ := by
  change HasDerivAt (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z)
    (deriv (fun z' => deriv (fun θ' => Function.uncurry f (z', θ')) θ) z) θ
  -- `fderiv ℝ (uncurry f)` is differentiable at `(z,θ)` because `f` is `C²` there.
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)
  -- `uncurry f` is differentiable near `(z,θ)`, hence along the vertical slice through `z`.
  have hnd : ∀ᶠ y in 𝓝 (z, θ), DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffAt.eventually h (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ (Function.uncurry f) (z, θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually hnd
  -- the `(1,0)`-evaluation of the derivative of `uncurry f`
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ (Function.uncurry f) y (1, 0)
  -- the slice agrees with `Φ` along `{z} × ℝ`
  have hcongr : (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) =ᶠ[𝓝 θ]
      (fun t => Φ (z, t)) := by
    filter_upwards [hslice] with θ' hθ'
    have h3 : deriv (fun z' => Function.uncurry f (z', θ')) z
        = (fderiv ℝ (Function.uncurry f) (z, θ')) (1, 0) :=
      Work.Spaces.deriv_slice_fst (Function.uncurry f) z θ' hθ'
    simpa only [Φ] using h3
  -- `Φ` is the composition of a continuous linear map with `fderiv ℝ (uncurry f)`
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (1, 0)) ∘ (fderiv ℝ (Function.uncurry f)) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z, θ) := by
    rw [hΦ]
    exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  -- the derivative of the slice of `Φ`
  have hstep : HasDerivAt (fun t => Φ (z, t)) ((fderiv ℝ Φ (z, θ)) (0, 1)) θ := by
    have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (z, t))
        ((fderiv ℝ Φ (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ := by
      convert (hΦdiff.hasFDerivAt.comp θ h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    simpa only [ContinuousLinearMap.inr_apply] using h3
  have hmain : HasDerivAt (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z)
      ((fderiv ℝ Φ (z, θ)) (0, 1)) θ := hcongr.hasDerivAt_iff.mpr hstep
  -- identify the value of the derivative
  have hΦderiv : fderiv ℝ Φ (z, θ) =
      (ContinuousLinearMap.apply ℝ ℝ (1, 0)) ∘SL
        fderiv ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z, θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  have hval1 : (fderiv ℝ Φ (z, θ)) (0, 1)
      = deriv (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) θ := by
    rw [hΦderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact (Work.Spaces.deriv_deriv_snd_fst (Function.uncurry f) z θ h).symm
  -- Clairaut: the two orders of the mixed partial derivative agree
  have hval2 : deriv (fun θ' => deriv (fun z' => Function.uncurry f (z', θ')) z) θ
      = deriv (fun z' => deriv (fun θ' => Function.uncurry f (z', θ')) θ) z := by
    have hp := Work.Spaces.pz_pth_comm (f := f) h
    simpa only [Work.Spaces.pz, Work.Spaces.pth, Function.uncurry] using hp.symm
  exact (hmain.congr_deriv hval1).congr_deriv hval2

end Work.FTS.EllipticEst.TT.step2Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.swap_prod_supported =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms =====
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

/-! ## Measurability of the two angular weight factors

The summands of `Work.Spaces.HkIntegrand` are squares of products `D · weight`, where the
weight is either the radial factor `w z / sin(2θ)^{η/2}` or the product weight
`Wt α z θ = w z · sin(2θ)^{-γ/2}`.  Both are measurable functions of `θ`, being built from
the measurable map `θ ↦ sin(2θ)` by `rpow`, division and multiplication by a constant. -/


/-- The angular slice `θ ↦ Wt α z θ` of the product weight is measurable. -/
private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this

/-! ## Continuity of the angular slices of the iterated derivatives

`SmoothNbhd G` says that the uncurried `G` is `C^∞` on the open set `nbhU` of the closed
quadrant; every `D`-iterate of `G` is then smooth there too, and hence has continuous
angular slices on `Iθ`. -/


/-- For `z ∈ Iz`, the angular slice `θ ↦ D_z^j D_θ^i G z θ` of a `SmoothNbhd` function is
continuous on the closed interval `Iθ`. -/
private lemma continuousOn_mixed_slice {G : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd G)
    (i j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.mixed j i G z θ) Work.Spaces.Iθ := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.mixed j i G) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i G)) (z, θ) :=
    hsm'.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-! ## The individual summands are integrable

Each summand is a square, hence nonnegative, and is one of the summands of the full
integrand `HkIntegrand α k G z θ`; a single term of a sum of nonnegative terms is bounded
by the sum (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).
Together with the a.e. strong measurability supplied by the smoothness of `G` and the
measurability of the weights, `Integrable.mono'` gives the conclusion. -/


end Work.FTS.EllipticEst
end
end
