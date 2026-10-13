import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

/-- `x₁ = sin(π/4) = √2/2` is strictly smaller than `1`, hence lies in the domain `(-1,1)` of the
arcsine. -/
private theorem xNear_lt_one : xNear < 1 := by
  rw [xNear, Real.sin_pi_div_four]
  have h : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- `x₁ > 0`. -/
private theorem xNear_pos : 0 < xNear := by
  rw [xNear, Real.sin_pi_div_four]
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- On all of `ℝ` the factor `κ x = cos (2 θ(x))` coincides with `√(1-x²)`. -/
private theorem kappa_eq_sqrt (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  simp only [kappa, thetaOf]
  rw [show 2 * (Real.arcsin x / 2) = Real.arcsin x by ring, Real.cos_arcsin]

private theorem thetaOf_zero : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ(x₁) = π/8`. -/
private theorem thetaOf_xNear : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- The change of variables `x = sin(2θ)` out of the `x`-variable into the `θ`-variable, on the
half `(0, x₁)` of the interval (where `κ ≥ 1/√2`): the substitution is carried by the
`ds/dθ = 2κ(s)` Jacobian `1/(2κ x)`, and since `Ψ ≥ 0` the integral over the corresponding
sub-interval `(0, π/8) ⊆ Iθ` is at most the full weighted integral. -/
theorem thetaOfSubst {Ψ : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn Ψ Work.Spaces.Iθ)
    (hnonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Ψ θ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x)))
        (Set.Ioc 0 xNear) ∧
      (∫ x in (0 : ℝ)..xNear, Ψ (thetaOf x) * (1 / (2 * kappa x)))
        ≤ ∫ θ in Work.Spaces.Iθ, Ψ θ := by
  have hcont : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  -- the derivative of `θ` at `x` is the Jacobian `1/(2κ x)`
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left (le_of_lt xNear_pos), max_eq_right (le_of_lt xNear_pos)] at hx
    have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
      Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt_one])
    have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
      h1.div_const 2
    have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
      rw [kappa_eq_sqrt x]; ring
    exact h2.congr_deriv hval
  -- the Jacobian is nonnegative
  have hnn : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear), 0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left (le_of_lt xNear_pos), max_eq_right (le_of_lt xNear_pos)] at hx
    have hpos : 0 < Real.sqrt (1 - x ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2, xNear_lt_one])
    rw [kappa_eq_sqrt x]
    positivity
  -- `Ψ` is integrable on the image interval `(0, π/8)`
  have hPsi_int : IntervalIntegrable Ψ volume (0 : ℝ) (Real.pi / 8) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)]
    exact hint.mono_set (by intro x hx; exact ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  -- integrability on `(0, x₁)`, by the change-of-variables criterion
  have hI : IntervalIntegrable (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x))) volume
      (0 : ℝ) xNear := by
    have hPsi' : IntervalIntegrable Ψ volume (thetaOf 0) (thetaOf xNear) := by
      rwa [thetaOf_zero, thetaOf_xNear]
    exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x => 1 / (2 * kappa x)) (g := Ψ)
      hcont hderiv hnn).mpr hPsi'
  have hIntOn : IntegrableOn (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x)))
      (Set.Ioc 0 xNear) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt xNear_pos)).mp hI
  -- the change-of-variables identity
  have hmain : ∫ x in (0 : ℝ)..xNear, Ψ (thetaOf x) * (1 / (2 * kappa x))
      = ∫ u in (0 : ℝ)..(Real.pi / 8), Ψ u := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x => 1 / (2 * kappa x)) (g := Ψ)
      hcont hderiv hnn
    rw [thetaOf_zero, thetaOf_xNear] at h
    simpa [Function.comp_def] using h
  -- enlarge the interval to the whole `Iθ`
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))] Ψ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall
        (fun x hx => hnonneg x ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩))
  have hPsi2 : IntervalIntegrable Ψ volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)).mpr
      (hint.mono_set (by intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩))
  have h1 : ∫ u in (0 : ℝ)..(Real.pi / 8), Ψ u ≤ ∫ u in (0 : ℝ)..(Real.pi / 2), Ψ u :=
    intervalIntegral.integral_mono_interval (f := Ψ) (a := (0 : ℝ)) (b := Real.pi / 8)
      (μ := volume) (c := (0 : ℝ)) (d := Real.pi / 2)
      le_rfl (by positivity) (by linarith [Real.pi_pos]) hae hPsi2
  have hconv : ∫ u in (0 : ℝ)..(Real.pi / 2), Ψ u = ∫ θ in Work.Spaces.Iθ, Ψ θ := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc (f := Ψ) (x := (0 : ℝ))
      (y := Real.pi / 2)).symm
  exact ⟨hIntOn, by rw [hmain]; exact h1.trans (le_of_eq hconv)⟩

end Work.FTS.H2.DivQ
