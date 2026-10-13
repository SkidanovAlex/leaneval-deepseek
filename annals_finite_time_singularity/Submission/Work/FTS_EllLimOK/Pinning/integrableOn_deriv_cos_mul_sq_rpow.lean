import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_EllLimOK.Reconstruct

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(∂_θ (cos θ · Ψ z θ))² sin(2θ)^{-η}` from the `Vop`-counterpart

The `θ`-reconstruction of `Work.FTS_EllLimOK.Reconstruct` records that `Vop Ψ = ∂_θΨ - tan θ · Ψ`
is `1/cos θ` times the derivative of `θ ↦ cos θ · Ψ z θ`:

`cos θ · Vop Ψ z θ = ∂_θ (cos θ · Ψ z θ)`.  (`cos_mul_Vop_eq`.)

Hence everywhere on the open angular interval

`(∂_θ (cos θ · Ψ z θ))² sin(2θ)^{-η} = cos²θ · (Vop Ψ z θ)² · sin(2θ)^{-η}
  ≤ (Vop Ψ z θ)² sin(2θ)^{-η}`,

because `cos²θ ≤ 1` and `sin(2θ)^{-η} ≥ 0` there.  So the integrability of the `Vop`-integrand
on the *closed* interval `Iθ = [0,π/2]` (the hypothesis supplied by the `ℋ⁰`-memberships, whose
weight is integrable at `θ = 0`) transfers to the integrability of the derivative-integrand on
the *open* interval `(0,π/2)`.

The identity `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)` needs the `θ`-derivatives of the slice at the
interior points only, which is exactly what `SmoothOpen.curry_θ` supplies (the *analyticity* of
`SmoothOpen` is of course irrelevant here, but only `C^∞`-on-the-open-quadrant is used).  The
a.e. strong measurability of the left-hand side is free: `deriv` of anything is Borel measurable
(`measurable_deriv`).
-/

namespace Work.FTS_EllLimOK.Pinning

open MeasureTheory Set Filter

theorem integrableOn_deriv_cos_mul_sq_rpow {η : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) := by
  -- the `Vop`-integrand is integrable on the smaller, open interval as well
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the derivative of `θ ↦ cos θ · Ψ z θ` is `cos θ · Vop Ψ z θ` on the open interval
  have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun s => Real.cos s * Ψ z s) θ = Real.cos θ * Work.Construction.Vop Ψ z θ := by
    intro θ hθ
    have hslice : HasDerivAt (fun s : ℝ => Ψ z s) (Work.Spaces.pth Ψ z θ) θ :=
      (((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => Real.cos s * Ψ z s)
        (-Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ) θ :=
      (Real.hasDerivAt_cos θ).mul hslice
    refine (h3.congr_deriv ?_).deriv
    rw [Work.FTS_EllLimOK.cos_mul_Vop_eq Ψ hθ]
    ring
  refine MeasureTheory.Integrable.mono'
    (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
    (g := fun θ => (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
    hGint ?_ ?_
  · -- measurability: `deriv` is Borel measurable, and so are the two weight factors
    refine Measurable.aestronglyMeasurable ?_
    refine ((measurable_deriv _).pow_const 2).mul ?_
    exact Measurable.pow (Real.measurable_sin.comp
      ((measurable_const : Measurable fun _ : ℝ => (2:ℝ)).mul measurable_id))
      (measurable_const : Measurable fun _ : ℝ => (-η))
  · -- the pointwise domination, everywhere on the open interval
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hd := hderiv θ hθ
    have hsinpos : 0 < Real.sin (2 * θ) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hsinnn : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsinpos.le _
    have hFnn : 0 ≤ (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      mul_nonneg (sq_nonneg _) hsinnn
    have hle : (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
      rw [hd, mul_pow]
      calc (Real.cos θ) ^ 2 * (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          ≤ 1 * (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (Real.cos_sq_le_one θ) (sq_nonneg _)) hsinnn
        _ = (Work.Construction.Vop Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    exact hle

end Work.FTS_EllLimOK.Pinning
