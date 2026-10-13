import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs

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
