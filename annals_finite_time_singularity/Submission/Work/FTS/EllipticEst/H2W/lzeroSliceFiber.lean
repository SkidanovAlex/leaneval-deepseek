import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slice of `∂_z^m F` against the weight `sinθcos²θ` is integrable

For a weak-class solution pair `(F,Ψ)` of the elliptic problem of Elgindi, Annals **194**
(2021), §'Elliptic Regularity Estimates', the angular moment of the source is

  `F_*(F)(z) = ∫_θ F(z,θ)·sinθcos²θ dθ`

(`Work.Elliptic.Fstar`).  The moment conditions of the weak class (`Work.FTS.EllipticEst.MomentZ`)
require the *angular slices* at a fixed `z` of the plain radial derivatives of the source,

  `θ ↦ ∂_z^m F(z,θ)·sinθcos²θ`  on  `Iθ = [0,π/2]`,

to be honest (integrable) for `m ≤ 2`: this is the prerequisite for differentiating the moment
under the integral sign in the `z`-variable.  This module supplies exactly that.

## The argument

The hypotheses of `Work.FTS.EllipticEst.WeakPos2` are: the equation `bslOp α Ψ = F` on the open
quadrant, the Dirichlet *values* of `Ψ`, the decay of `Ψ` at `z → ∞`, the two orthogonality
conditions and, crucially, `C^∞`-smoothness of `Ψ` on the open quadrant and
`Work.Spaces.HkMem α 2 F` (honesty of the weighted `ℋ²`-integrand of the source).

1. **Smoothness of the source.**  On the open quadrant `F` coincides with `bslOp α Ψ`; the
   elliptic operator is built from `Ψ` and its partials and the `C^∞` factors `z`, `z²`, `tan θ`
   (`tan` is smooth on `Q0` since `cos θ ≠ 0` there), so `SmoothOpen F`
   (`remov.SmoothOpen_bslOp_of_smoothOpen` followed by the congruence
   `Cert.smoothOpen_congr_bsl`).

2. **The `D_z = z∂_z` slices.**  For `z > 0` and `i ≤ 2`, the absorption inequality
   `|a·sinθcos²θ| ≤ (a·w(z)/sin(2θ)^{η/2})² + 1` for `θ ∈ Iθ` (with `w(z) ≥ 1` and
   `sin(2θ)^{η/2} ≤ 1`) together with `ℋ²`-honesty of the source
   (`OpenQDefs.integrableOn_zSummand`) gives the integrability of the slices of `D_z^i F`
   (`GbarSin.integrableOn_DzIter_mul_sinCos2`), for **every** `z > 0` (the weight `w(z)` and the
   angular weight are the only inputs, so no `z`-a.e. caveat is needed).

3. **From `D_z` back to `∂_z`.**  `D_z = z∂_z`, hence `D_z^i` is triangular in the `∂_z^k`
   (`k ≤ i`) with invertible diagonal, and

   * `m = 0`: `∂_z^0 F = D_z^0 F`;
   * `m = 1`: `z·∂_z F = D_z F` holds *by definition* (`rfl`), so the slice of `∂_z F` is the
     constant multiple `z⁻¹` of an integrable slice;
   * `m = 2`: `D_z²F = D_zF + z²∂_z²F` at every point of the open quadrant (product rule, using
     that the `z`-slice of `∂_z F` is differentiable there, `SmoothOpen.hasDerivAt_slice_pzIter`),
     i.e. `z²·∂_z²F = D_z²F - D_zF`.  The identity only holds on the open interval; since
     `Iθ \ (0,π/2) = {0,π/2}` is a null set, it holds a.e. on `Iθ` and transports integrability.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The two pointwise identities relating `∂_z^m` and `D_z^m` for `m ≤ 2` -/

/-- `D_z^2 F = D_z F + z²∂_z²F` at a point where the `z`-slice of `∂_z F` is differentiable.
(Since `D_z^2 F = z·∂_z(z·∂_z F) = z·∂_zF + z²·∂_z²F` by the product rule, and `z·∂_zF = D_z F`.) -/
theorem lzsf_DzIter_two_eq (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hd : HasDerivAt (fun z' => Work.Spaces.pzIter 1 F z' θ) (Work.Spaces.pzIter 2 F z θ) z) :
    Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  have hmul : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ)
      (1 * Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ) z := by
    have h := (hasDerivAt_id z).mul hd
    have h2 : (id : ℝ → ℝ) * (fun z' : ℝ => Work.Spaces.pzIter 1 F z' θ)
        = fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ := by
      funext z'; simp
    rw [h2] at h
    simpa using h
  have hderiv : deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ) z
      = Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ := by
    simpa only [one_mul] using hmul.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ) z
      = z * Work.Spaces.pzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ
  rw [hderiv]
  ring

/-- At an interior angle of a source which is `C^∞` on the open quadrant, the slice of `∂_z²F`
is the constant multiple `z⁻²` of the difference of the two `D_z`-slices. -/
theorem lzsf_pzIter_two_mul_sinCos2_eq {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    z⁻¹ ^ 2 * ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        * Work.Elliptic.sinCos2 θ)
      = Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ := by
  have hd := hF.hasDerivAt_slice_pzIter 1 hθ hz
  have h2 := lzsf_DzIter_two_eq F hd
  have hz' : z ≠ 0 := ne_of_gt hz
  rw [h2]
  have hcancel : Work.Spaces.DzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ
      - Work.Spaces.DzIter 1 F z θ = z ^ 2 * Work.Spaces.pzIter 2 F z θ := by ring
  rw [hcancel]
  have hzsq : z⁻¹ ^ 2 * z ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz', one_pow]
  calc z⁻¹ ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ)
      = z⁻¹ ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ) := by ring_nf
    _ = Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ := by rw [hzsq, one_mul]

/-- `z·∂_zF = D_z F` holds by definition, so the slice of `∂_zF` is `z⁻¹` times the slice of
`D_zF` everywhere. -/
theorem lzsf_pzIter_one_mul_sinCos2_eq (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ
      = z⁻¹ * (Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ) := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hD : Work.Spaces.DzIter 1 F z θ = z * Work.Spaces.pzIter 1 F z θ := rfl
  rw [hD]
  calc Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ
      = (z⁻¹ * z) * (Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ) := by
        rw [inv_mul_cancel₀ hz', one_mul]
    _ = z⁻¹ * (z * Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ) := by ring

/-- Almost everywhere on `Iθ` the angle is interior (the two endpoints form a null set). -/
theorem lzsf_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
  exact Work.FTS.EllipticEst.GbarSin.ae_imp_of_mem_Ioo (fun θ hθ => hθ)

/-! ## The requested statement -/

/-- **The angular slice of `∂_z^m F` against `sinθcos²θ` is integrable on `Iθ`, for `m ≤ 2`.**

This is the integrability input of the moment conditions of the weak class
(`Work.FTS.EllipticEst.MomentZ`); see the module docstring for the route. -/
theorem lzeroSliceFiber : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.WeakPos2 α F Ψ →
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ m : ℕ, m ≤ 2 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.pzIter m F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 hW z hz m hm
  obtain ⟨hEq, h0, hpi, hdec, hOF, hOP, hsm, hmF⟩ := hW
  -- the source is `C^∞` on the open quadrant, since there it equals `bslOp α Ψ`
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso)
      (fun z θ hz hθ0 hθ1 => hEq z hz θ hθ0 hθ1)
  -- the `D_z`-slices of the source are integrable, for every `z > 0`
  have hDz : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.DzIter i F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun i hi => Work.FTS.EllipticEst.GbarSin.integrableOn_DzIter_mul_sinCos2 α 2 F hF hmF hi hz
  interval_cases m
  · -- `m = 0`: `∂_z^0 = D_z^0`
    simpa using hDz 0 (by norm_num)
  · -- `m = 1`: `z·∂_zF = D_z F`, by definition
    have hfun : (fun θ : ℝ => Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => z⁻¹ * (Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ) := by
      funext θ
      exact lzsf_pzIter_one_mul_sinCos2_eq F hz θ
    rw [hfun]
    exact (hDz 1 (by norm_num)).const_mul z⁻¹
  · -- `m = 2`: `z²·∂_z²F = D_z²F - D_z F` on the open interval, hence a.e. on `Iθ`
    have hmain : MeasureTheory.IntegrableOn
        (fun θ : ℝ => z⁻¹ ^ 2 * ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
          * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ := by
      refine ((hDz 2 le_rfl).const_mul (z⁻¹ ^ 2)).sub
        ((hDz 1 (by norm_num)).const_mul (z⁻¹ ^ 2)) |>.congr ?_
      filter_upwards [lzsf_ae_mem_Ioo_Iθ] with θ hθ
      simp only [Pi.sub_apply]
      ring
    refine hmain.congr ?_
    filter_upwards [lzsf_ae_mem_Ioo_Iθ] with θ hθ
    exact lzsf_pzIter_two_mul_sinCos2_eq hF hz hθ

end Work.FTS.EllipticEst.H2W
