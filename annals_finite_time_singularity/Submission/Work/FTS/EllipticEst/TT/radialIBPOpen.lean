/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial T-adjoint identity on an interval (non-compact form)

Step 4 of the route recorded in `NOTES_interpGamma.md` is the radial integration by parts with the
weight `w(z) = (1+z)²/z²` and the T-adjoint coefficient `b z = (z-3)/(1+z)`:

  `∫_z w² · (D_zF)(D_zH) = -∫_z w² · (D_z²F + b D_zF) · H + [H · D_zF · z w²]`,

where `D_zF = z ∂_zF`.  The compactly supported case is `Work.EllipticEst.Core.radialPairIBP`;
this module proves the *exact interval version*, i.e. with the flux `H · D_zF · z w²` evaluated at
the two endpoints instead of vanishing.  That form is what the limit passage `a → 0⁺`, `b → ∞`
needs: the flux is `H(z)·∂_zF(z)·(1+z)⁴/z²` and, for the slices of the elliptic problem, it is
`o(1)` along sequences (both `∂_zF` and `H` are controlled by the `ℋ⁰`-integrability against `w²`),
so the identity passes to `(0,∞)`.

The identity itself is the FTC for the flux `G = w²·z·H·(D_zF)`, whose derivative is the sum of the
two integrands.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The T-adjoint coefficient `b z = (z-3)/(1+z)`. -/
def bcoefR (z : ℝ) : ℝ := (z - 3) / (1 + z)

@[simp] theorem bcoefR_apply (z : ℝ) : bcoefR z = (z - 3) / (1 + z) := rfl

/-- The squared radial weight `(w z)²` written out. -/
@[simp] theorem w_sq_unfold (z : ℝ) :
    (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl

/-- **`(z w²)' = w² · b`**, i.e. the T-adjoint coefficient is the logarithmic derivative of the
radial weight `z w²`. -/
theorem deriv_zw_sq (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y) ((Work.Spaces.w z) ^ 2 * bcoefR z) z := by
  -- near `z` the function is `(1+y)^4/y^3`
  have hev : (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y) =ᶠ[𝓝 z] fun y : ℝ => (1 + y) ^ 4 / y ^ 3 := by
    filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hz)] with y hy
    simp only [w_sq_unfold]
    field_simp
  have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + z) ^ 3) z := by
    have h : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    exact (h.pow 4).congr_deriv (by ring)
  have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * z ^ 2) z := by
    have h : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
    exact (h.pow 3).congr_deriv (by ring)
  have h := (hnum.div hden (pow_ne_zero 3 (ne_of_gt hz))).congr_of_eventuallyEq hev
  refine h.congr_deriv ?_
  simp only [bcoefR_apply, w_sq_unfold]
  field_simp
  ring

/-- **The radial T-adjoint identity on an interval.**  For `0 < a < b` and `F ∈ C²`, `H ∈ C¹` on
`(0,∞)`,

  `∫_a^b w²(D_zF)(D_zH) = [H·D_zF·z w²]_a^b - ∫_a^b w²(D_z²F + b D_zF)H`. -/
theorem radial_ibp_interval {F H : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hF : ContDiffOn ℝ 2 F (Set.Ioi (0 : ℝ))) (hH : ContDiffOn ℝ 1 H (Set.Ioi (0 : ℝ))) :
    (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z))
      = (Work.Spaces.w b) ^ 2 * b * H b * (b * deriv F b)
        - (Work.Spaces.w a) ^ 2 * a * H a * (a * deriv F a)
        - (∫ z in a..b, (Work.Spaces.w z) ^ 2
            * (z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z)) * H z) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => lt_of_lt_of_le ha hx.1
  -- continuity of the building blocks
  have hcw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hw : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) :=
      (((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
    refine hw.congr ?_
    intro z hz
    simp only [w_sq_unfold]
  have hderF : ContinuousOn (deriv F) (Set.Ioi (0 : ℝ)) :=
    hF.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hderH : ContinuousOn (deriv H) (Set.Ioi (0 : ℝ)) :=
    hH.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hC1 : ContDiffOn ℝ 1 (fun y : ℝ => y * deriv F y) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.mul (hF.deriv_of_isOpen isOpen_Ioi (by norm_num))
  have hderdF : ContinuousOn (deriv (fun y : ℝ => y * deriv F y)) (Set.Ioi (0 : ℝ)) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcb : ContinuousOn (fun z : ℝ => bcoefR z) (Set.Ioi (0 : ℝ)) := by
    simp only [bcoefR_apply]
    exact (continuousOn_id.sub continuousOn_const).div (continuousOn_const.add continuousOn_id)
      (fun z hz => by have hz' : (0 : ℝ) < z := hz; linarith)
  -- continuity at every point of the closed interval (via `HasDerivAt`)
  have hmem : ∀ x ∈ Set.Icc a b, Set.Ioi (0 : ℝ) ∈ 𝓝 x := fun x hx =>
    isOpen_Ioi.mem_nhds (hsub hx)
  have hdF : ∀ x ∈ Set.Icc a b, HasDerivAt F (deriv F x) x := fun x hx =>
    ((hF.contDiffAt (hmem x hx)).differentiableAt (by norm_num)).hasDerivAt
  have hddF : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv F) (deriv (deriv F) x) x := fun x hx =>
    (((hF.contDiffAt (hmem x hx)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hdH : ∀ x ∈ Set.Icc a b, HasDerivAt H (deriv H x) x := fun x hx =>
    ((hH.contDiffAt (hmem x hx)).differentiableAt (by norm_num)).hasDerivAt
  have hzpos : ∀ x ∈ Set.Icc a b, 0 < x := fun x hx => lt_of_lt_of_le ha hx.1
  -- the two integrands
  set I1 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z) with hI1
  set I2 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2
    * (z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z)) * H z with hI2
  have hcont1 : ContinuousOn I1 (Set.Icc a b) := by
    have h := ((hcw.mono hsub).mul (continuousOn_id.mul (hderF.mono hsub))).mul
      (continuousOn_id.mul (hderH.mono hsub))
    refine h.congr ?_
    intro z hz
    simp only [hI1, Pi.mul_apply, Pi.add_apply, id_eq]
  have hcont2 : ContinuousOn I2 (Set.Icc a b) := by
    have h := ((hcw.mono hsub).mul ((continuousOn_id.mul (hderdF.mono hsub)).add
      ((hcb.mono hsub).mul (continuousOn_id.mul (hderF.mono hsub))))).mul
      (hH.continuousOn.mono hsub)
    refine h.congr ?_
    intro z hz
    simp only [hI2, Pi.mul_apply, Pi.add_apply, id_eq]
  have hInt1 : IntervalIntegrable I1 MeasureTheory.volume a b :=
    hcont1.intervalIntegrable_of_Icc hab.le
  have hInt2 : IntervalIntegrable I2 MeasureTheory.volume a b :=
    hcont2.intervalIntegrable_of_Icc hab.le
  -- the flux and its derivative
  set G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * z * H z * (z * deriv F z) with hG
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt G (I1 x + I2 x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    have hzw : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
        ((Work.Spaces.w x) ^ 2 * bcoefR x) x := deriv_zw_sq x (hzpos x hx)
    have hzF : HasDerivAt (fun y : ℝ => y * deriv F y)
        (x * deriv (deriv F) x + deriv F x) x :=
      ((hasDerivAt_id x).mul (hddF x hx)).congr_deriv (by simp only [id_eq]; ring)
    have h1 : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y * H y)
        (((Work.Spaces.w x) ^ 2 * bcoefR x) * H x
          + ((Work.Spaces.w x) ^ 2 * x) * deriv H x) x := hzw.mul (hdH x hx)
    have h2 : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y * H y * (y * deriv F y))
        ((((Work.Spaces.w x) ^ 2 * bcoefR x) * H x
            + ((Work.Spaces.w x) ^ 2 * x) * deriv H x) * (x * deriv F x)
          + ((Work.Spaces.w x) ^ 2 * x * H x)
            * (x * deriv (deriv F) x + deriv F x)) x := h1.mul hzF
    have hfun : (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y * H y * (y * deriv F y)) = G := by
      funext y; rw [hG]
    rw [hfun] at h2
    refine h2.congr_deriv ?_
    have hzwz : deriv (fun y : ℝ => y * deriv F y) x = x * deriv (deriv F) x + deriv F x :=
      hzF.deriv
    rw [hI1, hI2]
    simp only [hzwz]
    ring
  have hIntG : IntervalIntegrable (fun z : ℝ => I1 z + I2 z) MeasureTheory.volume a b :=
    hInt1.add hInt2
  have hFTC : (∫ z in a..b, I1 z + I2 z) = G b - G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntG
  have hsplit : (∫ z in a..b, I1 z + I2 z) = (∫ z in a..b, I1 z) + (∫ z in a..b, I2 z) :=
    intervalIntegral.integral_add hInt1 hInt2
  have hval : G b = (Work.Spaces.w b) ^ 2 * b * H b * (b * deriv F b) := by rw [hG]
  have hval' : G a = (Work.Spaces.w a) ^ 2 * a * H a * (a * deriv F a) := by rw [hG]
  rw [hval, hval'] at hFTC
  rw [hsplit] at hFTC
  rw [hI1] at hFTC
  rw [hI2] at hFTC
  linarith [hFTC]


end Work.FTS.EllipticEst.TT
