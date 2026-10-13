import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EfEta_eq_wip
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.f_sq_w_sq_integrable

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

/-! ## The pointwise arithmetic behind the `Z₂` bound

`Z₂ f z θ = 2z/(1+z)² · f z θ`, so the integrand of `wip Weta (Z2 f) (Dz f)` is
`c(z)·f·D_z f·W` with `c(z) = 2z/(1+z)²`.  For `z ≥ 0` one has `0 ≤ c(z) ≤ 1/2`, and the
elementary inequality
`|c·u·v·X| ≤ 4u²X + (1/64)v²X` (AM-GM, using `c ≤ 1/2`) for `X ≥ 0` gives both the
integrability (by domination) and the lower bound of the statement. -/

private theorem cc_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ 2 * z / (1 + z) ^ 2 := by
  positivity

private theorem cc_le_half {z : ℝ} (_hz : 0 ≤ z) : 2 * z / (1 + z) ^ 2 ≤ 1 / 2 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- The AM-GM inequality `|c u v| X ≤ 4u²X + (1/64)v²X` for `0 ≤ c ≤ 1/2` and `X ≥ 0`. -/
private theorem amgm_abs (c u v X : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (hX : 0 ≤ X) :
    |c * u * v * X| ≤ (1 / 64) * (v * v * X) + 4 * (u * u * X) := by
  have hu : u * u = |u| * |u| := by rw [← pow_two, ← pow_two (|u|), sq_abs u]
  have hv : v * v = |v| * |v| := by rw [← pow_two, ← pow_two (|v|), sq_abs v]
  have hle : c * |u| * |v| * X ≤ (1 / 64) * (|v| * |v| * X) + 4 * (|u| * |u| * X) := by
    have hid : (1 / 64) * (|v| * |v|) + 4 * (|u| * |u|) - c * |u| * |v|
        = (|v| / 8 - 2 * |u|) ^ 2 + (1 / 2 - c) * |u| * |v| := by ring
    have hnn : 0 ≤ (1 / 64) * (|v| * |v|) + 4 * (|u| * |u|) - c * |u| * |v| := by
      rw [hid]
      have h2 : 0 ≤ (1 / 2 - c) * |u| * |v| := by
        have h3 : 0 ≤ (1 / 2 - c) * |u| := mul_nonneg (by linarith) (abs_nonneg u)
        exact mul_nonneg h3 (abs_nonneg v)
      nlinarith [sq_nonneg (|v| / 8 - 2 * |u|)]
    nlinarith [mul_nonneg hX hnn]
  calc |c * u * v * X| = c * |u| * |v| * X := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hX]
    _ ≤ (1 / 64) * (v * v * X) + 4 * (u * u * X) := by rw [hu, hv]; exact hle

/-- Pointwise form of the `Z₂` estimate on the quadrant. -/
private theorem bound_Z2_pt (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    |Z2 f z θ * Spaces.Dz f z θ * Weta z θ|
      ≤ (1 / 64) * (Spaces.Dz f z θ * Spaces.Dz f z θ * Weta z θ)
        + 4 * (f z θ * f z θ * Weta z θ) := by
  have hW : 0 ≤ Weta z θ := by
    rw [Weta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have h := amgm_abs (2 * z / (1 + z) ^ 2) (f z θ) (Spaces.Dz f z θ) (Weta z θ)
    (cc_nonneg hz) (cc_le_half hz) hW
  simpa only [Z2] using h

theorem bound_Z2 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z2 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)
    ∧ wip Weta (Z2 f) (Spaces.Dz f) ≥ -((1 / 64) * EDz f + 4 * EfEta f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = P := by
    rw [hP, Measure.volume_eq_prod]
    exact (Measure.prod_restrict _ _).symm
  have hmem : ∀ᵐ p ∂P, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
    rw [← hvol]
    exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  -- ## The two weighted squares are integrable
  have hGz : Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
    rw [← hvol]
    exact hi.intDz
  have hFz : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) P := by
    rw [← hvol]
    exact hi.intFeta
  have hGw : Integrable (fun p : ℝ × ℝ =>
      Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) P :=
    hGz.congr (Eventually.of_forall fun p => by simp only [Weta]; ring)
  have hFw : Integrable (fun p : ℝ × ℝ =>
      f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2) P :=
    hFz.congr (Eventually.of_forall fun p => by simp only [Weta]; ring)
  -- ## `f · D_z f · w²` is a.e. strongly measurable
  have hLf : Integrable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
    rw [← hvol]
    exact hi.intL
  have hF2 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
    rw [← hvol]
    exact f_sq_w_sq_integrable α f hi
  have hfg_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
    have h3 : Measurable (fun p : ℝ × ℝ => 1 - 2 / (1 + p.1)) := by fun_prop
    have h4 := h3.aestronglyMeasurable.mul hF2.aestronglyMeasurable
    refine (hLf.aestronglyMeasurable.sub h4).congr (Eventually.of_forall fun p => ?_)
    show L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        - (1 - 2 / (1 + p.1)) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      = f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2
    simp only [L]
    ring
  -- ## a.e. strong measurability and integrability of the `Z₂` integrand
  have hA_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) P := by
    have hsin : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta)) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
    have hcc : Measurable (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) := by fun_prop
    have h4 := (hcc.aestronglyMeasurable.mul hsin.aestronglyMeasurable).mul hfg_meas
    refine h4.congr (Eventually.of_forall fun p => ?_)
    show (2 * p.1 / (1 + p.1) ^ 2) * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
        * (f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2)
      = Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2
    simp only [Z2, Weta]
    ring
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        + 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)) P :=
    (hGw.const_mul (1 / 64)).add (hFw.const_mul 4)
  have hA : Integrable (fun p : ℝ × ℝ =>
      Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) P := by
    refine hdom.mono' hA_meas ?_
    filter_upwards [hmem] with p hp
    simpa only [Real.norm_eq_abs] using bound_Z2_pt f hp.1 hp.2
  have hAon : IntegrableOn
      (Function.uncurry (fun z θ => Z2 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, hvol]
    exact hA
  -- ## the comparison of integrals
  have hBint : Integrable (fun p : ℝ × ℝ =>
      -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
        - 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)) P :=
    ((hGw.const_mul (1 / 64)).neg).sub (hFw.const_mul 4)
  have hbound : ∀ᵐ p ∂P,
      -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
        - 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)
      ≤ Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 := by
    filter_upwards [hmem] with p hp
    have h' := neg_le_of_abs_le (bound_Z2_pt f hp.1 hp.2)
    have heq : -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
        - 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)
        = -(((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
          + 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)) := by ring
    rw [heq]
    exact h'
  have hmono : (∫ p, -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
        - 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2) ∂P)
      ≤ ∫ p, Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂P :=
    integral_mono_ae hBint hA hbound
  have hBval : (∫ p, -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
        - 4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2) ∂P)
      = -(((1 / 64) * ∫ p, Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂P)
          + 4 * ∫ p, f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2 ∂P) := by
    have hneg : Integrable (fun p : ℝ × ℝ =>
        -((1 / 64) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))) P :=
      (hGw.const_mul (1 / 64)).neg
    have hfour : Integrable (fun p : ℝ × ℝ =>
        4 * (f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)) P := hFw.const_mul 4
    simp only [integral_sub hneg hfour, integral_neg, integral_const_mul]
    ring
  -- ## rewrite the two sides in terms of the product-measure integrals
  have hwipA : wip Weta (Z2 f) (Spaces.Dz f)
      = ∫ p, Z2 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod Weta (Z2 f) (Spaces.Dz f) hAon
  have hwipG : wip Weta (Spaces.Dz f) (Spaces.Dz f)
      = ∫ p, Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂P := by
    rw [hP]
    refine wip_eq_integral_prod Weta (Spaces.Dz f) (Spaces.Dz f) ?_
    rw [IntegrableOn, hvol]
    exact hGw
  have hwipF : wip Weta f f
      = ∫ p, f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2 ∂P := by
    rw [hP]
    refine wip_eq_integral_prod Weta f f ?_
    rw [IntegrableOn, hvol]
    exact hFw
  have hEDz : EDz f = wip Weta (Spaces.Dz f) (Spaces.Dz f) := EDz_eq_wip f
  have hEfEta : EfEta f = wip Weta f f := EfEta_eq_wip f
  refine ⟨hAon, ?_⟩
  rw [hwipA, hEDz, hwipG, hEfEta, hwipF]
  linarith [hmono, hBval]

end Work.Coercivity
