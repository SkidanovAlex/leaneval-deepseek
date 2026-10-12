import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.ScatT3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Scattering `g`-integrals via the Newton representation (Layer 3 / Layer 5)

For a radial weak scattering solution `w` of a non-negative radial `v`
(`tsupport v ⊆ ball 0 R`), with `g := v·(1−w)` (the corpus's scattering
`g`), this module records the basic integrability/bounds of the quantities
that the Fournais--Solovej box-bound package expresses in terms of the
"zero-momentum values" `ĝ(0) = ∫g` and `ĝω(0) = ∫g·ω`:

  * `g·w` is integrable and `0 ≤ ∫g·w ≤ ∫g` (uses `0 ≤ g` a.e. and
    `0 ≤ w ≤ 1` a.e. — `ScatT3.scattering_g_nonneg` +
    `ScatT3.scattering_bounds_ae`);
  * **Newton double integral identity**: multiplying the Newton
    representation (`NewtonRep.scattering_newton_representation`:
    `w x = (8π)⁻¹ ∫_y g(y)/‖x−y‖ dy` a.e.) by `g(x) ≥ 0` and integrating over
    `x` gives (Tonelli for non-negative integrands)
        ∫∫ g(x)·g(y)/‖x−y‖ dx dy = 8π · ∫ g(x)·w(x) dx = 8π·ĝω(0).
    This is the x-space substitute for the Fourier identity
    `ŵ(k) = ĝ(k)/(2k²)` (FS eq:scatteringFourier): wherever FS convert a
    momentum-space integral into `∫∫g g/|x−y|` (e.g. eq:HLS in the proof of
    their eq:I2-integral lemma), the corpus will use this identity directly.

No new Fourier infrastructure is needed (see NOTES.md Layer-5 architecture,
decision 1).  All statements are for an *arbitrary* radial scattering solution
`w` of a radial non-negative `v`; in the chosen branch of `a v ≠ 0` they
apply to `w₀` where additionally `∫v(1−w₀) = 8π·a v`
(`ScatChosen.chosen_scattering_integral`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `g·ω` is bounded between `0` and `g` almost everywhere
(`g := v·(1−w)`), using `0 ≤ g` a.e. and `0 ≤ ω ≤ 1` a.e. -/
lemma scat_gomega_ae_bounds {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∀ᵐ x : ℝ³, 0 ≤ (v x * (1 - w x)) * w x) ∧
      (∀ᵐ x : ℝ³, (v x * (1 - w x)) * w x ≤ v x * (1 - w x)) := by
  have hbounds := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hrad hw
  have hg := scattering_g_nonneg hR hv_nonneg hvrad hv_supp hrad hw
  constructor
  · filter_upwards [hg, hbounds.1] with x hgx hw0
    exact mul_nonneg hgx hw0
  · filter_upwards [hg, hbounds.2] with x hgx hw1
    simpa [mul_one] using
      (mul_le_mul_of_nonneg_left (a := v x * (1 - w x)) (b := w x) (c := 1) hw1 hgx)

/-- `g·ω := v(1−w)·w` is (globally) integrable (its modulus is `≤ |g|` a.e.
and `g` is integrable by `ScatG.scatG_integrable`). -/
theorem scat_gomega_integrable {v w : ℝ³ → ℝ} {R : ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    MeasureTheory.Integrable (fun x : ℝ³ => (v x * (1 - w x)) * w x) := by
  by_cases hR : 0 < R
  · have hb := scat_gomega_ae_bounds hR hv_nonneg hvrad hv_supp hrad hw
    have hg := scattering_g_nonneg hR hv_nonneg hvrad hv_supp hrad hw
    have hG : MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - w x)) :=
      scatG_integrable hv_supp hw
    have hFsm : AEStronglyMeasurable (fun x : ℝ³ => (v x * (1 - w x)) * w x) := by
      exact hG.aestronglyMeasurable.mul hw.lhs_integrable.aestronglyMeasurable
    have hbd : ∀ᵐ x : ℝ³, ‖((v x * (1 - w x)) * w x : ℝ)‖ ≤ ‖(v x * (1 - w x) : ℝ)‖ := by
      filter_upwards [hb.1, hb.2, hg] with x hf0 hfle hg0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0, abs_of_nonneg hg0]
      exact hfle
    exact MeasureTheory.Integrable.mono hG hFsm hbd
  · have hR0 : R ≤ 0 := le_of_not_gt hR
    have hF0 : (fun x : ℝ³ => (v x * (1 - w x)) * w x) = fun _ : ℝ³ => (0 : ℝ) := by
      funext x
      have hvx : v x = 0 := v_eq_zero_of_norm_ge hv_supp (by linarith [norm_nonneg x])
      simp [hvx]
    rw [hF0]
    exact MeasureTheory.integrable_zero ℝ³ ℝ volume

/-- `0 ≤ ∫g·ω ≤ ∫g` where `g := v(1−w)`. -/
theorem scat_gomega_integral_bounds {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    0 ≤ (∫ x : ℝ³, (v x * (1 - w x)) * w x) ∧
      (∫ x : ℝ³, (v x * (1 - w x)) * w x) ≤ (∫ x : ℝ³, v x * (1 - w x)) := by
  have hb := scat_gomega_ae_bounds hR hv_nonneg hvrad hv_supp hrad hw
  have hFi : MeasureTheory.Integrable (fun x : ℝ³ => (v x * (1 - w x)) * w x) :=
    scat_gomega_integrable hv_nonneg hvrad hv_supp hrad hw
  have hG : MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - w x)) :=
    scatG_integrable hv_supp hw
  constructor
  · exact MeasureTheory.integral_nonneg_of_ae hb.1
  · exact MeasureTheory.integral_mono_ae hFi hG hb.2

/-- **Newton double-integral identity.**  For a radial weak scattering solution
`w` of a radial `v` (`tsupport v ⊆ ball 0 R`):
`∫∫ g(x)·g(y)/‖x−y‖ dx dy = 8π·∫ g(x)·w(x) dx`, `g := v(1−w)`.
Proof: multiply the a.e. Newton representation by the a.e.-non-negative `g`
and integrate over `x` (Tonelli). -/
theorem scattering_newton_double_eq {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) =
      8 * π * (∫ x : ℝ³, (v x * (1 - w x)) * w x) := by
  have hrep : ∀ᵐ x : ℝ³,
      w x = (1 / (8 * π)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
    exact scattering_newton_representation (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
  have hinner (x : ℝ³) :
      (∫ y : ℝ³, (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) =
        (v x * (1 - w x)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
    calc
      (∫ y : ℝ³, (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)
          = ∫ y : ℝ³, (v x * (1 - w x)) * ((v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              ring
      _ = (v x * (1 - w x)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
              exact MeasureTheory.integral_const_mul (v x * (1 - w x))
                (fun y : ℝ³ => (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)
  have hae :
      (fun x : ℝ³ => (∫ y : ℝ³,
          (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹))
        =ᵐ[volume] (fun x : ℝ³ => 8 * π * ((v x * (1 - w x)) * w x)) := by
    filter_upwards [hrep] with x hx
    have hwI : (8 * π) * w x =
        (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
      have hc : (8 : ℝ) * π ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
      calc
        (8 * π) * w x =
            (8 * π) * ((1 / (8 * π)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)) := by
              rw [hx]
        _ = (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := by
              rw [← mul_assoc, one_div, mul_inv_cancel₀ hc, one_mul]
    calc
      (∫ y : ℝ³, (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)
          = (v x * (1 - w x)) * (∫ y : ℝ³, (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹) := hinner x
      _ = (v x * (1 - w x)) * ((8 * π) * w x) := by
          congr 1
          exact hwI.symm
      _ = 8 * π * ((v x * (1 - w x)) * w x) := by
          ring
  calc
    (∫ x : ℝ³, ∫ y : ℝ³,
        (v x * (1 - w x)) * (v y * (1 - w y)) * (‖x - y‖ : ℝ)⁻¹)
        = ∫ x : ℝ³, 8 * π * ((v x * (1 - w x)) * w x) := MeasureTheory.integral_congr_ae hae
    _ = 8 * π * (∫ x : ℝ³, (v x * (1 - w x)) * w x) := by
        exact MeasureTheory.integral_const_mul (8 * π)
          (fun x : ℝ³ => (v x * (1 - w x)) * w x)

end BoseGases

end Submission
