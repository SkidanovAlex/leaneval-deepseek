/-
# The `Z5` bound of the `D_z`-coercivity estimate

This file proves `bound_Z5`, the estimate for the fifth term `Z5` in the expansion
`D_z(𝓛_Γ^T f) = Z1 + ⋯ + Z7` of `Dz_LGammaT_decomp`, namely

`wip Weta (Z5 f) (D_z f) ≥ -(1/32) EDz f - 10 EDth α f`

together with the joint integrability of the integrand.

Since `Z5 f z θ = (3z/(1+z)²) · D_θ f z θ`, the estimate is the AM–GM inequality
`(3/4)|a||b| ≤ (1/32)b² + (9/2)a²` applied with `a = D_θ f · w·sin(2θ)^{-η/2}` and
`b = D_z f · w·sin(2θ)^{-η/2}`, using `3z/(1+z)² ≤ 3/4` for `z ≥ 0` and
`sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `Iθ`.

The subtle point is again joint integrability: `CoerciveData` only provides integrability
of *quadratic* products, so the integrand is written as

`Z5 f · D_z f · Weta = c(z) · (D_θf·f·Weta)·(D_zf·f·Weta) / (f²·Weta)`

which exhibits it as an a.e. strongly measurable function (Lean's totalised division
`0/0 = 0` makes the identity valid wherever the right-hand side is defined).  The algebraic
identity can only fail where `f = 0`, `Weta ≠ 0` and `D_θ f · D_z f ≠ 0`; that set is null
because at such a point `z ↦ f z θ` vanishes with nonzero derivative, so it is an isolated
zero of the slice, and isolated zeros are countable.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Coercivity.zero_set_deriv_countable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The product measure of the two restricted Lebesgue measures -/

/-- The product of the restrictions of Lebesgue measure to `Iz` and `Iθ`. -/
private abbrev Pzθ : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

private theorem Pzθ_eq : Pzθ = volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) :=
  prod_restrict_eq _ _

private theorem ae_mem_dom : ∀ᵐ p ∂Pzθ, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
  rw [Pzθ_eq]
  exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-! ## The pointwise AM–GM inequality -/

private theorem three_z_div_sq_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ 3 * z / (1 + z) ^ 2 :=
  div_nonneg (mul_nonneg (by norm_num) hz) (sq_nonneg _)

private theorem three_z_div_sq_le {z : ℝ} (hz : 0 ≤ z) : 3 * z / (1 + z) ^ 2 ≤ 3 / 4 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

private theorem three_quarters_mul_le (X Y : ℝ) :
    (3 / 4) * |X| * |Y| ≤ (1 / 32) * |Y| ^ 2 + (9 / 2) * |X| ^ 2 := by
  nlinarith [sq_nonneg (|Y| - 12 * |X|)]

private theorem Weta_nonneg {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Weta z θ := by
  rw [Weta]
  have h1 : 0 ≤ Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact mul_nonneg (pow_nonneg h1 2) (Real.rpow_nonneg h2 _)

private theorem amgm_abs_Z5 (c X Y W : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 3 / 4) (hW : 0 ≤ W) :
    |c * X * Y * W| ≤ (1 / 32) * Y ^ 2 * W + (9 / 2) * X ^ 2 * W := by
  have haux : |c * X * Y * W| = c * |X| * |Y| * W := by
    simp only [abs_mul, abs_of_nonneg hc0, abs_of_nonneg hW]
  rw [haux]
  have h2 : c * |X| * |Y| ≤ (1 / 32) * |Y| ^ 2 + (9 / 2) * |X| ^ 2 := by
    have hA : c * |X| * |Y| ≤ (3 / 4) * |X| * |Y| := by
      have h := mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg X) (abs_nonneg Y))
      calc c * |X| * |Y| = c * (|X| * |Y|) := by ring
        _ ≤ (3 / 4) * (|X| * |Y|) := h
        _ = (3 / 4) * |X| * |Y| := by ring
    exact hA.trans (three_quarters_mul_le X Y)
  have h3 : c * |X| * |Y| * W ≤ ((1 / 32) * |Y| ^ 2 + (9 / 2) * |X| ^ 2) * W :=
    mul_le_mul_of_nonneg_right h2 hW
  have h4 : ((1 / 32) * |Y| ^ 2 + (9 / 2) * |X| ^ 2) * W
      = (1 / 32) * Y ^ 2 * W + (9 / 2) * X ^ 2 * W := by
    rw [sq_abs, sq_abs]; ring
  rwa [h4] at h3

private theorem Z5_pt_abs (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    |Z5 f z θ * Spaces.Dz f z θ * Weta z θ| ≤
      (1 / 32) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        + (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hW := Weta_nonneg hz hθ
  have hc0 := three_z_div_sq_nonneg hz
  have hc := three_z_div_sq_le hz
  obtain ⟨hs0, hs1⟩ : 0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]),
      Real.sin_le_one _⟩
  have hgam : Spaces.eta ≤ Spaces.gam α := by rw [Spaces.eta, Spaces.gam]; linarith
  have hle := rpow_neg_eta_le_gam hs0 hs1 hgam
  have hmain := amgm_abs_Z5 (3 * z / (1 + z) ^ 2) (Spaces.Dth f z θ) (Spaces.Dz f z θ)
    (Weta z θ) hc0 hc hW
  rw [show Z5 f z θ * Spaces.Dz f z θ * Weta z θ
      = (3 * z / (1 + z) ^ 2) * Spaces.Dth f z θ * Spaces.Dz f z θ * Weta z θ from by
    rw [Z5]]
  refine hmain.trans ?_
  have hkey : (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Weta z θ
      ≤ (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    unfold Weta
    calc (9 / 2) * (Spaces.Dth f z θ) ^ 2
            * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        = ((9 / 2) * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2)
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by ring
      _ ≤ ((9 / 2) * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by ring
  linarith [hkey]

private theorem Z5_pt_lower (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    -((1 / 32) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        + 10 * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      ≤ Z5 f z θ * Spaces.Dz f z θ * Weta z θ := by
  have hW := Weta_nonneg hz hθ
  have hc0 := three_z_div_sq_nonneg hz
  have hc := three_z_div_sq_le hz
  obtain ⟨hs0, hs1⟩ : 0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]),
      Real.sin_le_one _⟩
  have hgam : Spaces.eta ≤ Spaces.gam α := by rw [Spaces.eta, Spaces.gam]; linarith
  have hle := rpow_neg_eta_le_gam hs0 hs1 hgam
  have hmain := amgm_abs_Z5 (3 * z / (1 + z) ^ 2) (Spaces.Dth f z θ) (Spaces.Dz f z θ)
    (Weta z θ) hc0 hc hW
  have hkey : (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Weta z θ
      ≤ 10 * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    have hstep : (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
      mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    have hcoef : (9 : ℝ) / 2 * (Spaces.Dth f z θ) ^ 2 ≤ 10 * (Spaces.Dth f z θ) ^ 2 := by
      have := sq_nonneg (Spaces.Dth f z θ); linarith
    have hmain' := mul_le_mul hcoef hstep
      (by positivity : (0 : ℝ) ≤ (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (by positivity : (0 : ℝ) ≤ 10 * (Spaces.Dth f z θ) ^ 2)
    have hnorm : (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Weta z θ
        = ((9 / 2) * (Spaces.Dth f z θ) ^ 2)
            * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
      unfold Weta; ring
    calc (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Weta z θ
        = ((9 / 2) * (Spaces.Dth f z θ) ^ 2)
            * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := hnorm
      _ ≤ (10 * (Spaces.Dth f z θ) ^ 2)
            * ((Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := hmain'
      _ = 10 * (Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by ring
  have hA : (1 / 32) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
      + (9 / 2) * (Spaces.Dth f z θ) ^ 2 * Weta z θ
      ≤ (1 / 32) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        + 10 * (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    linarith [hkey]
  have hneg := neg_le_of_abs_le hmain
  rw [show Z5 f z θ * Spaces.Dz f z θ * Weta z θ
      = (3 * z / (1 + z) ^ 2) * Spaces.Dth f z θ * Spaces.Dz f z θ * Weta z θ from by
    rw [Z5]]
  linarith [hneg, hA]

/-! ## Almost-everywhere strong measurability of the ingredients -/

private theorem aesm_fsq_Weta (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 ^ 2 * Weta p.1 p.2) Pzθ := by
  have h1 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Pzθ := by
    rw [Pzθ_eq]; exact hi.intFeta
  refine h1.aestronglyMeasurable.congr ?_
  filter_upwards with p
  simp only [Weta]
  ring

private theorem aesm_Dth_sq_gam (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ := by
  have h1 : Integrable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ := by
    rw [Pzθ_eq]; exact hi.intDthGam
  refine h1.aestronglyMeasurable.congr ?_
  filter_upwards with p
  ring

private theorem aesm_Dz_sq_Weta (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) Pzθ := by
  have h1 : Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Pzθ := by
    rw [Pzθ_eq]; exact hi.intDz
  refine h1.aestronglyMeasurable.congr ?_
  filter_upwards with p
  simp only [Weta]
  ring

private theorem aesm_Dth_mul_f (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * f p.1 p.2
      * Weta p.1 p.2) Pzθ := by
  have h1 : Integrable (fun p : ℝ × ℝ =>
      Transport f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) Pzθ := by
    rw [Pzθ_eq]; exact hi.intT
  have h2 : Measurable (fun p : ℝ × ℝ =>
      ((1 + p.1) / 3) * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by fun_prop
  refine ((h1.aestronglyMeasurable.mul h2.aestronglyMeasurable)).congr ?_
  filter_upwards [ae_mem_dom] with p hp
  obtain ⟨hz, hθ⟩ := hp
  have h1z : (1 : ℝ) + p.1 ≠ 0 := by
    have : (0 : ℝ) ≤ p.1 := hz
    positivity
  simp only [Pi.mul_apply, Weta, Transport]
  field_simp

private theorem aesm_Dz_mul_f (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * f p.1 p.2
      * Weta p.1 p.2) Pzθ := by
  have hL : Integrable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      Pzθ := by
    rw [Pzθ_eq]; exact hi.intL
  have hF2 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      Pzθ := by
    rw [Pzθ_eq]; exact f_sq_w_sq_integrable α f hi
  have h2 : Measurable (fun p : ℝ × ℝ => (1 - 2 / (1 + p.1))) := by fun_prop
  have h3 : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by fun_prop
  have hcomb : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2
        - (1 - 2 / (1 + p.1)) * (f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)) Pzθ :=
    hL.aestronglyMeasurable.sub (h2.aestronglyMeasurable.mul hF2.aestronglyMeasurable)
  refine ((hcomb.mul h3.aestronglyMeasurable)).congr ?_
  filter_upwards [ae_mem_dom] with p hp
  obtain ⟨hz, hθ⟩ := hp
  have h1z : (1 : ℝ) + p.1 ≠ 0 := by
    have : (0 : ℝ) ≤ p.1 := by exact hz
    positivity
  simp only [Pi.mul_apply, Weta, L, Spaces.Dz]
  field_simp
  ring

/-! ## The algebraic identity behind the integrand -/

/-- The set on which the algebraic identity
`Z5 f · D_z f · Weta = c(z) · (D_θf·f·Weta)·(D_zf·f·Weta)/(f²·Weta)` can fail is null. -/
private theorem ae_not_failure (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    ∀ᵐ p ∂Pzθ, ¬ (f p.1 p.2 = 0 ∧ Weta p.1 p.2 ≠ 0
      ∧ Spaces.Dth f p.1 p.2 ≠ 0 ∧ Spaces.Dz f p.1 p.2 ≠ 0) := by
  obtain ⟨V, hVsm, hVae⟩ := aesm_fsq_Weta α f hi
  obtain ⟨U, hUsm, hUae⟩ := aesm_Dth_sq_gam α f hi
  obtain ⟨Wz, hWzsm, hWzae⟩ := aesm_Dz_sq_Weta α f hi
  have hVmeas : Measurable V := hVsm.measurable
  have hUmeas : Measurable U := hUsm.measurable
  have hWzmeas : Measurable Wz := hWzsm.measurable
  -- the measurable surrogate
  have hHmeas : MeasurableSet {p : ℝ × ℝ | V p = 0 ∧ U p ≠ 0 ∧ Wz p ≠ 0} :=
    (hVmeas (measurableSet_singleton 0)).inter
      ((hUmeas (measurableSet_singleton 0).compl).inter
        (hWzmeas (measurableSet_singleton 0).compl))
  -- slices of the three differences are null for a.e. `z`
  have hVn : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      (volume.restrict Spaces.Iθ) {θ : ℝ | f z θ ^ 2 * Weta z θ ≠ V (z, θ)} = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hVae] with z hz
    exact MeasureTheory.ae_iff.mp hz
  have hUn : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      (volume.restrict Spaces.Iθ) {θ : ℝ | (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) ≠ U (z, θ)} = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hUae] with z hz
    exact MeasureTheory.ae_iff.mp hz
  have hWzn : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      (volume.restrict Spaces.Iθ) {θ : ℝ | (Spaces.Dz f z θ) ^ 2 * Weta z θ ≠ Wz (z, θ)} = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hWzae] with z hz
    exact MeasureTheory.ae_iff.mp hz
  -- the surrogate set is null
  have hHnull : Pzθ {p : ℝ × ℝ | V p = 0 ∧ U p ≠ 0 ∧ Wz p ≠ 0} = 0 := by
    rw [Measure.prod_apply hHmeas]
    refine (MeasureTheory.lintegral_eq_zero_iff'
      (measurable_measure_prodMk_left hHmeas).aemeasurable).mpr ?_
    filter_upwards [hVn, hUn, hWzn] with z hVz hUz hWzz
    have hcount : ({θ : ℝ | f z θ = 0 ∧ deriv (fun u : ℝ => f z u) θ ≠ 0}).Countable :=
      zero_set_deriv_countable (fun θ : ℝ => f z θ)
    have htheta : (volume.restrict Spaces.Iθ) (Spaces.Iθᶜ) = 0 := by
      show (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
        ((Set.Icc (0 : ℝ) (Real.pi / 2))ᶜ) = 0
      rw [MeasureTheory.Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self,
        measure_empty]
    refine measure_mono_null ?_ (measure_union_null (measure_union_null (measure_union_null
      (measure_union_null (Set.Countable.measure_zero hcount _) hVz) hUz) hWzz) htheta)
    intro θ hθ
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hθ
    have hdisj : (f z θ = 0 ∧ deriv (fun u : ℝ => f z u) θ ≠ 0)
        ∨ f z θ ^ 2 * Weta z θ ≠ V (z, θ)
        ∨ (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            ≠ U (z, θ)
        ∨ (Spaces.Dz f z θ) ^ 2 * Weta z θ ≠ Wz (z, θ)
        ∨ θ ∉ Spaces.Iθ := by
      by_cases h1 : f z θ = 0 ∧ deriv (fun u : ℝ => f z u) θ ≠ 0
      · exact Or.inl h1
      · by_cases h2 : f z θ ^ 2 * Weta z θ ≠ V (z, θ)
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
              * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) ≠ U (z, θ)
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : (Spaces.Dz f z θ) ^ 2 * Weta z θ ≠ Wz (z, θ)
            · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
            · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
              by_contra hθI
              have h2' : f z θ ^ 2 * Weta z θ = V (z, θ) := by
                by_contra hh; exact h2 hh
              have h3' : (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) = U (z, θ) := by
                by_contra hh; exact h3 hh
              have h4' : (Spaces.Dz f z θ) ^ 2 * Weta z θ = Wz (z, θ) := by
                by_contra hh; exact h4 hh
              have hWeta : Weta z θ ≠ 0 := by
                intro h0
                exact hθ.2.2 (by rw [← h4', h0, mul_zero])
              have hf : f z θ = 0 := by
                have h1' : f z θ ^ 2 * Weta z θ = 0 := by rw [h2', hθ.1]
                rcases mul_eq_zero.mp h1' with h | h
                · exact sq_eq_zero_iff.mp h
                · exact absurd h hWeta
              have hDth : Spaces.Dth f z θ ≠ 0 := by
                intro h0
                exact hθ.2.1 (by rw [← h3', h0]; simp)
              have hpth : Spaces.pth f z θ ≠ 0 := by
                intro h0
                exact hDth (by rw [Spaces.Dth, h0, mul_zero])
              exact h1 ⟨hf, hpth⟩
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  -- the failure set is contained in the surrogate together with the differences
  have hsub : {p : ℝ × ℝ | f p.1 p.2 = 0 ∧ Weta p.1 p.2 ≠ 0
      ∧ Spaces.Dth f p.1 p.2 ≠ 0 ∧ Spaces.Dz f p.1 p.2 ≠ 0}
      ⊆ {p : ℝ × ℝ | V p = 0 ∧ U p ≠ 0 ∧ Wz p ≠ 0}
        ∪ {p : ℝ × ℝ | f p.1 p.2 ^ 2 * Weta p.1 p.2 ≠ V p}
        ∪ {p : ℝ × ℝ | (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) ≠ U p}
        ∪ {p : ℝ × ℝ | (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ≠ Wz p}
        ∪ {p : ℝ × ℝ | p.1 ∈ ({0, -1} : Set ℝ)}
        ∪ {p : ℝ × ℝ | p.2 ∉ Spaces.Iθ} := by
    rintro p ⟨hf0, hWne, hDth, hDz⟩
    have hdisj : (V p = 0 ∧ U p ≠ 0 ∧ Wz p ≠ 0)
        ∨ f p.1 p.2 ^ 2 * Weta p.1 p.2 ≠ V p
        ∨ (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) ≠ U p
        ∨ (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ≠ Wz p
        ∨ p.1 ∈ ({0, -1} : Set ℝ)
        ∨ p.2 ∉ Spaces.Iθ := by
      by_cases hH : V p = 0 ∧ U p ≠ 0 ∧ Wz p ≠ 0
      · exact Or.inl hH
      · by_cases h2 : f p.1 p.2 ^ 2 * Weta p.1 p.2 ≠ V p
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) ≠ U p
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ≠ Wz p
            · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
            · by_cases h5 : p.1 ∈ ({0, -1} : Set ℝ)
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
                by_contra hθI
                have hV' : f p.1 p.2 ^ 2 * Weta p.1 p.2 = V p := by
                  by_contra hh; exact h2 hh
                have hU' : (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
                    * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) = U p := by
                  by_contra hh; exact h3 hh
                have hWz' : (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 = Wz p := by
                  by_contra hh; exact h4 hh
                have hV0 : V p = 0 := by rw [← hV', hf0]; ring
                have hw : Spaces.w p.1 ≠ 0 := by
                  intro h0
                  refine h5 ?_
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
                  have h1 : (1 + p.1) ^ 2 / p.1 ^ 2 = 0 := h0
                  rcases div_eq_zero_iff.mp h1 with h | h
                  · right
                    have h3' : (1 : ℝ) + p.1 = 0 := sq_eq_zero_iff.mp h
                    linarith
                  · left
                    exact sq_eq_zero_iff.mp h
                have hsin : 0 < Real.sin (2 * p.2) := by
                  have h3' : 0 ≤ Real.sin (2 * p.2) :=
                    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
                      (by linarith [hθI.2, Real.pi_pos])
                  rcases lt_or_eq_of_le h3' with h | h
                  · exact h
                  · exfalso
                    have h4' : (Real.sin (2 * p.2)) ^ (-Spaces.eta) = 0 := by
                      simpa only [h] using (Real.zero_rpow (show (-Spaces.eta) ≠ 0 by
                        norm_num [Spaces.eta]) : (0 : ℝ) ^ (-Spaces.eta) = 0)
                    exact hWne (by rw [Weta, h4', mul_zero])
                have hU0 : U p ≠ 0 := by
                  rw [← hU']
                  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hDth) (pow_ne_zero 2 hw))
                    (ne_of_gt (Real.rpow_pos_of_pos hsin _))
                have hWz0 : Wz p ≠ 0 := by
                  rw [← hWz']
                  exact mul_ne_zero (pow_ne_zero 2 hDz) hWne
                exact hH ⟨hV0, hU0, hWz0⟩
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  -- the two exceptional sets are null
  have hznull : Pzθ {p : ℝ × ℝ | p.1 ∈ ({0, -1} : Set ℝ)} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 ∈ ({0, -1} : Set ℝ)}
        = ({0, -1} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [hset, Measure.prod_prod]
    have hc : ({0, -1} : Set ℝ).Countable :=
      ((Set.finite_singleton (-1)).insert 0).countable
    rw [hc.measure_zero (volume.restrict Spaces.Iz), zero_mul]
  have hthetanull : Pzθ {p : ℝ × ℝ | p.2 ∉ Spaces.Iθ} = 0 := by
    have hset : {p : ℝ × ℝ | p.2 ∉ Spaces.Iθ} = (Set.univ : Set ℝ) ×ˢ Spaces.Iθᶜ := by
      ext p; simp
    rw [hset, Measure.prod_prod]
    have h0 : (volume.restrict Spaces.Iθ) (Spaces.Iθᶜ) = 0 := by
      show (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
        ((Set.Icc (0 : ℝ) (Real.pi / 2))ᶜ) = 0
      rw [MeasureTheory.Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self,
        measure_empty]
    rw [h0, mul_zero]
  have hF0 : Pzθ {p : ℝ × ℝ | f p.1 p.2 = 0 ∧ Weta p.1 p.2 ≠ 0
      ∧ Spaces.Dth f p.1 p.2 ≠ 0 ∧ Spaces.Dz f p.1 p.2 ≠ 0} = 0 := by
    refine measure_mono_null hsub ?_
    exact measure_union_null (measure_union_null (measure_union_null (measure_union_null
      (measure_union_null hHnull (MeasureTheory.ae_iff.mp hVae))
      (MeasureTheory.ae_iff.mp hUae)) (MeasureTheory.ae_iff.mp hWzae)) hznull) hthetanull
  refine (MeasureTheory.ae_iff).mpr ?_
  simpa only [not_not] using hF0

/-! ## The main estimate -/

theorem bound_Z5 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z5 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)
    ∧ wip Weta (Z5 f) (Spaces.Dz f) ≥ -((1 / 32) * EDz f + 10 * EDth α f) := by
  have hV := aesm_fsq_Weta α f hi
  have hA := aesm_Dth_mul_f α f hi
  have hB := aesm_Dz_mul_f α f hi
  have hfail := ae_not_failure α f hi
  -- a.e. strong measurability of the integrand via the algebraic identity
  have hG : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Z5 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pzθ := by
    have hnum : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Spaces.Dth f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)
          * (Spaces.Dz f p.1 p.2 * f p.1 p.2 * Weta p.1 p.2)
          / ((f p.1 p.2) ^ 2 * Weta p.1 p.2)) Pzθ := (hA.mul hB).div₀ hV
    have hc : Measurable (fun p : ℝ × ℝ => 3 * p.1 / (1 + p.1) ^ 2) := by fun_prop
    refine ((hc.aestronglyMeasurable.mul hnum)).congr ?_
    filter_upwards [hfail] with p hp
    simp only [Pi.mul_apply, Z5]
    by_cases hf : f p.1 p.2 = 0
    · by_cases hW : Weta p.1 p.2 = 0
      · simp [hW]
      · have hnot : ¬ (Spaces.Dth f p.1 p.2 ≠ 0 ∧ Spaces.Dz f p.1 p.2 ≠ 0) := by
          intro hcon
          exact hp ⟨hf, hW, hcon.1, hcon.2⟩
        rcases not_and_or.mp hnot with h0 | h0
        · rw [not_not] at h0; simp [h0]
        · rw [not_not] at h0; simp [h0]
    · by_cases hW : Weta p.1 p.2 = 0
      · simp [hW]
      · have hVne : (f p.1 p.2) ^ 2 * Weta p.1 p.2 ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 hf) hW
        field_simp
  -- the dominating function and the lower bound are integrable
  have hintDz : Integrable (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Pzθ := by
    rw [Pzθ_eq]; exact hi.intDz
  have hintDth : Integrable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ := by
    rw [Pzθ_eq]; exact hi.intDthGam
  have hDz2 : Integrable (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) Pzθ := by
    refine hintDz.congr ?_
    filter_upwards with p
    simp only [Weta]; ring
  have hDth2 : Integrable (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ := by
    refine hintDth.congr ?_
    filter_upwards with p
    ring
  have hDz2c : Integrable (fun p : ℝ × ℝ => (1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2
      * Weta p.1 p.2) Pzθ :=
    (hDz2.const_mul (1 / 32)).congr (Eventually.of_forall fun p => by ring)
  have hDth2c : Integrable (fun p : ℝ × ℝ => 10 * (Spaces.Dth f p.1 p.2) ^ 2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ :=
    (hDth2.const_mul 10).congr (Eventually.of_forall fun p => by ring)
  have hDth2c9 : Integrable (fun p : ℝ × ℝ => (9 / 2) * (Spaces.Dth f p.1 p.2) ^ 2
      * Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ :=
    (hDth2.const_mul (9 / 2)).congr (Eventually.of_forall fun p => by ring)
  have hR : Integrable (fun p : ℝ × ℝ =>
      (1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2
        + (9 / 2) * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Pzθ :=
    hDz2c.add hDth2c9
  have hLint : Integrable (fun p : ℝ × ℝ =>
      -((1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2
        + 10 * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))) Pzθ :=
    (hDz2c.add hDth2c).neg
  -- integrability of the integrand
  have hIntOn : IntegrableOn
      (Function.uncurry (fun z θ => Z5 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, ← Pzθ_eq]
    refine hR.mono' hG ?_
    filter_upwards [ae_mem_dom] with p hp
    obtain ⟨hz, hθ⟩ := hp
    rw [Real.norm_eq_abs]
    exact Z5_pt_abs α hα f hz hθ
  refine ⟨hIntOn, ?_⟩
  have hGint : Integrable (fun p : ℝ × ℝ =>
      Z5 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) Pzθ := by
    rw [Pzθ_eq]; exact hIntOn
  have hwip : wip Weta (Z5 f) (Spaces.Dz f)
      = ∫ p, Z5 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pzθ :=
    wip_eq_integral_prod Weta (Z5 f) (Spaces.Dz f) hIntOn
  have hmono : (∫ p, -((1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2
        + 10 * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) ∂Pzθ)
      ≤ ∫ p, Z5 f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂Pzθ := by
    refine integral_mono_ae hLint hGint ?_
    filter_upwards [ae_mem_dom] with p hp
    obtain ⟨hz, hθ⟩ := hp
    exact Z5_pt_lower α hα f hz hθ
  have hEDz : EDz f = ∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pzθ := by
    have h := wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz f) (Spaces.Dz f) (by
        refine hi.intDz.congr ?_
        filter_upwards with p
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair, Weta]; ring)
    rw [EDz_eq_wip f, h]
    congr 1 with p
    rw [Weta]; ring
  have hEDth : EDth α f = ∫ p, (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) ∂Pzθ := by
    have h := wip_eq_integral_prod
      (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) (by
        refine hi.intDthGam.congr ?_
        filter_upwards with p
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]; ring)
    rw [EDth_eq_wip α f, h]
    congr 1 with p
    ring_nf
  have hval : (∫ p, -((1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2
        + 10 * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) ∂Pzθ)
      = -((1 / 32) * EDz f + 10 * EDth α f) := by
    have hA : (∫ p, (1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂Pzθ)
        = (1 / 32) * EDz f := by
      rw [show (fun p : ℝ × ℝ => (1 / 32) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)
          = fun p => (1 / 32) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) from by
        funext p; ring]
      rw [integral_const_mul, ← hEDz]
    have hB : (∫ p, 10 * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) ∂Pzθ) = 10 * EDth α f := by
      rw [show (fun p : ℝ × ℝ => 10 * (Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))
          = fun p => 10 * ((Spaces.Dth f p.1 p.2) ^ 2 * Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) from by
        funext p; ring]
      rw [integral_const_mul, ← hEDth]
    rw [integral_neg, integral_add hDz2c hDth2c, hA, hB]
  rw [hwip]
  linarith [hmono, hval]

end Work.Coercivity
