import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.coulInt_integrable_of_le`

The Coulomb-energy double integral `∬ W(x)W(y)/‖x−y‖` of a *dominated* weight is controlled by the
single-slice bound of the dominating weight.  Precisely, if `g ∈ L¹` is non-negative a.e. and its
Coulomb slices satisfy `∫⁻_y ofReal (g y ‖x−y‖⁻¹) ≤ ofReal κ` for a.e. `x`, then any a.e.
non-negative `A ∈ L¹` with `A ≤ c·g` a.e. has integrable Coulomb integrand and

`∫_p coulInt A p ≤ c² κ ∫_x g x`.

The proof is Tonelli (`lintegral_prod`) applied to the non-negative integrand
`g x · (g y ‖x−y‖⁻¹)`, the a.e. slice bound, and the identification
`ofReal (∫ g) = ∫⁻ ofReal (g)` for the non-negative `L¹` function `g`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A one-variable a.e. statement lifts to the first coordinate of the product measure. -/
private lemma ae_prod_fst {p : E3 → Prop} (h : ∀ᵐ x : E3, p x) :
    ∀ᵐ q : E3 × E3 ∂(volume.prod volume), p q.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

/-- A one-variable a.e. statement lifts to the second coordinate of the product measure. -/
private lemma ae_prod_snd {p : E3 → Prop} (h : ∀ᵐ x : E3, p x) :
    ∀ᵐ q : E3 × E3 ∂(volume.prod volume), p q.2 :=
  Measure.quasiMeasurePreserving_snd.ae h

theorem coulInt_integrable_of_le {g A : EuclideanSpace ℝ (Fin 3) → ℝ} {c κ : ℝ}
    (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hg : MeasureTheory.Integrable g) (hg0 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ g x)
    (hA : MeasureTheory.Integrable A) (hA0 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ A x)
    (hAle : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), A x ≤ c * g x)
    (hslice : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) ≤ ENNReal.ofReal κ) :
    MeasureTheory.Integrable (Work.BoseBoxFock.coulInt A) ∧
      (∫ p, Work.BoseBoxFock.coulInt A p) ≤ c ^ 2 * κ * (∫ x, g x) := by
  set F : E3 × E3 → ℝ := fun q => g q.1 * g q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹ with hF
  have hFnn : 0 ≤ᵐ[volume.prod volume] F := by
    filter_upwards [ae_prod_fst hg0, ae_prod_snd hg0] with q h1 h2
    exact mul_nonneg (mul_nonneg h1 h2) (inv_nonneg.mpr (norm_nonneg _))
  -- measurability of the dominating integrand
  have hF_meas : AEMeasurable F (volume.prod volume) := by
    have h1 : AEMeasurable (fun q : E3 × E3 => g q.1) (volume.prod volume) :=
      hg.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun q : E3 × E3 => g q.2) (volume.prod volume) :=
      hg.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h3 : AEMeasurable (fun q : E3 × E3 => (‖q.1 - q.2‖ : ℝ)⁻¹) (volume.prod volume) :=
      (by measurability : Measurable (fun q : E3 × E3 => (‖q.1 - q.2‖ : ℝ)⁻¹)).aemeasurable
    exact (h1.mul h2).mul h3
  have hG_meas : AEMeasurable (fun q : E3 × E3 => ENNReal.ofReal (F q)) (volume.prod volume) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable hF_meas
  -- the master Tonelli/lintegral bound
  have hlint : (∫⁻ q : E3 × E3, ENNReal.ofReal (F q))
      ≤ ENNReal.ofReal κ * ENNReal.ofReal (∫ x, g x) := by
    have hpoint : ∀ x y : E3, F (x, y) = g x * (g y * (‖x - y‖ : ℝ)⁻¹) := by
      intro x y
      simp only [hF]
      ring
    calc (∫⁻ q : E3 × E3, ENNReal.ofReal (F q))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x, y)) := lintegral_prod _ hG_meas
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x) * ENNReal.ofReal (g y * (‖x - y‖ : ℝ)⁻¹) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hg0] with x hx
          refine lintegral_congr (fun y => ?_)
          rw [hpoint x y, ENNReal.ofReal_mul hx]
      _ = ∫⁻ x, ENNReal.ofReal (g x) * (∫⁻ y, ENNReal.ofReal (g y * (‖x - y‖ : ℝ)⁻¹)) := by
          refine lintegral_congr (fun x => ?_)
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal κ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hslice] with x hx
          exact mul_le_mul_of_nonneg_left hx zero_le
      _ = ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (g x) := by
          rw [lintegral_mul_const' (ENNReal.ofReal κ) (fun x => ENNReal.ofReal (g x))
            ENNReal.ofReal_ne_top]
          exact mul_comm _ _
      _ = ENNReal.ofReal κ * ENNReal.ofReal (∫ x, g x) := by
          rw [ofReal_integral_eq_lintegral_ofReal hg hg0]
  have hF_fin : HasFiniteIntegral F (volume.prod volume) :=
    (hasFiniteIntegral_iff_ofReal hFnn).mpr
      (lt_of_le_of_lt hlint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hF_int : Integrable F (volume.prod volume) :=
    ⟨hF_meas.aestronglyMeasurable, hF_fin⟩
  -- the single-slice estimate for `g` integrates to `κ ∫ g`
  have hF_bound : (∫ q : E3 × E3, F q) ≤ κ * ∫ x, g x := by
    have h1 : ENNReal.ofReal (∫ q : E3 × E3, F q)
        = ∫⁻ q : E3 × E3, ENNReal.ofReal (F q) :=
      ofReal_integral_eq_lintegral_ofReal hF_int hFnn
    have h2 : (∫⁻ q : E3 × E3, ENNReal.ofReal (F q)).toReal
        ≤ (ENNReal.ofReal κ * ENNReal.ofReal (∫ x, g x)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hlint
    have h3 : (ENNReal.ofReal κ * ENNReal.ofReal (∫ x, g x)).toReal = κ * ∫ x, g x := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ,
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hg0)]
    have h4 : (ENNReal.ofReal (∫ q : E3 × E3, F q)).toReal = ∫ q : E3 × E3, F q :=
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hFnn)
    calc (∫ q : E3 × E3, F q)
        = (ENNReal.ofReal (∫ q : E3 × E3, F q)).toReal := h4.symm
      _ = (∫⁻ q : E3 × E3, ENNReal.ofReal (F q)).toReal := by rw [h1]
      _ ≤ (ENNReal.ofReal κ * ENNReal.ofReal (∫ x, g x)).toReal := h2
      _ = κ * ∫ x, g x := h3
  -- measurability of the Coulomb integrand of `A`
  have hA_meas : AEMeasurable (Work.BoseBoxFock.coulInt A) (volume.prod volume) := by
    have h1 : AEMeasurable (fun q : E3 × E3 => A q.1) (volume.prod volume) :=
      hA.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun q : E3 × E3 => A q.2) (volume.prod volume) :=
      hA.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h3 : AEMeasurable (fun q : E3 × E3 => (‖q.1 - q.2‖ : ℝ)⁻¹) (volume.prod volume) :=
      (by measurability : Measurable (fun q : E3 × E3 => (‖q.1 - q.2‖ : ℝ)⁻¹)).aemeasurable
    exact (h1.mul h2).mul h3
  -- the pointwise comparison, a.e.
  have hkey : ∀ᵐ q : E3 × E3 ∂(volume.prod volume),
      ‖Work.BoseBoxFock.coulInt A q‖ ≤ c ^ 2 * F q ∧
        Work.BoseBoxFock.coulInt A q ≤ c ^ 2 * F q := by
    filter_upwards [ae_prod_fst hAle, ae_prod_snd hAle, ae_prod_fst hA0, ae_prod_snd hA0,
      ae_prod_fst hg0, ae_prod_snd hg0] with q h1 h2 h3 h4 h5 h6
    have hk : 0 ≤ (‖q.1 - q.2‖ : ℝ)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have hval : Work.BoseBoxFock.coulInt A q = A q.1 * A q.2 * (‖q.1 - q.2‖ : ℝ)⁻¹ := rfl
    have hle : Work.BoseBoxFock.coulInt A q ≤ c ^ 2 * F q := by
      rw [hval]
      have hcg : 0 ≤ c * g q.1 := mul_nonneg hc h5
      have hprod : A q.1 * A q.2 ≤ (c * g q.1) * (c * g q.2) := mul_le_mul h1 h2 h4 hcg
      refine le_trans (mul_le_mul_of_nonneg_right hprod hk) ?_
      simp only [hF]
      nlinarith
    have hnn : 0 ≤ Work.BoseBoxFock.coulInt A q := by
      rw [hval]
      exact mul_nonneg (mul_nonneg h3 h4) hk
    exact ⟨by rw [Real.norm_of_nonneg hnn]; exact hle, hle⟩
  have hA_int : Integrable (Work.BoseBoxFock.coulInt A) (volume.prod volume) :=
    Integrable.mono' (hF_int.const_mul (c ^ 2)) hA_meas.aestronglyMeasurable
      (hkey.mono fun q hq => hq.1)
  refine ⟨hA_int, ?_⟩
  calc (∫ q, Work.BoseBoxFock.coulInt A q)
      ≤ ∫ q, c ^ 2 * F q :=
        integral_mono_ae hA_int (hF_int.const_mul (c ^ 2)) (hkey.mono fun q hq => hq.2)
    _ = c ^ 2 * ∫ q, F q := integral_const_mul (c ^ 2) F
    _ ≤ c ^ 2 * (κ * ∫ x, g x) := mul_le_mul_of_nonneg_left hF_bound (sq_nonneg c)
    _ = c ^ 2 * κ * (∫ x, g x) := by ring

end Work.BoseBoxFock.L1Tails
