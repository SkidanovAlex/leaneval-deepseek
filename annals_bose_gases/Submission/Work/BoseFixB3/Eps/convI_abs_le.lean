import ChallengeDeps
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Eps.convI_abs_le`

FS's constant `I := ∫ W₁(y)ω(y) dy` of `lem:Convolution` (the convolution
constant `Work.BoseFixB3.convI`) is bounded by `16π·(a v)` in the dilute
regime `R ≤ ℓ·chiR0`.

The proof is the two-step sandwich that the corpus already provides for the
Fourier side (`Submission.Work.SmallBoxD1Assembly.abs_pairW_wScaled_g0_le`):

* `|ω| ≤ 1` a.e. (`Submission.Work.QMassUpper.chosen_w0_bounds_ae`, i.e. the
  Layer-3 `0 ≤ ω ≤ 1` bounds for the chosen scattering solution), hence
  `|W₁·ω| ≤ |W₁|` a.e.;
* `∫|W₁| ≤ 16π·(a v)` (`Submission.Work.SmallBoxBogWS1Bound.
  wScaled_g0_abs_integral_le`, which is `|wScaled| ≤ 2|g₀|` on the support
  of `g₀` plus `∫|g₀| = 8π·(a v)`).
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixB3.Eps

set_option autoImplicit false

/-- The chosen scattering solution is bounded by `1` in absolute value a.e. -/
lemma abs_choose_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), |Classical.choose h z| ≤ 1 := by
  have hb := Submission.BoseGases.chosen_w0_bounds_ae (R := R) hR hv hvrad hv_supp h
  filter_upwards [hb.1, hb.2] with z hz0 hz1
  exact abs_le.mpr ⟨by linarith, hz1⟩

theorem convI_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hℓ : 0 < ℓ)
    (hdil : R ≤ ℓ * Submission.BoseGases.chiR0) :
    |Work.BoseFixB3.convI ℓ v h| ≤ 16 * π * BoseGases.a v := by
  have hWint : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hdil
  have hω : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      |Classical.choose h z| ≤ 1 :=
    abs_choose_le_one hR hv hvrad hv_supp h
  have hbound : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      ‖Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z * Classical.choose h z‖
        ≤ |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z| := by
    filter_upwards [hω] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    calc |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z|
            * |Classical.choose h z|
          ≤ |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z| * 1 :=
        mul_le_mul_of_nonneg_left hz
          (abs_nonneg (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z))
      _ = |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z| := mul_one _
  have h1 : ‖∫ z : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z
        * Classical.choose h z‖
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z| :=
    MeasureTheory.norm_integral_le_of_norm_le hWint.abs hbound
  have h2 := Submission.BoseGases.wScaled_g0_abs_integral_le hR hv hvrad hv_supp h hℓ hdil
  rw [← Real.norm_eq_abs]
  unfold Work.BoseFixB3.convI
  exact h1.trans h2

end Work.BoseFixB3.Eps
