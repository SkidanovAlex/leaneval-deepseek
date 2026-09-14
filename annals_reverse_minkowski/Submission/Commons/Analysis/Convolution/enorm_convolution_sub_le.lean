import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Measure.Integral.integral_smoothing_rpow_le_of_integrable

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped ENNReal

/-- The `L²`-mass of `u` is finite when `u ∈ L²`, phrased as a `lintegral` of the squared
`enorm`. -/
private theorem lintegral_enorm_rpow_two_lt_top {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℂ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∫⁻ z, ‖u z‖ₑ ^ (2:ℝ) < ⊤ := by
  have hInt : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖u z‖ ^ (2:ℝ))
      MeasureTheory.volume := by
    simpa using hu.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
  have hfin : ∫⁻ z, ‖(‖u z‖ ^ (2:ℝ))‖ₑ < ⊤ :=
    MeasureTheory.hasFiniteIntegral_iff_enorm.mp hInt.2
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  apply lintegral_congr
  intro z
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) 2),
    show ‖u z‖ₑ = ENNReal.ofReal ‖u z‖ by simp [enorm],
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]

/-- For `ρ ∈ L¹` and `u ∈ L²`, the weighted `L²`-mass `∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ 2`
is finite for almost every `x`. -/
private theorem ae_lintegral_enorm_mul_enorm_rpow_two_lt_top {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℂ}
    (hρi : MeasureTheory.Integrable ρ (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ)) < ⊤ := by
  set F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) with hFdef
  have hΦ : AEMeasurable (Function.uncurry fun (x y : EuclideanSpace ℝ (Fin n)) =>
      ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ)) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖ρ p.2‖ₑ) (volume.prod volume) :=
      hρi.aestronglyMeasurable.enorm.comp_snd
    have h2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖u (p.1 - p.2)‖ₑ) (volume.prod volume) :=
      (hu.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact h1.mul (h2.pow_const (2:ℝ))
  have hFae : AEMeasurable F volume := by
    rw [hFdef]; exact hΦ.lintegral_prod_right'
  have hInt : ∫⁻ x, F x ∂volume < ⊤ := by
    rw [hFdef]
    rw [lintegral_lintegral_swap hΦ]
    have hinner : ∀ y : EuclideanSpace ℝ (Fin n),
        (∫⁻ x, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ))
          = ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) := by
      intro y
      rw [lintegral_const_mul'']
      · congr 1
        exact lintegral_sub_right_eq_self (fun z => ‖u z‖ₑ ^ (2:ℝ)) y
      · exact (hu.aestronglyMeasurable.enorm.pow_const (2:ℝ)).comp_quasiMeasurePreserving
          (by simpa [sub_eq_add_neg] using
            (measurePreserving_add_right volume (-y)).quasiMeasurePreserving)
    simp_rw [hinner]
    calc ∫⁻ y, ‖ρ y‖ₑ * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ))
        = (∫⁻ y, ‖ρ y‖ₑ) * (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) :=
          lintegral_mul_const'' _ hρi.aestronglyMeasurable.enorm
      _ < ⊤ := ENNReal.mul_lt_top hρi.2 (lintegral_enorm_rpow_two_lt_top hu)
  exact ae_lt_top' hFae (ne_of_lt hInt)

/-- If `ρ ∈ L¹` and `u ∈ L²`, then `y ↦ ρ y • u (x - y)` is Bochner integrable for almost
every `x`. -/
private theorem ae_integrable_smul_convolution {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {u : EuclideanSpace ℝ (Fin n) → ℂ}
    (hρi : MeasureTheory.Integrable ρ (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      MeasureTheory.Integrable (fun y => ρ y • u (x - y)) MeasureTheory.volume := by
  filter_upwards [ae_lintegral_enorm_mul_enorm_rpow_two_lt_top hρi hu] with x hx
  have hsub : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => u (x - y)) volume :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  refine ⟨hρi.aestronglyMeasurable.smul hsub, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hfa : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ‖u (x - y)‖ₑ) volume := hsub.enorm
  have hga : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ‖ρ y‖ₑ) volume :=
    hρi.aestronglyMeasurable.enorm
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le (ν := volume) (q := 2) (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y)‖ₑ * ‖ρ y‖ₑ) = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y)‖ₑ ^ (2:ℝ) * ‖ρ y‖ₑ)
        = ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hCS
  have hbound : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) ^ (2:ℝ) < ⊤ :=
    lt_of_le_of_lt hCS (ENNReal.mul_lt_top hx hρi.2)
  have hfin' : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) < ⊤ := by
    by_contra hc
    rw [not_lt] at hc
    have htop : (∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ) = ⊤ := top_le_iff.mp hc
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hbound
    exact lt_irrefl _ hbound
  exact lt_of_eq_of_lt (lintegral_congr fun y => by rw [enorm_smul]) hfin'

/-- **Convolution is close to the identity in a weighted `L²` sense.**

For a nonnegative integrable `ρ` with `∫ ρ = 1` and any `u ∈ L²`, almost every `x` satisfies
`‖(ρ ⋆ u)(x) - u x‖ₑ ^ 2 ≤ ∫⁻ y, ρ y ‖u (x - y) - u x‖ₑ ^ 2`. -/
theorem enorm_convolution_sub_le {n : ℕ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρnn : ∀ x, 0 ≤ ρ x) (hρi : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hρ1 : MeasureTheory.integral MeasureTheory.volume ρ = 1)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    Filter.Eventually (fun x => ‖(MeasureTheory.integral MeasureTheory.volume
        (fun y => ρ y • u (x - y))) - u x‖ₑ ^ 2 ≤ MeasureTheory.lintegral MeasureTheory.volume
          (fun y => ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  filter_upwards [ae_integrable_smul_convolution hρi hu] with x hx
  have hconst : ∫ y, ρ y • u x ∂volume = u x := by
    rw [integral_smul_const, hρ1, one_smul]
  have hsplit : (∫ y, ρ y • u (x - y) ∂volume) - u x
      = ∫ y, ρ y • (u (x - y) - u x) ∂volume := by
    conv_lhs => rw [← hconst]
    rw [← integral_sub hx (hρi.smul_const (u x))]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_sub]
  rw [hsplit]
  have hD : ‖∫ y, ρ y • (u (x - y) - u x) ∂volume‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂volume := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    rw [enorm_smul, Real.enorm_eq_ofReal (hρnn y)]
  have hD2 : ‖∫ y, ρ y • (u (x - y) - u x) ∂volume‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ∂volume) ^ (2:ℝ) :=
    ENNReal.rpow_le_rpow hD (by norm_num)
  have hfa : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ‖u (x - y) - u x‖ₑ) volume := by
    have hsub : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => u (x - y)) volume :=
      hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    exact (hsub.sub aestronglyMeasurable_const).enorm
  have hga : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (ρ y)) volume :=
    hρi.aemeasurable.ennreal_ofReal
  have ha1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρnn), hρ1,
      ENNReal.ofReal_one]
  have hCS := Commons.Measure.Integral.lintegral_mul_pow_le (ν := volume) (q := 2) (by norm_num) hfa hga
  rw [show (∫⁻ y, ‖u (x - y) - u x‖ₑ * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ from
        lintegral_congr fun y => mul_comm _ _,
      show (∫⁻ y, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (ρ y))
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) from
        lintegral_congr fun y => mul_comm _ _,
      ha1, show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, mul_one] at hCS
  simpa [ENNReal.rpow_two] using hD2.trans hCS

end Commons.Analysis.Convolution