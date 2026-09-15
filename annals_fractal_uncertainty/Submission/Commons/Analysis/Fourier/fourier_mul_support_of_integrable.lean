import Mathlib
import Submission.Commons.Analysis.Fourier.integral_mul_conj_eq_zero_of_disjoint_fourier_support

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace Commons.Analysis.Fourier

noncomputable section

/-- **Modulation / shift of the Fourier transform.**
Multiplying `h` by the character `x ↦ 𝐞 ⟪x, a⟫` shifts the Fourier transform by `a`. -/
lemma fourier_mul_fourierChar {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℂ)
    (a t : EuclideanSpace ℝ (Fin d)) :
    𝓕 (fun x => h x * (Real.fourierChar (inner ℝ x a) : ℂ)) t = 𝓕 h (t - a) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def, smul_eq_mul]
  have hinner : -(inner ℝ x (t - a)) = inner ℝ x a + (-(inner ℝ x t)) := by
    rw [inner_sub_right]; ring
  rw [hinner, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- Variant of `fourier_mul_fourierChar` with the sign convention used by the Fourier integral. -/
lemma fourier_mul_fourierChar_neg {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℂ)
    (ξ t : EuclideanSpace ℝ (Fin d)) :
    𝓕 (fun x => h x * (Real.fourierChar (-(inner ℝ x ξ)) : ℂ)) t = 𝓕 h (t + ξ) := by
  have h1 := fourier_mul_fourierChar h (-ξ) t
  simpa only [inner_neg_right, neg_neg, sub_neg_eq_add] using h1

/-- **Convolution formula for the Fourier transform of a product.**
For `g, h : ℝᵈ → ℂ` in `L¹ ∩ L²`,
`𝓕 (g · h) ξ = ∫ η, 𝓕 g η * 𝓕 h (ξ - η)`.
Derived from the integral form of Plancherel's theorem
(`integral_mul_eq_integral_fourier_mul_gen`) together with the modulation identity above. -/
theorem fourier_mul_eq_convolution_aux {d : ℕ} (g h : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg1 : Integrable g (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hh1 : Integrable h (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hh2 : MemLp h 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (fun x => g x * h x) ξ = ∫ η, 𝓕 g η * 𝓕 h (ξ - η) := by
  set c : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun x => (Real.fourierChar (-(inner ℝ x ξ)) : ℂ) with hc
  have harg : Continuous fun x : EuclideanSpace ℝ (Fin d) => -(inner ℝ x ξ) :=
    (Continuous.inner (𝕜 := ℝ) continuous_id continuous_const).neg
  have hc_cont : Continuous c := by
    rw [hc]
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp harg)
  have hc_bound : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖c x‖ ≤ 1 := by
    filter_upwards with x
    rw [hc]
    exact le_of_eq (Circle.norm_coe _)
  have hc_aesm : AEStronglyMeasurable c volume := hc_cont.aestronglyMeasurable
  have hu1 : Integrable (fun x => h x * c x) volume := hh1.mul_bdd hc_aesm hc_bound
  have hctop : MemLp c ⊤ volume := memLp_top_of_bound hc_aesm 1 hc_bound
  have hu2 : MemLp (fun x => h x * c x) 2 volume := hctop.mul hh2
  have hplanch : (∫ x, g x * (h x * c x)) =
      ∫ p, (𝓕 g) p * (𝓕 (fun x => h x * c x)) (-p) :=
    integral_mul_eq_integral_fourier_mul_gen hg1 hu1 hg2 hu2
  have hL : 𝓕 (fun x => g x * h x) ξ = ∫ x, g x * (h x * c x) := by
    rw [Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with x
    rw [hc]
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  have hmod : ∀ p : EuclideanSpace ℝ (Fin d),
      𝓕 (fun x => h x * c x) (-p) = 𝓕 h (ξ - p) := by
    intro p
    rw [hc]
    rw [fourier_mul_fourierChar_neg h ξ (-p), neg_add_eq_sub]
  rw [hL, hplanch]
  apply integral_congr_ae
  filter_upwards with p
  rw [hmod p]

-- Support consequence of `fourier_mul_eq_convolution_of_integrable`: if the Fourier transforms of
-- `g` and `h` (both in L¹ ∩ L²) vanish outside `E` resp. `F`, then the Fourier transform of the
-- pointwise product `g * h` vanishes outside the sumset `E + F`.  The statement writes the sumset
-- out to avoid notation instances.  Pure consequence of the convolution formula: for such `ξ` the
-- integrand vanishes identically (if `𝓕g η ≠ 0` and `𝓕h (ξ-η) ≠ 0` then `ξ = η + (ξ-η) ∈ E + F`).
theorem fourier_mul_support_of_integrable {d : ℕ} (g h : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg1 : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hg2 : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hh1 : MeasureTheory.Integrable h (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hh2 : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (E F : Set (EuclideanSpace ℝ (Fin d)))
    (hE : ∀ ξ : EuclideanSpace ℝ (Fin d), ξ ∉ E → FourierTransform.fourier g ξ = 0)
    (hF : ∀ ξ : EuclideanSpace ℝ (Fin d), ξ ∉ F → FourierTransform.fourier h ξ = 0) :
    ∀ ξ : EuclideanSpace ℝ (Fin d), (∀ a ∈ E, ∀ b ∈ F, ξ ≠ a + b) →
      FourierTransform.fourier (fun x => g x * h x) ξ = 0 := by
  intro ξ hξ
  rw [fourier_mul_eq_convolution_aux g h hg1 hg2 hh1 hh2 ξ]
  have hzero : ∀ η : EuclideanSpace ℝ (Fin d), 𝓕 g η * 𝓕 h (ξ - η) = 0 := by
    intro η
    by_cases hη : η ∈ E
    · have hmem : ξ - η ∉ F := by
        intro hFmem
        exact hξ η hη (ξ - η) hFmem (by abel)
      rw [hF (ξ - η) hmem, mul_zero]
    · rw [hE η hη, zero_mul]
  have hzero_int : (∫ η : EuclideanSpace ℝ (Fin d), 𝓕 g η * 𝓕 h (ξ - η))
      = ∫ η : EuclideanSpace ℝ (Fin d), (0 : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall hzero)
  rw [hzero_int, integral_zero]

end

end Commons.Analysis.Fourier
