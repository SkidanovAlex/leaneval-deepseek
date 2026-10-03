import Mathlib
import Submission.Work.KMTAreas.A7Rep.RephaseDefs
import Submission.Work.KMTAreas.A7Hi.vrsdIntegralLeSamples
import Submission.Work.Analysis.Fourier.bandlimited_weighted_reproduction
import Submission.Work.KMTAreas.A7Hi.VrSamplingShift

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

noncomputable section

/-! ## Scaling of the inverse Fourier transform

If `G : ℝ → ℂ` and `q > 0` then `𝓕⁻ (G (· / q)) u = q · 𝓕⁻ G (q u)`. -/
lemma fourierInv_comp_div (G : ℝ → ℂ) {q : ℝ} (hq : 0 < q) (u : ℝ) :
    FourierTransformInv.fourierInv (fun η : ℝ => G (η / q)) u
      = (q : ℂ) * FourierTransformInv.fourierInv G (q * u) := by
  have hfun : (fun η : ℝ => G (η / q)) = (fun η : ℝ => G (q⁻¹ • η)) := by
    funext η
    rw [smul_eq_mul, div_eq_inv_mul]
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, hfun,
    Commons.Analysis.Fourier.fourier_comp_inv_smul G hq (-u), Module.finrank_self, pow_one]
  show q • 𝓕 G (q • (-u)) = (q : ℂ) * 𝓕 G (-(q * u))
  rw [show q • (-u) = -(q * u) by rw [smul_eq_mul]; ring, Algebra.smul_def,
    Complex.coe_algebraMap]

/-! ## The affine substitution in the Lebesgue integral

`∫⁻ u, A (a + q u) ∂volume = q⁻¹ · ∫⁻ x, A x ∂volume` for `q > 0`. -/
lemma lintegral_comp_add_mul (A : ℝ → ℝ≥0∞) (a : ℝ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ u : ℝ, A (a + q * u) = (ENNReal.ofReal q)⁻¹ * ∫⁻ x : ℝ, A x := by
  have hqne : q ≠ 0 := hq.ne'
  have hmap : Measure.map (fun u : ℝ => a + q * u) volume = (ENNReal.ofReal q)⁻¹ • volume := by
    have hcomp : (fun u : ℝ => a + q * u)
        = (fun x : ℝ => a + x) ∘ (fun u : ℝ => q * u) := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      Real.map_volume_mul_left hqne, Measure.map_smul (hf := (measurable_const_add a).aemeasurable),
      Measure.IsAddLeftInvariant.map_add_left_eq_self, abs_of_pos (inv_pos.mpr hq),
      ENNReal.ofReal_inv_of_pos hq]
  set e : ℝ ≃ᵐ ℝ :=
    ((Homeomorph.mulLeft₀ q hqne).trans (Homeomorph.addLeft a)).toMeasurableEquiv with he
  have heq : ∀ u : ℝ, e u = a + q * u := by
    intro u
    rw [he]
    rfl
  calc ∫⁻ u : ℝ, A (a + q * u)
      = ∫⁻ u : ℝ, A (e u) := by
        apply lintegral_congr; intro u; rw [heq]
    _ = ∫⁻ x : ℝ, A x ∂(Measure.map (⇑e) volume) := (lintegral_map_equiv A e).symm
    _ = ∫⁻ x : ℝ, A x ∂(Measure.map (fun u : ℝ => a + q * u) volume) := by
        rw [show (⇑e) = fun u : ℝ => a + q * u from funext heq]
    _ = (ENNReal.ofReal q)⁻¹ * ∫⁻ x : ℝ, A x := by
        rw [hmap, lintegral_smul_measure]
        rfl

/-! ## Rescaling the amplitude of a band-limited function

For `g` the amplitude of a band-limited function `F = 𝓕⁻ g` and `q > 0`, the rescaled function
`u ↦ F (a + q u)` is again the inverse Fourier transform of an integrable amplitude, namely
`rescAmp q a g`; if `g` is supported in `[-β,β]` with `β q ≤ 1/4`, the rescaled amplitude is
supported in `[-1/4,1/4]`. -/
def rescAmp (q a : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun η => (q : ℂ)⁻¹ * (g (η / q) * Complex.exp (2 * Real.pi * Complex.I * ((η / q) * a)))

lemma integrable_rescAmp {g : ℝ → ℂ} (hg : Integrable g) {q a : ℝ} (hq : 0 < q) :
    Integrable (rescAmp q a g) := by
  have hmeas : AEStronglyMeasurable
      (fun η : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((η / q) * a))) volume := by
    fun_prop
  have hbound : ∀ η : ℝ,
      ‖Complex.exp (2 * Real.pi * Complex.I * ((η / q) * a))‖ ≤ 1 := by
    intro η
    rw [show 2 * Real.pi * Complex.I * ((η / q) * a)
        = ((2 * Real.pi * ((η / q) * a) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I]
  exact ((hg.comp_div hq.ne').mul_bdd hmeas (Filter.Eventually.of_forall hbound)).const_mul _

lemma rescAmp_eq_zero {g : ℝ → ℂ} {β : ℝ} (hsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → g ξ = 0)
    {q a : ℝ} (hq : 0 < q) (hβq : β * q ≤ 1 / 4) {ξ : ℝ}
    (hξ : ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) : rescAmp q a g ξ = 0 := by
  have hξabs : (1 / 4 : ℝ) < |ξ| := by
    by_contra hle
    rw [not_lt] at hle
    exact hξ (abs_le.mp hle)
  have hg0 : g (ξ / q) = 0 := by
    apply hsupp
    intro hmem
    have h2 : |ξ / q| ≤ β := abs_le.mpr hmem
    have h3 : |ξ / q| = |ξ| / q := by rw [abs_div, abs_of_pos hq]
    have hβle : β ≤ 1 / (4 * q) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hβq]
    rw [h3] at h2
    have hlt : (1 / 4 : ℝ) / q < |ξ| / q := div_lt_div_of_pos_right hξabs hq
    have h4 : (1 : ℝ) / (4 * q) = (1 / 4) / q := by field_simp
    linarith
  simp only [rescAmp, hg0, zero_mul, mul_zero]

lemma fourierInv_rescAmp (g : ℝ → ℂ) {q a : ℝ} (hq : 0 < q) (u : ℝ) :
    FourierTransformInv.fourierInv (rescAmp q a g) u
      = FourierTransformInv.fourierInv g (a + q * u) := by
  have hqne : q ≠ 0 := hq.ne'
  set G : ℝ → ℂ := fun ξ => g ξ * Complex.exp (2 * Real.pi * Complex.I * (ξ * a)) with hG
  have hWG : rescAmp q a g = fun η : ℝ => (q : ℂ)⁻¹ * G (η / q) := by
    funext η
    simp only [rescAmp, hG]
    push_cast
    ring
  have hpull : FourierTransformInv.fourierInv (fun η : ℝ => (q : ℂ)⁻¹ * G (η / q)) u
      = (q : ℂ)⁻¹ * FourierTransformInv.fourierInv (fun η : ℝ => G (η / q)) u := by
    rw [Real.fourierInv_eq', Real.fourierInv_eq']
    rw [show (fun η : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ η u) * Complex.I)
            • ((q : ℂ)⁻¹ * G (η / q)))
        = fun η : ℝ => (q : ℂ)⁻¹ * (Complex.exp (↑(2 * Real.pi * inner ℝ η u) * Complex.I)
            • G (η / q)) from by
      funext η
      rw [smul_eq_mul, smul_eq_mul]
      ring]
    rw [integral_const_mul]
  rw [hWG, hpull, fourierInv_comp_div G hq u]
  have hcancel : (q : ℂ)⁻¹ * ((q : ℂ) * FourierTransformInv.fourierInv G (q * u))
      = FourierTransformInv.fourierInv G (q * u) := by
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hqne), one_mul]
  rw [hcancel, Real.fourierInv_eq', Real.fourierInv_eq', hG]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  have hexp : Complex.exp (↑(2 * Real.pi * inner ℝ ξ (q * u)) * Complex.I)
        * Complex.exp (2 * ↑Real.pi * Complex.I * (↑ξ * ↑a))
      = Complex.exp (↑(2 * Real.pi * inner ℝ ξ (a + q * u)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Real.inner_apply, Real.inner_apply]
    push_cast
    ring
  rw [show Complex.exp (↑(2 * Real.pi * inner ℝ ξ (q * u)) * Complex.I)
        * (g ξ * Complex.exp (2 * ↑Real.pi * Complex.I * (↑ξ * ↑a)))
      = (Complex.exp (↑(2 * Real.pi * inner ℝ ξ (q * u)) * Complex.I)
        * Complex.exp (2 * ↑Real.pi * Complex.I * (↑ξ * ↑a))) * g ξ from by ring,
    hexp]

/-! ## The decimated sampling density comparison

The target theorem: the lattice sum over the arithmetic progression `a + q ℤ` and the integral over
`ℝ` of the `p`-th power of the `r`-variational norm are comparable, with densities `q` and `q⁻¹`,
for families whose members are band-limited to `[-β,β]` with `β q ≤ 1/4` (a fixed gap below the
Nyquist rate of the progression).  The proof rescales the family, `G n u := F n (a + q u)`, whose
amplitude is supported in `[-1/4,1/4]`, applies the two sampling comparisons
`vrsdSamplesLeIntegral` and `vrsdIntegralLeSamples`, and converts the ℤ-sum over the progression
into a ℤ-sum by the affine substitution in the Lebesgue integral (`lintegral_comp_add_mul`). -/
end

end Work.KMTAreas.A7Hi
