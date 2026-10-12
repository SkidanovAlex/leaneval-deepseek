import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Commons.Analysis.Fourier

/-- Conjugation commutes with the Bochner integral: this is `integral_conj` for `𝕜 = ℂ`
(formulated so that no integrability assumption is needed). -/
lemma star_integral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (h : α → ℂ) :
    star (∫ v, h v ∂μ) = ∫ v, star (h v) ∂μ :=
  (integral_conj (𝕜 := ℂ) (μ := μ) (f := h)).symm

/-- The complex conjugate of the standard character `𝐞 t = exp (2 π i t)`, viewed as an element
of the unit circle, is `𝐞 (-t)`. -/
lemma star_fourierChar_apply (t : ℝ) : star ((𝐞 t : Circle) : ℂ) = ((𝐞 (-t) : Circle) : ℂ) := by
  rw [Complex.star_def, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

/-- The pointwise Fourier transform of the pointwise conjugate of a function is the conjugate
of the Fourier transform at the reflected point: `𝓕 (conj ∘ g) p = conj (𝓕 g (-p))`. -/
lemma fourier_star_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (g : V → ℂ) (p : V) :
    𝓕 (fun x => star (g x)) p = star ((𝓕 g) (-p)) := by
  rw [Real.fourier_eq, Real.fourier_eq,
    star_integral_eq (μ := volume) (fun v => 𝐞 (-⟪v, -p⟫) • g v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, star_mul, star_fourierChar_apply, neg_neg,
    inner_neg_right]
  exact mul_comm _ _

/-- **Plancherel/multiplication formula in integral form, on `L¹ ∩ L²`.**

For `f, g` both integrable AND square-integrable (so that the pointwise Fourier
transform `𝓕 f` is the genuine Fourier integral rather than the junk value `0`,
and so that both displayed integrals converge),

`∫ x, f x * g x = ∫ p, (𝓕 f) p * (𝓕 g) (-p)`   (Mathlib's `e^{−2πi⟪x,ξ⟫}` convention).

Proof route: `⟪f, conj g⟫_{L²} = ∫ f · g`; the `L²` Plancherel inner-product
identity `MeasureTheory.Lp.inner_fourier_eq`; the identification of the pointwise
and `L²` transforms for `L¹ ∩ L²` functions
(`Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral`); and
`𝓕 (conj g) p = conj ((𝓕 g) (-p))`. -/
theorem integral_mul_eq_integral_fourier_mul {f g : ℝ³ → ℂ}
    (hfl1 : Integrable f) (hgl1 : Integrable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, f x * g x) = ∫ p, (𝓕 f) p * (𝓕 g) (-p) := by
  -- `star ∘ g` is again in `L¹ ∩ L²`.
  have hgS : MemLp (fun x => star (g x)) 2 volume := hg.star
  have hgS1 : Integrable (fun x => star (g x)) :=
    (integrable_norm_iff hg.aestronglyMeasurable.star).mp (by
      simpa only [Pi.star_apply, norm_star] using hgl1.norm)
  -- The `L²` inner product `⟪ḡ, f⟫` is the integral of `g * f`.
  have hInner : inner ℂ (hgS.toLp (fun x => star (g x))) (hf.toLp f) = ∫ x, g x * f x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hgS.coeFn_toLp, hf.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply']
    simp
  -- The same inner product, computed on the Fourier side, is the integral of `𝓕g(-·) * 𝓕f`.
  have hRight : inner ℂ (𝓕 (hgS.toLp (fun x => star (g x)))) (𝓕 (hf.toLp f))
      = ∫ p, (𝓕 g) (-p) * (𝓕 f) p := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [fourier_toLp_eq_fourier_integral (d := 3) (memLp_one_iff_integrable.mpr hgS1) hgS,
      fourier_toLp_eq_fourier_integral (d := 3) (memLp_one_iff_integrable.mpr hfl1) hf] with p hp1 hp2
    rw [hp1, hp2, RCLike.inner_apply', fourier_star_apply]
    simp
  -- Plancherel for the sesquilinear inner product, plus `hInner`:
  have hkey : (∫ p, (𝓕 g) (-p) * (𝓕 f) p) = ∫ x, g x * f x :=
    hRight.symm.trans
      ((Lp.inner_fourier_eq (hgS.toLp (fun x => star (g x))) (hf.toLp f)).trans hInner)
  have h1 : (∫ x, f x * g x) = ∫ x, g x * f x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have h2 : (∫ p, (𝓕 g) (-p) * (𝓕 f) p) = ∫ p, (𝓕 f) p * (𝓕 g) (-p) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
  exact h1.trans (hkey.symm.trans h2)

end Commons.Analysis.Fourier
