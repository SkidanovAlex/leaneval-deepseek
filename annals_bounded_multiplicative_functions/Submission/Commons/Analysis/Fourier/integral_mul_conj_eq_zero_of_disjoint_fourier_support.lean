import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul
import Submission.Commons.Analysis.Fourier.fourierIntegral_mul_measure_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vanishing of `∫ f · conj g` for functions with disjoint Fourier support

If `f` and `g` are integrable and square-integrable on `ℝⁿ` and their (pointwise) Fourier
integrals vanish off sets `S`, `T` respectively, with `S` and `T` disjoint, then
`∫ x, f x * conj (g x) = 0`.

The proof is Plancherel's theorem in integral form (`∫ f g = ∫ 𝓕f · 𝓕g(-·)`), the identity
`𝓕(conj g)(p) = conj (𝓕 g p)`, and the observation that the resulting integrand
`𝓕f p · conj (𝓕g p)` vanishes everywhere.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace Commons.Analysis.Fourier

noncomputable section

/-- The pointwise Fourier integral is Mathlib's Fourier transform: this rewrites `𝓕 h ξ` into
the explicit Lebesgue integral `∫ x, h x * exp (2πi(-⟪x,ξ⟫))`. -/
theorem fourier_eq_integral_exp {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 h ξ = ∫ x, h x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  show (𝐞 (-⟪x, ξ⟫) : Circle) • h x
      = h x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ))
  rw [Circle.smul_def, smul_eq_mul, mul_comm]
  congr 1
  rw [exp_two_pi_I_eq_fourierChar]

/-- **Plancherel/multiplication formula in integral form, on `L¹ ∩ L²`, in every dimension.**

For `f, g` both integrable and square-integrable,
`∫ x, f x * g x = ∫ p, (𝓕 f) p * (𝓕 g) (-p)`
(Mathlib's `e^{−2πi⟪x,ξ⟫}` convention). -/
theorem integral_mul_eq_integral_fourier_mul_gen {d : ℕ}
    {f g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hfl1 : Integrable f) (hgl1 : Integrable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, f x * g x) = ∫ p, (𝓕 f) p * (𝓕 g) (-p) := by
  have hgS : MemLp (fun x => star (g x)) 2 volume := hg.star
  have hgS1 : Integrable (fun x => star (g x)) :=
    (integrable_norm_iff hg.aestronglyMeasurable.star).mp (by
      simpa only [Pi.star_apply, norm_star] using hgl1.norm)
  have hInner : inner ℂ (hgS.toLp (fun x => star (g x))) (hf.toLp f) = ∫ x, g x * f x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hgS.coeFn_toLp, hf.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply']
    simp
  have hRight : inner ℂ (𝓕 (hgS.toLp (fun x => star (g x)))) (𝓕 (hf.toLp f))
      = ∫ p, (𝓕 g) (-p) * (𝓕 f) p := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [fourier_toLp_eq_fourier_integral (d := d)
        (memLp_one_iff_integrable.mpr hgS1) hgS,
      fourier_toLp_eq_fourier_integral (d := d)
        (memLp_one_iff_integrable.mpr hfl1) hf] with p hp1 hp2
    rw [hp1, hp2, RCLike.inner_apply', fourier_star_apply]
    simp
  have hkey : (∫ p, (𝓕 g) (-p) * (𝓕 f) p) = ∫ x, g x * f x :=
    hRight.symm.trans
      ((Lp.inner_fourier_eq (hgS.toLp (fun x => star (g x))) (hf.toLp f)).trans hInner)
  have h1 : (∫ x, f x * g x) = ∫ x, g x * f x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have h2 : (∫ p, (𝓕 g) (-p) * (𝓕 f) p) = ∫ p, (𝓕 f) p * (𝓕 g) (-p) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
  exact h1.trans (hkey.symm.trans h2)

/-- The Fourier transform of `conj ∘ g` at `-p` is the conjugate of `𝓕 g` at `p`. -/
theorem fourier_star_neg {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (p : EuclideanSpace ℝ (Fin d)) :
    𝓕 (fun x => star (g x)) (-p) = star ((𝓕 g) p) := by
  rw [fourier_star_apply, neg_neg]

theorem integral_mul_conj_eq_zero_of_disjoint_fourier_support (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (S T : Set (EuclideanSpace ℝ (Fin n)))
    (hf1 : MeasureTheory.Integrable f) (hg1 : MeasureTheory.Integrable g)
    (hf2 : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2))
    (hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2))
    (hS : ∀ ξ, ξ ∉ S →
      ∫ x, f x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) = 0)
    (hT : ∀ ξ, ξ ∉ T →
      ∫ x, g x * Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((-(inner ℝ x ξ)) : ℝ)) = 0)
    (hdisj : Disjoint S T) :
    ∫ x, f x * starRingEnd ℂ (g x) = 0 := by
  have hfm : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm hf1.aestronglyMeasurable).mpr hf2
  have hgm : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr hg2
  have hgcm : MemLp (fun x => star (g x)) 2 volume := hgm.star
  have hgc1 : Integrable (fun x => star (g x)) :=
    (integrable_norm_iff hgm.aestronglyMeasurable.star).mp (by
      simpa only [Pi.star_apply, norm_star] using hg1.norm)
  have hplanch := integral_mul_eq_integral_fourier_mul_gen hf1 hgc1 hfm hgcm
  have hright : (∫ p, (𝓕 f) p * (𝓕 (fun x => star (g x))) (-p))
      = ∫ p, (𝓕 f) p * star ((𝓕 g) p) := by
    apply integral_congr_ae
    filter_upwards with p
    show (𝓕 f) p * (𝓕 (fun x => star (g x))) (-p) = (𝓕 f) p * star ((𝓕 g) p)
    rw [fourier_star_neg]
  have hzero : ∀ p, (𝓕 f) p * star ((𝓕 g) p) = 0 := by
    intro p
    by_cases hp : p ∈ S
    · have hpT : p ∉ T := (Set.disjoint_left.mp hdisj) hp
      rw [fourier_eq_integral_exp g p, hT p hpT, star_zero, mul_zero]
    · rw [fourier_eq_integral_exp f p, hS p hp, zero_mul]
  have hzero_int : (∫ p, (𝓕 f) p * star ((𝓕 g) p)) = 0 := by
    have h : (∫ p, (𝓕 f) p * star ((𝓕 g) p)) = ∫ p, (0 : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall hzero)
    simpa using h
  calc ∫ x, f x * starRingEnd ℂ (g x)
      = ∫ x, f x * star (g x) := by
        apply integral_congr_ae
        filter_upwards with x
        show f x * starRingEnd ℂ (g x) = f x * star (g x)
        rw [starRingEnd_apply]
    _ = ∫ p, (𝓕 f) p * (𝓕 (fun x => star (g x))) (-p) := hplanch
    _ = ∫ p, (𝓕 f) p * star ((𝓕 g) p) := hright
    _ = 0 := hzero_int

end

end Commons.Analysis.Fourier
