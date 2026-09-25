import Mathlib
import Submission.Work.BourgainPlan.Maximal.plancherel_fourier_inner

namespace Work.BourgainPlan.Maximal

open MeasureTheory FourierTransform
open scoped FourierTransform ComplexInnerProductSpace

/-- Pointwise complex identity linking the (conjugate-linear in the first variable) inner
product `inner ℂ a b = b * star a` with the conjugate of a product: `inner ℂ a b = star (a * star b)`. -/
private lemma inner_apply_eq_star_mul_star (a b : ℂ) : inner ℂ a b = star (a * star b) := by
  rw [RCLike.inner_apply, star_mul, star_star]
  rfl

/-- Plancherel/Parselval in the form of an isometry of the inverse Fourier transform: the
`L²` pairing `∫ inner (fourierInv H) (fourierInv K)` equals the `L²` pairing `∫ inner H K`.
Obtained from the bilinear Plancherel identity `plancherel_fourier_inner`
(`∫ 𝓕⁻H · star (𝓕⁻K) = ∫ H · star K`) by conjugating both sides. -/
theorem integral_inner_fourierInv_fourierInv_eq (H K : ℝ → ℂ)
    (hH1 : MeasureTheory.Integrable H) (hH2 : MeasureTheory.MemLp H 2 MeasureTheory.volume)
    (hK1 : MeasureTheory.Integrable K) (hK2 : MeasureTheory.MemLp K 2 MeasureTheory.volume) :
    (∫ x : ℝ, inner ℂ (FourierTransform.fourierInv H x) (FourierTransform.fourierInv K x))
      = ∫ x : ℝ, inner ℂ (H x) (K x) := by
  have key := plancherel_fourier_inner H K hH1 hH2 hK1 hK2
  calc (∫ x : ℝ, inner ℂ (FourierTransform.fourierInv H x) (FourierTransform.fourierInv K x))
      = ∫ x : ℝ,
          star (FourierTransform.fourierInv H x * star (FourierTransform.fourierInv K x)) := by
        apply integral_congr_ae
        filter_upwards with x
        exact inner_apply_eq_star_mul_star _ _
    _ = star (∫ x : ℝ,
          FourierTransform.fourierInv H x * star (FourierTransform.fourierInv K x)) :=
        integral_conj
    _ = star (∫ x : ℝ, H x * star (K x)) := by rw [key]
    _ = ∫ x : ℝ, star (H x * star (K x)) := integral_conj.symm
    _ = ∫ x : ℝ, inner ℂ (H x) (K x) := by
        apply integral_congr_ae
        filter_upwards with x
        exact (inner_apply_eq_star_mul_star _ _).symm

end Work.BourgainPlan.Maximal
