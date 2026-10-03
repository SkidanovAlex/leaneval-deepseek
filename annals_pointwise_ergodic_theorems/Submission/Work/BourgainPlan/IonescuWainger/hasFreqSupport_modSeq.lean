import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas for `hasFreqSupport_modSeq`

Everything below is an internal helper; the helpers are `private` because the circle carries a
sibling development (`discFourier_mul_eq_circConv.lean`) which already names some of these
identities, and we do not want to shadow it. -/

/-- The characters are multiplicative in their argument:
`e^{2πi n (x + y)} = e^{2πi n x} · e^{2πi n y}` on `𝕋 = ℝ/ℤ`. -/
private theorem fourier_add_arg (n : ℤ) (x y : Circle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]

/-- `e^{2πi (-n) (-x)} = e^{2πi n x}` on `𝕋 = ℝ/ℤ`. -/
private theorem fourier_neg_neg (n : ℤ) (x : Circle) :
    fourier (-n) (-x) = fourier n x := by
  rw [fourier_apply, neg_zsmul, zsmul_neg, neg_neg, ← fourier_apply]

/-- The `i`-th coefficient of `ftLp h hh` along the Hilbert basis `fourierBasis` is `h i`. -/
private theorem repr_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) (i : ℤ) :
    fourierBasis.repr (ftLp h hh) i = h i := by
  rw [HilbertBasis.repr_apply_apply, ftLp_coeff]

/-- **The `i`-th Fourier coefficient of the translate `η ↦ 𝓕ρ (η + θ)` is `e^{2πi i θ} · ρ i`.**
This is the translation-invariance of the Haar measure (`integral_add_right_eq_self`) read through
the coefficient integral `fourierCoeff`. -/
private theorem repr_shift (ρ : ℤ → ℂ) (hρ : Memℓp ρ 2) (θ : Circle) (i : ℤ) :
    fourierBasis.repr (Lp.compMeasurePreserving (fun x : Circle => x + θ)
      (measurePreserving_add_right (AddCircle.haarAddCircle (T := 1)) θ) (ftLp ρ hρ)) i
      = fourier i θ * ρ i := by
  set F := ftLp ρ hρ with hF
  set U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    Lp.compMeasurePreserving (fun x : Circle => x + θ)
      (measurePreserving_add_right (AddCircle.haarAddCircle (T := 1)) θ) F with hU
  have hcoe : (U : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun t => (F : Circle → ℂ) (t + θ) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving F
      (measurePreserving_add_right (AddCircle.haarAddCircle (T := 1)) θ)] with t ht
    exact ht
  rw [fourierBasis_repr, fourierCoeff]
  have h1 : ∫ t, fourier (-i) t • (U : Circle → ℂ) t ∂AddCircle.haarAddCircle (T := 1)
      = ∫ t, fourier (-i) t • (F : Circle → ℂ) (t + θ) ∂AddCircle.haarAddCircle (T := 1) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with t ht
    rw [ht]
  have h2 : ∫ t, fourier (-i) t • (F : Circle → ℂ) (t + θ) ∂AddCircle.haarAddCircle (T := 1)
      = ∫ s, fourier (-i) (s - θ) • (F : Circle → ℂ) s ∂AddCircle.haarAddCircle (T := 1) := by
    have h := integral_add_right_eq_self (μ := AddCircle.haarAddCircle (T := 1))
      (fun s : Circle => fourier (-i) (s - θ) • (F : Circle → ℂ) s) θ
    simpa using h
  have h3 : ∫ s, fourier (-i) (s - θ) • (F : Circle → ℂ) s ∂AddCircle.haarAddCircle (T := 1)
      = fourier (-i) (-θ) * ∫ s, fourier (-i) s • (F : Circle → ℂ) s
          ∂AddCircle.haarAddCircle (T := 1) := by
    have hpt : (fun s : Circle => fourier (-i) (s - θ) • (F : Circle → ℂ) s)
        = fun s : Circle => fourier (-i) (-θ) * (fourier (-i) s • (F : Circle → ℂ) s) := by
      funext s
      simp only [sub_eq_add_neg, fourier_add_arg, smul_eq_mul]
      ring
    rw [hpt, integral_const_mul]
  have h4 : ∫ s, fourier (-i) s • (F : Circle → ℂ) s ∂AddCircle.haarAddCircle (T := 1) = ρ i := by
    have h := repr_ftLp (h := ρ) hρ i
    rw [fourierBasis_repr] at h
    simpa only [fourierCoeff] using h
  rw [h1, h2, h3, h4, fourier_neg_neg i θ]

/-- **Modulation shifts the frequency support.**  The Fourier transform of the modulated sequence
`modSeq ρ θ = (m ↦ ρ m · e^{2πi m θ})` is the translate `η ↦ 𝓕ρ (η + θ)` of that of `ρ`; hence if
`ρ` is band-limited with frequency support in `D`, the modulated sequence is band-limited with
frequency support in `{x | x + θ ∈ D}`.

Proof route: compute both sides against the Hilbert basis `fourierBasis`: the `n`-th coefficient of
`ftLp (modSeq ρ θ)` is `ρ n · e^{2πi n θ}` (`ftLp_coeff`), and that of `η ↦ 𝓕ρ (η + θ)` is
`∫ η, 𝓕ρ (η + θ) · conj (e_n η) dη = e^{2πi n θ} · ∫ η', 𝓕ρ η' · conj (e_n (η' - θ)) dη'`
(`integral_add_right_eq_self` for the translation invariance of the Haar measure, together with
`fourier_add_arg`); the two agree, so the two `L²` functions are equal, and the a.e. vanishing
transfers. -/
theorem hasFreqSupport_modSeq {ρ : ℤ → ℂ} (hρ : Memℓp ρ 2) {D : Set Circle}
    (hD : HasFreqSupport ρ hρ D) (θ : Circle) :
    HasFreqSupport (modSeq ρ θ) (memℓp_modSeq hρ θ) (fun x => x + θ ∈ D) := by
  have hμ : MeasurePreserving (fun x : Circle => x + θ)
      (AddCircle.haarAddCircle (T := 1)) (AddCircle.haarAddCircle (T := 1)) :=
    measurePreserving_add_right _ θ
  have hkey : ftLp (modSeq ρ θ) (memℓp_modSeq hρ θ)
      = Lp.compMeasurePreserving (fun x : Circle => x + θ) hμ (ftLp ρ hρ) := by
    refine fourierBasis.repr.injective ?_
    ext i
    rw [repr_ftLp (memℓp_modSeq hρ θ) i, repr_shift ρ hρ θ i]
    rw [modSeq, mul_comm]
  have hae : (ftLp (modSeq ρ θ) (memℓp_modSeq hρ θ) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun x => (ftLp ρ hρ : Circle → ℂ) (x + θ) := by
    rw [hkey]
    filter_upwards [Lp.coeFn_compMeasurePreserving (ftLp ρ hρ) hμ] with x hx
    exact hx
  have htr : ∀ᵐ x ∂AddCircle.haarAddCircle (T := 1),
      x + θ ∉ D → (ftLp ρ hρ : Circle → ℂ) (x + θ) = 0 :=
    hμ.quasiMeasurePreserving.ae hD
  filter_upwards [hae, htr] with x hx htx hmem
  rw [hx]
  exact htx hmem

end Work.BourgainPlan.IonescuWainger
