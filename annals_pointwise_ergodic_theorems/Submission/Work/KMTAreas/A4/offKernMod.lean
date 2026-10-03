/-
# The multiplicative form of the Ionescu--Wainger kernel identity (`offKernMod`)

Krause--Mirek--Tao, Annales de l'Institut Fourier? -- preprint `\cite{krause-mirek-tao}`,
the identity behind Lemma `iw-prop`(i): for a *fixed* frequency `j` the kernel of the summed
Ionescu--Wainger multiplier of `Φ` is `c_j` times the Fourier transform of `Φ` at `j`, with a
*constant* `c_j` that does not depend on `Φ` and is bounded by the cardinality of the set
`(ℚ/ℤ)_{≤l}` of arithmetic frequencies (frequencies of height `≤ l` with denominator
`Q_0 ≤ N_0`).

Indeed, `offKernelId` identifies the kernel with the Fourier transform of the finite sum of
translates `y ↦ ∑_{α ∈ A} Φ (y - a_α)` (`a_α` the representative of `α` in `[0,1)`), and the
Fourier transform of a translate `y ↦ Φ (y - c)` is `e(-c·w) 𝓕 Φ w`.  Hence

`kernel_j = (∑_{α ∈ A} e(-j a_α)) · 𝓕 Φ j`,

and the modulation coefficient `∑_{α ∈ A} e(-j a_α)` is a sum of `#A` unimodular numbers.

## Main result

* `Work.KMTAreas.A4.offKernMod`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offKernNormLe

open MeasureTheory
open scoped FourierTransform BigOperators

namespace Work.KMTAreas.A4

/-- The Fourier transform of a finite sum of translates is the modulation coefficient times the
Fourier transform: `𝓕 (∑ α ∈ A, F (· - c α)) w = (∑ α ∈ A, e(-c α w)) · 𝓕 F w`. -/
lemma fourier_finsetSum_sub_mul {ι : Type*} (A : Finset ι) (c : ι → ℝ) (F : ℝ → ℂ)
    (hint : Integrable F) (w : ℝ) :
    𝓕 (fun y : ℝ => ∑ α ∈ A, F (y - c α)) w
      = (∑ α ∈ A, ((Real.fourierChar (-(c α * w))) : ℂ)) * 𝓕 F w := by
  rw [fourier_finsetSum_sub A c F hint w]
  have h : ∀ α ∈ A, 𝓕 (fun y : ℝ => F (y - c α)) w
      = ((Real.fourierChar (-(c α * w))) : ℂ) * 𝓕 F w := by
    intro α _
    rw [fourier_comp_sub F (c α) w, Circle.smul_def, smul_eq_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_mul]

/-- **Modulation form of the Ionescu--Wainger kernel.**  For a fixed frequency `j`, the kernel of
the summed IW multiplier of `Φ` is the Fourier transform of `Φ` at `j` times a constant `c` which
is independent of `Φ` and whose modulus is at most the number of arithmetic frequencies. -/
theorem offKernMod (ρ : ℝ) (l : ℕ) (j : ℤ) :
    ∃ c : ℂ, ‖c‖ ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ∧
      ∀ Φ : SchwartzMap ℝ ℂ,
        Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))) j
          = c * FourierTransform.fourier (Φ : ℝ → ℂ) (j : ℝ) := by
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set a : Work.Analysis.IonescuWainger.Circle → ℝ :=
    fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val with ha
  refine ⟨∑ α ∈ A, ((Real.fourierChar (-(a α * (j : ℝ)))) : ℂ), ?_, ?_⟩
  · calc ‖∑ α ∈ A, ((Real.fourierChar (-(a α * (j : ℝ)))) : ℂ)‖
        ≤ ∑ α ∈ A, ‖((Real.fourierChar (-(a α * (j : ℝ)))) : ℂ)‖ := norm_sum_le A _
      _ = ∑ _α ∈ A, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact Circle.norm_coe _
      _ = (A.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · intro Φ
    have hint : Integrable (Φ : ℝ → ℂ) := Φ.integrable
    rw [offKernelId ρ l Φ j,
      fourier_finsetSum_sub_mul A a (Φ : ℝ → ℂ) hint (j : ℝ)]

end Work.KMTAreas.A4
