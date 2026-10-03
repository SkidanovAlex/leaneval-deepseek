import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

/-! ## Multiplying a symbol by a character `ee (c ·)`

On the physical side the multiplier with symbol `ξ ↦ ee (c ξ) φ (ξ)` is the translate by `c` of
the multiplier with symbol `φ`: formally, the modulation rule for the inverse Fourier transform
says that multiplying the integrand of `𝓕⁻` by `ee (c ·)` translates the argument of the result by
`c`.  Translation is a measure-preserving bijection of `(ℝ, volume)`, so it preserves every
`L^q` seminorm (`1 ≤ q ≤ ∞`), and the multiplier bound is unchanged.

The two Fourier-analytic inputs are
* `fourierInv_mul_ee'` — the modulation rule `𝓕⁻ (g · ee (c ·)) y = 𝓕⁻ g (y + c)`, proved by the
  integral formula and the character identity `ee (a + b) = ee a * ee b`;
* `eLpNorm_comp_add_right'` — translation invariance of the `eLpNorm` on `ℝ`. -/

/-- `ee x = exp (2 π i x)` is the complex character underlying Mathlib's `Real.fourierChar`. -/
private lemma ee_eq_fourierChar' (z : ℝ) : ee z = (Real.fourierChar z : ℂ) := by
  rw [ee, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- `ee` is an additive character. -/
private lemma ee_add' (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The modulation rule for the inverse Fourier transform.**  Multiplying the transformed
function by the character `ξ ↦ ee (a ξ)` translates the inverse Fourier transform by `a`.
(Both sides are integrals, so no integrability hypothesis is needed.) -/
private lemma fourierInv_mul_ee' (g : ℝ → ℂ) (a y : ℝ) :
    𝓕⁻ (fun ξ : ℝ => g ξ * ee (a * ξ)) y = 𝓕⁻ g (y + a) := by
  rw [fourierInv_eq_real, fourierInv_eq_real]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, Circle.smul_def, ← ee_eq_fourierChar' (v * y),
    ← ee_eq_fourierChar' (v * (y + a))]
  have hcirc : ee (v * y) * ee (a * v) = ee (v * (y + a)) := by
    rw [← ee_add']
    congr 1
    ring
  calc ee (v * y) * (g v * ee (a * v))
      = (ee (v * y) * ee (a * v)) * g v := by ring
    _ = ee (v * (y + a)) * g v := by rw [hcirc]

/-- **Translation invariance of the `eLpNorm` on `ℝ`.**  Lebesgue measure is invariant under
`x ↦ x + c`, hence the `L^q` seminorm is unchanged by precomposing with a translation.  The
statement holds for every exponent `q : ℝ≥0∞`, including `q = 0` and `q = ⊤`. -/
private lemma eLpNorm_comp_add_right' (g : ℝ → ℂ) (p : ℝ≥0∞) (c : ℝ) :
    eLpNorm (fun x : ℝ => g (x + c)) p volume = eLpNorm g p volume := by
  have hme : MeasurableEmbedding (fun x : ℝ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have h := hme.eLpNorm_map_measure (g := g) (μ := volume) (p := p)
  rw [MeasureTheory.Measure.IsAddRightInvariant.map_add_right_eq_self (μ := volume) c] at h
  simpa [Function.comp_def] using h.symm

/-- **Modulating a symbol by `ee (c ·)` does not change its `L^q` multiplier bound.**  If `M`
bounds the operator norm of the Fourier multiplier `T_φ` on `L^q(ℝ)`, then it bounds the operator
norm of `T_{ee (c ·) φ}`: the latter is a translation of the former on the physical side. -/
theorem isLqMultiplierBound_mul_ee {q : ENNReal} {φ : ℝ → ℂ} {M : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M) (c : ℝ) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound q (fun ξ : ℝ => ee (c * ξ) * φ ξ) M := by
  intro f
  have hpoint : ∀ x : ℝ,
      Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => ee (c * ξ) * φ ξ) (f : ℝ → ℂ) x
        = Work.Analysis.IWMultiplier.contMulOp φ (f : ℝ → ℂ) (x + c) := by
    intro x
    simp only [Work.Analysis.IWMultiplier.contMulOp]
    rw [show (fun ξ : ℝ => (ee (c * ξ) * φ ξ) * 𝓕 (f : ℝ → ℂ) ξ)
          = fun ξ : ℝ => (φ ξ * 𝓕 (f : ℝ → ℂ) ξ) * ee (c * ξ) from by
        funext ξ; ring,
      fourierInv_mul_ee' (g := fun ξ : ℝ => φ ξ * 𝓕 (f : ℝ → ℂ) ξ) c x]
  calc eLpNorm (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => ee (c * ξ) * φ ξ)
        (f : ℝ → ℂ)) q volume
      = eLpNorm (fun x : ℝ => Work.Analysis.IWMultiplier.contMulOp φ (f : ℝ → ℂ) (x + c))
          q volume := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        rw [hpoint x]
    _ = eLpNorm (Work.Analysis.IWMultiplier.contMulOp φ (f : ℝ → ℂ)) q volume :=
        eLpNorm_comp_add_right' _ q c
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) q volume := h f

/- The modulated `η`-cutoff is a uniform `L^q` Fourier multiplier: the phases `ee (c·ξ)` are
translations on the physical side, so the bound is the same as for `etaCut kmtEta k` alone
(`Work.KMTAreas.A7.EtaMult`, PROVED: `∃ M > 0, ∀ k q, 1 ≤ q → IsLqMultiplierBound q (etaCut kmtEta k) M`).
The `star` clause follows from the first because `kmtEta` is real-valued. -/
theorem isLqMultiplierBound_modulated_etaCut :
    ∃ M : NNReal, 0 < M ∧ ∀ (k c : ℤ) (q : ENNReal), 1 ≤ q →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound q
        (fun ξ : ℝ => Work.KMTAreas.A7.ee ((c : ℝ) * ξ) *
          Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ) M ∧
      Work.Analysis.IWMultiplier.IsLqMultiplierBound q
        (star (fun ξ : ℝ => Work.KMTAreas.A7.ee ((c : ℝ) * ξ) *
          Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ)) M := by
  obtain ⟨M, hMpos, hM⟩ := EtaMult
  refine ⟨M, hMpos, ?_⟩
  intro k c q hq
  have h1 : Work.Analysis.IWMultiplier.IsLqMultiplierBound q
      (fun ξ : ℝ => Work.KMTAreas.A7.ee ((c : ℝ) * ξ) *
        Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ) M :=
    isLqMultiplierBound_mul_ee (hM k q hq) (c : ℝ)
  exact ⟨h1, IsLqMultiplierBound_star h1⟩

end Work.KMTAreas.A7
