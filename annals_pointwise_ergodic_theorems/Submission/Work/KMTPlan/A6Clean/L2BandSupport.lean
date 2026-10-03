/-
# `L²`-amplitude band support, and its conversion to `L¹`-amplitude band support

The §8 adelic form of the A6 model estimate (`Work.KMTPlan.A6.AdelicFormPropRange`) requires the
adelic lift `F` of the frozen slice to be **band limited in the real variable**: for every residue
`ρ'` the slice `X ↦ F n X ρ'` has as inverse Fourier transform an *integrable* amplitude supported
in `Icc (-1/(8Q)) (1/(8Q))` (`Work.KMTAreas.A7Rep.HasRealFreqSupport`).

The natural construction of the *packets* whose `zmodAvg` gives `F` produces, for each arithmetic
frequency `α`, a function whose amplitude is only **`L²`**: the model packets are only `ℓ²`, so the
restriction of their discrete Fourier transform (`Work.BourgainPlan.IonescuWainger.ftLp`) to the arc
around `α` is an `L²` function.  The amplitudes nevertheless have **compact support**, which is all
that is needed:

* `L²` on a bounded set is `L¹` (`integrable_of_memLp_two_of_support`) — so every `L²` amplitude
  with bounded measurable support *is* an `L¹` amplitude, and the whole `L¹`-amplitude toolbox
  already in the tree (`Work.KMTPlan.A6.hasRealFreqSupport_mul`,
  `hasRealFreqSupport_finset_sum`, `hasRealFreqSupport_const_mul`, and
  `Work.KMTPlan.A6.continuous_of_hasRealFreqSupport`) applies verbatim;
* consequently an `L²`-band-limited function is continuous, hence measurable.

This module is the bridge that lets the packet construction (whose amplitudes come from `ftLp`)
feed the *proved* `L¹`-amplitude lemmas used by the assembly of the adelic form.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicLiftPackets
import Submission.Work.KMTPlan.A6.MdlSliceDiagonalSampling

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6Clean

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- **`L²`-amplitude real-frequency support.**  The function `ψ : ℝ → ℂ` is the inverse Fourier
transform of an `L²` function `A` vanishing off `S`.

This is the `L²` analogue of `Work.KMTAreas.A7Rep.HasRealFreqSupport` (which asks for an integrable
amplitude): the packet amplitudes of the adelic form are restrictions of discrete Fourier transforms
of `ℓ²` packets to bounded arcs, hence `L²` but generally not `L¹` *a priori*. -/
def HasL2FreqSupport (ψ : ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∃ A : ℝ → ℂ, MemLp A 2 volume ∧
    (∀ ξ : ℝ, ξ ∉ S → A ξ = 0) ∧ ∀ t : ℝ, ψ t = FourierTransformInv.fourierInv A t

/-- **The key conversion: an `L²` function supported in a set of finite measure is integrable.** -/
theorem integrable_of_memLp_two_of_support {A : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hvol : volume S < ⊤) (hA : MemLp A 2 volume) (hsupp : ∀ ξ : ℝ, ξ ∉ S → A ξ = 0) :
    Integrable A := by
  haveI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
  have hA' : MemLp A 2 (volume.restrict S) := hA.mono_measure Measure.restrict_le_self
  have hint : Integrable A (volume.restrict S) := MemLp.integrable (by norm_num) hA'
  have hind : Integrable (S.indicator A) volume :=
    IntegrableOn.integrable_indicator hint hS
  rwa [show S.indicator A = A from funext fun x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]] at hind

/-- An `L²` amplitude with bounded measurable support is an `L¹` amplitude:
`HasL2FreqSupport ψ S` upgrades to `Work.KMTAreas.A7Rep.HasRealFreqSupport ψ S`. -/
theorem hasRealFreqSupport_of_hasL2FreqSupport {ψ : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hvol : volume S < ⊤) (h : HasL2FreqSupport ψ S) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport ψ S := by
  obtain ⟨A, hA, hsupp, heq⟩ := h
  exact ⟨A, integrable_of_memLp_two_of_support hS hvol hA hsupp, hsupp, heq⟩

/-- **An `L²`-band-limited function with bounded band is continuous.** -/
theorem continuous_of_hasL2FreqSupport {ψ : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hvol : volume S < ⊤) (h : HasL2FreqSupport ψ S) : Continuous ψ :=
  Work.KMTPlan.A6.continuous_of_hasRealFreqSupport
    (hasRealFreqSupport_of_hasL2FreqSupport hS hvol h)

/-- **An `L²`-band-limited function with bounded band is measurable.** -/
theorem measurable_of_hasL2FreqSupport {ψ : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hvol : volume S < ⊤) (h : HasL2FreqSupport ψ S) : Measurable ψ :=
  (continuous_of_hasL2FreqSupport hS hvol h).measurable

/-- Multiplication by a scalar preserves `L²`-amplitude band support. -/
theorem hasL2FreqSupport_const_mul (c : ℂ) {S : Set ℝ} {ψ : ℝ → ℂ}
    (h : HasL2FreqSupport ψ S) : HasL2FreqSupport (fun t : ℝ => c * ψ t) S := by
  obtain ⟨A, hA, hAsupp, hAeq⟩ := h
  refine ⟨fun ξ : ℝ => c * A ξ, hA.const_mul c, ?_, ?_⟩
  · intro ξ hξ
    dsimp only
    rw [hAsupp ξ hξ, mul_zero]
  · intro t
    dsimp only
    rw [hAeq t, Work.KMTPlan.A6.fourierInv_const_mul c A t]

/-- The interval `Icc a b` has finite measure, so the conversion applies to it. -/
theorem volume_Icc_lt_top (a b : ℝ) : volume (Set.Icc a b) < ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

end

end Work.KMTPlan.A6Clean
