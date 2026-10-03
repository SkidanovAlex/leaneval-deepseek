import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs

/-!
# The Ionescu–Wainger multiplier for a non-integrable symbol is zero

The Ionescu–Wainger multiplier with symbol `m = iwSymbolSet A Φ` acts on sequences by convolution
with the kernel `iwKernel m j = ∫ m(ξ) e(-jξ) dξ`, the `j`-th Fourier coefficient of `m`.  When `m`
is **not** integrable on the circle, the Bochner integral defining this Fourier coefficient is a
junk value: by Mathlib's convention `MeasureTheory.integral_undef`, the integral of a
non-integrable function is `0`.  Hence every Fourier coefficient vanishes and the multiplier is
the zero operator.

For a *singleton* frequency set `A = {α}` we have `iwSymbolSet {α} Φ = fun ξ => Φ (ξ - α)`, a
translate of `Φ`; since the Haar measure of the circle is translation invariant, this symbol is
integrable exactly when `Φ` is.  So the degenerate case of the singleton symbol is detected by the
non-integrability of the symbol `σ` itself:

`Work.Analysis.IWMultiplier.iwConv_singleton_eq_zero_of_not_integrable` —
`iwConv {α} σ f = 0` whenever `¬ Integrable σ circleMeasure` (and `f` is finitely supported).

No measurability hypothesis on `σ` is needed: non-integrability is enough, because the Fourier
coefficients are junk-zero rather than being estimated.  This is the degenerate branch of the
Rubio de Francia square-function reduction for the Ionescu–Wainger multiplier.

## Main results

* `Work.Analysis.IWMultiplier.iwSymbolSet_singleton_eq` — `iwSymbolSet {α} Φ = Φ(· - α)`;
* `Work.Analysis.IWMultiplier.integrable_comp_sub_eq` — translation invariance of
  integrability for `circleMeasure`;
* `Work.Analysis.IWMultiplier.iwKernel_eq_zero_of_not_integrable` — the kernel of a non-integrable
  symbol vanishes;
* `Work.Analysis.IWMultiplier.iwConv_singleton_eq_zero_of_not_integrable` — the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory
open scoped BigOperators ENNReal NNReal FourierTransform

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- The additive Haar measure on the circle is translation invariant, so translating the argument
of a `ℂ`-valued function by a fixed element preserves integrability. -/
theorem integrable_comp_sub_eq (g : Circle → ℂ) (a : Circle) :
    Integrable (fun t : Circle => g (t - a)) circleMeasure ↔ Integrable g circleMeasure := by
  rw [show (fun t : Circle => g (t - a)) = fun t : Circle => g (t + (-a)) from by
    funext t
    rw [sub_eq_add_neg]]
  refine ⟨fun h => ?_, fun h => h.comp_add_right (-a)⟩
  have h' : Integrable (fun t : Circle => g (t + a + (-a))) circleMeasure := h.comp_add_right a
  have h'' : (fun t : Circle => g (t + a + (-a))) = g := by
    funext t
    rw [add_assoc, add_neg_cancel, add_zero]
  rwa [h''] at h'

/-- The Ionescu–Wainger symbol of a singleton frequency set: `iwSymbolSet {α} Φ` is the translate
`ξ ↦ Φ (ξ - α)`. -/
theorem iwSymbolSet_singleton_eq (α : Circle) (Φ : Circle → ℂ) :
    iwSymbolSet {α} Φ = fun ξ => Φ (ξ - α) := by
  funext ξ
  simp [iwSymbolSet]

/-- **The kernel of a non-integrable symbol vanishes.**  `iwKernel m j` is the Bochner integral of
`fourier (-j) · m` over the circle.  If `m` is not integrable then `fourier (-j) · m` is not
integrable either (multiply by `fourier j`, which has modulus one), so the integral is the junk
value `0` by `MeasureTheory.integral_undef`. -/
theorem iwKernel_eq_zero_of_not_integrable {m : Circle → ℂ}
    (hm : ¬ Integrable m circleMeasure) (j : ℤ) :
    iwKernel m j = 0 := by
  rw [iwKernel, fourierCoeff, integral_undef]
  intro h
  refine hm ?_
  have h2 : Integrable
      (fun t : Circle => (fourier (-j) t • m t) • fourier j t) circleMeasure :=
    h.mul_bdd ((map_continuous (fourier j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [fourier_apply, Circle.norm_coe])
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : fourier (-j) t * fourier j t = 1 := by
    rw [← fourier_add, neg_add_cancel]
    simp
  simp only [smul_eq_mul]
  calc (fourier (-j) t * m t) * fourier j t
      = (fourier (-j) t * fourier j t) * m t := by ring
    _ = 1 * m t := by rw [h1]
    _ = m t := one_mul _

/-- **The Ionescu–Wainger multiplier with a singleton frequency set and a non-integrable symbol is
zero.**  Since `iwSymbolSet {α} σ = σ(· - α)` is not integrable, all kernel coefficients
`iwKernel (iwSymbolSet {α} σ) j` vanish, and hence so does the convolution. -/
theorem iwConv_singleton_eq_zero_of_not_integrable {α : Work.Analysis.IonescuWainger.Circle}
    (σ : Work.Analysis.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ)
    (hf : (Function.support f).Finite)
    (hσ : ¬ MeasureTheory.Integrable σ Work.Analysis.IonescuWainger.circleMeasure) :
    Work.Analysis.IWMultiplier.iwConv {α} σ f = 0 := by
  have hσ' : ¬ Integrable (iwSymbolSet {α} σ) circleMeasure := by
    rw [iwSymbolSet_singleton_eq]
    intro h
    exact hσ ((integrable_comp_sub_eq σ α).mp h)
  funext n
  rw [iwConv_apply]
  simp only [iwKernel_eq_zero_of_not_integrable hσ']
  simp

end Work.Analysis.IWMultiplier
