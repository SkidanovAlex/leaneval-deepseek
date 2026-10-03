/-
# Measurability in the modulation parameter of the slice of the exact-height model tuple

The §6 model operator of the low case of area A6 (`Work.KMTPlan.A6.lowModel`,
`Work.KMTPlan.A6.Kmod`) is the `t`-integral over `[1/2,1]` of the twisted bilinear multiplier
`BtwistEx` evaluated at the two Ionescu--Wainger projections `Tm ρ l₁ (φ_{N,t}) f` and
`Tm ρ l₂ (φ̃_{N,t}) g` of the modulated bumps.  For the `t`-integral (Fubini, dominated
convergence) to make sense, each slice has to be a measurable function of the modulation
parameter `t ∈ ℝ`, and this is what the present file establishes.

The argument is short once the two ingredients are isolated:

* `Tm ρ l φ u = iwConv (diffFreqs ρ l) (periodize φ) u` is a convolution, i.e. an unconditional
  sum over `ℤ` of the kernel coefficients of the IW symbol `iwSymbolSet (diffFreqs ρ l)
  (periodize φ)` against `u`;  the measurability in `t` of those coefficients, for *every* finite
  frequency set, is `Work.KMTAreas.A7.measurable_iwKernel_varphiNt_general` /
  `…measurable_iwKernel_varphitildeNt_general`, and hence
  `Work.KMTAreas.A7.measurable_iwConv_varphiNt` / `…measurable_iwConv_varphitildeNt` give the
  measurability of the convolution values `t ↦ Tm ρ l (φ_{N,t}) f y` for each fixed `y : ℤ`
  (an unconditional sum of measurable functions over the countable set `ℤ` is measurable);
* `BtwistEx` is a double unconditional sum over `j₁, j₂ ∈ ℤ` of a *constant* arithmetic kernel
  times the two convolution values, so `Measurable.tsum` applied twice reduces everything to the
  previous bullet.

Everything here is a consequence of the joint measurability of `(t,ξ) ↦ φ_{N,t}(ξ)`,
`(t,ξ) ↦ φ̃_{N,t}(ξ)`, which lives in the imported modules.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTAreas.A7.iwConv_varphiNt_bounded_measurable
import Submission.Work.KMTAreas.A7.iwConv_varphitildeNt_bounded_measurable

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-- **Measurability in `t` of the slice of the exact-height twisted bilinear multiplier.**

`BtwistEx` is the double unconditional sum over `j₁, j₂ ∈ ℤ` of the constant arithmetic kernel
`arithKernelEx … * cw m₁ j₁ * cw m₂ j₂` times the values of the two Ionescu--Wainger projections
`Tm ρ l₁ (φ_{N,t}) f` and `Tm ρ l₂ (φ̃_{N,t}) g`; an unconditional sum of measurable functions is
measurable, and the measurability of each projection value is
`measurable_iwConv_varphiNt` / `measurable_iwConv_varphitildeNt`. -/
theorem measurable_BtwistEx_slice (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ u : ℕ)
    (m₁ m₂ : ℝ → ℂ) (f g : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ => BtwistEx ρ P l₁ l₂ m₁ m₂
        (Tm ρ l₁ (varphiNt u k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree u k₂ t) g) x) := by
  simp only [BtwistEx]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j₁ : ℤ => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j₂ : ℤ => ?_)
  have h₁ : Measurable (fun t : ℝ => Tm ρ l₁ (varphiNt u k₁ t) f (x - j₁)) :=
    measurable_iwConv_varphiNt (diffFreqs ρ l₁) u k₁ f (x - j₁)
  have h₂ : Measurable (fun t : ℝ => Tm ρ l₂ (varphitildeNt P P.natDegree u k₂ t) g (x - j₂)) :=
    measurable_iwConv_varphitildeNt P (diffFreqs ρ l₂) u k₂ g (x - j₂)
  exact (h₁.const_mul _).mul h₂

/-- **The requested lemma**: every `t`-slice of the exact-height model tuple of the low case is
a.e. measurable as a function of the modulation parameter.  This is the measurability input for
the Fubini and dominated-convergence arguments applied to the `t`-integral defining the model
operator. -/
theorem sliceAEMeasurable (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (u : ℕ)
    (f g : ℤ → ℂ) :
    ∀ x : ℤ, AEMeasurable (fun t : ℝ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ m₁ m₂
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt u k₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree u k₂ t) g) x)
      MeasureTheory.volume := by
  intro x
  exact (measurable_BtwistEx_slice ρ P l₁ l₂ k₁ k₂ u m₁ m₂ f g x).aemeasurable

end

end Work.KMTPlan.A6
