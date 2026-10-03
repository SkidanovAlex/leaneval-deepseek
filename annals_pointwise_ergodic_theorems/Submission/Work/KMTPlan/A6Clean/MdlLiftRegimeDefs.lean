/-
# The regime conditions of the model window-piece lifts, as named predicates

`Work.KMTPlan.A6Clean.mdlWindowLiftF` / `mdlWindowLiftG` (PROVED,
`A6Clean/MdlWindowLiftF.lean`) produce, at a *single* scale `n`, a band-`γᵢ n` lift `W` of the
window piece of the model slice, from the following five hypotheses on `n`:

* `1 ≤ ⌊a n⌋`,
* the *narrow band* inequality `2^{k₁ - logN ⌊a n⌋} ≤ 2^{-2·uScale ρ Lv - 1}`
  (`Lv = lcL l₁ l₂ k₁ k₂`),
* the non-aliasing of `iwArithFreqs ρ l₁` at the window scale `-(uScale ρ Lv)`,
* the arc support of the periodised modified bump `varphiNtj ⌊a n⌋ k₁ j₁ t`,
* the *separation* of distinct elements of `iwArithFreqs ρ l₁` at scale
  `2^{-2·uScale ρ Lv} + 2^{k₁ - logN ⌊a n⌋}`.

`Work.A6Clean.MdlWindowLiftRegime` / `MdlWindowLiftRegimeG` (PROVED) derive them from
`mdlCore ∧ goodScale` and the largeness `B(ρ) ≤ lv`; `MdlWindowLiftRegimeNoGS(B)` /
`MdlWindowLiftRegimeGNoGS(B)` (spawned) drop the `goodScale` hypothesis.

This module *names* the five conditions, so that the §8 assembly
(`adelicClausesCaseA`) can take them as per-scale hypotheses and the producer can discharge them
from the regime lemmas.  The two predicates are **exactly** the hypothesis lists of
`mdlWindowLiftF` / `mdlWindowLiftG` (minus the scale-independent data `ρ, C₀, P, f, g, hj, hk`),
so the projections are `And.left`/`And.right`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlWindowLiftF

set_option autoImplicit false

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The regime conditions of the `f`-side window-piece lift at scale `n`** (exactly the five
hypotheses of `Work.KMTPlan.A6Clean.mdlWindowLiftF` other than the datum-level ones). -/
def MdlLiftRegimeF (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (n : ℕ) : Prop :=
  (1 ≤ Nat.floor (a n)) ∧
  ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
    ≤ (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)) ∧
  Work.Analysis.IonescuWainger.NonAliasing
    (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) ∧
  Work.Analysis.IonescuWainger.SupportedInArc
    (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1)
    (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)) ∧
  (∀ ⦃α β : Circ⦄, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ →
    β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → α ≠ β →
    (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      + (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
      < ‖α - β‖)

/-- **The regime conditions of the `g`-side window-piece lift at scale `n`** (exactly the five
hypotheses of `Work.KMTPlan.A6Clean.mdlWindowLiftG` other than the datum-level ones). -/
def MdlLiftRegimeG (ρ : ℝ) (P : Polynomial ℤ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ) : Prop :=
  (1 ≤ Nat.floor (a n)) ∧
  ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
    ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2
        * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)) ∧
  Work.Analysis.IonescuWainger.NonAliasing
    (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) ∧
  Work.Analysis.IonescuWainger.SupportedInArc
    (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)
    (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)) ∧
  (∀ ⦃α β : Circ⦄, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ →
    β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → α ≠ β →
    (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2
        * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      + (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
      < ‖α - β‖)

end Work.KMTPlan.A6Clean
