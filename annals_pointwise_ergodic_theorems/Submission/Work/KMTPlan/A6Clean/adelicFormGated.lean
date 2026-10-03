/-
# The §8 adelic form on the large-`lcL` data, and its producer

`Work.KMTPlan.A6Clean.AdelicFormPropRangePosB` is the clause list
`Work.KMTPlan.A6Clean.AdelicClausesAt` demanded **only on the data with `B ρ ≤ lcL l₁ l₂ k₁ k₂`**
(`B : ℝ → ℕ` a threshold, `lcL = max (max l₁ l₂) (max k₁ k₂)`).

This gate is mathematically necessary, not cosmetic: `AdelicClausesAt`'s clause (1) asks for a
family whose first-variable slices are band limited to `1/(8·arithQ ρ (max l₁ l₂))` and whose
diagonal samples are the gated slice.  A band-`β` function is determined by its samples at the
spacing `arithQ ρ (max l₁ l₂)` (because `β·Q = 1/8 < 1/2`), while the frozen slice has spectral
bumps of width `≍ 2^{-2·uScale ρ Lv}` on the lattice `(1/Q)ℤ`; the sampling therefore works iff

  `8 · arithQ ρ (max l₁ l₂) · 2^{-2·uScale ρ Lv} ≤ 1`     (*the band condition*)

and this is equivalent to `Lv ≥ B₀(ρ)` for a `ρ`-only threshold `B₀` (use
`Work.Analysis.IonescuWainger.iwP_element_le`: every `q ∈ iwP ρ l` is `≤ 2^{K·2^{ρl}}`).  See
`NOTES_A6_adelicCaseB_OBSTRUCTION_SESSION.md`.

**Producer.**  For the data above the threshold the clauses are proved by the §8 packet
construction:

* `l₁ ≠ 0 ∧ l₂ ≠ 0`: `Work.KMTPlan.A6Clean.adelicClausesCaseA`, whose per-scale hypotheses are the
  regime predicates `MdlLiftRegimeF`/`MdlLiftRegimeG`; these are supplied by the PROVED
  `Work.A6Clean.MdlWindowLiftRegimeNoGSB` / `MdlWindowLiftRegimeGNoGSB` (a `ρ`-only threshold
  each, so the maximum is again `ρ`-only);
* `l₁ = 0 ∨ l₂ = 0`: `Work.KMTPlan.A6Clean.adelicClausesCaseZero` (no largeness at all: at `l = 0`
  the arithmetic frequency set is the singleton `iwArithFreqs ρ 0 = {0}`, so the separation
  condition is vacuous and `mdlLiftFZero`/`mdlLiftGZero` need only `mdlCore`; the data bounds are
  `PacketFamFZeroUniform`/`PacketFamGZeroUniform`, which have no vanishing hypothesis).

The two branches are combined with `Work.KMTPlan.A6Clean.adelicClausesAt_mono` (`c` smaller and
`A`, `Cin` larger is easier — note this needs `0 ≤ ρ`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.adelicClausesCaseA
import Submission.Work.KMTPlan.A6Clean.adelicClausesAt_mono
import Submission.Work.A6Clean.MdlWindowLiftRegimeNoGSB
import Submission.Work.A6Clean.MdlWindowLiftRegimeGNoGSB
import Submission.Work.A6Clean.PacketFamFZeroUniform
import Submission.Work.A6Clean.PacketFamGZeroUniform
import Submission.Work.KMTPlan.A6Clean.mdlLiftGZero

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTPlan.A6

noncomputable section

/-- **The §8 adelic form on the large-`lcL` data.**

Identical to `Work.KMTPlan.A6Clean.AdelicFormPropRangePos`, except that the clause list
`AdelicClausesAt` is demanded only on the data with `B ρ ≤ lcL l₁ l₂ k₁ k₂`.  The constants
`c, A, ρ₀, Cin` are still chosen before the datum (and `B` is a `ρ`-only threshold). -/
def AdelicFormPropRangePosB (P : ℤ[X]) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) (B : ℝ → ℕ) : Prop :=
  ∀ (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < adelicRTop P)
    (R : ℝ) (hR : 2 < R) (hRr : R < (r : ℝ))
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (j₁ j₂ : ℤ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)),
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        B ρ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
        AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin

end

end Work.KMTPlan.A6Clean
