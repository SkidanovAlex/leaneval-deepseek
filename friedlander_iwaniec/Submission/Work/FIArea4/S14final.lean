import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.prop_14_1
import Submission.Work.FIArea4.S12final
import Submission.Work.FIArea4.prop_13_1

/-!
# FI Proposition 14.1, assembled from the proved Propositions 11.1*, 12.1 and 13.1

This module proves the *consolidated* Jacobi-twisted variance bound of Friedlander–Iwaniec
(Proposition 14.1, (14.1)) in the form in which §15 consumes it:

`Work.FIArea4.p14_all_of_h11 (h11 : p14Prop111All)`:
`∀ ε > 0, ∃ C > 0, ∀ D R S α, 1 ≤ D → 1 ≤ R → 1 ≤ S → (∀ r s, α r s ≠ 0 → (r,2s) = 1) →
  Vvar R S D α ≤ C · p14Bracket D R S ε · p14Ener R S α`.

The three inputs are
* `h11` — Proposition 11.1 (11.14) in its all-`ε` form (the proved
  `Work.FIArea4.prop_11_1_box` supplies it);
* `Work.FIArea4.p12_all_of_h11 : p14Prop121All` (`Submission/Work/FIArea4/S12final.lean`, the
  §12 "flipping of moduli" argument);
* `Work.FIArea4.prop_13_1 : p14Prop121All → p14Prop131All` (the §13 "enlarging moduli"
  argument, proved),
* glued by the numerical case analysis `p14asm_assembly` of
  `Submission/Work/FIArea4/prop_14_1.lean`.

Putting `h11 := prop_11_1_box` (once that module builds; it is blocked only by an in-progress
sibling module) gives the unconditional form.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **FI Proposition 14.1 (14.1)**, in the `p14Bracket` normalisation, conditional on
Proposition 11.1 in all-`ε` form. -/
theorem p14_all_of_h11 (h11 : Work.FIArea4.p14Prop111All) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤
          C * p14Bracket D R S ε * p14Ener R S α := by
  intro ε hε
  have h12 : Work.FIArea4.p14Prop121All := p12_all_of_h11 h11
  have h13 : Work.FIArea4.p14Prop131All := prop_13_1 h12
  exact p14asm_assembly ε hε (h11 ε hε) (h12 ε hε) (h13 ε hε)

/-- **FI Proposition 14.1 (14.1)**, with the bracket written out (the exact shape of
`Work.FIArea4.prop_14_1`), conditional on Proposition 11.1 in all-`ε` form. -/
theorem p14_all_unfolded_of_h11 (h11 : Work.FIArea4.p14Prop111All) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤
          C * ((D : ℝ) + (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
                + (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
                  * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
                + ((R : ℝ) + (S : ℝ)) ^ ((1 : ℝ) / 12)
                  * ((R : ℝ) * (S : ℝ)) ^ ((11 : ℝ) / 12 + ε))
            * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
                ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s)) := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := p14_all_of_h11 h11 ε hε
  exact ⟨C, hC, fun D R S α hD hR hS hcop => by
    have := h D R S α hD hR hS hcop
    simpa only [p14Bracket, p14Ener, p14Last] using this⟩

end

end Work.FIArea4
