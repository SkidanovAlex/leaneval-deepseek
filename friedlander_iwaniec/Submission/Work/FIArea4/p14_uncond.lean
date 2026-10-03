import Mathlib
import Submission.Work.FIArea4.S14final
import Submission.Work.FIArea4.prop_11_1

/-!
# FI §§11–14, unconditional

`Work.FIArea4.prop_11_1` (FI Proposition 11.1, (11.14), proved in
`Submission/Work/FIArea4/prop_11_1.lean`) supplies `p14Prop111All`, so the whole chain
§11 → §12 → §13 → §14 becomes unconditional:

* `p12_all` — Proposition 12.1 (12.3)–(12.4);
* `p14_all` — Proposition 14.1 (14.1) in the `p14Bracket` normalisation;
* `p14_all_unfolded` — the same with the bracket written out.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- FI Proposition 11.1 (11.14) in the all-`ε` form `p14Prop111All`. -/
theorem h11_all : Work.FIArea4.p14Prop111All := Work.FIArea4.prop_11_1

/-- **FI Proposition 12.1 (12.3)–(12.4)**, unconditional. -/
theorem p12_all : Work.FIArea4.p14Prop121All := p12_all_of_h11 h11_all

/-- **FI Proposition 14.1 (14.1)** in the `p14Bracket` normalisation, unconditional. -/
theorem p14_all : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ),
    1 ≤ D → 1 ≤ R → 1 ≤ S →
    (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      Work.FIPlan.Vvar R S D α ≤ C * p14Bracket D R S ε * p14Ener R S α :=
  p14_all_of_h11 h11_all

/-- **FI Proposition 14.1 (14.1)** with the bracket written out, unconditional. -/
theorem p14_all_unfolded : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤
          C * ((D : ℝ) + (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
                + (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
                  * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
                + ((R : ℝ) + (S : ℝ)) ^ ((1 : ℝ) / 12)
                  * ((R : ℝ) * (S : ℝ)) ^ ((11 : ℝ) / 12 + ε))
            * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
                ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s)) :=
  p14_all_unfolded_of_h11 h11_all

end

end Work.FIArea4
