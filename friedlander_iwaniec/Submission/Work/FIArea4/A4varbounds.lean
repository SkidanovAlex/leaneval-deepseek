import Mathlib
import Submission.Work.FIPlan.Interface

/-!
# The numerical brackets and the three `Prop`s of Friedlander–Iwaniec §§11–14

This module fixes the *interface* between the three estimates that the paper's §§11–13 provide
and the assembly of Proposition 14.1 (`Submission/Work/FIArea4/prop_14_1.lean`).

* `p14T11` is the bracket of Proposition 11.1 (FI (11.14)),
* `p14T12` is the bracket `L(D,R,S)` of Proposition 12.1 (FI (12.3)–(12.4)),
* `p14T13` is the bracket of Proposition 13.1 (FI (13.5)),
* `p14Bracket` is the bracket of Proposition 14.1 (FI (14.1)),
* `p14L2` / `p14Ener` are the two energy normalisations (`Σ‖α‖²` resp. `Σ τ(r)‖α‖²`),
* `p14Prop111`, `p14Prop121`, `p14Prop131` are the three estimates themselves, as `Prop`s, with
  the support hypothesis `(r,2s) = 1` (the paper's (12.1)) where the paper needs it.

The variance is `Work.FIPlan.Vvar R S D α = Σ_{D<d≤2D} Σ_{a mod d} |Σ_{r̄s ≡ a (d)} α r s (r|d')|²`
with `(r|d')` the Jacobi symbol, `d' = oddPart d`, and `(r,s)` running over the *whole* box
`1 ≤ r ≤ 2R`, `1 ≤ s ≤ 2S`.
-/

namespace Work.FIArea4

open scoped BigOperators

noncomputable section

/-- `(R+S)^{1/12}(RS)^{11/12+ε}`, the last term of the bracket of FI Proposition 14.1. -/
def p14Last (R S : ℕ) (ε : ℝ) : ℝ :=
  ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((11:ℝ)/12 + ε)

/-- `D₁ = (R+S)^{1/12}(RS)^{5/12}` (FI Prop. 14.1). -/
def p14D1 (R S : ℕ) : ℝ := ((R:ℝ)+(S:ℝ)) ^ ((1:ℝ)/12) * ((R:ℝ)*(S:ℝ)) ^ ((5:ℝ)/12)

/-- `D₂ = (R+S)^{-1/8}(RS)^{5/8}` (FI Prop. 14.1). -/
def p14D2 (R S : ℕ) : ℝ := ((R:ℝ)+(S:ℝ)) ^ (-((1:ℝ)/8)) * ((R:ℝ)*(S:ℝ)) ^ ((5:ℝ)/8)

/-- The bracket `N(D,R,S)` of FI Proposition 14.1. -/
def p14Bracket (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ) + (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
    + p14Last R S ε

/-- The bracket of FI Proposition 11.1. -/
def p14T11 (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
      * (((R : ℝ) * (S : ℝ)) ^ ε)

/-- The bracket `L(D,R,S)` of FI Proposition 12.1 (12.4). -/
def p14T12 (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ)
    + (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
        * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ)
    + ((D : ℝ)⁻¹ * ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
      * (((R : ℝ) * (S : ℝ)) ^ ε)

def p14T13 (D R S : ℕ) (_ε : ℝ) : ℝ :=
  (D : ℝ) * ((R : ℝ) + (S : ℝ)) ^ ((1 : ℝ) / 4) * ((R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 4)
      + (D : ℝ) ^ (-(1 : ℝ) / 2) * ((R : ℝ) + (S : ℝ)) ^ ((1 : ℝ) / 8)
          * ((R : ℝ) * (S : ℝ)) ^ ((9 : ℝ) / 8)

/-- `Σ_{r ≤ 2R, s ≤ 2S} ‖α r s‖²`, the energy normalisation of Propositions 11.1/13.1. -/
def p14L2 (R S : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)

/-- `Σ_{r ≤ 2R, s ≤ 2S} τ(r)‖α r s‖²`, the energy normalisation of Proposition 14.1. -/
def p14Ener (R S : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
    ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (α r s)

/-- FI Proposition 11.1 (11.14), as a `Prop`. -/
def p14Prop111 (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
    Work.FIPlan.Vvar R S D α ≤ C * p14T11 D R S ε * p14L2 R S α

/-- FI Proposition 12.1 (12.3)–(12.4), as a `Prop`. -/
def p14Prop121 (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
    (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      Work.FIPlan.Vvar R S D α ≤ C * p14T12 D R S ε * p14Ener R S α

def p14Prop131 (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
    (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α

/-- FI Proposition 11.1 with its full "for every `ε > 0`" quantifier (this is the shape of the
sibling statement `Work.FIArea4.prop_11_1`, and it is what the *derivations* of §§12–13 need:
the paper's proofs use the estimate at a smaller exponent than the one in their conclusion, to
absorb the `τ`-weight, the `log`-powers and the `(RS)^ε`-bookkeeping). -/
def p14Prop111All : Prop := ∀ ε : ℝ, 0 < ε → p14Prop111 ε

/-- FI Proposition 12.1 with its full "for every `ε > 0`" quantifier. -/
def p14Prop121All : Prop := ∀ ε : ℝ, 0 < ε → p14Prop121 ε

/-- FI Proposition 13.1 with its full "for every `ε > 0`" quantifier. -/
def p14Prop131All : Prop := ∀ ε : ℝ, 0 < ε → p14Prop131 ε

end

end Work.FIArea4
