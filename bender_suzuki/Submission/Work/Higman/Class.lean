/-
Copyright (c) 2024. All rights reserved.

# Higman's Theorem 1, stated

`Submission.Blueprint.HigmanProp` contains
* the four structural clauses `Z(P) = Ω₁(P)`, `x ^ 2 ∈ Z(P)`, `P' = Z(P)`, `|P| ∈ {q², q³}`,
* the classification of the `|P| = q²` case as `A(n,θ)`.

It is missing the classification of the `|P| = q³` case, i.e. the types `B`, `C`, `D` of
Higman's table, which are used by areas `Hering` (Peterfalvi I App. VIII) and `PSU3`
(Peterfalvi II Ch. VI §3, App. VIII).  This file states that missing part as `HigmanQ3Prop`
and bundles it with `HigmanProp` as `HigmanClassProp`.

**Status.**  The proof of `HigmanClassProp` is Higman's Theorem 1 (about 15 pages of linear
algebra over `GF(2ⁿ)`); the pieces are being formalised in this directory.  `Main.lean`
assembles whatever is available; see `NOTES.md`.
-/

import Submission.Work.Higman.Family
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open LeanEval.GroupTheory.Defs

namespace Work.Higman

/-- **The order-`q³` classification** (Higman 1963, Theorem 1, types `B`, `C`, `D`).

For a Suzuki 2-group `P` with `|P| = q³`, `q = |Z(P)| = 2ⁿ`, there are
`θ : GF(2ⁿ) ≃+* GF(2ⁿ)` of odd order, `ε ∈ GF(2ⁿ)`, and a bijection
`e : P ≃ (GF(2ⁿ) × GF(2ⁿ)) × GF(2ⁿ)` (the first factor is `P/Z(P)`, the second `Z(P)`),
such that the multiplication of `P` is one of the three laws of Column V of Higman's table
(`B`, `C`, `D`), with the excluded values of `ε` of Column III. -/
def HigmanQ3Prop : Prop :=
  ∀ (P : Type) [Group P] [Finite P], Submission.Blueprint.IsSuzukiTwoGroup P →
    Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 →
    ∃ (n : ℕ)
      (e : P ≃ (GaloisField 2 n × GaloisField 2 n) × GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n),
      Nat.card ↥(Subgroup.center P) = 2 ^ n ∧ Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
            (e x).2 + (e y).2 + bCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1))
        ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
              (e x).2 + (e y).2 + cCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1))
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
              (e x).2 + (e y).2 + dCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1)))

/-- The full classification: `HigmanProp` together with the missing order-`q³` part. -/
def HigmanClassProp : Prop := Submission.Blueprint.HigmanProp ∧ HigmanQ3Prop

/-- The old `HigmanProp` follows from the extended statement. -/
theorem higmanProp_of_classProp (h : HigmanClassProp) : Submission.Blueprint.HigmanProp := h.1

/-- The extension only adds clauses. -/
theorem higmanProp_iff_classProp_left : HigmanClassProp → Submission.Blueprint.HigmanProp :=
  higmanProp_of_classProp

/-- **The bridge to the extended blueprint**: if the lead adds the order-`q³` clause to
`Submission.Blueprint.HigmanProp` in `Interfaces.lean`, this is how the new `Prop` is obtained
from the old one and the proved `HigmanQ3Prop`. -/
theorem higmanClassProp_of_parts (h : Submission.Blueprint.HigmanProp) (hq3 : HigmanQ3Prop) :
    HigmanClassProp := ⟨h, hq3⟩

end Work.Higman
