/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Perlis/Gassmann input of §6

Reference: arXiv:2601.01251, §6, proof of `thm:uchida isomorphism`, citing
*arithmetic equivalence Perlis* (Perlis' theorem: arithmetically equivalent number fields have the
same Galois closure) and Gassmann's theorem.

If `M₁`, `M₂` are arithmetically equivalent number fields inside a common finite Galois extension
`N/ℚ`, then — in the common Galois group `Gal(N/ℚ)` — every element of `Gal(N/M₁)` is conjugate into
`Gal(N/M₂)`, and conversely.  This is the classical Gassmann condition; it is the **only** step of
§6 whose proof needs the Dedekind zeta function (and hence the only analytic input of this area).
-/

import Submission.NK.UchidaKummer.Uchida.ArithmeticEquivalent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

open IntermediateField

/-- **The Perlis/Gassmann input.**

Two arithmetically equivalent number fields `M₁`, `M₂` with a common finite Galois closure `N/ℚ`
have conjugate-into fixing subgroups in `Gal(N/ℚ)`: every element of `Gal(N/M₁)` is conjugate in
`Gal(N/ℚ)` into `Gal(N/M₂)` and conversely.  (Equivalently: the subgroups are Gassmann equivalent,
which for arithmetically equivalent fields is Perlis' theorem; the "conjugate into" form used here
is the immediate consequence of the Gassmann condition that §6 consumes.) -/
def PerlisGassmannInput : Prop :=
  ∀ (N : Type) [Field N] [NumberField N] [Algebra ℚ N] [IsGalois ℚ N]
    (M₁ M₂ : IntermediateField ℚ N),
    ArithmeticallyEquivalent ↥M₁ ↥M₂ →
    (∀ x ∈ M₁.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₂.fixingSubgroup) ∧
    (∀ x ∈ M₂.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ M₁.fixingSubgroup)

end NK.UchidaKummer
