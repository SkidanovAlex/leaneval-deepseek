/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The division closure of `K[G]` as a rational `Kˣ × G`-semiring

This file starts the formalisation of [JZLA20, §4.3] and [JZLA20, §6.1] in the setting of the
Theorem 6.1 induction: for a field `K`, a group `G` and a ring `U` with a ring homomorphism
`φ : K[G] →+* U`, the **division closure** `D = divisionClosure (Set.range φ) ⊆ U` is a rational
`Kˣ × G`-semiring ([JZLA20, §4.3]), with

* `smul (λ,g) x = φ (λ·g) * x` and `smulRight x (λ,g) = x * φ (λ·g)`, where `λ·g = single g λ`;
* `x⋄ = x⁻¹` if `x` is a unit of `D`, and `x⋄ = 0` otherwise.

Since `⋄` is inversion on the units, the image of the universal morphism
`Φ : Rat(Kˣ × G) →+* D` is closed under inverses of its units; as it is also a subring containing
`φ(K[G])`, an induction on the division-closure chain `Q₀ ⊆ Q₁ ⊆ ⋯` shows that
**`Φ` is surjective onto `D`** — this is [JZLA20, Lemma 4.2] (see [Sthesis, Examples 5.37, 5.38]),
and it is what makes the `H`-complexity `tree_H` of [JZLA20, §4.3] well defined.

Everything here is `Prop`-valued data about an arbitrary `φ`; the Theorem 6.1 induction
(`Submission/Work/ORHughesFree/Section6/…`) consumes it together with [JZLA20, Proposition 5.1]
(`Submission.Work.ORHughesFree.Prop51.isUnit_of_conclB`, with the coefficient-unit hypothesis
of [JZLA20, Proposition 5.1]).
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.JZLA20

set_option autoImplicit false

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- The element `λ · g` of `K[G]`, for `(λ, g) : Kˣ × G`: the group-like unit of the group algebra. -/
noncomputable def unitOf (u : Kˣ × G) : MonoidAlgebra K G := MonoidAlgebra.single u.2 (u.1 : K)

@[simp] theorem unitOf_one : unitOf (K := K) (G := G) 1 = 1 := by
  simp [unitOf, MonoidAlgebra.one_def]

theorem unitOf_mul (u v : Kˣ × G) : unitOf (u * v) = unitOf u * unitOf v := by
  rw [unitOf, unitOf, unitOf, Prod.mk_mul_mk, MonoidAlgebra.single_mul_single, Units.val_mul]

theorem unitOf_left_inv (u : Kˣ × G) : unitOf u⁻¹ * unitOf u = 1 := by
  rw [← unitOf_mul, inv_mul_cancel, unitOf_one]

theorem unitOf_right_inv (u : Kˣ × G) : unitOf u * unitOf u⁻¹ = 1 := by
  rw [← unitOf_mul, mul_inv_cancel, unitOf_one]

end Work.ORHughesFree
