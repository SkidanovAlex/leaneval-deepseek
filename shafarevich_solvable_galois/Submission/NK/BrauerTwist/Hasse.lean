/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Brauer / local-global inputs of Neukirch's criterion, with `μ_p`-coefficients

This is the twisted-coefficient counterpart of `Submission/Work/BrauerHasse/Hasse.lean`.
The sibling file states Neukirch's criterion with the **trivial** coefficient module `Z/p`, i.e. for
`H²(·, Z/p)`; by local Tate duality that group is `Hom(μ_p(κ), Q/Z)`, which *vanishes* whenever
`μ_p ⊄ κ` (e.g. `κ = Q_p`, `p` odd), so the classical input cannot be stated that way.  Here the
coefficients are the `p`-th roots of unity `μ_p = Z/p(1)` (see `Basic.lean`), and the three inputs
are the ones that are actually true:

* `NK.BrauerTwist.LocalH2Input` — the local computation `H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p`
  (Kummer sequence + Hilbert 90; `Br(κ) ≅ Q/Z`), transported to the closed subgroups
  `H ≤ G_K` isomorphic to `G_κ`.  This is *unconditional* for a `p`-adic `κ` (Serre, *Local
  Fields* XII–XIV; CoNF (7.2.6)) — in contrast with the trivial-coefficient form.
* `NK.BrauerTwist.Sha2Vanishing` — the Hasse–Brauer–Noether principle in `μ_p`-coefficients
  together with its limit form over the levels: `Br(M)[p] → ∏_v Br(M_v)[p]` is injective.
* `NK.BrauerTwist.LocalDecompositionCriterion` — Neukirch's local finishing step.

The one thing *proved* here (from the inputs) is the cohomological core of Neukirch's argument:
`NK.BrauerTwist.exists_loc_ne_zero`.
-/

import Submission.NK.BrauerTwist.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.BrauerTwist

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The local Brauer input, with `μ_p`-coefficients.**  For a `p`-adic field `κ` with separable
closure `κ'`, every closed subgroup `H ≤ G_K` isomorphic to `G_κ = Gal(κ'/κ)` has a non-zero class
in `H²(H, μ_p)`.

Classically: the Kummer sequence `1 → μ_p → κ'ˣ → κ'ˣ → 1` together with Hilbert 90 gives
`H²(G_κ, μ_p) ≅ Br(κ)[p] ≅ Z/p`, and `Br(κ) ≅ Q/Z`.  Unlike the trivial-coefficient form
(`NK.BrauerHasse.LocalH2Input`), this holds for **every** `p`-adic field `κ` and every prime
`p`, with no hypothesis relating `p` to `κ`; see the module docstring of `Basic.lean`. -/
def LocalH2Input (p : ℕ) (K K' κ κ' : Type u) [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Nonempty (H ≃* Gal(κ'/κ)) →
    ∃ x : H2Twist p H, x ≠ 0

/-- **The local Brauer group computation with `μ_p`-coefficients**: for a `p`-adic field `κ`,
`H²(G_κ, μ_p) ≅ Z/p`, i.e. `Br(κ)[p] ≅ Z/p`.

The second component (`∃ x ≠ 0`) is the only consequence the argument uses; the first says that
the colimit has exactly `p` elements.  Classically this is the local invariant
`inv : Br(κ) ≅ Q/Z` (Serre, *Local Fields* XII–XIV; CoNF (7.2.6)). -/
def LocalFieldBrauerCyclic (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  Nonempty (H2Twist (K := κ) (K' := κ') p ⊤ ≃ ZMod p) ∧
    ∃ x : H2Twist (K := κ) (K' := κ') p ⊤, x ≠ 0

/-- The second half of the local Brauer group computation: there is a non-zero class in
`H²(G_κ, μ_p)`.  This is the only consequence of `LocalFieldBrauerCyclic` that the argument uses. -/
theorem exists_ne_zero_of_localFieldBrauerCyclic {p : ℕ}
    (h : LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p) :
    ∃ x : H2Twist (K := κ) (K' := κ') p ⊤, x ≠ 0 := h.2

/-- **The Hasse principle / vanishing of the limiting Sha², with `μ_p`-coefficients**: a class in
`H²(H, μ_p)` (for `H ≤ G_K` closed and isomorphic to the absolute Galois group of a `p`-adic
field `κ`) whose localisation at every place of `K̄` over a finite prime of `K` vanishes is itself
zero.  Classically this is Hasse–Brauer–Noether for the `p`-torsion of the Brauer group,
`Br(M)[p] ↪ ∏_v Br(M_v)[p]`, together with the passage to the direct limit over the levels
(CoNF XII §12.1). -/
def Sha2Vanishing (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ x : H2Twist p H,
      (∀ A : OverFinitePrime K K', H2Twist.loc p H x A = 0) → x = 0

/-- **Neukirch's local finishing step, with `μ_p`-coefficients**: if a class in `H²(H, μ_p)` has a
non-zero local component at a place `A` of `K̄` over a finite prime of `K`, then `H` is the
decomposition group of a place of `K̄` over a finite prime of `K`.  This is the local half of the
"if" direction of CoNF (12.1.9), i.e. Neukirch's Theorem 1. -/
def LocalDecompositionCriterion (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Subgroup.normalizer H = H → Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : OverFinitePrime K K') (x : H2Twist p H),
      H2Twist.loc p H x A ≠ 0 →
      ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
        MulAction.stabilizer Gal(K'/K) A' = H

/-- **The cohomological core of Neukirch's argument, with `μ_p`-coefficients.**  Under the local
Brauer input and the vanishing of the limiting Sha², every non-zero class in `H²(H, μ_p)` has a
non-zero local component at some place of `K̄` over a finite prime of `K`.

Equivalently: the localisation map `H²(H, μ_p) → ∏_A H²(H ⊓ D_A, μ_p)` has trivial kernel, so
that `Z/p ≅ H²(H, μ_p)` injects into the product of the local groups. -/
theorem exists_loc_ne_zero (p : ℕ) (hvan : Sha2Vanishing (K := K) (K' := K') p κ κ')
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Twist p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Twist.loc p H x A ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (hvan H hH hκ x h)

end NK.BrauerTwist
