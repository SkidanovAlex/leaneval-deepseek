/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Brauer / local-global inputs of Neukirch's decomposition-group criterion

This file isolates the classical inputs that Neukirch's characterisation of the decomposition
groups of an absolute Galois group needs, and derives from them the statement that the
development consumes.

## The inputs

* `NK.BrauerHasse.LocalFieldBrauerCyclic` — the **local Brauer group computation** at the local
  field itself: `H²(G_κ, Z/p) ≅ Z/p` for a p-adic field `κ` (local class field theory:
  `Br(κ) ≅ Q/Z`; with trivial `Z/p`-coefficients this holds for every prime `p`).  The proved
  lemma `NK.BrauerHasse.exists_ne_zero_of_localFieldBrauerCyclic` extracts the non-zero class.

* `NK.BrauerHasse.LocalH2Input` — the **transported form** of the local computation: for a
  p-adic field `κ`
  and every closed subgroup `H ≤ G_K` isomorphic to `G_κ = Gal(κ̄/κ)`, the second cohomology
  `H²(H, Z/p)` has a non-zero element.  Classically this is `Br(κ)[p] ≅ Z/p` (local class field
  theory), transported along the isomorphism `H ≅ G_κ`; the classical statement is

    `H²(G_κ, Z/p) ≅ Z/p` for every p-adic field `κ`.

* `NK.BrauerHasse.Sha2Vanishing` — the **Hasse principle** in the form used by the argument,
  i.e. the vanishing of the limiting Sha²: a class in `H²(H, Z/p)`, `H ≤ G_K` closed isomorphic to
  a local Galois group, whose localisation at *every* place of `K̄` over a finite prime of `K`
  vanishes, is zero.  Classically this is Hasse–Brauer–Noether (`Br(K) → ∏_v Br(K_v)`
  injective in `Z/p`-coefficients) together with its passage to the direct limit over the open
  subgroups containing `H` (CoNF XII §12.1, Ivanov, arXiv:1309.2801, §2.3).  See the module
  docstring of `NK.BrauerHasse.Main` for what would discharge it.

* `NK.BrauerHasse.LocalDecompositionCriterion` — the **local finishing step** of Neukirch's
  argument: a non-zero local Brauer obstruction of `H` at a place forces `H` to be that place's
  decomposition group (Neukirch, *Kennzeichnung der p-adischen und der endlich algebraischen
  Zahlkörper*, Invent. Math. 6 (1969), Theorem 1; CoNF (12.1.9); Ivanov, arXiv:1309.2801,
  proof of Theorem 2.14 `(b) ⇒ (a)`, where this is the "the prime is indecomposed" step, using
  Neukirch's Korollar 1 on injections of local absolute Galois groups).

## What is *proved* here

`NK.BrauerHasse.exists_loc_ne_zero`: from `LocalH2Input` and `Sha2Vanishing` it follows that a
non-zero class in `H²(H, Z/p)` has a non-zero local component at some place of `K̄` over a finite
prime of `K`.  This is the cohomological core of Neukirch's argument ("`Z/p ↪ ∏_v H²(D_v, Z/p)`").
-/

import Submission.NK.BrauerHasse.Profinite
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

namespace NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The local Brauer group input.**  For a p-adic field `κ` (with separable closure `κ'`),
every closed subgroup `H ≤ G_K` isomorphic to `G_κ` has non-zero second cohomology with trivial
`Z/p` coefficients.  Classically: `Br(κ)[p] ≅ Z/p` for a p-adic field `κ`, i.e.
`H²(G_κ, Z/p) ≅ Z/p` (local class field theory), transported along `H ≅ G_κ`. -/
def LocalH2Input (p : ℕ) (K K' κ κ' : Type u) [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Nonempty (H ≃* Gal(κ'/κ)) →
    ∃ x : H2Profinite p H, x ≠ 0

/-- **The local Brauer group computation** for a `p`-adic field `κ`: `H²(G_κ, Z/p) ≅ Z/p`.

(Local class field theory: `Br(κ) ≅ Q/Z`, so `Br(κ)[p] ≅ Z/p`; equivalently, the fundamental class
generates a cyclic group of order `p`.  With trivial `Z/p`-coefficients this is `H²(G_κ, Z/p) ≅ Z/p`
for *every* rational prime `p` — in particular no restriction on the relation between `p` and the
residue characteristic of `κ` is needed for this statement.  We record it as an equivalence of
types, which is what the argument uses.) -/
def LocalFieldBrauerCyclic (p : ℕ) (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  Nonempty (H2Profinite (K := κ) (K' := κ') p ⊤ ≃ Coeff.{u} p) ∧
    ∃ x : H2Profinite (K := κ) (K' := κ') p ⊤, x ≠ 0

/-- The second half of the local Brauer group computation: `H²(G_κ, Z/p)` has a non-zero class.
This is the only consequence of `LocalFieldBrauerCyclic` that the argument uses. -/
theorem exists_ne_zero_of_localFieldBrauerCyclic {p : ℕ}
    (h : LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p) :
    ∃ x : H2Profinite (K := κ) (K' := κ') p ⊤, x ≠ 0 := h.2

/-- **The Hasse principle / vanishing of the limiting Sha²**, in the local-global form used by
Neukirch's argument: a class in `H²(H, Z/p)` (for `H ≤ G_K` closed and isomorphic to the absolute
Galois group of a p-adic field `κ`) whose localisation at every place of `K̄` over a finite prime
of `K` vanishes is itself zero.  This is Hasse–Brauer–Noether in `Z/p`-coefficients together with
the passage to the direct limit; see the module docstring. -/
def Sha2Vanishing (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ x : H2Profinite p H,
      (∀ A : OverFinitePrime K K', H2Profinite.loc p H x A = 0) → x = 0

/-- **The local finishing step of Neukirch's argument** (see the module docstring): if a class in
`H²(H, Z/p)` has non-zero local component at a place `A` of `K̄` over a finite prime of `K`, then
`H` is the decomposition group of a place of `K̄` over a finite prime of `K`.  This is the local
half of the "if" direction of CoNF (12.1.9), i.e. Neukirch's Theorem 1. -/
def LocalDecompositionCriterion (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Subgroup.normalizer H = H → Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : OverFinitePrime K K') (x : H2Profinite p H),
      H2Profinite.loc p H x A ≠ 0 →
      ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
        MulAction.stabilizer Gal(K'/K) A' = H

/-- **The cohomological core of Neukirch's argument.**  Under the local Brauer input and the
vanishing of the limiting Sha², every non-zero class in `H²(H, Z/p)` (for `H` closed
isomorphic to the absolute Galois group of a p-adic field) has a non-zero local component at some
place of `K̄` over a finite prime of `K`.

Equivalently: the localisation map `H²(H, Z/p) → ∏_A H²(H ∩ D_A, Z/p)` has trivial kernel, so
that `Z/p ≅ H²(H, Z/p)` injects into the product of the local groups. -/
theorem exists_loc_ne_zero (p : ℕ) (hvan : Sha2Vanishing (K := K) (K' := K') p κ κ')
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (hvan H hH hκ x h)

end NK.BrauerHasse
