/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse norm theorem for cyclic extensions of number fields

This module records, as a `structure` whose fields are `Prop`s (so that every theorem stated from
it is a *proved* conditional theorem, never an axiom), the number-theoretic input that the classical
proof of the Hasse principle / Brauer–Hasse–Noether theorem consumes:

> **Hasse norm theorem.**  For a cyclic extension `L/K` of number fields, an element of `Kˣ` that is
> a norm from every completion `L_w` is a norm from `L`.

together with its equivalent form in terms of the idèle class groups ("the reciprocity isomorphism
for cyclic extensions with its index formula")

> `[C_K : N_{L/K} C_L] = [L : K]`  for cyclic `L/K`.

The two fields are the two classical faces of the same theorem: the index formula is the
reciprocity isomorphism for cyclic extensions (cf. `NK.GlobalCFT.FieldAxiom`, which states it for
abelian extensions and which is *derived* on disk from the cohomological field axiom and the
`H⁰`-computation), and the local-global form is the Hasse norm theorem proper.  The classical
proof of `index_eq` for cyclic `L/K` uses the two inequalities of class field theory (the first of
which is proved unconditionally on disk as
`NK.GlobalCFT.first_inequality_of_herbrandQuotient`, and the second of which is the field axiom
`H¹(Gal(L/K), C_L) = 0`), while `hasse_norm` is obtained from the index formula together with the
reciprocity isomorphisms at the completions.

See `Submission/Work/HassePrinciple/README.md` for how this input is consumed and what would
discharge it.
-/

import Submission.NK.GlobalCFT.GlobalCFT

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The Hasse norm theorem for cyclic extensions of number fields**, in its two classical forms:

* `index_eq` — the reciprocity isomorphism for a cyclic extension `L/K` in index form,
  `[C_K : N_{L/K} C_L] = [L : K]`;
* `hasse_norm` — the Hasse norm theorem: an element of `Kˣ` whose principal idèle is a norm from
  the idèles of `L` (equivalently: which is a local norm at every place) is the norm of an element
  of `Lˣ`, i.e. `Kˣ ∩ N_{L/K} 𝕀_L = N_{L/K} Lˣ`. -/
structure HasseNormTheorem : Prop where
  /-- **The reciprocity isomorphism for cyclic extensions, in index form.** -/
  index_eq : ∀ {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      IsCyclic (L ≃ₐ[K] L) →
        (Idele.normClassSubgroup K L).index = Module.finrank K L
  /-- **The Hasse norm theorem.** -/
  hasse_norm : ∀ {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      IsCyclic (L ≃ₐ[K] L) → ∀ a : Kˣ,
        Idele.principalIdele K a ∈ Idele.normImage K L →
          ∃ b : Lˣ, Idele.principalIdele K a =
            Idele.normIdeleFun K L (Idele.principalIdele L b)


/-- **The Hasse norm theorem implies the field axiom for cyclic extensions.**  The norm index
formula of `HasseNormTheorem` together with the positivity of `[L : K]` gives the field axiom
`NK.GlobalCFT.FieldAxiom K L` of the on-disk class formation for every cyclic extension `L/K`:
the norm subgroup has finite index and its index is `[L : K]`. -/
theorem fieldAxiom_of_hasseNormTheorem (h : HasseNormTheorem.{u}) {K L : Type u} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, h.index_eq hcyc]
    exact (Module.finrank_pos).ne'
  index_eq := h.index_eq hcyc

end NK.HassePrinciple
