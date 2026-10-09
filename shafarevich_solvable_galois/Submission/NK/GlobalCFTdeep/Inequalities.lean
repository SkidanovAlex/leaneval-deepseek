/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two inequalities of global class field theory

The delivered chapter `Submission/Work/GlobalCFT/` proves the **first** inequality
`[C_K : N_{L/K} C_L] ≥ [L : K]` from the Herbrand-quotient computation `h(G, C_L) = [L : K]`
(`NK.GlobalCFT.first_inequality_of_herbrandQuotient`) and the `H⁰`-computation
(`NK.GlobalCFT.globalCFT_H0Computation : H0Computation K L`, unconditional).

This file adds the **second** inequality `[C_K : N_{L/K} C_L] ≤ [L : K]` as the chapter's first
named classical input, and proves the ladder

* `TwoInequalities K L` (`NK.GlobalCFT.TwoInequalities`);
* `FieldAxiom K L` (`NK.GlobalCFT.FieldAxiom`);
* `[C_K : N_{L/K} C_L] = [L : K]`,

for every finite **abelian** extension `L / K`, from `SecondInequality` and the Herbrand-quotient
computation.  The index form `[C_K : N_{L/K}C_L] = [L : K]` for cyclic `L/K` is exactly the first
field of `NK.HassePrinciple.HasseNormTheorem` (see `Corollaries/HasseNorm.lean`).

## The named input

`SecondInequality` is the second inequality of class field theory, a specific classical theorem:

* Milne, *Class Field Theory*, Theorem 5.1(a), proved analytically in Chapter VI, Theorem 4.9
  (the Dedekind zeta function `ζ_L(s)/ζ_K(s)` extends holomorphically to `s = 1`);
* equivalently the *analytic* form "the `L`-series of a non-trivial character of the ray class
  group is holomorphic at `s = 1`" (see `Submission/Work/HeckeL/`, which formalises the analysis);
* or algebraically, by Kummer theory and the first inequality (Milne, *CFT*, Chapter VII §6;
  Lang, *Algebraic Number Theory*, Chapter VI).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **The second inequality of global class field theory** (Takagi), in the index form
`[C_K : N_{L/K} C_L] ≤ [L : K]` for every finite Galois extension of number fields.

This is a specific classical theorem; see the module docstring for references to the two standard
proofs.  It is *strictly weaker* than the class-formation axioms
(`NK.GlobalCFT.CohomologicalFieldAxiom`): it contains no cohomological statement. -/
structure SecondInequality : Prop where
  /-- the second inequality: `[C_K : N_{L/K} C_L] ≤ [L : K]`. -/
  index_le : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    (Idele.normClassSubgroup K L).index ≤ Module.finrank K L

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The index of the norm subgroup is the degree** (abelian case), from the two inequalities:
the first inequality is the delivered `NK.GlobalCFT.first_inequality_of_herbrandQuotient`
(which uses the unconditional `H⁰`-computation and the Herbrand-quotient computation
`h(G, C_L) = [L : K]`), the second is the input `SecondInequality`. -/
theorem index_eq_finrank_of_secondInequality [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  le_antisymm (h2.index_le)
    (first_inequality_of_herbrandQuotient (globalCFT_H0Computation (K := K) (L := L)) hh)

/-- The two inequalities, from the second inequality and the Herbrand-quotient computation. -/
theorem twoInequalities_of_secondInequality [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    TwoInequalities K L where
  first := first_inequality_of_herbrandQuotient (globalCFT_H0Computation (K := K) (L := L)) hh
  second := h2.index_le

/-- **The field axiom of the class formation** for an abelian extension, from the second
inequality and the Herbrand-quotient computation (no reciprocity, no fundamental class). -/
theorem fieldAxiom_of_secondInequality [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    FieldAxiom K L where
  finiteIndex := by
    rw [Subgroup.finiteIndex_iff, index_eq_finrank_of_secondInequality hh h2]
    exact (Module.finrank_pos).ne'
  index_eq := index_eq_finrank_of_secondInequality hh h2


/-! ## The Herbrand-quotient computation as a universal statement -/

/-- **The Herbrand-quotient computation for cyclic extensions** (Milne, *Class Field Theory*,
Theorem 4.3): for every finite cyclic extension `L/K` of number fields,
`h(Gal(L/K), C_L) = |Ĥ⁰(Gal(L/K), C_L)| / |Ĥ¹(Gal(L/K), C_L)| = [L : K]`.

This is the universal form of the input `NK.GlobalCFT.HerbrandQuotient K L`, which the delivered
chapter states at a fixed extension.  The *proof* of Milne's theorem (which is where the local
Herbrand quotients, the `S`-units and Dirichlet's unit theorem enter) is organised in the
`NK.GlobalCFTdeep.Herbrand` files; here it is the chapter's Herbrand input. -/
structure CyclicHerbrandQuotient : Prop where
  /-- `h(Gal(L/K), C_L) = [L : K]` for every finite cyclic `L/K`. -/
  herbrand : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], HerbrandQuotient K L

/-- The universal Herbrand input specialises to a fixed cyclic extension. -/
theorem herbrandQuotient_of_cyclicHerbrandQuotient (h : CyclicHerbrandQuotient)
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    HerbrandQuotient K L :=
  h.herbrand

/-- **The index of the norm subgroup is the degree** for a cyclic extension, from the universal
Herbrand input and the second inequality. -/
theorem index_eq_finrank_of_cyclicHerbrandQuotient (hH : CyclicHerbrandQuotient)
    (h2 : SecondInequality) [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  index_eq_finrank_of_secondInequality (herbrandQuotient_of_cyclicHerbrandQuotient hH) h2

/-- **The field axiom for a cyclic extension**, from the universal Herbrand input and the second
inequality. -/
theorem fieldAxiom_of_cyclicHerbrandQuotient (hH : CyclicHerbrandQuotient)
    (h2 : SecondInequality) [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    FieldAxiom K L :=
  fieldAxiom_of_secondInequality (herbrandQuotient_of_cyclicHerbrandQuotient hH) h2

end NK.GlobalCFTdeep
