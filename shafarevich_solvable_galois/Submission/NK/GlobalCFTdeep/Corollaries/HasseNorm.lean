/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.CoCore.Reciprocity
import Submission.NK.HassePrinciple.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hasse norm theorem

`NK.HassePrinciple.HasseNormTheorem` is the licensed arithmetic input of the Neukirch–Uchida
development: the structure with the two classical forms of Hasse's norm theorem,

* `index_eq`: the reciprocity isomorphism for cyclic `L/K` in index form,
  `[C_K : N_{L/K}C_L] = [L : K]`;
* `hasse_norm`: the local-global principle for norms, `Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`.

This file **proves the first of the two forms** from the chapter's class-formation ladder, and
provides the second from the licensed input `HasseNormPrinciple` (the local-global principle
itself).  Concretely:

* `index_eq` is the index computation of the two inequalities
  (`index_eq_finrank_of_cyclicHerbrandQuotient`): for cyclic `L/K` it uses the universal
  Herbrand-quotient input (Milne, *CFT*, Theorem 4.3), the second inequality
  (`SecondInequality`) and the unconditional `H⁰`-computation
  (`NK.GlobalCFT.globalCFT_H0Computation`).  **No reciprocity is used**, which is why the
  statement is not circular.
* `hasse_norm` is the local-global principle for norms, i.e. Hasse's theorem proper; its classical
  proof goes through the reciprocity isomorphism (available here as
  `galoisReciprocity_of_cohomologicalFieldAxiom`), the product formula for the global Artin symbol
  (a product of local symbols), and local class field theory (`Submission/Work/LocalCFT/`,
  `Submission/Work/LocalArtin/`) — in particular the equivalence "`a` is a local norm at `v` iff
  the local Artin symbol of `a` is trivial".  It is the licensed input of the development and is
  recorded here as `HasseNormPrinciple`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

universe u

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Hasse's norm theorem**, the local-global principle for norms: for a cyclic extension `L/K` of
number fields, an element of `Kˣ` that is a norm from every completion `L_w` is a norm from `L`
(equivalently, `Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`).

This is the licensed arithmetic input; see the module docstring for the classical proof route. -/
structure HasseNormPrinciple : Prop where
  /-- the local-global principle for norms. -/
  hasse_norm : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L], IsCyclic (L ≃ₐ[K] L) → ∀ a : Kˣ,
      Idele.principalIdele K a ∈ Idele.normImage K L →
        ∃ b : Lˣ, Idele.principalIdele K a = Idele.normIdeleFun K L (Idele.principalIdele L b)

/-- **The Hasse norm theorem** (`NK.HassePrinciple.HasseNormTheorem`) from the chapter's inputs:
the index form is *proved* (from the universal Herbrand-quotient input, the second inequality and
the unconditional `H⁰`-computation), the local-global form is the licensed input
`HasseNormPrinciple`. -/
theorem hasseNormTheorem_of_inputs (hH : CyclicHerbrandQuotient) (h2 : SecondInequality)
    (h : HasseNormPrinciple) : NK.HassePrinciple.HasseNormTheorem.{0} where
  index_eq := by
    intro K L _ _ _ _ _ _ _ hcyc
    haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm fun a b => mul_comm a b
    exact index_eq_finrank_of_secondInequality (herbrandQuotient_of_cyclicHerbrandQuotient hH) h2
  hasse_norm := by
    intro K L _ _ _ _ _ _ _ hcyc a ha
    exact h.hasse_norm hcyc a ha

/-- The index form alone, in the shape in which the consumers of `HasseNormTheorem` use it. -/
theorem index_eq_of_hasseNormInputs (hH : CyclicHerbrandQuotient) (h2 : SecondInequality)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    (Idele.normClassSubgroup K L).index = Module.finrank K L :=
  index_eq_finrank_of_cyclicHerbrandQuotient hH h2

end NK.GlobalCFTdeep
