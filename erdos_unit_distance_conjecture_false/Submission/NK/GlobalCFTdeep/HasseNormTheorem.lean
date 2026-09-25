/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.H1Cyclic
import Submission.NK.GlobalCFTdeep.hasseNorm_of_subsingleton_tateCohomology_neg_one
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.HBNUnits_from_cyclic
import Submission.NK.GlobalCFTdeep.Corollaries.HasseNorm
import Submission.NK.GlobalCFTdeep.Corollaries.Unconditional

/-!
# Hasse's norm theorem for cyclic extensions, unconditionally

`NK.HassePrinciple.HasseNormTheorem` is the structure with the two classical faces of Hasse's
norm theorem for a cyclic extension `L/K` of number fields:

* `index_eq` — the index form `[C_K : N_{L/K}C_L] = [L:K]` (the reciprocity isomorphism);
* `hasse_norm` — the local–global principle for norms, `Kˣ ∩ N_{L/K}𝕀_L = N_{L/K}Lˣ`.

Both are now **theorems** of this chapter:

* `index_eq` is `index_eq_finrank_of_isCyclic` (first inequality, unconditional for cyclic `L/K`
  from Milne's Theorem 4.3, plus the second inequality from the Kummer-theoretic cyclic
  prime-degree case and the tower inequality);
* `hasse_norm` follows from the vanishing of `Ĥ⁻¹(G, C_L)` for cyclic `G`
  (`subsingleton_tateCohomology_neg_one_of_isCyclic`, i.e. Tate periodicity in degree `−1` plus the
  index formula) by
  `hasseNorm_of_subsingleton_tateCohomology_neg_one` (the six-term Tate cohomology sequence of
  `1 → Lˣ → 𝕀_L → C_L → 1`: `ker(α) = im(Ĥ⁻¹(G,C_L) → Ĥ⁰(G,Lˣ)) = 0`).

Consequently the whole downstream chain of the `HassePrinciple` chapter becomes unconditional:

* `NK.HassePrinciple.CyclicHasseInput` (`cyclicHasseInput`), hence
  `NK.HassePrinciple.hbnUnits_from_cyclicInput` — the relative **Hasse–Brauer–Noether theorem**
  (`hbnUnits`);
* and this chapter's own licensed input `NK.GlobalCFTdeep.HasseNormPrinciple` is discharged
  (`hasseNormPrinciple`), so the analytic-route theorems of `Corollaries/Unconditional.lean` and
  `SecondInequality/Corollaries.lean` lose that hypothesis.

## Main results

* `NK.GlobalCFTdeep.hasseNormTheorem : NK.HassePrinciple.HasseNormTheorem.{0}`;
* `NK.GlobalCFTdeep.hasseNormPrinciple : NK.GlobalCFTdeep.HasseNormPrinciple`;
* `NK.GlobalCFTdeep.cyclicHasseInput : NK.HassePrinciple.CyclicHasseInput`;
* `NK.GlobalCFTdeep.hbnUnits : NK.HassePrinciple.HBNUnits F E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Hasse's norm theorem for cyclic extensions of number fields**, in its two classical forms,
proved unconditionally (Milne, *CFT*, Lemma 5.2 together with the index computation). -/
theorem hasseNormTheorem : NK.HassePrinciple.HasseNormTheorem.{0} where
  index_eq := by
    intro K L _ _ _ _ _ _ _ hcyc
    exact index_eq_finrank_of_isCyclic (K := K) (L := L)
  hasse_norm := by
    intro K L _ _ _ _ _ _ _ hcyc a ha
    exact hasseNorm_of_subsingleton_tateCohomology_neg_one
      (subsingleton_tateCohomology_neg_one_of_isCyclic (K := K) (L := L)) a ha

/-- **The licensed local–global principle for norms is discharged**: this chapter's input
`NK.GlobalCFTdeep.HasseNormPrinciple` (Hasse's norm theorem proper) is now a theorem. -/
theorem hasseNormPrinciple : HasseNormPrinciple where
  hasse_norm := fun {_ _} _ _ _ _ _ _ _ hcyc a ha => hasseNormTheorem.hasse_norm hcyc a ha

/-- **The licensed cyclic input of the `HassePrinciple` chapter, unconditionally**: the Hasse norm
theorem and the Herbrand quotient of `C_L` for cyclic `L/K`. -/
theorem cyclicHasseInput : NK.HassePrinciple.CyclicHasseInput where
  hasse_norm := hasseNormTheorem
  herbrand := fun {_ _} _ _ _ _ _ _ _ _ => cyclicHerbrandQuotient.herbrand

/-- **The relative Hasse–Brauer–Noether theorem at every finite Galois extension of number
fields** (Milne, *CFT*, VII.7.1), unconditionally: the complex `HBNUnits F E` is acyclic. -/
theorem hbnUnits {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] : NK.HassePrinciple.HBNUnits F E :=
  NK.HassePrinciple.hbnUnits_from_cyclicInput cyclicHasseInput

/-- **`H¹` of the idèle class group, re-derived through the HassePrinciple chapter**: the same
statement as `subsingleton_groupCohomology_one_ideleClassGroup`, obtained from the (now
unconditional) cyclic input. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup' {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) :=
  NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all cyclicHasseInput

end NK.GlobalCFTdeep
