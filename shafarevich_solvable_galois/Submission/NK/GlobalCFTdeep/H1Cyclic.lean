/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFTdeep.CoCore.H1
import Submission.NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(L/K), C_L) = 0` for cyclic `L/K`, unconditionally

Milne's Lemma 5.2 for a cyclic Galois group `G` says that the index formula
`[C_K : N_{L/K}C_L] = [L:K]`, the vanishing of `H¹(G, C_L)` and the vanishing of the negative Tate
cohomology `Ĥ⁻¹(G, C_L) = ker(N)/I·C_L` are all equivalent.  The index formula is now
unconditional for cyclic extensions (`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, from the
Kummer-theoretic second inequality for cyclic extensions of prime degree, the tower inequality and
the unconditional first inequality), so both cohomological statements follow without further input
(the first one being `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_of_index_eq`, already on
disk; the second one is Tate periodicity in degree `-1`).

## Main results

* `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_of_isCyclic` — `H¹(G, C_L) = 0` for cyclic
  `L/K`;
* `NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_isCyclic` — `Ĥ⁻¹(G,C_L) = 0` for
  cyclic `L/K`.
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

/-- **`H¹(Gal(L/K), C_L) = 0` for a cyclic extension** `L/K` of number fields, unconditionally:
the index formula `[C_K : N_{L/K}C_L] = [L:K]` (which no longer needs any input, see
`index_eq_finrank_of_isCyclic`) and the Herbrand-quotient computation force `|Ĥ¹| = 1`. -/
theorem subsingleton_groupCohomology_one_of_isCyclic {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) :=
  subsingleton_groupCohomology_one_of_index_eq
    (cyclicHerbrandQuotient.herbrand (K := K) (L := L))
    (index_eq_finrank_of_isCyclic (K := K) (L := L))

/-- **`Ĥ⁻¹(Gal(L/K), C_L) = 0` for a cyclic extension** `L/K` of number fields, unconditionally:
Tate periodicity in degree `-1` (`ℤ[G]`-modules for cyclic `G` satisfy `Ĥ⁻¹ ≅ H¹`). -/
theorem subsingleton_tateCohomology_neg_one_of_isCyclic {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Subsingleton (tateCohomology (IdeleClassGroup.rep K L) (-1)) :=
  subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic
    (IdeleClassGroup.rep K L) subsingleton_groupCohomology_one_of_isCyclic

end NK.GlobalCFTdeep
