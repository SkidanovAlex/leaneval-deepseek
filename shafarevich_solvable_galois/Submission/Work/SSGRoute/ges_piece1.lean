import Mathlib
import Submission.Work.SSGRoute.ges_escape_aux
import Submission.Work.SSGRoute.finiteIndex_gesU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Piece (1) of the escape-form Grünwald construction, assembled

`U := im(Kˣ · E) ≤ C_K`, where `E = powTIdeles K p T` is the group of idèles that are `p`-th powers
at the finite primes of `T` and local units outside the places above `T`
(`Submission/Work/SSGRoute/ges_escape_aux.lean`).

* `Work.SSGRoute.isOpen_gesU` (aux module) — openness of `U`;
* `Work.SSGRoute.finiteIndex_gesU` (`Submission/Work/SSGRoute/finiteIndex_gesU.lean`) — finite
  index of `U`: `C_K/U` is an extension of the `T`-integer class group
  `Cl(K)/⟨[𝔭] : 𝔭 ∈ T⟩` by a quotient of the finite product `∏_{𝔭∈T} K𝔭ˣ ⧸ (K𝔭ˣ)ᵖ`.

`gesU_open_finiteIndex` is exactly the shape `Work.SSGRoute.CFTSide.classField_exists_of_index`
consumes: it yields the class field `M/K` of `U`, with `N_{M/K} C_M = U = ker (Art_M)`, which is what
the reading-off (step 4 of `NOTE_ges_zmod_escape_route.md` §2) needs.
-/

open scoped NumberField RestrictedProduct

namespace Work.SSGRoute

variable {K : Type*} [Field K] [NumberField K]

/-- **`U = im(Kˣ · E)` is an open subgroup of finite index of the idèle class group.** -/
theorem gesU_open_finiteIndex (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    let U : Subgroup (NK.GlobalCFT.IdeleClassGroup K) :=
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔ powTIdeles K p T).map
        (NK.GlobalCFT.IdeleClassGroup.mk K)
    U.FiniteIndex ∧ IsOpen (U : Set (NK.GlobalCFT.IdeleClassGroup K)) :=
  ⟨finiteIndex_gesU K p T, isOpen_gesU (K := K) (Fact.out) T⟩

end Work.SSGRoute
