import Mathlib
import Submission.Work.HilbertSymbolGeneral.Defs
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of the global product formula for the quadratic Hilbert symbol

This module collects the definitions shared by the file `hilbertReciprocityTwo` and the lemmas
delegated for it.  Everything here is a definition; no arithmetic is proved.

For a number field `K`, a finite Galois extension `L / K` and an element `x ∈ Kˣ`, the *bad set* of
`x` is the set of places of `K` at which `x` fails to be a local norm:

  `badSet K L x = {v : Place K | ¬ NK.NUV2.LC.IsLocalNorm K L x v}`;

equivalently (`isLocalNorm_iff_localNormSubgroup`, delegated) the set of places at which the image
of `x` in `K_vˣ` is not in the local norm subgroup `NK.CFTLib.IdeleHasse.localNormSubgroup K L v`.

Hilbert reciprocity for the quadratic pair `(x, L/K)` is the statement that this bad set is finite
of *even* cardinality, i.e. that the product `∏_v (x, L/K)_v` of the local symbols is `1`.

The idèle-theoretic form of the second ingredient is the subgroup

  `localNormIdeles K L = {y : 𝕀 K | ∀ v, y v ∈ localNormSubgroup K L v}`

of idèles that are local norms at every place (the "local norm condition" `𝕀^N`), together with its
image in the idèle class group.  The index input of the proof is that

  `[𝕀 K : localNormIdeles K L ⊔ principalSubgroup K] ∣ [L : K]`

(the norm index theorem `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`), while the arithmetic input
is the "one place omitted" form of Hilbert reciprocity
(`NK.CFTLib.HilbertReciprocityOnePlace`, proved): the bad set is never a singleton.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.HilbertSymbolGeneral

open NK.GlobalCFT

/-- The subgroup of the idèle group consisting of the idèles that are local norms at every place
of `K` (written `𝕀^N` in the classical proof of Hilbert reciprocity). -/
noncomputable def localNormIdeles (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    Subgroup (Idele K) :=
  ⨅ v : Place K,
    (NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v).comap (Idele.eval v)

@[simp] theorem mem_localNormIdeles {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {y : Idele K} :
    y ∈ localNormIdeles K L ↔
      ∀ v : Place K,
        y v ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
  simp [localNormIdeles]

/-- The bad set of `x ∈ Kˣ`: the set of places of `K` at which `x` is not a local norm from `L`.
Hilbert reciprocity says that it is finite of even cardinality. -/
def badSet (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Set (Place K) :=
  {v | ¬ NK.NUV2.LC.IsLocalNorm K L x v}

/-- The bad set in the idèle-theoretic vocabulary: the places at which the image of `x` in `K_vˣ`
is not in the local norm subgroup. -/
def badSetSubgroup (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Set (Place K) :=
  {v | NK.CFTLib.IdeleHasse.localImageAt v x ∉
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v}

end Work.HilbertSymbolGeneral
