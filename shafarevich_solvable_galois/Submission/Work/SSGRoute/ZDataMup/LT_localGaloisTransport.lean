import Mathlib
import Submission.Work.SSGRoute.lcHoms_congr
import Submission.Work.SSGRoute.LT_LocalCFTUmbrella
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the level-`K` local characters along the local Galois identification

The level-`K` local `H¹`-group at a finite place `A` of `Ω` over `k` is
`V_A = H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)`, and the local Kummer dictionary
`mupKummerDictionary` describes it through the locally constant characters of the level-`K` local
group `↥(decomp (k := ↥K) A)`.  The local arithmetic (the local Artin map, the maximal abelian
extension of the completion) lives instead on `Gal(κ̄_A/κ_A)`, attached to `A` by the canonical
homeomorphism `mupLocalGalEquiv` of `mupLocalVocab`.

This file provides the transport of the characters along that homeomorphism: since a homeomorphism
is continuous with continuous inverse (i.e. open), the subgroup of locally constant characters is
carried isomorphically (`lcHoms_congr`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

/-- **Transport of the level-`K` local characters to the completion.**  The locally constant
characters of the level-`K` local group `↥(decomp (k := ↥K) A)` are the locally constant characters
of the absolute Galois group of the completion `κ_A`. -/
theorem LT_lcHoms_levelK_localGalois
    {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    {A : ValuationSubring Ω} (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Nonempty
      (↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)) ≃*
        ↥(Work.SSGRoute.lcHoms p
          ((SeparableClosure (mupCompletion (K := K) A hAK)) ≃ₐ[mupCompletion (K := K) A hAK]
            (SeparableClosure (mupCompletion (K := K) A hAK))))) :=
  _root_.Work.SSGRoute.lcHoms_congr (mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K) A hAK)
    (isHomeomorph_mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K) A hAK).continuous
    (isHomeomorph_mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K) A hAK).isOpenMap

end Work.SSGRoute.ZDataMup
