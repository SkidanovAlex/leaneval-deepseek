import Mathlib
import Submission.Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp_canonical
import Submission.Work.SSGRoute.ZConstruction.lcHoms_natCard_congr
import Submission.Work.SSGRoute.PTembedding.lcHoms_localUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer count at the level-`K` local group

`|lcHoms p ↥(decomp (k := ↥K) A)| = |κˣ ⧸ (κˣ)^p|`, where `κ = 𝔭.adicCompletion ↥K` is the
completion at the canonical prime `𝔭 = Submission.NeukirchUchida.primeOf A hAK`.

Two steps: `Work.SSGRoute.ZConstruction.natCard_lcHoms_congr` transports the count along the
homeomorphic group isomorphism `decomp (k := ↥K) A ≃* Gal(κ̄/κ)` of
`…localGaloisEquiv_decomp_canonical`, and `Work.SSGRoute.PTembedding.lcHoms_localUnits` -- local
Kummer theory at the completion, resting on the axiom-clean `NK.NUV2.kernelCondition_all` and
`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` -- evaluates it as the `p`-power
class group of `κ`.  The match is by `rfl`, because `localGalOf`/`localFieldOf` are *defined* from
`primeOf A ·`.
-/

namespace Work.SSGRoute.ZConstruction

/-- **The local Kummer count at the level-`K` local group.** -/
theorem natCard_lcHoms_levelK_localGroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (hA' : SSGRoute.IsFinPlace ↥K A) :
    Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))
      = Nat.card (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
          ((powMonoidHom p :
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range)) := by
  classical
  -- `Ω` is an algebraic closure of `↥K`, for the instantiation of the local count at `↥K`
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  obtain ⟨e, he⟩ := localGaloisEquiv_decomp_canonical p k Ω K A hAK
  have hsymm : Continuous
      (e.symm : (SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) ≃ₐ[
          (Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K]
          SeparableClosure ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)) →
        ↥(SSGRoute.decomp (k := ↥K) A)) :=
    e.toEquiv.continuous_symm_iff.2 he.isOpenMap
  rw [natCard_lcHoms_congr p e he.continuous hsymm]
  exact Work.SSGRoute.PTembedding.lcHoms_localUnits p ↥K Ω A hA'

end Work.SSGRoute.ZConstruction
