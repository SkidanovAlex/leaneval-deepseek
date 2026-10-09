import Submission.NK.LocalReciprocityLubinTate.Unramified.NormInKernel_isCyclic
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicResidual
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `NormInKernel` for the canonical tower, from cyclicity of the level Galois groups

The `𝔭.adicCompletion K` form of `NK.LocalReciprocityLubinTate.normInKernel_of_isCyclic`: if every
level `E_{m,n}` of the canonical Lubin–Tate symbol tower of
`NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ` has cyclic Galois group, then the canonical
symbol kills norms — i.e. `NK.LocalReciprocityLubinTate.NormInKernel` holds for that tower, which is
one of the two hypotheses of the boundary theorem
`NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover`.

The norm index theorem is not a hypothesis here: it is
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`.

## Main result

* `NK.LocalReciprocityLubinTate.NormInKernel.of_isCyclic_adicCompletion`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u

/-- **`NormInKernel` for the canonical tower, whenever the level Galois groups are cyclic.** -/
theorem NormInKernel.of_isCyclic_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (hcyc : ∀ m n, IsCyclic (↥((NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ).level m n) ≃ₐ[
      Q.adicCompletion K] ↥((NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ).level m n))) :
    NormInKernel (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)) π
      (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.adicSymbolTower K Q hπ) :=
  normInKernel_of_isCyclic _ (NormIndex.normIndex_adicCompletion Q) hcyc

end NK.LocalReciprocityLubinTate
