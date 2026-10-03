import Mathlib
import Submission.Work.ORReductions.Basic

/-!
# Vocabulary for the reduction of coherence of `K[G]` to finitely generated subfields

If `L` is a subfield of a field `K` and `G` is a group, then `K[G]` is naturally a (left)
module over `L[G]` by left multiplication.  The key structural fact, proved in
`Work.ORReductions.Coherent.exists_basis_single`, is that `K[G]` is *free* over `L[G]` with
basis the elements `single 1 (b j)`, where `b` is a basis of `K` over `L`; these basis
elements are central in `K[G]`.

This module only contains definitions (and their unfolding lemmas), so that it can be imported
both by `coherent_of_subfield.lean` and by the auxiliary modules proving the lemmas there.
-/

namespace Work.ORReductions.Coherent

/-- The ring hom `L[G] →+* K[G]` induced by the inclusion of a subfield `L ≤ K`. -/
noncomputable abbrev subfieldAlgHom (K : Type*) [Field K] (L : Subfield K) (G : Type*) [Group G] :
    MonoidAlgebra (↥L) G →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapRingHom G (algebraMap ↥L K)

/-- Unfolding lemma for `subfieldAlgHom`. -/
theorem subfieldAlgHom_apply (K : Type*) [Field K] (L : Subfield K) (G : Type*) [Group G]
    (r : MonoidAlgebra (↥L) G) :
    subfieldAlgHom K L G r = MonoidAlgebra.mapRingHom G (algebraMap ↥L K) r := rfl

/-- The element `single 1 (b j)` of `K[G]`, for `b` a basis of `K` over `L`. -/
noncomputable abbrev basisElem (K : Type*) [Field K] (L : Subfield K) (G : Type*) [Group G]
    {ι : Type*} (b : Module.Basis ι ↥L K) (j : ι) : MonoidAlgebra K G :=
  MonoidAlgebra.single (1 : G) (b j)

/-- Unfolding lemma for `basisElem`. -/
theorem basisElem_apply (K : Type*) [Field K] (L : Subfield K) (G : Type*) [Group G]
    {ι : Type*} (b : Module.Basis ι ↥L K) (j : ι) :
    basisElem K L G b j = MonoidAlgebra.single (1 : G) (b j) := rfl

/-- `K[G]` is a left module over `L[G]`, with the action given by left multiplication
through `subfieldAlgHom`. -/
noncomputable instance instModuleMonoidAlgebraSubfield (K : Type*) [Field K] (L : Subfield K)
    (G : Type*) [Group G] : Module (MonoidAlgebra (↥L) G) (MonoidAlgebra K G) :=
  (subfieldAlgHom K L G).toModule

@[simp]
theorem subfieldAlgHom_smul (K : Type*) [Field K] (L : Subfield K) (G : Type*) [Group G]
    (r : MonoidAlgebra (↥L) G) (x : MonoidAlgebra K G) :
    r • x = subfieldAlgHom K L G r * x :=
  RingHom.toModule_smul _ r x

end Work.ORReductions.Coherent
