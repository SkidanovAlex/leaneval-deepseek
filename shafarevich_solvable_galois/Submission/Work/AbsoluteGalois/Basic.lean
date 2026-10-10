import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Combine
import Submission.EmbeddingProblem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-! ## Instances -/

/-- The algebraic closure of `ℚ` re-registered as an algebraic closure, so that type class search
finds `IsAlgClosure ℚ (AlgebraicClosure ℚ)` (see the header). -/
instance instIsAlgClosureAlgebraicClosureRat : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.instIsAlgClosure ℚ

/-- `Field.absoluteGaloisGroup K` is definitionally equal to
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`, but type class search cannot unfold the `def`, so we
register the `FunLike` instance by hand. -/
instance instFunLikeAbsoluteGaloisGroup (K : Type*) [Field K] :
    FunLike (Field.absoluteGaloisGroup K) (AlgebraicClosure K) (AlgebraicClosure K) where
  coe σ := (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ)
  coe_injective := fun σ τ h => by
    apply AlgEquiv.ext
    intro x
    exact congrFun h x

section Restrict

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

/-- **The restriction of an absolute Galois automorphism.**  If `L ⊆ ℚ̄` is normal over `ℚ`, every
`ℚ`-automorphism of `ℚ̄` maps `L` onto itself, and restricting gives a group homomorphism
`G_ℚ →* Gal(L/ℚ)`; this is Mathlib's `AlgEquiv.restrictNormalHom`. -/
def restrictHom [Normal ℚ L] :
    Field.absoluteGaloisGroup ℚ →* (L ≃ₐ[ℚ] L) :=
  AlgEquiv.restrictNormalHom L

@[simp]
lemma restrictHom_def [Normal ℚ L] :
    restrictHom L = AlgEquiv.restrictNormalHom L := rfl

/-- Restriction of an absolute Galois automorphism to a normal subextension acts as `σ` itself. -/
lemma restrictHom_apply [hL : Normal ℚ L] (σ : Field.absoluteGaloisGroup ℚ) (x : L) :
    ((restrictHom L) σ) x = σ (x : AlgebraicClosure ℚ) :=
  @AlgEquiv.restrictNormalHom_apply ℚ _ (AlgebraicClosure ℚ) _ _ L hL σ x

/-- The kernel of the restriction map is exactly the fixing subgroup of `L`. -/
lemma restrictHom_ker [hL : Normal ℚ L] :
    (restrictHom L).ker = L.fixingSubgroup :=
  @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ L hL

/-- Restriction to a normal subextension is surjective (every automorphism of `L/ℚ` extends to
`ℚ̄`). -/
lemma restrictHom_surjective [hL : Normal ℚ L] :
    Function.Surjective (restrictHom L) :=
  @AlgEquiv.restrictNormalHom_surjective ℚ _ (↥L) _ _ (AlgebraicClosure ℚ) _ _ _ _ hL
    (inferInstance : Normal ℚ (AlgebraicClosure ℚ))

/-- Restriction to a normal subextension is continuous (for the Krull topologies). -/
lemma restrictHom_continuous [hL : Normal ℚ L] : Continuous (restrictHom L) :=
  @InfiniteGalois.restrictNormalHom_continuous ℚ (AlgebraicClosure ℚ) _ _ _ L hL

/-- The kernel of the restriction map is an *open* subgroup as soon as `L/ℚ` is finite. -/
lemma restrictHom_ker_isOpen [FiniteDimensional ℚ L] [hL : Normal ℚ L] :
    IsOpen ((restrictHom L).ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  rw [restrictHom_ker L]
  exact @IntermediateField.fixingSubgroup_isOpen ℚ (AlgebraicClosure ℚ) _ _ _ L ‹_›

/-- The fixed field of the kernel of the restriction map is `L` itself (infinite Galois theory):
restriction to `L` is onto `Gal(L/ℚ)` with kernel exactly the fixing subgroup of `L`. -/
lemma fixedField_ker_restrictHom [FiniteDimensional ℚ L] [hL : Normal ℚ L] :
    IntermediateField.fixedField (restrictHom L).ker = L := by
  rw [restrictHom_ker L]
  exact @InfiniteGalois.fixedField_fixingSubgroup ℚ (AlgebraicClosure ℚ) _ _ _ L
    (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ))

/-- The kernel of the restriction map is a closed subgroup (for each normal `L`). -/
lemma restrictHom_ker_isClosed [hL : Normal ℚ L] :
    IsClosed ((restrictHom L).ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  rw [restrictHom_ker L]
  exact @InfiniteGalois.fixingSubgroup_isClosed ℚ (AlgebraicClosure ℚ) _ _ _ L
    (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ))

/-- The kernel of the restriction map is normal when `L/ℚ` is Galois. -/
lemma restrictHom_ker_normal [hL : IsGalois ℚ L] :
    (restrictHom L).ker.Normal := by
  rw [restrictHom_ker L]
  exact @IsGalois.fixingSubgroup_normal_of_isGalois ℚ (AlgebraicClosure ℚ) _ _ _ L
    (inferInstance : IsGalois ℚ (AlgebraicClosure ℚ)) hL

/-- Compatibility of `restrictHom` with the inclusions of intermediate fields: restricting to the
smaller field or restricting to the larger one and then including gives the same element. -/
lemma restrictHom_inclusion {L M : IntermediateField ℚ (AlgebraicClosure ℚ)} [hL : Normal ℚ L]
    [hM : Normal ℚ M] (h : L ≤ M) (σ : Field.absoluteGaloisGroup ℚ) (x : L) :
    ((restrictHom M) σ ⟨x, h x.2⟩ : AlgebraicClosure ℚ) = ((restrictHom L) σ) x := by
  rw [restrictHom_apply M σ ⟨x, h x.2⟩, restrictHom_apply L σ x]

end Restrict

end

end Work.AbsoluteGalois
