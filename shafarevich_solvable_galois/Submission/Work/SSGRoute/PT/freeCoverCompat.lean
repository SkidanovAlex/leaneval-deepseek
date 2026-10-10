import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.ExtChain.FreeCover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (i) `PhiE`-compat: the canonical comparison of the two canonical covers

For a group homomorphism `φ : H →* G` and `X : Rep Coeff G`, the canonical cover of `X` over `G`,
`freeCover X : Rep.free Coeff G X.V ⟶ X`, restricts to a cover of `Rep.res φ X`, but its middle term
`Rep.res φ (Rep.free Coeff G X.V)` is **not** the canonical cover
`Rep.free Coeff H X.V` of the restricted module (measured: `Rep.res φ (Rep.free k G α)` is
`Rep.free k H α` tensored with `[G : φ H]` copies, so the two are different free modules —
`PT/NOTE_e1aChainC_localComparison.md` §11.3).  The two *presentations* of `Rep.res φ X` are related
by the canonical map of complexes which is the identity on the generators:

    freeCoverCompat φ X : Rep.free Coeff H X.V ⟶ Rep.res φ (Rep.free Coeff G X.V),
    single x (single 1 1) ↦ single x (single 1 1)      (`freeCoverCompat_single`),

whose compatibility with the two covers is `freeCoverCompat_comp`:

    freeCoverCompat φ X ≫ (Rep.resFunctor φ).map (freeCover X) = freeCover (Rep.res φ X).

This is the first artifact of piece (i) of the comparison square: with it, the connecting classes
`PhiE` of the two presentations (`ExtChain.freeCoverSES X` and the restriction of it, on the one
hand, and `freeCoverSES (Rep.res φ X)` on the other) can be compared, which is what
`bijective_extClass_precomp_map` (`ExtChain/ext_shift_natural_res.lean`, proved) reduces the
`h1Transfer`-step to.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **The canonical comparison of the two canonical covers** of `X` along `φ : H →* G`: the
canonical cover of the restricted module maps onto the restriction of the canonical cover, fixing
the generators. -/
noncomputable def freeCoverCompat {G H : Type} [Group G] [Group H] (φ : H →* G)
    (X : Rep.{0} Coeff G) :
    Rep.free Coeff H X.V ⟶ Rep.res φ (Rep.free Coeff G X.V) :=
  Rep.freeLift (k := Coeff) (G := H) (α := X.V)
    (A := Rep.res φ (Rep.free Coeff G X.V))
    (fun x : X.V => Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : Coeff)))

/-- The comparison map is the identity on the generators. -/
theorem freeCoverCompat_single {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] (φ : H →* G)
    (X : Rep.{0} Coeff G) (x : X.V) :
    (freeCoverCompat φ X).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : Coeff)))
      = Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : Coeff)) := by
  show (Rep.freeLift (k := Coeff) (G := H) (α := X.V)
      (A := Rep.res φ (Rep.free Coeff G X.V))
      (fun y : X.V => Finsupp.single y (MonoidAlgebra.single (1 : G) (1 : Coeff))))
      (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : Coeff)))
    = Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : Coeff))
  exact Work.SSGRoute.rep_freeLift_apply_single (G := H)
    (Rep.res φ (Rep.free Coeff G X.V)) X.V
    (fun y : X.V => Finsupp.single y (MonoidAlgebra.single (1 : G) (1 : Coeff))) x

/-- The comparison map of covers is compatible with the two canonical covers. -/
theorem freeCoverCompat_comp {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] (φ : H →* G)
    (X : Rep.{0} Coeff G) :
    freeCoverCompat φ X ≫ (Rep.resFunctor φ).map (Work.SSGRoute.freeCover X)
      = Work.SSGRoute.freeCover (Rep.res φ X) := by
  apply Rep.free_ext
  intro x
  change ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X)).hom
      ((freeCoverCompat φ X).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : Coeff))))
    = (Work.SSGRoute.freeCover (Rep.res φ X)).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : Coeff)))
  rw [freeCoverCompat_single φ X x]
  rw [show ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X)).hom
      (Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : Coeff))) = x from
    Work.SSGRoute.rep_freeLift_apply_single (G := G) X X.V (id : X.V → X.V) x]
  exact (Work.SSGRoute.rep_freeLift_apply_single (G := H) (Rep.res φ X) X.V
    (id : X.V → X.V) x).symm

/-- **The comparison map of the two canonical covers, packaged**: it is the identity on the
generators and it is compatible with the two canonical covers. -/
theorem freeCoverCompat_spec {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] (φ : H →* G)
    (X : Rep.{0} Coeff G) :
    (∀ x : X.V, (freeCoverCompat φ X).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : H) (1 : Coeff)))
      = Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : Coeff)))
    ∧ CategoryTheory.CategoryStruct.comp (freeCoverCompat φ X)
        ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
      = Work.SSGRoute.freeCover (Rep.res φ X) :=
  ⟨fun x => freeCoverCompat_single φ X x, freeCoverCompat_comp φ X⟩

end Work.SSGRoute.PT
