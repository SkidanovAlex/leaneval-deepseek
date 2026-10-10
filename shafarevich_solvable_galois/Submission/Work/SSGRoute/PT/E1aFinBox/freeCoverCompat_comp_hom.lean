import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_comp
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_single
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Functoriality of the comparison map of the canonical covers in the group homomorphism

`Work.SSGRoute.PT.freeCoverCompat φ X` (`PT/freeCoverCompat.lean`) is the canonical comparison
between the two canonical covers of `X`: the cover over `H` of the restricted module `Rep.res φ X`
and the restriction of the cover over `G`, `Rep.res φ (Rep.free Coeff G X.V)`.  It is the identity
on the generators, and it is compatible with the two covers (`freeCoverCompat_comp`).

This file records its compatibility with the *composition* of group homomorphisms: for
`ψ : H₂ →* H` and `φ : H →* G`,

    freeCoverCompat (φ.comp ψ) X
      = freeCoverCompat ψ (Rep.res φ X) ≫ (Rep.resFunctor ψ).map (freeCoverCompat φ X).

Both sides are morphisms out of the free representation on the underlying set of `X`, and both fix
the generators: `freeCoverCompat_single` gives the value of each comparison map on a generator, and
the restriction functor does not change the underlying map of a morphism (`Rep.resMap_hom_apply`).
Hence `Rep.free_ext` reduces the identity to the generators, where it is a computation.

This is the functoriality of the comparison of the two canonical presentations that the
"level-box" bookkeeping of piece (i) needs: iterated restriction of the canonical cover can be
compared to the canonical cover of the twice-restricted module either in one step (the left side)
or in two (the right side).
-/

namespace Work.SSGRoute.PT.E1aFinBox

open CategoryTheory

theorem freeCoverCompat_comp_hom {G H H₂ : Type} [Group G] [Group H] [Group H₂]
    (φ : H →* G) (ψ : H₂ →* H) (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Work.SSGRoute.PT.freeCoverCompat (φ.comp ψ) X =
      CategoryTheory.CategoryStruct.comp (Work.SSGRoute.PT.freeCoverCompat ψ (Rep.res φ X))
        ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) ψ).map
          (Work.SSGRoute.PT.freeCoverCompat φ X)) := by
  -- both sides are morphisms out of the free representation on the generators
  refine Rep.free_ext SSGRoute.PTExt.Coeff H₂
    (A := Rep.res (φ.comp ψ) (Rep.free SSGRoute.PTExt.Coeff G ↑X)) _ _ ?_
  intro x
  -- the composite acts as `g ∘ f` on the underlying elements
  rw [Rep.comp_apply]
  -- the comparison map for the composite homomorphism fixes the generators
  rw [Work.SSGRoute.E1cGeneric.freeCoverCompat_single (φ.comp ψ) X x]
  -- rewrite the two `ConcreteCategory.hom`s of the right-hand side as `Rep.Hom.hom`
  show Finsupp.single x (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff)) =
    Rep.Hom.hom (Rep.resMap ψ (Work.SSGRoute.PT.freeCoverCompat φ X))
      (Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat ψ (Rep.res φ X))
        (Finsupp.single x (MonoidAlgebra.single (1 : H₂) (1 : SSGRoute.PTExt.Coeff))))
  -- the restriction functor does not change the underlying map
  rw [Rep.resMap_hom_apply]
  -- and both comparison maps fix the generators
  rw [Work.SSGRoute.E1cGeneric.freeCoverCompat_single ψ (Rep.res φ X) x]
  rw [Work.SSGRoute.E1cGeneric.freeCoverCompat_single φ X x]

end Work.SSGRoute.PT.E1aFinBox
