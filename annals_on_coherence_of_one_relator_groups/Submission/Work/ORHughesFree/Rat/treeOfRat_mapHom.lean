/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The complexity `Tree` is preserved by `RatU.mapHom`

The functor `RatU.mapHom f : Rat(N) →+* Rat(N')` of `Rat/MapHom.lean` induced by an *arbitrary*
group homomorphism `f : N →* N'` preserves the complexity `Tree` of [JZLA20, §4.2]:

`treeOfRat N' (mapHom f x) = treeOfRat N x`.

This is the common generalization of `Rat.treeOfRat_ofSubgroup` (the case `f = V.subtype`, via
`RatU.ofSubgroup_eq_mapHom`) and of `Rat.treeOfRat_transport` (the case of an isomorphism, via
`Rat.transport_eq_mapHom`).  The proof is the same as for `treeOfRat_transport`: the composite
`Tree_{N'} ∘ mapHom f : Rat(N) → T` is a morphism of rational `N`-semirings from `Rat(N)` to the
trees, because

* `mapHom f` is a morphism over the pulled back structure `Rat.comapHom f` on `Rat(N')`, whose
  rational operation is that of `Rat(N')` and whose `N`-action is the `N'`-action along `f`;
* `Tree_{N'} = RatU.lift Tree (treeRational N')` is a morphism of rational `N'`-semirings, hence
  also of rational `N`-semirings for the pullback along `f`;
* the structure `treeRational N` on the trees has the *trivial* `N`-action ([JZLA20, §4.1]), so it
  is the pullback of `treeRational N'` along `f`.

By the universal property of `Rat(N)` (`RatU.lift_unique`) this composite must be the universal
morphism `RatU.lift Tree (treeRational N) = treeOfRat N`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.MapHom

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

/-- **The complexity `Tree` is preserved by `RatU.mapHom`**: for every group homomorphism
`f : N →* N'` and every `x : Rat(N)`, the complexity of the image of `x` in `Rat(N')` equals the
complexity of `x`. -/
theorem treeOfRat_mapHom {N N' : Type} [Group N] [Group N'] (f : N →* N')
    (x : Work.ORHughesFree.RatU N) :
    Work.ORHughesFree.Rat.treeOfRat N' (Work.ORHughesFree.RatU.mapHom f x)
      = Work.ORHughesFree.Rat.treeOfRat N x := by
  have hTree : IsRationalUSemiringHom (RatU.rational (U := N)) (treeRational (U := N))
      ((RatU.lift Tree (treeRational (U := N'))).comp (RatU.mapHom f)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      show RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f ((RatU.rational (U := N)).ratOp y)) =
        (treeRational (U := N)).ratOp (RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f y))
      rw [(RatU.mapHom_isHom f).map_rat y]
      exact (RatU.lift_isHom Tree (treeRational (U := N'))).map_rat (RatU.mapHom f y)
    · intro u y
      show RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f ((RatU.rational (U := N)).smul u y)) =
        (treeRational (U := N)).smul u (RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f y))
      rw [(RatU.mapHom_isHom f).map_smul u y]
      exact (RatU.lift_isHom Tree (treeRational (U := N'))).map_smul (f u) (RatU.mapHom f y)
    · intro y u
      show RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f ((RatU.rational (U := N)).smulRight y u)) =
        (treeRational (U := N)).smulRight (RatU.lift Tree (treeRational (U := N'))
          (RatU.mapHom f y)) u
      rw [(RatU.mapHom_isHom f).map_smulRight y u]
      exact (RatU.lift_isHom Tree (treeRational (U := N'))).map_smulRight
        (RatU.mapHom f y) (f u)
  have heq := RatU.lift_unique (Tree) (treeRational (U := N))
    ((RatU.lift Tree (treeRational (U := N'))).comp (RatU.mapHom f)) hTree
  have hx := DFunLike.congr_fun heq x
  simpa only [Rat.treeOfRat, RingHom.comp_apply] using hx

end Work.ORHughesFree.Rat
