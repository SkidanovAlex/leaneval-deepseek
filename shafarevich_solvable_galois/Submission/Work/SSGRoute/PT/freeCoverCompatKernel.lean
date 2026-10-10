import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.PT.freeCoverCompat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The comparison of the two syzygies `R → R'`

`freeCoverCompat φ X` (see `PT/freeCoverCompat.lean`) compares the two canonical covers of `X`, so
it must *descend to the syzygies*: for `r` in the kernel of the canonical cover of the restricted
module `Rep.res φ X` (the "local" syzygy `R' = E1cR1 (Rep.res φ X)`), its image under
`freeCoverCompat φ X` lies in the kernel of the restricted cover morphism (the "global" syzygy
`R = E1cR1 X`, restricted).

This is `freeCoverCompat` used a second time, at the level of the syzygies: the two kernels live in
free modules with the *same* index set `X.V` but different coefficient rings (`Coeff[H]` versus
`Coeff[G]`), which is the measured trap of `PT/NOTE_e1aChainC_localComparison.md` §11.3/§11.13, and
the reason `freeCoverCompat` is needed at all.

Following §11.14 (Route 2), the two kernel objects are bound by `abbrev`s **before** the statement
quantifies over them — exactly what `E1cGeneric.E1cR1` does — so that the `Rep`-instances are in
scope when `.V` is projected (spelling the kernel inline triggers
`failed to synthesize instance Semiring Coeff` and a cascade of field-notation errors).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- The syzygy of the canonical cover of the **restricted** module: the "local" syzygy `R'`. -/
noncomputable abbrev freeCoverR1 {G H : Type} [Group G] [Group H] (φ : H →* G) (X : Rep.{0} Coeff G) :
    Rep.{0} Coeff H :=
  CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover (Rep.res φ X))

/-- The restriction of the syzygy of the canonical cover of `X` — the "global" syzygy `R` — as the
kernel of the **restricted cover morphism** `(Rep.resFunctor φ).map (freeCover X)`. -/
noncomputable abbrev freeCoverR1Res {G H : Type} [Group G] [Group H] (φ : H →* G) (X : Rep.{0} Coeff G) :
    Rep.{0} Coeff H :=
  CategoryTheory.Limits.kernel ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))

/-- **The syzygy comparison.**  There is a map on the syzygies which intertwines the two kernel
inclusions with `freeCoverCompat`: for `r` in the local syzygy `R'`, its image under
`freeCoverCompat` lies in the restricted global syzygy `R|`, and `f` is that correspondence. -/
theorem freeCoverCompat_kernelMap {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    (φ : H →* G) (X : Rep.{0} Coeff G) :
    ∃ f : (freeCoverR1 φ X).V → (freeCoverR1Res φ X).V,
      ∀ r, (CategoryTheory.Limits.kernel.ι
            ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))).hom (f r)
          = (freeCoverCompat φ X).hom
              ((CategoryTheory.Limits.kernel.ι
                (Work.SSGRoute.freeCover (Rep.res φ X))).hom r) := by
  refine ⟨fun r => (CategoryTheory.Limits.kernel.lift
      ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
      (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover (Rep.res φ X))
        ≫ freeCoverCompat φ X)
      (by
        rw [CategoryTheory.Category.assoc, freeCoverCompat_comp]
        exact CategoryTheory.Limits.kernel.condition _)).hom r, ?_⟩
  intro r
  change ((CategoryTheory.Limits.kernel.lift
      ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
      (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover (Rep.res φ X))
        ≫ freeCoverCompat φ X) _) ≫
      CategoryTheory.Limits.kernel.ι
        ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))).hom r
    = (freeCoverCompat φ X).hom
        ((CategoryTheory.Limits.kernel.ι
          (Work.SSGRoute.freeCover (Rep.res φ X))).hom r)
  rw [CategoryTheory.Limits.kernel.lift_ι]
  rfl

/-- **The syzygy comparison, as a morphism of `H`-representations.**  The map `f` of
`freeCoverCompat_kernelMap` can be taken to be a morphism of `H`-representations — hence additive
and `H`-equivariant — which is what the coefficient change of the comparison square needs: the
index sets `R.V` and `R'.V` are compared by a map that commutes with the `D_A`-action. -/
theorem freeCoverCompat_kernelHom {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    (φ : H →* G) (X : Rep.{0} Coeff G) :
    ∃ F : freeCoverR1 φ X ⟶ freeCoverR1Res φ X,
      F ≫ CategoryTheory.Limits.kernel.ι
          ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
        = CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover (Rep.res φ X))
            ≫ freeCoverCompat φ X := by
  refine ⟨CategoryTheory.Limits.kernel.lift
      ((Rep.resFunctor φ).map (Work.SSGRoute.freeCover X))
      (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover (Rep.res φ X))
        ≫ freeCoverCompat φ X)
      (by
        rw [CategoryTheory.Category.assoc, freeCoverCompat_comp]
        exact CategoryTheory.Limits.kernel.condition _), ?_⟩
  exact CategoryTheory.Limits.kernel.lift_ι _ _ _

end Work.SSGRoute.PT
