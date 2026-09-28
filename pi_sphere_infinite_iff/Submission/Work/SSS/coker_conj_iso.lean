import Mathlib
import Submission.Work.SSS.serreE1PieceDefs

/-!
# The σ-piece is invariant under an isomorphism of the target

For a **monomorphism** `Φ : W ⟶ Z` of simplicial sets, the two cokernels

* `cokernel (C(P.image Φ) ⟶ C(Φ.range))`  and
* `cokernel (C(P) ⟶ C(W))`

are isomorphic.  Indeed `Φ` being a mono, the induced maps `W ⟶ Φ.range` (`Subcomplex.toRange Φ`)
and `P ⟶ P.image Φ` (`Subcomplex.toImage Φ`) are isomorphisms, and the square

```
      P   --P.toImage Φ-->   P.image Φ
      |                          |
   P.ι                     homOfLE (image_le_range P Φ)
      |                          |
      v                          v
      W   --W.toRange Φ-->    Φ.range
```

commutes in `SSet`.  Applying the chain-complex functor and `cokernel.mapIso` finishes.

This is the formal statement that the σ-piece `C(T_σ)/C(∂T_σ)` of the Serre filtration depends only
on the image of the simplex, hence can be computed after restricting along a monomorphism.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

theorem coker_conj_iso {W Z : SSet.{0}} (Φ : W ⟶ Z) [CategoryTheory.Mono Φ]
    (P : W.Subcomplex) :
    Nonempty (CategoryTheory.Limits.cokernel
        (Work.SSS.sCCMap (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ))) ≅
      CategoryTheory.Limits.cokernel (Work.SSS.sCCMap P.ι)) := by
  -- functoriality of `sCCMap` on composites
  have hcomp : ∀ {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
      sCCMap (f ≫ g) = sCCMap f ≫ sCCMap g := by
    intro X Y Z f g
    simp only [sCCMap, Functor.map_comp]
  -- `Φ` is an isomorphism onto its range
  haveI : IsIso (SSet.Subcomplex.toRange Φ) := inferInstance
  -- `P.ι ≫ Φ` is a mono, so `P.toImage Φ : P ⟶ P.image Φ` is an iso (it is always an epi)
  haveI : IsIso (P.toImage Φ) := by
    haveI : Mono (P.toImage Φ) :=
      mono_of_mono_fac (SSet.Subcomplex.toImage_ι P Φ)
    exact CategoryTheory.isIso_of_mono_of_epi (P.toImage Φ)
  haveI : IsIso (sCCMap (P.toImage Φ)) := inferInstance
  haveI : IsIso (sCCMap (SSet.Subcomplex.toRange Φ)) := inferInstance
  -- the square relating `P.toImage Φ` and `Φ.toRange`
  have hsq : P.toImage Φ ≫ SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)
      = P.ι ≫ SSet.Subcomplex.toRange Φ := by
    apply (cancel_mono (SSet.Subcomplex.range Φ).ι).1
    rw [Category.assoc, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι,
        SSet.Subcomplex.toImage_ι P Φ]
  refine ⟨(CategoryTheory.Limits.cokernel.mapIso (sCCMap P.ι)
      (sCCMap (SSet.Subcomplex.homOfLE (SSet.Subcomplex.image_le_range P Φ)))
      (asIso (sCCMap (P.toImage Φ)))
      (asIso (sCCMap (SSet.Subcomplex.toRange Φ))) ?_).symm⟩
  simp only [asIso_hom]
  rw [← hcomp, ← hcomp, hsq]

end

end Work.SSS
