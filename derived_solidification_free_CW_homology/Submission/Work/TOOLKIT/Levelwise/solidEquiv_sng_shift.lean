/-
AREA TOOLKIT/Levelwise — a solid-equivalence in degree `0` is one in any degree.

The single complex `sng q M` (i.e. `M` concentrated in degree `q`) is the shift of
`sng 0 M` by `q`, so this is a consequence of the stability of `SolidEquiv` under shifts
(`Work.TOOLKIT.Shift.solidEquiv_shift`) together with the invariance of `SolidEquiv` under
composing with isomorphisms (`solidEquiv_iso_conj`).

Concretely, the `SingleFunctors` package `DerivedCategory.singleFunctors` supplies a
natural isomorphism
`φ : singleFunctor 0 ⋙ shift(-q) ≅ singleFunctor q`,
whose naturality square says that the morphism `singleFunctor q |>.map g` is the morphism
`shift(-q) |>.map (singleFunctor 0 |>.map g)` conjugated by the isomorphisms `φ`.  Hence
`SolidEquiv (singleFunctor q |>.map g)` follows from
`SolidEquiv (shift(-q) |>.map (singleFunctor 0 |>.map g))`, which is
`solidEquiv_shift hg (-q)`.  Finally `Q.map ((sng q).map g)` is definitionally
`(singleFunctor q).map g`.
-/
import Mathlib
import Submission.Work.TOOLKIT.Levelwise.Basic
import Submission.Work.TOOLKIT.Levelwise.SolidEquivBasic
import Submission.Work.TOOLKIT.Shift.solidEquiv_shift

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.Levelwise

/-- **A solid-equivalence in degree `0` is a solid-equivalence in every degree.**
If `g : M ⟶ N` induces a solid-equivalence on the single complexes concentrated in degree
`0`, then it does so on the single complexes concentrated in degree `q`.

This is the same statement as `solidEquiv_sng_shift`, stated with
`DerivedCategory.singleFunctor` (which is definitionally the image under `Q` of the single
complex `sng q`). -/
theorem solidEquiv_singleFunctor {M N : LightCondAb} (g : M ⟶ N) (q : ℤ)
    (hg : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map g)) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb q).map g) := by
  -- the single functors, together with their compatibility with the shift on `D(LightCondAb)`
  let S := DerivedCategory.singleFunctors LightCondAb
  let φ : S.functor 0 ⋙ CategoryTheory.shiftFunctor Work.TOOLKIT.DCat (-q) ≅ S.functor q :=
    S.shiftIso (-q) q 0 (by ring)
  -- naturality of `φ`: `singleFunctor q |>.map g` is the conjugate of the shift
  -- of `singleFunctor 0 |>.map g` by the isomorphisms `φ`
  have key : (S.functor q).map g =
      φ.inv.app M ≫ (CategoryTheory.shiftFunctor Work.TOOLKIT.DCat (-q)).map
        ((S.functor 0).map g) ≫ φ.hom.app N := by
    have h1 : (CategoryTheory.shiftFunctor Work.TOOLKIT.DCat (-q)).map
        ((S.functor 0).map g) ≫ φ.hom.app N = φ.hom.app M ≫ (S.functor q).map g :=
      φ.hom.naturality g
    rw [h1, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [key]
  exact (solidEquiv_iso_conj (φ.inv.app M) _ (φ.hom.app N)
    inferInstance inferInstance).mpr
    (Work.TOOLKIT.Shift.solidEquiv_shift hg (-q))

theorem solidEquiv_sng_shift {M N : LightCondAb} (g : M ⟶ N) (q : ℤ) (hg : Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map g)) : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map ((Work.TOOLKIT.Levelwise.sng q).map g)) := by
  change Submission.Blueprint.SolidEquiv
    ((DerivedCategory.singleFunctor LightCondAb q).map g)
  exact solidEquiv_singleFunctor g q hg

end Work.TOOLKIT.Levelwise
