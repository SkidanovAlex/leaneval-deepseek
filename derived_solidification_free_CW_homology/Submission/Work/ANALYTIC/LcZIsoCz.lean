import Mathlib
import Submission.Work.ANALYTIC.ProdZAux

/-!
# The presheaf of locally constant `ℤ`-valued functions is the presheaf of continuous ones

`Submission/Work/ANALYTIC/ProdZAux.lean` introduces two models of the constant sheaf `ℤ` on
`LightProfinite`:

* `Cz`, the presheaf `S ↦ C(S,ℤ)` of *continuous* `ℤ`-valued functions, and
* `lcZ`, Mathlib's model `S ↦ LocallyConstant S ℤ` of the presheaf underlying the constant sheaf
  (`LightCondMod.LocallyConstant.functorToPresheaves`).

Since a light profinite space is totally disconnected and `ℤ` carries the discrete topology, the
two presheaves of `ℤ`-modules are equal on the nose on points; this file records the resulting
natural isomorphism `lcZ ≅ Cz` (`lcZIsoCz`), together with the two explicit natural maps.

The two remaining comparisons needed by AN2 are `Z.obj ≅ lcZ` (`ZobjIsoLcZ`, in `ProdZAux`) and
the present `lcZ ≅ Cz`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The `S`-points of `Cz` are (definitionally) the continuous maps `S → ℤ`. -/
theorem Cz_obj_obj (S : LightProfinite) : ↥(Cz.obj (op S)) = C(S, ℤ) := rfl

/-- The `S`-points of `lcZ` are (definitionally) the locally constant maps `S → ℤ`. -/
theorem lcZ_obj_obj (S : LightProfinite) : ↥(lcZ.obj (op S)) = LocallyConstant S ℤ := rfl

/-- The natural map `lcZ ⟶ Cz`: a locally constant function `S → ℤ` is continuous, because `ℤ` is
discrete.  Linearity is pointwise. -/
noncomputable def lcZToCz : lcZ ⟶ Cz where
  app d := ModuleCat.ofHom
    { toFun := fun f => (f : C(d.unop, ℤ))
      map_add' := by intro a b; ext s; rfl
      map_smul' := by intro a b; ext s; rfl }
  naturality d d' g := by ext x; rfl

/-- The natural map `Cz ⟶ lcZ`: a continuous function `S → ℤ` into the discrete `ℤ` is locally
constant.  Linearity is pointwise. -/
noncomputable def CzTolcZ : Cz ⟶ lcZ where
  app d := ModuleCat.ofHom
    { toFun := fun f =>
        (⟨f, (IsLocallyConstant.iff_continuous f).mpr f.continuous⟩ : LocallyConstant d.unop ℤ)
      map_add' := by intro a b; ext s; rfl
      map_smul' := by intro a b; ext s; rfl }
  naturality d d' g := by ext x; rfl

/-- **The presheaf `lcZ` of locally constant `ℤ`-valued functions is the presheaf `Cz` of
continuous `ℤ`-valued functions** (a light profinite space is totally disconnected, so
continuity into the discrete `ℤ` is local constancy). -/
noncomputable def lcZIsoCz : lcZ ≅ Cz where
  hom := lcZToCz
  inv := CzTolcZ
  hom_inv_id := by ext d x; rfl
  inv_hom_id := by ext d x; rfl

theorem LcZIsoCz : Nonempty (Work.ANALYTIC.lcZ ≅ Work.ANALYTIC.Cz) := ⟨lcZIsoCz⟩

end Work.ANALYTIC
