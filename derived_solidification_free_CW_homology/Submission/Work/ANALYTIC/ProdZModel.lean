import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.Bounded
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.ProdZ
import Submission.Work.ANALYTIC.prodZPresheaf_sheaf

/-!
# The model `∏_ℕ ℤ` and the inclusion `∏^bnd ℤ ⊆ ∏ℤ` (AN2)

`prodZModel` is the light condensed abelian group `∏_ℕ ℤ` modelled with explicit sections
(`boundedSeqSet S` is a submodule of its `S`-points), and `boundedSeqIncl : boundedSeq ⟶ prodZModel`
is the inclusion of REFS/03 §3.  The statement of AN2 is that `boundedSeqIncl` is a
solid-equivalence (see `Submission/Work/ANALYTIC/README.md`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

universe u

theorem prodZPresheaf_FP :
    PreservesFiniteProducts (prodZPresheaf.{u} ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  prodZPresheaf_sheaf.{u, u}.1

theorem prodZPresheaf_Eq :
    CategoryTheory.regularTopology.EqualizerCondition
      (prodZPresheaf.{u} ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  prodZPresheaf_sheaf.{u, u}.2

/-- **A model of `∏_ℕ ℤ`** with explicit sections: `S ↦ (ℕ → C(S,ℤ))`. -/
noncomputable def prodZModel : LightCondAb :=
  letI : PreservesFiniteProducts
      (prodZPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := prodZPresheaf_FP
  LightCondensed.ofSheafForgetLightProfinite prodZPresheaf prodZPresheaf_Eq

/-- The `S`-points of `prodZModel` are the `ℕ`-indexed families of continuous `ℤ`-valued functions
on `S` (definitionally). -/
theorem prodZModel_obj_obj (S : LightProfinite) :
    ↥(prodZModel.obj.obj (Opposite.op S)) = (ℕ → C(S, ℤ)) := rfl

/-- **The inclusion `∏^bnd ℤ ⟶ ∏ℤ`** of REFS/03 §3: the identity on families of continuous
functions (the bounded families are a submodule of all families). -/
noncomputable def boundedSeqIncl : boundedSeq ⟶ prodZModel where
  hom :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x => (x.1 : ℕ → C(S.unop, ℤ))
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      naturality := fun _ _ _ => rfl }

/-- The defining property of the inclusion: on `S`-points it is the identity on families. -/
theorem boundedSeqIncl_apply (S : LightProfinite) (x : ↥(boundedSeqSet S)) (n : ℕ) :
    (boundedSeqIncl.hom.app (Opposite.op S) x) n = x.1 n := rfl

end Work.ANALYTIC
