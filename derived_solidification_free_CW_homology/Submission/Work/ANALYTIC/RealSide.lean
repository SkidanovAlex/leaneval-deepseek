import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.RealSideDefs
import Submission.Work.ANALYTIC.prodReal_sheaf
import Submission.Work.ANALYTIC.boundedReal_preservesFiniteProducts
import Submission.Work.ANALYTIC.boundedRealSheaf
import Submission.Work.ANALYTIC.ProdZModel
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.boundedSeq_map_injective

/-!
# The ℝ-side of AN2 (REFS/03 §3)

The ℝ-valued analogues of `∏_ℕ ℤ` and `∏^bnd ℤ` of `Submission/Work/ANALYTIC/RealSideDefs.lean`,
together with the inclusions

`∏^bnd ℤ ⟶ ∏^bnd ℝ ⟶ ∏ℝ`  and  `∏^bnd ℤ ⟶ ∏ℤ ⟶ ∏ℝ`

and the quotient `realQuot = ∏ℝ/∏^bndℝ` through which the map `∏ℤ ⟶ realQuot` factors.  The
content of REFS/03 §3 used by AN2 is that `realQuot` (a quotient of the ℝ-module object `∏ℝ`) is
solid-null; the short exact sequence `∏^bnd ℤ ⟶ ∏ℤ ⟶ realQuot` then shows (via
`Submission.Blueprint.ToolkitProp.ses₂`) that `∏^bnd ℤ ⟶ ∏ℤ` is a solid-equivalence.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

/-- **The light condensed abelian group `∏_ℕ ℝ`**, whose `S`-points are the `ℕ`-indexed families
of continuous real-valued functions on `S` (definitionally). -/
noncomputable def prodReal : LightCondAb :=
  let hProd : PreservesFiniteProducts
      (prodRealPresheaf.{0} ⋙ CategoryTheory.forget (ModuleCat.{0, 0} ℤ)) :=
    prodReal_sheaf.{0,0}.1
  let hEq : CategoryTheory.regularTopology.EqualizerCondition
      (prodRealPresheaf.{0} ⋙ CategoryTheory.forget (ModuleCat.{0, 0} ℤ)) :=
    prodReal_sheaf.{0,0}.2
  letI := hProd
  LightCondensed.ofSheafForgetLightProfinite prodRealPresheaf.{0} hEq

/-- The `S`-points of `prodReal` are the families of continuous `ℝ`-valued functions on `S`
(definitionally). -/
theorem prodReal_obj_obj (S : LightProfinite) :
    ↥(prodReal.obj.obj (Opposite.op S)) = (ℕ → C(S, ℝ)) := rfl

/-- **The light condensed abelian group `∏^bnd ℝ`** of uniformly bounded families of continuous
real-valued functions (definitionally). -/
noncomputable def boundedReal : LightCondAb :=
  letI : PreservesFiniteProducts
      (boundedRealPresheaf.{0} ⋙ CategoryTheory.forget (ModuleCat.{0, 0} ℤ)) :=
    boundedReal_preservesFiniteProducts
  LightCondensed.ofSheafForgetLightProfinite boundedRealPresheaf.{0}
    boundedRealSheafEqualizer

/-- The `S`-points of `boundedReal` are the uniformly bounded families of continuous `ℝ`-valued
functions on `S` (definitionally). -/
theorem boundedReal_obj_obj (S : LightProfinite) :
    ↥(boundedReal.obj.obj (Opposite.op S)) = boundedRealSet S := rfl

/-! ## The inclusions -/

/-- **The inclusion `∏^bnd ℝ ⟶ ∏ℝ`** (the identity on families). -/
noncomputable def boundedRealIncl : boundedReal ⟶ prodReal where
  hom :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x => (x.1 : ℕ → C(S.unop, ℝ))
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      naturality := fun _ _ _ => rfl }

/-- The defining property of the inclusion `∏^bnd ℝ ⟶ ∏ℝ`: on `S`-points it is the identity. -/
theorem boundedRealIncl_apply (S : LightProfinite) (x : ↥(boundedRealSet S)) (n : ℕ) :
    (boundedRealIncl.hom.app (Opposite.op S) x) n = (x.1 : ℕ → C(S, ℝ)) n := rfl

/-- **The inclusion `∏^bnd ℤ ⟶ ∏^bnd ℝ`** (the identity on families). -/
noncomputable def boundedIntRealIncl : boundedSeq ⟶ boundedReal where
  hom :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x =>
            ⟨fun n => ⟨fun s => ((x.1 n s : ℤ) : ℝ),
                (continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp (x.1 n).continuous⟩,
              by
                obtain ⟨N, hN⟩ := x.2
                refine ⟨|(N : ℝ)|, fun n s => ?_⟩
                calc |(((x.1 n s : ℤ)) : ℝ)| = ((|x.1 n s| : ℤ) : ℝ) := by simp
                  _ ≤ ((N : ℤ) : ℝ) := by exact_mod_cast hN n s
                  _ ≤ |(N : ℝ)| := le_abs_self _⟩
          map_add' := fun x y => Subtype.ext (funext fun n => ContinuousMap.ext fun s => by
            simp [Int.cast_add])
          map_smul' := fun c x => Subtype.ext (funext fun n => ContinuousMap.ext fun s => by
            simp [Int.cast_mul]) }
      naturality := fun _ _ _ => rfl }

/-- The defining property of the inclusion `∏^bnd ℤ ⟶ ∏^bnd ℝ`. -/
theorem boundedIntRealIncl_apply (S : LightProfinite) (x : ↥(boundedSeqSet S)) (n : ℕ) (s : S) :
    (boundedIntRealIncl.hom.app (Opposite.op S) x).1 n s = ((x.1 : ℕ → C(S, ℤ)) n s : ℝ) := rfl

/-- **The inclusion `∏ℤ ⟶ ∏ℝ`** (the identity on families). -/
noncomputable def prodZRealIncl : prodZModel ⟶ prodReal where
  hom :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x => fun n => ⟨fun s => ((x n s : ℤ) : ℝ),
            (continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp (x n).continuous⟩
          map_add' := fun x y => funext fun n => ContinuousMap.ext fun s => by
            simp [Int.cast_add]
          map_smul' := fun c x => funext fun n => ContinuousMap.ext fun s => by
            simp [Int.cast_mul] }
      naturality := fun _ _ _ => rfl }

/-- The defining property of the inclusion `∏ℤ ⟶ ∏ℝ`. -/
theorem prodZRealIncl_apply (S : LightProfinite) (x : ℕ → C(S, ℤ)) (n : ℕ) (s : S) :
    (prodZRealIncl.hom.app (Opposite.op S) x) n s = ((x n s : ℤ) : ℝ) := rfl

/-- **The two inclusions into `∏ℝ` agree on `∏^bnd ℤ`.** -/
theorem boundedIntRealIncl_boundedRealIncl :
    boundedIntRealIncl ≫ boundedRealIncl = boundedSeqIncl ≫ prodZRealIncl := by
  apply LightCondensed.hom_ext
  intro S
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine funext fun n => ContinuousMap.ext fun s => ?_
  rfl

/-! ## The quotient `∏ℝ / ∏^bnd ℝ` -/

/-- The quotient `∏ℝ/∏^bnd ℝ` (the ℝ-side model of `∏ℤ/∏^bnd ℤ` of REFS/03 §3). -/
noncomputable abbrev realQuot : LightCondAb := cokernel boundedRealIncl

/-- The map `∏ℤ ⟶ ∏ℝ/∏^bnd ℝ`. -/
noncomputable abbrev zToRealQuot : prodZModel ⟶ realQuot :=
  prodZRealIncl ≫ cokernel.π boundedRealIncl

/-- The map `∏^bnd ℤ ⟶ ∏ℝ/∏^bnd ℝ` (whose vanishing is the "kernel" part of the exactness of
`∏^bnd ℤ ⟶ ∏ℤ ⟶ ∏ℝ/∏^bnd ℝ`). -/
noncomputable abbrev boundedToRealQuot : boundedSeq ⟶ realQuot :=
  boundedSeqIncl ≫ zToRealQuot

/-- The composite `∏^bnd ℤ ⟶ ∏ℤ ⟶ ∏ℝ/∏^bnd ℝ` vanishes: the bounded sequences map into the
bounded *real* families, which are killed by the quotient map. -/
theorem boundedToRealQuot_eq_zero : boundedToRealQuot = 0 := by
  rw [boundedToRealQuot, zToRealQuot, ← Category.assoc, ← boundedIntRealIncl_boundedRealIncl,
    Category.assoc, cokernel.condition, comp_zero]

/-! ## Monomorphisms -/

/-- The inclusion `∏^bnd ℤ ⟶ ∏ℤ` is a monomorphism. -/
theorem mono_boundedSeqIncl : Mono boundedSeqIncl := by
  apply CategoryTheory.Sheaf.mono_of_injective
  intro S x y h
  exact Subtype.ext h

/-- The inclusion `∏^bnd ℝ ⟶ ∏ℝ` is a monomorphism. -/
theorem mono_boundedRealIncl : Mono boundedRealIncl := by
  apply CategoryTheory.Sheaf.mono_of_injective
  intro S x y h
  exact Subtype.ext h

end Work.ANALYTIC
