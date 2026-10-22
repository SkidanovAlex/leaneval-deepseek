import Mathlib
import Submission.Work.ANALYTIC.ProdZModel
import Submission.Work.ANALYTIC.solidNull_of_unit_action
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.preSolid_all
import Submission.Work.ANALYTIC.RealSideDefs
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.ANALYTIC.NullFamily
import Submission.Work.ANALYTIC.RealAssembly
import Submission.Work.ANALYTIC.prodReal_rounding
import Submission.Work.ANALYTIC.solidNull_prodReal
import Submission.Work.ANALYTIC.solidNull_boundedReal
import Submission.Work.ANALYTIC.shortExact_realQuot

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **AN2 (REFS/03 §3).**  The inclusion `boundedSeqIncl : ∏^bnd ℤ ⟶ ∏ℤ`
(`Submission/Work/ANALYTIC/ProdZModel.lean`, the identity on families of continuous `ℤ`-valued
functions) is a solid-equivalence.

Route (REFS/03 §3):
1. Form the short exact sequence of complexes `0 → ∏^bnd ℤ → ∏ℤ → Q → 0`,
   `Q := cokernel boundedSeqIncl` (in degree 0), using the definitional description of the
   `S`-points of both objects as submodules of `ℕ → C(S,ℤ)` (`prodZModel_obj_obj`,
   `Work.ANALYTIC.boundedSeq_obj_obj`).
2. Show that `Q` is solid-null.  Introduce the ℝ-valued analogues `prodReal` (`S ↦ ℕ → C(S,ℝ)`,
   constructed like `prodZModel`) and `boundedReal` (`S ↦` uniformly bounded families) and prove
   `Q ≅ prodReal / boundedReal` from the exact sequences `0 → ∏ℤ → ∏ℝ → ∏ℝ/ℤ → 0` and
   `0 → ∏^bnd ℤ → ∏^bnd ℝ → ∏ℝ/ℤ → 0` (REFS/03 §3).  Then `prodReal/boundedReal` is an
   `ℝ`-module object by coordinatewise multiplication (which preserves boundedness), with unit
   `u : 𝟙_ ⟶ realCond` the "constant `1`", so that
   `Work.ANALYTIC.solidNull_of_realModule'` (module `Submission.Work.ANALYTIC.Main`, or inline its
   two-line proof using `Work.ANALYTIC.solidNull_of_unit_action` +
   `Work.ANALYTIC.exists_realNullSeq` + `Work.ANALYTIC.preSolid_all`) gives `Hom_D(Q, ι N) = 0`
   for all `N : DSolid`.
3. Deduce the solid-equivalence: `ses₂` of `Submission.Blueprint.ToolkitProp` applied to the
   morphism of short exact sequences `[∏^bnd ⟶id ∏^bnd ⟶ 0] ⟶ [∏^bnd ⟶incl ∏ℤ ⟶π Q]` gives
   `SolidEquiv incl` from `SolidEquiv id` and `SolidEquiv (0 : ∏^bnd ⟶ Q)` (the latter is
   `SolidNull Q`, using that `⟦1⟧` of a complex of solids is again a complex of solids and that
   `derivedInclusion` commutes with shifts). -/
theorem boundedSeqIncl_solidEquiv (hflat : Submission.Blueprint.FlatProp)
    (hTK : Submission.Blueprint.ToolkitProp)
    [PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P)] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map boundedSeqIncl) := by
  -- The quotient `∏ℝ/∏^bndℝ` is solid-null (REFS/03 §3): `∏ℝ` and `∏^bndℝ` are ℝ-module
  -- objects, hence solid-null (`solidNull_prodReal`, `solidNull_boundedReal`), and two-out-of-three
  -- for the short exact sequence `∏^bndℝ ⟶ ∏ℝ ⟶ ∏ℝ/∏^bndℝ` gives it for the quotient
  -- (`solidNull_realQuot`).
  have hQ : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj realQuot) :=
    solidNull_realQuot hTK solidNull_prodReal solidNull_boundedReal
  -- The single-object functor `X ↦ X[0]`.
  let F : LightCondAb ⥤ CochainComplex LightCondAb ℤ :=
    HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0
  -- The two short exact sequences of complexes.
  let S₁ : ShortComplex (CochainComplex LightCondAb ℤ) :=
    (ShortComplex.mk (𝟙 boundedSeq) (0 : boundedSeq ⟶ (0 : LightCondAb)) (by simp)).map F
  let S₂ : ShortComplex (CochainComplex LightCondAb ℤ) :=
    (ShortComplex.mk boundedSeqIncl zToRealQuot boundedToRealQuot_eq_zero).map F
  have hS₁ : S₁.ShortExact := (shortExact_id_zero boundedSeq).map_of_exact F
  have hS₂ : S₂.ShortExact := (shortExact_realQuot).map_of_exact F
  -- The morphism of short exact sequences
  -- `[∏^bnd ℤ ⟶id ∏^bnd ℤ ⟶ 0] ⟶ [∏^bnd ℤ ⟶incl ∏ℤ ⟶ ∏ℝ/∏^bndℝ]`.
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 𝟙 (F.obj boundedSeq)
      τ₂ := F.map boundedSeqIncl
      τ₃ := 0
      comm₁₂ := by
        change 𝟙 (F.obj boundedSeq) ≫ F.map boundedSeqIncl =
          F.map (𝟙 boundedSeq) ≫ F.map boundedSeqIncl
        simp
      comm₂₃ := by
        change F.map boundedSeqIncl ≫ F.map zToRealQuot =
          F.map (0 : boundedSeq ⟶ (0 : LightCondAb)) ≫
            (0 : F.obj (0 : LightCondAb) ⟶ F.obj realQuot)
        rw [← Functor.map_comp, show boundedSeqIncl ≫ zToRealQuot = 0 from
          boundedToRealQuot_eq_zero, Functor.map_zero, comp_zero] }
  -- Its first component is an isomorphism.
  haveI : IsIso φ.τ₁ := by rw [show φ.τ₁ = 𝟙 _ from rfl]; infer_instance
  have h₁ : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₁) :=
    hTK.of_iso _ (Functor.map_isIso DerivedCategory.Q φ.τ₁)
  -- Its third component is the zero map out of a zero object, so its `SolidEquiv`-ness is
  -- exactly the solid-nullness of `∏ℝ/∏^bndℝ`.
  have hzero : IsZero (F.obj (0 : LightCondAb)) :=
    Functor.map_isZero F (isZero_zero LightCondAb)
  have hz : IsZero (DerivedCategory.Q.obj S₁.X₃) :=
    Functor.map_isZero DerivedCategory.Q hzero
  have h₃ : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₃) :=
    (solidEquiv_zero_iff _ hz).mpr fun N => hQ N
  -- Two-out-of-three gives the solid-equivalence of the middle map, i.e. of
  -- `boundedSeqIncl : ∏^bnd ℤ ⟶ ∏ℤ`.
  exact hTK.ses₂ hS₁ hS₂ φ h₁ h₃

end
