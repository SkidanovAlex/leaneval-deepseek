import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.NullFamily
import Submission.Work.ANALYTIC.RealSide

/-!
# Assembly lemmas for AN2 (`boundedSeqIncl_solidEquiv`)

These are the elementary categorical lemmas used in the final assembly of
`Work.ANALYTIC.boundedSeqIncl_solidEquiv`:

* `Work.ANALYTIC.shortExact_cokernel`: the cokernel sequence `A --f--> B --> coker f` is short exact;
* `Work.ANALYTIC.shortExact_zero`: the zero short complex `0 --> 0 --> 0` is short exact;
* `Work.ANALYTIC.solidNull_realQuot`: `SolidNull` of the quotient `∏ℝ/∏^bndℝ` follows (via
  `Submission.Blueprint.ToolkitProp.ses₃`) from `SolidNull` of `∏ℝ` and of `∏^bnd ℝ`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

/-- **The cokernel sequence is short exact**: for `f : A ⟶ B`, the short complex
`A --f--> B --cokernel.π f--> coker f` is short exact. -/
theorem shortExact_cokernel (A B : LightCondAb) (f : A ⟶ B) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  exact kernel.condition (cokernel.π f)

/-- **The zero short complex is short exact.**  It is the short complex
`0 --0--> 0 --0--> 0` in `LightCondAb`, and it is used as the source of the morphism of short
complexes in the `ses₃`-argument producing the solid-nullness of `∏ℝ/∏^bndℝ`. -/
theorem shortExact_zero :
    (ShortComplex.mk (0 : (0 : LightCondAb) ⟶ (0 : LightCondAb))
      (0 : (0 : LightCondAb) ⟶ (0 : LightCondAb)) (by simp)).ShortExact := by
  refine ShortComplex.Splitting.shortExact
    ⟨(0 : (0 : LightCondAb) ⟶ (0 : LightCondAb)),
      (0 : (0 : LightCondAb) ⟶ (0 : LightCondAb)), ?_, ?_, ?_⟩
  · exact IsZero.eq_of_src (isZero_zero LightCondAb) _ _
  · exact IsZero.eq_of_src (isZero_zero LightCondAb) _ _
  · exact IsZero.eq_of_src (isZero_zero LightCondAb) _ _

/-- **Solid-nullness of `∏ℝ/∏^bndℝ`.**  This is the two-out-of-three consequence of the short
exact sequence `∏^bndℝ ⟶ ∏ℝ ⟶ ∏ℝ/∏^bndℝ` (REFS/03 §3): a morphism of short exact sequences out of
the zero short complex with all three components zero has components `0 : 0 ⟶ ∏^bndℝ`,
`0 : 0 ⟶ ∏ℝ` and `0 : 0 ⟶ ∏ℝ/∏^bndℝ`, so `ToolkitProp.ses₃` gives the solid-equivalence (i.e. the
solid-nullness) of the last one from the solid-nullness of the first two. -/
theorem solidNull_realQuot (hTK : Submission.Blueprint.ToolkitProp)
    (hV : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj prodReal))
    (hW : SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj boundedReal)) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj realQuot) := by
  let F : LightCondAb ⥤ CochainComplex LightCondAb ℤ :=
    HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0
  -- the short exact sequence `∏^bndℝ ⟶ ∏ℝ ⟶ ∏ℝ/∏^bndℝ`
  let C : ShortComplex LightCondAb :=
    ShortComplex.mk boundedRealIncl (cokernel.π boundedRealIncl) (cokernel.condition _)
  haveI := mono_boundedRealIncl
  have hC : C.ShortExact := shortExact_cokernel _ _ _
  -- the zero short exact sequence
  let Z : ShortComplex LightCondAb :=
    ShortComplex.mk (0 : (0 : LightCondAb) ⟶ (0 : LightCondAb))
      (0 : (0 : LightCondAb) ⟶ (0 : LightCondAb)) (by simp)
  have hZ : Z.ShortExact := shortExact_zero
  -- the two short exact sequences of complexes
  let S₁ : ShortComplex (CochainComplex LightCondAb ℤ) := Z.map F
  let S₂ : ShortComplex (CochainComplex LightCondAb ℤ) := C.map F
  have hS₁ : S₁.ShortExact := hZ.map_of_exact F
  have hS₂ : S₂.ShortExact := hC.map_of_exact F
  -- the zero morphism of short complexes
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := 0
      τ₂ := 0
      τ₃ := 0
      comm₁₂ := by simp
      comm₂₃ := by simp }
  have hzero : IsZero (F.obj (0 : LightCondAb)) :=
    Functor.map_isZero F (isZero_zero LightCondAb)
  have hz : IsZero (DerivedCategory.Q.obj S₁.X₁) :=
    Functor.map_isZero DerivedCategory.Q hzero
  have h₁ : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₁) :=
    (solidEquiv_zero_iff _ hz).mpr fun N => hW N
  have h₂ : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₂) :=
    (solidEquiv_zero_iff _ hz).mpr fun N => hV N
  have h₃ : Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₃) :=
    hTK.ses₃ hS₁ hS₂ φ h₁ h₂
  intro N
  exact ((solidEquiv_zero_iff (DerivedCategory.Q.map φ.τ₃) hz).mp h₃) N

end Work.ANALYTIC
