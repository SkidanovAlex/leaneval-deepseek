import Mathlib
import Submission.Work.TOOLKIT.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.Les

/-- Three-term exactness of the contravariant long exact sequence of `Hom(-, W)` attached to a
distinguished triangle `T` in `D(LightCondAb)`, at the target shifted by `k`:
`Hom(T.obj₃, W⟦k⟧) → Hom(T.obj₂, W⟦k⟧) → Hom(T.obj₁, W⟦k⟧) → Hom(T.obj₃, W⟦k+1⟧)`.
`pre₁`, `pre₂` are precomposition with `T.mor₁`, `T.mor₂`, and `conn` is the connecting
homomorphism. -/
theorem les_exact (T : CategoryTheory.Pretriangulated.Triangle Work.TOOLKIT.DCat)
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (W : Work.TOOLKIT.DCat) (k : ℤ) :
    Function.Exact (Work.TOOLKIT.pre₂ T W k) (Work.TOOLKIT.pre₁ T W k) ∧
      Function.Exact (Work.TOOLKIT.pre₁ T W k) (Work.TOOLKIT.conn T W k) ∧
      Function.Exact (Work.TOOLKIT.conn T W k) (Work.TOOLKIT.pre₂ T W (k + 1)) := by
  have hT' : Work.TOOLKIT.opTriangle T ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles :=
    CategoryTheory.Pretriangulated.op_distinguished T hT
  refine ⟨?_, ?_, ?_⟩
  · -- exactness at the middle of `Hom(T.obj₃, W⟦k⟧) → Hom(T.obj₂, W⟦k⟧) → Hom(T.obj₁, W⟦k⟧)`
    have h := CategoryTheory.Functor.homologySequence_exact₂
      (CategoryTheory.preadditiveYoneda.obj W) (Work.TOOLKIT.opTriangle T) hT' k
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  · -- exactness at the middle of `Hom(T.obj₂, W⟦k⟧) → Hom(T.obj₁, W⟦k⟧) → Hom(T.obj₃, W⟦k+1⟧)`
    have h := CategoryTheory.Functor.homologySequence_exact₃
      (CategoryTheory.preadditiveYoneda.obj W) (Work.TOOLKIT.opTriangle T) hT' k (k + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  · -- exactness at the middle of `Hom(T.obj₁, W⟦k⟧) → Hom(T.obj₃, W⟦k+1⟧) → Hom(T.obj₂, W⟦k+1⟧)`
    have h := CategoryTheory.Functor.homologySequence_exact₁
      (CategoryTheory.preadditiveYoneda.obj W) (Work.TOOLKIT.opTriangle T) hT' k (k + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h

end Work.TOOLKIT.Les
