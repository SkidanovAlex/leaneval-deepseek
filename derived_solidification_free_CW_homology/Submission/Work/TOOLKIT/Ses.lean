/-
AREA TOOLKIT — the two-out-of-three fields `ses₁`, `ses₂`, `ses₃`.

Given a morphism `φ : S₁ ⟶ S₂` of short exact sequences of cochain complexes of light condensed
abelian groups, the associated distinguished triangles `triangleOfSES` give a morphism of
distinguished triangles, and the contravariant long exact `Hom(-, iD.obj N⟦m⟧)` sequences (proved
in `Submission/Work/TOOLKIT/Les/`) allow the five-lemma.  The results proved here are the fields
`ses₁`, `ses₂`, `ses₃` of `Submission.Blueprint.ToolkitProp`.
-/
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Les.solidEquiv_middle
import Submission.Work.TOOLKIT.Les.solidEquiv_right
import Submission.Work.TOOLKIT.Les.solidEquiv_left

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

namespace Work.TOOLKIT

/-- **ses₂.**  If `φ.τ₁` and `φ.τ₃` are solid-equivalences, so is `φ.τ₂`. -/
theorem solidEquiv_ses₂ {S₁ S₂ : ShortComplex Cpx} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) (h₁ : SolidEquiv (DerivedCategory.Q.map φ.τ₁))
    (h₃ : SolidEquiv (DerivedCategory.Q.map φ.τ₃)) :
    SolidEquiv (DerivedCategory.Q.map φ.τ₂) := by
  intro N
  have hmid := Les.solidEquiv_middle (DerivedCategory.triangleOfSES_distinguished hS₁)
    (DerivedCategory.triangleOfSES_distinguished hS₂)
    (DerivedCategory.triangleOfSES.map hS₁ hS₂ φ) N
    (fun m => h₁ ((shiftFunctor SDCat m).obj N))
    (fun m => h₃ ((shiftFunctor SDCat m).obj N)) 0
  exact (solidEquiv_target_iso_iff (DerivedCategory.Q.map φ.τ₂)
    (iD.mapIso ((shiftFunctorZero SDCat ℤ).app N))).1 hmid

/-- **ses₃.**  If `φ.τ₁` and `φ.τ₂` are solid-equivalences, so is `φ.τ₃`. -/
theorem solidEquiv_ses₃ {S₁ S₂ : ShortComplex Cpx} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) (h₁ : SolidEquiv (DerivedCategory.Q.map φ.τ₁))
    (h₂ : SolidEquiv (DerivedCategory.Q.map φ.τ₂)) :
    SolidEquiv (DerivedCategory.Q.map φ.τ₃) := by
  intro N
  have hmid := Les.solidEquiv_right (DerivedCategory.triangleOfSES_distinguished hS₁)
    (DerivedCategory.triangleOfSES_distinguished hS₂)
    (DerivedCategory.triangleOfSES.map hS₁ hS₂ φ) N
    (fun m => h₁ ((shiftFunctor SDCat m).obj N))
    (fun m => h₂ ((shiftFunctor SDCat m).obj N)) 0
  exact (solidEquiv_target_iso_iff (DerivedCategory.Q.map φ.τ₃)
    (iD.mapIso ((shiftFunctorZero SDCat ℤ).app N))).1 hmid

/-- **ses₁.**  If `φ.τ₂` and `φ.τ₃` are solid-equivalences, so is `φ.τ₁`. -/
theorem solidEquiv_ses₁ {S₁ S₂ : ShortComplex Cpx} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) (h₂ : SolidEquiv (DerivedCategory.Q.map φ.τ₂))
    (h₃ : SolidEquiv (DerivedCategory.Q.map φ.τ₃)) :
    SolidEquiv (DerivedCategory.Q.map φ.τ₁) := by
  intro N
  have hmid := Les.solidEquiv_left (DerivedCategory.triangleOfSES_distinguished hS₁)
    (DerivedCategory.triangleOfSES_distinguished hS₂)
    (DerivedCategory.triangleOfSES.map hS₁ hS₂ φ) N
    (fun m => h₂ ((shiftFunctor SDCat m).obj N))
    (fun m => h₃ ((shiftFunctor SDCat m).obj N)) 0
  exact (solidEquiv_target_iso_iff (DerivedCategory.Q.map φ.τ₁)
    (iD.mapIso ((shiftFunctorZero SDCat ℤ).app N))).1 hmid

end Work.TOOLKIT
