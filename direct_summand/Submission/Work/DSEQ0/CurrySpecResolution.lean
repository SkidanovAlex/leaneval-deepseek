import Mathlib
import Submission.Work.DSEQ0.CurryAffineCover
import Submission.Work.DSF1.Cech.cechAffineCover_quasiIso

/-!
# The Čech resolution of the affine open `W` via `Spec Γ(X, W)`

Combining `Work.DSF1.Cech.cechAffineCover_quasiIso` with the pulled-back family
`curryPullback hW U` of `Submission.Work.DSEQ0.CurryAffineCover`: the `ℤ`-indexed Čech complex
of the family `curryPullback hW U` on `Spec Γ(X, W)` is a resolution of `Γ(X, W)`, hence its
homology vanishes in positive degrees.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {W : X.Opens}

/-- The Čech complex of the pulled-back family on `Spec Γ(X, W)`. -/
noncomputable def currySpecComplex (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} (X.presheaf.obj (Opposite.op W))) ℤ :=
  DSMap.cechZ (X.presheaf.obj (Opposite.op W))
    (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
    (CategoryTheory.CategoryStruct.id _) (curryPullback hW U)

/-- **The positive-degree homology of the pulled-back Čech complex vanishes.** -/
theorem isZero_homology_currySpecComplex (hW : AlgebraicGeometry.IsAffineOpen W) {ι : Type u}
    [Finite ι] (U : ι → X.Opens)
    (hinf : ∀ (n : ℕ) (y : Fin (n + 1) → ι),
      AlgebraicGeometry.IsAffineOpen (W ⊓ ⨅ a, U (y a))) (hle : W ≤ ⨆ i, U i)
    (i : ℤ) (hi : 0 < i) : IsZero ((currySpecComplex hW U).homology i) := by
  obtain ⟨cc, -, hcc⟩ := Work.DSF1.Cech.cechAffineCover_quasiIso
    (X.presheaf.obj (Opposite.op W)) (curryPullback hW U)
    (fun j => isAffineOpen_curryPullback hW U hinf j) (iSup_curryPullback hW U hle)
  haveI : QuasiIso cc := (HomologicalComplex.mem_quasiIso_iff cc).mp hcc
  have hiso : IsIso (HomologicalComplex.homologyMap cc i) :=
    (quasiIsoAt_iff_isIso_homologyMap cc i).mp inferInstance
  have hzero : IsZero
      (((HomologicalComplex.single (ModuleCat.{u} (X.presheaf.obj (Opposite.op W)))
        (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of (X.presheaf.obj (Opposite.op W))
            (X.presheaf.obj (Opposite.op W)))).homology i) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ i (by omega)
  exact IsZero.of_iso hzero (asIso (HomologicalComplex.homologyMap cc i)).symm

end Work.DSEQ0
