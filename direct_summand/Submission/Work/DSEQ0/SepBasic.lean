import Mathlib
import Submission.Work.DSEQ0.atv_machine
import Submission.Work.DSF1.Sheaf.cech_unit_basicOpen_exact

/-!
# Serre vanishing for the structure sheaf on an affine scheme

The machine `Work.DSEQ0.isZero_rightDerived_of_cechTrivOnBasic` (built by the `DSEQ0` area)
reduces the vanishing of the higher right derived functors of `Γ(X, ⊤)` at a sheaf `Z` on an
affine scheme `X` to the Čech-triviality of `Z` on basic-open covers
(`Work.DSEQ0.CechTrivOnBasic`).  For `Z = 𝒪_X` this is Stacks 30.2.1, available in the workspace
as `Work.DSF1.Sheaf.cech_unit_basicOpen_exact`.

This file records the resulting statement, which is the input ("Serre vanishing on affine
schemes") for the acyclicity of the sheaves `secSheaf W` along an affine open immersion.
-/

namespace Work.DSEQ0.Sep

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- The base case of the affine machine: the structure sheaf of an affine scheme is Čech-trivial
on every basic-open cover. -/
theorem cechTrivOnBasic_unit (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X] :
    CechTrivOnBasic X (SheafOfModules.unit X.ringCatSheaf) := by
  intro ι _ f g hmem hcov n hn
  exact Work.DSF1.Sheaf.cech_unit_basicOpen_exact X f g hmem hcov n hn

/-- **Serre vanishing for the structure sheaf on an affine scheme**: the higher right derived
functors of the global-sections functor at `𝒪_X` vanish. -/
theorem affine_unit_acyclic (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X]
    [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero
      (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  isZero_rightDerived_of_cechTrivOnBasic X _ (cechTrivOnBasic_unit X)

end Work.DSEQ0.Sep
