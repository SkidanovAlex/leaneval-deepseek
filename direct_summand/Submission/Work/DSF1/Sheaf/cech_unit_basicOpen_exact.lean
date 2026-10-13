import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.cech_standard_tilde_exact
import Submission.Work.DSF1.Sheaf.CechStructMain

set_option maxHeartbeats 4000000

namespace Work.DSF1.Sheaf

universe u

theorem cech_unit_basicOpen_exact (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X]
    {ι : Type u} [Finite ι]
    (f : ι → X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g)
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        (Work.DSF1.Sheaf.cechComplex (fun i ↦ X.basicOpen (f i))
          (SheafOfModules.unit X.ringCatSheaf)) n) := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact isZero_homology_cech_unit X f g hmem hcov n hn

end Work.DSF1.Sheaf
