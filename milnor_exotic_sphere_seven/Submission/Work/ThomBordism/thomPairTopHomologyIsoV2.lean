import Mathlib
import Submission.Work.Tubular.LocalStep
import Submission.Work.ThomBordism.cohEightMan8
import Submission.Work.ThomBordism.relHomologyIntOfCoh
import Submission.Work.ThomBordism.finiteHomologyThomPair
import Submission.Work.ThomBordism.dimCohVanishingCharted

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open CategoryTheory

theorem thomPairTopHomologyIsoV2 {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type} {hk : 1 ≤ k}
    (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) [PathConnectedSpace V.pt]
    (hZ : Nonempty (Work.Thom.ThomClass Z k)) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology (k + 8) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  obtain ⟨T⟩ := hZ
  have hfin : ∀ j : ℕ, Module.Finite ℤ ↥((Work.Cohomology.relChains (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology j) := fun j => finiteHomologyThomPair Z j
  have hC : Nonempty ((Work.Cohomology.relComplex ℤ (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology (k + 8) ≅ ModuleCat.of ℤ ℤ) := by
    obtain ⟨e8⟩ := cohEightMan8 V
    refine ⟨(eqToIso (congrArg (Work.Thom.OpenThom Z) (Nat.add_comm 8 k))).symm.trans
      (((LinearEquiv.toModuleIso (T.thomEquiv 8)).symm).trans e8)⟩
  have hC0 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℤ (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z)).homology (k + 9)) := by
    haveI h9 : Subsingleton ((Work.Cohomology.singularCochainComplex ℤ V.X).homology 9) :=
      Work.ThomBordism.dimCohVanishingCharted (N := 8) V.X 9 (by norm_num)
    have hSig : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ 9 V.X) := by
      change CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularCochainComplex ℤ V.X).homology 9)
      exact ModuleCat.isZero_of_subsingleton _
    have h10 : CategoryTheory.Limits.IsZero (Work.Thom.OpenThom Z (9 + k)) :=
      CategoryTheory.Limits.IsZero.of_iso hSig ((LinearEquiv.toModuleIso (T.thomEquiv 9)).symm)
    exact CategoryTheory.Limits.IsZero.of_iso h10
      (eqToIso (congrArg (Work.Thom.OpenThom Z) (Nat.add_comm 9 k).symm))
  exact Work.ThomBordism.relHomologyIntOfCoh (X := TopCat.of Z.TotalSpace)
    (A := Work.Thom.zeroComplement Z) (n := k + 8) hfin hC hC0

end Work.ThomBordism
