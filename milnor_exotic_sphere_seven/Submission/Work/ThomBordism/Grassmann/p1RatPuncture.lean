import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Gen.TautDualPuncture
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.cp2H_cup_generates
import Submission.Work.Projective.cpnUV_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Vanishing of `H^k` of the punctured total space of `tautDual 2` over `ℂP²`

`Work.ThomBordism.Grassmann.puncturedTautDualTwoHZero` and its model-space form
`Work.ThomBordism.Grassmann.puncturedComplexHZeroOf` are used by the crux
`Work.ThomBordism.Grassmann.zStd_pontryagin_ne_zero` (via the pieces
`Work.ThomBordism.Grassmann.UR`/`VR` of `Work.ThomBordism.Grassmann.W`), so they live in this
separate module to keep the import graph acyclic: the crux and its support files import *this*
module instead of `p1Rat_ne_zero_via_probe`, which in turn imports the crux.
-/

namespace Work.ThomBordism.Grassmann

noncomputable section


/-- **`H^k(ℂ^{m+2}∖{0};ℤ) = 0` off the degrees `0` and `2m+3`**, from the Mayer–Vietoris
computation `Work.Projective.cpnUV_cohomology_zero` through the homeomorphism
`Work.Projective.cpnUV_homeo`. -/
theorem puncturedComplexHZeroOf (m k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * m + 3) :
    CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ k (TopCat.of {z : Fin (m + 2) → ℂ // z ≠ 0})) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (Work.Projective.cpnUV_homeo (m + 2)).toHomotopyEquiv k
  have hz : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ k
        (TopCat.of ↥(Work.Projective.cpU (m + 2) ∩ Work.Projective.cpV (m + 2)))) :=
    Work.Projective.cpnUV_cohomology_zero (m + 1) k hk0 (by omega)
  exact CategoryTheory.Limits.IsZero.of_iso hz e.symm

/-- **`H^k` of the punctured total space of `realification (tautDual 2)` vanishes** off the
degrees `0` and `5`, since that space is the punctured model space `ℂ³∖{0}`
(`Work.Gen.ChernGen.tautDualPunctHomeo 2`). -/
theorem puncturedTautDualTwoHZero (k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 5) :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ k
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2)))) := by
  obtain ⟨e⟩ := Work.Gen.ChernGen.tautDualPunctHomeo 2
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e.toHomotopyEquiv k
  exact CategoryTheory.Limits.IsZero.of_iso (puncturedComplexHZeroOf 1 k hk0 (by omega)) iso


end

end Work.ThomBordism.Grassmann
