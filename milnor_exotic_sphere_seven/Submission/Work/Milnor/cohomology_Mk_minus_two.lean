import Mathlib
import Submission.Work.Milnor.Homeo7
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.pathConnected_band

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The singular cohomology of `Mk (-2)`

Milnor's manifold `Submission.Milnor.Mk (-2)` is homeomorphic to `S⁷` (`Work.Milnor.mk_minus_two_homeo`),
and singular cohomology is a homotopy invariant (`Work.Cohomology.cohomologyIso_of_homotopyEquiv`).
Hence its singular cohomology with `ℤ` coefficients agrees with that of `S⁷`:
`ℤ` in degrees `0` and `7`, and `0` in all other degrees — the statement requested here.

The cohomology of the standard sphere `S⁷ = Metric.sphere (0 : ℝ⁸) 1` is supplied by
`Work.Cohomology.sphereCohomologyTop` (top degree), `Work.Cohomology.sphereCohomologyZero`
(vanishing off `0` and `7`) and `Work.Cohomology.singularCohomology_zero` (degree `0`).
-/

namespace Work.Milnor

open CategoryTheory AlgebraicTopology Limits
open Submission.Milnor

noncomputable section

/-- `S⁷ ⊆ ℝ⁸` is path connected, so its degree-`0` singular cohomology is `ℤ`. -/
lemma pathConnectedSpace_sphere8 :
    PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 (by norm_num)
  rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin 8)) = (8 : Cardinal) from by
    have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin 8) ℝ).toLinearEquiv
    rw [h2]; exact rank_fin_fun 8]
  norm_num

/-- **The singular cohomology of `S⁷`**, in the shape requested for `Mk (-2)`: `ℤ` in degrees `0`
and `7`, and `0` otherwise. -/
theorem singularCohomology_sphere7 (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  by_cases h0 : n = 0
  · subst h0
    have hm : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 7 then 1 else 0) = 1 := by
      norm_num
    rw [hm]
    haveI : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :=
      pathConnectedSpace_sphere8
    obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero ℤ
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1))
    exact ⟨e ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · by_cases h7 : n = 7
    · subst h7
      have hm : (if (7 : ℕ) = 0 then 1 else 0) + (if (7 : ℕ) = 7 then 1 else 0) = 1 := by
        norm_num
      rw [hm]
      obtain ⟨e⟩ := Work.Cohomology.sphereCohomologyTop 7 (by norm_num)
      exact ⟨e ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
    · have hm : (if n = 0 then 1 else 0) + (if n = 7 then 1 else 0) = 0 := by
        rw [if_neg h0, if_neg h7]
      rw [hm]
      have hz : CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology ℤ n
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1))) :=
        Work.Cohomology.sphereCohomologyZero 7 n (by norm_num) h0 h7
      have hz' : CategoryTheory.Limits.IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
        rw [ModuleCat.isZero_iff_subsingleton]
        infer_instance
      exact ⟨CategoryTheory.Limits.IsZero.iso hz hz'⟩

/-- **The singular cohomology of `Mk (-2)`**: `ℤ` in degrees `0` and `7`, and `0` otherwise. -/
theorem cohomology_Mk_minus_two (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of (Submission.Milnor.Mk (-2))) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  obtain ⟨h⟩ := mk_minus_two_homeo
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv h.toHomotopyEquiv n
  exact ⟨iso ≪≫ (singularCohomology_sphere7 n).some⟩

end

end Work.Milnor
