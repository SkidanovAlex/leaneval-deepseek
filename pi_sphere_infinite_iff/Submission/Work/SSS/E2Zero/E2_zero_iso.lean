import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.E2Aux.homologyZeroIsoCokernel
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.E2Zero.Defs
import Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff
import Submission.Work.SSS.E2Zero.Cincl_mem_V_one_iff
import Submission.Work.SSS.E2Zero.ker_chi_map
import Submission.Work.SSS.E2Zero.range_chi
import Submission.Work.SSS.E2Zero.ker_comap_hT
import Submission.Work.SSS.GradedZero.graded_zero

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.SSS.E2Zero

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- `(E1Complex ξ t).d 1 0 = d1 ξ 0 t`, by definition of the complex. -/
theorem E1Complex_d_zero (ξ : Filtration C) (t : ℕ) :
    (E1Complex ξ t).d 1 0 = d1 ξ 0 t :=
  ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) 0

/-- `E2 ξ 0 t ≅ coker (kF ξ 0 t)`:  the second page in the bottom row is the cokernel of the
connecting map `kF ξ 0 t` (the `H_0` of the E¹ row complex).  This is
`Work.SSS.GradedZero.E2_zero_iso_coker`, restated as an explicit linear equivalence. -/
theorem E2_zero_iso_coker (ξ : Filtration C) (t : ℕ) :
    Nonempty (E2 ξ 0 t ≃ₗ[ℤ] (↑(cokernel (kF ξ 0 t)))) :=
  ⟨(Work.SSS.GradedZero.E2_zero_iso_coker ξ t).toLinearEquiv⟩

/-- The left column of the second page at `s = 0`: `↥(Zof ξ t) ⧸ VZ ξ t 1 ≅ coker (kF ξ 0 t)`. -/
theorem coker_iso (ξ : Filtration C) (t : ℕ) :
    Nonempty ((↥(Zof ξ t) ⧸ VZ ξ t 1) ≃ₗ[ℤ] (↑(cokernel (kF ξ 0 t)))) := by
  have hsurj : Function.Surjective (chi ξ t) := LinearMap.range_eq_top.mp (range_chi ξ t)
  refine ⟨?_⟩
  have e1 : (↥(Zof ξ t) ⧸ VZ ξ t 1) ≃ₗ[ℤ]
      (↥(((ξ.F.obj 0).sc t).homology) ⧸ LinearMap.ker (chi ξ t)) :=
    (LinearMap.quotKerEquivOfSurjective (chi ξ t) hsurj).symm
  -- `H_t(F_0) ⧸ im (kF ξ 0 t) ≅ H_t(F_0) ⧸ ker (chi ξ t)` via the linear equivalence `hT ξ t`
  -- (which only differs from the identity by the index bookkeeping `0 + t`), using that
  -- `map (hT ξ t).symm (ker (chi ξ t)) = range (kF ξ 0 t)` (`ker_chi_map`).
  have e2 : (↥(((ξ.F.obj 0).sc t).homology) ⧸ LinearMap.ker (chi ξ t)) ≃ₗ[ℤ]
      (↥((ξ.F.obj 0).homology (0 + t)) ⧸ LinearMap.range (kF ξ 0 t).hom) :=
    Submodule.Quotient.equiv _ _ (hT ξ t).symm (ker_chi_map ξ t)
  exact e1.trans (e2.trans (ModuleCat.cokernelIsoRangeQuotient (kF ξ 0 t)).symm.toLinearEquiv)

/-- **The left column starts at `Z_t(F_0)/V_1`.**  The `E²` term `E2 ξ 0 t` of the filtration is
isomorphic to `Z_t(F_0)/V_1`, where `Z_t(F_0)` is the group of `t`-cycles of the bottom filtration
term `F_0` and `V_1 = ∂(F_1C_{t+1}) ∩ Z_t(F_0)`.

Roadmap.  `E2 ξ 0 t = (E1Complex ξ t).homology 0`, and for a `ℕ`-indexed chain complex the
homology in degree `0` is the cokernel of the differential `X_1 → X_0` (nothing maps into degree
`0` from below), so `E2 ξ 0 t ≅ coker (d1 ξ 0 t)` with `d1 ξ 0 t = kF ξ 0 t` because
`jF ξ 0 t = 𝟙`.  Here `kF ξ 0 t : H_{t+1}(F_1/F_0) → H_t(F_0)` is the connecting map of the short
exact sequence `0 → F_0 → F_1 → F_1/F_0 → 0` in degrees `t+1 → t`.  Now `H_t(F_0) = Z_t(F_0)/∂F_0C_{t+1}`
and `ShortComplex.ShortExact.δ_eq` says that `kF ξ 0 t` sends the class of a relative cycle `x` to
the class of `∂x` (with `x` any lift of the class to `F_1C_{t+1}`); hence `im (kF ξ 0 t)` is the
image of `V_1 = ∂(F_1C_{t+1}) ∩ Z_t(F_0)` in `H_t(F_0)`, and the cokernel is
`Z_t(F_0)/V_1 = ↥(Zof ξ t) ⧸ VZ ξ t 1`.  Conclude with the first isomorphism theorem
(`LinearMap.quotKerEquivRange`) and `ModuleCat.cokernelIsoRangeQuotient`. -/
theorem E2_zero_iso {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ) :
    Nonempty ((↥(Zof ξ t) ⧸ VZ ξ t 1) ≃ₗ[ℤ] (E2 ξ 0 t)) := by
  obtain ⟨e1⟩ := coker_iso ξ t
  obtain ⟨e2⟩ := E2_zero_iso_coker ξ t
  exact ⟨e1.trans e2.symm⟩

end

end Work.SSS.E2Zero
