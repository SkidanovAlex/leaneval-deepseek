import Mathlib
import Submission.Work.TorusCover.Basic

namespace Work.TorusCover

open LeanEval.KnotTheory.PardonDistortion Set

/-- Two lifts of the same closed curve through a parametrised torus differ by a continuous
function with values in the (discrete) period lattice, hence by a constant.  Consequently the
period shift over one period is the same for both, so the winding vector is unique. -/
theorem hasWinding_unique (P : Work.TorusCover.TorusParam) {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    {v w : ℤ × ℤ} (hv : Work.TorusCover.HasWinding P.psi γ v)
    (hw : Work.TorusCover.HasWinding P.psi γ w) : v = w := by
  obtain ⟨Λ, hΛ⟩ := hv
  obtain ⟨Λ', hΛ'⟩ := hw
  -- Both lifts take the same value under `psi`, so their difference lies in the period lattice.
  have hmem : ∀ t, (Λ t - Λ' t) ∈ lattice := fun t =>
    P.psiMap_eq_iff.mp (by
      show P.psi (Λ t).1 (Λ t).2 = P.psi (Λ' t).1 (Λ' t).2
      rw [hΛ.map_eq t, hΛ'.map_eq t])
  have hcont : Continuous (fun t : ℝ => Λ t - Λ' t) := hΛ.continuous.sub hΛ'.continuous
  -- A continuous map from the (pre)connected `ℝ` into the discrete lattice is constant.
  have hconst := isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice
    hcont.continuousOn (fun t _ => hmem t) (mem_univ (0 : ℝ)) (mem_univ (2 * Real.pi))
  change Λ 0 - Λ' 0 = Λ (2 * Real.pi) - Λ' (2 * Real.pi) at hconst
  -- Evaluate the displacement over one period.
  rw [hΛ.displacement, hΛ'.displacement] at hconst
  have hdis : periodShift v - periodShift w = 0 := by
    have hab : (Λ 0 + periodShift v) - (Λ' 0 + periodShift w)
        = (Λ 0 - Λ' 0) + (periodShift v - periodShift w) := by abel
    rw [hab] at hconst
    have h2 : (Λ 0 - Λ' 0) + (periodShift v - periodShift w) = (Λ 0 - Λ' 0) + 0 := by
      rw [add_zero]; exact hconst.symm
    exact add_left_cancel h2
  exact periodShift_injective (sub_eq_zero.mp hdis)

end Work.TorusCover
