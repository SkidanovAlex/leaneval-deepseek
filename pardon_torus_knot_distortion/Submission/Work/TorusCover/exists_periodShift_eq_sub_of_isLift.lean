import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.isLift_unique

namespace Work.TorusCover

/-- Two lifts of the same curve `γ` through a parametrised torus differ by a constant element
of the period lattice: there is `w : ℤ × ℤ` with `Λ' t = Λ t + periodShift w` for all `t`.

Indeed the difference `Λ' 0 - Λ 0` lies in `2πℤ²` (both points map to `γ 0`), so it is
`periodShift w` for some `w`; then `t ↦ Λ t + periodShift w` is again a lift of `γ`, agreeing
with `Λ'` at `0`, hence equal to it by uniqueness of lifts. -/
theorem exists_periodShift_eq_sub_of_isLift (P : Work.TorusCover.TorusParam)
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {Λ Λ' : ℝ → ℝ × ℝ}
    (h : Work.TorusCover.IsLift P.psi γ Λ) (h' : Work.TorusCover.IsLift P.psi γ Λ') :
    ∃ w : ℤ × ℤ, ∀ t, Λ' t = Λ t + Work.TorusCover.periodShift w := by
  -- Both `Λ 0` and `Λ' 0` map to `γ 0`, so their difference is a period-lattice element.
  have h0 : Λ' 0 - Λ 0 ∈ lattice := by
    rw [← P.psiMap_eq_iff]
    show psiMap P.psi (Λ' 0) = psiMap P.psi (Λ 0)
    rw [psiMap_apply, psiMap_apply, h'.2 0, h.2 0]
  obtain ⟨w, hw⟩ := (mem_lattice_iff (Λ' 0 - Λ 0)).mp h0
  refine ⟨w, ?_⟩
  -- `t ↦ Λ t + periodShift w` is again a lift of `γ`, and agrees with `Λ'` at `0`.
  have hΛ'' : IsLift P.psi γ (fun t => Λ t + periodShift w) := by
    refine ⟨h.1.add continuous_const, ?_⟩
    intro t
    have : psiMap P.psi (Λ t + periodShift w) = γ t := by
      rw [P.psiMap_add_periodShift]
      exact h.2 t
    simpa [psiMap_apply] using this
  have heq : (fun t => Λ t + periodShift w) = Λ' :=
    isLift_unique P hΛ'' h' (by rw [hw]; abel)
  intro t
  exact (congrFun heq t).symm

end Work.TorusCover
