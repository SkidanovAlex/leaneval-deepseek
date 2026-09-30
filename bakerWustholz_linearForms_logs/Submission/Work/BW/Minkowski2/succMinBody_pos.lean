import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

/-- The `j`-th successive minimum is nonnegative: it is the infimum of a set of positive reals. -/
theorem succMinBody_nonneg' {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (j : ℕ) : 0 ≤ Work.BW.succMinBody Λ K j :=
  Real.sInf_nonneg (fun _ hx => le_of_lt hx.1)

/-- The standard basis vector `stdVec i` is nonzero. -/
theorem stdVec_ne_zero {d : ℕ} (i : Fin d) : Work.BW.stdVec i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [Work.BW.stdVec] at this

/-- Assuming the standard basis vectors `eᵢ` all lie in `succMinBody Λ K (i+1) • K`
(the successive minima are realised by the `eᵢ`), every successive minimum is positive. -/
theorem succMinBody_pos {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (hreal : ∀ i : Fin d,
      Work.BW.stdVec i ∈ Work.BW.smulSet (Work.BW.succMinBody Λ K (i.1 + 1)) K)
    {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d) : 0 < Work.BW.succMinBody Λ K j := by
  have hnn : 0 ≤ Work.BW.succMinBody Λ K j := succMinBody_nonneg' Λ K j
  by_contra hcon
  have hzero : Work.BW.succMinBody Λ K j = 0 := le_antisymm (not_lt.mp hcon) hnn
  -- the index `i = j - 1` is a valid `Fin d`
  have hlt : j - 1 < d := by omega
  have hmem := hreal ⟨j - 1, hlt⟩
  have hidx : ((⟨j - 1, hlt⟩ : Fin d) : ℕ) + 1 = j := by simp; omega
  rw [hidx] at hmem
  obtain ⟨a, _ha, haeq⟩ := hmem
  have hz : Work.BW.stdVec (⟨j - 1, hlt⟩ : Fin d) = 0 := by
    rw [haeq, hzero, zero_smul]
  exact stdVec_ne_zero ⟨j - 1, hlt⟩ hz

end Work.BW.Minkowski2
