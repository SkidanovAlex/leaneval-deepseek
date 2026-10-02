import Mathlib
import Submission.Work.RatHurewicz.DomeMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RatHurewicz

/-- A boundary point of `I^{m+1}` which is not in the interior of the bottom face `{s = 0}`
either has last coordinate `1`, or has its space part on `∂I^m`. -/
theorem dome_cond_of_not_bottom_interior {m : ℕ} {z : Fin (m + 1) → unitInterval}
    (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h : ¬(z (Fin.last m) = 0 ∧
      ∀ i : Fin m, 0 < (z i.castSucc : ℝ) ∧ (z i.castSucc : ℝ) < 1)) :
    z (Fin.last m) = 1 ∨ (fun i : Fin m => z i.castSucc) ∈ Cube.boundary (Fin m) := by
  by_cases h1 : z (Fin.last m) = 1
  · exact Or.inl h1
  refine Or.inr ?_
  obtain ⟨i, hi | hi⟩ := hz
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact ⟨j, Or.inl (by simpa using hi)⟩
    · have hz0 : z (Fin.last m) = 0 := hi
      have hnot : ¬ ∀ j : Fin m, 0 < (z j.castSucc : ℝ) ∧ (z j.castSucc : ℝ) < 1 :=
        fun hc => h ⟨hz0, hc⟩
      obtain ⟨j, hj⟩ := not_forall.mp hnot
      rw [not_and_or] at hj
      rcases hj with hj | hj
      · exact ⟨j, Or.inl (Subtype.ext (le_antisymm (not_lt.mp hj) (z j.castSucc).2.1))⟩
      · exact ⟨j, Or.inr (Subtype.ext (le_antisymm (z j.castSucc).2.2 (not_lt.mp hj)))⟩
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact ⟨j, Or.inr (by simpa using hi)⟩
    · exact absurd hi h1

theorem domePt_surj_dome (m : ℕ) (hm : 1 ≤ m) {z : Fin (m + 1) → unitInterval}
    (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h : ¬(z (Fin.last m) = 0 ∧
      ∀ i : Fin m, 0 < (z i.castSucc : ℝ) ∧ (z i.castSucc : ℝ) < 1)) :
    ∃ y : Fin m → unitInterval, Work.RatHurewicz.domePt hm y = z :=
  domePt_surj hm hz (dome_cond_of_not_bottom_interior hz h)

end Work.RatHurewicz
