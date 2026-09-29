import Mathlib
import Submission.Work.Params.qall
import Submission.Work.Params.basic
import Submission.Work.Params.defs

/-! `F = (d-1)!` carries every prime `≤ d`, and `Q` carries each factor `2Fk ± 1` for `1 ≤ k < d`. -/

namespace Work.Params

open HvdH

theorem nt1 :
    (∀ p : ℕ, Nat.Prime p → p ≤ D → p ∣ Ffac) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ D - 1 → (2 * Ffac * k + 1) ∣ Qall) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ D - 1 → (2 * Ffac * k - 1) ∣ Qall) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hle
    apply dvd_Ffac_of_le hp.pos
    have hnp : ¬ Nat.Prime 1729 := by norm_num
    have hD : D = 1729 := rfl
    have hlt : p < 1729 := by
      rcases lt_or_eq_of_le (hD ▸ hle) with h | h
      · exact h
      · exact absurd (h ▸ hp) hnp
    omega
  · intro k _ hkD
    have hmem : k - 1 ∈ List.range (D - 1) := by
      rw [List.mem_range]; omega
    have hprod : (2 * Ffac * ((k - 1) + 1) + 1) * (2 * Ffac * ((k - 1) + 1) - 1) ∣ Qall := by
      unfold Qall
      exact List.dvd_prod (List.mem_map.mpr ⟨k - 1, hmem, rfl⟩)
    have hk' : (k - 1) + 1 = k := by omega
    rw [hk'] at hprod
    exact dvd_trans (dvd_mul_right _ _) hprod
  · intro k _ hkD
    have hmem : k - 1 ∈ List.range (D - 1) := by
      rw [List.mem_range]; omega
    have hprod : (2 * Ffac * ((k - 1) + 1) + 1) * (2 * Ffac * ((k - 1) + 1) - 1) ∣ Qall := by
      unfold Qall
      exact List.dvd_prod (List.mem_map.mpr ⟨k - 1, hmem, rfl⟩)
    have hk' : (k - 1) + 1 = k := by omega
    rw [hk'] at hprod
    exact dvd_trans (dvd_mul_left _ _) hprod

end Work.Params
