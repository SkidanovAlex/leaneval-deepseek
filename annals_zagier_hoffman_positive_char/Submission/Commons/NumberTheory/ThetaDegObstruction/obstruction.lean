import Mathlib

namespace Commons.NumberTheory.ThetaDegObstruction

theorem obstruction {q w D E : ℕ} (hq : 3 ≤ q) (hw : 0 < w)
    (hE : E = q * (D - w)) (hDe : E ≤ max D q) (hwD : w ≤ D) (hDq : E < D → D ≤ q) :
    (q - 1) ∣ w ∨ w ≤ q := by
  by_cases hwq : w ≤ q
  · exact Or.inr hwq
  · push_neg at hwq
    have hqD : q < D := lt_of_lt_of_le hwq hwD
    have hmax : max D q = D := max_eq_left (le_of_lt hqD)
    have hED : E ≤ D := by rw [hmax] at hDe; exact hDe
    have hnotlt : ¬ E < D := by
      intro h
      have hDle : D ≤ q := hDq h
      omega
    have hEqD : E = D := by omega
    have hE' : q * (D - w) = D := by rw [hE] at hEqD; exact hEqD
    have hDw : D = w + (D - w) := (Nat.add_sub_of_le hwD).symm
    have hmain : q * (D - w) = w + (D - w) := hE'.trans hDw
    refine Or.inl ⟨D - w, ?_⟩
    have h1 : (q - 1) * (D - w) = q * (D - w) - (D - w) := by
      rw [Nat.mul_sub_right_distrib]; simp
    have h2 : q * (D - w) - (D - w) = w := by rw [hmain, Nat.add_sub_cancel]
    rw [h1, h2]

end Commons.NumberTheory.ThetaDegObstruction
