import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Nat.GCD.Basic

namespace Commons.NumberTheory.ThetaDegObstruction

theorem obstruction_bound {q Q w D E : ℕ} (hq : 3 ≤ q) (hQ : q ≤ Q) (hw : 0 < w)
    (hE : E = q * (D - w)) (hDe : E ≤ max D Q) (hwD : w ≤ D) (hDq : E < D → D ≤ Q) :
    (q - 1) ∣ w ∨ w ≤ Q := by
  by_cases hwQ : w ≤ Q
  · exact Or.inr hwQ
  · left
    push_neg at hwQ
    have hQD : Q < D := lt_of_lt_of_le hwQ hwD
    -- In this regime hDq forces E = D.
    have hDE : D ≤ E := by
      by_contra h
      rw [not_le] at h
      exact absurd (hDq h) (not_le.mpr hQD)
    have hED : E ≤ D := by
      have hmax : max D Q = D := max_eq_left (le_of_lt hQD)
      rw [hmax] at hDe; exact hDe
    have hEDeq : E = D := le_antisymm hED hDE
    -- Hence q * (D - w) = D.
    have hqDw : q * (D - w) = D := by rw [← hE, hEDeq]
    -- Multiply out: q * w = D * (q - 1).
    have key : q * w = D * (q - 1) := by
      have h1 : q * (D - w) + q * w = q * D := by
        rw [← mul_add, Nat.sub_add_cancel hwD]
      rw [hqDw] at h1
      have h2 : q * w = q * D - D := by omega
      rw [Nat.mul_sub_left_distrib, mul_comm D q, mul_one]
      exact h2
    have hdiv : (q - 1) ∣ q * w := ⟨D, by rw [key, mul_comm]⟩
    have hcop : Nat.Coprime (q - 1) q := by
      have h1 : 1 ≤ q := by omega
      exact (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left q)
    exact hcop.dvd_of_dvd_mul_left hdiv

end Commons.NumberTheory.ThetaDegObstruction