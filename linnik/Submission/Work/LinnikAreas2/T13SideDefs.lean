import Mathlib
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.t13_sin_cos_taylor

open scoped BigOperators
noncomputable section
namespace Work.LinnikAreas2
open Work.LinnikAreas.Density4
open Work.LinnikAreas.Density4.T13

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxHeartbeats 8000000

/-- The two numerical side conditions that HB Lemma 12.1 needs at `ε = 0` for the test
function of HB §7 with `θ = θ13 λ λ₁`, `λ̂ = λ`: `f(0)/6 < F(λ-λ₁)` and the discriminant
condition `(F(λ-λ₁) - f(0)/6)^2 > F(-λ₁)·f(0)/6`. -/
def sideCond (lam lam1 : ℝ) : Prop :=
  fT (theta13 lam lam1) lam 0 / 6 < FT (theta13 lam lam1) lam (lam - lam1) ∧
    (FT (theta13 lam lam1) lam (lam - lam1) - fT (theta13 lam lam1) lam 0 / 6) ^ 2 >
      FT (theta13 lam lam1) lam (-lam1) * (fT (theta13 lam lam1) lam 0 / 6)

/-- Interval version of the above: from an interval enclosure of `A, B, c` and three rational
inequalities, the two side conditions of `sideCond`. -/
theorem ratio_side {A B c Alo Ahi Blo Bhi clo chi : ℝ}
    (hA1 : Alo ≤ A) (hA2 : A ≤ Ahi) (hB1 : Blo ≤ B) (hB2 : B ≤ Bhi)
    (hc1 : clo ≤ c) (hc2 : c ≤ chi)
    (hAlo0 : 0 ≤ Alo) (hclo0 : 0 ≤ clo) (hcBlo : chi ≤ Blo)
    (hden : 0 < (Blo - chi) ^ 2 - Ahi * chi) :
    c < B ∧ (B - c) ^ 2 > A * c := by
  have hA0 : 0 ≤ A := le_trans hAlo0 hA1
  have hAhi0 : 0 ≤ Ahi := le_trans hA0 hA2
  have hc0 : 0 ≤ c := le_trans hclo0 hc1
  have hchi0 : 0 ≤ chi := le_trans hc0 hc2
  have hchiBlo : chi < Blo := by
    rcases lt_or_eq_of_le hcBlo with h | h
    · exact h
    · exfalso
      have hzero : (Blo - chi) ^ 2 = 0 := by rw [h]; ring
      have hprod : 0 ≤ Ahi * chi := mul_nonneg hAhi0 hchi0
      rw [hzero] at hden
      linarith
  have hden_ge : (Blo - chi) ^ 2 - Ahi * chi ≤ (B - c) ^ 2 - A * c := by
    have h1 : Blo - chi ≤ B - c := by linarith
    have h2 : 0 ≤ Blo - chi := by linarith
    have h3 : (Blo - chi) ^ 2 ≤ (B - c) ^ 2 := by nlinarith
    have h4 : A * c ≤ Ahi * chi := by
      have h5 : A * c ≤ Ahi * c := mul_le_mul_of_nonneg_right hA2 hc0
      have h6 : Ahi * c ≤ Ahi * chi := mul_le_mul_of_nonneg_left hc2 hAhi0
      linarith
    linarith
  exact ⟨hc2.trans_lt (hchiBlo.trans_le hB1), by linarith [hden, hden_ge]⟩

end Work.LinnikAreas2
