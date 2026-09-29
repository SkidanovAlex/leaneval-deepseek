import Mathlib
import Submission.Work.CPull.defs
import Submission.CDT.PureDenom

/-!
# Coefficient bound for the pure function `B₃`

`Submission.CDTPlan.B3` is the pure function
`B₃ = Σ_{n ≥ 1} (n-1)!²/(2n)! · yⁿ`.  Its coefficients decay geometrically: we prove
`‖[yⁿ]B₃‖ ≤ 2·(1/4)ⁿ` for every `n` (`[yⁿ]B₃ = 0` for `n = 0`).

Writing `bₙ = [yⁿ]B₃ ∈ ℚ` for `n ≥ 1`, the successive ratio is
`b_{n+1}/b_n = n²/((2n+1)(2n+2)) ≤ 1/4`,
so `bₙ ≤ b₁·4^{1-n} = 2·4^{-n}`.  Everything is carried out over `ℚ` and transferred to `ℂ`
at the end.
-/

namespace Work.CPull

open PowerSeries

noncomputable section

/-- The coefficients of `B₃` are nonnegative rationals. -/
private lemma b3_nonneg (n : ℕ) : 0 ≤ Submission.CDT.PureDenom.b3 n := by
  rw [Submission.CDT.PureDenom.b3]
  split_ifs with h
  · norm_num
  · positivity

/-- Successive-ratio formula for the coefficients of `B₃`, valid for `n ≥ 1`:
`b_{n+1} = b_n · n²/((2n+1)(2n+2))`. -/
private lemma b3_succ_ratio (n : ℕ) (hn : 1 ≤ n) :
    Submission.CDT.PureDenom.b3 (n+1) =
      Submission.CDT.PureDenom.b3 n * ((n:ℚ)^2 / ((2*(n:ℚ)+1)*(2*(n:ℚ)+2))) := by
  rw [Submission.CDT.PureDenom.b3, Submission.CDT.PureDenom.b3]
  simp only [if_neg (by omega : ¬ (n+1) = 0), if_neg (by omega : ¬ n = 0)]
  have e1 : (↑(n+1-1).factorial : ℚ) = (n:ℚ) * ↑(n-1).factorial := by
    have h := Submission.CDT.PureDenom.factorial_succ_cast n hn
    have : n+1-1 = n := by omega
    rw [this]; exact h
  have e2 : (↑(2*(n+1)).factorial : ℚ)
      = (2*(n:ℚ)+2) * (2*(n:ℚ)+1) * ↑(2*n).factorial := by
    have h1 := Submission.CDT.PureDenom.factorial_succ_cast (2*(n+1)) (by omega)
    have hh1 : 2*(n+1)-1 = 2*n+1 := by omega
    rw [hh1] at h1
    have h2 := Submission.CDT.PureDenom.factorial_succ_cast (2*n+1) (by omega)
    have hh2 : 2*n+1-1 = 2*n := by omega
    rw [hh2] at h2
    rw [h1, h2]
    push_cast
    ring
  rw [e1, e2]
  field_simp

/-- The geometric bound `bₙ ≤ 2·(1/4)ⁿ` for `n ≥ 1`, by induction from `b₁ = 1/2 = 2·(1/4)`
using `b_{n+1} = b_n·n²/((2n+1)(2n+2)) ≤ b_n/4`. -/
private lemma b3_le_ge_one : ∀ n ≥ 1, Submission.CDT.PureDenom.b3 n ≤ 2 * (1/4:ℚ)^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [Submission.CDT.PureDenom.b3]
  | succ n hn ih =>
    have hratio := b3_succ_ratio n hn
    have hb3n : 0 ≤ Submission.CDT.PureDenom.b3 n := b3_nonneg n
    have hle : (n:ℚ)^2 / ((2*(n:ℚ)+1)*(2*(n:ℚ)+2)) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity : (0:ℚ) < (2*(n:ℚ)+1)*(2*(n:ℚ)+2))]
      nlinarith [show (0:ℚ) ≤ (n:ℚ) from Nat.cast_nonneg n]
    calc Submission.CDT.PureDenom.b3 (n+1)
        = Submission.CDT.PureDenom.b3 n
            * ((n:ℚ)^2 / ((2*(n:ℚ)+1)*(2*(n:ℚ)+2))) := hratio
      _ ≤ Submission.CDT.PureDenom.b3 n * (1/4) := mul_le_mul_of_nonneg_left hle hb3n
      _ ≤ (2*(1/4:ℚ)^n) * (1/4) := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = 2*(1/4:ℚ)^(n+1) := by rw [pow_succ]; ring

/-- The coefficient bound `bₙ ≤ 2·(1/4)ⁿ` over `ℚ`, all `n`. -/
private lemma b3_le (n : ℕ) : Submission.CDT.PureDenom.b3 n ≤ 2 * (1/4:ℚ)^n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Submission.CDT.PureDenom.b3, if_pos rfl]
    norm_num
  · exact b3_le_ge_one n h

/-- `PowerSeries.coeff n B₃` agrees with the pure-denominator spelling `PureDenom.b3`. -/
private lemma coeff_B3 (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B3 = Submission.CDT.PureDenom.b3 n := by
  rw [Submission.CDTPlan.B3, PowerSeries.coeff_mk, Submission.CDT.PureDenom.b3]

/-- The coefficient bound, as a real inequality after the `ℚ → ℝ → ℂ` cast. -/
private lemma coeff_B3_abs_le (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ ≤ 2 * (1/4 : ℝ) ^ n := by
  rw [coeff_B3 n]
  have h1 : ((Submission.CDT.PureDenom.b3 n : ℚ) : ℂ) =
      (((Submission.CDT.PureDenom.b3 n : ℚ) : ℝ) : ℂ) := by push_cast; norm_num
  rw [h1]
  have h2 : ‖(((Submission.CDT.PureDenom.b3 n : ℚ) : ℝ) : ℂ)‖ =
      ((Submission.CDT.PureDenom.b3 n : ℚ) : ℝ) := by
    have hnrm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by simp
    rw [hnrm]
    exact abs_of_nonneg (by exact_mod_cast b3_nonneg n)
  rw [h2]
  have hval : ((2 * (1/4:ℚ)^n : ℚ) : ℝ) = 2 * (1/4:ℝ)^n := by push_cast; norm_num
  rw [← hval]
  exact_mod_cast b3_le n

theorem norm_coeff_B3_le (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ ≤ 2 * (1 / 4 : ℝ) ^ n :=
  coeff_B3_abs_le n

end

end Work.CPull
