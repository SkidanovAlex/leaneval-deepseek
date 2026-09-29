import Mathlib
import Submission.Work.Pure.b4_B2_ode

/-!
# Coefficient bound for the pure function `B₂`

`Submission.CDTPlan.B2` is the pure function
`B₂ = Σ_{n ≥ 2} 2·(n-2)!·n!/(2n)! · yⁿ`.  Its coefficients decay geometrically: we prove
`‖[yⁿ]B₂‖ ≤ 3·(1/4)ⁿ` for every `n` (`[yⁿ]B₂ = 0` for `n < 2`).

Writing `bₙ = [yⁿ]B₂ ∈ ℚ` for `n ≥ 2`, the successive ratio is
`b_{n+1}/b_n = (n-1)/(2(2n+1)) = (n-1)(n+1)/((2n+1)(2n+2)) ≤ 1/4`,
so `bₙ ≤ (1/6)·4^{2-n} ≤ 3·4^{-n}`.  Everything is carried out over `ℚ` and transferred to `ℂ`
at the end.
-/

namespace Work.CPull

open PowerSeries

noncomputable section

/-- The coefficients of `B₂` are nonnegative rationals. -/
private lemma b2_nonneg (n : ℕ) : 0 ≤ Submission.CDT.PureDenom.b2 n := by
  rw [Submission.CDT.PureDenom.b2]
  split_ifs with h
  · norm_num
  · positivity

/-- Successive-ratio formula for the coefficients of `B₂`, valid for `n ≥ 2`:
`b_{n+1} = b_n · (n-1)/(2(2n+1))`. -/
private lemma b2_succ_ratio (n : ℕ) (hn : 2 ≤ n) :
    Submission.CDT.PureDenom.b2 (n+1) =
      Submission.CDT.PureDenom.b2 n * ((n:ℚ)-1) / (2*(2*(n:ℚ)+1)) := by
  rw [Submission.CDT.PureDenom.b2, Submission.CDT.PureDenom.b2]
  simp only [if_neg (by omega : ¬ (n+1) < 2), if_neg (by omega : ¬ n < 2)]
  have h1 : n + 1 - 2 = n - 1 := by omega
  have h2 : 2 * (n+1) = 2 * n + 2 := by omega
  rw [h1, h2]
  have e1 : (↑(n+1).factorial : ℚ) = ((n:ℚ)+1) * ↑n.factorial := by
    have h := Submission.CDT.PureDenom.factorial_succ_cast (n+1) (by omega)
    have : (n+1-1) = n := by omega
    rw [this] at h
    have : ((n+1 : ℕ) : ℚ) = (n:ℚ)+1 := by push_cast; ring
    rw [this] at h; exact h
  have e2 : (↑(n-1).factorial : ℚ) = ((n:ℚ)-1) * ↑(n-2).factorial := by
    have h := Submission.CDT.PureDenom.factorial_succ_cast (n-1) (by omega)
    have hh : (n-1-1) = n-2 := by omega
    rw [hh] at h
    have : ((n-1 : ℕ) : ℚ) = (n:ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
    rw [this] at h; exact h
  have e3 : (↑(2*n+2).factorial : ℚ) = (2*(n:ℚ)+2) * ↑(2*n+1).factorial := by
    have h := Submission.CDT.PureDenom.factorial_succ_cast (2*n+2) (by omega)
    have hh : (2*n+2-1) = 2*n+1 := by omega
    rw [hh] at h
    have : ((2*n+2 : ℕ) : ℚ) = 2*(n:ℚ)+2 := by push_cast; ring
    rw [this] at h; exact h
  have e4 : (↑(2*n+1).factorial : ℚ) = (2*(n:ℚ)+1) * ↑(2*n).factorial := by
    have h := Submission.CDT.PureDenom.factorial_succ_cast (2*n+1) (by omega)
    have hh : (2*n+1-1) = 2*n := by omega
    rw [hh] at h
    have : ((2*n+1 : ℕ) : ℚ) = 2*(n:ℚ)+1 := by push_cast; ring
    rw [this] at h; exact h
  rw [e1, e2, e3, e4]
  field_simp

/-- The geometric bound `bₙ ≤ 3·(1/4)ⁿ` for `n ≥ 2`, by induction from `b₂ = 1/6 ≤ 3/16`
using `b_{n+1} = b_n·(n-1)/(2(2n+1)) ≤ b_n/4`. -/
private lemma b2_le_ge_two : ∀ n ≥ 2, Submission.CDT.PureDenom.b2 n ≤ 3 * (1/4:ℚ)^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [Submission.CDT.PureDenom.b2]
  | succ n hn ih =>
    have hratio := b2_succ_ratio n hn
    have hb2n : 0 ≤ Submission.CDT.PureDenom.b2 n := b2_nonneg n
    have hle : ((n:ℚ)-1)/(2*(2*(n:ℚ)+1)) ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity : (0:ℚ) < 2*(2*(n:ℚ)+1))]
      nlinarith [show (0:ℚ) ≤ (n:ℚ) from Nat.cast_nonneg n]
    calc Submission.CDT.PureDenom.b2 (n+1)
        = Submission.CDT.PureDenom.b2 n * (((n:ℚ)-1)/(2*(2*(n:ℚ)+1))) := by rw [hratio]; ring
      _ ≤ Submission.CDT.PureDenom.b2 n * (1/4) := mul_le_mul_of_nonneg_left hle hb2n
      _ ≤ (3*(1/4:ℚ)^n) * (1/4) := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = 3*(1/4:ℚ)^(n+1) := by rw [pow_succ]; ring

/-- The coefficient bound `bₙ ≤ 3·(1/4)ⁿ` over `ℚ`, all `n`. -/
private lemma b2_le (n : ℕ) : Submission.CDT.PureDenom.b2 n ≤ 3 * (1/4:ℚ)^n := by
  rcases lt_or_ge n 2 with h | h
  · rw [Submission.CDT.PureDenom.b2, if_pos h]; positivity
  · exact b2_le_ge_two n h

/-- `PowerSeries.coeff n B₂` agrees with the pure-denominator spelling `PureDenom.b2`. -/
private lemma coeff_B2 (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B2 = Submission.CDT.PureDenom.b2 n := by
  rw [Submission.CDTPlan.B2, PowerSeries.coeff_mk, Submission.CDT.PureDenom.b2]
  split_ifs with h
  · rfl
  · ring

/-- The coefficient bound, as a real inequality after the `ℚ → ℝ → ℂ` cast. -/
private lemma coeff_B2_abs_le (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ 3 * (1/4 : ℝ) ^ n := by
  rw [coeff_B2 n]
  have h1 : ((Submission.CDT.PureDenom.b2 n : ℚ) : ℂ) =
      (((Submission.CDT.PureDenom.b2 n : ℚ) : ℝ) : ℂ) := by push_cast; norm_num
  rw [h1]
  have h2 : ‖(((Submission.CDT.PureDenom.b2 n : ℚ) : ℝ) : ℂ)‖ =
      ((Submission.CDT.PureDenom.b2 n : ℚ) : ℝ) := by
    have hnrm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by simp
    rw [hnrm]
    exact abs_of_nonneg (by exact_mod_cast b2_nonneg n)
  rw [h2]
  have hval : ((3 * (1/4:ℚ)^n : ℚ) : ℝ) = 3 * (1/4:ℝ)^n := by push_cast; norm_num
  rw [← hval]
  exact_mod_cast b2_le n

theorem B2_coeff_bound :
    ∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ 3 * (1 / 4 : ℝ) ^ n :=
  fun n => coeff_B2_abs_le n

end

end Work.CPull
