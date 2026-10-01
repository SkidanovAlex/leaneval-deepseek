/-
# Area 4 — a crude (polynomial in `X`) bound for `Ssm`

Given only the pointwise hypothesis `‖mollCoeff q U V W χ n‖ ≤ B·n`, the smoothed sum
`Ssm = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n/X}` (HB (11.6)–(11.8)) is bounded by

    ‖Ssm q U V W X χ ρ‖ ≤ B · (X+1)^3     (for `1 ≤ X`, `Re ρ ≥ 0`).

The proof splits the summand as `mollCoeff n · n^{-ρ} · e^{-n/X}`, notes
`‖n^{-ρ}‖ ≤ 1` (since `Re ρ ≥ 0`) and `‖e^{-n/X}‖ = r^n` with `r = e^{-1/X} ∈ [0,1)`,
and bounds the resulting geometric series `Σ_n B·n·r^n` via
`Σ' n, n·r^n ≤ (X+1)^2` (cf. `tsum_nat_mul_exp_neg_div_le`).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.norm_mollCoeff_cpow_exp_le
import Submission.Work.LinnikAreas.Density4.tsum_nat_mul_exp_neg_div_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

theorem Ssm_crude_bound (q : ℕ) [NeZero q] {U V W X : ℝ} (hU : 0 < U) (hX : 1 ≤ X)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hβ : 0 ≤ ρ.re) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ n : ℕ, ‖mollCoeff q U V W χ n‖ ≤ B * (n : ℝ)) :
    ‖Ssm q U V W X χ ρ‖ ≤ B * (X + 1) ^ 3 := by
  set r : ℝ := Real.exp (-(1 / X)) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff, neg_lt_zero]; positivity
  have hnormr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hrlt
  have hsum : Summable (fun n : ℕ => (n:ℝ) * r^n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnormr).summable
  have hBs : Summable (fun n : ℕ => B * (n:ℝ) * r^n) :=
    (hsum.mul_left B).congr (fun n => by ring)
  have hF : ∀ n : ℕ, ‖mollCoeff q U V W χ n * (n:ℂ)^(-ρ) * ((Real.exp (-(n:ℝ)/X):ℝ):ℂ)‖
      ≤ B * (n:ℝ) * r^n := by
    intro n
    have := norm_mollCoeff_cpow_exp_le q hU hX χ hβ hB hbound n
    simpa [hrdef] using this
  have hnormF : Summable (fun n : ℕ =>
      ‖mollCoeff q U V W χ n * (n:ℂ)^(-ρ) * ((Real.exp (-(n:ℝ)/X):ℝ):ℂ)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF hBs
  rw [Ssm_eq_tsum_mollCoeff]
  calc ‖∑' n : ℕ, mollCoeff q U V W χ n * (n:ℂ)^(-ρ) * ((Real.exp (-(n:ℝ)/X):ℝ):ℂ)‖
      ≤ ∑' n : ℕ, ‖mollCoeff q U V W χ n * (n:ℂ)^(-ρ) * ((Real.exp (-(n:ℝ)/X):ℝ):ℂ)‖ :=
        norm_tsum_le_tsum_norm hnormF
    _ ≤ ∑' n : ℕ, B * (n:ℝ) * r^n := Summable.tsum_le_tsum hF hnormF hBs
    _ = B * (∑' n : ℕ, (n:ℝ) * r^n) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun n => by ring)
    _ ≤ B * (X + 1)^2 := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        have := tsum_nat_mul_exp_neg_div_le X hX
        simpa [hrdef] using this
    _ ≤ B * (X + 1)^3 := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact pow_le_pow_right₀ (by linarith) (by norm_num)

end Work.LinnikAreas.Density4
