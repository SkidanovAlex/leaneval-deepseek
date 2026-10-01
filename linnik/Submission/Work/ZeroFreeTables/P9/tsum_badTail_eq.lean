import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-- Absolute convergence of the von Mangoldt series with a real power weight:
`∑_n Λ(n) · n^{-σ} · (log n)^j` converges for `σ > 1` and any `j`. -/
theorem summable_vonMangoldt_rpow_log {σ : ℝ} (hσ : 1 < σ) (j : ℕ) :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j) := by
  refine (Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hσ j).congr (fun n => ?_)
  rw [div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n)]
  ring

/-- Absolute convergence of the "bad" (non-coprime to `q`) von Mangoldt tail with a
logarithmic-power weight: `∑_n 1_{¬(n,q)=1} Λ(n) n^{-σ} (log n)^j`. -/
theorem summable_tailSummand (q : ℕ) {σ : ℝ} (hσ : 1 < σ) (j : ℕ) :
    Summable (fun n : ℕ => tailSummand q σ j n) := by
  have h := (summable_vonMangoldt_rpow_log hσ j).norm
  refine Summable.of_norm_bounded h (fun n => ?_)
  have hb : ‖(if Nat.Coprime n q then (0:ℝ) else 1)‖ ≤ 1 := by split <;> simp
  have heq : tailSummand q σ j n
      = (if Nat.Coprime n q then (0:ℝ) else 1)
        * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j) := by
    rw [tailSummand]; ring
  rw [heq]
  calc ‖(if Nat.Coprime n q then (0:ℝ) else 1)
        * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j)‖
      ≤ ‖(if Nat.Coprime n q then (0:ℝ) else 1)‖
        * ‖(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log n) ^ j‖ :=
        one_mul _

theorem tsum_badTail_eq (q : ℕ) [NeZero q] {σ : ℝ} (hσ : 1 < σ) (a lam₁ L : ℝ) :
    (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Work.ZeroFreeTables.hbWL L a lam₁ n) = (a + lam₁) * (∑' n : ℕ, Work.ZeroFreeTables.P9.tailSummand q σ 0 n) + ((a + lam₁)^2 / L) * (∑' n : ℕ, Work.ZeroFreeTables.P9.tailSummand q σ 1 n) + (1/3) * ((a + lam₁)^3 / L^2) * (∑' n : ℕ, Work.ZeroFreeTables.P9.tailSummand q σ 2 n) := by
  have h0 := summable_tailSummand q hσ 0
  have h1 := summable_tailSummand q hσ 1
  have h2 := summable_tailSummand q hσ 2
  have hA : Summable (fun n : ℕ => tailSummand q σ 0 n * (a + lam₁)) := h0.mul_right _
  have hB : Summable (fun n : ℕ => tailSummand q σ 1 n * ((a + lam₁)^2 / L)) := h1.mul_right _
  have hC : Summable (fun n : ℕ => tailSummand q σ 2 n * ((1/3) * ((a + lam₁)^3 / L^2))) :=
    h2.mul_right _
  have key : (∑' n : ℕ, (if Nat.Coprime n q then (0:ℝ) else 1)
        * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        * Work.ZeroFreeTables.hbWL L a lam₁ n)
      = ∑' n : ℕ, (tailSummand q σ 0 n * (a + lam₁)
          + tailSummand q σ 1 n * ((a + lam₁)^2 / L)
          + tailSummand q σ 2 n * ((1/3) * ((a + lam₁)^3 / L^2))) :=
    tsum_congr (fun n => by
      simp only [Work.ZeroFreeTables.hbWL, tailSummand]
      ring)
  rw [key, Summable.tsum_add (hA.add hB) hC, Summable.tsum_add hA hB]
  simp only [tsum_mul_right]
  ring

end Work.ZeroFreeTables.P9
