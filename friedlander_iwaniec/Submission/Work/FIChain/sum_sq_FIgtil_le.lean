import Mathlib
import Submission.Work.FIChain.Defs

namespace Work.FIChain

/-- **The square-sum of the FI density is bounded.**  There is an absolute constant `C > 0` with

    ∑_{p < Δ} g̃(p)² ≤ C     for every `Δ : ℕ`.

Proof: `Submission.ASP.FIgtil_bound` gives `g̃(p) ≤ C₀/p` for every prime `p` (any `C₀ ≥ 4` works),
hence `g̃(p)² ≤ C₀²/p²`; `∑_n 1/n²` converges (`Real.summable_one_div_nat_pow`,
`Summable.sum_le_tsum`) and a finite sum over `Nat.primesBelow Δ` is at most the full `tsum`. -/
theorem sum_sq_FIgtil_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℕ,
      (∑ p ∈ Nat.primesBelow Δ, (Submission.ASP.FIgtil p) ^ 2) ≤ C := by
  obtain ⟨C0, hC0pos, hC0⟩ := Submission.ASP.FIgtil_bound
  have hsumm0 : Summable (fun n : ℕ => (1 / (n : ℝ)) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa [one_div, inv_pow] using h
  have hsummg : Summable (fun n : ℕ => (C0 / (n : ℝ)) ^ 2) := by
    have h2 := hsumm0.mul_left (C0 ^ 2)
    refine h2.congr (fun n => ?_)
    rw [div_pow]; ring
  have htsum_nonneg : 0 ≤ ∑' n : ℕ, (1 / (n : ℝ)) ^ 2 := tsum_nonneg (fun n => by positivity)
  have hCpos : 0 < C0 ^ 2 * (∑' n : ℕ, (1 / (n : ℝ)) ^ 2) + 1 := by
    have := mul_nonneg (pow_pos hC0pos 2).le htsum_nonneg
    linarith
  refine ⟨C0 ^ 2 * (∑' n : ℕ, (1 / (n : ℝ)) ^ 2) + 1, hCpos, fun Δ => ?_⟩
  have hterm : ∀ p ∈ Nat.primesBelow Δ, (Submission.ASP.FIgtil p) ^ 2 ≤ (C0 / (p : ℝ)) ^ 2 := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hle : Submission.ASP.FIgtil p ≤ C0 / (p : ℝ) := hC0 p hpp
    have hnn : 0 ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
    exact pow_le_pow_left₀ hnn hle 2
  have htsum_eq : (∑' n : ℕ, (C0 / (n : ℝ)) ^ 2)
      = C0 ^ 2 * (∑' n : ℕ, (1 / (n : ℝ)) ^ 2) := by
    rw [show (fun n : ℕ => (C0 / (n : ℝ)) ^ 2) = (fun n : ℕ => C0 ^ 2 * (1 / (n : ℝ)) ^ 2)
        from funext (fun n => by rw [div_pow]; ring)]
    rw [tsum_mul_left]
  calc
    (∑ p ∈ Nat.primesBelow Δ, (Submission.ASP.FIgtil p) ^ 2)
        ≤ ∑ p ∈ Nat.primesBelow Δ, (C0 / (p : ℝ)) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑' n : ℕ, (C0 / (n : ℝ)) ^ 2 :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) hsummg
    _ = C0 ^ 2 * (∑' n : ℕ, (1 / (n : ℝ)) ^ 2) := htsum_eq
    _ ≤ C0 ^ 2 * (∑' n : ℕ, (1 / (n : ℝ)) ^ 2) + 1 := by linarith

end Work.FIChain
