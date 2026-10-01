import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.LinnikAreas.Density4.vonMangoldt_mul_Bz_sum
import Submission.Work.LinnikAreas.Density4.prime_log_gap_sum

namespace Work.ZeroDensity.Jutila

open Finset

/-- **The mixed sum in Graham's range, upper bound.**  For `2 ≤ z ≤ N < z²`, the mixed sum
`∑_{n ≤ N} Λ(n) B_z(n)` equals `-∑_{z < p ≤ N} log p · log(p/z)` (this is
`Work.LinnikAreas.Density4.vonMangoldt_mul_Bz_sum`), so the prime-sum hypothesis `hPr` applied
at `(y, x) = (z, N)` gives the lower bound
`∑_{z < p ≤ N} log p · log(p/z) ≥ N log(N/z) - C2 · N`;
multiplying by `-2` and using `log(N/z) = log N - log z` yields the claim. -/
theorem MixedSumLe (C2 : ℝ)
    (hPr : ∀ (y x : ℝ), 1 ≤ y → y ≤ x →
      |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) - x * Real.log (x / y)| ≤ C2 * x)
    (z N : ℕ) (hz : 2 ≤ z) (hzN : z ≤ N) (hN : N < z * z) :
    2 * (∑ n ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt n * Work.LinnikAreas.Density4.Bz z n)
      ≤ -2 * ((N : ℝ) * (Real.log (N : ℝ) - Real.log (z : ℝ))) + 2 * C2 * (N : ℝ) := by
  have hsum := Work.LinnikAreas.Density4.vonMangoldt_mul_Bz_sum z N hz hzN hN
  have hzR1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hzNR : (z : ℝ) ≤ (N : ℝ) := by exact_mod_cast hzN
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hpred : ∀ p : ℕ, (Nat.Prime p ∧ (z : ℝ) < (p : ℝ)) ↔ (Nat.Prime p ∧ z < p) :=
    fun p => by simp only [Nat.cast_lt]
  have hset : (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ (z : ℝ) < (p : ℝ))
      = (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p) :=
    Finset.filter_congr (fun p _ => hpred p)
  have hPr' := hPr (z : ℝ) (N : ℝ) hzR1 hzNR
  have hPr'' : |(∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / (z : ℝ)))
      - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ C2 * (N : ℝ) := by
    simpa only [hfloor, hset] using hPr'
  have hlog : Real.log ((N : ℝ) / (z : ℝ)) = Real.log (N : ℝ) - Real.log (z : ℝ) := by
    rw [Real.log_div]
    · exact_mod_cast (by omega : N ≠ 0)
    · exact_mod_cast (by omega : z ≠ 0)
  have hS : (N : ℝ) * (Real.log (N : ℝ) - Real.log (z : ℝ)) - C2 * (N : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < p),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / (z : ℝ)) := by
    have h1 := (abs_le.mp hPr'').1
    rw [hlog] at h1
    linarith
  rw [hsum]
  linarith

end Work.ZeroDensity.Jutila
