import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.moebius_mul_selTheta_real
import Submission.Work.LinnikAreas.Density4.coprime_indicator_moebius
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

noncomputable section

/-- Recursion for the coprime Mertens-type sum: expanding the coprime indicator
`[(m,r)=1] = Σ_{d | (m,r)} μ(d)` and reindexing `m = d*k` gives
`Θ(Q,r) = Σ_{d | r} (μ(d)²/d) Θ(Q/d, d)`, valid for all real `Q` and all `r ≥ 1`. -/
theorem selTheta_recursion (Q : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    selTheta Q r = ∑ d ∈ r.divisors,
      ((ArithmeticFunction.moebius d : ℝ))^2 / (d:ℝ) * selTheta (Q/(d:ℝ)) d := by
  classical
  -- Step 1: expand the coprimality indicator by Möbius inversion and swap the two sums.
  have hmain : selTheta Q r
      = ∑ d ∈ r.divisors, ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
          if d ∣ m then (ArithmeticFunction.moebius d : ℝ)
            * ((ArithmeticFunction.moebius m : ℝ) * Real.log (Q / (m : ℝ)) / (m : ℝ)) else 0 := by
    rw [selTheta, Finset.sum_filter]
    calc ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (if Nat.Coprime m r then
              (ArithmeticFunction.moebius m : ℝ) * Real.log (Q / (m : ℝ)) / (m : ℝ) else 0)
        = ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ d ∈ r.divisors,
            (if d ∣ m then (ArithmeticFunction.moebius d : ℝ)
              * ((ArithmeticFunction.moebius m : ℝ) * Real.log (Q / (m : ℝ)) / (m : ℝ)) else 0) :=
          Finset.sum_congr rfl (fun m _ => coprime_indicator_moebius m r hr _)
      _ = ∑ d ∈ r.divisors, ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
            (if d ∣ m then (ArithmeticFunction.moebius d : ℝ)
              * ((ArithmeticFunction.moebius m : ℝ) * Real.log (Q / (m : ℝ)) / (m : ℝ)) else 0) :=
          Finset.sum_comm
  rw [hmain]
  -- Step 2: for each `d ∣ r`, reindex `m = d*k` and recognise `Θ(Q/d, d)`.
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd1 : 1 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
  have hinn : (∑ m ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun m => d ∣ m),
        (ArithmeticFunction.moebius m : ℝ) * Real.log (Q / (m : ℝ)) / (m : ℝ))
      = (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * selTheta (Q / (d : ℝ)) d := by
    rw [sum_Icc_filter_dvd_reindex ⌊Q⌋₊ d hd1]
    calc ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (ArithmeticFunction.moebius (d * k) : ℝ)
            * Real.log (Q / ((d * k : ℕ) : ℝ)) / ((d * k : ℕ) : ℝ)
        = ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (1 / (d : ℝ))
            * ((ArithmeticFunction.moebius (d * k) : ℝ)
                * Real.log ((Q / (d : ℝ)) / (k : ℝ)) / (k : ℝ)) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hkr : (k : ℝ) ≠ 0 := by
            have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
            exact this.ne'
          rw [Nat.cast_mul, ← div_div]
          field_simp
      _ = (1 / (d : ℝ)) * ∑ k ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (ArithmeticFunction.moebius (d * k) : ℝ) * Real.log ((Q / (d : ℝ)) / (k : ℝ)) / (k : ℝ) := by
          rw [Finset.mul_sum]
      _ = (1 / (d : ℝ)) * ((ArithmeticFunction.moebius d : ℝ) * selTheta (Q / (d : ℝ)) d) := by
          rw [moebius_mul_selTheta_real Q d hd1]
      _ = (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * selTheta (Q / (d : ℝ)) d := by ring
  rw [← Finset.sum_filter, ← Finset.mul_sum, hinn]
  ring

end

end Work.LinnikAreas.Density4
