import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.IcVolAux

namespace Work.HP.MM2

/-- `ι_{d,n} = V_{N-2}/(8 ζ(N-2))` is positive when `2 ≤ d ≤ n`.  `six_le_NN` gives
`6 ≤ NN d n`, hence `NN d n - 2 ≥ 4 ≥ 1`; `IcVolAux.ballVol_pos` gives `0 < ballVol (NN d n - 2)`
and the zeta sum `∑' k, 1/((k:ℝ)+1)^(NN d n - 2)` is positive (its `k = 0` term is `1`; use
`Summable.sum_le_tsum` with summability of `k ↦ 1/((k:ℝ)+1)^m` for `m ≥ 2`). -/
theorem iotaDN_pos (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have hN : 6 ≤ NN d n := six_le_NN d n hd hdn
  have h1 : 1 ≤ NN d n - 2 := by omega
  have h2 : 1 < NN d n - 2 := by omega
  have hball : 0 < ballVol (NN d n - 2) := ballVol_pos _ h1
  have hsumm : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (NN d n - 2)) := by
    have h := (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ (NN d n - 2)) 1).2
      (Real.summable_one_div_nat_pow.mpr h2)
    refine h.congr (fun k => ?_)
    push_cast
    ring_nf
  have hpos : 0 < ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2) := by
    refine Summable.tsum_pos hsumm (fun k => ?_) 0 (by norm_num)
    positivity
  unfold iotaDN
  exact div_pos hball (by positivity)

end Work.HP.MM2
