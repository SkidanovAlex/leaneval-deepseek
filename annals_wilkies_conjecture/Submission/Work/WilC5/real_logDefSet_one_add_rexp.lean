import Mathlib
import Submission.Work.WilC5.LogFunReal
import Submission.Work.WilC5.RealFacts
import Submission.Work.WilC5.LogDefSetModel

namespace Work.WilC5

/-- **`rexp` computes `1 + x` from `log(1 + x)` on `[-1/2, 1/2]`.**

This is the "inverse function" half of the restricted exponential: if `y` is the definable
logarithm of `1 + x` (so that `exp y = 1 + x` when `1 + x > 0`), and if `|2x| ≤ 1` — i.e.
`x ∈ [-1/2, 1/2]`, so that `1 + x ∈ [1/2, 3/2]` and `log(1+x) ∈ [-1, 1]` — then the restricted
exponential `rexpFromExp` (which is `exp` on `[-1,1]` and `0` outside, see `rexpFromExp_real`)
returns `1 + x`.

The case `1 + x ≤ 0` of `logDefSet` cannot occur under `|2x| ≤ 1`, and in the remaining case
`y = log(1 + x)` the bound `|log(1+x)| ≤ 1` follows from `log t ≤ t - 1`
(`Real.log_le_sub_one_of_pos`) applied at `t = 3/2` and at `t = 2`. -/
theorem real_logDefSet_one_add_rexp {x y : ℝ}
    (hy : Work.WilC5.logDefSet (Work.WilC5.addE Work.WilC5.oneE x) y)
    (hx : Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) x)) :
    Work.WilC5.rexpFromExp y = Work.WilC5.addE Work.WilC5.oneE x := by
  -- `|2 * x| ≤ 1`
  have hx' : |2 * x| ≤ 1 := by
    have h : mulE (addE oneE oneE) x = 2 * x := by
      rw [mulE_real, addE_real, oneE_real]; norm_num
    rw [h, absLeOne_real] at hx
    exact hx
  -- hence `|x| ≤ 1/2` and `1/2 ≤ 1 + x ≤ 3/2`
  have hxabs : |x| ≤ 1/2 := by
    rw [abs_mul] at hx'; norm_num at hx'; linarith
  have hge : 1/2 ≤ 1 + x := by linarith [neg_abs_le x]
  have hle : 1 + x ≤ 3/2 := by linarith [le_abs_self x]
  have hpos : 0 < 1 + x := by linarith
  -- describe `y` through the graph of the logarithm
  have hy' : logDefSet (1 + x) y := by
    have h : addE oneE x = 1 + x := by rw [addE_real, oneE_real]
    rwa [h] at hy
  rw [logDefSet_real] at hy'
  rcases hy' with ⟨_, hyeq⟩ | ⟨hle', _⟩
  · -- `y = log (1 + x)`, and `|log (1 + x)| ≤ 1`
    have habs : |y| ≤ 1 := by
      rw [hyeq, abs_le]
      constructor
      · have h1 : Real.log (1/2) ≤ Real.log (1 + x) := Real.log_le_log (by norm_num) hge
        have h2 : Real.log (1/2 : ℝ) = - Real.log 2 := by
          rw [show (1/2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
        have h3 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
          linarith
        linarith
      · have h1 : Real.log (1 + x) ≤ Real.log (3/2) := Real.log_le_log (by linarith) hle
        have h2 : Real.log (3/2 : ℝ) ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3/2)
          linarith
        linarith
    rw [rexpFromExp_real, WilkiesDesign.rexp, ite_eq_left habs, hyeq, Real.exp_log hpos]
    rw [addE_real, oneE_real]
  · -- `1 + x ≤ 0` contradicts `1/2 ≤ 1 + x`
    exfalso; linarith

end Work.WilC5
