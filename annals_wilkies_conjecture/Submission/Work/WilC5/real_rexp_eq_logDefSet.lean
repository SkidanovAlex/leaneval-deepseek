import Mathlib
import Submission.Work.WilC5.logFun_one_add_rexp

namespace Work.WilC5

theorem real_rexp_eq_logDefSet {x y : ℝ}
    (hy : Work.WilC5.rexpFromExp y = Work.WilC5.addE Work.WilC5.oneE x)
    (hx : Work.WilC5.absLeOne (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) x)) :
    Work.WilC5.logDefSet (Work.WilC5.addE Work.WilC5.oneE x) y := by
  -- `|2 * x| ≤ 1`
  have hx2 : |2 * x| ≤ 1 := by
    have h : mulE (addE oneE oneE) x = 2 * x := by
      rw [mulE_real, addE_real, oneE_real]; norm_num
    rw [h, absLeOne_real] at hx
    exact hx
  -- hence `|x| ≤ 1/2` and `1/2 ≤ 1 + x ≤ 3/2`, in particular `1 + x > 0`
  have hxabs : |x| ≤ 1 / 2 := by
    rw [abs_mul] at hx2; norm_num at hx2; linarith
  have hge : 1 / 2 ≤ 1 + x := by linarith [neg_abs_le x]
  have hpos : 0 < 1 + x := by linarith
  -- `rexpFromExp y = 1 + x`
  have hy' : rexpFromExp y = 1 + x := by rw [hy, addE_real, oneE_real]
  -- the `else` branch `0` is impossible, so `|y| ≤ 1` and `exp y = 1 + x`
  have hyl : absLeOne y := by
    by_contra h
    rw [rexpFromExp_of_not_absLeOne h, zeroE_real] at hy'
    linarith
  have hexp : expE y = 1 + x := by
    rw [← rexpFromExp_of_absLeOne hyl]; exact hy'
  -- the graph of the logarithm: `1 + x > 0` and `exp y = 1 + x`, so `y = log (1 + x)`
  have hae : addE oneE x = 1 + x := by rw [addE_real, oneE_real]
  rw [hae, logDefSet_real]
  refine Or.inl ⟨hpos, ?_⟩
  have hexp' : Real.exp y = 1 + x := by rw [← expE_real, hexp]
  rw [← Real.log_exp y, hexp']

end Work.WilC5
