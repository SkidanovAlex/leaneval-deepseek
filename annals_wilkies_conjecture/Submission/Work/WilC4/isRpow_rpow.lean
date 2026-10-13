import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- Over `ℝ`, the `LRc`-definable relation `IsRpow` holds at the genuine real power: for `x > 0`
and `q : ℚ`, the witness is `t = x ^ (q : ℝ)`, presented as `t ^ n = x ^ p` with `p = q.num`,
`n = q.den` (so that `q = p / n`), together with the positivity `t = 0 ∨ ∃ w ≠ 0, w ^ 2 = t`. -/
theorem isRpow_rpow {x : ℝ} (hx : 0 < x) (q : ℚ) : Work.WilC4.IsRpow x q (x ^ (q : ℝ)) := by
  refine ⟨q.num, q.den, q.den_pos, (Rat.num_div_den q).symm, ?_, ?_⟩
  · -- `(x ^ q) ^ q.den = x ^ q.num`
    have h1 : (q : ℚ) * (q.den : ℚ) = (q.num : ℚ) := by
      have h := Rat.num_div_den q
      rw [div_eq_iff (by exact_mod_cast (ne_of_gt q.den_pos))] at h
      exact h.symm
    have hqx : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast h1
    calc (x ^ (q : ℝ)) ^ q.den
        = (x ^ (q : ℝ)) ^ (q.den : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ ((q : ℝ) * (q.den : ℝ)) := (Real.rpow_mul hx.le _ _).symm
      _ = x ^ (q.num : ℝ) := by rw [hqx]
      _ = x ^ q.num := Real.rpow_intCast _ _
  · -- `x ^ q` is a nonzero square
    right
    exact ⟨Real.sqrt (x ^ (q : ℝ)),
      ne_of_gt (Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hx _)),
      Real.sq_sqrt (Real.rpow_nonneg hx.le _)⟩

end Work.WilC4
