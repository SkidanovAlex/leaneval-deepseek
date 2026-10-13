import Mathlib
import Submission.Work.WilC4.isRpow_canon
import Submission.Work.WilC4.isRpow_rpow

namespace Work.WilVP

/-- The `IsRpow` witness is the genuine real power: for `x > 0` there is only one nonnegative
`n`-th root.  (`Work.WilC4.isRpow_canon` gives `t ^ n = x ^ p` with `t ≥ 0`; then
`t = (x^(q:ℝ))` using `Real.rpow_mul`/`rpow_natCast`.) -/
theorem isRpow_eq_rpow {x t : ℝ} {q : ℚ} (hx : 0 < x) (h : Work.WilC4.IsRpow x q t) :
    t = x ^ (q : ℝ) := by
  -- Present `q` with its canonical numerator and denominator, `q = q.num / q.den`.
  rw [← Rat.num_div_den q] at h
  have hcanon := (Work.WilC4.isRpow_canon q.den_pos hx).mp h
  -- `t` is `0` or a nonzero square, hence nonnegative.
  have ht_nonneg : 0 ≤ t := by
    rcases hcanon.2 with h0 | ⟨w, _hw, hw2⟩
    · rw [h0]
    · rw [← hw2]; exact sq_nonneg w
  have hxq_nonneg : 0 ≤ x ^ (q : ℝ) := Real.rpow_nonneg hx.le _
  -- `q * q.den = q.num`, hence `(x^q) ^ q.den = x ^ q.num`.
  have hnum : (q : ℚ) * (q.den : ℚ) = (q.num : ℚ) := by
    have h := Rat.num_div_den q
    rw [div_eq_iff (by exact_mod_cast (ne_of_gt q.den_pos))] at h
    exact h.symm
  have hqx : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast hnum
  have hrpow : (x ^ (q : ℝ)) ^ q.den = x ^ q.num := by
    calc (x ^ (q : ℝ)) ^ q.den
        = (x ^ (q : ℝ)) ^ (q.den : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ ((q : ℝ) * (q.den : ℝ)) := (Real.rpow_mul hx.le _ _).symm
      _ = x ^ (q.num : ℝ) := by rw [hqx]
      _ = x ^ q.num := Real.rpow_intCast _ _
  -- Both `t` and `x^q` are nonnegative and have the same `q.den`-th power.
  exact (pow_left_inj₀ ht_nonneg hxq_nonneg (Nat.pos_iff_ne_zero.mp q.den_pos)).mp
    (by rw [hcanon.1, hrpow])

end Work.WilVP
