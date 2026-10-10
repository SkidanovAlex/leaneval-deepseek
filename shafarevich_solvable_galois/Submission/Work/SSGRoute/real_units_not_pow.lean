import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Prime.Basic
import Submission.Work.SSGRoute.exists_sign_mul_pow_eq_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **A unit of `ℝ` which is not a `p`-th power of a unit is negative and `p = 2`.**

Let `p` be prime and `x ∈ ℝˣ`.  If `x` is not the `p`-th power of any unit of `ℝ`, then `p = 2` and
`x < 0` as a real number. -/
theorem real_units_not_pow (p : ℕ) [Fact p.Prime] (x : ℝˣ)
    (hx : ¬ ∃ y : ℝˣ, y ^ p = x) : p = 2 ∧ (x : ℝ) < 0 := by
  obtain ⟨s, y, hs, hxy⟩ := exists_sign_mul_pow_eq_real p x
  -- the sign is not `1`, otherwise `x` would itself be a `p`-th power
  have hsneg : s = -1 := by
    rcases hs with h | h
    · exact absurd ⟨y, by rw [← hxy, h, one_mul]⟩ hx
    · exact h
  -- numerical identity: `x = - y ^ p`
  have hval : (x : ℝ) = - ((y : ℝ) ^ p) := by
    have h := congrArg (fun u : ℝˣ => (u : ℝ)) hxy
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
    rw [hsneg] at h
    simp at h
    linarith
  rcases (Fact.out (p := p.Prime)).eq_two_or_odd with h2 | hodd
  · rw [h2] at hval
    refine ⟨h2, ?_⟩
    have hy : (y : ℝ) ≠ 0 := Units.ne_zero y
    have hpos : (0:ℝ) < (y:ℝ)^2 := sq_pos_of_ne_zero hy
    linarith
  · -- odd `p`: then `x = (-y) ^ p` is a `p`-th power, contradiction
    exact absurd ⟨-y, by
      rw [Units.ext_iff]
      simp only [Units.val_pow_eq_pow_val, Units.val_neg]
      rw [Odd.neg_pow (Nat.odd_iff.mpr hodd)]
      exact hval.symm⟩ hx

end Work.SSGRoute
