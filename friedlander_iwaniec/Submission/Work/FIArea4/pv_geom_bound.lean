import Mathlib
import Submission.Work.FIArea4.geom_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

/-- Geometric-series bound for the standard additive character of `ZMod q`: for `j ≠ 0` the
element `z = ZMod.stdAddChar j` is a root of unity different from `1`, so
`‖∑_{n=1}^{X} z ^ n‖ ≤ 2 / ‖z - 1‖`. -/
theorem pv_geom_bound {q : ℕ} [NeZero q] (j : ZMod q) (hj : j ≠ 0) (X : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 X, ZMod.stdAddChar (j * (n : ZMod q))‖
      ≤ 2 / ‖ZMod.stdAddChar j - 1‖ := by
  have hpow : ∀ n : ℕ, ZMod.stdAddChar (j * (n : ZMod q)) = (ZMod.stdAddChar j) ^ n := by
    intro n
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [Finset.sum_congr rfl (fun n _ => hpow n)]
  apply geom_sum_bound X
  · intro h
    have h0 : ZMod.stdAddChar (0 : ZMod q) = 1 := AddChar.map_zero_eq_one _
    rw [← h] at h0
    exact hj (ZMod.injective_stdAddChar h0).symm
  · rw [ZMod.stdAddChar_apply, Circle.norm_coe]

end Work.FIArea4
