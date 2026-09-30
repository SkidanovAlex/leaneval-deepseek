import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Abel summation (summation by parts): writing `A h = ∑ h' ∈ Icc 1 h, a h'` for the partial
sums of `a` starting at `1`, the weighted sum `∑ h ∈ Icc 1 L, a h * b h` equals
`A L * b L` minus the sum over `h ∈ range L` of `A h * (b (h + 1) - b h)`. -/
theorem abel_identity (L : ℕ) (a b : ℕ → ℂ) :
    ∑ h ∈ Finset.Icc 1 L, a h * b h =
      (∑ h ∈ Finset.Icc 1 L, a h) * b L -
        ∑ h ∈ Finset.range L, (∑ h' ∈ Finset.Icc 1 h, a h') * (b (h + 1) - b h) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (f := fun h => a h * b h),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) (f := a),
        Finset.sum_range_succ]
    rw [ih]
    ring

end Work.BMF
