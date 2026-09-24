import Mathlib
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

/-- GM, proof of Prop 7.1: "the inner integral vanishes unless `v₁ ∈ [1/2,2]` and `v₂ ∈ [1/2,2]`".
Here `pbox = Set.Icc (1/2:ℝ) 2 ×ˢ Set.Icc (1/2:ℝ) 2` and
`innerInt N m v = ∫ e(-N(m₁v₁+m₂v₂+m₃)u₃) w₂(u₃,v) du₃`, `w₂(u₃,v) = u₃²w(u₃)²w(v₁u₃)²w(v₂u₃)²`.

Proof route: show the integrand is *identically* zero for `u₃` arbitrary. If `w(u₃) ≠ 0` then
`u₃ ∈ [1,2]`; if moreover `v₁ ∉ [1/2,2]` then `v₁u₃ ∉ [1,2]` (check `v₁ ≤ 0`, `0 < v₁ < 1/2`,
`v₁ > 2`), so `w(v₁u₃) = 0`.  The helper `Work.GM.S3.w2v_eq_zero_of_not_mem` in
`Work.GM.S3.prop71_defs` does exactly this (it needs `v ∉ pbox` unfolded to a disjunction). -/
theorem prop71_inner_support (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ) (hv : v ∉ pbox) :
    innerInt N m v = 0 := by
  have hv' : v.1 ∉ Set.Icc (1 / 2 : ℝ) 2 ∨ v.2 ∉ Set.Icc (1 / 2 : ℝ) 2 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hv (by rw [pbox]; exact h)
  unfold innerInt
  have hzero : (fun u : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) * w2v v u)
      = fun _ => (0 : ℂ) := by
    funext u
    rw [w2v_eq_zero_of_not_mem hv', mul_zero]
  rw [hzero]
  simp

end Work.GM.S3
