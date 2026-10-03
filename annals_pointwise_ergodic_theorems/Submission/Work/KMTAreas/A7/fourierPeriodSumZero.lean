import Mathlib

namespace Work.KMTAreas.A7

/-- If `α : AddCircle 1` is a nonzero element of order dividing `q`, then the sum of the
Fourier characters of indices `n, n+1, …, n+q-1` at `α` vanishes: the summands form a
geometric progression of ratio `fourier 1 α = toCircle α`, which is a `q`-th root of unity
(by `q • α = 0`) different from `1` (by `α ≠ 0`). -/
theorem fourierPeriodSumZero (q : ℕ) (hq : 0 < q) (α : AddCircle (1 : ℝ))
    (hα : q • α = 0) (hne : α ≠ 0) (n : ℤ) :
    ∑ r ∈ Finset.range q, fourier (T := 1) (n + (r : ℤ)) α = 0 := by
  set z : ℂ := (AddCircle.toCircle α : ℂ) with hz
  -- `z` is a `q`-th root of unity.
  have hqpow : (AddCircle.toCircle α : Circle) ^ q = 1 := by
    rw [← AddCircle.toCircle_nsmul, hα, AddCircle.toCircle_zero]
  have hzq : z ^ q = 1 := by
    rw [hz, ← Circle.coe_pow, hqpow, Circle.coe_one]
  -- and `z ≠ 1` because `toCircle` is injective and `α ≠ 0`.
  have hz1 : z ≠ 1 := by
    intro h
    have h' : (AddCircle.toCircle α : ℂ) = 1 := by rw [← hz]; exact h
    have h'' : (AddCircle.toCircle α : Circle) = 1 := Circle.coe_eq_one.mp h'
    refine hne (AddCircle.injective_toCircle (T := 1) (by norm_num : (1 : ℝ) ≠ 0) ?_)
    rw [AddCircle.toCircle_zero]
    exact h''
  -- each summand is `fourier n α * z ^ r`.
  have hterm : ∀ r : ℕ,
      fourier (T := 1) (n + (r : ℤ)) α = fourier (T := 1) n α * z ^ r := by
    intro r
    have h2 : fourier (T := 1) (r : ℤ) α = z ^ r := by
      rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, zpow_natCast, ← hz]
    rw [fourier_add, h2]
  calc ∑ r ∈ Finset.range q, fourier (T := 1) (n + (r : ℤ)) α
      = ∑ r ∈ Finset.range q, fourier (T := 1) n α * z ^ r :=
        Finset.sum_congr rfl (fun r _ => hterm r)
    _ = fourier (T := 1) n α * ∑ r ∈ Finset.range q, z ^ r :=
        (Finset.mul_sum _ _ _).symm
    _ = fourier (T := 1) n α * ((z ^ q - 1) / (z - 1)) := by rw [geom_sum_eq hz1 q]
    _ = 0 := by rw [hzq, sub_self, zero_div, mul_zero]

end Work.KMTAreas.A7
