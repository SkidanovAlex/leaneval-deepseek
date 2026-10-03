import Mathlib

namespace Work.Pert.Lattice

/-- If `α * w` is at positive distance from the lattice `ℤ ⊂ ℂ`, then
`exp (-(2 π i α w)) ≠ 1`.  Indeed `exp x = 1` forces `x ∈ 2 π i ℤ`, so
`-(2 π i α w) = 2 π i n` gives `α * w = -n ∈ ℤ`, contradicting the strict
positivity of the infimum of the distances (which is `≤ 0` on `ℤ`). -/
theorem exp_neg_two_pi_I_mul_ne_one_of_lattice_pos {α w : ℂ}
    (hd : 0 < ⨅ k : ℤ, dist (α * w) (k : ℂ)) :
    Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 := by
  intro h
  -- `exp x = 1` forces `x` to be an integer multiple of `2 π i`
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  -- cancel the factor `2 π i`: the hypothesis becomes `α * w = -n`
  have key : (2 * Real.pi * Complex.I : ℂ) * (α * w)
      = (2 * Real.pi * Complex.I : ℂ) * (-(↑n : ℂ)) := by
    linear_combination -hn
  have hz : α * w = ((-n : ℤ) : ℂ) := by
    rw [Int.cast_neg]
    exact mul_left_cancel₀ hc key
  -- hence the distance to the `(-n)`-th lattice point vanishes, so the
  -- infimum of the distances is `≤ 0`, contradicting `hd`
  have hzero : dist (α * w) (((-n : ℤ)) : ℂ) = 0 := by rw [hz, dist_self]
  have hle : (⨅ k : ℤ, dist (α * w) (k : ℂ)) ≤ dist (α * w) (((-n : ℤ)) : ℂ) :=
    ciInf_le (f := fun k : ℤ => dist (α * w) (k : ℂ))
      ⟨0, by rintro _ ⟨k, rfl⟩; exact dist_nonneg⟩ (-n)
  exact (not_lt_of_ge (hle.trans_eq hzero)) hd

end Work.Pert.Lattice
