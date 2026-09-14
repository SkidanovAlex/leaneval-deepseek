import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Submission.Commons.Analysis.Interval.interior_argmax_of_zero_ends
import Submission.Commons.Analysis.Calculus.Deriv.deriv_deriv_nonpos_of_localMax

open Filter Set Topology

namespace Commons.Analysis.Calculus

/-- The second iterated derivative is the derivative of the derivative. -/
theorem iteratedDeriv_two_eq_deriv_deriv (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 f x = deriv (deriv f) x := by
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- Let `f` be continuous on `[a, b]`, vanish at `a` and `b`, be positive somewhere in the open
interval `(a, b)`, and be twice continuously differentiable on the region `{f > 0}`.  Then `f`
has a point of positive value in `(a, b)` at which its second derivative is non-positive.

Take an interior point `x₀` where `f` attains its maximum on `[a, b]`; it has positive value
(hence lies in the interior and in `{f > 0}`), so `f` is `C²` there and `x₀` is a local maximum.
At a local maximum of a `C²` function the second derivative is non-positive. -/
theorem exists_localMax_secondDeriv_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hpos : ∃ x ∈ Set.Ioo a b, 0 < f x)
    (hdiff : ContDiffOn ℝ 2 f {x : ℝ | 0 < f x}) :
    ∃ t ∈ Set.Ioo a b, 0 < f t ∧ iteratedDeriv 2 f t ≤ 0 := by
  -- an interior point where `f` attains its maximum on `[a, b]`
  obtain ⟨x₀, hx₀_ioo, hmax', _hsup⟩ :=
    Commons.Analysis.Interval.interior_argmax_of_zero_ends hab hcont ha hb hpos
  -- the maximum value is positive
  obtain ⟨t, ht_ioo, hft⟩ := hpos
  have hx₀_pos : 0 < f x₀ := lt_of_lt_of_le hft (hmax' t (Ioo_subset_Icc_self ht_ioo))
  -- `x₀` is a local maximum of `f`
  have hloc : IsLocalMax f x₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀_ioo] with y hy
    exact hmax' y (Ioo_subset_Icc_self hy)
  -- and `f` is `C²` at `x₀`, since `x₀ ∈ {f > 0}` and the latter is open
  have hcontAt : ContinuousAt f x₀ :=
    hcont.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx₀_ioo)
      Ioo_subset_Icc_self)
  have hnhds : {x : ℝ | 0 < f x} ∈ 𝓝 x₀ :=
    hcontAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx₀_pos)
  have hC2 : ContDiffAt ℝ 2 f x₀ := (hdiff.contDiffWithinAt hx₀_pos).contDiffAt hnhds
  -- the second derivative test at a local maximum
  have hsecond : deriv (deriv f) x₀ ≤ 0 :=
    Commons.Analysis.Calculus.Deriv.deriv_deriv_nonpos_of_localMax hC2 hloc
  exact ⟨x₀, hx₀_ioo, hx₀_pos, by rwa [iteratedDeriv_two_eq_deriv_deriv]⟩

end Commons.Analysis.Calculus