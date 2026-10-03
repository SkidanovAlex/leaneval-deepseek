/-
# `Submission.Work.FIRed6Axis.NearMassDefs` — the numerical vocabulary of the near-axis mass bound

The *near-axis mass bound* (`Work.FIRed6Axis.NearMassBound`) bounds the `τ`-mass
`∑_{z ∈ T} τ(|z|²)` of a part `T` of the annulus `(N, 2N]` of squarefree norm lying within the
angular distance `4ϑ` of one of the four axes.  The `τ`-route runs through the divisor
localization: for squarefree `n`, `τ(n) ≤ 4 ∑_{d ∣ n, d³ ≤ n} τ(d)³`, so the mass is at most
`4 ∑_{d ≤ (2N)^{1/3}} τ(d)³ · #{z ∈ T : d ∣ |z|²}`.

The near zone is *axis-aligned*: by `nearArg_axis_transverse`, a `z` in the near zone satisfies
`|Im z| ≤ 4ϑ|z|` or `|Re z| ≤ 4ϑ|z|`, so `T` is contained in the union of the two axis-parallel
boxes

* `{|Re z| ≤ √(2N) , |Im z| ≤ 6ϑ√N}` and `{|Im z| ≤ √(2N) , |Re z| ≤ 6ϑ√N}`,

of side lengths `(2√(2N), 12ϑ√N)` and its transpose — a *radial* side `≍ √N` and a *transverse*
side `≍ ϑ√N`, which is what makes the box count `(2√(2N)/d + 1)(12ϑ√N/d + 1)·ρ(d)`
(`Work.FIRed6Axis.card_box_dvd_gnorm_le`) sum to `ϑN (log)^{O(1)}` rather than `N (log)^{O(1)}`.

This file contains only the three numerical quantities (`nearMassX`, `nearBoxR`, `nearBoxT`)
together with their elementary bounds, so that the pieces can be stated in a common vocabulary.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

noncomputable section

/-- **The `d`-cutoff** `⌈(2N)^{1/3}⌉` of the `τ`-localization: every divisor `d` with `d³ ≤ |z|²`
for some `z` of norm `≤ 2N` satisfies `d ≤ nearMassX N`. -/
def nearMassX (N : ℝ) : ℕ := ⌈(2 * N) ^ ((1 : ℝ) / 3)⌉₊

/-- **The radial half-side** `√(2N)` of the near-axis box: `|Re z| ≤ √(2N)` for every `z` of
norm `≤ 2N`. -/
def nearBoxR (N : ℝ) : ℝ := Real.sqrt (2 * N)

/-- **The transverse half-side** `6ϑ√N` of the near-axis box: from `nearArg (4ϑ) z` and
`|z|² ≤ 2N` one gets `|Im z| ≤ 4ϑ|z| ≤ 4√2 ϑ√N ≤ 6ϑ√N` (or the same with `Re`). -/
def nearBoxT (ϑ N : ℝ) : ℝ := 6 * ϑ * Real.sqrt N

lemma nearMassX_le_rpow (N : ℝ) (hN : 1 ≤ N) :
    (nearMassX N : ℝ) ≤ 2 * (2 * N) ^ ((1 : ℝ) / 3) := by
  have h2N : (0 : ℝ) < 2 * N := by linarith
  have hx1 : (1 : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hceil : (nearMassX N : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 3) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  linarith

lemma le_nearMassX {N : ℝ} (hN : 0 ≤ N) {d : ℕ} (hd : (d : ℝ) ^ 3 ≤ 2 * N) :
    d ≤ nearMassX N := by
  have h2N : (0 : ℝ) ≤ 2 * N := by linarith
  have hd3 : (d : ℝ) ^ (3 : ℝ) ≤ 2 * N := by
    have h : (d : ℝ) ^ (3 : ℝ) = (d : ℝ) ^ 3 := by norm_num
    rw [h]; exact hd
  have key : ((d : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (d : ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  have h1 : (d : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 3) := by
    rw [← key]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg d) 3) hd3 (by norm_num)
  have h2 : (d : ℝ) ≤ (nearMassX N : ℝ) := le_trans h1 (Nat.le_ceil _)
  exact_mod_cast h2

lemma nearBoxR_nonneg (N : ℝ) : 0 ≤ nearBoxR N := Real.sqrt_nonneg _

lemma nearBoxT_nonneg (ϑ N : ℝ) (hϑ : 0 ≤ ϑ) : 0 ≤ nearBoxT ϑ N := by
  rw [nearBoxT]
  exact mul_nonneg (mul_nonneg (by norm_num) hϑ) (Real.sqrt_nonneg N)

/-- `2√(2N) ≤ 3√N`: the radial side of the near-axis box has length `≍ √N`. -/
lemma two_mul_nearBoxR_le (N : ℝ) (hN : 1 ≤ N) : 2 * nearBoxR N ≤ 3 * Real.sqrt N := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    have h : Real.sqrt 2 ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt (9 / 4 : ℝ) = 3 / 2 from by
      rw [show (9/4 : ℝ) = (3/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  rw [nearBoxR, hsq]
  have hsn := Real.sqrt_nonneg N
  nlinarith

/-- The transverse side of the near-axis box is `12ϑ√N`. -/
lemma two_mul_nearBoxT (ϑ N : ℝ) : 2 * nearBoxT ϑ N = 12 * ϑ * Real.sqrt N := by
  rw [nearBoxT]; ring

/-- The area of the near-axis box: `4·√(2N)·6ϑ√N = 24√2 ϑN`. -/
lemma four_mul_nearBoxR_mul_nearBoxT (ϑ N : ℝ) (hN : 0 ≤ N) :
    4 * nearBoxR N * nearBoxT ϑ N = 24 * Real.sqrt 2 * ϑ * N := by
  have hsq : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hsqq : Real.sqrt N * Real.sqrt N = N := by
    have h := Real.sq_sqrt hN
    rw [pow_two] at h
    exact h
  rw [nearBoxR, nearBoxT, hsq]
  linear_combination (24 * Real.sqrt 2 * ϑ) * hsqq

end

end Work.FIRed6Axis
