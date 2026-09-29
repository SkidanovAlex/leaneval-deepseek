import Mathlib

namespace Work.TMComp.MAnalytic

/-- Uniqueness of the invariant section of the (complexified) almost Mathieu section equation
`u x = z - 2λ cos(2π(x-α)) - 1/u (x-α)` among functions bounded below by `z.im/2` and above
by a finite constant `B`.

Writing `g x := z - 2λ cos(2π(x-α))` for the common inhomogeneity, the two solutions satisfy
`u x = g x - 1/u (x-α)` and `v x = g x - 1/v (x-α)`, hence for `w := u - v`
`w x = w (x-α) / (u (x-α) * v (x-α))`.  Since `‖u‖, ‖v‖ ≥ z.im/2 ≥ 2` the reciprocal factor
has norm at most `4/z.im² ≤ 1/4 < 1`, so `‖w x‖ ≤ c ‖w (x-α)‖` with `c < 1`.  Iterating and
using the global bound `‖w‖ ≤ 2B` gives `‖w x‖ ≤ c^n · 2B` for all `n`, and letting `n → ∞`
yields `w x = 0`. -/
theorem section_unique_real {α lam : ℝ} {z : ℂ} (hz : 4 ≤ z.im) :
    ∀ (B : ℝ) (u v : ℝ → ℂ),
      (∀ x, z.im / 2 ≤ ‖u x‖ ∧ ‖u x‖ ≤ B) →
      (∀ x, u x = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / u (x - α)) →
      (∀ x, z.im / 2 ≤ ‖v x‖ ∧ ‖v x‖ ≤ B) →
      (∀ x, v x = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / v (x - α)) →
      ∀ x, u x = v x := by
  intro B u v hu huf hv hvf x
  have hzpos : 0 < z.im := by linarith
  have hhalfpos : 0 < z.im / 2 := by linarith
  have hB : 0 < B := by
    have h1 := (hu 0).1
    have h2 := (hu 0).2
    linarith [norm_nonneg (u 0)]
  have hu_ne : ∀ y, u y ≠ 0 := by
    intro y hy
    have h1 := (hu y).1
    rw [hy, norm_zero] at h1
    linarith
  have hv_ne : ∀ y, v y ≠ 0 := by
    intro y hy
    have h1 := (hv y).1
    rw [hy, norm_zero] at h1
    linarith
  set c : ℝ := 4 / z.im ^ 2 with hc
  have hc_nn : 0 ≤ c := by rw [hc]; positivity
  have hc_lt : c < 1 := by
    rw [hc, div_lt_one (by positivity : (0:ℝ) < z.im ^ 2)]
    nlinarith
  -- the exact relation satisfied by the difference `w = u - v`
  have key : ∀ y, u y - v y = (u (y - α) - v (y - α)) / (u (y - α) * v (y - α)) := by
    intro y
    rw [huf y, hvf y]
    field_simp [hu_ne (y - α), hv_ne (y - α)]
    ring
  -- contraction with ratio `c < 1`
  have hstep : ∀ y, ‖u y - v y‖ ≤ c * ‖u (y - α) - v (y - α)‖ := by
    intro y
    have hu_l : 0 < ‖u (y - α)‖ := lt_of_lt_of_le hhalfpos (hu (y - α)).1
    have hv_l : 0 < ‖v (y - α)‖ := lt_of_lt_of_le hhalfpos (hv (y - α)).1
    have hpq_pos : 0 < ‖u (y - α)‖ * ‖v (y - α)‖ := mul_pos hu_l hv_l
    have hpq_ge : z.im ^ 2 / 4 ≤ ‖u (y - α)‖ * ‖v (y - α)‖ := by
      have h1 := (hu (y - α)).1
      have h2 := (hv (y - α)).1
      calc z.im ^ 2 / 4 = (z.im / 2) * (z.im / 2) := by ring
        _ ≤ ‖u (y - α)‖ * ‖v (y - α)‖ := mul_le_mul h1 h2 (by linarith) (le_of_lt hu_l)
    rw [key y, norm_div, norm_mul]
    rw [div_le_iff₀ hpq_pos]
    have hcge : 1 ≤ c * (‖u (y - α)‖ * ‖v (y - α)‖) := by
      rw [hc]
      have h4 : (0:ℝ) ≤ 4 / z.im ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hpq_ge h4
      have heq : (4 / z.im ^ 2) * (z.im ^ 2 / 4) = 1 := by field_simp
      linarith [hmul, heq]
    calc ‖u (y - α) - v (y - α)‖
        = ‖u (y - α) - v (y - α)‖ * 1 := (mul_one _).symm
      _ ≤ ‖u (y - α) - v (y - α)‖ * (c * (‖u (y - α)‖ * ‖v (y - α)‖)) :=
          mul_le_mul_of_nonneg_left hcge (norm_nonneg _)
      _ = (c * ‖u (y - α) - v (y - α)‖) * (‖u (y - α)‖ * ‖v (y - α)‖) := by ring
  -- iterating the contraction, using the global upper bound `‖w‖ ≤ 2B`
  have hbnd : ∀ n : ℕ, ∀ y, ‖u y - v y‖ ≤ c ^ n * (2 * B) := by
    intro n
    induction n with
    | zero =>
      intro y
      simp only [pow_zero, one_mul]
      calc ‖u y - v y‖ ≤ ‖u y‖ + ‖v y‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hu y).2 (hv y).2
        _ = 2 * B := by ring
    | succ k ih =>
      intro y
      calc ‖u y - v y‖ ≤ c * ‖u (y - α) - v (y - α)‖ := hstep y
        _ ≤ c * (c ^ k * (2 * B)) := mul_le_mul_of_nonneg_left (ih (y - α)) hc_nn
        _ = c ^ (k + 1) * (2 * B) := by ring
  have htend : Filter.Tendsto (fun n : ℕ => c ^ n * (2 * B)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => c ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hc_nn hc_lt
    simpa using h0.mul_const (2 * B)
  have hle : ‖u x - v x‖ ≤ 0 := ge_of_tendsto' htend (fun n => hbnd n x)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

end Work.TMComp.MAnalytic
