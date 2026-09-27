import Mathlib
import Submission.Work.EQ.hetero_local

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! The invariant `χ` of the two-step equichordal half-map and the "leaf" argument.

Near the fixed point `A₁ = -1/2` the two-step map `T = eqU ∘ eqU` has the form
`T(x,y) = (x + O(y²), y·M(x,y))` with `M ≤ κ < 1`.  Hence the `x`-coordinate of every orbit
converges; its limit `χ(x,y)` is invariant under `T` and separates points with equal `y`
(two orbits with the same `y` keep `x`-coordinates differing by at least half the initial gap).
Consequently a level set of `χ` meets every horizontal line in at most one point, which is what
makes the local invariant curve unique. -/

namespace Work.EQ

open Complex

open scoped BigOperators

/-- Quantitative local data for the equichordal two-step map near `A₁`, as supplied by
`loc_estimates`. -/
structure LocData (a : ℝ) where
  ρ : ℝ
  h : ℝ
  κ : ℝ
  C : ℝ
  ρpos : 0 < ρ
  hpos : 0 < h
  κpos : 0 < κ
  κlt : κ < 1
  Cpos : 0 < C
  Ch : C * h ^ 2 ≤ 1 / 2
  Cρ : C * h ^ 2 / (1 - κ ^ 2) ≤ ρ
  boxR : ∀ x y : ℝ, |x| ≤ 4 * ρ → 0 < y → y ≤ h →
    0 < locR a x y ∧ 0 < locLy a x y ∧ locLy a x y ≤ κ ∧ locY a x y = y * locLy a x y
  step : ∀ x y : ℝ, |x| ≤ 3 * ρ → 0 < y → y ≤ h →
    (locT a (x, y)).1 = x + locA a (x, y) ∧ (locT a (x, y)).2 = y * locM a (x, y) ∧
    |locA a (x, y)| ≤ C * y ^ 2 ∧ 0 < locM a (x, y) ∧ locM a (x, y) ≤ κ
  lipX : ∀ x₁ x₂ y : ℝ, |x₁| ≤ 3 * ρ → |x₂| ≤ 3 * ρ → 0 < y → y ≤ h →
    |locA a (x₁, y) - locA a (x₂, y)| ≤ C * y ^ 2 * |x₁ - x₂| ∧
    |locM a (x₁, y) - locM a (x₂, y)| ≤ C * |x₁ - x₂|
  lipY : ∀ x y₁ y₂ : ℝ, |x| ≤ 3 * ρ → 0 < y₁ → y₁ ≤ h → 0 < y₂ → y₂ ≤ h →
    |locA a (x, y₁) - locA a (x, y₂)| ≤ C * (y₁ + y₂) * |y₁ - y₂| ∧
    |locM a (x, y₁) - locM a (x, y₂)| ≤ C * |y₁ - y₂|

namespace LocData

variable {a : ℝ} (d : LocData a)

theorem one_sub_sq_pos : 0 < 1 - d.κ ^ 2 := by
  nlinarith [d.κpos, d.κlt, sq_nonneg d.κ]

theorem one_sub_pos : 0 < 1 - d.κ := by linarith [d.κlt]

theorem kpow_le_one (n : ℕ) : d.κ ^ n ≤ 1 :=
  pow_le_one₀ (le_of_lt d.κpos) (le_of_lt d.κlt)

theorem kpow_pos (n : ℕ) : 0 < d.κ ^ n := pow_pos d.κpos n

/-- The `x`-drift of an orbit is bounded by `ρ`. -/
theorem drift_le (y : ℝ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) ≤ d.ρ := by
  have h1 : (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) ≤ 1 / (1 - d.κ ^ 2) := by
    have h2 : (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) = (1 - (d.κ ^ 2) ^ n) / (1 - d.κ ^ 2) := by
      rw [geom_sum_eq (by nlinarith [d.κpos, d.κlt]) n]
      rw [div_eq_div_iff (by nlinarith [d.κpos, d.κlt]) (ne_of_gt d.one_sub_sq_pos)]
      ring
    rw [h2, div_le_div_iff_of_pos_right d.one_sub_sq_pos]
    have h3 : 0 ≤ (d.κ ^ 2) ^ n := by positivity
    linarith
  have hy : y ^ 2 ≤ d.h ^ 2 := by nlinarith [hy0, hyh]
  calc d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k)
      ≤ d.C * y ^ 2 * (1 / (1 - d.κ ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt d.Cpos) (sq_nonneg y))
    _ = d.C * y ^ 2 / (1 - d.κ ^ 2) := by ring
    _ ≤ d.C * d.h ^ 2 / (1 - d.κ ^ 2) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt d.one_sub_sq_pos)
        exact mul_le_mul_of_nonneg_left hy (le_of_lt d.Cpos)
    _ ≤ d.ρ := d.Cρ

/-- The orbit of the two-step map `locT`. -/
noncomputable def orb (a : ℝ) (x y : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x, y)
  | n + 1 => locT a (orb a x y n)

@[simp] theorem orb_zero (a : ℝ) (x y : ℝ) : orb a x y 0 = (x, y) := rfl

theorem orb_succ (a : ℝ) (x y : ℝ) (n : ℕ) : orb a x y (n + 1) = locT a (orb a x y n) := rfl

/-- Main orbit bounds: starting in `|x| ≤ 2ρ`, `0 < y ≤ h`, the orbit stays in `|x| ≤ 3ρ` and its
height decays at least geometrically. -/
theorem orb_bound (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) :
    ∀ n, |(orb a x y n).1| ≤ 2 * d.ρ + d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) ∧
      0 < (orb a x y n).2 ∧ (orb a x y n).2 ≤ d.κ ^ n * y := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, hy0, by simp⟩
      simp only [orb_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      linarith [d.ρpos]
  | succ n ih =>
      obtain ⟨ihx, ihy0, ihy⟩ := ih
      have hynh : (orb a x y n).2 ≤ d.h := by
        calc (orb a x y n).2 ≤ d.κ ^ n * y := ihy
          _ ≤ 1 * y := mul_le_mul_of_nonneg_right (d.kpow_le_one n) (le_of_lt hy0)
          _ = y := one_mul y
          _ ≤ d.h := hyh
      have hx3 : |(orb a x y n).1| ≤ 3 * d.ρ := by
        have := d.drift_le y hy0 hyh n
        nlinarith [ihx, this, d.ρpos]
      obtain ⟨e1, e2, e3, e4, e5⟩ := d.step _ _ hx3 ihy0 hynh
      rw [orb_succ a x y n, e1, e2]
      refine ⟨?_, ?_, ?_⟩
      · have hY : (orb a x y n).2 ^ 2 ≤ (d.κ ^ n * y) ^ 2 :=
          pow_le_pow_left₀ (le_of_lt ihy0) ihy 2
        have hA : |locA a ((orb a x y n).1, (orb a x y n).2)| ≤ d.C * y ^ 2 * (d.κ ^ 2) ^ n := by
          calc |locA a ((orb a x y n).1, (orb a x y n).2)|
              ≤ d.C * (orb a x y n).2 ^ 2 := e3
            _ ≤ d.C * (d.κ ^ n * y) ^ 2 := mul_le_mul_of_nonneg_left hY (le_of_lt d.Cpos)
            _ = d.C * y ^ 2 * (d.κ ^ 2) ^ n := by
                rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]; ring
        calc |(orb a x y n).1 + locA a ((orb a x y n).1, (orb a x y n).2)|
            ≤ |(orb a x y n).1| + |locA a ((orb a x y n).1, (orb a x y n).2)| := abs_add_le _ _
          _ ≤ 2 * d.ρ + d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) +
                d.C * y ^ 2 * (d.κ ^ 2) ^ n := by linarith
          _ = 2 * d.ρ + d.C * y ^ 2 * (∑ k ∈ Finset.range (n + 1), (d.κ ^ 2) ^ k) := by
              rw [Finset.sum_range_succ]; ring
      · exact mul_pos ihy0 e4
      · calc (orb a x y n).2 * locM a ((orb a x y n).1, (orb a x y n).2)
            ≤ (d.κ ^ n * y) * d.κ :=
              mul_le_mul ihy e5 (le_of_lt e4) (mul_nonneg (d.kpow_pos n).le hy0.le)
          _ = d.κ ^ (n + 1) * y := by rw [pow_succ]; ring

theorem orb_x_le (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    |(orb a x y n).1| ≤ 3 * d.ρ := by
  have h1 := (orb_bound d x y hx hy0 hyh n).1
  have h2 := d.drift_le y hy0 hyh n
  nlinarith [h1, h2, d.ρpos]

theorem orb_y_pos (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    0 < (orb a x y n).2 := (orb_bound d x y hx hy0 hyh n).2.1

theorem orb_y_le (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    (orb a x y n).2 ≤ d.κ ^ n * y := (orb_bound d x y hx hy0 hyh n).2.2

theorem orb_y_le_h (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    (orb a x y n).2 ≤ d.h := by
  calc (orb a x y n).2 ≤ d.κ ^ n * y := orb_y_le d x y hx hy0 hyh n
    _ ≤ 1 * y := mul_le_mul_of_nonneg_right (d.kpow_le_one n) (le_of_lt hy0)
    _ = y := one_mul y
    _ ≤ d.h := hyh

theorem orb_y_decay (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    (orb a x y n).2 ≤ d.κ ^ n * y := orb_y_le d x y hx hy0 hyh n

/-- The `x`-increment along an orbit. -/
noncomputable def incr (a : ℝ) (x y : ℝ) (n : ℕ) : ℝ :=
  (orb a x y (n + 1)).1 - (orb a x y n).1

theorem incr_eq (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    incr a x y n = locA a ((orb a x y n).1, (orb a x y n).2) := by
  have := (d.step _ _ (orb_x_le d x y hx hy0 hyh n) (orb_y_pos d x y hx hy0 hyh n)
    (orb_y_le_h d x y hx hy0 hyh n)).1
  rw [incr, orb_succ, this]
  ring

theorem abs_incr_le (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) (n : ℕ) :
    |incr a x y n| ≤ d.C * y ^ 2 * (d.κ ^ 2) ^ n := by
  have h := (d.step _ _ (orb_x_le d x y hx hy0 hyh n) (orb_y_pos d x y hx hy0 hyh n)
    (orb_y_le_h d x y hx hy0 hyh n)).2.2.1
  have hY : (orb a x y n).2 ^ 2 ≤ (d.κ ^ n * y) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (orb_y_pos d x y hx hy0 hyh n)) (orb_y_le d x y hx hy0 hyh n) 2
  rw [incr_eq d x y hx hy0 hyh n]
  calc |locA a ((orb a x y n).1, (orb a x y n).2)| ≤ d.C * (orb a x y n).2 ^ 2 := h
    _ ≤ d.C * (d.κ ^ n * y) ^ 2 := mul_le_mul_of_nonneg_left hY (le_of_lt d.Cpos)
    _ = d.C * y ^ 2 * (d.κ ^ 2) ^ n := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]; ring

theorem summable_incr (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) :
    Summable (incr a x y) := by
  refine Summable.of_norm_bounded (g := fun n => d.C * y ^ 2 * (d.κ ^ 2) ^ n) ?_ ?_
  · simpa using (summable_geometric_of_lt_one (r := d.κ ^ 2) (by positivity)
      (by nlinarith [d.κpos, d.κlt])).mul_left (d.C * y ^ 2)
  · intro n
    simpa using abs_incr_le d x y hx hy0 hyh n

/-- The limit of the `x`-coordinate along an orbit. -/
noncomputable def chi (a : ℝ) (x y : ℝ) : ℝ := x + ∑' n, incr a x y n

theorem chi_eq_lim (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) :
    Filter.Tendsto (fun n => (orb a x y n).1) Filter.atTop (nhds (chi a x y)) := by
  have hsum := summable_incr d x y hx hy0 hyh
  have hps : ∀ n, (orb a x y n).1 = x + ∑ k ∈ Finset.range n, incr a x y k := by
    intro n
    induction n with
    | zero => simp [orb_zero]
    | succ n ih =>
        have hstep : (orb a x y (n + 1)).1 = (orb a x y n).1 + incr a x y n := by
          rw [incr, orb_succ]; ring
        rw [hstep, ih, Finset.sum_range_succ]
        ring
  have htend : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, incr a x y k) Filter.atTop
      (nhds (∑' n, incr a x y n)) := hsum.hasSum.tendsto_sum_nat
  have h2 := (tendsto_const_nhds (x := x)).add htend
  simpa only [chi, hps] using h2

theorem abs_chi_sub (x y : ℝ) (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y) (hyh : y ≤ d.h) :
    |chi a x y - x| ≤ d.C * y ^ 2 / (1 - d.κ ^ 2) := by
  have hgeom : Summable (fun n => d.C * y ^ 2 * (d.κ ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (r := d.κ ^ 2) (by positivity)
      (by nlinarith [d.κpos, d.κlt])).mul_left (d.C * y ^ 2)
  have hsum : Summable (fun n => ‖incr a x y n‖) := by
    refine Summable.of_norm_bounded (g := fun n => d.C * y ^ 2 * (d.κ ^ 2) ^ n) hgeom ?_
    intro n
    simpa using abs_incr_le d x y hx hy0 hyh n
  have htsum : (∑' n, d.C * y ^ 2 * (d.κ ^ 2) ^ n) = d.C * y ^ 2 / (1 - d.κ ^ 2) := by
    rw [tsum_mul_left,
      tsum_geometric_of_lt_one (r := d.κ ^ 2) (by positivity) (by nlinarith [d.κpos, d.κlt])]
    ring
  have hbound : ‖∑' n, incr a x y n‖ ≤ d.C * y ^ 2 / (1 - d.κ ^ 2) := by
    refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
    rw [← htsum]
    exact Summable.tsum_le_tsum (fun n => abs_incr_le d x y hx hy0 hyh n) hsum hgeom
  have hsub : chi a x y - x = ∑' n, incr a x y n := by rw [chi]; ring
  rw [Real.norm_eq_abs] at hbound
  rw [hsub]
  exact hbound

/-- Smallness condition on the starting height needed to run the two-orbit comparison. -/
def Small (y : ℝ) : Prop :=
  2 * d.C * y ^ 2 * (1 / (1 - d.κ ^ 2) + 8 * d.C / (d.κ * (1 - d.κ ^ 2) ^ 2)) ≤ 1 / 2 ∧
  2 * d.C * y / (1 - d.κ) ^ 2 ≤ d.κ / 8

end LocData

end Work.EQ
