import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.FatouCoord.Main

/-!
# Petal capture for `f₀(z) = z + z²`

Every `f₀`-orbit converging to `0` without hitting `0` eventually enters every petal
`Petal r M` with `r > 0`, `M > 1/r` (`Work.FatouCoord.Petal`).

The argument is entirely explicit.  In the parabolic chart `w = -1/z` the map `f₀` becomes the
rational map `wMap f₀ w = w²/(w-1) = w + 1 + 1/(w-1)`, so `wMap f₀ w - (w + 1) = 1/(w-1)` is
`O(1/w)`: for `‖w‖ ≥ 4` the real part increases by at least `1/2` at every step, hence the
chart orbit, whose modulus tends to `∞` (`‖z_n‖ → 0`, `z_n ≠ 0`), has real part tending to `+∞`.
The petal condition `Re (-1/z) > M`, `‖z‖ < r` is then satisfied as soon as `Re (chart z) > M`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

/-- The explicit chart form of `f₀(z) = z + z²`: `wMap f₀ w = w² / (w - 1)`. -/
lemma wMap_f0_eq_div (v : ℂ) : Work.FatouCoord.wMap MandelDim.f0 v = v ^ 2 / (v - 1) := by
  rw [Work.FatouCoord.wMap_apply]
  simp only [MandelDim.f0]
  rcases eq_or_ne v 0 with rfl | hv0
  · norm_num
  · field_simp
    rw [show (-v + 1 : ℂ) = -(v - 1) by ring, div_neg, neg_neg]

/-- The drift form of the chart dynamics of `f₀`: away from `v = 1`,
`wMap f₀ v = v + 1 + 1/(v - 1)`. -/
lemma wMap_f0_eq (v : ℂ) (hv : v ≠ 1) :
    Work.FatouCoord.wMap MandelDim.f0 v = v + 1 + 1 / (v - 1) := by
  rw [wMap_f0_eq_div v]
  have h1 : v - 1 ≠ 0 := sub_ne_zero.mpr hv
  field_simp
  ring

/-- For `u ≠ 0`, `Re (1/u) ≥ -1/‖u‖`. -/
lemma neg_inv_norm_le_re_one_div (u : ℂ) (hu : u ≠ 0) : -(1 / ‖u‖) ≤ (1 / u).re := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hkey : (1 / u).re = u.re / Complex.normSq u := by
    rw [one_div, Complex.inv_re]
  rw [hkey, Complex.normSq_eq_norm_sq]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖u‖ ^ 2)]
  have h2 : -(1 / ‖u‖) * ‖u‖ ^ 2 = -‖u‖ := by field_simp
  rw [h2]
  exact neg_le_of_abs_le (Complex.abs_re_le_norm u)

/-- **One step moves `Re` up by `1/2`.**  Once `‖v‖ ≥ 4` the chart orbit of `f₀` has
`Re (wMap f₀ v) ≥ Re v + 1/2`.  (Note `‖v‖ ≥ 4` excludes the exceptional point `v = 1`.) -/
lemma wMap_f0_re_step (v : ℂ) (hv : 4 ≤ ‖v‖) :
    v.re + 1 / 2 ≤ (Work.FatouCoord.wMap MandelDim.f0 v).re := by
  have hv1 : v ≠ 1 := by
    intro h; rw [h] at hv; norm_num at hv
  rw [wMap_f0_eq v hv1]
  have hne : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
  have h3 : (3 : ℝ) ≤ ‖v - 1‖ := by
    have h := norm_sub_norm_le v (1 : ℂ)
    norm_num at h
    linarith
  have hbound : -(1 / 3) ≤ (1 / (v - 1)).re := by
    have h := neg_inv_norm_le_re_one_div (v - 1) hne
    have hle : (1 : ℝ) / ‖v - 1‖ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
    linarith
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- **Chart orbits escape to the right.**  A sequence `w` satisfying the chart recursion
`w (n+1) = wMap f₀ (w n)` and whose moduli are eventually `≥ 4` has `Re (w n) → +∞`. -/
lemma re_tendsto_atTop_of_wMap_f0 {w : ℕ → ℂ}
    (hrec : ∀ n, w (n + 1) = Work.FatouCoord.wMap MandelDim.f0 (w n))
    (hnorm : ∀ᶠ n in atTop, (4 : ℝ) ≤ ‖w n‖) :
    Tendsto (fun n => (w n).re) atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnorm
  have hstep : ∀ n, N ≤ n → (w n).re + 1 / 2 ≤ (w (n + 1)).re := by
    intro n hn
    rw [hrec n]
    exact wMap_f0_re_step (w n) (hN n hn)
  have hgrowth : ∀ k : ℕ, (w N).re + k / 2 ≤ (w (N + k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hstep (N + k) (Nat.le_add_right N k)
      have h2 : N + k + 1 = N + (k + 1) := by ring
      rw [h2] at h1
      push_cast
      linarith
  have hg : Tendsto (fun m : ℕ => (w (N + m)).re) atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun b => ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (b - (w N).re))
    refine eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
    have := hgrowth n
    nlinarith
  refine Filter.tendsto_atTop.mpr fun b => ?_
  obtain ⟨k, hk⟩ := eventually_atTop.mp (Filter.tendsto_atTop.mp hg b)
  refine eventually_atTop.mpr ⟨N + k, fun n hn => ?_⟩
  have hNle : N ≤ n := le_trans (Nat.le_add_right N k) hn
  have hge : k ≤ n - N := by omega
  have heq : N + (n - N) = n := Nat.add_sub_cancel' hNle
  rw [← heq]
  exact hk (n - N) hge

/-- Petal capture: if `z` has `f₀`-orbit converging to `0` and never hitting `0`, then the orbit
eventually enters the petal `Petal r M` (`Work.FatouCoord.Petal`), for every `r > 0` and
`M > 1/r`. -/
theorem eventually_mem_petal {r M : ℝ} (hr : 0 < r) (hM : 1 / r < M) {z : ℂ}
    (hconv : Tendsto (fun n : ℕ => MandelDim.f0^[n] z) atTop (𝓝 0))
    (hne : ∀ n : ℕ, MandelDim.f0^[n] z ≠ 0) :
    ∃ N : ℕ, MandelDim.f0^[N] z ∈ Work.FatouCoord.Petal r M := by
  let W : ℕ → ℂ := fun n => Work.FatouCoord.chart (MandelDim.f0^[n] z)
  have hnorm : ∀ᶠ n in atTop, (4 : ℝ) ≤ ‖W n‖ := by
    have hsmall : ∀ᶠ n in atTop, ‖MandelDim.f0^[n] z‖ < 1 / 4 :=
      hconv.norm.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hsmall] with n hn
    have hzn : 0 < ‖MandelDim.f0^[n] z‖ := norm_pos_iff.mpr (hne n)
    show (4 : ℝ) ≤ ‖Work.FatouCoord.chart (MandelDim.f0^[n] z)‖
    rw [Work.FatouCoord.norm_chart (hne n), inv_eq_one_div]
    rw [le_div_iff₀ hzn]
    linarith
  have hrec : ∀ n, W (n + 1) = Work.FatouCoord.wMap MandelDim.f0 (W n) := by
    intro n
    show Work.FatouCoord.chart (MandelDim.f0^[n + 1] z) = _
    rw [Function.iterate_succ_apply']
    rw [Work.FatouCoord.chart_comp MandelDim.f0 (hne n)]
  have hT : Tendsto (fun n => (W n).re) atTop atTop := re_tendsto_atTop_of_wMap_f0 hrec hnorm
  have hev : ∀ᶠ n in atTop, M < (W n).re := hT.eventually_gt_atTop M
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  have hzN : MandelDim.f0^[N] z ≠ 0 := hne N
  refine (Work.FatouCoord.chart_mem_Petal_iff (M := M) hr hzN).mpr ?_
  refine ⟨hN N le_rfl, ?_⟩
  have hMN := hN N le_rfl
  show (1 : ℝ) / r < ‖W N‖
  linarith [Complex.re_le_norm (W N)]

end Work.F0Facts
