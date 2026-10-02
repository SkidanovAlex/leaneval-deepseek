import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.Bottcher.Auxiliary.two_pow_sq_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lipschitz estimate for the Böttcher series of the tricorn

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c (p_c^n z))` is holomorphic in
`z` on the far region `{4 (1 + ‖c‖) ≤ ‖z‖}`, and its derivative there is `O(1/‖z‖³)`.
Consequently the series is Lipschitz with constant `C (1 + ‖c‖) / ‖u‖³` on a ball
around `u` of radius `‖u‖ / 2`.

The estimates follow the shape of `Core.analyticAt_bottcher`:
* the orbit grows: `‖p_c^n w‖ ≥ 4^n ‖w‖`;
* hence `∏_{k<n} ‖p_c^k w‖³ ≤ 2^n ‖p_c^n w‖ / ‖w‖`;
* combining with `‖Pd c n w‖ ≤ 8^n ∏ …` and `‖dlognf c v‖ ≤ (32‖c‖+32)/‖v‖³`
  gives `‖btDeriv c n w‖ ≤ (8‖c‖+8) (1/4)^n / ‖w‖³`, whose sum over `n` converges.
-/

namespace Work.Bottcher.Contraction

open Filter Function
open scoped Topology ComplexConjugate

/-- **Growth of the `p_c`-orbit.**  Once `‖w‖ ≥ 2 + ‖c‖`, the `n`-th iterate of `w`
under `p_c` has norm at least `4^n ‖w‖`. -/
theorem four_pow_mul_norm_le_iterate (c w : ℂ) (hR : 2 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    (4 : ℝ) ^ n * ‖w‖ ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ := by
  have hR2 : (2 : ℝ) ≤ ‖w‖ := by linarith [norm_nonneg c]
  have hR3 : (8 : ℝ) ≤ ‖w‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR2 3
    norm_num at h; exact h
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := Work.Bottcher.Core.pMap_norm_iterate_succ c w hR n
      have hnn : (0 : ℝ) ≤ (4 : ℝ) ^ n * ‖w‖ := by positivity
      have hpow : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ (4 * n) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have key : (4 : ℝ) ^ (n + 1) * ‖w‖ ≤ ((4 : ℝ) ^ n * ‖w‖) ^ 4 / 2 := by
        have h4n : ((4 : ℝ) ^ n) ^ 4 = (4 : ℝ) ^ (4 * n) := by
          rw [← pow_mul, Nat.mul_comm]
        have h1 : (4 : ℝ) ^ (n + 1) * 2 ≤ (4 : ℝ) ^ (4 * n) * ‖w‖ ^ 3 := by
          rw [pow_succ]
          calc (4 : ℝ) ^ n * 4 * 2 = 8 * (4 : ℝ) ^ n := by ring
            _ ≤ 8 * (4 : ℝ) ^ (4 * n) := mul_le_mul_of_nonneg_left hpow (by norm_num)
            _ = (4 : ℝ) ^ (4 * n) * 8 := by ring
            _ ≤ (4 : ℝ) ^ (4 * n) * ‖w‖ ^ 3 := mul_le_mul_of_nonneg_left hR3 (by positivity)
        rw [mul_pow, h4n, le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)]
        rw [show (4 : ℝ) ^ (n + 1) * ‖w‖ * 2 = ((4 : ℝ) ^ (n + 1) * 2) * ‖w‖ by ring]
        calc ((4 : ℝ) ^ (n + 1) * 2) * ‖w‖ ≤ ((4 : ℝ) ^ (4 * n) * ‖w‖ ^ 3) * ‖w‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
          _ = (4 : ℝ) ^ (4 * n) * ‖w‖ ^ 4 := by ring
      calc (4 : ℝ) ^ (n + 1) * ‖w‖ ≤ ((4 : ℝ) ^ n * ‖w‖) ^ 4 / 2 := key
        _ ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 4 / 2 := by
            have h4 := pow_le_pow_left₀ hnn ih 4
            linarith
        _ ≤ ‖(Work.Bottcher.pMap c)^[n + 1] w‖ := hstep

/-- **Product bound.**  Once `‖w‖ ≥ 2 + ‖c‖`, `∏_{k<n} ‖p_c^k w‖³ ≤ 2^n ‖p_c^n w‖ / ‖w‖`. -/
theorem prod_iterate_norm_pow_three_le (c w : ℂ) (hR : 2 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3
      ≤ 2 ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := by linarith [norm_nonneg c]
  induction n with
  | zero =>
      rw [Finset.prod_range_zero, Function.iterate_zero_apply, pow_zero, one_mul]
      exact (div_self (ne_of_gt hwpos)).ge
  | succ n ih =>
      rw [Finset.prod_range_succ, pow_succ]
      have hstep := Work.Bottcher.Core.pMap_norm_iterate_succ c w hR n
      have h4 : ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 4
          ≤ 2 * ‖(Work.Bottcher.pMap c)^[n + 1] w‖ := by linarith
      calc (∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) *
              ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3
          ≤ (2 ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ / ‖w‖) *
              ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3 :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = 2 ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 4 / ‖w‖ := by ring
        _ ≤ 2 ^ n * (2 * ‖(Work.Bottcher.pMap c)^[n + 1] w‖) / ‖w‖ := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hwpos)
            exact mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 2 ^ n * 2 * ‖(Work.Bottcher.pMap c)^[n + 1] w‖ / ‖w‖ := by ring

/-- **Pointwise bound on the derivative of one Böttcher term.**  On the far region
`4 (1 + ‖c‖) ≤ ‖w‖`, `‖btDeriv c n w‖ ≤ (8‖c‖ + 8) (1/4)^n / ‖w‖³`. -/
theorem norm_btDeriv_le_sharp (c w : ℂ) (hR : 4 * (1 + ‖c‖) ≤ ‖w‖) (n : ℕ) :
    ‖Work.Bottcher.Core.btDeriv c n w‖ ≤ (8 * ‖c‖ + 8) * (1 / 4 : ℝ) ^ n / ‖w‖ ^ 3 := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hR2 : 2 + ‖c‖ ≤ ‖w‖ := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hge : ∀ k, 1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[k] w‖ := fun k => by
    have := Work.Bottcher.Core.pMap_norm_iterate_ge c w hR2 k
    linarith
  have hzn : 0 < ‖(Work.Bottcher.pMap c)^[n] w‖ := by
    have := hge n; linarith
  have hdl := Work.Bottcher.Core.norm_dlognf_le c ((Work.Bottcher.pMap c)^[n] w) (hge n)
  have hPd := Work.Bottcher.Core.norm_Pd_le c w hge n
  have hprod := prod_iterate_norm_pow_three_le c w hR2 n
  have hgr := four_pow_mul_norm_le_iterate c w hR2 n
  -- strip the constant of the `n`-th term
  have hconst : ‖(((1 / 4 : ℝ) : ℂ)) ^ (n + 1)‖ = (1 / 4 : ℝ) ^ (n + 1) := by
    rw [norm_pow]; simp
  have hbt : ‖Work.Bottcher.Core.btDeriv c n w‖
      = (1 / 4 : ℝ) ^ (n + 1)
        * (‖Work.Bottcher.Core.dlognf c ((Work.Bottcher.pMap c)^[n] w)‖
            * ‖Work.Bottcher.Core.Pd c n w‖) := by
    simp only [Work.Bottcher.Core.btDeriv, norm_mul, hconst]
  -- Step 1: bound each factor.
  have h1 : ‖Work.Bottcher.Core.btDeriv c n w‖
      ≤ (1 / 4 : ℝ) ^ (n + 1)
        * (((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3)) := by
    rw [hbt]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖Work.Bottcher.Core.dlognf c ((Work.Bottcher.pMap c)^[n] w)‖
            * ‖Work.Bottcher.Core.Pd c n w‖
        ≤ ((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * ‖Work.Bottcher.Core.Pd c n w‖ :=
          mul_le_mul_of_nonneg_right hdl (norm_nonneg _)
      _ ≤ ((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) :=
          mul_le_mul_of_nonneg_left hPd (by positivity)
  -- Step 2: use the product bound.
  have h2 : (1 / 4 : ℝ) ^ (n + 1)
        * (((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3))
      ≤ (1 / 4 : ℝ) ^ (n + 1)
        * (((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * (8 ^ n * (2 ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ / ‖w‖))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by positivity))
      (by positivity)
  -- Step 3: the arithmetic.
  have h816 : (8 : ℝ) ^ n * 2 ^ n = 16 ^ n := by rw [← mul_pow]; norm_num
  have hkey : 16 ^ n * ‖w‖ ^ 2 ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2 := by
    have h4 : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
      rw [← pow_mul, show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
    have h5 : ((4 : ℝ) ^ n * ‖w‖) * ((4 : ℝ) ^ n * ‖w‖)
        ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ * ‖(Work.Bottcher.pMap c)^[n] w‖ :=
      mul_le_mul hgr hgr (by positivity) (norm_nonneg _)
    nlinarith [h4, h5]
  have h3 : (1 / 4 : ℝ) ^ (n + 1)
        * (((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3)
            * (8 ^ n * (2 ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ / ‖w‖)))
      ≤ (8 * ‖c‖ + 8) * (1 / 4 : ℝ) ^ n / ‖w‖ ^ 3 := by
    set Z : ℝ := ‖(Work.Bottcher.pMap c)^[n] w‖
    have hZ : 0 < Z := hzn
    have hZ2 : 0 < Z ^ 2 := by positivity
    have hkey' : 16 ^ n * ‖w‖ ^ 2 ≤ Z ^ 2 := hkey
    rw [le_div_iff₀ (show (0 : ℝ) < ‖w‖ ^ 3 by positivity)]
    have hre : (1 / 4 : ℝ) ^ (n + 1)
          * ((32 * ‖c‖ + 32) / Z ^ 3 * (8 ^ n * (2 ^ n * Z / ‖w‖))) * ‖w‖ ^ 3
        = (1 / 4 : ℝ) ^ (n + 1) * (32 * ‖c‖ + 32) * 16 ^ n * (‖w‖ ^ 2 / Z ^ 2) := by
      rw [← h816]
      field_simp
    rw [hre]
    have hratio : ‖w‖ ^ 2 / Z ^ 2 ≤ 1 / 16 ^ n := by
      rw [div_le_div_iff₀ hZ2 (by positivity)]
      nlinarith [hkey']
    calc (1 / 4 : ℝ) ^ (n + 1) * (32 * ‖c‖ + 32) * 16 ^ n * (‖w‖ ^ 2 / Z ^ 2)
        ≤ (1 / 4 : ℝ) ^ (n + 1) * (32 * ‖c‖ + 32) * 16 ^ n * (1 / 16 ^ n) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (8 * ‖c‖ + 8) * (1 / 4 : ℝ) ^ n := by
          rw [pow_succ]
          field_simp
          ring
  linarith [h1, h2, h3]

/-- **Derivative bound.**  On the far region, the sum of the termwise derivatives is
bounded by `64 (1 + ‖c‖) / ‖w‖³`. -/
theorem norm_tsum_btDeriv_le (c w : ℂ) (hR : 4 * (1 + ‖c‖) ≤ ‖w‖) :
    ‖∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w‖ ≤ 64 * (1 + ‖c‖) / ‖w‖ ^ 3 := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hwpos : 0 < ‖w‖ := by linarith
  have hmaj : Summable (fun n : ℕ => (8 * ‖c‖ + 8) * (1 / 4 : ℝ) ^ n / ‖w‖ ^ 3) := by
    have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (h0.mul_left ((8 * ‖c‖ + 8) / ‖w‖ ^ 3)).congr fun n => ?_
    ring
  have hsum : Summable (fun n : ℕ => ‖Work.Bottcher.Core.btDeriv c n w‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_btDeriv_le_sharp c w hR n) hmaj
  calc ‖∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w‖
      ≤ ∑' n : ℕ, ‖Work.Bottcher.Core.btDeriv c n w‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, (8 * ‖c‖ + 8) * (1 / 4 : ℝ) ^ n / ‖w‖ ^ 3 :=
        hsum.tsum_le_tsum (fun n => norm_btDeriv_le_sharp c w hR n) hmaj
    _ = ((8 * ‖c‖ + 8) / ‖w‖ ^ 3) * (∑' n : ℕ, (1 / 4 : ℝ) ^ n) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring
    _ = ((8 * ‖c‖ + 8) / ‖w‖ ^ 3) * (4 / 3) := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
    _ ≤ 64 * (1 + ‖c‖) / ‖w‖ ^ 3 := by
        rw [show ((8 * ‖c‖ + 8) / ‖w‖ ^ 3) * (4 / 3)
              = ((8 * ‖c‖ + 8) * (4 / 3)) / ‖w‖ ^ 3 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

/-- **Differentiability of the Böttcher series on the far region.**  For
`4 (1 + ‖c‖) ≤ ‖w‖` the series is complex differentiable at `w` with derivative
`∑' n, btDeriv c n w`. -/
theorem hasDerivAt_bottcherSeries (c w : ℂ) (hw : 4 * (1 + ‖c‖) ≤ ‖w‖) :
    HasDerivAt (Work.Bottcher.bottcherSeries c)
      (∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w) w := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hwpos : 0 < ‖w‖ := by linarith
  have hw1 : 1 + ‖c‖ ≤ ‖w‖ := by linarith
  have hρpos : 0 < ‖w‖ / 2 := by linarith
  have hs_open : IsOpen (Metric.ball w (‖w‖ / 2)) := Metric.isOpen_ball
  have hs_pre : IsPreconnected (Metric.ball w (‖w‖ / 2)) :=
    (convex_ball w (‖w‖ / 2)).isPreconnected
  have hlow : ∀ y ∈ Metric.ball w (‖w‖ / 2), 2 + ‖c‖ ≤ ‖y‖ := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : ‖w‖ ≤ ‖y‖ + ‖y - w‖ := by
      have h := norm_add_le y (w - y)
      have h2 : y + (w - y) = w := by ring
      rw [h2] at h
      rwa [norm_sub_rev w y] at h
    linarith
  have hderiv : ∀ n y, y ∈ Metric.ball w (‖w‖ / 2) →
      HasDerivAt (fun z => Work.Bottcher.bottcherTerm c n z)
        (Work.Bottcher.Core.btDeriv c n y) y := fun n y hy =>
    Work.Bottcher.Core.hasDerivAt_bottcherTerm c y n (fun k => by
      have := Work.Bottcher.Core.pMap_norm_iterate_ge c y (hlow y hy) k
      linarith [norm_nonneg c])
  have hbound : ∀ n y, y ∈ Metric.ball w (‖w‖ / 2) →
      ‖Work.Bottcher.Core.btDeriv c n y‖ ≤ Work.Bottcher.Core.uSeq c n :=
    fun n y hy => Work.Bottcher.Core.norm_btDeriv_le c y (hlow y hy) n
  have hu : Summable (Work.Bottcher.Core.uSeq c) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (8 * ‖c‖ + 8)
  have hg0 : Summable (fun n => Work.Bottcher.bottcherTerm c n w) := by
    refine Summable.of_norm_bounded (g := fun n => (15 / 8) * (1 / 4 : ℝ) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (15 / 8)
    · intro n; exact Work.Bottcher.Core.norm_term_le c w hw1 n
  exact hasDerivAt_tsum_of_isPreconnected hu hs_open hs_pre hderiv hbound
    (Metric.mem_ball_self hρpos) hg0 (Metric.mem_ball_self hρpos)

/-- **Lipschitz estimate for the Böttcher series.**  There is `r > 0` such that on a
ball of radius `‖u‖ / 2` around any `u` with `‖u‖ ≥ r`, the Böttcher series is
Lipschitz with constant `1024 (1 + ‖c‖) / ‖u‖³`. -/
theorem norm_bottcherSeries_sub_le (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ u x y : ℂ, r ≤ ‖u‖ →
      ‖x - u‖ ≤ ‖u‖ / 2 → ‖y - u‖ ≤ ‖u‖ / 2 →
      ‖Work.Bottcher.bottcherSeries c x - Work.Bottcher.bottcherSeries c y‖
        ≤ 1024 * (1 + ‖c‖) / ‖u‖ ^ 3 * ‖x - y‖ := by
  refine ⟨8 * (1 + ‖c‖), by positivity, ?_⟩
  intro u x y hu hx hy
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hupos : 0 < ‖u‖ := by linarith
  have hρpos : 0 < ‖u‖ / 2 := by linarith
  have hfar : ∀ w ∈ Metric.closedBall u (‖u‖ / 2), 4 * (1 + ‖c‖) ≤ ‖w‖ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 : ‖u‖ ≤ ‖w‖ + ‖w - u‖ := by
      have h := norm_add_le w (u - w)
      have h2 : w + (u - w) = u := by ring
      rw [h2, norm_sub_rev u w] at h
      exact h
    linarith
  have hxu : x ∈ Metric.closedBall u (‖u‖ / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
  have hyu : y ∈ Metric.closedBall u (‖u‖ / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  have hderiv : ∀ w ∈ Metric.closedBall u (‖u‖ / 2),
      HasFDerivWithinAt (Work.Bottcher.bottcherSeries c)
        (ContinuousLinearMap.toSpanSingleton ℂ
          (∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w))
        (Metric.closedBall u (‖u‖ / 2)) w := fun w hw =>
    ((hasDerivAt_bottcherSeries c w (hfar w hw)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ w ∈ Metric.closedBall u (‖u‖ / 2),
      ‖ContinuousLinearMap.toSpanSingleton ℂ
          (∑' n : ℕ, Work.Bottcher.Core.btDeriv c n w)‖
        ≤ 1024 * (1 + ‖c‖) / ‖u‖ ^ 3 := by
    intro w hw
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    have h1 := norm_tsum_btDeriv_le c w (hfar w hw)
    have hw2 : ‖u‖ / 2 ≤ ‖w‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have h1' : ‖u‖ ≤ ‖w‖ + ‖w - u‖ := by
        have h := norm_add_le w (u - w)
        have h2 : w + (u - w) = u := by ring
        rw [h2, norm_sub_rev u w] at h
        exact h
      linarith
    have hwp : 0 < ‖w‖ := by linarith
    have hw3 : (‖u‖ / 2) ^ 3 ≤ ‖w‖ ^ 3 := pow_le_pow_left₀ (by positivity) hw2 3
    have h3 : 64 * (1 + ‖c‖) / ‖w‖ ^ 3 ≤ 1024 * (1 + ‖c‖) / ‖u‖ ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hwp 3) (pow_pos hupos 3)]
      nlinarith [hw3, norm_nonneg c, pow_nonneg (norm_nonneg u) 3, pow_nonneg (norm_nonneg w) 3]
    linarith
  have hMVT := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_closedBall u (‖u‖ / 2)) hxu hyu
  rw [norm_sub_rev (Work.Bottcher.bottcherSeries c y) (Work.Bottcher.bottcherSeries c x),
      norm_sub_rev y x] at hMVT
  exact hMVT

end Work.Bottcher.Contraction
