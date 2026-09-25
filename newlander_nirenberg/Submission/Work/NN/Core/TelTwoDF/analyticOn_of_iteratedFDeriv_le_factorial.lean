/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Real analyticity from factorial growth of the iterated derivatives

Let `f : (Fin n → ℂ) → ℂ` be smooth on a ball `Metric.ball x ρ` and suppose that for every
`k : ℕ` and every `y` in that ball

`‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k !`

with `C > 0` and `M > 0`.  Then `f` is real analytic on some ball around `x`.

The proof is the classical one.  Fix a point `z` and expand `f` along the segment
`t ↦ f (z + t • v)`, `t ∈ [0,1]`, for `v = y - z` with `‖v‖` small.  The one-variable Taylor
theorem with a Lagrange remainder shows that the Taylor series of this slice at `0` converges
to its value at `1` as soon as the sup-norm of its `k`-th derivative grows like `C (M ‖v‖)^k k!`
with `M ‖v‖ < 1`; the chain rule identifies the Taylor coefficients with
`(k !)⁻¹ D^k f z (v, …, v)`.  Hence the formal Taylor series `p k = (k !)⁻¹ • D^k f z` of `f`
at `z` has positive radius and sums to `f` on a ball, i.e. `f` is analytic at `z`.  Since the
hypotheses are uniform in `z` this gives analyticity on a whole ball around `x`.

## Main results

* `Work.NN.Core.TelTwoDF.iteratedDeriv_slice_real` : the chain rule for the slice
  `t ↦ f (z + t • v)`.
* `Work.NN.Core.TelTwoDF.hasSum_taylor_of_bound` : the one-variable criterion.
* `Work.NN.Core.TelTwoDF.analyticOn_of_iteratedFDeriv_le_factorial` : the target statement.
-/

namespace Work.NN.Core.TelTwoDF

open Set Metric Filter
open scoped Topology ContDiff ENNReal NNReal

set_option maxHeartbeats 4000000

/-! ### The chain rule along a real line -/

/-- The `k`-th iterated (real) derivative of the slice `s ↦ f (z + s • v)` at `t` is the `k`-th
iterated real derivative of `f` at `z + t • v` evaluated on the constant tuple `v`.

This is the chain rule for the affine curve `s ↦ z + s • v`, obtained by composing the
continuous linear map `L s = s • v` with the translate `w ↦ f (z + w)` of `f`. -/
theorem iteratedDeriv_slice_real {n k : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ (k : ℕ∞ω) f Ω)
    {z v : Fin n → ℂ} {t : ℝ} (ht : z + t • v ∈ Ω) :
    iteratedDeriv k (fun s : ℝ => f (z + s • v)) t
      = iteratedFDeriv ℝ k f (z + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] (Fin n → ℂ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hLu : ∀ u : ℝ, L u = u • v := fun u => by simp [L]
  have hL1 : L 1 = v := by simpa using hLu 1
  set s : Set (Fin n → ℂ) := (fun w : Fin n → ℂ => z + w) ⁻¹' Ω with hsdef
  have hs_open : IsOpen s := hΩ.preimage (by continuity)
  have hF0 : ContDiffOn ℝ (k : ℕ∞ω) (fun w : Fin n → ℂ => f (z + w)) s := by
    refine hf.comp ?_ ?_
    · exact (by fun_prop : ContDiffOn ℝ (k:ℕ∞ω) (fun w : Fin n → ℂ => z + w) s)
    · intro w hw; exact hw
  have hpre_open : IsOpen (L ⁻¹' s) := hs_open.preimage L.continuous
  have hmem : L t ∈ s := by rw [hsdef, mem_preimage, hLu]; exact ht
  have hkey := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hF0
      hs_open.uniqueDiffOn hpre_open.uniqueDiffOn (x := t) hmem (i := k) (le_refl (k:ℕ∞ω))
  have hfun : ((fun w : Fin n → ℂ => f (z + w)) ∘ L) = (fun u : ℝ => f (z + u • v)) := by
    funext u; simp [hLu]
  have hleft : iteratedFDerivWithin ℝ k ((fun w : Fin n → ℂ => f (z + w)) ∘ L) (L ⁻¹' s) t
      = iteratedFDeriv ℝ k (fun u : ℝ => f (z + u • v)) t := by
    rw [iteratedFDerivWithin_of_isOpen k hpre_open (mem_preimage.mpr hmem), hfun]
  have hright : iteratedFDerivWithin ℝ k (fun w : Fin n → ℂ => f (z + w)) s (L t)
      = iteratedFDeriv ℝ k f (z + t • v) := by
    rw [iteratedFDerivWithin_of_isOpen k hs_open hmem, hLu t]
    exact iteratedFDeriv_comp_add_left k z (t • v)
  have hmain : iteratedFDeriv ℝ k (fun u : ℝ => f (z + u • v)) t
      = (iteratedFDeriv ℝ k f (z + t • v)).compContinuousLinearMap (fun _ => L) := by
    rw [← hleft, hkey, hright]
  rw [iteratedDeriv_eq_iteratedFDeriv, hmain,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [hL1]

/-! ### The one-variable criterion -/

/-- If `h : ℝ → ℂ` is smooth on a neighbourhood of `[0,1]` and the `k`-th derivative of `h` on
`[0,1]` is bounded by `C * s ^ k * k !` with `0 ≤ s < 1`, then the Taylor series of `h` at `0`
converges to `h 1`. -/
theorem hasSum_taylor_of_bound {h : ℝ → ℂ} {C s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞ω) h (Metric.ball (0:ℝ) 2))
    (hbd : ∀ k : ℕ, ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv k h t‖ ≤ C * s ^ k * (k.factorial : ℝ)) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • iteratedDeriv n h 0) (h 1) := by
  set u : ℕ → ℂ := fun n => (n.factorial : ℝ)⁻¹ • iteratedDeriv n h 0 with hudef
  have hinball : ∀ t ∈ Icc (0:ℝ) 1, t ∈ Metric.ball (0:ℝ) 2 := by
    intro t ht
    simp only [mem_Icc] at ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hmem : ∀ t ∈ Icc (0:ℝ) 1, (Metric.ball (0:ℝ) 2) ∈ 𝓝 t :=
    fun t ht => Metric.isOpen_ball.mem_nhds (hinball t ht)
  -- the Taylor polynomial is the partial sum of the series
  have hTaylor : ∀ N : ℕ, taylorWithinEval h N (Icc 0 1) 0 1 = ∑ k ∈ Finset.range (N+1), u k := by
    intro N
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hcd : ContDiffAt ℝ (k:ℕ∞ω) h 0 :=
      (hsm k).contDiffAt (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 2))
    have huu : iteratedDerivWithin k h (Icc 0 1) 0 = iteratedDeriv k h 0 :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) hcd (by norm_num)
    rw [huu, hudef]
    simp
  -- Lagrange remainder bound
  have hbound : ∀ N : ℕ, ‖h 1 - taylorWithinEval h N (Icc 0 1) 0 1‖ ≤
      C * s ^ (N+1) * ((N+1).factorial : ℝ) * 1 ^ (N+1) / (N.factorial : ℝ) := by
    intro N
    have hf : ContDiffOn ℝ ((N+1 : ℕ) : ℕ∞ω) h (Icc 0 1) :=
      (hsm (N+1)).mono (fun t ht => hinball t ht)
    have hC : ∀ y ∈ Icc (0:ℝ) 1,
        ‖iteratedDerivWithin (N+1) h (Icc 0 1) y‖ ≤ C * s ^ (N+1) * ((N+1).factorial : ℝ) := by
      intro y hy
      have hcd : ContDiffAt ℝ ((N+1 : ℕ):ℕ∞ω) h y := (hsm (N+1)).contDiffAt (hmem y hy)
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) hcd hy]
      exact hbd (N+1) y hy
    have := taylor_mean_remainder_bound (f := h) (a := 0) (b := 1)
      (C := C * s ^ (N+1) * ((N+1).factorial : ℝ)) (x := 1) (n := N)
      (by norm_num) (by simpa using hf) (by norm_num) hC
    simpa using this
  -- the remainder tends to zero
  have hg : Tendsto (fun N : ℕ => C * s ^ (N+1) * ((N+1).factorial : ℝ) * 1 ^ (N+1) / (N.factorial : ℝ))
      atTop (𝓝 0) := by
    have heq : (fun N : ℕ => C * s ^ (N+1) * ((N+1).factorial : ℝ) * 1 ^ (N+1) / (N.factorial : ℝ))
        = fun N : ℕ => C * (s ^ (N+1) * ((N:ℝ) + 1)) := by
      funext N
      have hfac : ((N+1).factorial : ℝ) = ((N:ℝ)+1) * (N.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac, one_pow, mul_one]
      field_simp
    rw [heq]
    have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hs0 hs1
    have h2 : Tendsto (fun N : ℕ => ((N:ℝ) + 1) * s ^ (N+1)) atTop (𝓝 0) := by
      have := h1.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, pow_one, Nat.cast_add, add_comm] using this
    have h3 := h2.const_mul C
    simpa [mul_comm, mul_left_comm, mul_assoc] using h3
  have hlim : Tendsto (fun N : ℕ => taylorWithinEval h N (Icc 0 1) 0 1) atTop (𝓝 (h 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun N => norm_nonneg _) (fun N => by rw [norm_sub_rev]; exact hbound N) hg
  have hpart : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N+1), u k) atTop (𝓝 (h 1)) := by
    simpa only [hTaylor] using hlim
  have hpart' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, u k) atTop (𝓝 (h 1)) :=
    (tendsto_add_atTop_iff_nat (f := fun N => ∑ k ∈ Finset.range N, u k) 1).mp hpart
  have hsumm : Summable (fun k => ‖u k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hs0 hs1).mul_left |C|)
    have h1 : ‖u k‖ ≤ C * s ^ k := by
      have hx : ‖iteratedDeriv k h 0‖ ≤ C * s ^ k * ((k.factorial:ℝ)) := hbd k 0 (by norm_num)
      calc ‖u k‖ = ((k.factorial:ℝ))⁻¹ * ‖iteratedDeriv k h 0‖ := by
              rw [hudef]; simp
        _ ≤ ((k.factorial:ℝ))⁻¹ * (C * s^k * (k.factorial:ℝ)) := by gcongr
        _ = C * s^k := by field_simp
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hs0 k))
  exact (hasSum_iff_tendsto_nat_of_summable_norm hsumm).mpr hpart'

/-! ### Analyticity at a point -/

/-- If the iterated real derivatives of `f` on a ball around `z` are bounded by
`C * M ^ k * k !`, then `f` is real analytic at `z`. -/
theorem analyticAt_of_iteratedFDeriv_le_factorial {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} {R C M : ℝ} (hR : 0 < R) (hC : 0 < C) (hM : 0 < M)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ (k : ℕ∞ω) f (Metric.ball z R))
    (hbd : ∀ k : ℕ, ∀ y ∈ Metric.ball z R,
        ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * (k.factorial : ℝ)) :
    AnalyticAt ℝ f z := by
  have hrpos : 0 < min (R/2) (1/(2*M)) := lt_min (by positivity) (by positivity)
  set r : ℝ≥0 := (min (R/2) (1/(2*M))).toNNReal with hrdef
  have hrc : (r : ℝ) = min (R/2) (1/(2*M)) := by
    rw [hrdef]; exact Real.coe_toNNReal _ hrpos.le
  have hrpos' : 0 < r := by rw [← NNReal.coe_pos, hrc]; exact hrpos
  have hrR : (r:ℝ) ≤ R/2 := by rw [hrc]; exact min_le_left _ _
  have hrM : (r:ℝ) ≤ 1/(2*M) := by rw [hrc]; exact min_le_right _ _
  have hMr : M * (r:ℝ) ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hrM hM.le
    rwa [show M * (1/(2*M)) = 1/2 by field_simp] at h
  let p : FormalMultilinearSeries ℝ (Fin n → ℂ) ℂ :=
    fun k => (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f z
  have hp_bound : ∀ k : ℕ, ‖p k‖ ≤ C * M^k := by
    intro k
    have hzk : z ∈ Metric.ball z R := Metric.mem_ball_self hR
    have hb := hbd k z hzk
    have hpk : p k = (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f z := rfl
    rw [hpk, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ((k.factorial:ℝ))⁻¹)]
    calc ((k.factorial:ℝ))⁻¹ * ‖iteratedFDeriv ℝ k f z‖
        ≤ ((k.factorial:ℝ))⁻¹ * (C * M^k * (k.factorial:ℝ)) := by gcongr
      _ = C * M^k := by field_simp
  have hle : (r : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound C ?_
    intro k
    have hMk : (M * (r:ℝ))^k ≤ (1/2:ℝ)^k :=
      pow_le_pow_left₀ (mul_nonneg hM.le (by positivity)) hMr k
    calc ‖p k‖ * (r:ℝ)^k ≤ (C * M^k) * (r:ℝ)^k := by gcongr; exact hp_bound k
      _ = C * (M * (r:ℝ))^k := by rw [mul_pow]; ring
      _ ≤ C * (1/2:ℝ)^k := by gcongr
      _ ≤ C * 1 := by
          gcongr
          exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = C := by ring
  refine HasFPowerSeriesOnBall.analyticAt ⟨hle, by exact_mod_cast hrpos', ?_⟩
  intro y hy
  rw [Metric.mem_eball] at hy
  have hyco : (‖y‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) := by simpa [edist_eq_enorm_sub] using hy
  have hynn : ‖y‖₊ < r := ENNReal.coe_lt_coe.mp hyco
  have hyr : ‖y‖ < (r:ℝ) := by
    have : (‖y‖₊ : ℝ) < (r : ℝ) := by exact_mod_cast hynn
    rwa [coe_nnnorm] at this
  have hyR : ‖y‖ < R/2 := lt_of_lt_of_le hyr hrR
  have hyM : M * ‖y‖ < 1 := by
    have h : M * ‖y‖ < M * (1/(2*M)) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hyr hrM) hM
    rw [show M * (1/(2*M)) = 1/2 by field_simp] at h
    linarith
  have hyM0 : 0 ≤ M * ‖y‖ := mul_nonneg hM.le (norm_nonneg _)
  have hmap : ∀ t ∈ Metric.ball (0:ℝ) 2, z + t • y ∈ Metric.ball z R := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm] at ht ⊢
    rw [show z + t • y - z = t • y from by abel, norm_smul, Real.norm_eq_abs]
    have ht2 : |t| < 2 := by simpa [Real.norm_eq_abs] using ht
    calc |t| * ‖y‖ ≤ 2 * ‖y‖ := mul_le_mul_of_nonneg_right ht2.le (norm_nonneg _)
      _ < 2 * (R/2) := mul_lt_mul_of_pos_left hyR (by norm_num)
      _ = R := by ring
  have hsm' : ∀ k : ℕ, ContDiffOn ℝ (k:ℕ∞ω) (fun t : ℝ => f (z + t • y))
      (Metric.ball (0:ℝ) 2) := by
    intro k
    exact (hsm k).comp (by fun_prop) hmap
  have hbd' : ∀ k : ℕ, ∀ t ∈ Icc (0:ℝ) 1,
      ‖iteratedDeriv k (fun t : ℝ => f (z + t • y)) t‖ ≤ C * (M * ‖y‖) ^ k * (k.factorial : ℝ) := by
    intro k t ht
    have htR : z + t • y ∈ Metric.ball z R := by
      refine hmap t ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
      linarith [ht.2]
    have hslice : iteratedDeriv k (fun t : ℝ => f (z + t • y)) t
        = iteratedFDeriv ℝ k f (z + t • y) (fun _ => y) :=
      iteratedDeriv_slice_real (Ω := Metric.ball z R) (v := y) (t := t) Metric.isOpen_ball
        (hsm k) htR
    rw [hslice]
    have hop := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ k f (z + t • y)) (fun _ : Fin k => y)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hop
    calc ‖iteratedFDeriv ℝ k f (z + t • y) (fun _ => y)‖
        ≤ ‖iteratedFDeriv ℝ k f (z + t • y)‖ * ‖y‖^k := hop
      _ ≤ (C * M^k * (k.factorial:ℝ)) * ‖y‖^k := by gcongr; exact hbd k _ htR
      _ = C * (M * ‖y‖)^k * (k.factorial:ℝ) := by rw [mul_pow]; ring
  have hmain := hasSum_taylor_of_bound (h := fun t : ℝ => f (z + t • y))
    (C := C) (s := M * ‖y‖) hyM0 hyM hsm' hbd'
  have h0R : z + (0:ℝ) • y ∈ Metric.ball z R := by
    rw [zero_smul, add_zero]; exact Metric.mem_ball_self hR
  have hterm : ∀ k : ℕ,
      p k (fun _ => y) = (k.factorial:ℝ)⁻¹ • iteratedDeriv k (fun t : ℝ => f (z + t • y)) 0 := by
    intro k
    have hslice : iteratedDeriv k (fun t : ℝ => f (z + t • y)) 0
        = iteratedFDeriv ℝ k f (z + (0:ℝ) • y) (fun _ => y) :=
      iteratedDeriv_slice_real (Ω := Metric.ball z R) (v := y) (t := 0) Metric.isOpen_ball
        (hsm k) h0R
    rw [show p k = (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k f z from rfl]
    rw [hslice, zero_smul, add_zero]
    exact smul_apply _ _ _
  have hfin := hmain.congr_fun hterm
  rw [one_smul] at hfin
  exact hfin

/-! ### The target statement -/

/-- **Real analyticity from factorial growth of the iterated derivatives.**

If `f : (Fin n → ℂ) → ℂ` is smooth on `Metric.ball x ρ` and every iterated real derivative of `f`
on that ball is bounded by `C * M ^ k * k !`, then `f` is real analytic on a ball around `x`. -/
theorem analyticOn_of_iteratedFDeriv_le_factorial {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {x : Fin n → ℂ} {ρ C M : ℝ} (hρ : 0 < ρ) (hC : 0 < C) (hM : 0 < M)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k f (Metric.ball x ρ))
    (hbd : ∀ k : ℕ, ∀ y ∈ Metric.ball x ρ,
        ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * (k.factorial : ℝ)) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ AnalyticOn ℝ f (Metric.ball x ρ') := by
  have hρ' : 0 < min ρ (1/(2*M)) / 2 := div_pos (lt_min hρ (by positivity)) (by norm_num)
  refine ⟨min ρ (1/(2*M)) / 2, hρ', ?_⟩
  rw [Metric.isOpen_ball.analyticOn_iff_analyticOnNhd]
  intro z hz
  rw [Metric.mem_ball] at hz
  have hRpos : 0 < ρ - dist z x := by
    have h2 : min ρ (1/(2*M)) / 2 ≤ ρ / 2 := by
      gcongr; exact min_le_left _ _
    linarith
  refine analyticAt_of_iteratedFDeriv_le_factorial hRpos hC hM ?_ ?_
  · intro k
    refine (hsm k).mono ?_
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    calc dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ < (ρ - dist z x) + dist z x := by linarith [hw]
      _ = ρ := by ring
  · intro k w hw
    refine hbd k w ?_
    rw [Metric.mem_ball] at hw ⊢
    calc dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ < (ρ - dist z x) + dist z x := by linarith [hw]
      _ = ρ := by ring

end Work.NN.Core.TelTwoDF
