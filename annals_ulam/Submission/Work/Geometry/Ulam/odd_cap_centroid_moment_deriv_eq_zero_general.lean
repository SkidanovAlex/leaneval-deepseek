import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Commons.Geometry.Ulam.odd_moment_integral_hasDerivAt
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval
import Submission.Commons.Geometry.Ulam.concaveOn_Icc_bounded
import Submission.Work.Geometry.Ulam.active_nonneg_outside_of_roots_inside_general
import Submission.Work.Geometry.Ulam.odd_active_integral_eq_interval_general
import Submission.Work.Geometry.Ulam.odd_pow_clamp_integral_eq_interval_of_active_general

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma odd_weight_eq_zero_of_not_active {n : ℕ} {f L : ℝ}
    (hf_nonneg : 0 ≤ f)
    (hnot : ¬ (-f < L ∧ L < f)) :
    (f ^ 2 - L ^ 2) ^ (n - 1) * Real.sqrt (f ^ 2 - L ^ 2) = 0 := by
  have hbase_nonpos : f ^ 2 - L ^ 2 ≤ 0 := by
    by_cases hL_le : L ≤ -f
    · have hf_le_negL : f ≤ -L := by linarith
      have hL_nonneg_neg : 0 ≤ -L := by linarith
      have hsq : f ^ 2 ≤ L ^ 2 := by
        rw [← neg_sq L]
        exact (sq_le_sq₀ hf_nonneg hL_nonneg_neg).2 hf_le_negL
      nlinarith
    · have hnegf_lt_L : -f < L := lt_of_not_ge hL_le
      have hf_le_L : f ≤ L := le_of_not_gt (by
        intro hLf
        exact hnot ⟨hnegf_lt_L, hLf⟩)
      have hL_nonneg : 0 ≤ L := le_trans hf_nonneg hf_le_L
      have hsq : f ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hf_nonneg hL_nonneg).2 hf_le_L
      nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hbase_nonpos, mul_zero]

lemma odd_pow_weight_eq_zero_of_not_active {n : ℕ} {f L : ℝ}
    (hf_nonneg : 0 ≤ f)
    (hnot : ¬ (-f < L ∧ L < f)) :
    (f ^ 2 - L ^ 2) ^ n * Real.sqrt (f ^ 2 - L ^ 2) = 0 := by
  have hbase_nonpos : f ^ 2 - L ^ 2 ≤ 0 := by
    by_cases hL_le : L ≤ -f
    · have hf_le_negL : f ≤ -L := by linarith
      have hL_nonneg_neg : 0 ≤ -L := by linarith
      have hsq : f ^ 2 ≤ L ^ 2 := by
        rw [← neg_sq L]
        exact (sq_le_sq₀ hf_nonneg hL_nonneg_neg).2 hf_le_negL
      nlinarith
    · have hnegf_lt_L : -f < L := lt_of_not_ge hL_le
      have hf_le_L : f ≤ L := le_of_not_gt (by
        intro hLf
        exact hnot ⟨hnegf_lt_L, hLf⟩)
      have hL_nonneg : 0 ≤ L := le_trans hf_nonneg hf_le_L
      have hsq : f ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hf_nonneg hL_nonneg).2 hf_le_L
      nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hbase_nonpos, mul_zero]



lemma hasDerivAt_const_div_sqrt_one_add_sq (C s : ℝ) :
    HasDerivAt (fun r : ℝ => C / Real.sqrt (1 + r ^ 2))
      (-(C * s) / Real.sqrt (1 + s ^ 2) ^ 3) s := by
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * s) s := by
    have h := (hasDerivAt_const s (1:ℝ)).add (hasDerivAt_pow 2 s)
    have hd : HasDerivAt ((fun x : ℝ => 1) + fun x : ℝ => x ^ 2) (2 * s) s := by
      simpa [show (0 : ℝ) + 2 * s ^ (2 - 1) = 2 * s by ring] using h
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [] with r
      simp [Pi.add_apply])
  have hpos : 0 < 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hsqrt : HasDerivAt (fun r : ℝ => Real.sqrt (1 + r ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s := by
    exact h1.sqrt (ne_of_gt hpos)
  have hden_ne : Real.sqrt (1 + s ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hdiv : HasDerivAt (fun r : ℝ => C / Real.sqrt (1 + r ^ 2))
      (-(C * ((2 * s) / (2 * Real.sqrt (1 + s ^ 2)))) / (Real.sqrt (1 + s ^ 2) ^ 2)) s := by
    have hc : HasDerivAt (fun _ : ℝ => C) 0 s := hasDerivAt_const s C
    have h := HasDerivAt.div (𝕜 := ℝ) (𝕜' := ℝ) hc hsqrt hden_ne
    have hd : HasDerivAt ((fun _ : ℝ => C) / fun r : ℝ => Real.sqrt (1 + r ^ 2))
        (-(C * ((2 * s) / (2 * Real.sqrt (1 + s ^ 2)))) / (Real.sqrt (1 + s ^ 2) ^ 2)) s := by
      simpa [sub_eq_add_neg, zero_mul, zero_sub] using h
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [] with r
      simp [Pi.div_apply])
  convert hdiv using 1
  have hsq_sqrt : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
  field_simp [hsq_sqrt, hden_ne]



lemma odd_cap_centroid_moment_deriv_eq_zero_general {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    {A B : ℝ} (hAB : A < B) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc A B)
    (hf_cont : ContDiffOn ℝ (⊤ : WithTop ℕ∞) f (Set.Ioo A B))
    (hf_conc : ConcaveOn ℝ (Set.Icc A B) f)
    (hf_left : f A = 0) (hf_right : f B = 0)
    (hf_pos : ∀ t ∈ Set.Ioo A B, 0 < f t)
    (hh_cont : ContDiffOn ℝ (⊤ : WithTop ℕ∞) h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo A B ∧ y s ∈ Set.Ioo A B)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in A..B,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0) = 0 := by
  intro s hs
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  rcases hxy_inside s hs with ⟨hp_mem, hq_mem⟩
  let p : ℝ := -x s
  let q : ℝ := y s
  have hp_neg : p < 0 := by dsimp [p]; linarith
  have hq_pos : 0 < q := by dsimp [q]; exact hypos
  have hfp_sq : f p ^ 2 = (s * p + h s) ^ 2 := by simpa [p] using hfx_sq
  have hfq_sq : f q ^ 2 = (s * q + h s) ^ 2 := by simpa [q] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t :=
    profile_nonneg_Icc_general (a := A) (b := B) hAB.le hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    profile_measurable_smooth_general (a := A) (b := B) hAB.le hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc A B) :=
    concaveOn_Icc_bounded hAB.le hf_conc
  have hactive := active_nonneg_outside_of_roots_inside_general (f := f) (s := s) (h := h s)
    (u := p) (v := q) (α := A) (β := B) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (L t) ^ 2)
  let Gpow : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (L t) ^ 2)
  let Cder : ℝ := deriv h s
  let D : ℝ → ℝ := fun t => (t + s * (L t)) * W t * (t + Cder) - Gpow t / (2 * (n : ℝ) + 1)
  have hD_zero_out : ∀ t ∈ Set.Icc A B, ¬ (-f t < L t ∧ L t < f t) → D t = 0 := by
    intro t ht hnot
    have hW0 : W t = 0 := by
      dsimp [W, L]
      exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    have hG0 : Gpow t = 0 := by
      dsimp [Gpow, L]
      exact odd_pow_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    dsimp [D]
    rw [hW0, hG0]
    simp
  have hD_p : D p = 0 := by
    have hbase : f p ^ 2 - (L p) ^ 2 = 0 := by
      dsimp [L]
      rw [hfp_sq]
      ring
    have hWp : W p = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    have hGp : Gpow p = 0 := by
      dsimp [Gpow, L]
      rw [hbase]
      simp
    dsimp [D]
    rw [hWp, hGp]
    simp
  have hD_q : D q = 0 := by
    have hbase : f q ^ 2 - (L q) ^ 2 = 0 := by
      dsimp [L]
      rw [hfq_sq]
      ring
    have hWq : W q = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    have hGq : Gpow q = 0 := by
      dsimp [Gpow, L]
      rw [hbase]
      simp
    dsimp [D]
    rw [hWq, hGq]
    simp
  have hconv : (∫ t in A..B, if -f t < L t ∧ L t < f t then D t else 0) =
      ∫ t in p..q, D t := by
    simpa [L] using odd_active_integral_eq_interval_general (f := f) (s := s) (h := h s) (a := p) (b := q) (A := A) (B := B) hAB
      (D := D) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq hD_zero_out hD_p hD_q
  have hI : (∫ t in p..q, Gpow t) = C / Real.sqrt (1 + s ^ 2) := by
    have hI0 := h_moment s hs
    simpa [p, q, Gpow, L] using hI0
  have hJcenter : (∫ t in p..q, W t * (t + Cder)) = 0 := by
    have hJ0 := h_center s hs
    simpa [p, q, W, L, Cder] using hJ0
  have hpq_le : p ≤ q := le_of_lt (lt_trans hp_neg hq_pos)
  have hf_cont_ab : ContinuousOn f (Set.Icc p q) := by
    exact hf_cont.continuousOn.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hp_mem.1 ht.1, lt_of_le_of_lt ht.2 hq_mem.2⟩)
  have hG_nonneg_on : ∀ t ∈ Set.Icc p q, 0 ≤ f t ^ 2 - L t ^ 2 := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have h1 : 0 ≤ f t - L t := hnonneg.1
    have h2 : 0 ≤ f t + L t := hnonneg.2
    nlinarith [mul_nonneg h1 h2]
  have hG_cont : ContinuousOn (fun t : ℝ => f t ^ 2 - L t ^ 2) (Set.Icc p q) := by
    dsimp [L]
    have hf_sq : ContinuousOn (fun t : ℝ => f t ^ 2) (Set.Icc p q) := hf_cont_ab.pow 2
    have hL_aff : ContinuousOn (fun t : ℝ => (s * t + h s) ^ 2) (Set.Icc p q) := by
      fun_prop
    exact hf_sq.sub hL_aff
  have hW_cont : ContinuousOn W (Set.Icc p q) := by
    dsimp [W]
    exact (hG_cont.pow (n - 1)).mul hG_cont.sqrt
  have hGpow_cont : ContinuousOn Gpow (Set.Icc p q) := by
    dsimp [Gpow]
    exact (hG_cont.pow n).mul hG_cont.sqrt
  have hL_cont : ContinuousOn L (Set.Icc p q) := by
    dsimp [L]
    fun_prop
  have hid_cont : ContinuousOn (fun t : ℝ => t) (Set.Icc p q) := continuousOn_id
  have hD_interval : (∫ t in p..q, D t) =
      (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) -
        (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1) := by
    have hfun : Set.EqOn (fun t : ℝ => (t + s * L t) * W t * (t + Cder)) (fun t : ℝ =>
        (1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder))) (Set.Icc p q) := by
      intro t ht
      dsimp [L]
      ring
    have h_int1 : (∫ t in p..q, (t + s * L t) * W t * (t + Cder)) =
        ∫ t in p..q, ((1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc p q := by
        rwa [Set.uIcc_of_le hpq_le] at ht
      exact hfun htIcc
    have h_int2 : (∫ t in p..q, ((1 + s ^ 2) * (W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (W t * (t + Cder)))) =
        (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (∫ t in p..q, W t * (t + Cder)) := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
      · have h1 : ContinuousOn (fun t : ℝ => W t * (t + Cder) ^ 2) (Set.Icc p q) := by
          exact hW_cont.mul ((hid_cont.add continuousOn_const).pow 2)
        exact (continuousOn_const.mul h1).intervalIntegrable_of_Icc hpq_le
      · have h2 : ContinuousOn (fun t : ℝ => W t * (t + Cder)) (Set.Icc p q) := by
          exact hW_cont.mul (hid_cont.add continuousOn_const)
        exact (continuousOn_const.mul h2).intervalIntegrable_of_Icc hpq_le
    have h_int3 : (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) +
          (s * h s - (1 + s ^ 2) * Cder) * (∫ t in p..q, W t * (t + Cder)) =
        (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
      rw [hJcenter]
      simp
    have hD_eq : (∫ t in p..q, D t) =
        (∫ t in p..q, (t + s * L t) * W t * (t + Cder)) -
          (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1) := by
      dsimp [D]
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_div]
      · have h1 : ContinuousOn (fun t : ℝ => (t + s * L t) * W t * (t + Cder)) (Set.Icc p q) := by
          exact ((hid_cont.add (continuousOn_const.mul hL_cont)).mul hW_cont).mul
            (hid_cont.add continuousOn_const)
        exact h1.intervalIntegrable_of_Icc hpq_le
      · exact (hGpow_cont.div_const (2 * (n : ℝ) + 1)).intervalIntegrable_of_Icc hpq_le
    rw [hD_eq, h_int1, h_int2, h_int3]
  have hQ_deriv := odd_moment_integral_hasDerivAt (n := n) (f := f) (h := h) (a := A) (b := B)
    hn hAB.le hf_nonneg hf_meas hf_bdd hh_cont s
  have hR_deriv := hasDerivAt_const_div_sqrt_one_add_sq C s
  let Qfun : ℝ → ℝ := fun r => ∫ t in A..B,
      (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2) ^ n *
        Real.sqrt (f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2)
  let Qfun_unclamped : ℝ → ℝ := fun r => ∫ t in A..B, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)
  let Rfun : ℝ → ℝ := fun r => C / Real.sqrt (1 + r ^ 2)
  have hQ_eq_event : Qfun =ᶠ[𝓝 s] Rfun := by
    have hpos_ev : ∀ᶠ r in 𝓝 s, 0 < r := by
      exact (isOpen_Ioi.mem_nhds hs)
    filter_upwards [hpos_ev] with r hr
    have hrxy := hxy r hr
    have hrinside := hxy_inside r hr
    rcases hrxy with ⟨hxr, hyr, hfy_r, hfx_r⟩
    let ar : ℝ := -x r
    let br : ℝ := y r
    have har_mem : ar ∈ Set.Ioo A B := by simpa [ar] using hrinside.1
    have hbr_mem : br ∈ Set.Ioo A B := by simpa [br] using hrinside.2
    have har_neg : ar < 0 := by dsimp [ar]; linarith
    have hbr_pos : 0 < br := by dsimp [br]; exact hyr
    have hfar_sq : f ar ^ 2 = (r * ar + h r) ^ 2 := by simpa [ar] using hfx_r
    have hfbr_sq : f br ^ 2 = (r * br + h r) ^ 2 := by simpa [br] using hfy_r
    have hpow_eq := odd_pow_clamp_integral_eq_interval_of_active_general (n := n) (f := f) (s := r) (h := h r) (A := A) (B := B) hn hr hAB
      (a := ar) (b := br) har_mem hbr_mem har_neg hbr_pos hf_conc hf_nonneg hf_pos hfar_sq hfbr_sq
    have hI_r := h_moment r hr
    calc
      Qfun r = ∫ t in ar..br, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) := by
        dsimp [Qfun]
        simpa using hpow_eq
      _ = C / Real.sqrt (1 + r ^ 2) := by
        simpa [ar, br] using hI_r
      _ = Rfun r := by dsimp [Rfun]
  have hQfun_eq_unclamped : Qfun =ᶠ[𝓝 s] Qfun_unclamped := by
    have hpos_ev : ∀ᶠ r in 𝓝 s, 0 < r := by
      exact (isOpen_Ioi.mem_nhds hs)
    filter_upwards [hpos_ev] with r hr
    dsimp [Qfun, Qfun_unclamped]
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases hact : -f t < r * t + h r ∧ r * t + h r < f t
    · have hU : max (-f t) (min (f t) (r * t + h r)) = r * t + h r := by
        rw [min_eq_right hact.2.le, max_eq_right hact.1.le]
      simp [hU]
    · have hU_base_zero : f t ^ 2 - (max (-f t) (min (f t) (r * t + h r))) ^ 2 = 0 := by
        have hle_or : r * t + h r ≤ -f t ∨ f t ≤ r * t + h r := by
          by_contra hboth
          have hnot := not_or.mp hboth
          have hlt_lower : -f t < r * t + h r := lt_of_not_ge hnot.1
          have hlt_upper : r * t + h r < f t := lt_of_not_ge hnot.2
          exact hact ⟨hlt_lower, hlt_upper⟩
        rcases hle_or with hL_low | hL_high
        · have hmin : min (f t) (r * t + h r) = r * t + h r := by
            rw [min_eq_right (le_trans hL_low (by
              have htIcc : t ∈ Set.Icc A B := by
                simpa [Set.uIcc_of_le hAB.le] using ht
              linarith [hf_nonneg t htIcc]))]
          have hU : max (-f t) (min (f t) (r * t + h r)) = -f t := by
            rw [hmin]
            exact max_eq_left hL_low
          rw [hU]
          ring
        · have hmin : min (f t) (r * t + h r) = f t := by
            rw [min_eq_left hL_high]
          have hU : max (-f t) (min (f t) (r * t + h r)) = f t := by
            rw [hmin]
            exact max_eq_right (by
              have htIcc : t ∈ Set.Icc A B := by
                simpa [Set.uIcc_of_le hAB.le] using ht
              linarith [hf_nonneg t htIcc])
          rw [hU]
          ring
      have h_unclamped_zero : (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) = 0 := by
        have htIcc : t ∈ Set.Icc A B := by
          simpa [Set.uIcc_of_le hAB.le] using ht
        exact odd_pow_weight_eq_zero_of_not_active (n := n) (f := f t) (L := r * t + h r) (hf_nonneg t htIcc) hact
      simp [hU_base_zero, h_unclamped_zero]
  have hQ_derivQ : HasDerivAt Qfun (-(2 * (n : ℝ) + 1) * (∫ t in A..B,
        (s * t + h s) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s))) s := by
    have heq : Qfun =ᶠ[𝓝 s] (fun r : ℝ => ∫ t in A..B, (f t ^ 2 - (r * t + h r) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2)) := by
      simpa [Qfun_unclamped] using hQfun_eq_unclamped
    exact hQ_deriv.congr_of_eventuallyEq heq
  have hQ_deriv' : HasDerivAt Qfun (-(C * s) / Real.sqrt (1 + s ^ 2) ^ 3) s :=
    hR_deriv.congr_of_eventuallyEq hQ_eq_event
  have hder_eq : -(2 * (n : ℝ) + 1) * (∫ t in A..B,
        (s * t + h s) * (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s)) =
      -(C * s) / Real.sqrt (1 + s ^ 2) ^ 3 := by
    have huniq := hQ_derivQ.unique hQ_deriv'
    simpa [Qfun_unclamped, L, W, Cder] using huniq
  have hJL_full : (∫ t in A..B, L t * W t * (t + Cder)) =
      C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hcoef_pos : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hsqrt_pos : 0 < Real.sqrt (1 + s ^ 2) := by
      exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg s])
    have hsqrt3_ne : Real.sqrt (1 + s ^ 2) ^ 3 ≠ 0 := by
      exact pow_ne_zero 3 (ne_of_gt hsqrt_pos)
    have hder_pos : (2 * (n : ℝ) + 1) * (∫ t in A..B, L t * W t * (t + Cder)) =
        (C * s) / Real.sqrt (1 + s ^ 2) ^ 3 := by
      have hder_eq' := hder_eq
      field_simp [hsqrt3_ne] at hder_eq'
      field_simp [hsqrt3_ne]
      simpa [L, W, Cder, mul_comm, mul_left_comm, mul_assoc] using hder_eq'
    have hder_mul : (2 * (n : ℝ) + 1) * (∫ t in A..B, L t * W t * (t + Cder)) *
        Real.sqrt (1 + s ^ 2) ^ 3 = C * s := by
      rw [hder_pos]
      field_simp [hsqrt3_ne]
    field_simp [hcoef_pos, hsqrt3_ne]
    nlinarith [hder_mul]
  have hWzero_out : ∀ t ∈ Set.Icc A B, ¬ (-f t < L t ∧ L t < f t) → L t * W t * (t + Cder) = 0 := by
    intro t ht hnot
    have hW0 : W t = 0 := by
      dsimp [W, L]
      exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t ht) hnot
    rw [hW0]
    simp
  have hJL_end_p : L p * W p * (p + Cder) = 0 := by
    have hbase : f p ^ 2 - (L p) ^ 2 = 0 := by
      dsimp [L]
      rw [hfp_sq]
      ring
    have hWp : W p = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    rw [hWp]
    simp
  have hJL_end_q : L q * W q * (q + Cder) = 0 := by
    have hbase : f q ^ 2 - (L q) ^ 2 = 0 := by
      dsimp [L]
      rw [hfq_sq]
      ring
    have hWq : W q = 0 := by
      dsimp [W, L]
      rw [hbase]
      simp
    rw [hWq]
    simp
  have hJL_interval : (∫ t in p..q, L t * W t * (t + Cder)) =
      C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hfull := hJL_full
    have hconv2 : (∫ t in A..B, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0) =
        ∫ t in p..q, L t * W t * (t + Cder) := by
      simpa [L] using odd_active_integral_eq_interval_general (f := f) (s := s) (h := h s) (a := p) (b := q) (A := A) (B := B) hAB
        (D := fun t => L t * W t * (t + Cder)) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq hWzero_out hJL_end_p hJL_end_q
    have hfull' : (∫ t in A..B, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0) =
        C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
      calc
        (∫ t in A..B, if -f t < L t ∧ L t < f t then L t * W t * (t + Cder) else 0)
            = ∫ t in A..B, L t * W t * (t + Cder) := by
              apply intervalIntegral.integral_congr
              intro t ht
              by_cases hact : -f t < L t ∧ L t < f t
              · simp [hact]
              · have hW0 : W t = 0 := by
                  have htIcc : t ∈ Set.Icc A B := by
                    simpa [Set.uIcc_of_le hAB.le] using ht
                  dsimp [W, L]
                  exact odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := s * t + h s) (hf_nonneg t htIcc) hact
                simp [hact, hW0]
        _ = C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := hfull
    rwa [hconv2] at hfull'
  have hJ2 : (∫ t in p..q, W t * (t + Cder) ^ 2) =
      C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
    have hL_int : (∫ t in p..q, L t * W t * (t + Cder)) =
        s * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
      calc
        (∫ t in p..q, L t * W t * (t + Cder))
            = ∫ t in p..q, (s * t + h s) * W t * (t + Cder) := by
                simp [L]
        _ = ∫ t in p..q, (s * ((t + Cder) * W t * (t + Cder)) + (h s - s * Cder) * (W t * (t + Cder))) := by
                apply intervalIntegral.integral_congr
                intro t ht
                ring_nf
        _ = s * (∫ t in p..q, (t + Cder) * W t * (t + Cder)) + (h s - s * Cder) * (∫ t in p..q, W t * (t + Cder)) := by
                rw [intervalIntegral.integral_add]
                · rw [intervalIntegral.integral_const_mul]
                  rw [intervalIntegral.integral_const_mul]
                · have h1 : ContinuousOn (fun t : ℝ => s * ((t + Cder) * W t * (t + Cder))) (Set.Icc p q) := by
                    exact continuousOn_const.mul (((hid_cont.add continuousOn_const).mul hW_cont).mul (hid_cont.add continuousOn_const))
                  exact h1.intervalIntegrable_of_Icc hpq_le
                · have h2 : ContinuousOn (fun t : ℝ => (h s - s * Cder) * (W t * (t + Cder))) (Set.Icc p q) := by
                    exact continuousOn_const.mul (hW_cont.mul (hid_cont.add continuousOn_const))
                  exact h2.intervalIntegrable_of_Icc hpq_le
        _ = s * (∫ t in p..q, W t * (t + Cder) ^ 2) := by
                rw [hJcenter]
                simp only [mul_zero, add_zero]
                apply congrArg (fun q : ℝ => s * q)
                apply intervalIntegral.integral_congr
                intro t ht
                ring
    have hs_ne : s ≠ 0 := ne_of_gt hs
    calc
      (∫ t in p..q, W t * (t + Cder) ^ 2)
          = (∫ t in p..q, L t * W t * (t + Cder)) / s := by
            rw [hL_int]
            field_simp [hs_ne]
      _ = (C * s / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) / s := by rw [hJL_interval]
      _ = C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3) := by
            field_simp [hs_ne]
  have hD_zero : (∫ t in p..q, D t) = 0 := by
    rw [hD_interval]
    have hsq : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg s])]
    have hden_ne : Real.sqrt (1 + s ^ 2) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg s]))
    have hcoef_pos : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    calc
      (1 + s ^ 2) * (∫ t in p..q, W t * (t + Cder) ^ 2) -
          (∫ t in p..q, Gpow t) / (2 * (n : ℝ) + 1)
          = (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) -
              (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1) := by
            rw [hJ2, hI]
      _ = 0 := by
            have hsqrt3_eq : Real.sqrt (1 + s ^ 2) ^ 3 = (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) := by
              rw [pow_succ, hsq]
            calc
              (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2) ^ 3)) -
                  (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1)
                  = (1 + s ^ 2) * (C / ((2 * (n : ℝ) + 1) * ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)))) -
                      (C / Real.sqrt (1 + s ^ 2)) / (2 * (n : ℝ) + 1) := by
                    rw [hsqrt3_eq]
              _ = C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2)) -
                    C / ((2 * (n : ℝ) + 1) * Real.sqrt (1 + s ^ 2)) := by
                    field_simp [hsq, hden_ne, hcoef_pos]
              _ = 0 := by ring
  calc
    (∫ t in A..B,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (t + s * (s * t + h s)) * ((f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
            Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) * (t + deriv h s) -
          ((f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) /
            (2 * (n : ℝ) + 1)
        else 0)
        = ∫ t in p..q, D t := by
          simpa [D, L, W, Gpow, Cder] using hconv
    _ = 0 := hD_zero


end Commons.Geometry.Ulam
