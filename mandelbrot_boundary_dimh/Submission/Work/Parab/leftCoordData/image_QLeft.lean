import Mathlib
import Submission.Work.Parab.Setup
import Submission.Work.Parab.leftCoordData.norm_log_sub_le
import Submission.Work.Parab.leftCoordData.exists_preimage_ballL

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Parab.leftCoordData

open Complex Set Metric Filter
open scoped Topology

noncomputable section

open Filter

private lemma mul_log_eventually_le (c : ℝ) (hc : 0 ≤ c) (m : ℝ) (hm : 0 < m) :
    ∀ᶠ s : ℝ in Filter.atTop, c * Real.log s ≤ s / m := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with s hs
    simp only [zero_mul]
    positivity
  · have hO : (fun s : ℝ => Real.log s) =o[Filter.atTop] (fun s : ℝ => s) := by
      simpa using isLittleO_log_rpow_atTop (show (0:ℝ) < 1 by norm_num)
    have hε : ∀ᶠ s : ℝ in Filter.atTop, ‖Real.log s‖ ≤ (1 / (m * c)) * ‖s‖ :=
      (Asymptotics.isLittleO_iff.mp hO) (show (0:ℝ) < 1 / (m * c) by positivity)
    filter_upwards [hε, Filter.eventually_ge_atTop (1:ℝ)] with s hs hs1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hs1),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ s)] at hs
    have h2 : Real.log s ≤ s / (m * c) := by
      have h' := hs
      rw [one_div, mul_comm] at h'
      exact h'
    calc c * Real.log s ≤ c * (s / (m * c)) := mul_le_mul_of_nonneg_left h2 hc
      _ = s / m := by field_simp

private theorem thresholds {A M₀ M₁ K R : ℝ} (hA : 0 ≤ A) (hK : 0 < K) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ s : ℝ, ξ ≤ s →
      4 ≤ Real.log s ∧ 16 ≤ s ∧ 4 * (M₀ + 2) ≤ s ∧ R + 2 ≤ s / 4 ∧
      R + 2 ≤ (K / 2) * Real.log s ∧
      K * (Real.log s + M₁ + 2) ≤ (Real.sqrt 3 / 2) * s ∧
      A * (Real.log s + Real.pi) ≤ s / 4 ∧
      512 * A * (A * (Real.log s + Real.pi) + 1) ≤ s := by
  have hδ : (0:ℝ) < Real.sqrt 3 / 2 - 1 / 6 := by
    have h3 : (1:ℝ) < Real.sqrt 3 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have e1 : ∀ᶠ s : ℝ in Filter.atTop, 4 ≤ Real.log s :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 4)
  have e2 : ∀ᶠ s : ℝ in Filter.atTop, (16:ℝ) ≤ s := Filter.eventually_ge_atTop 16
  have e3 : ∀ᶠ s : ℝ in Filter.atTop, 4 * (M₀ + 2) ≤ s :=
    Filter.eventually_ge_atTop (4 * (M₀ + 2))
  have e4 : ∀ᶠ s : ℝ in Filter.atTop, R + 2 ≤ s / 4 := by
    filter_upwards [Filter.eventually_ge_atTop (4 * (R + 2))] with s hs
    linarith
  have e5 : ∀ᶠ s : ℝ in Filter.atTop, R + 2 ≤ (K / 2) * Real.log s := by
    have h2 : ∀ᶠ s : ℝ in Filter.atTop, 2 * (R + 2) / K ≤ Real.log s :=
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (2 * (R + 2) / K))
    filter_upwards [h2] with s hs
    rw [div_le_iff₀ hK] at hs
    linarith
  have e6 : ∀ᶠ s : ℝ in Filter.atTop,
      K * (Real.log s + M₁ + 2) ≤ (Real.sqrt 3 / 2) * s := by
    have h6a : ∀ᶠ s : ℝ in Filter.atTop, K * Real.log s ≤ s / 6 :=
      mul_log_eventually_le K hK.le 6 (by norm_num)
    have h6b : ∀ᶠ s : ℝ in Filter.atTop, K * (M₁ + 2) ≤ (Real.sqrt 3 / 2 - 1 / 6) * s := by
      filter_upwards [Filter.eventually_ge_atTop (K * (M₁ + 2) / (Real.sqrt 3 / 2 - 1 / 6))]
        with s hs
      rw [div_le_iff₀ hδ] at hs
      nlinarith [hs]
    filter_upwards [h6a, h6b] with s hs1 hs2
    have hsum : s / 6 + (Real.sqrt 3 / 2 - 1 / 6) * s = (Real.sqrt 3 / 2) * s := by ring
    nlinarith [hs1, hs2, hsum]
  have e7 : ∀ᶠ s : ℝ in Filter.atTop, A * (Real.log s + Real.pi) ≤ s / 4 := by
    have h7a : ∀ᶠ s : ℝ in Filter.atTop, A * Real.log s ≤ s / 8 :=
      mul_log_eventually_le A hA 8 (by norm_num)
    have h7b : ∀ᶠ s : ℝ in Filter.atTop, A * Real.pi ≤ s / 8 := by
      filter_upwards [Filter.eventually_ge_atTop (8 * A * Real.pi)] with s hs
      linarith
    filter_upwards [h7a, h7b] with s hs1 hs2
    have hexp : A * (Real.log s + Real.pi) = A * Real.log s + A * Real.pi := by ring
    rw [hexp]
    linarith
  have e8 : ∀ᶠ s : ℝ in Filter.atTop, 512 * A * (A * (Real.log s + Real.pi) + 1) ≤ s := by
    have h8a : ∀ᶠ s : ℝ in Filter.atTop, 512 * A ^ 2 * Real.log s ≤ s / 3 :=
      mul_log_eventually_le (512 * A ^ 2) (by positivity) 3 (by norm_num)
    have h8b : ∀ᶠ s : ℝ in Filter.atTop, 512 * A ^ 2 * Real.pi ≤ s / 3 := by
      filter_upwards [Filter.eventually_ge_atTop (1536 * A ^ 2 * Real.pi)] with s hs
      linarith
    have h8c : ∀ᶠ s : ℝ in Filter.atTop, 512 * A ≤ s / 3 := by
      filter_upwards [Filter.eventually_ge_atTop (1536 * A)] with s hs
      linarith
    filter_upwards [h8a, h8b, h8c] with s hs1 hs2 hs3
    have hexp : 512 * A * (A * (Real.log s + Real.pi) + 1)
        = 512 * A ^ 2 * Real.log s + 512 * A ^ 2 * Real.pi + 512 * A := by ring
    rw [hexp]
    linarith
  obtain ⟨ξ, hξ⟩ := Filter.eventually_atTop.mp
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and e8)))))))
  refine ⟨max ξ 1, lt_of_lt_of_le one_pos (le_max_right ξ 1), ?_⟩
  intro s hs
  exact hξ s (le_trans (le_max_left ξ 1) hs)

theorem image_QLeft {Φ : ℂ → ℂ} {L : Set ℂ} {M₀ M₁ : ℝ} {a : ℂ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hLleft : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L)
    (hLim : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L)
    (hΦ : DifferentiableOn ℂ Φ L)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - a * Complex.log (-ζ))‖ < ε) :
    ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ∀ w : ℂ, ξ₁ < ‖w‖ → w ∈ MandelDim.QLeft ξ₁ →
      ∃ ζ ∈ L, Φ ζ = w := by
  set A : ℝ := ‖a‖ with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact norm_nonneg a
  set K : ℝ := 1024 * (A + 1) ^ 2 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hK4A : 4 * A ≤ K := by rw [hK]; nlinarith [sq_nonneg (A + 1), hA0]
  have hK2 : 2 ≤ K := by rw [hK]; nlinarith [sq_nonneg (A + 1), hA0]
  obtain ⟨R, hR⟩ := hasym (1 / 32) (by norm_num)
  obtain ⟨ξ₀, hξ₀pos, hξ₀⟩ :=
    thresholds (A := A) (M₀ := M₀) (M₁ := M₁) (K := K) (R := R) hA0 hKpos
  set ξ₁ : ℝ := max ξ₀ 1 + 1 with hξ₁
  have hξ₁pos : 0 < ξ₁ := by rw [hξ₁]; positivity
  refine ⟨ξ₁, hξ₁pos, ?_⟩
  intro w hw hwQ
  set s : ℝ := ‖w‖ with hs
  have hw' : ξ₁ < s := by rw [hs]; exact hw
  have hsξ : ξ₀ ≤ s := by
    rw [hξ₁] at hw'
    exact le_of_lt (((le_max_left ξ₀ 1).trans_lt (lt_add_one _)).trans hw')
  obtain ⟨hlog4, h16, hM₀2, hR4, hRlog, hKs, hAs, hA5⟩ := hξ₀ s hsξ
  have hlog_pi : Real.pi ≤ Real.log s := le_trans Real.pi_le_four hlog4
  have hlogs_pos : 0 < Real.log s := lt_of_lt_of_le (by norm_num) hlog4
  have hspos : 0 < s := by linarith
  have hQ : 2 * (w + (ξ₁ : ℂ)).re < ‖w + (ξ₁ : ℂ)‖ := (QLeft_iff ξ₁ w).mp hwQ
  have hQre : 2 * w.re < s - ξ₁ := by
    have h1 : (w + (ξ₁ : ℂ)).re = w.re + ξ₁ := by simp
    have h2 : ‖w + (ξ₁ : ℂ)‖ ≤ s + ξ₁ := by
      calc ‖w + (ξ₁ : ℂ)‖ ≤ ‖w‖ + ‖(ξ₁ : ℂ)‖ := norm_add_le _ _
        _ = s + ξ₁ := by simp [← hs, abs_of_pos hξ₁pos]
    linarith
  set c : ℂ := w + a * Complex.log (-w) with hc
  -- ============ case-independent bounds ============
  have hlogw : ‖Complex.log (-w)‖ ≤ Real.log s + Real.pi := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log (-w))
    rw [Complex.log_re, Complex.log_im] at h1
    have h2 : ‖-w‖ = s := by rw [norm_neg, hs]
    have h3 : |Real.log ‖-w‖| = Real.log s := by rw [h2, abs_of_nonneg hlogs_pos.le]
    have h4 : |(-w).arg| ≤ Real.pi := by
      rw [abs_le]
      exact ⟨(Complex.neg_pi_lt_arg (-w)).le, Complex.arg_le_pi (-w)⟩
    linarith
  have hcw0 : ‖c - w‖ ≤ A * (Real.log s + Real.pi) := by
    have h1 : c - w = a * Complex.log (-w) := by rw [hc]; ring
    rw [h1, norm_mul, hA]
    exact mul_le_mul_of_nonneg_left hlogw hA0
  have hball_dist : ∀ ζ ∈ Metric.closedBall c 1, ‖ζ - c‖ ≤ 1 := by
    intro ζ hζ
    have := Metric.mem_closedBall.mp hζ
    rwa [dist_eq_norm] at this
  have hwdist : ∀ ζ ∈ Metric.closedBall c 1, ‖w - ζ‖ ≤ A * (Real.log s + Real.pi) + 1 := by
    intro ζ hζ
    have h1 := hball_dist ζ hζ
    have h2 : ‖w - ζ‖ ≤ ‖w - c‖ + ‖c - ζ‖ := by
      rw [show w - ζ = (w - c) + (c - ζ) by ring]
      exact norm_add_le _ _
    rw [norm_sub_rev w c, norm_sub_rev c ζ] at h2
    linarith
  -- ============ the two cases ============
  have key :
      (Metric.closedBall c 1 ⊆ L) ∧
      (∀ ζ ∈ Metric.closedBall c 1, ‖a * (Complex.log (-w) - Complex.log (-ζ))‖ ≤ 1 / 32) ∧
      (∀ ζ ∈ Metric.closedBall c (1 / 2), R < ‖ζ‖) := by
    by_cases hW : K * (Real.log s + M₁ + 2) ≤ |w.im|
    · -- ================= case W =================
      have hM₁2 : (0:ℝ) < M₁ + 2 := by linarith
      have hKlog : K * Real.log s ≤ |w.im| := by
        have h1 : K * Real.log s ≤ K * (Real.log s + M₁ + 2) := by nlinarith [hM₁2, hKpos]
        linarith
      have him4 : 4 ≤ |w.im| := by
        have h1 : K * 4 ≤ K * Real.log s := by nlinarith [hlog4, hKpos]
        nlinarith [hKlog, h1, hK2]
      have him_a : |(a * Complex.log (-w)).im| ≤ A * (Real.log s + Real.pi) := by
        calc |(a * Complex.log (-w)).im| ≤ ‖a * Complex.log (-w)‖ := Complex.abs_im_le_norm _
          _ = A * ‖Complex.log (-w)‖ := by rw [norm_mul, hA]
          _ ≤ A * (Real.log s + Real.pi) := mul_le_mul_of_nonneg_left hlogw hA0
      have hAlog : A * (Real.log s + Real.pi) ≤ |w.im| / 2 := by
        have hlt : Real.log s + Real.pi ≤ 2 * Real.log s := by linarith [hlog_pi]
        have h1 : A * (Real.log s + Real.pi) ≤ 2 * A * Real.log s := by
          calc A * (Real.log s + Real.pi) ≤ A * (2 * Real.log s) := mul_le_mul_of_nonneg_left hlt hA0
            _ = 2 * A * Real.log s := by ring
        have h2 : (2 * A / K) * (K * Real.log s) = 2 * A * Real.log s := by
          field_simp
        have h3 : (2 * A / K) * (K * Real.log s) ≤ (2 * A / K) * |w.im| :=
          mul_le_mul_of_nonneg_left hKlog (by positivity)
        have h5 : 2 * A / K ≤ 1 / 2 := by rw [div_le_iff₀ hKpos]; linarith
        have h4 : (2 * A / K) * |w.im| ≤ |w.im| / 2 := by
          have := mul_le_mul_of_nonneg_right h5 (abs_nonneg w.im)
          linarith
        linarith
      have hImc : |w.im| / 2 ≤ |c.im| := by
        have h1 : c.im = w.im + (a * Complex.log (-w)).im := by rw [hc]; simp [Complex.add_im]
        have h2 : |w.im| ≤ |w.im + (a * Complex.log (-w)).im| + |(a * Complex.log (-w)).im| := by
          refine abs_le.mpr ⟨?_, ?_⟩
          · have h1 := neg_le_abs (w.im + (a * Complex.log (-w)).im)
            have h2 := le_abs_self ((a * Complex.log (-w)).im)
            linarith
          · have h1 := le_abs_self (w.im + (a * Complex.log (-w)).im)
            have h2 := neg_le_abs ((a * Complex.log (-w)).im)
            linarith
        rw [h1]
        linarith [him_a, hAlog]
      have hcre : c.re ≤ w.re + |w.im| / 2 := by
        have h1 : c.re = w.re + (a * Complex.log (-w)).re := by rw [hc]; simp [Complex.add_re]
        have h3 : |(a * Complex.log (-w)).re| ≤ A * (Real.log s + Real.pi) := by
          calc |(a * Complex.log (-w)).re| ≤ ‖a * Complex.log (-w)‖ := Complex.abs_re_le_norm _
            _ = A * ‖Complex.log (-w)‖ := by rw [norm_mul, hA]
            _ ≤ A * (Real.log s + Real.pi) := mul_le_mul_of_nonneg_left hlogw hA0
        rw [h1]
        linarith [h3, hAlog, le_abs_self ((a * Complex.log (-w)).re)]
      have hwdistW : ∀ ζ ∈ Metric.closedBall c 1, ‖w - ζ‖ ≤ |w.im| / 2 + 1 :=
        fun ζ hζ => (hwdist ζ hζ).trans (by linarith [hAlog])
      -- the segment stays far from the slit
      have him_seg : ∀ ζ ∈ Metric.closedBall c 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
          |w.im| / 4 ≤ |((1 - t) * (-w) + t * (-ζ)).im| := by
        intro ζ hζ t ht
        have hwz := hwdistW ζ hζ
        have h1 : |w.im| / 4 ≤ |w.im| - (|w.im| / 2 + 1) := by linarith [him4]
        have hz' : ((1 - t) * (-w) + t * (-ζ)) = -((1 - t) * w + t * ζ) := by ring
        rw [hz', Complex.neg_im, abs_neg]
        have h2 : |w.im| - |((1 - t) * w + t * ζ).im| ≤ ‖w - ((1 - t) * w + t * ζ)‖ := by
          calc |w.im| - |((1 - t) * w + t * ζ).im|
              ≤ |w.im - ((1 - t) * w + t * ζ).im| := abs_sub_abs_le_abs_sub _ _
            _ = |(w - ((1 - t) * w + t * ζ)).im| := by rw [Complex.sub_im]
            _ ≤ ‖w - ((1 - t) * w + t * ζ)‖ := Complex.abs_im_le_norm _
        have h3 : ‖w - ((1 - t) * w + t * ζ)‖ ≤ ‖w - ζ‖ := by
          have heq : w - ((1 - t) * w + t * ζ) = t * (w - ζ) := by ring
          rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
          calc |t| * ‖w - ζ‖ ≤ 1 * ‖w - ζ‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
            _ = ‖w - ζ‖ := one_mul _
        linarith [h1, h2, h3, hwz]
      have hsepW : ∀ ζ ∈ Metric.closedBall c 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
          |w.im| / 4 ≤ ‖(1 - t) * (-w) + t * (-ζ)‖ :=
        fun ζ hζ t ht => (him_seg ζ hζ t ht).trans (Complex.abs_im_le_norm _)
      have hslitW : ∀ ζ ∈ Metric.closedBall c 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
          (1 - t) * (-w) + t * (-ζ) ∈ Complex.slitPlane := by
        intro ζ hζ t ht
        rw [Complex.mem_slitPlane_iff]
        right
        have h := him_seg ζ hζ t ht
        intro hc0
        rw [hc0, abs_zero] at h
        linarith [him4]
      have hratio : 4 * A * (A * (Real.log s + Real.pi) + 1) ≤ (1 / 32) * K * Real.log s := by
        have hlt : Real.log s + Real.pi ≤ 2 * Real.log s := by linarith [hlog_pi]
        have h1 : A * (Real.log s + Real.pi) + 1 ≤ 2 * A * Real.log s + 1 := by
          have := mul_le_mul_of_nonneg_left hlt hA0
          linarith
        have h2 : A * (A * (Real.log s + Real.pi) + 1) ≤ A * (2 * A * Real.log s + 1) :=
          mul_le_mul_of_nonneg_left h1 hA0
        have h3 : A * (2 * A * Real.log s + 1) = 2 * A ^ 2 * Real.log s + A := by ring
        have h4 : 4 * A ≤ A * Real.log s := by nlinarith [hA0, hlog4]
        have h5 : 8 * A ^ 2 + A ≤ 32 * (A + 1) ^ 2 := by nlinarith [sq_nonneg (A + 1), hA0]
        rw [hK]
        nlinarith [h2, h3, h4, h5, hlogs_pos.le]
      have hlogballW : ∀ ζ ∈ Metric.closedBall c 1,
          ‖a * (Complex.log (-w) - Complex.log (-ζ))‖ ≤ 1 / 32 := by
        intro ζ hζ
        have hmain := norm_log_sub_le (hh := by linarith [him4]) (hslitW ζ hζ) (hsepW ζ hζ)
        have hnum : ‖-w - (-ζ)‖ = ‖w - ζ‖ := by
          rw [show -w - (-ζ) = ζ - w by ring, norm_sub_rev]
        rw [hnum] at hmain
        have hdw := hwdist ζ hζ
        have hpos4 : (0:ℝ) < |w.im| / 4 := by linarith [him4]
        have hstep : A * (‖w - ζ‖ / (|w.im| / 4)) ≤ 1 / 32 := by
          rw [mul_div_assoc', div_le_iff₀ hpos4]
          have h1 : A * ‖w - ζ‖ ≤ A * (A * (Real.log s + Real.pi) + 1) :=
            mul_le_mul_of_nonneg_left hdw hA0
          have h2 : A * (A * (Real.log s + Real.pi) + 1) ≤ (1 / 128) * (K * Real.log s) := by
            linarith [hratio]
          have h3 : (1 / 128) * (K * Real.log s) ≤ (1 / 32) * (|w.im| / 4) := by
            nlinarith [hKlog]
          linarith
        calc ‖a * (Complex.log (-w) - Complex.log (-ζ))‖
            = A * ‖Complex.log (-w) - Complex.log (-ζ)‖ := by rw [norm_mul, hA]
          _ ≤ A * (‖w - ζ‖ / (|w.im| / 4)) := mul_le_mul_of_nonneg_left hmain hA0
          _ ≤ 1 / 32 := hstep
      -- the image ball lies in the wedge, hence in L
      have hwedge : ∀ ζ ∈ Metric.closedBall c 1, M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im| := by
        intro ζ hζ
        have h1 := hball_dist ζ hζ
        have h2 : |c.im| - ‖ζ - c‖ ≤ |ζ.im| := by
          have h3 : |c.im| - |ζ.im| ≤ ‖c - ζ‖ := by
            calc |c.im| - |ζ.im| ≤ |c.im - ζ.im| := abs_sub_abs_le_abs_sub _ _
              _ = |(c - ζ).im| := by rw [Complex.sub_im]
              _ ≤ ‖c - ζ‖ := Complex.abs_im_le_norm _
          rw [norm_sub_rev] at h3
          linarith
        have h3 : M₁ + 2 ≤ |w.im| / 2 := by
          have h4 : K * (M₁ + 2) ≤ |w.im| := by nlinarith [hW, hKpos, hM₁2]
          nlinarith [h4, hK2, hM₁]
        have h4 : M₁ < |ζ.im| := by linarith [h2, hImc, h3, h1]
        have h5 : ζ.re ≤ c.re + ‖ζ - c‖ := by
          have := Complex.re_le_norm (ζ - c); rw [Complex.sub_re] at this; linarith
        have h6 : ζ.re < 3 * |ζ.im| := by
          have hre_ub : ζ.re ≤ c.re + 1 := by linarith [h5, h1]
          have him_lb : 3 * (|c.im| - 1) ≤ 3 * |ζ.im| := by linarith [h2]
          rcases le_or_gt 0 w.re with hwr | hwr
          · have hwr2 : w.re < s / 2 := by linarith [hQre, hξ₁pos]
            have hgeom : (Real.sqrt 3 / 2) * s ≤ |w.im| := by
              have hsq : s ^ 2 = w.re ^ 2 + w.im ^ 2 := by
                rw [hs, Complex.sq_norm, Complex.normSq_apply]; ring
              have h8 : (3 / 4) * s ^ 2 ≤ w.im ^ 2 := by nlinarith [hsq, hwr2, hwr]
              have h9 : ((Real.sqrt 3 / 2) * s) ^ 2 ≤ |w.im| ^ 2 := by
                rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_abs]
                nlinarith [h8]
              calc (Real.sqrt 3 / 2) * s = Real.sqrt (((Real.sqrt 3 / 2) * s) ^ 2) :=
                    (Real.sqrt_sq (by positivity)).symm
                _ ≤ Real.sqrt (|w.im| ^ 2) := Real.sqrt_le_sqrt h9
                _ = |w.im| := Real.sqrt_sq (abs_nonneg _)
            have hcre' : c.re ≤ s := by
              have h10 : |w.im| ≤ s := by rw [hs]; exact Complex.abs_im_le_norm w
              linarith [hcre, hwr2, hgeom, h10]
            have hsqrt3 : (129 / 100 : ℝ) ≤ 3 * Real.sqrt 3 / 4 := by
              nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
            have hli : 3 * (|c.im| - 1) ≥ (129 / 100) * s - 3 := by
              have := hImc
              nlinarith [hgeom, hsqrt3]
            linarith [hre_ub, hcre', hli, him_lb, h16]
          · have hcre' : c.re ≤ |w.im| / 2 := by linarith [hcre, hwr]
            have hli : 3 * (|c.im| - 1) ≥ 3 * (|w.im| / 2 - 1) := by linarith [hImc]
            linarith [hre_ub, hcre', hli, him_lb, him4]
        exact ⟨h4, h6⟩
      have hballLW : Metric.closedBall c 1 ⊆ L :=
        fun ζ hζ => hLim ζ (hwedge ζ hζ).1 (hwedge ζ hζ).2
      have hRballW : ∀ ζ ∈ Metric.closedBall c (1 / 2), R < ‖ζ‖ := by
        intro ζ hζ
        have h1 : ‖ζ - c‖ ≤ 1 / 2 := by
          have := Metric.mem_closedBall.mp hζ
          rwa [dist_eq_norm] at this
        have h1' : ‖c - ζ‖ ≤ 1 / 2 := by rw [norm_sub_rev]; exact h1
        have h2 : R + 2 ≤ |c.im| := by linarith [hRlog, hKlog, hImc]
        have h3 : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
        have h5 : ‖c‖ - ‖c - ζ‖ ≤ ‖ζ‖ := by
          have h6 : ‖c‖ ≤ ‖ζ‖ + ‖c - ζ‖ := by
            have he : (c - ζ) + ζ = c := by ring
            calc ‖c‖ = ‖(c - ζ) + ζ‖ := by rw [he]
              _ ≤ ‖c - ζ‖ + ‖ζ‖ := norm_add_le _ _
              _ = ‖ζ‖ + ‖c - ζ‖ := by ring
          linarith
        linarith [h2, h3, h5, h1']
      exact ⟨hballLW, hlogballW, hRballW⟩
    · -- ================= case Z =================
      have hW' : |w.im| < K * (Real.log s + M₁ + 2) := not_le.mp hW
      have hwr : w.re ≤ -s / 2 := by
        by_contra hcon
        push Not at hcon
        have hwr2 : w.re < s / 2 := by linarith [hQre, hξ₁pos]
        have hsq : s ^ 2 = w.re ^ 2 + w.im ^ 2 := by
          rw [hs, Complex.sq_norm, Complex.normSq_apply]; ring
        have h1 : w.re ^ 2 < (s / 2) ^ 2 := by nlinarith [hcon, hwr2]
        have h2 : (3 / 4) * s ^ 2 < w.im ^ 2 := by nlinarith [hsq, h1]
        have h3 : (Real.sqrt 3 / 2) * s < |w.im| := by
          have h4 : ((Real.sqrt 3 / 2) * s) ^ 2 < |w.im| ^ 2 := by
            rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_abs]
            nlinarith [h2]
          calc (Real.sqrt 3 / 2) * s = Real.sqrt (((Real.sqrt 3 / 2) * s) ^ 2) :=
                (Real.sqrt_sq (by positivity)).symm
            _ < Real.sqrt (|w.im| ^ 2) := Real.sqrt_lt_sqrt (by positivity) h4
            _ = |w.im| := Real.sqrt_sq (abs_nonneg _)
        linarith [h3, hW', hKs]
      have hcre : c.re ≤ -s / 4 := by
        have h1 : c.re ≤ w.re + A * (Real.log s + Real.pi) := by
          have h2 : c.re = w.re + (a * Complex.log (-w)).re := by rw [hc]; simp [Complex.add_re]
          have h3 : (a * Complex.log (-w)).re ≤ A * ‖Complex.log (-w)‖ := by
            calc (a * Complex.log (-w)).re ≤ ‖a * Complex.log (-w)‖ := Complex.re_le_norm _
              _ = A * ‖Complex.log (-w)‖ := by rw [norm_mul, hA]
          rw [h2]; linarith [h3, mul_le_mul_of_nonneg_left hlogw hA0]
        linarith [h1, hwr, hAs]
      have hzre : ∀ ζ ∈ Metric.closedBall c 1, ζ.re ≤ -s / 4 + 1 := by
        intro ζ hζ
        have h1 := hball_dist ζ hζ
        have h2 : ζ.re ≤ c.re + ‖ζ - c‖ := by
          have := Complex.re_le_norm (ζ - c); rw [Complex.sub_re] at this; linarith
        linarith [hcre, h2, h1]
      have hsegZ : ∀ ζ ∈ Metric.closedBall c 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
          s / 8 ≤ ‖(1 - t) * (-w) + t * (-ζ)‖ ∧
            (1 - t) * (-w) + t * (-ζ) ∈ Complex.slitPlane := by
        intro ζ hζ t ht
        have hz := hzre ζ hζ
        have hwr_le : w.re ≤ -s / 4 + 1 := by linarith [hwr]
        have hz' : ((1 - t) * (-w) + t * (-ζ)) = -((1 - t) * w + t * ζ) := by ring
        have hre : ((1 - t) * w + t * ζ).re ≤ -s / 4 + 1 := by
          have he : ((1 - t) * w + t * ζ).re = (1 - t) * w.re + t * ζ.re := by
            simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
              Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
              zero_mul, sub_zero]
          rw [he]
          nlinarith [ht.1, ht.2, hwr_le, hz]
        have hneg : (0:ℝ) < -((1 - t) * w + t * ζ).re := by linarith [hre, h16]
        constructor
        · rw [hz', norm_neg]
          have hzr : -((1 - t) * w + t * ζ).re ≤ |((1 - t) * w + t * ζ).re| := neg_le_abs _
          have hn : |((1 - t) * w + t * ζ).re| ≤ ‖(1 - t) * w + t * ζ‖ :=
            Complex.abs_re_le_norm _
          linarith [hre, hzr, hn, h16]
        · rw [hz', Complex.mem_slitPlane_iff]
          left
          rw [Complex.neg_re]
          linarith [hre, h16]
      have hlogballZ : ∀ ζ ∈ Metric.closedBall c 1,
          ‖a * (Complex.log (-w) - Complex.log (-ζ))‖ ≤ 1 / 32 := by
        intro ζ hζ
        have hmain := norm_log_sub_le (hh := by linarith [h16])
          (fun t ht => (hsegZ ζ hζ t ht).2) (fun t ht => (hsegZ ζ hζ t ht).1)
        have hnum : ‖-w - (-ζ)‖ = ‖w - ζ‖ := by
          rw [show -w - (-ζ) = ζ - w by ring, norm_sub_rev]
        rw [hnum] at hmain
        have hdw := hwdist ζ hζ
        have hsp8 : (0:ℝ) < s / 8 := by linarith
        have hstep : A * (‖w - ζ‖ / (s / 8)) ≤ 1 / 32 := by
          rw [mul_div_assoc', div_le_iff₀ hsp8]
          have h1 : A * ‖w - ζ‖ ≤ A * (A * (Real.log s + Real.pi) + 1) :=
            mul_le_mul_of_nonneg_left hdw hA0
          have h2 : 256 * (A * (A * (Real.log s + Real.pi) + 1)) ≤ s := by linarith [hA5]
          nlinarith [h1, h2]
        calc ‖a * (Complex.log (-w) - Complex.log (-ζ))‖
            = A * ‖Complex.log (-w) - Complex.log (-ζ)‖ := by rw [norm_mul, hA]
          _ ≤ A * (‖w - ζ‖ / (s / 8)) := mul_le_mul_of_nonneg_left hmain hA0
          _ ≤ 1 / 32 := hstep
      have hballLZ : Metric.closedBall c 1 ⊆ L := by
        intro ζ hζ
        apply hLleft
        have h := hzre ζ hζ
        linarith [h, hM₀2]
      have hRballZ : ∀ ζ ∈ Metric.closedBall c (1 / 2), R < ‖ζ‖ := by
        intro ζ hζ
        have h1 : ζ.re ≤ -s / 4 + 1 := by
          have h2 : ‖ζ - c‖ ≤ 1 / 2 := by
            have := Metric.mem_closedBall.mp hζ
            rwa [dist_eq_norm] at this
          have h3 : ζ.re ≤ c.re + ‖ζ - c‖ := by
            have := Complex.re_le_norm (ζ - c); rw [Complex.sub_re] at this; linarith
          linarith [hcre, h3, h2]
        have h4 : R + 1 ≤ s / 4 - 1 := by linarith [hR4]
        have h5 : |ζ.re| = -ζ.re := by
          rw [abs_of_nonpos]; linarith [h1, h16]
        calc R < R + 1 := by norm_num
          _ ≤ s / 4 - 1 := h4
          _ ≤ -ζ.re := by linarith [h1]
          _ = |ζ.re| := h5.symm
          _ ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
      exact ⟨hballLZ, hlogballZ, hRballZ⟩
  rcases key with ⟨hballL, hlogball, hRball⟩
  have hlogb : ‖a * (Complex.log (-w) - Complex.log (-c))‖ ≤ 1 / 32 :=
    hlogball c (Metric.mem_closedBall_self (by norm_num))
  have hlogb' : ∀ ζ ∈ Metric.sphere c (1 / 2),
      ‖a * (Complex.log (-w) - Complex.log (-ζ))‖ ≤ 1 / 32 := by
    intro ζ hζ
    refine hlogball ζ ?_
    have h1 : ζ ∈ Metric.closedBall c (1 / 2 : ℝ) := Metric.sphere_subset_closedBall hζ
    exact Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) / 2 ≤ 1) h1
  exact exists_preimage_ballL hballL hΦ hc (fun ζ hζ hRζ => hR ζ hζ hRζ) hRball hlogb hlogb'

end

end Work.Parab.leftCoordData
