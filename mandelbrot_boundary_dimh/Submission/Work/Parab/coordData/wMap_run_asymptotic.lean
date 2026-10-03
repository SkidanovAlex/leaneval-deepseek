import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.coordData.log_shift_bound
import Submission.Work.Parab.coordData.sum_log_inv_bound
import Submission.Work.Parab.coordData.log_sq_le_id

namespace Work.Parab.coordData

open Complex Set Metric Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000

/-- `‖log (-z)‖ ≤ log (2 + ‖z‖) + π` for `‖z‖ ≥ 1`. -/
private lemma norm_log_neg_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Complex.log (-z)‖ ≤ Real.log (2 + ‖z‖) + Real.pi := by
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.log (-z))
  rw [Complex.log_re, Complex.log_im, norm_neg] at h
  have h1 : Real.log ‖z‖ ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_nonneg (Real.log_nonneg hz)
  have h3 : |(-z).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
  rw [h2] at h
  linarith [h, h1, h3]

/-- `‖a log(-z) + b‖ ≤ (‖a‖(1+π)+‖b‖+1) (1 + log (2 + ‖z‖))` for `‖z‖ ≥ 1`. -/
private lemma norm_alogb_le {a b : ℂ} {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖a * Complex.log (-z) + b‖ ≤ (‖a‖ * (1 + Real.pi) + ‖b‖ + 1) * (1 + Real.log (2 + ‖z‖)) := by
  have h1 := norm_log_neg_le hz
  have h2 : ‖a * Complex.log (-z) + b‖ ≤ ‖a‖ * ‖Complex.log (-z)‖ + ‖b‖ := by
    calc ‖a * Complex.log (-z) + b‖ ≤ ‖a * Complex.log (-z)‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * ‖Complex.log (-z)‖ + ‖b‖ := by rw [norm_mul]
  have hL : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
  have h3 : ‖a‖ * ‖Complex.log (-z)‖ + ‖b‖ ≤ ‖a‖ * (Real.log (2 + ‖z‖) + Real.pi) + ‖b‖ := by
    have := mul_le_mul_of_nonneg_left h1 (norm_nonneg a); linarith
  have h4 : ‖a‖ * (Real.log (2 + ‖z‖) + Real.pi) + ‖b‖
      ≤ (‖a‖ * (1 + Real.pi) + ‖b‖ + 1) * (1 + Real.log (2 + ‖z‖)) := by
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hp := Real.pi_pos
    nlinarith [mul_nonneg ha hL, mul_nonneg hb hL, hL]
  linarith [h2, h3, h4]

/-- **The core run estimate.**  Abstract form of `wMap_run_asymptotic`: if `wMap f` deviates from
`x ↦ x + 1 + a/x` by at most `K/‖x‖²` beyond radius `Nc`, and `w₀` is within `ε/16` of the
approximate inverse coordinate `u ↦ u + a log(-u) + b`, then the whole run stays within `ε` of
`u + n ↦ (u+n) + a log(-(u+n)) + b`, uniformly in `n`, as `|Im u| → ∞`. -/
private theorem core_bound
    {f : ℂ → ℂ} {a b : ℂ} {K Nc : ℝ} (hNc : 0 < Nc) (hK : 0 ≤ K)
    (hchart : ∀ x : ℂ, Nc < ‖x‖ →
      ‖Work.FatouCoord.wMap f x - (x + 1 + a / x)‖ ≤ K / ‖x‖ ^ 2)
    (hlsb : ∀ z : ℂ, 2 ≤ ‖z‖ → z.im ≠ 0 →
      ‖Complex.log (-z) - Complex.log (-(z + 1)) + 1 / z‖ ≤ 1 / ‖z‖ ^ 2)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC₀b : ∀ x η : ℝ, 1 ≤ η → ∀ k : ℕ,
      ∑ j ∈ Finset.range k, (1 + Real.log (2 + |x + (j:ℝ)|)) / ((x + (j:ℝ))^2 + η^2)
        ≤ C₀ * (1 + Real.log (2 + η)) / η)
    (hlogsq : ∀ c : ℝ, ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t → c * (1 + Real.log (2 + t))^2 ≤ t)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ R : ℝ, ∀ (u w₀ : ℂ), R < |u.im| →
      ‖w₀ - (u + a * Complex.log (-u) + b)‖ < ε/16 →
      ∀ n : ℕ, (∀ j ≤ n, Nc < ‖(Work.FatouCoord.wMap f)^[j] w₀‖) →
        ‖(Work.FatouCoord.wMap f)^[n] w₀
          - (u + (n:ℂ) + a * Complex.log (-(u + (n:ℂ))) + b)‖ < ε := by
  have hε16 : 0 < ε / 16 := by linarith
  set La : ℝ := ‖a‖ with hLadef
  have hLa0 : 0 ≤ La := by rw [hLadef]; positivity
  set Clog : ℝ := ‖a‖ * (1 + Real.pi) + ‖b‖ + 1 with hClogdef
  have hClog0 : 0 ≤ Clog := by rw [hClogdef]; positivity
  set α : ℝ := 2 * La with hαdef
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  set A2 : ℝ := La + 2 * La * Clog + 4 * K with hA2def
  have hA20 : 0 ≤ A2 := by rw [hA2def]; nlinarith [hLa0, hClog0, hK]
  set A3 : ℝ := 2 * La * Clog with hA3def
  have hA30 : 0 ≤ A3 := by rw [hA3def]; nlinarith [hLa0, hClog0]
  obtain ⟨M1, hM11, hM1b⟩ := hlogsq (4 * Clog)
  obtain ⟨M2, hM21, hM2b⟩ := hlogsq (α * C₀ / Real.log 2)
  obtain ⟨M3, hM31, hM3b⟩ := hlogsq (8 * C₀ * (A2 + A3) / ε)
  set R : ℝ := max (max (max (max 3 M1) M2) M3) 1 with hRdef
  have hR3 : 3 ≤ R :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hRM1 : M1 ≤ R :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hRM2 : M2 ≤ R :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hRM3 : M3 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨R, ?_⟩
  intro u w₀ hηu hw0 n hb
  set η : ℝ := |u.im| with hηdef
  have hRη : R ≤ η := le_of_lt hηu
  have hη3 : 3 ≤ η := le_trans hR3 hRη
  have hη1 : 1 ≤ η := by linarith
  have hη2 : 2 ≤ η := by linarith
  have hηpos : 0 < η := by linarith
  have himne : u.im ≠ 0 := by
    intro h
    have : η = 0 := by rw [hηdef, h]; simp
    linarith
  have hlogη0 : 0 ≤ Real.log (2 + η) := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ 1 + Real.log (2 + η) := by linarith
  -- ------------------------------------------------------------- thresholds
  have hClogη : Clog * (1 + Real.log (2 + η)) ≤ η / 4 := by
    have h := hM1b η (le_trans hRM1 hRη)
    have hLL : (1 + Real.log (2 + η)) ≤ (1 + Real.log (2 + η))^2 := by
      nlinarith [hL1]
    have hm := mul_le_mul_of_nonneg_left hLL (by linarith : (0:ℝ) ≤ 4 * Clog)
    linarith
  have hαC₀η : α * C₀ * (1 + Real.log (2 + η)) ≤ η * Real.log 2 := by
    have h := hM2b η (le_trans hRM2 hRη)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog2] at h
    have hLL : (1 + Real.log (2 + η)) ≤ (1 + Real.log (2 + η))^2 := by
      nlinarith [hL1]
    have hm := mul_le_mul_of_nonneg_left hLL (mul_nonneg hα0 hC₀)
    linarith
  have hsumη : C₀ * (A2 + A3) * (1 + Real.log (2 + η))^2 ≤ ε * η / 8 := by
    have h := hM3b η (le_trans hRM3 hRη)
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h
    linarith
  -- ------------------------------------------------------------- the run
  set X : ℕ → ℂ := fun j => (Work.FatouCoord.wMap f)^[j] w₀ with hXdef
  set Gf : ℂ → ℂ := fun z => z + a * Complex.log (-z) + b with hGfdef
  set E : ℕ → ℂ := fun j => X j - Gf (u + (j:ℂ)) with hEdef
  set W : ℕ → ℝ := fun j => ‖u + (j:ℂ)‖ with hWdef
  set bb : ℕ → ℝ := fun j => (A2 + A3 * Real.log (2 + W j)) / W j ^ 2 with hbbdef
  have hWs : ∀ j : ℕ, W j ^ 2 = (u.re + (j:ℝ))^2 + η^2 := by
    intro j
    have h1 : (u + (j:ℂ)).re = u.re + (j:ℝ) := by simp
    have h2 : (u + (j:ℂ)).im = u.im := by simp
    simp only [hWdef]
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2, hηdef, sq_abs]
    ring
  have hWge : ∀ j : ℕ, η ≤ W j := by
    intro j
    simp only [hWdef]
    calc η = |u.im| := hηdef
      _ = |(u + (j:ℂ)).im| := by simp
      _ ≤ ‖u + (j:ℂ)‖ := Complex.abs_im_le_norm _
  have hW1 : ∀ j : ℕ, 1 ≤ W j := fun j => le_trans hη1 (hWge j)
  have hW2 : ∀ j : ℕ, 2 ≤ W j := fun j => le_trans hη2 (hWge j)
  have hW3 : ∀ j : ℕ, 3 ≤ W j := fun j => le_trans hη3 (hWge j)
  have hWpos : ∀ j : ℕ, 0 < W j := fun j => lt_of_lt_of_le zero_lt_one (hW1 j)
  have hW3pos : ∀ j : ℕ, 0 < W j ^ 2 := fun j => pow_pos (hWpos j) 2
  have hClogW : ∀ j : ℕ, Clog * (1 + Real.log (2 + W j)) ≤ W j / 4 := by
    intro j
    have h := hM1b (W j) (le_trans hRM1 (le_trans hRη (hWge j)))
    have hL1' : 1 ≤ 1 + Real.log (2 + W j) := by
      have : 0 ≤ Real.log (2 + W j) := Real.log_nonneg (by linarith [hW1 j])
      linarith
    have hLL : (1 + Real.log (2 + W j)) ≤ (1 + Real.log (2 + W j))^2 := by nlinarith [hL1']
    have hm := mul_le_mul_of_nonneg_left hLL (by linarith : (0:ℝ) ≤ 4 * Clog)
    linarith
  -- ------------------------------------------------------------- real sums
  have hS1 : ∀ k : ℕ, ∑ i ∈ Finset.range k, 1 / ((u.re + (i:ℝ))^2 + η^2)
      ≤ C₀ * (1 + Real.log (2 + η)) / η := by
    intro k
    calc ∑ i ∈ Finset.range k, 1 / ((u.re + (i:ℝ))^2 + η^2)
        ≤ ∑ i ∈ Finset.range k,
            (1 + Real.log (2 + |u.re + (i:ℝ)|)) / ((u.re + (i:ℝ))^2 + η^2) := by
          apply Finset.sum_le_sum
          intro i _
          have hden : 0 < (u.re + (i:ℝ))^2 + η^2 := by
            nlinarith [sq_nonneg (u.re + (i:ℝ)), hη1]
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          have : 0 ≤ Real.log (2 + |u.re + (i:ℝ)|) :=
            Real.log_nonneg (by linarith [abs_nonneg (u.re + (i:ℝ))])
          linarith
      _ ≤ C₀ * (1 + Real.log (2 + η)) / η := hC₀b u.re η hη1 k
  have hS2 : ∀ k : ℕ,
      ∑ i ∈ Finset.range k, Real.log (2 + |u.re + (i:ℝ)|) / ((u.re + (i:ℝ))^2 + η^2)
        ≤ C₀ * (1 + Real.log (2 + η)) / η := by
    intro k
    calc ∑ i ∈ Finset.range k, Real.log (2 + |u.re + (i:ℝ)|) / ((u.re + (i:ℝ))^2 + η^2)
        ≤ ∑ i ∈ Finset.range k,
            (1 + Real.log (2 + |u.re + (i:ℝ)|)) / ((u.re + (i:ℝ))^2 + η^2) := by
          apply Finset.sum_le_sum
          intro i _
          have hden : 0 < (u.re + (i:ℝ))^2 + η^2 := by
            nlinarith [sq_nonneg (u.re + (i:ℝ)), hη1]
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          linarith
      _ ≤ C₀ * (1 + Real.log (2 + η)) / η := hC₀b u.re η hη1 k
  have hsum1 : ∀ k : ℕ, ∑ i ∈ Finset.range k, 1 / W i ^ 2
      ≤ C₀ * (1 + Real.log (2 + η)) / η := by
    intro k
    have heq : ∑ i ∈ Finset.range k, 1 / W i ^ 2
        = ∑ i ∈ Finset.range k, 1 / ((u.re + (i:ℝ))^2 + η^2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hWs i]
    rw [heq]; exact hS1 k
  have hsum2 : ∀ k : ℕ, ∑ i ∈ Finset.range k, bb i
      ≤ C₀ * (A2 + A3) * (1 + Real.log (2 + η))^2 / η := by
    intro k
    have hterm : ∀ i ∈ Finset.range k, bb i
        ≤ (A2 + A3 + A3 * Real.log (2 + η)) * (1 + Real.log (2 + |u.re + (i:ℝ)|))
            / ((u.re + (i:ℝ))^2 + η^2) := by
      intro i _
      have hden : 0 < (u.re + (i:ℝ))^2 + η^2 := by
        nlinarith [sq_nonneg (u.re + (i:ℝ)), hη1]
      have hWa : W i ≤ |u.re + (i:ℝ)| + η := by
        have h : ‖u + (i:ℂ)‖ ≤ |(u + (i:ℂ)).re| + |(u + (i:ℂ)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        have hr : (u + (i:ℂ)).re = u.re + (i:ℝ) := by simp
        have hi : (u + (i:ℂ)).im = u.im := by simp
        rw [hr, hi, ← hηdef] at h
        simpa only [hWdef] using h
      have hlog : Real.log (2 + W i)
          ≤ Real.log (2 + |u.re + (i:ℝ)|) + Real.log (2 + η) := by
        have hprod : 2 + W i ≤ (2 + |u.re + (i:ℝ)|) * (2 + η) := by
          nlinarith [hWa, abs_nonneg (u.re + (i:ℝ)), hη1]
        calc Real.log (2 + W i) ≤ Real.log ((2 + |u.re + (i:ℝ)|) * (2 + η)) := by
              apply Real.log_le_log <;> linarith [hW1 i, abs_nonneg (u.re + (i:ℝ))]
          _ = Real.log (2 + |u.re + (i:ℝ)|) + Real.log (2 + η) :=
              Real.log_mul (by linarith [abs_nonneg (u.re + (i:ℝ))]) (by linarith)
      have hL1i : 0 ≤ Real.log (2 + |u.re + (i:ℝ)|) :=
        Real.log_nonneg (by linarith [abs_nonneg (u.re + (i:ℝ))])
      have hnum : A2 + A3 * Real.log (2 + W i)
          ≤ (A2 + A3 + A3 * Real.log (2 + η)) * (1 + Real.log (2 + |u.re + (i:ℝ)|)) := by
        have h3 : A3 * Real.log (2 + W i)
            ≤ A3 * (Real.log (2 + |u.re + (i:ℝ)|) + Real.log (2 + η)) :=
          mul_le_mul_of_nonneg_left hlog hA30
        have hp1 : 0 ≤ A2 * Real.log (2 + |u.re + (i:ℝ)|) := mul_nonneg hA20 hL1i
        have hp2 : 0 ≤ A3 * Real.log (2 + |u.re + (i:ℝ)|) := mul_nonneg hA30 hL1i
        have hp3 : 0 ≤ A3 * Real.log (2 + |u.re + (i:ℝ)|) * Real.log (2 + η) :=
          mul_nonneg hp2 hlogη0
        nlinarith [h3, hp1, hp2, hp3, hA20, hA30, hL1i, hlogη0]
      simp only [hbbdef]
      rw [hWs i]
      exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
    calc ∑ i ∈ Finset.range k, bb i
        ≤ ∑ i ∈ Finset.range k, (A2 + A3 + A3 * Real.log (2 + η))
            * (1 + Real.log (2 + |u.re + (i:ℝ)|)) / ((u.re + (i:ℝ))^2 + η^2) :=
          Finset.sum_le_sum hterm
      _ = (A2 + A3 + A3 * Real.log (2 + η))
            * (∑ i ∈ Finset.range k, (1 + Real.log (2 + |u.re + (i:ℝ)|))
                / ((u.re + (i:ℝ))^2 + η^2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ (A2 + A3 + A3 * Real.log (2 + η)) * (C₀ * (1 + Real.log (2 + η)) / η) := by
          apply mul_le_mul_of_nonneg_left (hC₀b u.re η hη1 k)
          have : 0 ≤ A3 * Real.log (2 + η) := mul_nonneg hA30 hlogη0
          linarith
      _ ≤ C₀ * (A2 + A3) * (1 + Real.log (2 + η))^2 / η := by
          have hfac : 0 ≤ C₀ * (1 + Real.log (2 + η)) / η := by positivity
          have hbound : A2 + A3 + A3 * Real.log (2 + η)
              ≤ (A2 + A3) * (1 + Real.log (2 + η)) := by
            nlinarith [hL1, hA20, hA30, hlogη0]
          calc (A2 + A3 + A3 * Real.log (2 + η)) * (C₀ * (1 + Real.log (2 + η)) / η)
              ≤ ((A2 + A3) * (1 + Real.log (2 + η))) * (C₀ * (1 + Real.log (2 + η)) / η) := by
                apply mul_le_mul_of_nonneg_right hbound hfac
            _ = C₀ * (A2 + A3) * (1 + Real.log (2 + η))^2 / η := by ring
  have hbb0 : ∀ j : ℕ, 0 ≤ bb j := by
    intro j
    rw [hbbdef]
    apply div_nonneg _ (le_of_lt (hW3pos j))
    have : 0 ≤ Real.log (2 + W j) := Real.log_nonneg (by linarith [hW1 j])
    nlinarith [hA20, hA30, this]
  -- ------------------------------------------------------------- product bound
  have hP : ∀ k : ℕ, ∏ i ∈ Finset.range k, (1 + α / W i ^ 2) ≤ 2 := by
    intro k
    have h1 : ∏ i ∈ Finset.range k, (1 + α / W i ^ 2)
        ≤ ∏ i ∈ Finset.range k, Real.exp (α / W i ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have h0i : 0 ≤ α / W i ^ 2 := div_nonneg hα0 (le_of_lt (hW3pos i))
        linarith
      · intro i _
        have := Real.add_one_le_exp (α / W i ^ 2)
        linarith
    have h3 : ∑ i ∈ Finset.range k, α / W i ^ 2 ≤ Real.log 2 := by
      have hαsum : ∑ i ∈ Finset.range k, α / W i ^ 2
          = α * ∑ i ∈ Finset.range k, 1 / W i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_one_div]
      rw [hαsum]
      calc α * ∑ i ∈ Finset.range k, 1 / W i ^ 2
          ≤ α * (C₀ * (1 + Real.log (2 + η)) / η) :=
            mul_le_mul_of_nonneg_left (hsum1 k) hα0
        _ ≤ Real.log 2 := by
            rw [← mul_div_assoc]
            rw [div_le_iff₀ hηpos]
            nlinarith [hαC₀η]
    calc ∏ i ∈ Finset.range k, (1 + α / W i ^ 2)
        ≤ ∏ i ∈ Finset.range k, Real.exp (α / W i ^ 2) := h1
      _ = Real.exp (∑ i ∈ Finset.range k, α / W i ^ 2) := by rw [← Real.exp_sum]
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h3
      _ = 2 := Real.exp_log (by norm_num)
  have hEunif : ∀ k : ℕ,
      (∏ i ∈ Finset.range k, (1 + α / W i ^ 2)) * (ε / 16 + ∑ i ∈ Finset.range k, bb i)
        ≤ 3 * ε / 8 := by
    intro k
    have h1 := hP k
    have h2 : ∑ i ∈ Finset.range k, bb i ≤ ε / 8 := by
      have h5 := hsum2 k
      rw [le_div_iff₀ hηpos] at h5
      have h6 : (∑ i ∈ Finset.range k, bb i) * η ≤ (ε / 8) * η := by linarith [h5, hsumη]
      exact le_of_mul_le_mul_right h6 hηpos
    have hsum0 : 0 ≤ ε / 16 + ∑ i ∈ Finset.range k, bb i := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range k) => hbb0 i)
      linarith
    calc (∏ i ∈ Finset.range k, (1 + α / W i ^ 2)) * (ε / 16 + ∑ i ∈ Finset.range k, bb i)
        ≤ 2 * (3 * ε / 16) := by
          apply mul_le_mul h1 _ hsum0 (by norm_num)
          linarith
      _ ≤ 3 * ε / 8 := by linarith
  -- ------------------------------------------------------------- the key induction
  have hXge : ∀ j : ℕ, ‖E j‖ ≤ 3 * ε / 8 → W j / 2 ≤ ‖X j‖ := by
    intro j hEj
    have hXeq : X j = E j + Gf (u + (j:ℂ)) := by
      have h : E j = X j - Gf (u + (j:ℂ)) := by simp only [hEdef]
      rw [h]; ring
    have hGsub : Gf (u + (j:ℂ)) = (u + (j:ℂ)) + (a * Complex.log (-(u + (j:ℂ))) + b) := by
      rw [hGfdef]; ring
    have hnormlog : ‖a * Complex.log (-(u + (j:ℂ))) + b‖
        ≤ Clog * (1 + Real.log (2 + W j)) := by
      rw [hClogdef]; exact norm_alogb_le (hW1 j)
    have hEsmall : ‖E j‖ ≤ W j / 4 := by
      have hWjj : 3 ≤ W j := hW3 j
      have : 3 * ε / 8 ≤ 3 / 8 := by nlinarith [hε1]
      nlinarith [hEj, hWjj, this]
    have hlower : ‖u + (j:ℂ)‖ - Clog * (1 + Real.log (2 + W j)) ≤ ‖Gf (u + (j:ℂ))‖ := by
      rw [hGsub]
      have h := norm_sub_le (u + (j:ℂ) + (a * Complex.log (-(u + (j:ℂ))) + b))
        (a * Complex.log (-(u + (j:ℂ))) + b)
      have h3 : (u + (j:ℂ) + (a * Complex.log (-(u + (j:ℂ))) + b))
          - (a * Complex.log (-(u + (j:ℂ))) + b) = u + (j:ℂ) := by ring
      rw [h3] at h
      linarith [h, hnormlog]
    have hrev : ‖Gf (u + (j:ℂ))‖ - ‖E j‖ ≤ ‖X j‖ := by
      rw [hXeq]
      have h := norm_sub_le (E j + Gf (u + (j:ℂ))) (E j)
      have h3 : (E j + Gf (u + (j:ℂ))) - E j = Gf (u + (j:ℂ)) := by ring
      rw [h3] at h
      linarith [h]
    rw [hWdef]
    linarith [hlower, hClogW j, hEsmall, hrev]
  have key : ∀ k : ℕ, (∀ j ≤ k, Nc < ‖X j‖) →
      ‖E k‖ ≤ (∏ i ∈ Finset.range k, (1 + α / W i ^ 2)) * (ε / 16 + ∑ i ∈ Finset.range k, bb i) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hE0 : E 0 = w₀ - (u + a * Complex.log (-u) + b) := by
        simp only [hEdef, hXdef, hGfdef, Function.iterate_zero_apply, Nat.cast_zero, add_zero]
      rw [hE0]
      simpa using le_of_lt hw0
    | succ k ih =>
      intro hk
      have hprev : ∀ j ≤ k, Nc < ‖X j‖ := fun j hj => hk j (Nat.le_succ_of_le hj)
      have hIH := ih hprev
      have hEk : ‖E k‖ ≤ 3 * ε / 8 := le_trans hIH (hEunif k)
      have hXgek : W k / 2 ≤ ‖X k‖ := hXge k hEk
      have hXkne : X k ≠ 0 := by
        have := hk k (Nat.le_succ k)
        intro h; rw [h] at this; simp at this; linarith [hNc]
      have hstep : ‖E (k+1)‖ ≤ (1 + α / W k ^ 2) * ‖E k‖ + bb k := by
        set w : ℂ := u + (k:ℂ) with hwdef
        have hwW : ‖w‖ = W k := by simp only [hwdef, hWdef]
        have hwne : w ≠ 0 := by
          have : 0 < ‖w‖ := by rw [hwW]; exact lt_of_lt_of_le (by norm_num) (hW1 k)
          exact norm_pos_iff.mp this
        have hwim : w.im ≠ 0 := by
          have hh : w.im = u.im := by simp [hwdef]
          rw [hh]; exact himne
        have hls := hlsb w (by rw [hwW]; exact hW2 k) hwim
        have hXk1 : X (k+1) = Work.FatouCoord.wMap f (X k) := by
          simp only [hXdef, Function.iterate_succ_apply']
        have hw1 : u + ((k+1 : ℕ) : ℂ) = w + 1 := by
          simp only [hwdef]; push_cast; ring
        have hG1 : Gf (u + ((k+1 : ℕ) : ℂ)) - Gf w
            = 1 + a * (Complex.log (-(w+1)) - Complex.log (-w)) := by
          rw [hw1, hGfdef]; ring
        have hA : E (k+1) = E k + (a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w)
              + (a * (1/X k - 1/w)
                + (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k)))) := by
          have hd : E (k+1) - E k
              = (Work.FatouCoord.wMap f (X k) - X k)
                - (Gf (u + ((k+1 : ℕ) : ℂ)) - Gf w) := by
            have h1 : E (k+1) = X (k+1) - Gf (u + ((k+1 : ℕ) : ℂ)) := by simp only [hEdef]
            have h2 : E k = X k - Gf w := by simp only [hEdef, hwdef]
            rw [h1, h2, hXk1]; ring
          have hd2 : (Work.FatouCoord.wMap f (X k) - X k)
                - (Gf (u + ((k+1 : ℕ) : ℂ)) - Gf w)
              = a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w)
                + (a * (1/X k - 1/w)
                  + (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k))) := by
            rw [hG1]; ring
          rw [← hd2, ← hd]; ring
        have hT1 : ‖Complex.log (-w) - Complex.log (-(w+1)) + 1 / w‖ ≤ 1 / W k ^ 2 := by
          rw [← hwW]; exact hls
        have hT2 : ‖1 / X k - 1 / w‖
            ≤ 2 * (‖E k‖ + Clog * (1 + Real.log (2 + W k))) / W k ^ 2 := by
          have hXeq : X k = E k + Gf w := by
            have h : E k = X k - Gf w := by simp only [hEdef, hwdef]
            rw [h]; ring
          have hGsub : Gf w = w + (a * Complex.log (-w) + b) := by rw [hGfdef]; ring
          have hnum : ‖w - X k‖ ≤ ‖E k‖ + Clog * (1 + Real.log (2 + W k)) := by
            have hwX : w - X k = -(E k + (a * Complex.log (-w) + b)) := by
              rw [hXeq, hGsub]; ring
            rw [hwX, norm_neg]
            have h1 := norm_add_le (E k) (a * Complex.log (-w) + b)
            have hb := norm_alogb_le (a := a) (b := b) (z := w) (by rw [hwW]; exact hW1 k)
            have hb' : ‖a * Complex.log (-w) + b‖ ≤ Clog * (1 + Real.log (2 + W k)) := by
              rw [hClogdef]; rw [hwW] at hb; exact hb
            linarith
          have hnum0 : 0 ≤ ‖E k‖ + Clog * (1 + Real.log (2 + W k)) := by
            have h1 := norm_nonneg (E k)
            have h2 : 0 ≤ Clog * (1 + Real.log (2 + W k)) := by
              have : 0 ≤ Real.log (2 + W k) := Real.log_nonneg (by linarith [hW1 k])
              exact mul_nonneg hClog0 (by linarith)
            linarith
          have heq : 1 / X k - 1 / w = (w - X k) / (X k * w) := by
            field_simp
          have h3 : 1 / (‖X k‖ * W k) ≤ 2 / W k ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hXgek, hWpos k]
          rw [heq, norm_div, norm_mul, hwW]
          calc ‖w - X k‖ / (‖X k‖ * W k)
              = ‖w - X k‖ * (1 / (‖X k‖ * W k)) := by rw [mul_one_div]
            _ ≤ (‖E k‖ + Clog * (1 + Real.log (2 + W k))) * (1 / (‖X k‖ * W k)) :=
                mul_le_mul_of_nonneg_right hnum (by positivity)
            _ ≤ (‖E k‖ + Clog * (1 + Real.log (2 + W k))) * (2 / W k ^ 2) :=
                mul_le_mul_of_nonneg_left h3 hnum0
            _ = 2 * (‖E k‖ + Clog * (1 + Real.log (2 + W k))) / W k ^ 2 := by ring
        have herr : ‖Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k)‖ ≤ K / ‖X k‖ ^ 2 :=
          hchart (X k) (hk k (Nat.le_succ k))
        have herr' : K / ‖X k‖ ^ 2 ≤ 4 * K / W k ^ 2 := by
          have hXkpos : 0 < ‖X k‖ := norm_pos_iff.mpr hXkne
          have hWle : W k ≤ 2 * ‖X k‖ := by linarith [hXgek]
          have hsq : W k ^ 2 ≤ 4 * ‖X k‖ ^ 2 := by nlinarith [hWle, hWpos k]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsq, hK]
        have hAC : ‖a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w)‖ ≤ La * (1 / W k ^ 2) := by
          rw [norm_mul, hLadef]
          exact mul_le_mul_of_nonneg_left hT1 (norm_nonneg a)
        have hBC : ‖a * (1/X k - 1/w)‖
            ≤ La * (2 * (‖E k‖ + Clog * (1 + Real.log (2 + W k))) / W k ^ 2) := by
          rw [norm_mul, hLadef]
          exact mul_le_mul_of_nonneg_left hT2 (norm_nonneg a)
        have hCC : ‖Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k)‖ ≤ 4 * K / W k ^ 2 :=
          le_trans herr herr'
        calc ‖E (k+1)‖
            = ‖E k + (a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w)
                + (a * (1/X k - 1/w)
                  + (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k))))‖ := by rw [hA]
          _ ≤ ‖E k‖ + (La * (1 / W k ^ 2)
                + (La * (2 * (‖E k‖ + Clog * (1 + Real.log (2 + W k))) / W k ^ 2)
                  + 4 * K / W k ^ 2)) := by
              have h2 := norm_add_le (E k) (a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w)
                + (a * (1/X k - 1/w)
                  + (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k))))
              have h3 := norm_add_le (a * (Complex.log (-w) - Complex.log (-(w+1)) + 1/w))
                (a * (1/X k - 1/w) + (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k)))
              have h4 := norm_add_le (a * (1/X k - 1/w))
                (Work.FatouCoord.wMap f (X k) - (X k + 1 + a / X k))
              linarith [h2, h3, h4, hAC, hBC, hCC]
          _ = (1 + α / W k ^ 2) * ‖E k‖ + bb k := by
              rw [hbbdef, hαdef, hA2def, hA3def, hClogdef, hLadef]
              ring
      have hmul := mul_le_mul_of_nonneg_left hIH (by positivity : (0:ℝ) ≤ 1 + α / W k ^ 2)
      calc ‖E (k+1)‖ ≤ (1 + α / W k ^ 2) * ‖E k‖ + bb k := hstep
        _ ≤ (1 + α / W k ^ 2) * ((∏ i ∈ Finset.range k, (1 + α / W i ^ 2))
              * (ε / 16 + ∑ i ∈ Finset.range k, bb i)) + bb k := by linarith
        _ = (∏ i ∈ Finset.range (k+1), (1 + α / W i ^ 2))
              * (ε / 16 + ∑ i ∈ Finset.range k, bb i) + bb k := by
              rw [Finset.prod_range_succ]; ring
        _ ≤ (∏ i ∈ Finset.range (k+1), (1 + α / W i ^ 2))
              * (ε / 16 + ∑ i ∈ Finset.range (k+1), bb i) := by
              rw [Finset.sum_range_succ]
              have hPge1 : 1 ≤ ∏ i ∈ Finset.range (k+1), (1 + α / W i ^ 2) := by
                have := Finset.prod_le_prod₀
                  (s := Finset.range (k+1)) (f := fun _ : ℕ => (1:ℝ))
                  (g := fun i : ℕ => 1 + α / W i ^ 2)
                  (fun i _ => by norm_num)
                  (fun i _ => by
                    have : 0 ≤ α / W i ^ 2 := div_nonneg hα0 (le_of_lt (hW3pos i))
                    linarith)
                simpa using this
              have hbbk := hbb0 k
              have hle : bb k ≤ (∏ i ∈ Finset.range (k+1), (1 + α / W i ^ 2)) * bb k :=
                le_mul_of_one_le_left hbbk hPge1
              linarith
  have hn' : (∀ j ≤ n, Nc < ‖X j‖) := by
    intro j hj
    simpa only [hXdef] using hb j hj
  have hEn : E n = (Work.FatouCoord.wMap f)^[n] w₀
      - (u + (n:ℂ) + a * Complex.log (-(u + (n:ℂ))) + b) := by
    simp only [hEdef, hXdef, hGfdef]
  rw [← hEn]
  calc ‖E n‖ ≤ 3 * ε / 8 := le_trans (key n hn') (hEunif n)
    _ < ε := by linarith

/-- **The end asymptotic of the inverse left coordinate along a chart run.**

`Φ` is a left (repelling) coordinate of the chart dynamics `wMap f ζ = -1/f(-1/ζ)` of a parabolic
germ: holomorphic and injective on `L`, satisfying the conditional Abel equation, asymptotic to
`ζ ↦ ζ - a log(-ζ) - b`, and proper (`N < ‖Φ ζ‖ ⟹ R < ‖ζ‖`); `τ` is its inverse on a sector
`QLeft ξ₀` (`Φ (τ u) = u`, `τ u ∈ L`, `τ u = u + a log(-u) + b + o(1)`).

Then every chart run leaving the sector has the same asymptotic: for `u` in the sector and ANY
number of steps `n`, the point `wMap^[n] (τ u)` is asymptotic to
`(u + n) + a * log (-(u + n)) + b`, uniformly in `u` and `n` as `|Im (u + n)| = |Im u| → ∞`.
The correction to the plain translation `u ↦ u + n` telescopes the chart defect
`wMap x - x - 1 - a/x` into the difference of the two logarithm terms; both signs of `Im u` share
the same constant `b` because the principal branch of `log (-·)` is continuous along the run. -/
theorem wMap_run_asymptotic {f : ℂ → ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ : ℝ} {a b : ℂ} {K Nc : ℝ}
    (hξ₀ : 0 < ξ₀) (hNc : 0 < Nc) (hK : 0 ≤ K)
    (hchart : ∀ x : ℂ, Nc < ‖x‖ →
      ‖Work.FatouCoord.wMap f x - (x + 1 + a / x)‖ ≤ K / ‖x‖ ^ 2)
    (hτmem : ∀ u ∈ MandelDim.QLeft ξ₀, τ u ∈ L)
    (hτspec : ∀ u ∈ MandelDim.QLeft ξ₀, Φ (τ u) = u)
    (hτasym : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, R < ‖u‖ →
      ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε)
    (hΦasym : ∀ ε > 0, ∃ R : ℝ, ∀ x ∈ L, R < ‖x‖ →
      ‖Φ x - (x - a * Complex.log (-x) - b)‖ < ε)
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ x ∈ L, N < ‖Φ x‖ → R < ‖x‖) :
    ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, ∀ n : ℕ,
      R < |(u + (n : ℂ)).im| →
      (∀ j ≤ n, Nc < ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖) →
      ‖(Work.FatouCoord.wMap f)^[n] (τ u) - (u + (n : ℂ) + a * Complex.log (-(u + (n : ℂ))) + b)‖ < ε := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := sum_log_inv_bound
  intro ε hε
  set ε' : ℝ := min ε 1 with hε'def
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  have hε'leε : ε' ≤ ε := min_le_left _ _
  obtain ⟨R₀, hR₀⟩ := core_bound (a := a) (b := b) hNc hK hchart
    (fun z hz hzim => log_shift_bound hz hzim) hC₀ hC₀b
    (fun c => log_sq_le_id c) hε'pos hε'le1
  obtain ⟨Rτ, hRτ⟩ := hτasym (ε' / 16) (by linarith)
  refine ⟨max R₀ Rτ, ?_⟩
  intro u hu n hη hb
  have hη' : max R₀ Rτ < |u.im| := by simpa using hη
  have h1 : R₀ < |u.im| := lt_of_le_of_lt (le_max_left R₀ Rτ) hη'
  have h2 : Rτ < ‖u‖ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right R₀ Rτ) hη') (Complex.abs_im_le_norm u)
  have h3 : ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε' / 16 := hRτ u hu h2
  have h4 := hR₀ u (τ u) h1 h3 n hb
  exact lt_of_lt_of_le h4 hε'leε

end

end Work.Parab.coordData
