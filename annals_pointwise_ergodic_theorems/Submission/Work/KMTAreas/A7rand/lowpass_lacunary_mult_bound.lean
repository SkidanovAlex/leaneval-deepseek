import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Work.KMTAreas.A7rand.sum_range_abel
import Submission.Work.KMTAreas.A7rand.bad_card_le_three
import Submission.Work.KMTAreas.A7rand.good_value_zero
import Submission.Work.KMTAreas.A7rand.good_deriv_zero
import Submission.Work.KMTAreas.A7rand.good_deriv2_zero
import Submission.Work.KMTAreas.A7rand.symbol_deriv_formulas

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7rand

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

/-! ## The cutoff `η = kmtEta` is locally constant at `0`

`kmtEta` equals `1` on the closed ball of radius `1/2`, hence at every interior point of that ball
its derivative and second derivative vanish.  These two facts make the "good/bad level" dichotomy
work: on the dyadic scales `2^k` with `2^k|ξ| < 1/2` the bump is constant, and on those with
`2^k|ξ| > 1` it vanishes near `ξ`. -/

lemma kmtEta_eventuallyEq_one (y : ℝ) (hy : |y| < 1 / 2) :
    Work.KMTContract.kmtEta =ᶠ[𝓝 y] fun _ => (1 : ℂ) := by
  have hmem : Metric.ball y (1 / 2 - |y|) ∈ 𝓝 y := Metric.ball_mem_nhds y (by linarith)
  refine Filter.mem_of_superset hmem (fun z hz => ?_)
  rw [Metric.mem_ball, Real.dist_eq] at hz
  refine Work.KMTContract.kmtEta_one (le_of_lt ?_)
  have h1 : |z| - |y| ≤ |z - y| := abs_sub_abs_le_abs_sub z y
  linarith [abs_nonneg y]

lemma kmtEta_deriv_eq_zero_of_abs_lt (y : ℝ) (hy : |y| < 1 / 2) :
    deriv Work.KMTContract.kmtEta y = 0 := by
  have h := kmtEta_eventuallyEq_one y hy
  calc deriv Work.KMTContract.kmtEta y
      = deriv (fun _ : ℝ => (1 : ℂ)) y := Filter.EventuallyEq.eq_of_nhds h.deriv
    _ = 0 := deriv_const y 1

lemma kmtEta_iteratedDeriv_two_eq_zero_of_abs_lt (y : ℝ) (hy : |y| < 1 / 2) :
    iteratedDeriv 2 Work.KMTContract.kmtEta y = 0 := by
  have h := kmtEta_eventuallyEq_one y hy
  have h2 : iteratedDeriv 2 Work.KMTContract.kmtEta y
      = iteratedDeriv 2 (fun _ : ℝ => (1 : ℂ)) y :=
    Filter.EventuallyEq.eq_of_nhds (h.iteratedDeriv 2)
  rw [h2, iteratedDeriv_const]
  norm_num

/-! ## The Mikhlin bound for the low-pass lacunary symbol -/

theorem lowpass_symbol_mikhlin (η : ℝ → ℂ) (M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (hηcd : ContDiff ℝ 2 η)
    (hη0 : ∀ y : ℝ, |y| ≤ 1 → ‖η y‖ ≤ M0)
    (hη1 : ∀ y : ℝ, |y| ≤ 1 → ‖deriv η y‖ ≤ M1)
    (hη2 : ∀ y : ℝ, |y| ≤ 1 → ‖iteratedDeriv 2 η y‖ ≤ M2)
    (hηs0 : ∀ y : ℝ, 1 ≤ |y| → η y = 0)
    (hηs1 : ∀ y : ℝ, 1 ≤ |y| → deriv η y = 0)
    (hηs2 : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 η y = 0)
    (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y)
    (hηone : ∀ y : ℝ, |y| ≤ 1 / 2 → η y = 1)
    (hη1in : ∀ y : ℝ, |y| < 1 / 2 → deriv η y = 0)
    (hη2in : ∀ y : ℝ, |y| < 1 / 2 → iteratedDeriv 2 η y = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℕ → ℕ) (hs : Monotone s) (K : ℕ) (d : ℕ → ℂ),
      (∀ c e : ℕ, ‖∑ m ∈ Finset.Icc c e, d m‖ ≤ 4) →
      ContDiff ℝ 2 (fun ξ : ℝ => ∑ k ∈ Finset.range K, d k * η ((2 : ℝ) ^ (s k) * ξ)) ∧
      (∀ ξ : ℝ, ‖∑ k ∈ Finset.range K, d k * η ((2 : ℝ) ^ (s k) * ξ)‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => ∑ k ∈ Finset.range K, d k * η ((2 : ℝ) ^ (s k) * ξ)) ξ‖
        ≤ A) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 *
        ‖iteratedDeriv 2 (fun ξ : ℝ => ∑ k ∈ Finset.range K, d k * η ((2 : ℝ) ^ (s k) * ξ)) ξ‖
        ≤ A) := by
  set Ac : ℝ := 28 * (M0 + M1 + M2) + 1 with hAcdef
  have hAcpos : 0 < Ac := by
    rw [hAcdef]
    nlinarith
  refine ⟨Ac, hAcpos, ?_⟩
  intro s hs K d hd
  -- uniform bounds for `η` and its first two derivatives
  have hU0 : ∀ y : ℝ, ‖η y‖ ≤ M0 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hη0 y h
    · rw [hηs0 y (le_of_lt (not_le.mp h)), norm_zero]
      exact hM0
  have hU1 : ∀ y : ℝ, |y| * ‖deriv η y‖ ≤ M1 := by
    intro y
    by_cases h : |y| ≤ 1
    · calc |y| * ‖deriv η y‖ ≤ 1 * ‖deriv η y‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = ‖deriv η y‖ := one_mul _
        _ ≤ M1 := hη1 y h
    · rw [hηs1 y (le_of_lt (not_le.mp h)), norm_zero, mul_zero]
      exact hM1
  have hU2 : ∀ y : ℝ, |y| ^ 2 * ‖iteratedDeriv 2 η y‖ ≤ M2 := by
    intro y
    by_cases h : |y| ≤ 1
    · have h2 : |y| ^ 2 ≤ 1 := by nlinarith [abs_nonneg y]
      calc |y| ^ 2 * ‖iteratedDeriv 2 η y‖ ≤ 1 * ‖iteratedDeriv 2 η y‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖iteratedDeriv 2 η y‖ := one_mul _
        _ ≤ M2 := hη2 y h
    · rw [hηs2 y (le_of_lt (not_le.mp h)), norm_zero, mul_zero]
      exact hM2
  -- prefix sums of `d`
  have hP : ∀ m : ℕ, ‖∑ j ∈ Finset.range m, d j‖ ≤ 4 := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hrange : Finset.range m = Finset.Icc 0 (m - 1) := by
        ext j
        simp only [Finset.mem_range, Finset.mem_Icc]
        omega
      rw [hrange]
      exact hd 0 (m - 1)
  have habel : ∀ (n : ℕ) (w : ℕ → ℂ),
      ∑ k ∈ Finset.range n, d k * w k
        = (∑ k ∈ Finset.range n, d k) * w (n - 1)
          + ∑ k ∈ Finset.range (n - 1),
              (∑ j ∈ Finset.range (k + 1), d j) * (w k - w (k + 1)) :=
    fun n w => sum_range_abel n d w
  have hforms := symbol_deriv_formulas η hηcd hηd hηd2 s K d
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ContDiff.sum (fun k _ => ?_)
    exact (contDiff_const (c := d k)).mul (hηcd.comp (contDiff_const.mul contDiff_id))
  · -- ## the pointwise bound
    intro ξ
    set B : Finset ℕ := (Finset.range (K - 1)).filter (fun k : ℕ => s (k + 1) > s k ∧
      (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) with hB
    have hBcard : B.card ≤ 3 := by
      rw [hB]; exact bad_card_le_three (K - 1) s hs ξ
    have hzero : ∀ k ∈ Finset.range (K - 1),
        ¬ (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
            (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) →
        η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ) = 0 :=
      fun k _ hk => good_value_zero η hηone hηs0 s hs k ξ hk
    have hterm : ∀ k ∈ Finset.range (K - 1),
        ‖(∑ j ∈ Finset.range (k + 1), d j) *
          (η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
        ≤ if (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
          then 4 * (2 * M0) else 0 := by
      intro k hk
      by_cases hp : (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
      · rw [if_pos hp, norm_mul]
        have hdiff : ‖η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖ ≤ 2 * M0 := by
          calc ‖η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖
              ≤ ‖η ((2 : ℝ) ^ (s k) * ξ)‖ + ‖η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖ := norm_sub_le _ _
            _ ≤ M0 + M0 := add_le_add (hU0 _) (hU0 _)
            _ = 2 * M0 := by ring
        exact mul_le_mul (hP (k + 1)) hdiff (norm_nonneg _) (by norm_num)
      · rw [if_neg hp, hzero k hk hp]
        simp
    have hboundary : ‖(∑ k ∈ Finset.range K, d k) * η ((2 : ℝ) ^ (s (K - 1)) * ξ)‖ ≤ 4 * M0 := by
      rw [norm_mul]
      exact mul_le_mul (hP K) (hU0 _) (norm_nonneg _) (by norm_num)
    have hmain : ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
        (η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
        ≤ 3 * (4 * (2 * M0)) := by
      calc ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
            (η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
          ≤ ∑ k ∈ Finset.range (K - 1), ‖(∑ j ∈ Finset.range (k + 1), d j) *
              (η ((2 : ℝ) ^ (s k) * ξ) - η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (K - 1), (if (s (k + 1) > s k ∧
              (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
              then 4 * (2 * M0) else 0) := Finset.sum_le_sum hterm
        _ = ∑ k ∈ B, 4 * (2 * M0) := by rw [hB, Finset.sum_filter]
        _ = (B.card : ℝ) * (4 * (2 * M0)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (4 * (2 * M0)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) (by positivity)
    rw [habel K (fun k => η ((2 : ℝ) ^ (s k) * ξ))]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add hboundary hmain) ?_)
    rw [hAcdef]; nlinarith [hM1, hM2]
  · -- ## the first derivative bound
    intro ξ
    rw [hforms.1 ξ]
    set B : Finset ℕ := (Finset.range (K - 1)).filter (fun k : ℕ => s (k + 1) > s k ∧
      (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) with hB
    have hBcard : B.card ≤ 3 := by
      rw [hB]; exact bad_card_le_three (K - 1) s hs ξ
    have hzero : ∀ k ∈ Finset.range (K - 1),
        ¬ (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
            (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) →
        (2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
          - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ) = 0 :=
      fun k _ hk => good_deriv_zero η hη1in hηs1 s hs k ξ hk
    have hw : ∀ k : ℕ, |ξ| * ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)‖ ≤ M1 := by
      intro k
      have hc : (0 : ℝ) < (2 : ℝ) ^ (s k) := by positivity
      have hn : ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)‖
          = (2 : ℝ) ^ (s k) * ‖deriv η ((2 : ℝ) ^ (s k) * ξ)‖ := by
        simp only [(Complex.ofReal_pow 2 (s k)).symm, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hc]
      rw [hn]
      calc |ξ| * ((2 : ℝ) ^ (s k) * ‖deriv η ((2 : ℝ) ^ (s k) * ξ)‖)
          = |(2 : ℝ) ^ (s k) * ξ| * ‖deriv η ((2 : ℝ) ^ (s k) * ξ)‖ := by
            rw [abs_mul, abs_of_pos hc]; ring
        _ ≤ M1 := hU1 _
    have hterm : ∀ k ∈ Finset.range (K - 1),
        |ξ| * ‖(∑ j ∈ Finset.range (k + 1), d j) *
          ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
            - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
        ≤ if (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
          then 4 * (2 * M1) else 0 := by
      intro k hk
      by_cases hp : (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
      · rw [if_pos hp]
        have hdiff : |ξ| * ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
            - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖ ≤ 2 * M1 := by
          calc |ξ| * ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖
              ≤ |ξ| * (‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)‖
                  + ‖(2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖) :=
                mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg ξ)
            _ = |ξ| * ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)‖
                  + |ξ| * ‖(2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖ := by ring
            _ ≤ M1 + M1 := add_le_add (hw k) (hw (k + 1))
            _ = 2 * M1 := by ring
        calc |ξ| * ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
            = |ξ| * (‖(∑ j ∈ Finset.range (k + 1), d j)‖ *
                ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                  - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖) := by
              rw [norm_mul]
          _ = ‖(∑ j ∈ Finset.range (k + 1), d j)‖ *
                (|ξ| * ‖(2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                  - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ)‖) := by ring
          _ ≤ 4 * (2 * M1) :=
              mul_le_mul (hP (k + 1)) hdiff (by positivity) (by norm_num)
      · rw [if_neg hp, hzero k hk hp]
        simp
    have hboundary : |ξ| * ‖(∑ k ∈ Finset.range K, d k) *
        ((2 : ℝ) ^ (s (K - 1)) * deriv η ((2 : ℝ) ^ (s (K - 1)) * ξ))‖ ≤ 4 * M1 := by
      rw [norm_mul]
      calc |ξ| * (‖∑ k ∈ Finset.range K, d k‖ *
            ‖(2 : ℝ) ^ (s (K - 1)) * deriv η ((2 : ℝ) ^ (s (K - 1)) * ξ)‖)
          = ‖∑ k ∈ Finset.range K, d k‖ *
            (|ξ| * ‖(2 : ℝ) ^ (s (K - 1)) * deriv η ((2 : ℝ) ^ (s (K - 1)) * ξ)‖) := by ring
        _ ≤ 4 * M1 := mul_le_mul (hP K) (hw (K - 1)) (by positivity) (by norm_num)
    have hmain : |ξ| * ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
        ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
          - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
        ≤ 3 * (4 * (2 * M1)) := by
      calc |ξ| * ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
            ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
              - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
          ≤ |ξ| * ∑ k ∈ Finset.range (K - 1), ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg ξ)
        _ = ∑ k ∈ Finset.range (K - 1), |ξ| * ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
                - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖ :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ k ∈ Finset.range (K - 1), (if (s (k + 1) > s k ∧
              (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
              then 4 * (2 * M1) else 0) := Finset.sum_le_sum hterm
        _ = ∑ k ∈ B, 4 * (2 * M1) := by rw [hB, Finset.sum_filter]
        _ = (B.card : ℝ) * (4 * (2 * M1)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (4 * (2 * M1)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) (by positivity)
    rw [habel K (fun k => (2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ))]
    have hcomb : |ξ| * (‖(∑ k ∈ Finset.range K, d k) *
          ((2 : ℝ) ^ (s (K - 1)) * deriv η ((2 : ℝ) ^ (s (K - 1)) * ξ))‖
        + ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
            ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)
              - (2 : ℝ) ^ (s (k + 1)) * deriv η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖)
        ≤ 4 * M1 + 3 * (4 * (2 * M1)) := by
      rw [mul_add]
      exact add_le_add hboundary hmain
    refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg ξ)) ?_
    refine le_trans hcomb ?_
    rw [hAcdef]; nlinarith [hM0, hM2]
  · -- ## the second derivative bound
    intro ξ
    rw [hforms.2 ξ]
    set B : Finset ℕ := (Finset.range (K - 1)).filter (fun k : ℕ => s (k + 1) > s k ∧
      (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) with hB
    have hBcard : B.card ≤ 3 := by
      rw [hB]; exact bad_card_le_three (K - 1) s hs ξ
    have hcast2 : ∀ k : ℕ, ((2 : ℝ) ^ (2 * s k) : ℂ)
        = ((2 : ℝ) ^ (s k) : ℂ) * ((2 : ℝ) ^ (s k) : ℂ) := by
      intro k
      rw [show 2 * s k = s k + s k by ring, pow_add]
    have hzero : ∀ k ∈ Finset.range (K - 1),
        ¬ (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
            (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|) →
        (2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
          - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
              iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)) = 0 := by
      intro k _ hk
      have h := good_deriv2_zero η hη2in hηs2 s hs k ξ hk
      have h1 : (2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
          = (2 : ℝ) ^ (2 * s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ) := by
        rw [hcast2 k]; ring
      have h2 : (2 : ℝ) ^ (s (k + 1)) *
            ((2 : ℝ) ^ (s (k + 1)) * iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))
          = (2 : ℝ) ^ (2 * s (k + 1)) * iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ) := by
        rw [hcast2 (k + 1)]; ring
      rw [h1, h2]
      exact h
    have hw : ∀ k : ℕ, |ξ| ^ 2 * ‖(2 : ℝ) ^ (s k) *
        ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))‖ ≤ M2 := by
      intro k
      have hc : (0 : ℝ) < (2 : ℝ) ^ (s k) := by positivity
      have hn : ‖(2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))‖
          = (2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) *
              ‖iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)‖) := by
        simp only [(Complex.ofReal_pow 2 (s k)).symm, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hc]
      rw [hn]
      calc |ξ| ^ 2 * ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) *
              ‖iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)‖))
          = |(2 : ℝ) ^ (s k) * ξ| ^ 2 * ‖iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)‖ := by
            rw [abs_mul, abs_of_pos hc]; ring
        _ ≤ M2 := hU2 _
    have hterm : ∀ k ∈ Finset.range (K - 1),
        |ξ| ^ 2 * ‖(∑ j ∈ Finset.range (k + 1), d j) *
          ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
            - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖
        ≤ if (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
          then 4 * (2 * M2) else 0 := by
      intro k hk
      by_cases hp : (s (k + 1) > s k ∧ (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧
              (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
      · rw [if_pos hp]
        have hdiff : |ξ| ^ 2 * ‖(2 : ℝ) ^ (s k) *
              ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
            - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖ ≤ 2 * M2 := by
          calc |ξ| ^ 2 * ‖(2 : ℝ) ^ (s k) *
                ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
              - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                  iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖
              ≤ |ξ| ^ 2 * (‖(2 : ℝ) ^ (s k) *
                    ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))‖
                  + ‖(2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                      iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖) :=
                mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg _)
            _ = |ξ| ^ 2 * ‖(2 : ℝ) ^ (s k) *
                    ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))‖
                  + |ξ| ^ 2 * ‖(2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                      iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖ := by ring
            _ ≤ M2 + M2 := add_le_add (hw k) (hw (k + 1))
            _ = 2 * M2 := by ring
        calc |ξ| ^ 2 * ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
                - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                    iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖
            = |ξ| ^ 2 * (‖(∑ j ∈ Finset.range (k + 1), d j)‖ *
                ‖(2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
                  - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                      iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖) := by
              rw [norm_mul]
          _ = ‖(∑ j ∈ Finset.range (k + 1), d j)‖ *
                (|ξ| ^ 2 * ‖(2 : ℝ) ^ (s k) *
                  ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
                  - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                      iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ))‖) := by ring
          _ ≤ 4 * (2 * M2) := mul_le_mul (hP (k + 1)) hdiff (by positivity) (by norm_num)
      · rw [if_neg hp, hzero k hk hp]
        simp
    have hboundary : |ξ| ^ 2 * ‖(∑ k ∈ Finset.range K, d k) *
        ((2 : ℝ) ^ (s (K - 1)) * ((2 : ℝ) ^ (s (K - 1)) *
          iteratedDeriv 2 η ((2 : ℝ) ^ (s (K - 1)) * ξ)))‖ ≤ 4 * M2 := by
      rw [norm_mul]
      calc |ξ| ^ 2 * (‖∑ k ∈ Finset.range K, d k‖ *
            ‖(2 : ℝ) ^ (s (K - 1)) * ((2 : ℝ) ^ (s (K - 1)) *
              iteratedDeriv 2 η ((2 : ℝ) ^ (s (K - 1)) * ξ))‖)
          = ‖∑ k ∈ Finset.range K, d k‖ *
            (|ξ| ^ 2 * ‖(2 : ℝ) ^ (s (K - 1)) * ((2 : ℝ) ^ (s (K - 1)) *
              iteratedDeriv 2 η ((2 : ℝ) ^ (s (K - 1)) * ξ))‖) := by ring
        _ ≤ 4 * M2 := mul_le_mul (hP K) (hw (K - 1)) (by positivity) (by norm_num)
    have hmain : |ξ| ^ 2 * ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
        ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
          - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
              iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖
        ≤ 3 * (4 * (2 * M2)) := by
      calc |ξ| ^ 2 * ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
            ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
              - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                  iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖
          ≤ |ξ| ^ 2 * ∑ k ∈ Finset.range (K - 1), ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
                - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                    iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
        _ = ∑ k ∈ Finset.range (K - 1), |ξ| ^ 2 * ‖(∑ j ∈ Finset.range (k + 1), d j) *
              ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
                - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                    iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖ :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ k ∈ Finset.range (K - 1), (if (s (k + 1) > s k ∧
              (2 : ℝ) ^ (s k) * |ξ| ≤ 1 ∧ (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (k + 1)) * |ξ|)
              then 4 * (2 * M2) else 0) := Finset.sum_le_sum hterm
        _ = ∑ k ∈ B, 4 * (2 * M2) := by rw [hB, Finset.sum_filter]
        _ = (B.card : ℝ) * (4 * (2 * M2)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (4 * (2 * M2)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) (by positivity)
    rw [habel K (fun k => (2 : ℝ) ^ (s k) *
      ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)))]
    have hcomb : |ξ| ^ 2 * (‖(∑ k ∈ Finset.range K, d k) *
          ((2 : ℝ) ^ (s (K - 1)) * ((2 : ℝ) ^ (s (K - 1)) *
            iteratedDeriv 2 η ((2 : ℝ) ^ (s (K - 1)) * ξ)))‖
        + ‖∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) *
            ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))
              - (2 : ℝ) ^ (s (k + 1)) * ((2 : ℝ) ^ (s (k + 1)) *
                  iteratedDeriv 2 η ((2 : ℝ) ^ (s (k + 1)) * ξ)))‖)
        ≤ 4 * M2 + 3 * (4 * (2 * M2)) := by
      rw [mul_add]
      exact add_le_add hboundary hmain
    refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg _)) ?_
    refine le_trans hcomb ?_
    rw [hAcdef]; nlinarith [hM0, hM1]

/-! ## The continuous multiplier of a symbol is the inverse Fourier integral -/

lemma lowpass_contMulOp_eq_integral (m : ℝ → ℂ) (G : SchwartzMap ℝ ℂ) (x : ℝ) :
    Work.Analysis.IWMultiplier.contMulOp m (G : ℝ → ℂ) x
      = ∫ ξ : ℝ, (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (G : ℝ → ℂ) ξ) := by
  rw [Work.Analysis.IWMultiplier.contMulOp, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [smul_eq_mul]
  have hexp : (↑(2 * Real.pi * inner ℝ v x) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (x * v) := by
    rw [Real.inner_apply]
    push_cast
    ring
  rw [hexp]
  ring

/-! ## The target: the low-pass lacunary multiplier is bounded on `L^p(ℝ)` -/

theorem lowpass_lacunary_mult_bound (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (M : ℕ) (d : ℕ → ℂ),
      (∀ c e : ℕ, ‖∑ m ∈ Finset.Icc c e, d m‖ ≤ 4) →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal p)
        (fun ξ : ℝ => ∑ m ∈ Finset.range M,
          d m * Work.KMTAreas.A7.varphiN (Nat.floor (a m)) 0 ξ) C := by
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hηcd, hη0, hη1, hη2, hηs0, hηs1, hηs2, hηd, hηd2⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  have hηone : ∀ y : ℝ, |y| ≤ 1 / 2 → Work.KMTContract.kmtEta y = 1 :=
    fun y hy => Work.KMTContract.kmtEta_one hy
  have hη1in : ∀ y : ℝ, |y| < 1 / 2 → deriv Work.KMTContract.kmtEta y = 0 :=
    kmtEta_deriv_eq_zero_of_abs_lt
  have hη2in : ∀ y : ℝ, |y| < 1 / 2 → iteratedDeriv 2 Work.KMTContract.kmtEta y = 0 :=
    kmtEta_iteratedDeriv_two_eq_zero_of_abs_lt
  obtain ⟨A, hApos, hA⟩ :=
    lowpass_symbol_mikhlin Work.KMTContract.kmtEta M0 M1 M2 hM0 hM1 hM2 hηcd hη0 hη1 hη2
      hηs0 hηs1 hηs2 hηd hηd2 hηone hη1in hη2in
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  have hCmA : (0 : ℝ) < Cm * A := mul_pos hCmpos hApos
  refine ⟨⟨Cm * A, le_of_lt hCmA⟩, ?_, ?_⟩
  · exact NNReal.coe_pos.mp hCmA
  intro a ha M d hd f
  -- `a n > 0` and `a` is strictly increasing
  have hpos_a : ∀ n : ℕ, (0 : NNReal) < a n := by
    intro n
    by_contra h
    have h0 : a n = 0 := le_antisymm (not_lt.mp h) (zero_le : (0 : NNReal) ≤ a n)
    have h1 := ha n
    rw [h0, div_zero] at h1
    exact absurd h1 (not_lt.mpr (zero_le : (0 : NNReal) ≤ Λ))
  have hstep : ∀ n : ℕ, (Λ : ℝ) * (a n : ℝ) < (a (n + 1) : ℝ) := by
    intro n
    have h := ha n
    have h'' : ((Λ : NNReal) : ℝ) < ((a (n + 1) / a n : NNReal) : ℝ) := by exact_mod_cast h
    rw [NNReal.coe_div] at h''
    have hp0 : 0 < (a n : ℝ) := by
      have := hpos_a n
      exact_mod_cast this
    have := mul_lt_mul_of_pos_right h'' hp0
    rw [div_mul_cancel₀ _ (ne_of_gt hp0)] at this
    simpa [mul_comm] using this
  have hle_succ : ∀ n : ℕ, a n ≤ a (n + 1) := by
    intro n
    have h1 : (a n : ℝ) ≤ (Λ : ℝ) * (a n : ℝ) := by
      have h2 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast (le_of_lt hΛ)
      nlinarith [show (0 : ℝ) ≤ (a n : ℝ) by positivity]
    have h3 : (a n : ℝ) ≤ (a (n + 1) : ℝ) := le_trans h1 (le_of_lt (hstep n))
    exact_mod_cast h3
  have hmono : Monotone a := monotone_nat_of_le_succ hle_succ
  set s : ℕ → ℕ := fun m => Nat.log 2 (max (Nat.floor (a m)) 2) with hsdef
  have hsmono : Monotone s := fun i j hij =>
    Nat.log_mono_right (max_le_max (Nat.floor_mono (hmono hij)) le_rfl)
  -- identify `varphiN ⌊a m⌋ 0` with `kmtEta (2 ^ (s m) ·)`
  have hsym : (fun ξ : ℝ => ∑ m ∈ Finset.range M,
        d m * Work.KMTAreas.A7.varphiN (Nat.floor (a m)) 0 ξ)
      = fun ξ : ℝ => ∑ m ∈ Finset.range M,
          d m * Work.KMTContract.kmtEta ((2 : ℝ) ^ (s m) * ξ) := by
    funext ξ
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    have harg : ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℤ) : ℝ) = ((s m : ℕ) : ℝ) := by
      simp only [Work.Analysis.EndVar.logN, s]
      norm_num
    rw [Work.KMTAreas.A7.varphiN]
    simp only [↓reduceIte]
    rw [harg, Real.rpow_natCast]
  rw [hsym]
  obtain ⟨hcd, hb0, hb1, hb2⟩ := hA s hsmono M d hd
  have hmain := hCm (fun ξ : ℝ => ∑ k ∈ Finset.range M,
      d k * Work.KMTContract.kmtEta ((2 : ℝ) ^ (s k) * ξ)) A hApos.le hcd hb0 hb1 hb2 f
  rw [show Work.Analysis.IWMultiplier.contMulOp
      (fun ξ : ℝ => ∑ k ∈ Finset.range M,
        d k * Work.KMTContract.kmtEta ((2 : ℝ) ^ (s k) * ξ)) (f : ℝ → ℂ)
      = fun x : ℝ => ∫ ξ : ℝ, ((∑ k ∈ Finset.range M,
          d k * Work.KMTContract.kmtEta ((2 : ℝ) ^ (s k) * ξ)) *
          Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
            • (FourierTransform.fourier (f : ℝ → ℂ) ξ) from
    funext (fun x => lowpass_contMulOp_eq_integral _ f x)]
  exact hmain

end Work.KMTAreas.A7rand
