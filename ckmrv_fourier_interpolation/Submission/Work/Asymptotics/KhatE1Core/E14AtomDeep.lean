import Mathlib
import Submission.Work.Asymptotics.funnel_tauAtom_second_order

/-!
# Deep `q`-expansion of `E₁₄ = E₄²E₆` at the cusp

The `E(z)^4`-coefficient of the `Sh`-cleared `d = 24` bracket needs the second-order term of
`E₁₄(z) = E₄(z)²E₆(z)`.  This module proves

  `E₁₄(z) = 1 - 24 q(z) - 196632 q(z)² + O(‖q(z)‖³)`  on `{1 ≤ Im z}`,

from the proved `Work.Asymptotics.E4Fun_second_order` and
`Work.Asymptotics.E6Fun_second_order` via the exact identity
`E₄²E₆ - Q = (E₄ - P)(E₄ + P)E₆ + P²(E₆ - P6)` with `P = 1 + 240q + 2160q²`,
`P6 = 1 - 504q - 16632q²`, `P²P6 = Q = 1 - 24q - 196632q²`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- **Third-order expansion of `E₁₄ = E₄²E₆` on `{1 ≤ Im z}`.** -/
theorem E14FunFourthOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E14Fun z - (1 - 24 * Work.Kernels.qParamFun z
          - 196632 * (Work.Kernels.qParamFun z) ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C4, hC40, h4⟩ := Work.Asymptotics.E4Fun_second_order
  obtain ⟨C6, hC60, h6⟩ := Work.Asymptotics.E6Fun_second_order
  refine ⟨C4 * (C4 + 4802) * (C6 + 17137) + 5764801 * C6 + 98779668480 + 1, by positivity,
    fun z hz => ?_⟩
  have hqle : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hqnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by nlinarith [hqle, hqnn]
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := by nlinarith [hqle, hq2, hqnn]
  have hE4' : ‖Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖
      ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    convert h4 z hz using 2 <;> ring_nf
  have hE6' : ‖Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
      - 16632 * (Work.Kernels.qParamFun z) ^ 2)‖
      ≤ C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    convert h6 z hz using 2 <;> ring_nf
  have hP : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ 2401 := by
    have h1 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
        + 2160 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖
          + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have a := norm_add_le ((1 : ℂ) + 240 * Work.Kernels.qParamFun z)
        ((2160 : ℂ) * (Work.Kernels.qParamFun z) ^ 2)
      have b := norm_add_le (1 : ℂ) ((240 : ℂ) * Work.Kernels.qParamFun z)
      simp only [norm_mul, norm_one, norm_pow, Complex.norm_ofNat] at a b
      linarith
    nlinarith [h1, hqle, hq2, hqnn]
  have hP6 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
      - 16632 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ 17137 := by
    have h1 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
        - 16632 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ 1 + 504 * ‖Work.Kernels.qParamFun z‖
          + 16632 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have a := norm_sub_le ((1 : ℂ) - 504 * Work.Kernels.qParamFun z)
        ((16632 : ℂ) * (Work.Kernels.qParamFun z) ^ 2)
      have b := norm_sub_le (1 : ℂ) ((504 : ℂ) * Work.Kernels.qParamFun z)
      simp only [norm_mul, norm_one, norm_pow, Complex.norm_ofNat] at a b
      linarith
    nlinarith [h1, hqle, hq2, hqnn]
  have hP2 : ‖(1 : ℂ) + 480 * Work.Kernels.qParamFun z
      + 61920 * (Work.Kernels.qParamFun z) ^ 2‖ ≤ 62401 := by
    have h1 : ‖(1 : ℂ) + 480 * Work.Kernels.qParamFun z
        + 61920 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ 1 + 480 * ‖Work.Kernels.qParamFun z‖
          + 61920 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have a := norm_add_le ((1 : ℂ) + 480 * Work.Kernels.qParamFun z)
        ((61920 : ℂ) * (Work.Kernels.qParamFun z) ^ 2)
      have b := norm_add_le (1 : ℂ) ((480 : ℂ) * Work.Kernels.qParamFun z)
      simp only [norm_mul, norm_one, norm_pow, Complex.norm_ofNat] at a b
      linarith
    nlinarith [h1, hqle, hq2, hqnn]
  have hsub : ‖Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖ ≤ C4 := by
    refine le_trans hE4' ?_
    have h := mul_le_mul_of_nonneg_left hq3 hC40.le
    linarith
  have hsum4 : ‖Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖ ≤ C4 + 4802 := by
    have h2P : ‖(2 : ℂ) * (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖ ≤ 4802 := by
      rw [norm_mul]
      have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h2]
      linarith [hP]
    have h' := norm_add_le (Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * (Work.Kernels.qParamFun z) ^ 2))
      (2 * (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * (Work.Kernels.qParamFun z) ^ 2))
    have heq : Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2)
        + 2 * (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2)
        = Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2) := by ring_nf
    rw [heq] at h'
    linarith [h', h2P, hsub]
  have hE6b : ‖Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
      - 16632 * (Work.Kernels.qParamFun z) ^ 2)‖ ≤ C6 := by
    refine le_trans hE6' ?_
    have h := mul_le_mul_of_nonneg_left hq3 hC60.le
    linarith
  have hnE6 : ‖Work.Kernels.E6Fun z‖ ≤ C6 + 17137 := by
    have h' := norm_add_le (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
        - 16632 * (Work.Kernels.qParamFun z) ^ 2))
      (1 - 504 * Work.Kernels.qParamFun z - 16632 * (Work.Kernels.qParamFun z) ^ 2)
    have heq : Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
          - 16632 * (Work.Kernels.qParamFun z) ^ 2)
        + (1 - 504 * Work.Kernels.qParamFun z
          - 16632 * (Work.Kernels.qParamFun z) ^ 2) = Work.Kernels.E6Fun z := by ring_nf
    rw [heq] at h'
    linarith [h', hE6b, hP6]
  have hkey : Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z
      - (1 - 24 * Work.Kernels.qParamFun z - 196632 * (Work.Kernels.qParamFun z) ^ 2)
      = (Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * Work.Kernels.E6Fun z
        + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
          * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
            - 16632 * (Work.Kernels.qParamFun z) ^ 2))
        + ((1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
            * (1 - 504 * Work.Kernels.qParamFun z
              - 16632 * (Work.Kernels.qParamFun z) ^ 2)
            - (1 - 24 * Work.Kernels.qParamFun z
              - 196632 * (Work.Kernels.qParamFun z) ^ 2)) := by
    ring
  have hP2n : ‖(1 + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2‖ ≤ 5764801 := by
    rw [norm_pow]
    nlinarith [hP, norm_nonneg ((1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2)]
  have hrem : ‖(1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
        * (1 - 504 * Work.Kernels.qParamFun z
          - 16632 * (Work.Kernels.qParamFun z) ^ 2)
        - (1 - 24 * Work.Kernels.qParamFun z
          - 196632 * (Work.Kernels.qParamFun z) ^ 2)‖
      ≤ 98779668480 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hid : (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
          * (1 - 504 * Work.Kernels.qParamFun z
            - 16632 * (Work.Kernels.qParamFun z) ^ 2)
          - (1 - 24 * Work.Kernels.qParamFun z
            - 196632 * (Work.Kernels.qParamFun z) ^ 2)
        = Work.Kernels.qParamFun z ^ 3
          * ((-38154240 : ℂ) - 1547735040 * Work.Kernels.qParamFun z
              - 19595520000 * (Work.Kernels.qParamFun z) ^ 2
              - 77598259200 * (Work.Kernels.qParamFun z) ^ 3) := by ring_nf
    rw [hid, norm_mul, norm_pow]
    have hqnn3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
    have hn : ‖((-38154240 : ℂ) - 1547735040 * Work.Kernels.qParamFun z
          - 19595520000 * (Work.Kernels.qParamFun z) ^ 2
          - 77598259200 * (Work.Kernels.qParamFun z) ^ 3)‖ ≤ 98779668480 := by
      have a := norm_sub_le (((-38154240 : ℂ) - 1547735040 * Work.Kernels.qParamFun z
        - 19595520000 * (Work.Kernels.qParamFun z) ^ 2))
        (77598259200 * (Work.Kernels.qParamFun z) ^ 3)
      have b := norm_sub_le (((-38154240 : ℂ) - 1547735040 * Work.Kernels.qParamFun z))
        (19595520000 * (Work.Kernels.qParamFun z) ^ 2)
      have c := norm_sub_le ((-38154240 : ℂ)) (1547735040 * Work.Kernels.qParamFun z)
      simp only [norm_mul, norm_pow, norm_one, norm_neg, Complex.norm_ofNat] at a b c
      have e1 : 1547735040 * ‖Work.Kernels.qParamFun z‖ ≤ 1547735040 := by
        nlinarith [hqle, hqnn]
      have e2 : 19595520000 * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 19595520000 := by
        nlinarith [hq2, hqnn]
      have e3 : 77598259200 * ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 77598259200 := by
        nlinarith [hq3, hqnn]
      linarith [a, b, c, e1, e2, e3]
    calc ‖Work.Kernels.qParamFun z‖ ^ 3
          * ‖((-38154240 : ℂ) - 1547735040 * Work.Kernels.qParamFun z
              - 19595520000 * (Work.Kernels.qParamFun z) ^ 2
              - 77598259200 * (Work.Kernels.qParamFun z) ^ 3)‖
        ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 * 98779668480 :=
          mul_le_mul_of_nonneg_left hn hqnn3
      _ = 98779668480 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring_nf
  have hgoal : Work.Kernels.E14Fun z - (1 - 24 * Work.Kernels.qParamFun z
        - 196632 * (Work.Kernels.qParamFun z) ^ 2)
      = (Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * Work.Kernels.E6Fun z
        + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
          * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
            - 16632 * (Work.Kernels.qParamFun z) ^ 2))
        + ((1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
            * (1 - 504 * Work.Kernels.qParamFun z
              - 16632 * (Work.Kernels.qParamFun z) ^ 2)
            - (1 - 24 * Work.Kernels.qParamFun z
              - 196632 * (Work.Kernels.qParamFun z) ^ 2)) := by
    rw [show Work.Kernels.E14Fun z
        = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z from rfl]
    exact hkey
  rw [hgoal]
  have htri : ‖(Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * Work.Kernels.E6Fun z
        + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
          * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
            - 16632 * (Work.Kernels.qParamFun z) ^ 2))
        + ((1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
            * (1 - 504 * Work.Kernels.qParamFun z
              - 16632 * (Work.Kernels.qParamFun z) ^ 2)
            - (1 - 24 * Work.Kernels.qParamFun z
              - 196632 * (Work.Kernels.qParamFun z) ^ 2))‖
      ≤ ‖(Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2))
          * Work.Kernels.E6Fun z
        + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
          * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
            - 16632 * (Work.Kernels.qParamFun z) ^ 2))‖
        + ‖(1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
            * (1 - 504 * Work.Kernels.qParamFun z
              - 16632 * (Work.Kernels.qParamFun z) ^ 2)
            - (1 - 24 * Work.Kernels.qParamFun z
              - 196632 * (Work.Kernels.qParamFun z) ^ 2)‖ := norm_add_le _ _
  have hA : ‖(Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2))
        * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2))
        * Work.Kernels.E6Fun z‖
      ≤ C4 * (C4 + 4802) * (C6 + 17137) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    have hnn1 : (0:ℝ) ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
    have hnn2 : (0:ℝ) ≤ C4 + 4802 := by linarith [hC40.le]
    calc ‖Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖
          * ‖Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * (Work.Kernels.qParamFun z) ^ 2)‖
          * ‖Work.Kernels.E6Fun z‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (C4 + 4802) * (C6 + 17137) :=
          mul_le_mul (mul_le_mul hE4' hsum4 (norm_nonneg _) hnn1) hnE6 (norm_nonneg _)
            (mul_nonneg hnn1 hnn2)
      _ = C4 * (C4 + 4802) * (C6 + 17137) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hB : ‖(1 + 240 * Work.Kernels.qParamFun z
          + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
        * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
          - 16632 * (Work.Kernels.qParamFun z) ^ 2))‖
      ≤ 5764801 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul]
    refine le_trans (mul_le_mul hP2n hE6' (by positivity) (by positivity)) ?_
    nlinarith [hC60.le, norm_nonneg (Work.Kernels.qParamFun z)]
  have hsum : C4 * (C4 + 4802) * (C6 + 17137) * ‖Work.Kernels.qParamFun z‖ ^ 3
        + 5764801 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3
        + 98779668480 * ‖Work.Kernels.qParamFun z‖ ^ 3
      ≤ (C4 * (C4 + 4802) * (C6 + 17137) + 5764801 * C6 + 98779668480 + 1)
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hqnn3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
    have h3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := hq3
    nlinarith [hqnn3, h3, hC40.le, hC60.le]
  calc _ ≤ _ := htri
    _ ≤ (C4 * (C4 + 4802) * (C6 + 17137) * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 5764801 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        + 98779668480 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        have h1 : ‖(Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2))
            * (Work.Kernels.E4Fun z + (1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2))
            * Work.Kernels.E6Fun z
          + (1 + 240 * Work.Kernels.qParamFun z
              + 2160 * (Work.Kernels.qParamFun z) ^ 2) ^ 2
            * (Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
              - 16632 * (Work.Kernels.qParamFun z) ^ 2))‖
          ≤ C4 * (C4 + 4802) * (C6 + 17137) * ‖Work.Kernels.qParamFun z‖ ^ 3
            + 5764801 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          le_trans (norm_add_le _ _) (add_le_add hA hB)
        linarith [h1, hrem]
    _ = (C4 * (C4 + 4802) * (C6 + 17137) + 5764801 * C6 + 98779668480)
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring_nf
    _ ≤ (C4 * (C4 + 4802) * (C6 + 17137) + 5764801 * C6 + 98779668480 + 1)
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        have hqnn3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
        nlinarith [hqnn3]
