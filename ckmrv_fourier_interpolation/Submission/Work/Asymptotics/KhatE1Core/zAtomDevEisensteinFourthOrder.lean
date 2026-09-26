import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Residues.ThetaEpt

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# The second-order deviations of the `z`-atoms `E₈`, `E₆`, `E₁₀`

`dE8 z = E₈(z) - (1 + 480 q(z))`, `dE6 z = E₆(z) - (1 - 504 q(z))`,
`dE10 z = E₁₀(z) - (1 - 264 q(z))` with `q(z) = qParamFun z = (Ept z)²` and
`E₈ = E₄²`, `E₁₀ = E₄E₆`.  From the three-term expansions `E₄ = 1+240q+2160q²+O(q³)`,
`E₆ = 1-504q-16632q²+O(q³)` one gets the explicit second-order deviations

  `dE8 = 61920 q² + O(q³)`,  `dE6 = -16632 q² + O(q³)`,  `dE10 = -135432 q² + O(q³)`,

since `(1+240q+2160q²)² = 1+480q+61920q²+O(q³)` and
`(1+240q+2160q²)(1-504q-16632q²) = 1-264q-135432q²+O(q³)`.
-/

private lemma q_eq_Ept_sq (z : ℍ) : Work.Kernels.qParamFun z = (Work.Residues.Ept z) ^ 2 := by
  rw [Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
  congr 1; ring

private lemma q_norm_eq (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [q_eq_Ept_sq z, norm_pow, Work.Residues.norm_Ept]
  rw [sq, ← Real.exp_add]
  congr 1; ring

private lemma q_norm_le_one {z : ℍ} (hz : 2 ≤ z.im) : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [q_norm_eq, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

/-- `‖q‖ ^ (k+1) ≤ ‖q‖ ^ k` on the funnel. -/
private lemma qpow_step {z : ℍ} (hz : 2 ≤ z.im) (k : ℕ) :
    ‖Work.Kernels.qParamFun z‖ ^ (k + 1) ≤ ‖Work.Kernels.qParamFun z‖ ^ k := by
  have h1 := q_norm_le_one hz
  have h0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ k :=
    pow_nonneg (norm_nonneg _) k
  calc ‖Work.Kernels.qParamFun z‖ ^ (k + 1)
      = ‖Work.Kernels.qParamFun z‖ ^ k * ‖Work.Kernels.qParamFun z‖ := by ring
    _ ≤ ‖Work.Kernels.qParamFun z‖ ^ k * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = ‖Work.Kernels.qParamFun z‖ ^ k := by ring

/-- `‖q‖ ^ 6 ≤ ‖q‖ ^ 3` on the funnel. -/
private lemma qpow6_le {z : ℍ} (hz : 2 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  have h1 : ‖Work.Kernels.qParamFun z‖ ^ (5 + 1) ≤ ‖Work.Kernels.qParamFun z‖ ^ 5 :=
    qpow_step hz 5
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ (4 + 1) ≤ ‖Work.Kernels.qParamFun z‖ ^ 4 :=
    qpow_step hz 4
  have h3 : ‖Work.Kernels.qParamFun z‖ ^ (3 + 1) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    qpow_step hz 3
  norm_num at h1 h2 h3
  linarith

private lemma dE8_fourth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 2 ≤ z.im →
    ‖Work.Asymptotics.Compact.dE8 z - 61920 * (Work.Kernels.qParamFun z) ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C4, hC4, h4⟩ := e4ThreeTerm
  refine ⟨C4 * (4802 + C4) + 5702400 + 1, by positivity, fun z hz => ?_⟩
  have h1 : 1 ≤ z.im := by linarith
  have hq1 := q_norm_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hR : ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
      - 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h4 z h1
  have hd : Work.Asymptotics.Compact.dE8 z
      = Work.Kernels.E4Fun z ^ 2 - (1 + 480 * Work.Kernels.qParamFun z) := by
    simp only [Work.Asymptotics.Compact.dE8, Work.Asymptotics.Compact.E8ref, Work.Kernels.E8Fun]
    rw [← q_eq_Ept_sq z]
  set R : ℂ := Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
      - 2160 * Work.Kernels.qParamFun z ^ 2 with hRdef
  have hR' : ‖R‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by rw [hRdef]; exact hR
  have hkey : Work.Asymptotics.Compact.dE8 z - 61920 * (Work.Kernels.qParamFun z) ^ 2
      = R * (2 * (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2) + R)
        + (1036800 * (Work.Kernels.qParamFun z) ^ 3
            + 4665600 * (Work.Kernels.qParamFun z) ^ 4) := by
    rw [hd, hRdef]
    ring
  rw [hkey]
  have hAp : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ 2401 := by
    have h2 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
        ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_ofNat]
    have h3 : ‖(2160 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
        = 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h4' := norm_add_le ((1 : ℂ) + 240 * Work.Kernels.qParamFun z)
      (2160 * Work.Kernels.qParamFun z ^ 2)
    rw [h3] at h4'
    nlinarith [h2, h4', hq0, hq1]
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    qpow_step hz 3
  have hmid : ‖2 * (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
      + R‖ ≤ 2 * 2401 + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h5 : ‖2 * (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2)‖ ≤ 2 * 2401 := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left hAp (by norm_num)
    have h6 := norm_add_le (2 * (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2)) R
    linarith
  have hmain : ‖R * (2 * (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2) + R)
      + (1036800 * (Work.Kernels.qParamFun z) ^ 3
          + 4665600 * (Work.Kernels.qParamFun z) ^ 4)‖
      ≤ (C4 * (4802 + C4) + 5702400) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h7 : ‖R * (2 * (1 + 240 * Work.Kernels.qParamFun z
        + 2160 * Work.Kernels.qParamFun z ^ 2) + R)‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (2 * 2401
            + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul hR' hmid (norm_nonneg _) (by positivity)
    have h8 : ‖(1036800 : ℂ) * (Work.Kernels.qParamFun z) ^ 3
        + 4665600 * (Work.Kernels.qParamFun z) ^ 4‖
        ≤ 1036800 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 4665600 * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
    have h9 := norm_add_le (R * (2 * (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2) + R))
      (1036800 * (Work.Kernels.qParamFun z) ^ 3
        + 4665600 * (Work.Kernels.qParamFun z) ^ 4)
    have hq6 : ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
      qpow6_le hz
    have hprod : C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        ≤ C4 * C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      calc C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
          = C4 * C4 * (‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
            ring
        _ = C4 * C4 * ‖Work.Kernels.qParamFun z‖ ^ 6 := by ring
        _ ≤ C4 * C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hq6 (by positivity)
    calc ‖R * (2 * (1 + 240 * Work.Kernels.qParamFun z
          + 2160 * Work.Kernels.qParamFun z ^ 2) + R)
        + (1036800 * (Work.Kernels.qParamFun z) ^ 3
            + 4665600 * (Work.Kernels.qParamFun z) ^ 4)‖
        ≤ ‖R * (2 * (1 + 240 * Work.Kernels.qParamFun z
            + 2160 * Work.Kernels.qParamFun z ^ 2) + R)‖
          + ‖(1036800 : ℂ) * (Work.Kernels.qParamFun z) ^ 3
            + 4665600 * (Work.Kernels.qParamFun z) ^ 4‖ := h9
      _ ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (2 * 2401
            + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
          + (1036800 * ‖Work.Kernels.qParamFun z‖ ^ 3
            + 4665600 * ‖Work.Kernels.qParamFun z‖ ^ 4) := add_le_add h7 h8
      _ ≤ (C4 * (4802 + C4) + 5702400) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          have e1 : (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (2 * 2401
              + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
              ≤ (C4 * 4802 + C4 * C4) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
            calc (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (2 * 2401
                  + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)
                = C4 * 4802 * ‖Work.Kernels.qParamFun z‖ ^ 3
                  + C4 * ‖Work.Kernels.qParamFun z‖ ^ 3
                    * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by ring
              _ ≤ C4 * 4802 * ‖Work.Kernels.qParamFun z‖ ^ 3
                  + C4 * C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := add_le_add le_rfl hprod
              _ = (C4 * 4802 + C4 * C4) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
          have e2 : 1036800 * ‖Work.Kernels.qParamFun z‖ ^ 3
              + 4665600 * ‖Work.Kernels.qParamFun z‖ ^ 4
              ≤ 5702400 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
            have := mul_le_mul_of_nonneg_left hq4 (by norm_num : (0:ℝ) ≤ 4665600)
            linarith
          linarith [e1, e2, pow_nonneg hq0 3]
  exact le_trans hmain (by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0 3)
    linarith)

private lemma dE6_fourth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 2 ≤ z.im →
    ‖Work.Asymptotics.Compact.dE6 z + 16632 * (Work.Kernels.qParamFun z) ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C6, hC6, h6⟩ := e6ThreeTerm
  refine ⟨C6, hC6, fun z hz => ?_⟩
  have h1 : 1 ≤ z.im := by linarith
  have hd : Work.Asymptotics.Compact.dE6 z + 16632 * (Work.Kernels.qParamFun z) ^ 2
      = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
        + 16632 * Work.Kernels.qParamFun z ^ 2 := by
    simp only [Work.Asymptotics.Compact.dE6, Work.Asymptotics.Compact.E6ref]
    rw [← q_eq_Ept_sq z]
    ring
  rw [hd]
  exact h6 z h1

private lemma dE10_fourth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 2 ≤ z.im →
    ‖Work.Asymptotics.Compact.dE10 z + 135432 * (Work.Kernels.qParamFun z) ^ 2‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C4, hC4, h4⟩ := e4ThreeTerm
  obtain ⟨C6, hC6, h6⟩ := e6ThreeTerm
  refine ⟨C4 * 17137 + C6 * 2401 + C4 * C6 + (5080320 + 35925120) + 1,
    by positivity, fun z hz => ?_⟩
  have h1 : 1 ≤ z.im := by linarith
  have hq1 := q_norm_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq6 : ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    qpow6_le hz
  have hR4 : ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
      - 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h4 z h1
  have hR6 : ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
      + 16632 * Work.Kernels.qParamFun z ^ 2‖ ≤ C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h6 z h1
  have hd : Work.Asymptotics.Compact.dE10 z + 135432 * (Work.Kernels.qParamFun z) ^ 2
      = (Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)
        + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2))
        + (-((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
            - 35925120 * (Work.Kernels.qParamFun z) ^ 4) := by
    simp only [Work.Asymptotics.Compact.dE10, Work.Asymptotics.Compact.E10ref,
      Work.Kernels.E10Fun]
    rw [← q_eq_Ept_sq z]
    ring
  rw [hd]
  have hB : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z
      - 16632 * Work.Kernels.qParamFun z ^ 2‖ ≤ 17137 := by
    have h2 : ‖(1 : ℂ) - 504 * Work.Kernels.qParamFun z‖
        ≤ 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_ofNat]
    have h3 : ‖(16632 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
        = 16632 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h4' := norm_sub_le ((1 : ℂ) - 504 * Work.Kernels.qParamFun z)
      (16632 * Work.Kernels.qParamFun z ^ 2)
    rw [h3] at h4'
    nlinarith [h2, h4', hq0, hq1]
  have hA : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z
      + 2160 * Work.Kernels.qParamFun z ^ 2‖ ≤ 2401 := by
    have h2 : ‖(1 : ℂ) + 240 * Work.Kernels.qParamFun z‖
        ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_one, norm_mul, Complex.norm_ofNat]
    have h3 : ‖(2160 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
        = 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h4' := norm_add_le ((1 : ℂ) + 240 * Work.Kernels.qParamFun z)
      (2160 * Work.Kernels.qParamFun z ^ 2)
    rw [h3] at h4'
    nlinarith [h2, h4', hq0, hq1]
  have h8 : ‖-((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
      - 35925120 * (Work.Kernels.qParamFun z) ^ 4‖
      ≤ 5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
        + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
    rw [show -((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
        - 35925120 * (Work.Kernels.qParamFun z) ^ 4
        = -((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3
            + 35925120 * (Work.Kernels.qParamFun z) ^ 4) by ring, norm_neg]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
  have hq4 : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    qpow_step hz 3
  have hstep : ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)
        + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2))‖
      ≤ (C4 * 17137 + C6 * 2401 + C4 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have e1 : ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * 17137 := by
      rw [norm_mul]
      exact mul_le_mul hR4 hB (norm_nonneg _) (by positivity)
    have e2 : ‖(1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2)‖
        ≤ 2401 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul hA hR6 (norm_nonneg _) (by positivity)
    have e3 : ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2)‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul hR4 hR6 (norm_nonneg _) (by positivity)
    have h12 := norm_add_le ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2))
      ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2))
    have h34 := norm_add_le ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2))
      ((1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2))
    have hprod : C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3)
        ≤ C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      calc C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3)
          = C4 * C6 * (‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
            ring
        _ = C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 6 := by ring
        _ ≤ C4 * C6 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hq6 (by positivity)
    calc ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)
        + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2))‖
        ≤ ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
            + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
              * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
                  + 16632 * Work.Kernels.qParamFun z ^ 2)‖
          + ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)‖ := h12
      _ ≤ ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)‖
          + ‖(1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
              * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
                  + 16632 * Work.Kernels.qParamFun z ^ 2)‖
          + ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)‖ := add_le_add h34 le_rfl
      _ ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * 17137
          + 2401 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3)
          + (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
          add_le_add (add_le_add e1 e2) e3
      _ ≤ (C4 * 17137 + C6 * 2401 + C4 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          have hp2 := hprod
          nlinarith [hp2, pow_nonneg hq0 3]
  have hsum := norm_add_le ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
        - 2160 * Work.Kernels.qParamFun z ^ 2)
      * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
      + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2)
      + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2)))
    (-((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
      - 35925120 * (Work.Kernels.qParamFun z) ^ 4)
  have h429 : 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4
      ≤ 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    mul_le_mul_of_nonneg_left hq4 (by norm_num)
  have h3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := pow_nonneg hq0 3
  have hY : 5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
      + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4
      ≤ (41005440 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    calc 5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4
        ≤ 5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 3 := add_le_add le_rfl h429
      _ = 41005440 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
      _ ≤ (41005440 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          nlinarith [h3]
  calc ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * Work.Kernels.qParamFun z ^ 2)
        * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
      + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
        * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2)
      + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
            + 16632 * Work.Kernels.qParamFun z ^ 2))
      + (-((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
          - 35925120 * (Work.Kernels.qParamFun z) ^ 4)‖
      ≤ ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
            - 2160 * Work.Kernels.qParamFun z ^ 2)
          * (1 - 504 * Work.Kernels.qParamFun z - 16632 * Work.Kernels.qParamFun z ^ 2)
        + (1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2)
          * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2)
        + ((Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
              - 2160 * Work.Kernels.qParamFun z ^ 2)
            * (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
              + 16632 * Work.Kernels.qParamFun z ^ 2))‖
        + ‖-((5080320 : ℂ) * (Work.Kernels.qParamFun z) ^ 3)
            - 35925120 * (Work.Kernels.qParamFun z) ^ 4‖ := hsum
    _ ≤ (C4 * 17137 + C6 * 2401 + C4 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3
        + (5080320 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 35925120 * ‖Work.Kernels.qParamFun z‖ ^ 4) := add_le_add hstep h8
    _ ≤ (C4 * 17137 + C6 * 2401 + C4 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3
        + (41005440 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 := add_le_add le_rfl hY
    _ = (C4 * 17137 + C6 * 2401 + C4 * C6 + (41005440 + 1))
        * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
    _ ≤ (C4 * 17137 + C6 * 2401 + C4 * C6 + (5080320 + 35925120) + 1)
        * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ h3
        linarith

/-- **The second-order deviations of `E₈`, `E₆`, `E₁₀` at the cusp.** -/
theorem zAtomDevEisensteinFourthOrder :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, 2 ≤ z.im →
        ‖Work.Asymptotics.Compact.dE8 z - 61920 * (Work.Kernels.qParamFun z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (∀ z : UpperHalfPlane, 2 ≤ z.im →
        ‖Work.Asymptotics.Compact.dE6 z + 16632 * (Work.Kernels.qParamFun z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (∀ z : UpperHalfPlane, 2 ≤ z.im →
        ‖Work.Asymptotics.Compact.dE10 z + 135432 * (Work.Kernels.qParamFun z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
  obtain ⟨C8, hC8, h8⟩ := dE8_fourth
  obtain ⟨C6, hC6, h6⟩ := dE6_fourth
  obtain ⟨C10, hC10, h10⟩ := dE10_fourth
  refine ⟨max (max C8 C6) C10, lt_of_lt_of_le hC8 (le_trans (le_max_left C8 C6)
    (le_max_left (max C8 C6) C10)), ?_, ?_, ?_⟩
  · intro z hz
    refine le_trans (h8 z hz) ?_
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C8 C6)
      (le_max_left (max C8 C6) C10)) (by positivity)
  · intro z hz
    refine le_trans (h6 z hz) ?_
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C8 C6)
      (le_max_left (max C8 C6) C10)) (by positivity)
  · intro z hz
    refine le_trans (h10 z hz) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right (max C8 C6) C10) (by positivity)

end

end Work.Asymptotics.KhatE1Core
