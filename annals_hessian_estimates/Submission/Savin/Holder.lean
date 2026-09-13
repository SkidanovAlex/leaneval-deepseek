/-
# The Holder estimate for the sigma-2 perturbation equation (Savin's Corollary 3.3)

The oscillation decay `Submission.Savin.Oscillation.oscillation_decay` says that on a ball of
radius `R` on which the oscillation of `Φ` is small compared with `R ^ 2`, the oscillation on the
half ball loses a fixed proportion `δ > 0`.  Iterating this at the geometrically decreasing scales
`R_s = 2^{-s}` produces Savin's Holder estimate

  `osc_{B_{2^{-(s+1)}}} Φ ≤ (1 - δ)^s osc_{B_1} Φ`   for `s ≤ k`,

for a solution `Φ` of `s2 (A + D²Φ) = 1` (positive branch) whose oscillation on `B_1` is smaller
than `c₁ 2^{-2k}`.  The smallness at each intermediate scale is automatic because the decay is
(strictly) faster than the geometric shrinking of `R_s ^ 2`.

The iteration is carried out with the *pointwise* diametral inequality, so that the open-ball
hypotheses of `oscillation_decay` and the compactness of the closed balls are used directly and no
`sSup`/`sInf` over an open ball is needed: at each step the maximum and the minimum of `Φ` on the
current closed ball furnish the two bounds required by `oscillation_decay`, and their difference is
controlled by the diametral inequality produced at the previous step.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Oscillation

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **Savin's Corollary 3.3 (Holder estimate).**  There is a universal constant `c₁ > 0` and a
universal decay factor `δ ∈ (0,1)` such that every `C²` solution `Φ` of `s2 (A + D²Φ) = 1` on the
positive branch in `B_1`, with `m₀ ≤ Φ ≤ M₀` and `M₀ - m₀ ≤ c₁ 2^{-2k}` there, satisfies the
diametral Holder-type bound

  `Φ x - Φ y ≤ (1 - δ)^s (M₀ - m₀)`   for all `x, y ∈ closedBall 0 (2^{-(s+1)})`, `s ≤ k`. -/
theorem holder_estimate_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c')
    (hYnn : 0 ≤ Y) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ c₁ δ : ℝ, 0 < c₁ ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
        (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
        (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
        (hYb : 2 * trOp (cofOp A) / c ≤ Y)
        (Φ : ℝ⁴ → ℝ) (k : ℕ) (m₀ M₀ : ℝ),
        ContDiffOn ℝ 2 Φ (ball 0 1) →
        (∀ x ∈ ball 0 1, s2 (A + hessOp Φ x) = 1) →
        (∀ x ∈ ball 0 1, 0 < trOp (A + hessOp Φ x)) →
        (∀ x ∈ ball 0 1, m₀ ≤ Φ x) → (∀ x ∈ ball 0 1, Φ x ≤ M₀) →
        M₀ - m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) →
        ∀ s ≤ k, ∀ x ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
          ∀ y ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
            Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
  obtain ⟨δ, hδpos, hδlt, hdec⟩ :=
    oscillation_decay_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  have hMpos : 0 < M := by linarith
  have h2p4 : (0 : ℝ) < 2 ^ (2 * p + 4) := Real.rpow_pos_of_pos (by norm_num) (2 * p + 4)
  have hD1 : (0 : ℝ) < 25 * 768 * 2 ^ (2 * p + 4) := by positivity
  have hD2 : (0 : ℝ) < 25 * 1536 * M := by positivity
  set c₁ : ℝ := min (c / (25 * 768 * 2 ^ (2 * p + 4))) (c / (25 * 1536 * M)) with hc₁def
  have hc1a : c₁ ≤ c / (25 * 768 * 2 ^ (2 * p + 4)) := by
    rw [hc₁def]; exact min_le_left _ _
  have hc1b : c₁ ≤ c / (25 * 1536 * M) := by
    rw [hc₁def]; exact min_le_right _ _
  have hc1pos : 0 < c₁ := by
    rw [hc₁def]; exact lt_min (div_pos hc hD1) (div_pos hc hD2)
  refine ⟨c₁, δ, hc1pos, hδpos, hδlt, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ k m₀ M₀ hΦ heq hpos hlow hup hosc
  -- basic facts
  have hdelta : (0 : ℝ) ≤ 1 - δ := by linarith
  have h0ball : (0 : ℝ⁴) ∈ ball 0 1 := by
    rw [mem_ball, dist_self]; norm_num
  have hosc_nonneg : 0 ≤ M₀ - m₀ := by
    have h1 := hlow 0 h0ball; have h2 := hup 0 h0ball; linarith
  -- the geometric comparison of `(1/2) ^ (2 * k)` with the scale `s`
  have hpow_le : ∀ s, s + 1 ≤ k → (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ (2 * (s + 1)) := by
    intro s hs
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hosc_le : ∀ s, s + 1 ≤ k → M₀ - m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * (s + 1)) := by
    intro s hs
    calc M₀ - m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) := hosc
      _ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * (s + 1)) :=
          mul_le_mul_of_nonneg_left (hpow_le s hs) (le_of_lt hc1pos)
  have hrad_sq : ∀ s : ℕ, ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 = (1 / 2 : ℝ) ^ (2 * (s + 1)) := by
    intro s
    rw [← pow_mul]
    congr 1
    rw [Nat.mul_comm]
  -- the two coefficient estimates
  have hcoef1 : 768 * c₁ * 2 ^ (2 * p + 4) ≤ c / 25 := by
    have h := (le_div_iff₀ hD1).mp hc1a
    have h' : c₁ * (25 * 768 * 2 ^ (2 * p + 4)) / 25 ≤ c / 25 :=
      div_le_div_of_nonneg_right h (by norm_num)
    have heq : c₁ * (25 * 768 * 2 ^ (2 * p + 4)) / 25 = 768 * c₁ * 2 ^ (2 * p + 4) := by
      field_simp
    linarith [h', heq.le, heq.ge]
  have hcoef2 : 1536 * c₁ * M ≤ c / 25 := by
    have h := (le_div_iff₀ hD2).mp hc1b
    have h' : c₁ * (25 * 1536 * M) / 25 ≤ c / 25 :=
      div_le_div_of_nonneg_right h (by norm_num)
    have heq : c₁ * (25 * 1536 * M) / 25 = 1536 * c₁ * M := by
      field_simp
    linarith [h', heq.le, heq.ge]
  -- the main iteration
  have key : ∀ s, s ≤ k → ∀ x ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)),
      ∀ y ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)),
        Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
    intro s
    induction s with
    | zero =>
      intro _ x hx y hy
      simp only [pow_zero, one_mul]
      have hsub : closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (0 + 1)) ⊆ ball 0 1 :=
        closedBall_subset_ball (by norm_num)
      have h1 := hup x (hsub hx)
      have h2 := hlow y (hsub hy)
      linarith
    | succ s ih =>
      intro hs x hx y hy
      -- the current scale
      have hradpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (s + 1) := pow_pos (by norm_num) _
      have hradlt1 : (1 / 2 : ℝ) ^ (s + 1) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have hrad_eq : (1 / 2 : ℝ) ^ ((s + 1) + 1) = (1 / 2 : ℝ) ^ (s + 1) / 2 := by
        rw [pow_succ]; ring
      have hclosed_sub : closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)) ⊆ ball 0 1 :=
        closedBall_subset_ball hradlt1
      have hball_sub : ball (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)) ⊆ ball 0 1 :=
        ball_subset_ball (le_of_lt hradlt1)
      -- the maximum and the minimum of `Φ` on the current closed ball
      have hcont : ContinuousOn Φ (closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1))) :=
        hΦ.continuousOn.mono hclosed_sub
      have hne : (closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1))).Nonempty :=
        ⟨0, by rw [mem_closedBall, dist_self]; exact le_of_lt hradpos⟩
      obtain ⟨xm, hxm_mem, hxm_max⟩ :=
        (isCompact_closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1))).exists_isMaxOn hne hcont
      obtain ⟨ym, hym_mem, hym_min⟩ :=
        (isCompact_closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1))).exists_isMinOn hne hcont
      have hMm : Φ xm - Φ ym ≤ (1 - δ) ^ s * (M₀ - m₀) :=
        ih (by omega) xm hxm_mem ym hym_mem
      -- the smallness hypotheses at the current scale
      have hLbound : Φ xm - Φ ym ≤ c₁ * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 := by
        rw [hrad_sq s]
        calc Φ xm - Φ ym ≤ (1 - δ) ^ s * (M₀ - m₀) := hMm
          _ ≤ M₀ - m₀ := by
              have h1 : (1 - δ) ^ s ≤ 1 := pow_le_one₀ hdelta (by linarith)
              nlinarith [h1, hosc_nonneg]
          _ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * (s + 1)) := hosc_le s hs
      have hsc1 : 768 * (Φ xm - Φ ym) * 2 ^ (2 * p + 4)
          ≤ c * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 / 25 := by
        calc 768 * (Φ xm - Φ ym) * 2 ^ (2 * p + 4)
            ≤ 768 * (c₁ * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2) * 2 ^ (2 * p + 4) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hLbound (by norm_num)) (le_of_lt h2p4)
          _ = ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 * (768 * c₁ * 2 ^ (2 * p + 4)) := by ring
          _ ≤ ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 * (c / 25) :=
              mul_le_mul_of_nonneg_left hcoef1 (by positivity)
          _ = c * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 / 25 := by ring
      have hsc2 : 1536 * (Φ xm - Φ ym) * M
          ≤ c * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 / 25 := by
        calc 1536 * (Φ xm - Φ ym) * M
            ≤ 1536 * (c₁ * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2) * M :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hLbound (by norm_num)) (le_of_lt hMpos)
          _ = ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 * (1536 * c₁ * M) := by ring
          _ ≤ ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 * (c / 25) :=
              mul_le_mul_of_nonneg_left hcoef2 (by positivity)
          _ = c * ((1 / 2 : ℝ) ^ (s + 1)) ^ 2 / 25 := by ring
      -- the decay step
      have hdec' := hdec A hA hA1 htrA hcq hcq' hYb Φ ((1 / 2 : ℝ) ^ (s + 1)) (Φ ym) (Φ xm) hradpos
        (hΦ.mono hball_sub) (fun z hz => heq z (hball_sub hz))
        (fun z hz => hpos z (hball_sub hz))
        (fun z hz => hym_min (ball_subset_closedBall hz))
        (fun z hz => hxm_max (ball_subset_closedBall hz)) hsc1 hsc2
      have hx' : x ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1) / 2) := by
        rw [← hrad_eq]; exact hx
      have hy' : y ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1) / 2) := by
        rw [← hrad_eq]; exact hy
      have h1 := hdec' x hx' y hy'
      have h2 : (1 - δ) * (Φ xm - Φ ym) ≤ (1 - δ) ^ (s + 1) * (M₀ - m₀) := by
        have h3 : (1 - δ) * ((1 - δ) ^ s * (M₀ - m₀))
            = (1 - δ) ^ (s + 1) * (M₀ - m₀) := by
          rw [pow_succ]; ring
        calc (1 - δ) * (Φ xm - Φ ym) ≤ (1 - δ) * ((1 - δ) ^ s * (M₀ - m₀)) :=
              mul_le_mul_of_nonneg_left hMm hdelta
          _ = (1 - δ) ^ (s + 1) * (M₀ - m₀) := h3
      linarith [h1, h2]
  exact key

/-- **Savin's Corollary 3.3 (Holder estimate).**  There is a universal constant `c₁ > 0` and a
universal decay factor `δ ∈ (0,1)` such that every `C²` solution `Φ` of `s2 (A + D²Φ) = 1` on the
positive branch in `B_1`, with `m₀ ≤ Φ ≤ M₀` and `M₀ - m₀ ≤ c₁ 2^{-2k}` there, satisfies the
diametral Holder-type bound

  `Φ x - Φ y ≤ (1 - δ)^s (M₀ - m₀)`   for all `x, y ∈ closedBall 0 (2^{-(s+1)})`, `s ≤ k`. -/
theorem holder_estimate {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ c₁ δ : ℝ, 0 < c₁ ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (Φ : ℝ⁴ → ℝ) (k : ℕ) (m₀ M₀ : ℝ),
        ContDiffOn ℝ 2 Φ (ball 0 1) →
        (∀ x ∈ ball 0 1, s2 (A + hessOp Φ x) = 1) →
        (∀ x ∈ ball 0 1, 0 < trOp (A + hessOp Φ x)) →
        (∀ x ∈ ball 0 1, m₀ ≤ Φ x) → (∀ x ∈ ball 0 1, Φ x ≤ M₀) →
        M₀ - m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) →
        ∀ s ≤ k, ∀ x ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
          ∀ y ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
            Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
  obtain ⟨hc'pos, hYnn⟩ := harnack_base_data hc hcq hcq'
  obtain ⟨c₁, δ, h1, h2, h3, h4⟩ :=
    holder_estimate_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨c₁, δ, h1, h2, h3, h4 A hA hA1 htrA hcq hcq' le_rfl⟩

end

end Submission
