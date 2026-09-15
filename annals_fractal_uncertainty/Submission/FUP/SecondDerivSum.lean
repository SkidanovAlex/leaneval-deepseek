import Submission.FUP.ModifyWeightCancellation
import Submission.FUP.GrowthSum
import Submission.Commons.Measure.EuclideanSpace.volume_line_ball
import Submission.Commons.Analysis.Calculus.norm_iteratedFDeriv_two_sub_le

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, VIII: the second-derivative estimate over lines

This module proves the estimate `eq:estimate_second_deriv_line_tilde_omega_k_sum` of Cohen's
paper: for any line `ℓ = {x₀ + t ŷ}` (with `x₀` the closest point of `ℓ` to the origin) and any
unit `v̂ ⊥ ŷ`,

  `∑_k |∫_ℝ ⟨(D²ω̃_k(x₀ + tŷ))v̂, v̂⟩ dt| ≲ C_reg + C_gr`.

The three regimes of the paper are

* `2^{k+1} < ‖x₀‖`: the support annulus of `ω̃_k` misses the line, so the integral vanishes;
* `k ≥ m₀` (where `2^{m₀+1} ≥ ‖x₀‖`): translate the integral to the parallel line through the
  origin, where the *design* of the correction `g_k` gives the exact value `2 q_k`
  (`ModifyWeightCancellation.integral_iteratedFDeriv_two_omegaTildePiece`), and bound the
  translation error by the third-derivative bound.

Summing, `∑_k 2|q_k| ≤ 256 C_gr` (`GrowthSum.sum_abs_qk_le_growth`) and
`∑_{k ≥ m₀} ‖x₀‖ 2^{-k} ≤ 4` give the claim.

## Contents

* `gkConst`, `tildeConst` — the constants in `‖D^a ω̃_k‖ ≤ C_reg·C̃ 2^{(1-a)k}`;
* `norm_iteratedFDeriv_omegaTildePiece_le` — that bound, for all `x` and `a ≤ 3`;
* `norm_iteratedFDeriv_two_sub_le_omegaTildePiece` — its third-derivative consequence
  `‖D²ω̃_k z₁ - D²ω̃_k z₂‖ ≤ C_reg C̃ 2^{-2k} ‖z₁ - z₂‖`;
* `integral_eq_zero_of_norm_lt` — regime 1;
* `abs_integral_sub_le` — the translation estimate (regime 3);
* `sum_abs_integral_second_deriv_le` — the main estimate.
-/

/-! ## 1. The uniform constant of the modified pieces -/

/-- The constant in the derivative estimate for the correction `g_k`, obtained from
`norm_iteratedFDeriv_gk_le_Creg` by replacing `2^a` (`a ≤ 3`) by `8`. -/
noncomputable def gkConst (d : ℕ) : ℝ :=
  (2 * pkConst)⁻¹ * rpsCps d * 512000 * 8 * invNormConst d * pieceConst d

lemma gkConst_nonneg (d : ℕ) : 0 ≤ gkConst d := by
  have h1 := pkConst_pos
  have h2 := rpsCps_pos d
  have h3 := invNormConst_pos d
  have h4 := pieceConst_pos d
  rw [gkConst]
  positivity

/-- The uniform constant `C̃ = C_p + C_g` in the estimate
`‖D^a ω̃_k(x)‖ ≤ C_reg·C̃·2^{(1-a)k}` for `a ≤ 3`. -/
noncomputable def tildeConst (d : ℕ) : ℝ := pieceConst d + gkConst d

lemma tildeConst_pos (d : ℕ) : 0 < tildeConst d := by
  have := pieceConst_pos d
  have := gkConst_nonneg d
  rw [tildeConst]; linarith

lemma pieceConst_le_tildeConst (d : ℕ) : pieceConst d ≤ tildeConst d := by
  have := gkConst_nonneg d
  rw [tildeConst]; linarith

lemma gkConst_le_tildeConst (d : ℕ) : gkConst d ≤ tildeConst d := by
  have := pieceConst_pos d
  rw [tildeConst]; linarith

lemma tildeConst_nonneg (d : ℕ) : 0 ≤ tildeConst d := (tildeConst_pos d).le

/-! ## 2. The uniform derivative bound for the modified pieces -/

/-- Arithmetic: `2^{k}/4 < 2^{k-1}` for `k ≥ 1`. -/
lemma pow_div_four_lt (k : ℕ) (hk : 1 ≤ k) : (2 : ℝ) ^ k / 4 < (2 : ℝ) ^ (k - 1) := by
  have h1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
  rw [h1, div_lt_iff₀ (by norm_num : (0:ℝ) < 4)]
  linarith

/-- Arithmetic: `2^{k+1} < 4·2^{k}`. -/
lemma pow_succ_lt_four_mul (k : ℕ) : (2 : ℝ) ^ (k + 1) < 4 * (2 : ℝ) ^ k := by
  have h1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [h1]; linarith

/-- Outside the open annulus `annOpen k` the modified piece `ω̃_k` vanishes in a neighbourhood. -/
lemma omegaTildePiece_eventuallyEq_zero_of_notMem_annOpen (k : ℕ) (hk1 : 1 ≤ k)
    (w : ℝᵈ → ℝ) {x : ℝᵈ} (hx : x ∉ annOpen (d := d) k) :
    omegaTildePiece (d := d) k w =ᶠ[𝓝 x] 0 := by
  rw [annOpen, Set.mem_ofPred_eq, not_and_or, not_lt, not_lt] at hx
  rcases hx with hlo | hhi
  · have hlt : ‖x‖ < (2 : ℝ) ^ (k - 1) := lt_of_le_of_lt hlo (pow_div_four_lt k hk1)
    have hmem : Metric.ball x ((2 : ℝ) ^ (k - 1) - ‖x‖) ∈ 𝓝 x :=
      Metric.ball_mem_nhds x (sub_pos.mpr hlt)
    filter_upwards [hmem] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    linarith
  · have hlt : (2 : ℝ) ^ (k + 1) < ‖x‖ := lt_of_lt_of_le (pow_succ_lt_four_mul k) hhi
    have hmem : Metric.ball x (‖x‖ - (2 : ℝ) ^ (k + 1)) ∈ 𝓝 x :=
      Metric.ball_mem_nhds x (sub_pos.mpr hlt)
    filter_upwards [hmem] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt ?_)
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    rw [norm_sub_rev x y] at h1
    linarith

/-- **The uniform derivative bound for the modified pieces.**  For `k ≥ 1`, `a ≤ 3` and all
`x : ℝᵈ`, `‖D^a ω̃_k(x)‖ ≤ C_reg · C̃ · 2^{(1-a)k}`. -/
theorem norm_iteratedFDeriv_omegaTildePiece_le (hd : 1 ≤ d) (k a : ℕ) (ha : a ≤ 3) (hk1 : 1 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ a (omegaTildePiece (d := d) k w) x‖
      ≤ Creg * tildeConst d * (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ)) := by
  set P : ℝ := (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ)) with hP
  have hPnn : 0 ≤ P := Real.rpow_nonneg (by norm_num) _
  by_cases hx : x ∈ annOpen (d := d) k
  · rcases lt_or_ge k 2 with hk2 | hk2
    · -- `k < 2`: the piece is `ω_k`, whose bound holds everywhere
      have h := omegaPiece_iteratedFDeriv_le (d := d) k a ha hCreg hw hwzero hwbound x
      have heq : omegaTildePiece (d := d) k w = omegaPiece k w :=
        funext (omegaTildePiece_of_lt k w hk2)
      rw [heq]
      refine le_trans h ?_
      rw [show (2 : ℝ) ^ ((k : ℝ) * (1 - (a : ℝ))) = P from by
        simp only [hP]; rw [mul_comm]]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pieceConst_le_tildeConst d) hCreg.le) hPnn
    · -- `k ≥ 2`: bound `ω_k` and `g_k` separately
      have hk1' : 1 ≤ k := hk1
      have hpiece := omegaPiece_iteratedFDeriv_le (d := d) k a ha hCreg hw hwzero hwbound x
      have hg := norm_iteratedFDeriv_gk_le_Creg (d := d) hd k a ha hk1' hw hwzero
        hCreg hwbound hx
      have hpow : (2 : ℝ) ^ a ≤ 8 := by
        calc (2 : ℝ) ^ a ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) ha
          _ = 8 := by norm_num
      have hpowk : (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹
          = (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ)) := by
        have h := inv_mul_rpow_one_sub k a
        have h2 : (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ))
            = (2 : ℝ) ^ ((k : ℝ) * (1 - (a : ℝ))) := by rw [mul_comm]
        rw [h2, ← h, mul_comm]
        field_simp
      have hgk : ‖iteratedFDeriv ℝ a (gk k w) x‖ ≤ Creg * gkConst d * P := by
        refine le_trans hg ?_
        have hconst_nonneg : (0 : ℝ) ≤ (2 * pkConst)⁻¹ * rpsCps d * 512000
            * invNormConst d * Creg * pieceConst d := by
          have h1 := pkConst_pos; have h2 := rpsCps_pos d
          have h3 := invNormConst_pos d; have h4 := pieceConst_pos d
          positivity
        rw [hP]
        calc (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 ^ a * invNormConst d * Creg
              * pieceConst d * (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹
            = ((2 * pkConst)⁻¹ * rpsCps d * 512000 * invNormConst d * Creg * pieceConst d)
              * ((2 : ℝ) ^ a
                * ((2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹)) := by ring
          _ ≤ ((2 * pkConst)⁻¹ * rpsCps d * 512000 * invNormConst d * Creg * pieceConst d)
              * (8 * (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ))) := by
                refine mul_le_mul_of_nonneg_left ?_ hconst_nonneg
                rw [hpowk]
                exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by norm_num) _)
          _ = Creg * gkConst d * (2 : ℝ) ^ ((1 - (a : ℝ)) * (k : ℝ)) := by
                rw [gkConst]; ring
      have hpiece' : ‖iteratedFDeriv ℝ a (omegaPiece k w) x‖ ≤ Creg * pieceConst d * P := by
        refine le_trans hpiece (le_of_eq ?_)
        simp only [hP]; rw [mul_comm ((k:ℝ)) (1 - (a:ℝ))]
      have hsum : ‖iteratedFDeriv ℝ a (omegaTildePiece (d := d) k w) x‖
          ≤ ‖iteratedFDeriv ℝ a (omegaPiece k w) x‖ + ‖iteratedFDeriv ℝ a (gk k w) x‖ := by
        have heq : omegaTildePiece (d := d) k w = omegaPiece k w + gk k w := by
          funext y; rw [omegaTildePiece_of_le k w hk2]; rfl
        rw [heq, iteratedFDeriv_add (contDiff_omegaPiece hw k ha)
          ((contDiff_gk k hk1' hw).of_le (by exact_mod_cast ha))]
        exact norm_add_le _ _
      refine le_trans hsum ?_
      calc ‖iteratedFDeriv ℝ a (omegaPiece k w) x‖ + ‖iteratedFDeriv ℝ a (gk k w) x‖
          ≤ Creg * pieceConst d * P + Creg * gkConst d * P := add_le_add hpiece' hgk
        _ = Creg * tildeConst d * P := by rw [tildeConst]; ring
  · have hev := omegaTildePiece_eventuallyEq_zero_of_notMem_annOpen k hk1 w hx
    have hzero : iteratedFDeriv ℝ a (omegaTildePiece (d := d) k w) x = 0 := by
      have h1 := (hev.iteratedFDeriv ℝ a).self_of_nhds
      rw [h1]; simp
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg hCreg.le (tildeConst_nonneg d)) hPnn

/-! ## 3. Arithmetic of the dyadic weights -/

/-- Arithmetic: `(2^{-k})^2 · 2^{k+3} = 8·2^{-k}` (as real powers). -/
lemma dyadic_weight_arith (k : ℕ) :
    (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ ((k : ℝ) + 3)
      = 8 * (2 : ℝ) ^ (-(k : ℝ)) := by
  have h8 : (8 : ℝ) = (2 : ℝ) ^ (((3 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; norm_num
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [h8]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Arithmetic: `2^{(1-3)k} = 2^{-k}·2^{-k}`. -/
lemma dyadic_rpow_three (k : ℕ) :
    (2 : ℝ) ^ (((1 : ℝ) - ((3 : ℕ) : ℝ)) * (k : ℝ))
      = (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Arithmetic: `∑_{j<N} 2^{-j} ≤ 2`. -/
lemma sum_range_inv_pow_two_le (N : ℕ) :
    (∑ j ∈ Finset.range N, ((2 : ℝ) ^ j)⁻¹) ≤ 2 := by
  have hx : ((1 / 2 : ℝ)) ≠ 1 := by norm_num
  have h : (∑ j ∈ Finset.range N, ((2 : ℝ) ^ j)⁻¹)
      = ∑ j ∈ Finset.range N, ((1 / 2 : ℝ)) ^ j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← inv_pow]
    congr 1
    norm_num
  rw [h, geom_sum_eq hx N]
  have hpos : (0 : ℝ) < ((1 / 2 : ℝ)) ^ N := by positivity
  have heq : (((1 / 2 : ℝ)) ^ N - 1) / ((1 / 2 : ℝ) - 1) = 2 * (1 - ((1 / 2 : ℝ)) ^ N) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- Arithmetic: `∑_{m ≤ k ≤ K} 2^{-k} ≤ 2·2^{-m}`. -/
lemma sum_Icc_inv_pow_two_le (m K : ℕ) :
    (∑ k ∈ Finset.Icc m K, ((2 : ℝ) ^ k)⁻¹) ≤ 2 * ((2 : ℝ) ^ m)⁻¹ := by
  have hI : Finset.Ico m (K + 1) = Finset.Icc m K := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hI, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ (m + k))⁻¹ = ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    intro k
    rw [pow_add, mul_inv_rev, mul_comm]
  simp only [hterm]
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (sum_range_inv_pow_two_le _) (by positivity))
    (le_of_eq ?_)
  ring

/-! ## 4. The modified pieces have Lipschitz second derivatives -/

/-- **The second derivatives of the modified pieces are Lipschitz**, with constant
`C_reg C̃ 2^{-2k}`: the third-derivative bound of `norm_iteratedFDeriv_omegaTildePiece_le`
together with `Commons.Analysis.Calculus.norm_iteratedFDeriv_two_sub_le`. -/
theorem norm_iteratedFDeriv_two_sub_le_omegaTildePiece (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (z₁ z₂ : ℝᵈ) :
    ‖iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z₁
        - iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) z₂‖
      ≤ Creg * tildeConst d * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))) * ‖z₁ - z₂‖ := by
  have h3 : ∀ z : ℝᵈ, ‖iteratedFDeriv ℝ 3 (omegaTildePiece (d := d) k w) z‖
      ≤ Creg * tildeConst d * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))) := by
    intro z
    have h := norm_iteratedFDeriv_omegaTildePiece_le (d := d) hd k 3 (by norm_num) hk1
      hw hwzero hCreg hwbound z
    refine le_trans h (le_of_eq ?_)
    rw [dyadic_rpow_three]
  exact Commons.Analysis.Calculus.norm_iteratedFDeriv_two_sub_le
    (contDiff_omegaTildePiece k hw hk1) h3 z₂ z₁

/-! ## 5. The integrand and the vanishing regime -/

/-- For `x₀ ⊥ y` with `‖y‖ = 1`, the line `{x₀ + t·y}` stays outside the ball of radius
`‖x₀‖`. -/
lemma norm_add_smul_ge_of_inner_eq_zero {x₀ y : ℝᵈ} (hy : ‖y‖ = 1)
    (hperp : inner ℝ x₀ y = 0) (t : ℝ) : ‖x₀‖ ≤ ‖x₀ + t • y‖ := by
  have h2 : ‖x₀ + t • y‖ ^ 2 = ‖x₀‖ ^ 2 + t ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hperp, mul_zero, mul_zero, add_zero, norm_smul,
      hy, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (x₀ + t • y), norm_nonneg x₀, sq_nonneg t]

/-- The integrand of the second-derivative estimate, as a function of `t`. -/
noncomputable def lineSecondDeriv (k : ℕ) (w : ℝᵈ → ℝ) (x y v : ℝᵈ) (t : ℝ) : ℝ :=
  (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (x + t • y)) (fun _ : Fin 2 => v)

lemma lineSecondDeriv_def (k : ℕ) (w : ℝᵈ → ℝ) (x y v : ℝᵈ) (t : ℝ) :
    lineSecondDeriv (d := d) k w x y v t
      = (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (x + t • y))
          (fun _ : Fin 2 => v) := rfl

/-- **Regime 1**: if the support annulus of `ω̃_k` misses the line, the integral vanishes. -/
lemma integral_lineSecondDeriv_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) (x₀ y v : ℝᵈ) (hy : ‖y‖ = 1)
    (hperp : inner ℝ x₀ y = 0) (hmiss : (2 : ℝ) ^ (k + 1) < ‖x₀‖) :
    (∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t) = 0 := by
  have hzero : (fun t : ℝ => lineSecondDeriv (d := d) k w x₀ y v t) = fun _ => 0 := by
    funext t
    rw [lineSecondDeriv_def,
      iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w
        (z := x₀ + t • y) (by linarith [norm_add_smul_ge_of_inner_eq_zero hy hperp t]) 2]
    simp
  rw [hzero, integral_zero]

/-! ## 6. The translation estimate -/

/-- The set of parameters `t` for which either the line through `x₀` or the line through the
origin meets the ball of radius `2^{k+1}`. -/
def lineParamSet (k : ℕ) (x₀ y : ℝᵈ) : Set ℝ :=
  {t : ℝ | ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ (k + 1)} ∪ {t : ℝ | |t| ≤ (2 : ℝ) ^ (k + 1)}

lemma measurableSet_lineParamSet (k : ℕ) (x₀ y : ℝᵈ) :
    MeasurableSet (lineParamSet (d := d) k x₀ y) := by
  rw [lineParamSet]
  exact (isClosed_le (continuous_const.add (continuous_id.smul continuous_const)).norm
      continuous_const).measurableSet.union
    ((isClosed_le (continuous_id : Continuous (fun t : ℝ => t)).abs continuous_const).measurableSet)

lemma volume_lineParamSet_le (k : ℕ) (x₀ y : ℝᵈ) (hy : ‖y‖ = 1) :
    volume (lineParamSet (d := d) k x₀ y) ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 3)) := by
  have h1 : volume {t : ℝ | ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ (k + 1)}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) := by
    have h := Commons.Measure.EuclideanSpace.volume_line_ball x₀ y hy ((2 : ℝ) ^ (k + 1))
    have : (2 : ℝ) * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 2) := by
      rw [pow_succ]; ring
    rwa [this] at h
  have h2 : volume {t : ℝ | |t| ≤ (2 : ℝ) ^ (k + 1)} ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) := by
    have hsub : {t : ℝ | |t| ≤ (2 : ℝ) ^ (k + 1)}
        ⊆ Set.Icc (-((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ (k + 1)) := by
      intro t ht
      rw [Set.mem_ofPred_eq, abs_le] at ht
      exact ⟨ht.1, ht.2⟩
    calc volume {t : ℝ | |t| ≤ (2 : ℝ) ^ (k + 1)}
        ≤ volume (Set.Icc (-((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ (k + 1))) := measure_mono hsub
      _ = ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) := by
          rw [Real.volume_Icc]
          congr 1
          ring
  calc volume (lineParamSet (d := d) k x₀ y)
      ≤ volume {t : ℝ | ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ (k + 1)}
        + volume {t : ℝ | |t| ≤ (2 : ℝ) ^ (k + 1)} := by
        rw [lineParamSet]
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) + ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) := add_le_add h1 h2
    _ = ENNReal.ofReal ((2 : ℝ) ^ (k + 3)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The translation estimate**: replacing the line `{x₀ + t·y}` by the parallel line through
the origin changes the second-derivative integral by at most `8 C_reg C̃ 2^{-k} ‖x₀‖`. -/
theorem abs_integral_lineSecondDeriv_sub_le (hd : 1 ≤ d) (k : ℕ) (hk2 : 2 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x₀ y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) :
    |(∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t)
        - (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t)|
      ≤ 8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ := by
  have hk1 : 1 ≤ k := by omega
  set F := omegaTildePiece (d := d) k w with hF
  have hFcd : ContDiff ℝ 3 F := contDiff_omegaTildePiece k hw hk1
  set g₁ : ℝ → ℝ := fun t => (iteratedFDeriv ℝ 2 F (x₀ + t • y)) (fun _ : Fin 2 => v) with hg₁
  set g₂ : ℝ → ℝ := fun t => (iteratedFDeriv ℝ 2 F (t • y)) (fun _ : Fin 2 => v) with hg₂
  have hc2 : Continuous (iteratedFDeriv ℝ 2 F) :=
    ContDiff.continuous_iteratedFDeriv (𝕜 := ℝ) (f := F) (n := (3 : ℕ∞ω)) (m := 2)
      (by norm_num) hFcd
  have hev : Continuous (fun z : ℝᵈ => (iteratedFDeriv ℝ 2 F z) (fun _ : Fin 2 => v)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝᵈ) ℝ (fun _ : Fin 2 => v)).continuous.comp
      hc2
  have hc1 : Continuous g₁ := hev.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hc₂ : Continuous g₂ := hev.comp (continuous_id.smul continuous_const)
  have hnorm' : ∀ t : ℝ, ‖t • y‖ = |t| := by
    intro t; rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
  -- compact supports
  have hcs1 : HasCompactSupport g₁ := by
    have hsub : tsupport g₁ ⊆
        Set.Icc (-((2 : ℝ) ^ (k + 1) + ‖x₀‖)) ((2 : ℝ) ^ (k + 1) + ‖x₀‖) := by
      rw [tsupport]
      refine closure_minimal ?_ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      have hle : ‖x₀ + t • y‖ ≤ (2 : ℝ) ^ (k + 1) := by
        by_contra hc
        push Not at hc
        exact ht (by
          show (iteratedFDeriv ℝ 2 F (x₀ + t • y)) (fun _ : Fin 2 => v) = 0
          rw [hF, iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w hc 2]
          simp)
      have hb : |t| ≤ (2 : ℝ) ^ (k + 1) + ‖x₀‖ := by
        rw [← hnorm' t]
        calc ‖t • y‖ = ‖(x₀ + t • y) - x₀‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖x₀ + t • y‖ + ‖x₀‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      exact Set.mem_Icc.mpr (abs_le.mp hb)
    exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub
  have hcs2 : HasCompactSupport g₂ := by
    have hsub : tsupport g₂ ⊆
        Set.Icc (-((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ (k + 1)) := by
      rw [tsupport]
      refine closure_minimal ?_ isClosed_Icc
      intro t ht
      rw [Function.mem_support] at ht
      have hle : ‖t • y‖ ≤ (2 : ℝ) ^ (k + 1) := by
        by_contra hc
        push Not at hc
        exact ht (by
          show (iteratedFDeriv ℝ 2 F (t • y)) (fun _ : Fin 2 => v) = 0
          rw [hF, iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w hc 2]
          simp)
      have hb : |t| ≤ (2 : ℝ) ^ (k + 1) := by rwa [hnorm' t] at hle
      exact Set.mem_Icc.mpr (abs_le.mp hb)
    exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub
  have hi1 : Integrable g₁ := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable g₂ := hc₂.integrable_of_hasCompactSupport hcs2
  -- integral bookkeeping
  have e1 : (∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t) = ∫ t : ℝ, g₁ t := by
    rw [hg₁, hF]; rfl
  have e2 : (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t) = ∫ t : ℝ, g₂ t := by
    rw [hg₂, hF]
    simp only [lineSecondDeriv_def, zero_add]
  rw [e1, e2]
  -- the pointwise bound
  set s := lineParamSet (d := d) k x₀ y with hs
  set C₀ : ℝ := Creg * tildeConst d
      * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have := tildeConst_pos d
    positivity
  have hpt : ∀ t : ℝ, |g₁ t - g₂ t| ≤ C₀ * s.indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, mul_one]
      have hdiff := norm_iteratedFDeriv_two_sub_le_omegaTildePiece (d := d) hd k hk1 hw hwzero
        hCreg hwbound (x₀ + t • y) (t • y)
      have hsub : ‖x₀ + t • y - t • y‖ = ‖x₀‖ := by rw [add_sub_cancel_right]
      have hle : ‖(iteratedFDeriv ℝ 2 F (x₀ + t • y) - iteratedFDeriv ℝ 2 F (t • y))
            (fun _ : Fin 2 => v)‖
          ≤ ‖iteratedFDeriv ℝ 2 F (x₀ + t • y) - iteratedFDeriv ℝ 2 F (t • y)‖ := by
        have h := ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ 2 F (x₀ + t • y) - iteratedFDeriv ℝ 2 F (t • y))
          (fun _ : Fin 2 => v)
        simpa [hv] using h
      have hdiffF : ‖iteratedFDeriv ℝ 2 F (x₀ + t • y) - iteratedFDeriv ℝ 2 F (t • y)‖
          ≤ Creg * tildeConst d * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ := by
        rw [hF]
        rw [hsub] at hdiff
        exact hdiff
      have hone : g₁ t - g₂ t = (iteratedFDeriv ℝ 2 F (x₀ + t • y)
          - iteratedFDeriv ℝ 2 F (t • y)) (fun _ : Fin 2 => v) := by
        simp only [hg₁, hg₂, sub_apply]
      rw [hC₀, hone, ← Real.norm_eq_abs]
      exact le_trans hle hdiffF
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have h1 : (2 : ℝ) ^ (k + 1) < ‖x₀ + t • y‖ := by
        by_contra hc
        push Not at hc
        exact ht (Or.inl hc)
      have h2 : (2 : ℝ) ^ (k + 1) < ‖t • y‖ := by
        by_contra hc
        push Not at hc
        refine ht (Or.inr ?_)
        rw [hnorm' t] at hc
        exact hc
      have hz1 : g₁ t = 0 := by
        show (iteratedFDeriv ℝ 2 F (x₀ + t • y)) (fun _ : Fin 2 => v) = 0
        rw [hF, iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w h1 2]
        simp
      have hz2 : g₂ t = 0 := by
        show (iteratedFDeriv ℝ 2 F (t • y)) (fun _ : Fin 2 => v) = 0
        rw [hF, iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w h2 2]
        simp
      rw [hz1, hz2, sub_zero, abs_zero]
  -- integrability of the dominating function
  have hs_meas : MeasurableSet s := measurableSet_lineParamSet k x₀ y
  have hfin : volume s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_lineParamSet_le k x₀ y hy)
  have hIntC : Integrable (fun t : ℝ => C₀ * s.indicator (fun _ => (1 : ℝ)) t) := by
    have h1 : Integrable (s.indicator (fun _ : ℝ => C₀)) :=
      (integrableOn_const hfin).integrable_indicator hs_meas
    refine h1.congr ?_
    filter_upwards with t
    show s.indicator (fun _ : ℝ => C₀) t = C₀ * s.indicator (fun _ => (1 : ℝ)) t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  have hInt12 : Integrable (fun t : ℝ => |g₁ t - g₂ t|) := (hi1.sub hi2).abs
  have hpow : (2 : ℝ) ^ (k + 3) = (2 : ℝ) ^ ((k : ℝ) + 3) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k + 3)]
    congr 1
    push_cast
    ring
  calc |(∫ t : ℝ, g₁ t) - (∫ t : ℝ, g₂ t)|
      = ‖∫ t : ℝ, (g₁ t - g₂ t)‖ := by rw [← integral_sub hi1 hi2, Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ, |g₁ t - g₂ t| := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, C₀ * s.indicator (fun _ => (1 : ℝ)) t := integral_mono hInt12 hIntC hpt
    _ = C₀ * (volume s).toReal := by
        rw [integral_const_mul]
        congr 1
        exact integral_indicator_one (μ := volume) hs_meas
    _ ≤ C₀ * (2 : ℝ) ^ (k + 3) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₀nn
        rw [← ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2:ℝ)^(k+3))]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_lineParamSet_le k x₀ y hy)
    _ = 8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ := by
        rw [hC₀, hpow]
        rw [show Creg * tildeConst d * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖
              * (2 : ℝ) ^ ((k : ℝ) + 3)
            = Creg * tildeConst d * ‖x₀‖ * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ))
              * (2 : ℝ) ^ ((k : ℝ) + 3)) from by ring]
        rw [dyadic_weight_arith]
        ring

/-! ## 7. The main second-derivative estimate -/

/-- **`eq:estimate_second_deriv_line_tilde_omega_k_sum` of Cohen's §4.**  For any line
`ℓ = {x₀ + t ŷ}` through the point `x₀ ⊥ ŷ` closest to the origin and any unit `v̂ ⊥ ŷ`,

  `∑_{k=2}^K |∫_ℝ ⟨(D²ω̃_k(x₀ + tŷ))v̂, v̂⟩ dt| ≤ 32 C_reg C̃ + 256 C_gr`.

The sum is bounded uniformly in `K`; since the pieces vanish on the annuli
`2^{k-1} ≤ ‖x‖ ≤ 2^{k+1}`, this is the estimate that makes the piecewise sum
`∑_k ∫_ℝ⟨D²ω̃_k(…)v̂,v̂⟩` absolutely convergent. -/
theorem sum_abs_integral_second_deriv_le (hd : 1 ≤ d) {K : ℕ} {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (x₀ y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) (hvperp : inner ℝ y v = 0)
    (hperp₀ : inner ℝ x₀ y = 0) :
    (∑ k ∈ Finset.Icc 2 K,
        |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t|)
      ≤ 32 * Creg * tildeConst d + 256 * Cgr := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  -- the regularity hypothesis for `w` itself
  have hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro x
    have h := hwbound 0 (by norm_num) x
    simpa [norm_iteratedFDeriv_zero] using h
  -- the threshold `m₀`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖x₀‖ ≤ (2 : ℝ) ^ (m + 1) := by
    obtain ⟨n, hn⟩ := exists_pow_gt_norm (d := d) x₀
    refine ⟨n, le_of_lt (lt_of_lt_of_le hn ?_)⟩
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  set m₀ := Nat.find (show ∃ m : ℕ, ‖x₀‖ ≤ (2 : ℝ) ^ (m + 1) from ⟨m, hm⟩) with hm₀def
  have hex : ∃ m : ℕ, ‖x₀‖ ≤ (2 : ℝ) ^ (m + 1) := ⟨m, hm⟩
  have hm₀ : ‖x₀‖ ≤ (2 : ℝ) ^ (m₀ + 1) := Nat.find_spec hex
  have hm₀min : ∀ k : ℕ, k < m₀ → (2 : ℝ) ^ (k + 1) < ‖x₀‖ := by
    intro k hk
    refine lt_of_not_ge fun hc => ?_
    exact absurd (Nat.find_min' hex hc) (not_le.mpr hk)
  set S1 := (Finset.Icc 2 K).filter (fun k => k < m₀) with hS1def
  set S2 := (Finset.Icc 2 K).filter (fun k => ¬ k < m₀) with hS2def
  set f : ℕ → ℝ := fun k => |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t| with hf
  -- regime 1: the integral vanishes
  have hS1zero : (∑ k ∈ S1, f k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hS1def, Finset.mem_filter] at hk
    obtain ⟨hkI, hkm⟩ := hk
    show |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t| = 0
    rw [integral_lineSecondDeriv_eq_zero (d := d) k w x₀ y v hy hperp₀ (hm₀min k hkm),
      abs_zero]
  -- regime 3: the bound for each term
  have hterm : ∀ k ∈ S2, f k
      ≤ 8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ + 2 * |qk k w| := by
    intro k hk
    rw [hS2def, Finset.mem_filter] at hk
    obtain ⟨hkI, -⟩ := hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hkI).1
    have h1 := abs_integral_lineSecondDeriv_sub_le (d := d) hd k hk2 hw hwzero hCreg hwbound
      x₀ y v hy hv
    have h2 : (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t) = 2 * qk k w := by
      have h := integral_iteratedFDeriv_two_omegaTildePiece (d := d) k hk2 hw y v hy hv hvperp
      rw [← h]
      simp only [lineSecondDeriv_def, zero_add]
    show |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t| ≤ _
    have h3 : |∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t|
        ≤ |∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t|
          + |(∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t)
              - (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t)| := by
      have habs := abs_add_le
        ((∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t)
          - (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t))
        (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t)
      have hsum : ((∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t)
          - (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t))
          + (∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t)
          = ∫ t : ℝ, lineSecondDeriv (d := d) k w x₀ y v t := by ring
      rw [hsum] at habs
      linarith [habs]
    have h4 : |∫ t : ℝ, lineSecondDeriv (d := d) k w 0 y v t| = 2 * |qk k w| := by
      rw [h2, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4] at h3
    linarith [h1, h3]
  -- the split of the sum
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 K) (fun k => k < m₀) f
  rw [← hsplit, hS1zero, zero_add]
  -- the two parts
  have hRk : ∀ k : ℕ, (2 : ℝ) ^ (-(k : ℝ)) = ((2 : ℝ) ^ k)⁻¹ := fun k => (inv_two_pow k).symm
  have hS2sub : S2 ⊆ Finset.Icc m₀ K := by
    intro k hk
    rw [hS2def, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk2, hkK⟩, hkm⟩ := hk
    exact Finset.mem_Icc.mpr ⟨not_lt.mp hkm, hkK⟩
  have hsumR : (∑ k ∈ S2, (2 : ℝ) ^ (-(k : ℝ))) ≤ 2 * (2 : ℝ) ^ (-(m₀ : ℝ)) := by
    rw [hS2def]
    calc (∑ k ∈ (Finset.Icc 2 K).filter (fun k => ¬ k < m₀), (2 : ℝ) ^ (-(k : ℝ)))
        = ∑ k ∈ (Finset.Icc 2 K).filter (fun k => ¬ k < m₀), ((2 : ℝ) ^ k)⁻¹ := by
          refine Finset.sum_congr rfl fun k _ => hRk k
      _ ≤ ∑ k ∈ Finset.Icc m₀ K, ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hS2sub (fun k _ _ => by positivity)
      _ ≤ 2 * ((2 : ℝ) ^ m₀)⁻¹ := sum_Icc_inv_pow_two_le m₀ K
      _ = 2 * (2 : ℝ) ^ (-(m₀ : ℝ)) := by rw [hRk m₀]
  have hS2sub1 : S2 ⊆ Finset.Icc 1 K := by
    intro k hk
    rw [hS2def, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk2, hkK⟩, -⟩ := hk
    exact Finset.mem_Icc.mpr ⟨by omega, hkK⟩
  have hsumQ : (∑ k ∈ S2, |qk k w|) ≤ 128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS2sub1
      (fun k _ _ => abs_nonneg _)) ?_
    exact sum_abs_qk_le_growth (d := d) hd hw.continuous hwnonpos hCreg.le hreg hint
  -- put the pieces together
  have hA : (∑ k ∈ S2, 8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖)
      = 8 * (Creg * tildeConst d) * ‖x₀‖ * (∑ k ∈ S2, (2 : ℝ) ^ (-(k : ℝ))) := by
    rw [show 8 * (Creg * tildeConst d) * ‖x₀‖ * (∑ k ∈ S2, (2 : ℝ) ^ (-(k : ℝ)))
        = ∑ k ∈ S2, (8 * (Creg * tildeConst d) * ‖x₀‖) * (2 : ℝ) ^ (-(k : ℝ)) from by
      rw [Finset.mul_sum]]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hB : (∑ k ∈ S2, 2 * |qk k w|) = 2 * (∑ k ∈ S2, |qk k w|) := by
    rw [Finset.mul_sum]
  have hCnn : (0 : ℝ) ≤ 8 * (Creg * tildeConst d) * ‖x₀‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCreg.le (tildeConst_nonneg d)))
      (norm_nonneg _)
  have hC : 8 * (Creg * tildeConst d) * ‖x₀‖ * (2 * (2 : ℝ) ^ (-(m₀ : ℝ)))
      ≤ 32 * Creg * tildeConst d := by
    have h2nn : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (-(m₀ : ℝ)) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    have h2 : (2 : ℝ) ^ (m₀ + 1) * (2 * (2 : ℝ) ^ (-(m₀ : ℝ))) = 4 := by
      rw [hRk m₀, pow_succ]
      field_simp
      norm_num
    have h1 : ‖x₀‖ * (2 * (2 : ℝ) ^ (-(m₀ : ℝ))) ≤ 4 := by
      have h := mul_le_mul_of_nonneg_right hm₀ h2nn
      rwa [h2] at h
    calc 8 * (Creg * tildeConst d) * ‖x₀‖ * (2 * (2 : ℝ) ^ (-(m₀ : ℝ)))
        = 8 * (Creg * tildeConst d) * (‖x₀‖ * (2 * (2 : ℝ) ^ (-(m₀ : ℝ)))) := by ring
      _ ≤ 8 * (Creg * tildeConst d) * 4 :=
          mul_le_mul_of_nonneg_left h1 (by
            refine mul_nonneg (by norm_num) ?_
            exact mul_nonneg hCreg.le (tildeConst_nonneg d))
      _ = 32 * Creg * tildeConst d := by ring
  calc (∑ k ∈ S2, f k)
      ≤ ∑ k ∈ S2, (8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖ + 2 * |qk k w|) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ S2, 8 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ‖x₀‖)
          + ∑ k ∈ S2, 2 * |qk k w| := Finset.sum_add_distrib
    _ = 8 * (Creg * tildeConst d) * ‖x₀‖ * (∑ k ∈ S2, (2 : ℝ) ^ (-(k : ℝ)))
          + 2 * (∑ k ∈ S2, |qk k w|) := by rw [hA, hB]
    _ ≤ 8 * (Creg * tildeConst d) * ‖x₀‖ * (2 * (2 : ℝ) ^ (-(m₀ : ℝ)))
          + 2 * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hsumR hCnn
        · exact mul_le_mul_of_nonneg_left hsumQ (by norm_num)
    _ ≤ 32 * Creg * tildeConst d + 256 * Cgr := by
        have hQ : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr := by
          rw [← growthFunctional_eq_Gstar]; exact hgrle
        have h2 : 2 * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
            ≤ 256 * Cgr := by linarith
        linarith [hC, h2]

end Submission.FUP
