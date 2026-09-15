import Submission.FUP.ParametricContDiff
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_inv_norm_bound
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff Interval

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4: the estimates with all constants discharged

This module collects the fully discharged forms of the §4 estimates:

* `invNormConst` — the constant in the bound `‖D^n (‖x‖⁻¹)‖ ≤ C (‖x‖^{n+1})⁻¹` for `n ≤ 3`
  (from the commons `Commons.Analysis.Calculus.iteratedFDeriv_inv_norm_bound`);
* `pieceConst` — the uniform constant `8 (C_ψ · 4) + 1` in the bound
  `‖D^n ω_k(z)‖ ≤ C_reg · pieceConst · 2^{k(1-n)}` for `n ≤ 3`;
* the fully discharged forms of `norm_iteratedFDeriv_hk_le`, `abs_qk_le_regular` and
  `norm_iteratedFDeriv_gk_le` of `HkBound`/`GkBound`.
-/

/-- The constant in `‖D^n (‖x‖⁻¹)‖ ≤ C (‖x‖^{n+1})⁻¹` (`n ≤ 3`), from the shared commons. -/
noncomputable def invNormConst (d : ℕ) : ℝ :=
  Classical.choose (Commons.Analysis.Calculus.iteratedFDeriv_inv_norm_bound (d := d))

lemma invNormConst_pos (d : ℕ) : 0 < invNormConst d :=
  (Classical.choose_spec
    (Commons.Analysis.Calculus.iteratedFDeriv_inv_norm_bound (d := d))).1

/-- The inverse-norm bound, in the argument order used by the §4 estimates. -/
lemma invNormConst_spec (d : ℕ) : ∀ n : ℕ, n ≤ 3 →
    ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 →
    ‖iteratedFDeriv ℝ n (fun y : EuclideanSpace ℝ (Fin d) => (‖y‖)⁻¹) x‖
      ≤ invNormConst d * (‖x‖ ^ (n + 1))⁻¹ :=
  fun n hn x hx => (Classical.choose_spec
    (Commons.Analysis.Calculus.iteratedFDeriv_inv_norm_bound (d := d))).2 x n hn hx

/-- The uniform constant in the estimate for the dyadic pieces `ω_k`. -/
noncomputable def pieceConst (d : ℕ) : ℝ := 8 * (rpsCps d * 4) + 1

lemma pieceConst_pos (d : ℕ) : 0 < pieceConst d := by
  have := rpsCps_pos d
  rw [pieceConst]; nlinarith

/-- **The uniform estimate for the dyadic pieces**: `‖D^n ω_k(z)‖ ≤ C_reg·C_p·2^{k(1-n)}`. -/
theorem omegaPiece_iteratedFDeriv_le (k n : ℕ) (hn : n ≤ 3) {Creg : ℝ} (hCreg : 0 < Creg)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (z : ℝᵈ) :
    ‖iteratedFDeriv ℝ n (omegaPiece k w) z‖
      ≤ Creg * pieceConst d * (2 : ℝ) ^ ((k : ℝ) * (1 - (n : ℝ))) := by
  obtain ⟨C, hCpos, hCb⟩ := norm_iteratedFDeriv_omegaPiece_le (d := d) n hn
  refine le_trans (hCb Creg w hCreg hw hwzero hwbound k z) ?_
  have h1 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) ≤ 8 := by
    have h : (∑ i ∈ Finset.range (n + 1), n.choose i) = 2 ^ n := Nat.sum_range_choose n
    have h2 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      rw [← Nat.cast_sum, h]; norm_num
    rw [h2]
    have : (2 : ℝ) ^ n ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCreg.le) (by positivity)
  rw [pieceConst]
  nlinarith [rpsCps_pos d, h1]

/-- **The bound on the constants `q_k`**, fully discharged. -/
theorem abs_qk_le_Creg (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2)) :
    |qk k w| ≤ 256000 * invNormConst d * Creg * pieceConst d := by
  refine abs_qk_le_regular (d := d) hd k hk1 hw (contDiffOn_gwin (d := d) k hw)
    (invNormConst_pos d) hCreg.le (pieceConst_pos d).le
    (fun n hn x hx => invNormConst_spec d n hn x hx) ?_
  intro n hn z
  exact omegaPiece_iteratedFDeriv_le (d := d) k n hn hCreg hw hwzero hwbound z

/-- **The derivative bound for the correction `g_k`**, fully discharged:
`‖D^a g_k(x)‖ ≲ C_reg 2^{(1-a)k}` on the support annulus of `ω_k`. -/
theorem norm_iteratedFDeriv_gk_le_Creg (hd : 1 ≤ d) (k a : ℕ) (ha : a ≤ 3) (hk1 : 1 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    {x : ℝᵈ} (hx : x ∈ annOpen (d := d) k) :
    ‖iteratedFDeriv ℝ a (gk k w) x‖
      ≤ (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 ^ a * invNormConst d * Creg * pieceConst d
          * (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹ := by
  refine norm_iteratedFDeriv_gk_le (d := d) hd k a ha hk1 hw
    (contDiffOn_gwin (d := d) k hw) (invNormConst_pos d) hCreg.le (pieceConst_pos d).le
    (fun n hn x hx => invNormConst_spec d n hn x hx) ?_ hx
  intro n hn z
  exact omegaPiece_iteratedFDeriv_le (d := d) k n hn hCreg hw hwzero hwbound z

end Submission.FUP
