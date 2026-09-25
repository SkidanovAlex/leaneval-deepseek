import Mathlib
import Submission.Work.NN.Newton.C1smallSetup

/-!
# Radius and gap bounds for the `C^{1,α}`-small Newton iteration

`delta m = 2^{-(m+3)}` and `rad 0 = 4`, `rad (m+1) = rad m (1 - 2 δ_m)`.

The gap is small, `0 < δ_m ≤ 1/8`, and the radii stay in the interval `[2, 4]`;
consequently `rad m (1 - δ_m) > 1` and `rad m (1 - 2 δ_m) = rad (m+1) ≥ 2`.
-/

namespace Work.NN.Newton

/-- Elementary algebra: for `0 ≤ p ≤ 1`, `(2 + 2p)(1 - p/4) ≥ 2 + p`. -/
private lemma two_add_two_mul (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 + p ≤ (2 + 2 * p) * (1 - p / 4) := by
  nlinarith [mul_nonneg h0 (show (0:ℝ) ≤ 1 - p by linarith)]

lemma deltaPos (m : ℕ) : 0 < delta m := by
  unfold delta; positivity

lemma deltaLeEighth (m : ℕ) : delta m ≤ 1 / 8 := by
  have h := pow_le_pow_of_le_one (show (0:ℝ) ≤ 1 / 2 by norm_num)
      (show (1/2:ℝ) ≤ 1 by norm_num) (show 3 ≤ m + 3 by omega)
  unfold delta
  calc (1/2:ℝ) ^ (m + 3) ≤ (1/2:ℝ) ^ 3 := h
    _ = 1 / 8 := by norm_num

/-- `2 δ_m = 2^{-m}/4`. -/
lemma two_mul_delta (m : ℕ) : 2 * delta m = (1/2:ℝ) ^ m / 4 := by
  unfold delta
  rw [pow_add]
  ring

/-- The radii are bounded below by `2 + 2^{-m}` (in particular by `2`). -/
lemma rad_ge (m : ℕ) : 2 + 2 * (1/2:ℝ) ^ m ≤ rad m := by
  induction m with
  | zero => rw [rad_zero]; norm_num
  | succ m ih =>
    rw [rad_succ]
    have hp0 : (0:ℝ) ≤ (1/2:ℝ) ^ m := by positivity
    have hp1 : (1/2:ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hdelta := two_mul_delta m
    have hf0 : (0:ℝ) ≤ 1 - 2 * delta m := by rw [hdelta]; linarith
    have hstep1 : (2 + 2 * (1/2:ℝ) ^ m) * (1 - 2 * delta m)
        ≤ rad m * (1 - 2 * delta m) :=
      mul_le_mul_of_nonneg_right ih hf0
    have hstep2 : 2 + 2 * (1/2:ℝ) ^ (m + 1)
        ≤ (2 + 2 * (1/2:ℝ) ^ m) * (1 - 2 * delta m) := by
      rw [hdelta]
      have hpow : (1/2:ℝ) ^ (m + 1) = (1/2:ℝ) ^ m / 2 := by rw [pow_succ]; ring
      rw [hpow]
      have halg := two_add_two_mul ((1/2:ℝ) ^ m) hp0 hp1
      linarith [halg]
    linarith [hstep1, hstep2]

/-- In particular the radii are at least `2`. -/
lemma rad_ge_two (m : ℕ) : (2:ℝ) ≤ rad m := by
  have h := rad_ge m
  have hp : (0:ℝ) ≤ (1/2:ℝ) ^ m := by positivity
  linarith

/-- The radii are bounded above by `4`. -/
lemma rad_le_four (m : ℕ) : rad m ≤ 4 := by
  induction m with
  | zero => rw [rad_zero]
  | succ m ih =>
    rw [rad_succ]
    have h1 : (0:ℝ) ≤ rad m := by linarith [rad_ge_two m]
    have h2 : 1 - 2 * delta m ≤ 1 := by have := deltaPos m; linarith
    calc rad m * (1 - 2 * delta m) ≤ rad m * 1 := mul_le_mul_of_nonneg_left h2 h1
      _ = rad m := by ring
      _ ≤ 4 := ih

theorem C1smallRadBounds : ∀ m : ℕ,
    (0:ℝ) < delta m ∧ delta m ≤ 1/8 ∧ (1:ℝ) ≤ rad m ∧ rad m ≤ 4 ∧
    (1:ℝ) < rad m * (1 - delta m) ∧ (2:ℝ) ≤ rad m * (1 - 2 * delta m) := by
  intro m
  refine ⟨deltaPos m, deltaLeEighth m, ?_, rad_le_four m, ?_, ?_⟩
  · linarith [rad_ge_two m]
  · have hrp : (0:ℝ) < rad m := by linarith [rad_ge_two m]
    have hlt : 1 - 2 * delta m < 1 - delta m := by have := deltaPos m; linarith
    have h1 : rad (m + 1) < rad m * (1 - delta m) := by
      rw [rad_succ]
      exact mul_lt_mul_of_pos_left hlt hrp
    have h3 : (2:ℝ) ≤ rad (m + 1) := rad_ge_two (m + 1)
    linarith [h1, h3]
  · rw [← rad_succ m]
    linarith [rad_ge_two (m + 1)]

end Work.NN.Newton
