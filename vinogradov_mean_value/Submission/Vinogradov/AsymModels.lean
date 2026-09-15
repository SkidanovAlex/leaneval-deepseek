/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymRecIneq
import Submission.Vinogradov.DecLinLift

/-!
# The degree-`L` models of the §4 recursion from the induction hypothesis

The §4 recursion (`AsymRecIneq.asymExpSet_recursion_ineq`) consumes, for the degree-`L` factors
(`L = k - l` and `L = l - 1`), the model hypotheses

  `hmMod : ∀ M ≥ 1, DecLinScale L M (laneEnl k L hk hl hlk) (ofReal (a₀ · M^εm))`

at the FIXED enlargement `laneEnl k L` of the §3.4 lane.  This module shows that these models
follow from the induction hypothesis `etaLin L ≤ 0` at degree `L`:

  `etaLin L ≤ 0`  --`exists_decLinScale_of_etaLin_nonpos`-->  the λ = 2 ε-form at every level
  --`DecLinScale_lam_le`-->  the λ = 1 (un-enlarged) dyadic form
  --`DecLinLift.decLinScale_of_decLin_nat`-->  the λ = Λ form for any `Λ ≥ laneEnl`
  --`DecLinScale_lam_le`-->  the model at λ = `laneEnl`.

The level is chosen as `2^(max 1 (clog 2 M))`, which is `≤ 4M`, so the level loss
`(2^N)^{εm/2} ≤ 4^{εm/2} M^{εm}` is absorbed by the `M`-independent constant
`a₀ = max 1 (Λ · K · 4^{εm/2})`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- The §3.4 lane enlargement is positive. -/
lemma laneEnl_pos {k L : ℕ} (hk : 1 ≤ k) (hL1 : 1 ≤ L) (hLk : L ≤ k) :
    0 < laneEnl k L hk hL1 hLk := by
  have hlam : (0 : ℝ) < 2 * laneLam k L hk hL1 hLk := by
    have h := one_le_laneLam k L hk hL1 hLk
    linarith
  have hgain : 0 < tubeGainP L (projCL k L hL1 hLk) (projRR k L hL1 hLk)
      (2 * laneLam k L hk hL1 hLk) := by
    rw [tubeGainP]
    refine div_pos ?_ (mul_pos (tubeCBP_pos hL1) (projCL_pos k L hL1 hLk))
    exact mul_pos (mul_pos (mul_pos (mul_pos (by positivity)
      (projRR_pos k L hL1 hLk)) (by positivity)) (pow_pos hlam _)) (by positivity)
  rw [laneEnl, towerEnlP]
  exact mul_pos (mul_pos hlam (by linarith)) (lt_of_lt_of_le zero_lt_one (one_le_Ctube L))

set_option maxHeartbeats 16000000 in
/-- **The degree-`L` models of the §4 recursion from `etaLin L ≤ 0`.** -/
theorem exists_models_of_etaLin_le_zero {k L : ℕ} (hk : 1 ≤ k) (hL1 : 1 ≤ L) (hLk : L ≤ k)
    (hη : etaLin L ≤ 0) {εm : ℝ} (hεm : 0 < εm) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale L M (laneEnl k L hk hL1 hLk) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)) := by
  have hεm2 : 0 < εm / 2 := by linarith
  obtain ⟨K, hK, hD⟩ := exists_decLinScale_of_etaLin_nonpos hL1 hη hεm2
  obtain ⟨Λ₀, hΛ₀⟩ := exists_nat_ge (laneEnl k L hk hL1 hLk)
  have hΛge0 : laneEnl k L hk hL1 hLk ≤ (max 1 Λ₀ : ℕ) := by
    have h2 : (Λ₀ : ℝ) ≤ ((max 1 Λ₀ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 1 Λ₀
    linarith
  have hΛ1 : 1 ≤ max 1 Λ₀ := le_max_left _ _
  have hlenl : 0 < laneEnl k L hk hL1 hLk := laneEnl_pos hk hL1 hLk
  refine ⟨max 1 (((max 1 Λ₀ : ℕ) : ℝ) * K), le_max_left _ _, fun M hM => ?_⟩
  -- the λ = 1 statement at level `M`
  have hdec : DecLin L M (ENNReal.ofReal (K * (M : ℝ) ^ (εm / 2))) := by
    have h := DecLinScale_lam_le (k := L) (M := M) (by omega)
      (lam := 1) (lam' := 2) (by norm_num) (by norm_num) (hD M hM)
    rwa [decLinScale_one_iff] at h
  -- lift to the enlargement `Λ`
  have hm : M ≤ max 1 Λ₀ * M := Nat.le_mul_of_pos_left M (by omega)
  have hlift := decLinScale_of_decLin_nat (k := L) hL1 (max 1 Λ₀) hΛ1 hm hdec
  refine DecLinScale_lam_le (k := L) (M := M) (hM := by omega) hlenl.le hΛge0 ?_
  refine DecLinScale_mono ?_ hlift
  have hconst : ((max 1 Λ₀ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (K * (M : ℝ) ^ (εm / 2))
      = ENNReal.ofReal (((max 1 Λ₀ : ℕ) : ℝ) * (K * (M : ℝ) ^ (εm / 2))) := by
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [hconst]
  refine ENNReal.ofReal_le_ofReal ?_
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpow : (M : ℝ) ^ (εm / 2) ≤ (M : ℝ) ^ εm :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hMp : (0 : ℝ) ≤ (M : ℝ) ^ εm := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK0 : 0 ≤ K := hK.le
  have hLam0 : (0 : ℝ) ≤ ((max 1 Λ₀ : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((max 1 Λ₀ : ℕ) : ℝ) * (K * (M : ℝ) ^ (εm / 2))
      ≤ ((max 1 Λ₀ : ℕ) : ℝ) * (K * (M : ℝ) ^ εm) := by
        refine mul_le_mul_of_nonneg_left ?_ hLam0
        exact mul_le_mul_of_nonneg_left hpow hK0
    _ = (((max 1 Λ₀ : ℕ) : ℝ) * K) * (M : ℝ) ^ εm := by ring
    _ ≤ max 1 (((max 1 Λ₀ : ℕ) : ℝ) * K) * (M : ℝ) ^ εm :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hMp
    _ = max 1 (((max 1 Λ₀ : ℕ) : ℝ) * K) * (M : ℝ) ^ εm := rfl

end Submission.Vinogradov
