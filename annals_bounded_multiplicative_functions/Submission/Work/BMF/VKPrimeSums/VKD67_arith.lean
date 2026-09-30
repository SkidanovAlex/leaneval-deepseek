import Mathlib
import Submission.Work.BMF.VKPrimeSums.VKD67Defs
import Submission.Work.BMF.V4prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary arithmetic bounds for the Vinogradov–Korobov denominator `VKD67`

This file collects the elementary (purely real-variable) facts about
`VKD67 N t = (log(|t|+3))^{6/7} · (log(N+2) + log log(|t|+3))` that the
logarithmic-derivative bound `V4` needs, namely: positivity and `≥ 1` on `|t| ≥ 3`,
stability under a shift of the height by at most `1`, the quadratic upper bound
`VKD67 N t ≤ 4 L²` with `L = log (N (|t|+3))`, and `log (VKD67 N t) ≤ 5L`.
-/

namespace Work.BMF.VKPrimeSums

open Work.BMF

set_option maxHeartbeats 8000000

private lemma one_le_VKD67' (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) :
    1 ≤ VKD67 N t := by
  rw [VKD67_eq']
  have h1 : (1 : ℝ) ≤ VKA t ^ (6 / 7 : ℝ) :=
    Real.one_le_rpow (one_le_VKA ht) (by norm_num)
  have h2 : (1 : ℝ) ≤ VKE N t := one_le_VKE N ht
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ VKA t ^ (6 / 7 : ℝ) * VKE N t :=
        mul_le_mul h1 h2 (by linarith) (Real.rpow_nonneg (VKA_nonneg ht) _)

private lemma VKD67_pos' (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 < VKD67 N t :=
  lt_of_lt_of_le zero_lt_one (one_le_VKD67' N ht)

private lemma VKD67_shift_le (N : ℕ) [NeZero N] {t v : ℝ} (ht : 4 ≤ |t|)
    (htv : |v - t| ≤ 1) : VKD67 N v ≤ 4 * VKD67 N t := by
  have hvt : 3 ≤ |v| := three_le_abs_of_shift ht htv
  have hA : VKA v ≤ 2 * VKA t := VKA_shift_le ht htv
  have hE : VKE N v ≤ 2 * VKE N t := VKE_shift_le N ht htv
  have hAv : 0 ≤ VKA v := (VKA_pos hvt).le
  have hAt : 0 ≤ VKA t := (VKA_pos (by linarith)).le
  have hEv : 0 ≤ VKE N v := (VKE_pos N hvt).le
  have hEt : 0 ≤ VKE N t := (VKE_pos N (by linarith)).le
  have hpow : VKA v ^ (6 / 7 : ℝ) ≤ (2 * VKA t) ^ (6 / 7 : ℝ) :=
    Real.rpow_le_rpow hAv hA (by norm_num)
  have hmul : (2 * VKA t) ^ (6 / 7 : ℝ) = (2 : ℝ) ^ (6 / 7 : ℝ) * VKA t ^ (6 / 7 : ℝ) :=
    Real.mul_rpow (by norm_num) hAt
  have h2 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (y := (6 / 7 : ℝ)) (z := (1 : ℝ)) (by norm_num)
    simpa using h
  have hVt : 0 ≤ VKA t ^ (6 / 7 : ℝ) * VKE N t :=
    mul_nonneg (Real.rpow_nonneg hAt _) hEt
  rw [VKD67_eq', VKD67_eq']
  calc VKA v ^ (6 / 7 : ℝ) * VKE N v
      ≤ ((2 : ℝ) ^ (6 / 7 : ℝ) * VKA t ^ (6 / 7 : ℝ)) * (2 * VKE N t) := by
        refine mul_le_mul ?_ hE hEv (by positivity)
        rwa [hmul] at hpow
    _ = ((2 : ℝ) ^ (6 / 7 : ℝ) * 2) * (VKA t ^ (6 / 7 : ℝ) * VKE N t) := by ring
    _ ≤ 4 * (VKA t ^ (6 / 7 : ℝ) * VKE N t) := by
        refine mul_le_mul_of_nonneg_right ?_ hVt
        linarith

private lemma N_cast_one_le {N : ℕ} [NeZero N] : (1 : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

/-- `log (|t|+3) ≥ 1` for `|t| ≥ 4`. -/
private lemma one_le_log_abs_add_three {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log (|t| + 3) := by
  have h : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
  exact le_trans log_three_ge_one (Real.log_le_log (by norm_num) h)

/-- `L := log (N (|t|+3)) ≥ 1`. -/
private lemma one_le_log_N_mul {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hle : |t| + 3 ≤ (N : ℝ) * (|t| + 3) := by
    nlinarith [N_cast_one_le (N := N), h3]
  exact le_trans (one_le_log_abs_add_three ht) (Real.log_le_log h3 hle)

private lemma log_N_le {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (N : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hN : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
  exact Real.log_le_log (by linarith) (by nlinarith)

/-- `VKA t = log (|t|+3) ≤ L`. -/
private lemma VKA_le_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    VKA t ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [VKA_eq]
  exact Real.log_le_log (by linarith [abs_nonneg t])
    (by nlinarith [N_cast_one_le (N := N), abs_nonneg t])

/-- `VKE N t ≤ 4L`. -/
private lemma VKE_le_four_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    VKE N t ≤ 4 * Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [VKE_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ VKA t := one_le_VKA (by linarith)
  have hlogN2 : Real.log ((N : ℝ) + 2) ≤ Real.log (3 * (N : ℝ)) :=
    Real.log_le_log (by linarith [N_cast_one_le (N := N)]) (by nlinarith [N_cast_one_le (N := N)])
  have hlog3 : Real.log (3 * (N : ℝ)) = Real.log 3 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) (by linarith [N_cast_one_le (N := N)])
  have hlogN : Real.log (N : ℝ) ≤ L := by rw [hL]; exact log_N_le ht
  have hlogA : Real.log (VKA t) ≤ VKA t := Real.log_le_self (by linarith)
  have hA_L : VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  have hlog3le : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  rw [hlog3] at hlogN2
  linarith

/-- `VKD67 N t ≤ 4L²`. -/
private lemma VKD67_le_four_L_sq {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    VKD67 N t ≤ 4 * (Real.log ((N : ℝ) * (|t| + 3))) ^ 2 := by
  rw [VKD67_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ VKA t := one_le_VKA (by linarith)
  have hAnn : 0 ≤ VKA t := by linarith
  have hpow : VKA t ^ (6 / 7 : ℝ) ≤ VKA t :=
    Real.rpow_le_self_of_one_le hA1 (by norm_num)
  have hE := VKE_le_four_L (N := N) ht
  have hAL : VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  have hEnn : 0 ≤ VKE N t := le_of_lt (VKE_pos N (by linarith))
  calc VKA t ^ (6 / 7 : ℝ) * VKE N t
      ≤ VKA t * VKE N t := mul_le_mul_of_nonneg_right hpow hEnn
    _ ≤ L * (4 * L) := mul_le_mul hAL hE hEnn (by linarith)
    _ = 4 * L ^ 2 := by ring

/-- `log (VKD67 N t) ≤ 5L`. -/
private lemma log_VKD67_le {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (VKD67 N t) ≤ 5 * Real.log ((N : ℝ) * (|t| + 3)) := by
  rw [VKD67_eq']
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hL
  have hL1 : 1 ≤ L := one_le_log_N_mul ht
  have hA1 : 1 ≤ VKA t := one_le_VKA (by linarith)
  have hApos : 0 < VKA t := by linarith
  have hE1 : 1 ≤ VKE N t := one_le_VKE N (by linarith)
  have hEpos : 0 < VKE N t := by linarith
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hApos _)) (ne_of_gt hEpos)]
  rw [Real.log_rpow hApos]
  have hlogA : Real.log (VKA t) ≤ VKA t := Real.log_le_self hApos.le
  have hlogE : Real.log (VKE N t) ≤ VKE N t := Real.log_le_self hEpos.le
  have hE4 := VKE_le_four_L (N := N) ht
  have hA_L : VKA t ≤ L := by rw [hL]; exact VKA_le_L ht
  nlinarith

lemma VKD67_arith (N : ℕ) [NeZero N] :
    (∀ t : ℝ, 3 ≤ |t| → 0 < Work.BMF.VKPrimeSums.VKD67 N t) ∧
    (∀ t : ℝ, 3 ≤ |t| → 1 ≤ Work.BMF.VKPrimeSums.VKD67 N t) ∧
    (∀ t v : ℝ, 4 ≤ |t| → |v - t| ≤ 1 →
      Work.BMF.VKPrimeSums.VKD67 N v ≤ 4 * Work.BMF.VKPrimeSums.VKD67 N t) ∧
    (∀ t : ℝ, 4 ≤ |t| →
      Work.BMF.VKPrimeSums.VKD67 N t ≤ 4 * Real.log ((N : ℝ) * (|t| + 3)) ^ 2) ∧
    (∀ t : ℝ, 4 ≤ |t| →
      Real.log (Work.BMF.VKPrimeSums.VKD67 N t) ≤ 5 * Real.log ((N : ℝ) * (|t| + 3))) := by
  refine ⟨fun t ht => VKD67_pos' N ht, fun t ht => one_le_VKD67' N ht,
    fun t v ht htv => VKD67_shift_le N ht htv,
    fun t ht => VKD67_le_four_L_sq (N := N) ht,
    fun t ht => log_VKD67_le (N := N) ht⟩

end Work.BMF.VKPrimeSums
