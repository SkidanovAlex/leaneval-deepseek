import Mathlib
import Submission.Work.ZeroDensity.Ingham.polylogAbsorbGe

/-!
# The arithmetic of the wide (un-smoothed) detector integral

`Work.ZeroDensity.Ingham.zetaDetectorBig.wideIntegralArith` absorbs all the polylogarithmic
factors produced by the wide detector integral into a factor `T^ε · T^{1/3} (T+K)^{2/3}`.

The left-hand side is the product of the six non-negative factors

* `F1 = (12 Cg / (σ - 1/2))^{4/3}`,
* `F2 = (2L)^{1/3} (2L + 1)` with `L = A log (A T)`,
* `F3 = (2 C4 (T + L))^{1/3}`,
* `F4 = (log (T + L))^{4/3}`,
* `F5 = (CM (T + L + K))^{2/3}`,
* `F6 = (log (K + 2))^{4/3}`,

and we prove

* `sigmaFactorBound`: `F1 ≤ C (log (A T))^{4/3}` — this is where the hypothesis
  `σ - 1/2 > 1/(2 log (A T))` is used (`1/(σ - 1/2) < 2 log (A T)`);
* `LFactorBound`: `F2 ≤ C T^η` (`log (A T) ≥ 1` so that `2L + 1 ≤ (2A + 1) log (A T)`);
* `logFactorBound`: `(log (A T))^{4/3} (log (T + L))^{4/3} (log (K + 2))^{4/3} ≤ C T^η`,
  using `log x ≤ x` (hence `T + L ≤ (1 + A^2) T`) and `K ≤ 6 A^2 T^3`
  (hence `K + 2 ≤ (6 A^2 + 2) T^3`), together with the elementary polylog bound
  `rpowLogLe` of `Submission/Work/ZeroDensity/Ingham/polylogAbsorbGe.lean`;
* the two remaining factors are bounded by monotonicity of `·^{1/3}` and `·^{2/3}`:
  `F3 ≤ (2 C4 (1 + A^2))^{1/3} T^{1/3}` and `F5 ≤ (CM (1 + A^2))^{2/3} (T + K)^{2/3}`.

Choosing `η = ε/2` in the second and third estimates, the total `T`-exponent is
`ε/2 + ε/2 + 1/3 = ε + 1/3`, exactly what the right-hand side allows.
-/

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

set_option maxHeartbeats 1000000

/-- The pole `1/(σ - 1/2)` of the detector is dominated by `log (A T)` as soon as
`σ - 1/2 > 1/(2 log (A T))`. -/
lemma sigmaFactorBound (A Cg : ℝ) (hA : 6 ≤ A) (hCg : 0 < Cg) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 2 ≤ T → 1 / 2 < σ →
      σ - 1 / 2 > 1 / (2 * Real.log (A * T)) →
      (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) ≤ C * (Real.log (A * T)) ^ ((4 : ℝ) / 3) := by
  refine ⟨(24 * Cg) ^ ((4 : ℝ) / 3), Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  intro σ T hT hσ hσ2
  have hAT1 : (1 : ℝ) < A * T := by nlinarith
  have hlogpos : 0 < Real.log (A * T) := Real.log_pos hAT1
  have hs : 0 < σ - 1 / 2 := by linarith
  have h2l : 0 < 2 * Real.log (A * T) := by linarith
  have h1 : (1 : ℝ) < (σ - 1 / 2) * (2 * Real.log (A * T)) :=
    (div_lt_iff₀ h2l).mp hσ2
  have h12 : 12 * Cg / (σ - 1 / 2) ≤ 24 * Cg * Real.log (A * T) := by
    rw [div_le_iff₀ hs]
    have h := mul_lt_mul_of_pos_left h1 (by linarith : (0 : ℝ) < 12 * Cg)
    have he : (24 * Cg * Real.log (A * T)) * (σ - 1 / 2)
        = 12 * Cg * ((σ - 1 / 2) * (2 * Real.log (A * T))) := by ring
    linarith [h, he]
  have hb : 0 ≤ 12 * Cg / (σ - 1 / 2) := div_nonneg (by linarith) (le_of_lt hs)
  have hmono := Real.rpow_le_rpow hb h12 (by norm_num : (0 : ℝ) ≤ 4 / 3)
  rw [Real.mul_rpow (by linarith : (0 : ℝ) ≤ 24 * Cg) (le_of_lt hlogpos)] at hmono
  exact hmono

/-- `(2L)^{1/3}(2L+1)` with `L = A log (A T)` is a polylogarithm in `T`. -/
lemma LFactorBound (A η : ℝ) (hA : 6 ≤ A) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1)
        ≤ C * T ^ η := by
  obtain ⟨M, hMpos, hM⟩ := Work.ZeroDensity.Ingham.rpowLogLe ((4 : ℝ) / 3) η (by norm_num) hη
  refine ⟨(2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (M * A ^ η), by positivity, ?_⟩
  intro T hT
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hATpos : 0 < A * T := by nlinarith
  have hAT1 : (1 : ℝ) ≤ A * T := by nlinarith
  have hlog1 : (1 : ℝ) ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le hATpos]
    have h12 : (12 : ℝ) ≤ A * T := by nlinarith
    have h3 := Real.exp_one_lt_three
    linarith
  have hlog0 : 0 ≤ Real.log (A * T) := by linarith
  have hlogpos : 0 < Real.log (A * T) := by linarith
  have e1 : (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
      ≤ (2 * A) ^ ((1 : ℝ) / 3) * (Real.log (A * T)) ^ ((1 : ℝ) / 3) := by
    rw [show 2 * (A * Real.log (A * T)) = 2 * A * Real.log (A * T) by ring,
      Real.mul_rpow (by linarith : (0 : ℝ) ≤ 2 * A) hlog0]
  have e2 : 2 * (A * Real.log (A * T)) + 1 ≤ (2 * A + 1) * Real.log (A * T) := by
    nlinarith [hlog1]
  have hlogpow : (Real.log (A * T)) ^ ((1 : ℝ) / 3) * Real.log (A * T)
      = (Real.log (A * T)) ^ ((4 : ℝ) / 3) := by
    have h := Real.rpow_add hlogpos (1 / 3) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    norm_num
  have hstep : (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1)
      ≤ (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (Real.log (A * T)) ^ ((4 : ℝ) / 3) := by
    have h := mul_le_mul e1 e2 (by nlinarith [hlog0, hApos])
      (mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * A) _)
        (Real.rpow_nonneg hlog0 _))
    calc (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1)
        ≤ ((2 * A) ^ ((1 : ℝ) / 3) * (Real.log (A * T)) ^ ((1 : ℝ) / 3))
            * ((2 * A + 1) * Real.log (A * T)) := h
      _ = (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (Real.log (A * T)) ^ ((4 : ℝ) / 3) := by
          rw [show ((2 * A) ^ ((1 : ℝ) / 3) * (Real.log (A * T)) ^ ((1 : ℝ) / 3))
                * ((2 * A + 1) * Real.log (A * T))
              = (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1)
                * ((Real.log (A * T)) ^ ((1 : ℝ) / 3) * Real.log (A * T)) by ring,
            hlogpow]
  have hM' := hM (A * T) hAT1
  have hsplit : (A * T) ^ η = A ^ η * T ^ η := Real.mul_rpow (le_of_lt hApos) (le_of_lt hTpos)
  calc (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1)
      ≤ (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (Real.log (A * T)) ^ ((4 : ℝ) / 3) := hstep
    _ ≤ (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (M * (A * T) ^ η) :=
        mul_le_mul_of_nonneg_left hM' (by positivity)
    _ = (2 * A) ^ ((1 : ℝ) / 3) * (2 * A + 1) * (M * A ^ η) * T ^ η := by
        rw [hsplit]; ring

/-- The product of the three logarithmic factors of the wide detector integral is absorbed by
`T^η`. -/
lemma logFactorBound (A η : ℝ) (hA : 6 ≤ A) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T K : ℝ, 2 ≤ T → 1 ≤ K → K ≤ 6 * A ^ 2 * T ^ 3 →
      (Real.log (A * T)) ^ ((4 : ℝ) / 3) *
        (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3) *
        (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
      ≤ C * T ^ η := by
  obtain ⟨M, hMpos, hM⟩ := Work.ZeroDensity.Ingham.rpowLogLe 4 η (by norm_num) hη
  have hApos : 0 < A := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  set cA : ℝ := Real.log A / Real.log 2 + 1 with hcA
  set cT : ℝ := Real.log (1 + A ^ 2) / Real.log 2 + 1 with hcT
  set cK : ℝ := Real.log (6 * A ^ 2 + 2) / Real.log 2 + 3 with hcK
  have hcApos : 0 < cA := by
    rw [hcA]
    have h := Real.log_nonneg hA1
    have : 0 ≤ Real.log A / Real.log 2 := div_nonneg h (le_of_lt hlog2pos)
    linarith
  have hcTpos : 0 < cT := by
    rw [hcT]
    have h : 0 ≤ Real.log (1 + A ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg A])
    have : 0 ≤ Real.log (1 + A ^ 2) / Real.log 2 := div_nonneg h (le_of_lt hlog2pos)
    linarith
  have hcKpos : 0 < cK := by
    rw [hcK]
    have h : 0 ≤ Real.log (6 * A ^ 2 + 2) := Real.log_nonneg (by nlinarith [sq_nonneg A])
    have : 0 ≤ Real.log (6 * A ^ 2 + 2) / Real.log 2 := div_nonneg h (le_of_lt hlog2pos)
    linarith
  refine ⟨cA ^ ((4 : ℝ) / 3) * cT ^ ((4 : ℝ) / 3) * cK ^ ((4 : ℝ) / 3) * M,
    by positivity, ?_⟩
  intro T K hT hK hKle
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hA2pos : 0 < 1 + A ^ 2 := by nlinarith [sq_nonneg A]
  have hATpos : 0 < A * T := by nlinarith
  have hAT1 : (1 : ℝ) ≤ A * T := by nlinarith
  have hlogATpos : 0 < Real.log (A * T) := Real.log_pos (by nlinarith)
  have hlogAT0 : 0 ≤ Real.log (A * T) := le_of_lt hlogATpos
  have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT0 : 0 ≤ Real.log T := le_of_lt hlogTpos
  have hlogT2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  -- first factor: `log (A T) ≤ cA log T`
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hf1 : Real.log (A * T) ≤ cA * Real.log T := by
    rw [hcA]
    have hmulA : Real.log (A * T) = Real.log A + Real.log T :=
      Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)
    have hbase : (Real.log A / Real.log 2) * Real.log 2 = Real.log A :=
      div_mul_cancel₀ _ (ne_of_gt hlog2pos)
    have hmono : (Real.log A / Real.log 2) * Real.log 2
        ≤ (Real.log A / Real.log 2) * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT2 (div_nonneg hlogA0 (le_of_lt hlog2pos))
    linarith [hmulA, hbase, hmono]
  -- second factor: `log (T + A log (A T)) ≤ cT log T`
  have hTLpos : 0 < T + A * Real.log (A * T) := by
    have h := mul_nonneg (le_of_lt hApos) hlogAT0
    linarith
  have hTL : T + A * Real.log (A * T) ≤ (1 + A ^ 2) * T := by
    have h1 : A * Real.log (A * T) ≤ A * (A * T) :=
      mul_le_mul_of_nonneg_left (by
        have := Real.log_le_sub_one_of_pos hATpos; linarith) (le_of_lt hApos)
    nlinarith [h1]
  have hf2 : Real.log (T + A * Real.log (A * T)) ≤ cT * Real.log T := by
    rw [hcT]
    have hlogle : Real.log (T + A * Real.log (A * T)) ≤ Real.log ((1 + A ^ 2) * T) :=
      Real.log_le_log hTLpos hTL
    have hmulT : Real.log ((1 + A ^ 2) * T) = Real.log (1 + A ^ 2) + Real.log T :=
      Real.log_mul (ne_of_gt hA2pos) (ne_of_gt hTpos)
    have hlogA20 : 0 ≤ Real.log (1 + A ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg A])
    have hbase : (Real.log (1 + A ^ 2) / Real.log 2) * Real.log 2 = Real.log (1 + A ^ 2) :=
      div_mul_cancel₀ _ (ne_of_gt hlog2pos)
    have hmono : (Real.log (1 + A ^ 2) / Real.log 2) * Real.log 2
        ≤ (Real.log (1 + A ^ 2) / Real.log 2) * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT2 (div_nonneg hlogA20 (le_of_lt hlog2pos))
    linarith [hlogle, hmulT, hbase, hmono]
  -- third factor: `log (K + 2) ≤ cK log T`
  have hf3 : Real.log (K + 2) ≤ cK * Real.log T := by
    rw [hcK]
    have hK2pos : 0 < K + 2 := by linarith
    have hT3 : (1 : ℝ) ≤ T ^ 3 := one_le_pow₀ hT1
    have hKle' : K + 2 ≤ (6 * A ^ 2 + 2) * T ^ 3 := by nlinarith [hKle, hT3, sq_nonneg A]
    have hlogle : Real.log (K + 2) ≤ Real.log ((6 * A ^ 2 + 2) * T ^ 3) :=
      Real.log_le_log hK2pos hKle'
    have hmulK : Real.log ((6 * A ^ 2 + 2) * T ^ 3) = Real.log (6 * A ^ 2 + 2) + Real.log (T ^ 3) :=
      Real.log_mul (by positivity) (by positivity)
    have hlogT3 : Real.log (T ^ 3) = 3 * Real.log T := by
      rw [← Real.rpow_natCast T 3, Real.log_rpow hTpos]
      norm_num
    have hlogK20 : 0 ≤ Real.log (6 * A ^ 2 + 2) := Real.log_nonneg (by nlinarith [sq_nonneg A])
    have hbase : (Real.log (6 * A ^ 2 + 2) / Real.log 2) * Real.log 2 = Real.log (6 * A ^ 2 + 2) :=
      div_mul_cancel₀ _ (ne_of_gt hlog2pos)
    have hmono : (Real.log (6 * A ^ 2 + 2) / Real.log 2) * Real.log 2
        ≤ (Real.log (6 * A ^ 2 + 2) / Real.log 2) * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT2 (div_nonneg hlogK20 (le_of_lt hlog2pos))
    linarith [hlogle, hmulK, hlogT3, hbase, hmono]
  -- raise the three bounds to the power `4/3`
  have hB1 : (Real.log (A * T)) ^ ((4 : ℝ) / 3) ≤ cA ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) := by
    calc (Real.log (A * T)) ^ ((4 : ℝ) / 3) ≤ (cA * Real.log T) ^ ((4 : ℝ) / 3) :=
          Real.rpow_le_rpow hlogAT0 hf1 (by norm_num)
      _ = cA ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) :=
          Real.mul_rpow (le_of_lt hcApos) hlogT0
  have hB2 : (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
      ≤ cT ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) := by
    have hnn : 0 ≤ Real.log (T + A * Real.log (A * T)) :=
      Real.log_nonneg (by have h := mul_nonneg (le_of_lt hApos) hlogAT0; linarith)
    calc (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        ≤ (cT * Real.log T) ^ ((4 : ℝ) / 3) := Real.rpow_le_rpow hnn hf2 (by norm_num)
      _ = cT ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) :=
          Real.mul_rpow (le_of_lt hcTpos) hlogT0
  have hB3 : (Real.log (K + 2)) ^ ((4 : ℝ) / 3) ≤ cK ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) := by
    have hnn : 0 ≤ Real.log (K + 2) := Real.log_nonneg (by linarith)
    calc (Real.log (K + 2)) ^ ((4 : ℝ) / 3) ≤ (cK * Real.log T) ^ ((4 : ℝ) / 3) :=
          Real.rpow_le_rpow hnn hf3 (by norm_num)
      _ = cK ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3) :=
          Real.mul_rpow (le_of_lt hcKpos) hlogT0
  have hpow : (Real.log T) ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3)
        * (Real.log T) ^ ((4 : ℝ) / 3) = (Real.log T) ^ (4 : ℝ) := by
    rw [← Real.rpow_add hlogTpos (4 / 3) (4 / 3),
      ← Real.rpow_add hlogTpos (4 / 3 + 4 / 3) (4 / 3)]
    norm_num
  have hlogTL0' : 0 ≤ Real.log (T + A * Real.log (A * T)) :=
    Real.log_nonneg (by have h := mul_nonneg (le_of_lt hApos) hlogAT0; linarith)
  have hlogK2 : 0 ≤ Real.log (K + 2) := Real.log_nonneg (by linarith)
  calc (Real.log (A * T)) ^ ((4 : ℝ) / 3) *
        (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3) *
        (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
      = (Real.log (A * T)) ^ ((4 : ℝ) / 3) *
        ((Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3) *
         (Real.log (K + 2)) ^ ((4 : ℝ) / 3)) := by ring
    _ ≤ (cA ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3)) *
        ((cT ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3)) *
         (cK ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3))) := by
        gcongr
    _ = cA ^ ((4 : ℝ) / 3) * cT ^ ((4 : ℝ) / 3) * cK ^ ((4 : ℝ) / 3)
        * ((Real.log T) ^ ((4 : ℝ) / 3) * (Real.log T) ^ ((4 : ℝ) / 3)
           * (Real.log T) ^ ((4 : ℝ) / 3)) := by ring
    _ = cA ^ ((4 : ℝ) / 3) * cT ^ ((4 : ℝ) / 3) * cK ^ ((4 : ℝ) / 3) * (Real.log T) ^ (4 : ℝ) := by
        rw [hpow]
    _ ≤ cA ^ ((4 : ℝ) / 3) * cT ^ ((4 : ℝ) / 3) * cK ^ ((4 : ℝ) / 3) * (M * T ^ η) :=
        mul_le_mul_of_nonneg_left (hM T hT1) (by positivity)
    _ = cA ^ ((4 : ℝ) / 3) * cT ^ ((4 : ℝ) / 3) * cK ^ ((4 : ℝ) / 3) * M * T ^ η := by ring

/-- **Arithmetic of the wide detector integral.**  All polylogarithmic factors of the integral
count are absorbed into `T^ε`. -/
theorem wideIntegralArith :
    ∀ A ε Cg C4 CM : ℝ, 6 ≤ A → 0 < ε → 0 < Cg → 0 < C4 → 0 < CM →
      ∃ C : ℝ, 0 < C ∧ ∀ σ T K L : ℝ,
        1 / 2 < σ → 2 ≤ T → 1 ≤ K → K ≤ 6 * A ^ 2 * T ^ 3 → L = A * Real.log (A * T) →
        σ - 1 / 2 > 1 / (2 * Real.log (A * T)) →
        (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * L) ^ ((1 : ℝ) / 3) * (2 * L + 1) *
          (2 * C4 * (T + L)) ^ ((1 : ℝ) / 3) * (Real.log (T + L)) ^ ((4 : ℝ) / 3) *
          (CM * (T + L + K)) ^ ((2 : ℝ) / 3) * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
        ≤ C * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by
  intro A ε Cg C4 CM hA hε hCg hC4 hCM
  have hApos : 0 < A := by linarith
  have hA2nn : 0 ≤ A ^ 2 := sq_nonneg A
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨C1, hC1pos, hC1⟩ := sigmaFactorBound A Cg hA hCg
  obtain ⟨C2, hC2pos, hC2⟩ := LFactorBound A (ε / 2) hA hε2
  obtain ⟨C3, hC3pos, hC3⟩ := logFactorBound A (ε / 2) hA hε2
  have hbase3pos : 0 < 2 * C4 * (1 + A ^ 2) :=
    mul_pos (by linarith : (0 : ℝ) < 2 * C4) (by nlinarith [sq_nonneg A])
  have hbase5pos : 0 < CM * (1 + A ^ 2) :=
    mul_pos hCM (by nlinarith [sq_nonneg A])
  have hD3pos : 0 < (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hbase3pos _
  have hD5pos : 0 < (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hbase5pos _
  refine ⟨C1 * C2 * C3 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3)
      * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3),
    mul_pos (mul_pos (mul_pos (mul_pos hC1pos hC2pos) hC3pos) hD3pos) hD5pos, ?_⟩
  intro σ T K L hσ hT hK hKle hL hσb
  subst hL
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hTpos : 0 < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hATpos : 0 < A * T := by nlinarith
  have hAT1 : (1 : ℝ) ≤ A * T := by nlinarith
  have hlogAT0 : 0 ≤ Real.log (A * T) := Real.log_nonneg hAT1
  have hlogATle : Real.log (A * T) ≤ A * T := by
    have := Real.log_le_sub_one_of_pos hATpos; linarith
  have hTL : T + A * Real.log (A * T) ≤ (1 + A ^ 2) * T := by
    have h1 : A * Real.log (A * T) ≤ A * (A * T) :=
      mul_le_mul_of_nonneg_left hlogATle (le_of_lt hApos)
    nlinarith [h1]
  have hTL0 : 0 ≤ T + A * Real.log (A * T) := by
    have h := mul_nonneg (le_of_lt hApos) hlogAT0
    linarith
  have hTLK : T + A * Real.log (A * T) + K ≤ (1 + A ^ 2) * (T + K) := by
    have h2 : K ≤ (1 + A ^ 2) * K := by nlinarith [hK, hA2nn]
    nlinarith [hTL, h2]
  have hTLK0 : 0 ≤ T + A * Real.log (A * T) + K := by linarith
  have hTK0 : 0 ≤ T + K := by linarith
  have hF1 : (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3)
      ≤ C1 * (Real.log (A * T)) ^ ((4 : ℝ) / 3) := hC1 σ T hT hσ hσb
  have hF2 : (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1)
      ≤ C2 * T ^ (ε / 2) := hC2 T hT
  have hF3 : (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
      ≤ (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3) := by
    have hb : 0 ≤ 2 * C4 * (T + A * Real.log (A * T)) := mul_nonneg (by linarith) hTL0
    calc (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        ≤ (2 * C4 * ((1 + A ^ 2) * T)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hb (by nlinarith [hTL]) (by norm_num)
      _ = (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3) := by
          rw [show 2 * C4 * ((1 + A ^ 2) * T) = (2 * C4 * (1 + A ^ 2)) * T by ring,
            Real.mul_rpow (le_of_lt hbase3pos) (le_of_lt hTpos)]
  have hF5 : (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
      ≤ (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by
    have hb : 0 ≤ CM * (T + A * Real.log (A * T) + K) := mul_nonneg (le_of_lt hCM) hTLK0
    calc (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
        ≤ (CM * ((1 + A ^ 2) * (T + K))) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow hb (by nlinarith [hTLK]) (by norm_num)
      _ = (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by
          rw [show CM * ((1 + A ^ 2) * (T + K)) = (CM * (1 + A ^ 2)) * (T + K) by ring,
            Real.mul_rpow (le_of_lt hbase5pos) hTK0]
  have hP3 : (Real.log (A * T)) ^ ((4 : ℝ) / 3)
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3) ≤ C3 * T ^ (ε / 2) := hC3 T K hT hK hKle
  have hregroup :
      (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (2 * (A * Real.log (A * T)) + 1)
        * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
      = (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3)
        * ((2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1))
        * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3) := by ring
  have hmain :
      (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3)
        * ((2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1))
        * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
      ≤ (C1 * (Real.log (A * T)) ^ ((4 : ℝ) / 3)) * (C2 * T ^ (ε / 2))
        * ((2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3))
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * ((CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3))
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3) := by
    have hlogTL0 : 0 ≤ Real.log (T + A * Real.log (A * T)) :=
      Real.log_nonneg (by have h := mul_nonneg (le_of_lt hApos) hlogAT0; linarith)
    have hlogK20 : 0 ≤ Real.log (K + 2) := Real.log_nonneg (by linarith)
    have hAlog0 : 0 ≤ A * Real.log (A * T) := mul_nonneg (le_of_lt hApos) hlogAT0
    have hA2nn : 0 ≤ (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (2 * (A * Real.log (A * T)) + 1) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
    have hA3nn : 0 ≤ (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (mul_nonneg (by linarith) hTL0) _
    have hA4nn : 0 ≤ (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3) :=
      Real.rpow_nonneg hlogTL0 _
    have hA5nn : 0 ≤ (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg (mul_nonneg (le_of_lt hCM) hTLK0) _
    have hA6nn : 0 ≤ (Real.log (K + 2)) ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hlogK20 _
    have hB1nn : 0 ≤ C1 * (Real.log (A * T)) ^ ((4 : ℝ) / 3) :=
      mul_nonneg (le_of_lt hC1pos) (Real.rpow_nonneg hlogAT0 _)
    have hB2nn : 0 ≤ C2 * T ^ (ε / 2) :=
      mul_nonneg (le_of_lt hC2pos) (Real.rpow_nonneg (le_of_lt hTpos) _)
    have hB3nn : 0 ≤ (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hbase3pos) _)
        (Real.rpow_nonneg (le_of_lt hTpos) _)
    have hB5nn : 0 ≤ (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hbase5pos) _) (Real.rpow_nonneg hTK0 _)
    have h12 := mul_le_mul hF1 hF2 hA2nn hB1nn
    have h123 := mul_le_mul h12 hF3 hA3nn (mul_nonneg hB1nn hB2nn)
    have h1234 := mul_le_mul h123 (le_refl _) hA4nn (mul_nonneg (mul_nonneg hB1nn hB2nn) hB3nn)
    have h12345 := mul_le_mul h1234 hF5 hA5nn
      (mul_nonneg (mul_nonneg (mul_nonneg hB1nn hB2nn) hB3nn) hA4nn)
    exact mul_le_mul h12345 (le_refl _) hA6nn
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB1nn hB2nn) hB3nn) hA4nn) hB5nn)
  have hTpow : T ^ (ε / 2) * T ^ (ε / 2) = T ^ ε := by
    rw [← Real.rpow_add hTpos (ε / 2) (ε / 2)]
    ring_nf
  have hbound :
      (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (2 * (A * Real.log (A * T)) + 1)
        * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
        * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
        * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
        * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
      ≤ C1 * C2 * C3 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3)
        * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * T ^ ε
        * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by
    calc (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3) * (2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
          * (2 * (A * Real.log (A * T)) + 1)
          * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
          * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
          * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
          * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)
        = (12 * Cg / (σ - 1 / 2)) ^ ((4 : ℝ) / 3)
          * ((2 * (A * Real.log (A * T))) ^ ((1 : ℝ) / 3) * (2 * (A * Real.log (A * T)) + 1))
          * (2 * C4 * (T + A * Real.log (A * T))) ^ ((1 : ℝ) / 3)
          * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
          * (CM * (T + A * Real.log (A * T) + K)) ^ ((2 : ℝ) / 3)
          * (Real.log (K + 2)) ^ ((4 : ℝ) / 3) := hregroup
      _ ≤ (C1 * (Real.log (A * T)) ^ ((4 : ℝ) / 3)) * (C2 * T ^ (ε / 2))
          * ((2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3))
          * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
          * ((CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3))
          * (Real.log (K + 2)) ^ ((4 : ℝ) / 3) := hmain
      _ = (C1 * C2 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3))
          * (T ^ (ε / 2) * T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3))
          * ((Real.log (A * T)) ^ ((4 : ℝ) / 3)
             * (Real.log (T + A * Real.log (A * T))) ^ ((4 : ℝ) / 3)
             * (Real.log (K + 2)) ^ ((4 : ℝ) / 3)) := by ring
      _ ≤ (C1 * C2 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3))
          * (T ^ (ε / 2) * T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) * (C3 * T ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left hP3 (by positivity)
      _ = (C1 * C2 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * C3)
          * (T ^ (ε / 2) * T ^ (ε / 2)) * T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by ring
      _ = (C1 * C2 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3) * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * C3)
          * T ^ ε * T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by rw [hTpow]
      _ = C1 * C2 * C3 * (2 * C4 * (1 + A ^ 2)) ^ ((1 : ℝ) / 3)
          * (CM * (1 + A ^ 2)) ^ ((2 : ℝ) / 3) * T ^ ε
          * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by ring
  exact hbound

end Work.ZeroDensity.Ingham.zetaDetectorBig
