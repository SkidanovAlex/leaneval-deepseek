import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Log

-- Elementary bound for the exponent bookkeeping of the wedge/compound box.
-- If the numbers `lam j` (`j < N`) are trapped in `[Q ^ (-K0), Q ^ K0]` at a base `Q ≥ 2`,
-- then the "exponent" of a compound entry
--   `(log (Kc * ∏ t ∈ T, lam t) + (extra gap factor)) / log Q + γ`
-- is bounded, in absolute value, by `log (Kc + Kc⁻¹) / log 2 + K0 * r + 2 * K0 + γ`,
-- where `r = #T` (achieved by bounding `|log Kc| ≤ log (Kc + Kc⁻¹)`, `log (lam (k-1)/lam k)`
-- by `± 2 K0 log Q`, and using `log 2 ≤ log Q`).
theorem log_box_bound {N r k : ℕ} (hk : k < N)
    {K0 Kc γ Q : ℝ} (hK0 : 0 < K0) (hKc : 0 < Kc) (hγ : 0 ≤ γ) (hQ : 2 ≤ Q)
    (lam : ℕ → ℝ) (hlam : ∀ j : ℕ, j < N → Q ^ (-K0) ≤ lam j ∧ lam j ≤ Q ^ K0)
    (T : Finset (Fin N)) (hT : T.card = r) :
    |(Real.log (Kc * ∏ t ∈ T, lam t.val) +
        (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
          Real.log (lam (k - 1) / lam k) else 0)) / Real.log Q + γ|
      ≤ Real.log (Kc + Kc⁻¹) / Real.log 2 + K0 * r + 2 * K0 + γ := by
  have hQpos : 0 < Q := by linarith
  have hQ1 : 1 < Q := by linarith
  have hLQ : 0 < Real.log Q := Real.log_pos hQ1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_le : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ
  -- positivity of `lam j`
  have hlam_pos : ∀ j : ℕ, j < N → 0 < lam j := fun j hj =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hQpos (-K0)) (hlam j hj).1
  -- per-element absolute bound on the logarithms
  have hbound : ∀ j : ℕ, j < N → |Real.log (lam j)| ≤ K0 * Real.log Q := by
    intro j hj
    have h := hlam j hj
    have hlo : -(K0 * Real.log Q) ≤ Real.log (lam j) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hQpos (-K0)) h.1
      rw [Real.log_rpow hQpos] at h1
      have heq : (-K0) * Real.log Q = -(K0 * Real.log Q) := by ring
      linarith [h1, heq]
    have hhi : Real.log (lam j) ≤ K0 * Real.log Q := by
      have h1 := Real.log_le_log (hlam_pos j hj) h.2
      rwa [Real.log_rpow hQpos] at h1
    exact abs_le.mpr ⟨hlo, hhi⟩
  -- product bound
  have hPpos : 0 < ∏ t ∈ T, lam t.val :=
    Finset.prod_pos (fun t _ => hlam_pos t.val t.isLt)
  have hPbound : |Real.log (∏ t ∈ T, lam t.val)| ≤ r * (K0 * Real.log Q) := by
    rw [Real.log_prod (fun t _ => ne_of_gt (hlam_pos t.val t.isLt))]
    calc |∑ t ∈ T, Real.log (lam t.val)|
        ≤ ∑ t ∈ T, |Real.log (lam t.val)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ T, K0 * Real.log Q := by
            exact Finset.sum_le_sum (fun t _ => hbound t.val t.isLt)
      _ = T.card * (K0 * Real.log Q) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = r * (K0 * Real.log Q) := by rw [hT]
  -- `|log Kc| ≤ log (Kc + Kc⁻¹)`
  have hlogKc : |Real.log Kc| ≤ Real.log (Kc + Kc⁻¹) := by
    have hcinv : 0 < Kc⁻¹ := inv_pos.mpr hKc
    rw [abs_le]
    refine ⟨?_, Real.log_le_log hKc (le_add_of_nonneg_right hcinv.le)⟩
    have h1 := Real.log_le_log hcinv (le_add_of_nonneg_left hKc.le)
    rw [Real.log_inv] at h1
    linarith
  -- `0 ≤ log (Kc + Kc⁻¹)`
  have hKcadd_nonneg : 0 ≤ Real.log (Kc + Kc⁻¹) := by
    apply Real.log_nonneg
    rcases le_total 1 Kc with h | h
    · have : 0 ≤ Kc⁻¹ := inv_nonneg.mpr hKc.le
      linarith
    · have : (1:ℝ) ≤ Kc⁻¹ := (one_le_inv₀ hKc).mpr h
      linarith
  -- `k - 1 < N`
  have hkm1 : k - 1 < N := by
    cases k with
    | zero => simpa using hk
    | succ m => exact Nat.lt_of_succ_lt hk
  -- extra gap-factor bound
  have hEbound :
      |(if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
          Real.log (lam (k - 1) / lam k) else 0)| ≤ 2 * K0 * Real.log Q := by
    by_cases hTeq : T = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
    · rw [if_pos hTeq]
      have hdiv : Real.log (lam (k - 1) / lam k)
          = Real.log (lam (k - 1)) - Real.log (lam k) :=
        Real.log_div (ne_of_gt (hlam_pos (k-1) hkm1)) (ne_of_gt (hlam_pos k hk))
      rw [hdiv]
      calc
        |Real.log (lam (k - 1)) - Real.log (lam k)|
            ≤ |Real.log (lam (k - 1))| + |Real.log (lam k)| := by
              simpa using abs_sub_le (Real.log (lam (k - 1))) 0 (Real.log (lam k))
        _ ≤ K0 * Real.log Q + K0 * Real.log Q :=
              add_le_add (hbound (k-1) hkm1) (hbound k hk)
        _ = 2 * K0 * Real.log Q := by ring
    · rw [if_neg hTeq, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hK0.le) hLQ.le
  -- bound on the numerator
  have hA :
      |Real.log (Kc * ∏ t ∈ T, lam t.val) +
          (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
            Real.log (lam (k - 1) / lam k) else 0)|
        ≤ Real.log (Kc + Kc⁻¹) + (K0 * r + 2 * K0) * Real.log Q := by
    have h1 : |Real.log (Kc * ∏ t ∈ T, lam t.val)|
        ≤ Real.log (Kc + Kc⁻¹) + r * (K0 * Real.log Q) := by
      rw [Real.log_mul (ne_of_gt hKc) (ne_of_gt hPpos)]
      calc |Real.log Kc + Real.log (∏ t ∈ T, lam t.val)|
          ≤ |Real.log Kc| + |Real.log (∏ t ∈ T, lam t.val)| := by exact abs_add_le _ _
        _ ≤ Real.log (Kc + Kc⁻¹) + r * (K0 * Real.log Q) := by exact add_le_add hlogKc hPbound
    calc
      |Real.log (Kc * ∏ t ∈ T, lam t.val) +
          (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
            Real.log (lam (k - 1) / lam k) else 0)|
          ≤ |Real.log (Kc * ∏ t ∈ T, lam t.val)| +
            |(if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
                Real.log (lam (k - 1) / lam k) else 0)| := by exact abs_add_le _ _
        _ ≤ (Real.log (Kc + Kc⁻¹) + r * (K0 * Real.log Q)) + 2 * K0 * Real.log Q := by
              exact add_le_add h1 hEbound
        _ = Real.log (Kc + Kc⁻¹) + (K0 * r + 2 * K0) * Real.log Q := by ring
  -- final assembly
  have step1 :
      |(Real.log (Kc * ∏ t ∈ T, lam t.val) +
          (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
            Real.log (lam (k - 1) / lam k) else 0)) / Real.log Q + γ|
        ≤ |Real.log (Kc * ∏ t ∈ T, lam t.val) +
            (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
              Real.log (lam (k - 1) / lam k) else 0)| / Real.log Q + γ := by
    calc
      |(Real.log (Kc * ∏ t ∈ T, lam t.val) +
          (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
            Real.log (lam (k - 1) / lam k) else 0)) / Real.log Q + γ|
          ≤ |(Real.log (Kc * ∏ t ∈ T, lam t.val) +
              (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
                Real.log (lam (k - 1) / lam k) else 0)) / Real.log Q| + |γ| := by
                exact abs_add_le _ _
        _ = |Real.log (Kc * ∏ t ∈ T, lam t.val) +
              (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
                Real.log (lam (k - 1) / lam k) else 0)| / Real.log Q + γ := by
              rw [abs_div, abs_of_pos hLQ, abs_of_nonneg hγ]
  have step3 :
      (Real.log (Kc + Kc⁻¹) + (K0 * r + 2 * K0) * Real.log Q) / Real.log Q
        = Real.log (Kc + Kc⁻¹) / Real.log Q + (K0 * r + 2 * K0) := by
    rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hLQ)]
  have step4 : Real.log (Kc + Kc⁻¹) / Real.log Q ≤ Real.log (Kc + Kc⁻¹) / Real.log 2 :=
    div_le_div_of_nonneg_left hKcadd_nonneg hlog2 hlog2_le
  calc
    |(Real.log (Kc * ∏ t ∈ T, lam t.val) +
        (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
          Real.log (lam (k - 1) / lam k) else 0)) / Real.log Q + γ|
        ≤ |Real.log (Kc * ∏ t ∈ T, lam t.val) +
            (if T = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
              Real.log (lam (k - 1) / lam k) else 0)| / Real.log Q + γ := by exact step1
      _ ≤ (Real.log (Kc + Kc⁻¹) + (K0 * r + 2 * K0) * Real.log Q) / Real.log Q + γ := by
            exact add_le_add_left (div_le_div_of_nonneg_right hA hLQ.le) γ
      _ = Real.log (Kc + Kc⁻¹) / Real.log Q + (K0 * r + 2 * K0) + γ := by rw [step3]
      _ ≤ Real.log (Kc + Kc⁻¹) / Real.log 2 + (K0 * r + 2 * K0) + γ := by
            exact add_le_add_left (add_le_add_left step4 (K0 * r + 2 * K0)) γ
      _ = Real.log (Kc + Kc⁻¹) / Real.log 2 + K0 * r + 2 * K0 + γ := by ring

end Commons.Analysis.Log