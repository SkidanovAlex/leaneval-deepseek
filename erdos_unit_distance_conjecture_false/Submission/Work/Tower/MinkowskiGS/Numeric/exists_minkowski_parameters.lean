import Mathlib
import Submission.Work.Defs.Basic

set_option maxHeartbeats 800000

open scoped Topology
open Filter

namespace Work.Tower.MinkowskiGS.Numeric

/-- Analytic crux: for every positive `c` and constants `d e`, the expression
`d * ℓ * log ℓ + e` is eventually bounded above by `c * ℓ ^ 2`.

This packages the fact that `ℓ * log ℓ = o(ℓ ^ 2)` at infinity, in exactly the
form needed to select the parameters `ℓ`, `t`, `C` of the Minkowski argument. -/
lemma eventually_log_mul_lt_sq (c : ℝ) (hc : 0 < c) (d e : ℝ) :
    ∀ᶠ ℓ : ℕ in Filter.atTop, d * ℓ * Real.log ℓ + e < c * ℓ ^ 2 := by
  have hlog : Filter.Tendsto (fun ℓ : ℕ => Real.log ℓ / ℓ) Filter.atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_id_atTop.comp_tendsto
      tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
    simpa using h
  have hsq : Filter.Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun ℓ : ℕ => e / ℓ ^ 2) Filter.atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hsq).const_mul e
    simpa [div_eq_mul_inv] using h
  have hsum : ∀ᶠ ℓ : ℕ in Filter.atTop, d * (Real.log ℓ / ℓ) + e / ℓ ^ 2 < c := by
    have h1 : Filter.Tendsto (fun ℓ : ℕ => d * (Real.log ℓ / ℓ)) Filter.atTop (𝓝 (d * 0)) :=
      hlog.const_mul d
    have h3 : Filter.Tendsto (fun ℓ : ℕ => d * (Real.log ℓ / ℓ) + e / ℓ ^ 2)
        Filter.atTop (𝓝 (d * 0 + 0)) := h1.add h2
    have hlt : ∀ᶠ y in 𝓝 (d * 0 + 0), y < c := Iio_mem_nhds (by simpa using hc)
    exact h3.eventually hlt
  filter_upwards [Filter.eventually_ge_atTop 1, hsum] with ℓ hℓ hsumℓ
  have hpos : (0 : ℝ) < ℓ ^ 2 := by positivity
  have hmul := mul_lt_mul_of_pos_right hsumℓ hpos
  have heq : (d * (Real.log ℓ / ℓ) + e / ℓ ^ 2) * ℓ ^ 2 = d * ℓ * Real.log ℓ + e := by
    field_simp
  rw [heq] at hmul
  exact hmul

/-- Elementary numerical bound: for `0 < a`, `1 ≤ ℓ` and `0 ≤ log ℓ` we have
`1 + a * (ℓ * log ℓ) ≤ (1 + a) * ℓ ^ 2`. -/
lemma one_add_mul_log_le (a ℓ : ℝ) (ha : 0 < a) (hℓ : 1 ≤ ℓ) (_hlog : 0 ≤ Real.log ℓ) :
    1 + a * (ℓ * Real.log ℓ) ≤ (1 + a) * ℓ ^ 2 := by
  have hlog_le : Real.log ℓ ≤ ℓ := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ℓ by linarith)
    linarith only [h, hℓ]
  have h1 : a * (ℓ * Real.log ℓ) ≤ a * ℓ ^ 2 := by
    have h' : (a * ℓ) * Real.log ℓ ≤ (a * ℓ) * ℓ :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    nlinarith only [h']
  have h2 : (1 : ℝ) ≤ ℓ ^ 2 := by nlinarith only [hℓ]
  nlinarith only [h1, h2]

theorem exists_minkowski_parameters
    (C_A : ℝ) (hCA : 0 < C_A)
    (hap : ∀ ℓ : ℕ, ∃ r : Fin ℓ → ℕ, (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧
        (∀ i, r i % 3 = 1) ∧ (∑ i, Real.log (r i : ℝ)) ≤ C_A * (ℓ : ℝ) * Real.log ℓ + C_A)
    (C_M : ℝ) (hCM : 0 < C_M) (H : ℝ) (hH : 0 < H) :
    ∃ (ℓ : ℕ) (r : Fin ℓ → ℕ) (t : ℕ) (C : ℝ),
      (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧ (∀ i, r i % 3 = 1) ∧
      0 < ℓ ∧ 0 < t ∧ 1 ≤ C ∧
      C = max 1 (2 * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))) ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      t = ((ℓ - 1) ^ 2) / 100 ∧
      ∀ dimCl : ℕ,
        (dimCl : ℝ) ≤ 3 * Real.logb 3 (C_M * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) *
          (1 + Real.log (Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))))) →
        (((ℓ - 1 : ℕ) : ℝ)) ^ 2 > 4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ)) := by
  -- Abbreviations.
  set a : ℝ := (2 / 3) * C_A with ha_def
  have hapos : 0 < a := by rw [ha_def]; positivity
  set K : ℝ := 2 * Real.exp a with hK_def
  have hKge2 : 2 ≤ K := by
    rw [hK_def]
    have h1 : 1 ≤ Real.exp a := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (le_of_lt hapos)
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKge2
  set L : ℝ := max 1 (1 + Real.log K) with hL_def
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLupper : 1 + Real.log K ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  set P : ℝ := H ^ 2 * K ^ 2 * L ^ 2 * (1 + a) ^ 2 with hP_def
  have hPpos : 0 < P := by rw [hP_def]; positivity
  -- The two eventual inequalities that determine how large `ℓ` must be.
  have hlog2pos : 0 < Real.log 2 / 200 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hev2 := eventually_log_mul_lt_sq (Real.log 2 / 200) hlog2pos (2 * a + 4) (Real.log (2 * P))
  have hev3 := eventually_log_mul_lt_sq (11 / 25) (by norm_num) (24 * a) (12 * C_M + 24 * a + 8)
  have hmain : ∀ᶠ ℓ : ℕ in Filter.atTop,
      11 ≤ ℓ ∧
      Real.log (2 * P) + 4 * Real.log ℓ + 2 * a * ℓ * Real.log ℓ < (Real.log 2 / 200) * ℓ ^ 2 ∧
      24 * a * ℓ * Real.log ℓ + (12 * C_M + 24 * a + 8) < (11 / 25) * ℓ ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 11, hev2, hev3] with ℓ h11 h2 h3
    refine ⟨h11, ?_, h3⟩
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
    have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
    have h4 : 4 * Real.log ℓ ≤ 4 * (ℓ * Real.log ℓ) := by
      have := mul_le_mul_of_nonneg_left hℓ1 hlogℓ
      nlinarith only [this]
    nlinarith only [h2, h4]
  obtain ⟨ℓ, h11, h2, h3⟩ := hmain.exists
  obtain ⟨r, hrp, hri, hrm, hrsum⟩ := hap ℓ
  set S : ℝ := ∑ i, Real.log (r i : ℝ) with hS_def
  have hSnn : 0 ≤ S := by
    rw [hS_def]
    apply Finset.sum_nonneg
    intro i _
    apply Real.log_nonneg
    have : 1 ≤ r i := by have h := (hrp i).two_le; omega
    exact_mod_cast this
  have hSle : S ≤ C_A * (ℓ : ℝ) * Real.log ℓ + C_A := by simpa only [hS_def] using hrsum
  have hSa : (2 / 3) * S ≤ a * (ℓ * Real.log ℓ) + a := by
    have h := mul_le_mul_of_nonneg_left hSle (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [ha_def]
    nlinarith only [h]
  set t : ℕ := (ℓ - 1) ^ 2 / 100 with ht_def
  set C : ℝ := max 1 (2 * Real.exp ((2 / 3) * S)) with hC_def
  have hE1 : 1 ≤ Real.exp ((2 / 3) * S) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hCeq : C = 2 * Real.exp ((2 / 3) * S) := by
    rw [hC_def]
    exact max_eq_right (by linarith)
  have hCpos : 0 < C := by rw [hCeq]; positivity
  have hC1 : 1 ≤ C := by rw [hCeq]; nlinarith only [hE1]
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
  have hℓ4 : (4 : ℝ) ≤ ℓ := by exact_mod_cast (show 4 ≤ ℓ by omega)
  have hlogℓ_nn : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have htpos : 0 < t := by
    rw [ht_def]
    apply Nat.div_pos
    · have h10 : 10 ≤ ℓ - 1 := by omega
      calc (100 : ℕ) = 10 * 10 := by norm_num
        _ ≤ (ℓ - 1) * (ℓ - 1) := Nat.mul_le_mul h10 h10
        _ = (ℓ - 1) ^ 2 := by ring
    · norm_num
  -- Bound on `C` and on `log C`.
  have hexp_bound : C ≤ K * Real.exp (a * (ℓ * Real.log ℓ)) := by
    have hexp : Real.exp ((2 / 3) * S) ≤ Real.exp (a * (ℓ * Real.log ℓ) + a) :=
      Real.exp_le_exp.mpr (by linarith only [hSa])
    calc C = 2 * Real.exp ((2 / 3) * S) := hCeq
      _ ≤ 2 * Real.exp (a * (ℓ * Real.log ℓ) + a) := by linarith only [hexp]
      _ = 2 * (Real.exp (a * (ℓ * Real.log ℓ)) * Real.exp a) := by rw [Real.exp_add]
      _ = K * Real.exp (a * (ℓ * Real.log ℓ)) := by rw [hK_def]; ring
  have hlogC : Real.log C ≤ Real.log K + a * (ℓ * Real.log ℓ) := by
    have h := Real.log_le_log hCpos hexp_bound
    rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h
    exact h
  have hu_nn : 0 ≤ a * (ℓ * Real.log ℓ) :=
    mul_nonneg (le_of_lt hapos) (mul_nonneg (by positivity) hlogℓ_nn)
  have h1logCpos : 0 ≤ 1 + Real.log C := by
    have h := Real.log_nonneg hC1; linarith only [h]
  have h1logC : 1 + Real.log C ≤ L * (1 + a * (ℓ * Real.log ℓ)) := by
    nlinarith only [hlogC, hLupper, hL1, hu_nn]
  have hA_nn : 0 ≤ H * C * (1 + Real.log C) :=
    mul_nonneg (mul_nonneg (le_of_lt hH) (le_of_lt hCpos)) h1logCpos
  have hstep : H * C * (1 + Real.log C) ≤
      H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ))) := by
    have h1 : C * (1 + Real.log C) ≤
        (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ))) :=
      mul_le_mul hexp_bound h1logC h1logCpos (by positivity)
    calc H * C * (1 + Real.log C) = H * (C * (1 + Real.log C)) := by ring
      _ ≤ H * ((K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ)))) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hH)
      _ = H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ))) := by ring
  have hsqH : (H * C * (1 + Real.log C)) ^ 2 ≤
      (H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ)))) ^ 2 :=
    pow_le_pow_left₀ hA_nn hstep 2
  -- Monotonicity of `(1 + u) ^ 2` in `u`.
  have h1u : 1 + a * (ℓ * Real.log ℓ) ≤ (1 + a) * ℓ ^ 2 :=
    one_add_mul_log_le a ℓ hapos hℓ1 hlogℓ_nn
  have hu2_nn : 0 ≤ 1 + a * (ℓ * Real.log ℓ) := by linarith only [hu_nn]
  have hsq1u : (1 + a * (ℓ * Real.log ℓ)) ^ 2 ≤ ((1 + a) * ℓ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hu2_nn h1u 2
  have hexp2 : (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2 = Real.exp (2 * (a * (ℓ * Real.log ℓ))) := by
    rw [show 2 * (a * (ℓ * Real.log ℓ)) = a * (ℓ * Real.log ℓ) + a * (ℓ * Real.log ℓ) by ring,
      Real.exp_add]
    ring
  have hmid : (H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ)))) ^ 2
      ≤ P * Real.exp (2 * (a * (ℓ * Real.log ℓ))) * ℓ ^ 4 := by
    have hnonneg : 0 ≤ H ^ 2 * K ^ 2 * L ^ 2 := by positivity
    have hstep2 : H ^ 2 * K ^ 2 * L ^ 2 * (1 + a * (ℓ * Real.log ℓ)) ^ 2
          * (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2
        ≤ H ^ 2 * K ^ 2 * L ^ 2 * ((1 + a) * ℓ ^ 2) ^ 2
          * (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsq1u hnonneg
    calc (H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ)))) ^ 2
        = H ^ 2 * K ^ 2 * L ^ 2 * (1 + a * (ℓ * Real.log ℓ)) ^ 2
            * (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2 := by ring
      _ ≤ H ^ 2 * K ^ 2 * L ^ 2 * ((1 + a) * ℓ ^ 2) ^ 2
            * (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2 := hstep2
      _ = H ^ 2 * K ^ 2 * L ^ 2 * (1 + a) ^ 2 * ℓ ^ 4
            * (Real.exp (a * (ℓ * Real.log ℓ))) ^ 2 := by ring
      _ = P * Real.exp (2 * (a * (ℓ * Real.log ℓ))) * ℓ ^ 4 := by rw [hP_def, hexp2]; ring
  -- Turn the product bound into an exponential bound.
  have hexp4 : Real.exp (4 * Real.log ℓ) = ℓ ^ 4 := by
    have h4log : (4 : ℝ) * Real.log ℓ = Real.log (ℓ ^ 4) := by
      rw [Real.log_pow]; push_cast; ring
    rw [h4log, Real.exp_log (by positivity : (0 : ℝ) < ℓ ^ 4)]
  have hPexp : P * Real.exp (2 * (a * (ℓ * Real.log ℓ))) * ℓ ^ 4
      = Real.exp (Real.log P + 2 * (a * (ℓ * Real.log ℓ)) + 4 * Real.log ℓ) := by
    calc P * Real.exp (2 * (a * (ℓ * Real.log ℓ))) * ℓ ^ 4
        = Real.exp (Real.log P) * Real.exp (2 * (a * (ℓ * Real.log ℓ)))
            * Real.exp (4 * Real.log ℓ) := by rw [Real.exp_log hPpos, hexp4]
      _ = Real.exp (Real.log P + 2 * (a * (ℓ * Real.log ℓ)) + 4 * Real.log ℓ) := by
            rw [Real.exp_add, Real.exp_add]
  have h2' : Real.log P + 2 * (a * (ℓ * Real.log ℓ)) + 4 * Real.log ℓ
      < (Real.log 2 / 200) * ℓ ^ 2 - Real.log 2 := by
    have hlog2P : Real.log (2 * P) = Real.log 2 + Real.log P :=
      Real.log_mul (by norm_num) (ne_of_gt hPpos)
    have h2u : 2 * (a * (ℓ * Real.log ℓ)) = 2 * a * ℓ * Real.log ℓ := by ring
    rw [h2u]
    nlinarith only [h2, hlog2P]
  have hexp_lt : Real.exp (Real.log P + 2 * (a * (ℓ * Real.log ℓ)) + 4 * Real.log ℓ)
      < Real.exp ((Real.log 2 / 200) * ℓ ^ 2 - Real.log 2) := Real.exp_lt_exp.mpr h2'
  have hexp_eq : Real.exp ((Real.log 2 / 200) * ℓ ^ 2 - Real.log 2)
      = (2 : ℝ) ^ ((ℓ : ℝ) ^ 2 / 200 - 1) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hm1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ ℓ by omega)]
    norm_num
  have hn100 : ((ℓ - 1) ^ 2 : ℕ) < 100 * (t + 1) := by
    rw [ht_def]; omega
  have hn100R : ((ℓ : ℝ) - 1) ^ 2 < 100 * ((t : ℝ) + 1) := by
    have h3 : (((ℓ - 1) ^ 2 : ℕ) : ℝ) < ((100 * (t + 1) : ℕ) : ℝ) := by exact_mod_cast hn100
    rw [Nat.cast_pow, hm1] at h3
    push_cast at h3
    exact h3
  have ht_lb : ((ℓ : ℝ) - 1) ^ 2 / 100 - 1 < (t : ℝ) := by linarith only [hn100R]
  have hge200 : (ℓ : ℝ) ^ 2 / 200 ≤ ((ℓ : ℝ) - 1) ^ 2 / 100 := by nlinarith only [hℓ4]
  have ht_gt : (ℓ : ℝ) ^ 2 / 200 - 1 < (t : ℝ) := by linarith only [ht_lb, hge200]
  have h2t : (2 : ℝ) ^ ((ℓ : ℝ) ^ 2 / 200 - 1) < (2 : ℝ) ^ t := by
    rw [← Real.rpow_natCast 2 t]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ht_gt
  have hfinalA : (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t := by
    calc (H * C * (1 + Real.log C)) ^ 2
        ≤ (H * (K * Real.exp (a * (ℓ * Real.log ℓ))) * (L * (1 + a * (ℓ * Real.log ℓ)))) ^ 2 :=
          hsqH
      _ ≤ P * Real.exp (2 * (a * (ℓ * Real.log ℓ))) * ℓ ^ 4 := hmid
      _ = Real.exp (Real.log P + 2 * (a * (ℓ * Real.log ℓ)) + 4 * Real.log ℓ) := hPexp
      _ < Real.exp ((Real.log 2 / 200) * ℓ ^ 2 - Real.log 2) := hexp_lt
      _ = (2 : ℝ) ^ ((ℓ : ℝ) ^ 2 / 200 - 1) := hexp_eq
      _ < (2 : ℝ) ^ t := h2t
  -- The dimension constraint.
  have hB : ∀ dimCl : ℕ,
      (dimCl : ℝ) ≤ 3 * Real.logb 3 (C_M * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) *
        (1 + Real.log (Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))))) →
      (((ℓ - 1 : ℕ) : ℝ)) ^ 2 > 4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ)) := by
    intro dimCl hdim
    rw [← hS_def] at hdim
    set G : ℝ := C_M * Real.exp ((2 / 3) * S) * (1 + Real.log (Real.exp ((2 / 3) * S)))
      with hG_def
    have hlogE : Real.log (Real.exp ((2 / 3) * S)) = (2 / 3) * S := Real.log_exp _
    have hpos1 : 0 < 1 + Real.log (Real.exp ((2 / 3) * S)) := by rw [hlogE]; linarith only [hSnn]
    have hGpos : 0 < G := by
      rw [hG_def]
      positivity
    set M : ℝ := C_M + 2 * (a * (ℓ * Real.log ℓ) + a) with hM_def
    have hlogG : Real.log G ≤ M := by
      rw [hM_def, hG_def]
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hCM) (ne_of_gt (Real.exp_pos _))) (ne_of_gt hpos1),
          Real.log_mul (ne_of_gt hCM) (ne_of_gt (Real.exp_pos _)), hlogE]
      have h1 : Real.log C_M ≤ C_M := by
        have := Real.log_le_sub_one_of_pos hCM
        linarith only [this]
      have h3 : Real.log (1 + (2 / 3) * S) ≤ a * (ℓ * Real.log ℓ) + a := by
        have hp : 0 < 1 + (2 / 3) * S := by linarith only [hSnn]
        calc Real.log (1 + (2 / 3) * S) ≤ (1 + (2 / 3) * S) - 1 := Real.log_le_sub_one_of_pos hp
          _ = (2 / 3) * S := by ring
          _ ≤ a * (ℓ * Real.log ℓ) + a := hSa
      linarith only [h1, h3, hSa]
    have hlog3 : 1 < Real.log 3 := by
      have h : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
      rwa [Real.log_exp] at h
    have hdim_le : (dimCl : ℝ) ≤ 3 * M := by
      rcases le_or_gt 0 (Real.log G) with hG0 | hG0
      · have hlogb_le : Real.logb 3 G ≤ Real.log G := by
          rw [Real.logb]
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 3)]
          nlinarith only [hlog3, hG0]
        linarith only [hdim, hlogb_le, hlogG]
      · exfalso
        have hneg : Real.logb 3 G < 0 := by
          rw [Real.logb]
          exact div_neg_of_neg_of_pos hG0 (by linarith)
        have h0 : (0 : ℝ) ≤ (dimCl : ℝ) := Nat.cast_nonneg _
        linarith only [hdim, hneg, h0]
    have htle : (t : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) ^ 2 / 100 := by
      have h1 : (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) ≤ ((ℓ - 1) ^ 2 : ℕ) / 100 := Nat.cast_div_le
      have h2 : (((ℓ - 1) ^ 2 : ℕ) : ℝ) = ((ℓ - 1 : ℕ) : ℝ) ^ 2 := by rw [Nat.cast_pow]
      rw [ht_def]
      linarith only [h1, h2]
    have hXge : (ℓ : ℝ) ^ 2 / 2 ≤ ((ℓ - 1 : ℕ) : ℝ) ^ 2 := by
      rw [hm1]
      nlinarith only [hℓ4]
    have hD : 12 * M + 8 < (88 / 100) * ((ℓ - 1 : ℕ) : ℝ) ^ 2 := by
      have hMeq : 12 * M + 8 = 24 * a * ℓ * Real.log ℓ + 12 * C_M + 24 * a + 8 := by
        rw [hM_def]; ring
      rw [hMeq]
      have h6 : (88 / 100) * ((ℓ - 1 : ℕ) : ℝ) ^ 2 ≥ (11 / 25) * (ℓ : ℝ) ^ 2 := by
        nlinarith only [hXge]
      linarith only [h3, h6]
    have hfinalB : 4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ))
        ≤ 12 * M + 8 + (12 / 100) * ((ℓ - 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hdim_le, htle]
    have hXeq : ((ℓ - 1 : ℕ) : ℝ) ^ 2
        = (88 / 100) * ((ℓ - 1 : ℕ) : ℝ) ^ 2 + (12 / 100) * ((ℓ - 1 : ℕ) : ℝ) ^ 2 := by ring
    linarith only [hfinalB, hD, hXeq]
  exact ⟨ℓ, r, t, C, hrp, hri, hrm, by omega, htpos, hC1,
    by rw [hC_def, hS_def], hfinalA, by rw [ht_def], hB⟩

end Work.Tower.MinkowskiGS.Numeric
