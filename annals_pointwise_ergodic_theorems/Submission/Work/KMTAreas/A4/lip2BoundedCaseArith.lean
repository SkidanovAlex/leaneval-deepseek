import Mathlib

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

/-- A pure real-arithmetic lemma: the constraints

* `0 < ε ≤ 1`, `ε ^ (-K') ≤ M`,
* `0 < S ≤ L`,
* `L < Cip * (S / L) ^ (-Kip)`,
* `ε * M / CB ≤ S`, `L ≤ CB * M`

(with `K' > max Kip 1`, `Kip > 0`, `Cip > 0`, `CB > 0`) force `M` to be bounded by a constant
depending only on `Cip`, `Kip`, `CB`, `K'`.

Proof sketch: put `σ = S/L ∈ (0,1]`.  Multiplying the `Lip` inequality by `σ ^ Kip` gives
`L * σ ^ Kip < Cip`; combining with `ε M / CB ≤ S = σ L` and `ε ^ (-K') ≤ M` yields
`ε ^ (1 - K') < CB * Cip * σ ^ (1 - Kip)`, while `L ≤ CB * M ≤ CB ^ 2 * S / ε` gives
`ε ≤ CB ^ 2 * σ`.  Finally `M ≤ CB * S / ε < CB * Cip * σ ^ (1 - Kip) / ε`.
Taking logarithms (`α = log ε⁻¹ ≥ 0`, `β = log σ⁻¹ ≥ 0`) the two relations become the linear
system `(K'-1) α < log (CB*Cip) + (Kip-1) β` and `β ≤ α + 2 log CB`, which bounds
`α` and hence `log M`; exponentiating gives the constant. -/
theorem lip2BoundedCaseArith (Cip Kip CB K' : ℝ) (hCip : 0 < Cip) (hKip : 0 < Kip) (hCB : 0 < CB) (hK' : max Kip 1 < K') : ∃ Λ : ℝ, 0 < Λ ∧ ∀ (M ε L S : ℝ), 0 < ε → ε ≤ 1 → ε ^ (-K') ≤ M → 0 < L → 0 < S → S ≤ L → L < Cip * (S / L) ^ (-Kip) → ε * M / CB ≤ S → L ≤ CB * M → M ≤ Λ := by
  have hKip_lt : Kip < K' := lt_of_le_of_lt (le_max_left Kip 1) hK'
  have h1_lt : (1 : ℝ) < K' := lt_of_le_of_lt (le_max_right Kip 1) hK'
  have hK'pos : (0 : ℝ) < K' := by linarith
  have hKm1 : (0 : ℝ) < K' - 1 := by linarith
  have hKsub : (0 : ℝ) < K' - Kip := by linarith
  set P : ℝ := CB * Cip with hPdef
  have hPpos : 0 < P := by rw [hPdef]; exact mul_pos hCB hCip
  set X1 : ℝ := Real.log P + Real.log P / (K' - 1) with hX1def
  set Q : ℝ := (Real.log P + 2 * (Kip - 1) * Real.log CB) / (K' - Kip) with hQdef
  set X2 : ℝ := Real.log P + Kip * Q + 2 * (Kip - 1) * Real.log CB with hX2def
  set X : ℝ := max X1 X2 with hXdef
  refine ⟨Real.exp X + 1, by positivity, ?_⟩
  intro M ε L S hε hε1 hMε hL hS hSL hLip hSM hLM
  have hMpos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hε (-K')) hMε
  set σ : ℝ := S / L with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact div_pos hS hL
  have hσle : σ ≤ 1 := by
    rw [hσdef, div_le_one hL]
    exact hSL
  have hSeq : S = σ * L := by
    rw [hσdef]
    exact (div_mul_cancel₀ S (ne_of_gt hL)).symm
  -- multiply the `Lip` inequality by `σ ^ Kip`
  have hLipσ : L * σ ^ Kip < Cip := by
    have hpos : 0 < σ ^ Kip := Real.rpow_pos_of_pos hσpos Kip
    have h2 := mul_lt_mul_of_pos_right hLip hpos
    have hcancel : σ ^ (-Kip) * σ ^ Kip = 1 := by
      rw [← Real.rpow_add hσpos]
      simp
    nlinarith [h2, hcancel]
  have hLbound : L < Cip * σ ^ (-Kip) := by
    have hpos : 0 < σ ^ Kip := Real.rpow_pos_of_pos hσpos Kip
    have h5 : L < Cip * (σ ^ Kip)⁻¹ := (lt_div_iff₀ hpos).mpr hLipσ
    rwa [Real.rpow_neg hσpos.le Kip]
  -- `ε * M ≤ CB * S`
  have h1 : ε * M ≤ CB * S := by
    have h := hSM
    rw [div_le_iff₀ hCB] at h
    linarith
  have hM_le : M ≤ CB * S / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [h1]
  -- `ε ^ (1 - K') ≤ CB * S`
  have hA : ε ^ (1 - K') ≤ CB * S := by
    have h2 : ε ^ (-K') * ε ≤ M * ε := mul_le_mul_of_nonneg_right hMε hε.le
    have heq : ε ^ (-K') * ε = ε ^ (1 - K') := by
      have hh : ε ^ (-K') * ε ^ (1 : ℝ) = ε ^ (1 - K') := by
        rw [← Real.rpow_add hε]
        congr 1
        ring
      simpa using hh
    have h3 : M * ε ≤ CB * S := by nlinarith [h1]
    rw [heq] at h2
    linarith
  have hσmul : σ * σ ^ (-Kip) = σ ^ (1 - Kip) := by
    rw [Real.rpow_neg hσpos.le Kip, Real.rpow_sub hσpos, Real.rpow_one, div_eq_mul_inv]
  have h7 : CB * (σ * L) < P * σ ^ (1 - Kip) := by
    calc CB * (σ * L) < CB * (σ * (Cip * σ ^ (-Kip))) := by
          apply mul_lt_mul_of_pos_left _ hCB
          exact mul_lt_mul_of_pos_left hLbound hσpos
      _ = P * (σ * σ ^ (-Kip)) := by rw [hPdef]; ring
      _ = P * σ ^ (1 - Kip) := by rw [hσmul]
  -- `ε ^ (1 - K') < P * σ ^ (1 - Kip)`
  have hI : ε ^ (1 - K') < P * σ ^ (1 - Kip) := by
    have h8 : CB * S < P * σ ^ (1 - Kip) := by rw [hSeq]; exact h7
    linarith [hA, h8]
  -- `ε ≤ CB ^ 2 * σ`
  have hII : ε ≤ CB ^ 2 * σ := by
    have h8 : L ≤ CB * (CB * S / ε) := le_trans hLM (mul_le_mul_of_nonneg_left hM_le hCB.le)
    have h9 : CB * (CB * S / ε) = CB ^ 2 * σ * L / ε := by
      rw [hSeq]; ring
    rw [h9, le_div_iff₀ hε] at h8
    have h10 : ε * L ≤ CB ^ 2 * σ * L := by linarith
    exact le_of_mul_le_mul_right h10 hL
  -- logarithmic change of variables
  set α : ℝ := Real.log ε⁻¹ with hαdef
  set β : ℝ := Real.log σ⁻¹ with hβdef
  have hlogε : Real.log ε = -α := by rw [hαdef, Real.log_inv]; ring
  have hlogσ : Real.log σ = -β := by rw [hβdef, Real.log_inv]; ring
  have hαnn : 0 ≤ α := by
    rw [hαdef]
    apply Real.log_nonneg
    rw [one_le_inv₀ hε]
    exact hε1
  have hβnn : 0 ≤ β := by
    rw [hβdef]
    apply Real.log_nonneg
    rw [one_le_inv₀ hσpos]
    exact hσle
  have hL1 : (K' - 1) * α < Real.log P + (Kip - 1) * β := by
    have h := Real.log_lt_log (by positivity) hI
    rw [Real.log_rpow hε,
        Real.log_mul (ne_of_gt hPpos) (ne_of_gt (Real.rpow_pos_of_pos hσpos (1 - Kip))),
        Real.log_rpow hσpos] at h
    rw [hlogε, hlogσ] at h
    linarith
  have hlogCB2 : Real.log (CB ^ 2) = 2 * Real.log CB := by
    rw [Real.log_pow]; norm_num
  have hL2 : β ≤ α + 2 * Real.log CB := by
    have h := Real.log_le_log hε hII
    rw [Real.log_mul (ne_of_gt (pow_pos hCB 2)) (ne_of_gt hσpos), hlogCB2] at h
    rw [hlogε, hlogσ] at h
    linarith
  have hL3 : Real.log M < Real.log P + (Kip - 1) * β + α := by
    have hbound : M < P * σ ^ (1 - Kip) / ε := by
      calc M ≤ CB * S / ε := hM_le
        _ = CB * (σ * L) / ε := by rw [hSeq]
        _ < P * σ ^ (1 - Kip) / ε := div_lt_div_of_pos_right h7 hε
    have h := Real.log_lt_log hMpos hbound
    rw [Real.log_div (ne_of_gt (mul_pos hPpos (Real.rpow_pos_of_pos hσpos (1 - Kip))))
          (ne_of_gt hε),
        Real.log_mul (ne_of_gt hPpos) (ne_of_gt (Real.rpow_pos_of_pos hσpos (1 - Kip))),
        Real.log_rpow hσpos] at h
    rw [hlogε, hlogσ] at h
    linarith
  by_cases hcase : Kip ≤ 1
  · -- case `Kip ≤ 1`
    have hβ' : (Kip - 1) * β ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hβnn
    have hlogM : Real.log M < X1 := by
      rw [hX1def]
      have hαb : α < Real.log P / (K' - 1) := by
        rw [lt_div_iff₀ hKm1]
        linarith [hL1, hβ']
      linarith [hL3, hβ']
    have hX1X : X1 ≤ X := by rw [hXdef]; exact le_max_left X1 X2
    have hexp : M < Real.exp X :=
      lt_of_lt_of_le ((Real.log_lt_iff_lt_exp hMpos).mp hlogM) (Real.exp_le_exp.mpr hX1X)
    exact le_trans (le_of_lt hexp) (le_add_of_nonneg_right zero_le_one)
  · -- case `1 < Kip`
    have hcase' : (1 : ℝ) < Kip := not_le.mp hcase
    have hKp1 : 0 ≤ Kip - 1 := by linarith
    have hb : (Kip - 1) * β ≤ (Kip - 1) * (α + 2 * Real.log CB) :=
      mul_le_mul_of_nonneg_left hL2 hKp1
    have hαb : α < Q := by
      rw [hQdef, lt_div_iff₀ hKsub]
      nlinarith [hL1, hb]
    have hstep : Real.log P + (Kip - 1) * β + α
        ≤ Real.log P + Kip * Q + 2 * (Kip - 1) * Real.log CB := by
      have h1 : Real.log P + (Kip - 1) * β + α
          ≤ Real.log P + (Kip - 1) * (α + 2 * Real.log CB) + α := by linarith
      have h2 : Real.log P + (Kip - 1) * (α + 2 * Real.log CB) + α
          ≤ Real.log P + Kip * Q + 2 * (Kip - 1) * Real.log CB := by
        nlinarith [mul_lt_mul_of_pos_left hαb hKip]
      linarith
    have hlogM : Real.log M < X2 := by
      rw [hX2def]
      linarith [hL3, hstep]
    have hX2X : X2 ≤ X := by rw [hXdef]; exact le_max_right X1 X2
    have hexp : M < Real.exp X :=
      lt_of_lt_of_le ((Real.log_lt_iff_lt_exp hMpos).mp hlogM) (Real.exp_le_exp.mpr hX2X)
    exact le_trans (le_of_lt hexp) (le_add_of_nonneg_right zero_le_one)

end Work.KMTAreas.A4
