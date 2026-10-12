import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.adm_regime_gate`

The regime gate: from FS admissibility `Work.BoseBoxFix.Adm v ε₀ μ` with the diluteness
cap `ε₀ ≤ (1/(8π))^{323}` it follows that the parameter block `fsParams (μ a³)` of the
diluted Bose gas is *small*:

* `s = (μa³)^{1/323} ≤ 1/(8π)` and `d = (μa³)^{6/323} ≤ 1`;
* `4π ≤ (2s)⁻¹` and `4π ≤ (2ds)⁻¹`.

The mathematical content is that `μ a v ³ ≤ ε₀ ≤ (1/(8π))^{323}` propagates through the
`1/323`-power (and, for the second pair of clauses, that `s, d > 0`).

The only subtlety is the *sign* of the diluteness.  `BoseGases.a v` is the scattering
length of `v`, defined by a case split in `ChallengeDeps`; for a potential without a
radial scattering solution it is `0`, and it need not be positive.  When
`t := μ a v ³ ≤ 0` the block `fsParams t` is the junk block `t^{c/323}` and the
conclusion fails on the first clause: e.g. at `t = 0` all parameters vanish and
`(2s)⁻¹ = 0 < 4π`, while for `t < 0` one has `t^c = |t|^c cos(cπ)`, so `s ≈ cos(π/323)`
is *large*.  Both are excluded by `Work.BoseBox.ParamsOK (fsParams t) t` — the second
because `Con_Mlln` carries the factor `t^{-1/2}`, which is `|t|^{-1/2} cos(-π/2) = 0`
for `t < 0`, against the strictly positive left side `K_M t^{-1/4}`; the first because
`Con_sKell` demands `1 ≤ s·K_ℓ·t^ε`.  This is `AdmGate.paramsOK_fsParams_pos` below.
-/

namespace Work.BoseBoxFock

namespace AdmGate

/-! ## 1. `Real.rpow` with a negative base -/

/-- For `t < 0` and `c ∈ (-1/2, 1/2)` the power `t ^ c = exp(log t · c) cos(cπ)` is
strictly positive: `cos` is positive on `(-π/2, π/2)`. -/
lemma rpow_pos_of_neg_of_mem {t c : ℝ} (ht : t < 0) (hc : -(1 / 2 : ℝ) < c)
    (hc' : c < 1 / 2) : 0 < t ^ c := by
  rw [Real.rpow_def_of_neg ht]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have : 0 < (c + 1 / 2) * Real.pi := mul_pos (by linarith) Real.pi_pos
    nlinarith [this]
  · have : 0 < (1 / 2 - c) * Real.pi := mul_pos (by linarith) Real.pi_pos
    nlinarith [this]

/-- `t ^ (-1/2) = 0` for `t < 0`: the factor `cos(-π/2)` vanishes.  This is the reason
`Con_Mlln` refutes negative diluteness. -/
lemma rpow_neg_half_eq_zero_of_neg {t : ℝ} (ht : t < 0) : t ^ (-(1 / 2 : ℝ)) = 0 := by
  rw [Real.rpow_def_of_neg ht, show (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_pi_div_two, mul_zero]

/-! ## 2. The diluteness `μ a³` is positive -/

/-- **`ParamsOK (fsParams t) t` forces `0 < t`.**  The two degenerate cases are killed by
two different conjuncts of `ParamsOK`:

* `t < 0`: `Con_Mlln` reads `K_M t^{-1/4} ≤ K_ℓ³ t^{-1/2} · t^ε`, but `t^{-1/2} = 0`
  while `K_M t^{-1/4} > 0`;
* `t = 0`: `Con_sKell` reads `1 ≤ s · K_ℓ · t^ε`, but `s = K_ℓ = t^ε = 0`. -/
lemma paramsOK_fsParams_pos {t : ℝ} (h : Work.BoseBox.ParamsOK (Work.BoseBox.fsParams t) t) :
    0 < t := by
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · exfalso
    obtain ⟨ε, hε0, _hεle, hle⟩ := h.Mlln
    have hz : (Work.BoseBox.fsParams t).Kl ^ 3 * t ^ (-(1 / 2 : ℝ)) = 0 := by
      rw [rpow_neg_half_eq_zero_of_neg hlt, mul_zero]
    rw [hz, zero_mul] at hle
    have hf : 0 < (Work.BoseBox.fsParams t).KM * t ^ (-(1 / 4 : ℝ)) := by
      refine mul_pos ?_ (rpow_pos_of_neg_of_mem hlt (by norm_num) (by norm_num))
      show 0 < Work.BoseBox.fsXp t (-1)
      exact rpow_pos_of_neg_of_mem hlt (by norm_num) (by norm_num)
    linarith
  · exfalso
    obtain ⟨ε, hε0, _hεle, hle⟩ := h.sKell
    have hs : (Work.BoseBox.fsParams t).s = 0 := by
      show Work.BoseBox.fsXp t 1 = 0
      rw [Work.BoseBox.fsXp, heq]
      exact Real.zero_rpow (by norm_num)
    have hkl : (Work.BoseBox.fsParams t).Kl = 0 := by
      show Work.BoseBox.fsXp t (-(3 / 2)) = 0
      rw [Work.BoseBox.fsXp, heq]
      exact Real.zero_rpow (by norm_num)
    have htz : t ^ ε = 0 := by rw [heq]; exact Real.zero_rpow (ne_of_gt hε0)
    rw [hs, hkl, htz] at hle
    norm_num at hle
  · exact hgt

end AdmGate

/-! ## 3. The gate -/

theorem adm_regime_gate (v : ℝ³ → ℝ) {ε₀ μ : ℝ} (hε0 : 0 < ε₀)
    (hε : ε₀ ≤ (1 / (8 * Real.pi)) ^ (323 : ℝ))
    (hadm : Work.BoseBoxFix.Adm v ε₀ μ) :
    (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤ 1 / (8 * Real.pi) ∧
    (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ≤ 1 ∧
    4 * Real.pi ≤ (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s)⁻¹ ∧
    4 * Real.pi ≤ (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).s)⁻¹ := by
  obtain ⟨_hμ, hdil, hOK⟩ := hadm
  set T : ℝ := μ * (BoseGases.a v) ^ 3 with hT
  have hOK' : Work.BoseBox.ParamsOK (Work.BoseBox.fsParams T) T := hOK
  have hTpos : 0 < T := AdmGate.paramsOK_fsParams_pos hOK'
  have hTle : T ≤ (1 / (8 * Real.pi)) ^ (323 : ℝ) := by
    rw [hT]; exact le_trans hdil hε
  have hS : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s = T ^ (1 / 323 : ℝ) := rfl
  have hD : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d = T ^ (6 / 323 : ℝ) := rfl
  have hrpos : 0 < 1 / (8 * Real.pi) := by positivity
  have hrle1 : 1 / (8 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hSpos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
    rw [hS]; exact Real.rpow_pos_of_pos hTpos _
  have hDpos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    rw [hD]; exact Real.rpow_pos_of_pos hTpos _
  have hSle : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤ 1 / (8 * Real.pi) := by
    rw [hS]
    calc T ^ (1 / 323 : ℝ)
        ≤ ((1 / (8 * Real.pi)) ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow hTpos.le hTle (by norm_num)
      _ = (1 / (8 * Real.pi)) ^ ((323 : ℝ) * ((1 : ℝ) / 323)) :=
          (Real.rpow_mul hrpos.le 323 ((1 : ℝ) / 323)).symm
      _ = 1 / (8 * Real.pi) := by
          rw [show (323 : ℝ) * ((1 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
  refine ⟨hSle, ?_, ?_, ?_⟩
  · -- `d = t^{6/323} ≤ (1/(8π))⁶ ≤ 1`
    rw [hD]
    calc T ^ (6 / 323 : ℝ)
        ≤ ((1 / (8 * Real.pi)) ^ (323 : ℝ)) ^ ((6 : ℝ) / 323) :=
          Real.rpow_le_rpow hTpos.le hTle (by norm_num)
      _ = (1 / (8 * Real.pi)) ^ ((323 : ℝ) * ((6 : ℝ) / 323)) :=
          (Real.rpow_mul hrpos.le 323 ((6 : ℝ) / 323)).symm
      _ = (1 / (8 * Real.pi)) ^ (6 : ℝ) := by
          rw [show (323 : ℝ) * ((6 : ℝ) / 323) = 6 by norm_num]
      _ ≤ 1 := Real.rpow_le_one hrpos.le hrle1 (by norm_num)
  · -- `4π ≤ (2s)⁻¹` since `2s ≤ 1/(4π)`
    have h2Spos : 0 < 2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by linarith
    have h2Sle : 2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤ 1 / (4 * Real.pi) := by
      have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
      rw [le_div_iff₀ h4]
      have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
      have hS8 : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s * (8 * Real.pi) ≤ 1 :=
        (le_div_iff₀ h8).mp hSle
      nlinarith [hS8]
    have h := one_div_le_one_div_of_le h2Spos h2Sle
    simpa [one_div] using h
  · -- `4π ≤ (2ds)⁻¹` since `ds = t^{7/323} ≤ (1/(8π))⁷ ≤ 1/(8π)`
    have hDS : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s = T ^ (7 / 323 : ℝ) := by
      rw [hD, hS, ← Real.rpow_add hTpos]
      ring_nf
    have hDSle : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤ 1 / (8 * Real.pi) := by
      rw [hDS]
      calc T ^ (7 / 323 : ℝ)
          ≤ ((1 / (8 * Real.pi)) ^ (323 : ℝ)) ^ ((7 : ℝ) / 323) :=
            Real.rpow_le_rpow hTpos.le hTle (by norm_num)
        _ = (1 / (8 * Real.pi)) ^ ((323 : ℝ) * ((7 : ℝ) / 323)) :=
            (Real.rpow_mul hrpos.le 323 ((7 : ℝ) / 323)).symm
        _ = (1 / (8 * Real.pi)) ^ (7 : ℝ) := by
            rw [show (323 : ℝ) * ((7 : ℝ) / 323) = 7 by norm_num]
        _ ≤ (1 / (8 * Real.pi)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hrpos hrle1 (by norm_num)
        _ = 1 / (8 * Real.pi) := Real.rpow_one _
    have h2DSpos : 0 < 2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
      have h1 : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := mul_pos hDpos hSpos
      linarith
    have h2DSle : 2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s ≤ 1 / (4 * Real.pi) := by
      have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
      rw [le_div_iff₀ h4]
      have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
      have hDS8 : ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d *
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) * (8 * Real.pi) ≤ 1 :=
        (le_div_iff₀ h8).mp hDSle
      nlinarith [hDS8]
    have h := one_div_le_one_div_of_le h2DSpos h2DSle
    simpa [one_div] using h

end Work.BoseBoxFock
