import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2

/-!
# `Work.EKLC6Core.bad_outCol_upper_alt`

**Outside collar.**  A point `z` of the cell ball of radius `cellRad μ y m` around `y m` that is
pushed by a displacement `v ∈ V (ε * injCap z)` into the slightly enlarged ball of radius
`ρ ≤ cellRad μ y j * (1 + deltac * ε / 2)` around `y j` (with `ρ ≥ cellRad μ y j`) must itself lie
in the ball of radius `cellRad μ y j * (1 + deltac * ε)` around `y j`.

The displacement `v` is tiny compared with the scale `cellRad μ y j` because `z` lies in *some*
cell of the family, which bounds `injCap z` in terms of `injCap (y j)`; this is the geometric input
supplied by `injCap_le_mul_of_mem_Vball` and `injCap_mem_V_le`.

The argument splits on whether the "outside displacement radius"
`R = 30 (ε injCap z) + ρ + 3 (30 (ε injCap z)) ρ` is below `injCap (y j)/8`:

* in the easy case the comparison `injCap z ≤ 2^19 injCap (y j) ≤ 2^31 cellRad μ y j` is immediate;
* in the hard case one first shows that `ε injCap z` is not too small, which via the `y m`-cell
  forces `injCap (y m) ≤ 16 injCap (y j)` and hence the bound with the factor `2^35`.

The two pure-arithmetic cores are factored out as `outColAlt_final` and `outColAlt_caseB`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.EKLC6Core

noncomputable section

open Work.EKLContract

/-- **Final arithmetic of the outside collar.**  If `injz ≤ 2^35 rn` and
`ρ ≤ rn * (1 + deltac * ε / 2)` with `rn ≤ 1/4096`, then the radius
`30 (ε injz) + ρ + 3 (30 (ε injz)) ρ` of `V⁻¹ · ρ` stays below `rn * (1 + deltac * ε)`. -/
theorem outColAlt_final {ρ rn injz ε : ℝ} (hε0 : 0 < ε) (hinkz : 0 < injz)
    (hrn : 0 < rn) (hrn4096 : rn ≤ 1 / 4096)
    (hde : 0 ≤ deltac * ε) (hde1 : deltac * ε ≤ 1)
    (hρ_lo : rn ≤ ρ) (hρ_hi : ρ ≤ rn * (1 + deltac * ε / 2))
    (hinjz : injz ≤ 2 ^ 35 * rn) :
    30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ ≤ rn * (1 + deltac * ε) := by
  have ht_nonneg : 0 ≤ ε * injz := mul_nonneg (le_of_lt hε0) (le_of_lt hinkz)
  have hG : 1 + deltac * ε / 2 ≤ 3 / 2 := by linarith
  have hρle : ρ ≤ rn * (3 / 2) := le_trans hρ_hi (by nlinarith [hG, hrn])
  have h1p3 : 1 + 3 * ρ ≤ 2 := by nlinarith [hρle, hrn4096, hrn]
  have hkey : 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ
      = 30 * (ε * injz) * (1 + 3 * ρ) + ρ := by ring
  rw [hkey]
  have hstep1 : 30 * (ε * injz) * (1 + 3 * ρ) ≤ 60 * (ε * injz) := by
    have h1 : 30 * (ε * injz) * (1 + 3 * ρ) ≤ 30 * (ε * injz) * 2 :=
      mul_le_mul_of_nonneg_left h1p3 (by linarith [ht_nonneg])
    linarith [h1]
  have hstep2 : 60 * (ε * injz) ≤ 60 * (ε * (2 ^ 35 * rn)) := by
    have h := mul_le_mul_of_nonneg_left hinjz (le_of_lt hε0); nlinarith [h]
  have hstep3 : 60 * (ε * (2 ^ 35 * rn)) ≤ rn * (deltac * ε / 2) := by
    have h60 : (60 : ℝ) * 2 ^ 35 ≤ deltac / 2 := by rw [deltac]; norm_num
    have h := mul_le_mul_of_nonneg_right h60 (by positivity : (0 : ℝ) ≤ ε * rn)
    have h1 : 60 * (ε * (2 ^ 35 * rn)) = (60 * 2 ^ 35) * (ε * rn) := by ring
    have h2 : rn * (deltac * ε / 2) = (deltac / 2) * (ε * rn) := by ring
    rw [h1, h2]; exact h
  nlinarith [hstep1, hstep2, hstep3, hρ_hi]

/-- **Hard-case arithmetic of the outside collar.**  When the outside radius exceeds
`injCap (y j)/8`, the quantity `30 R + rm + 3 (30 R) rm` (the displacement radius needed to
transfer `y j` into the `y m`-ball) is controlled by `injCap (y m)/8`, and `R` itself is at most
`1`.  All hypotheses are pure inequalities between reals. -/
theorem outColAlt_caseB {ρ rn rm injz injj injm ε : ℝ} (hε0 : 0 < ε) (hinkz : 0 < injz)
    (hinkm : 0 < injm) (hinkm2 : injm ≤ 1 / 2) (hεsmall : ε ≤ 1 / (1000000 * 2 ^ 19))
    (hrn : 0 < rn) (hrm : 0 < rm) (hρ_lo : rn ≤ ρ) (hrn4096 : rn ≤ 1 / 4096)
    (hde1 : deltac * ε ≤ 1)
    (hρ_hi : ρ ≤ rn * (1 + deltac * ε / 2))
    (hcase : injj / 8 < 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ)
    (hrn2048 : rn ≤ injj / 2048) (hrm2048 : rm ≤ injm / 2048)
    (hz_m : injz ≤ 2 ^ 19 * injm) :
    30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ ≤ 1 ∧
    (30 * (30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ) + rm
        + 3 * (30 * (30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ)) * rm ≤ injm / 8) ∧
    (30 * (30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ) + rm
        + 3 * (30 * (30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ)) * rm ≤ 1 / 2) := by
  have ht_nn : 0 ≤ ε * injz := mul_nonneg (le_of_lt hε0) (le_of_lt hinkz)
  -- lower bound for `ε * injz`
  have ht_gt : injj / 1000 < ε * injz := by
    have hρle : ρ ≤ rn * (3 / 2) := le_trans hρ_hi (by nlinarith [hde1, hrn])
    have hρle2 : ρ ≤ injj * (3 / 4096) := by nlinarith [hρle, hrn2048]
    have h1p3 : 1 + 3 * ρ ≤ 2 := by nlinarith [hρle, hrn4096, hrn]
    have hkey : 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ
        = 30 * (ε * injz) * (1 + 3 * ρ) + ρ := by ring
    have hRgt : injj / 8 < 30 * (ε * injz) * (1 + 3 * ρ) + ρ := by rw [← hkey]; exact hcase
    have hA : 30 * (ε * injz) * (1 + 3 * ρ) ≤ 30 * (ε * injz) * 2 :=
      mul_le_mul_of_nonneg_left h1p3 (by linarith [ht_nn])
    nlinarith [hRgt, hA, hρle2]
  set E : ℝ := ε * 2 ^ 19 * injm with hEdef
  have hE_ge_t : ε * injz ≤ E := by rw [hEdef]; nlinarith [hz_m, hε0]
  have hEpos : 0 < E := lt_of_lt_of_le (mul_pos hε0 hinkz) hE_ge_t
  have hεK : ε * 2 ^ 19 ≤ 1 / 1000000 := by
    have h := mul_le_mul_of_nonneg_right hεsmall (by norm_num : (0 : ℝ) ≤ 2 ^ 19)
    have h2 : (1 / (1000000 * 2 ^ 19)) * 2 ^ 19 = 1 / 1000000 := by norm_num
    linarith [h, h2]
  have hEsmall : E ≤ 1 / 2 := by
    rw [hEdef]
    have h := mul_le_mul_of_nonneg_right hεK (le_of_lt hinkm)
    nlinarith [h, hinkm2]
  have hinjj_lt : injj < 1000 * E := by nlinarith [ht_gt, hE_ge_t]
  have hrn_lt_E : rn < E := by nlinarith [hrn2048, hinjj_lt]
  have hR_le : 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ ≤ 200 * E := by
    have hρle : ρ ≤ rn * (3 / 2) := le_trans hρ_hi (by nlinarith [hde1, hrn])
    have hρE : ρ ≤ E * (3 / 2) := le_trans hρle (by nlinarith [hrn_lt_E])
    nlinarith [hE_ge_t, hρE, hEpos, hEsmall, ht_nn, hρ_lo]
  have hR_le_injm :
      30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ ≤ 200 * (1 / 1000000) * injm := by
    rw [hEdef] at hR_le
    have h := mul_le_mul_of_nonneg_right hεK (by positivity : (0 : ℝ) ≤ 200 * injm)
    nlinarith [hR_le, h, hinkm]
  have hR_le_one : 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hinkm2 (by norm_num : (0 : ℝ) ≤ 200 * (1 / 1000000))
    nlinarith [hR_le_injm, h]
  set R : ℝ := 30 * (ε * injz) + ρ + 3 * (30 * (ε * injz)) * ρ with hR
  have hRnn : 0 ≤ R := by rw [hR]; nlinarith [ht_nn, hρ_lo, hrn]
  have h30R : 30 * R ≤ 6000 * (1 / 1000000) * injm := by nlinarith [hR_le_injm]
  have hterm : 3 * (30 * R) * rm ≤ 3 * (6000 * (1 / 1000000) * injm) * (injm / 2048) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h30R (by norm_num)) hrm2048
      (le_of_lt hrm) (by positivity)
  have ha_le : 30 * R + rm + 3 * (30 * R) * rm ≤ injm / 8 := by
    have key : 30 * R + rm + 3 * (30 * R) * rm
        ≤ 6000 * (1 / 1000000) * injm + injm / 2048
          + 3 * (6000 * (1 / 1000000) * injm) * (injm / 2048) :=
      by linarith [h30R, hterm, hrm2048]
    have key2 : 6000 * (1 / 1000000) * injm + injm / 2048
          + 3 * (6000 * (1 / 1000000) * injm) * (injm / 2048) ≤ injm / 8 :=
      by nlinarith [hinkm, hinkm2]
    linarith [key, key2]
  have ha_half : 30 * R + rm + 3 * (30 * R) * rm ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hinkm2 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    linarith [ha_le, h]
  exact ⟨hR_le_one, ha_le, ha_half⟩

theorem bad_outCol_upper_alt {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] {y : ℕ → Work.EKLContract.X3} {j m : ℕ}
    (hj : j ∈ Work.EKLC6Core.sel y) (hm : m ∈ Work.EKLC6Core.sel y) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3}
    {v : Work.EKLContract.SL3} {ρ : ℝ}
    (hz_in : z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y m) (y m))
    (hv : v ∈ Work.EKLContract.V (ε * Work.EKLC6Core.injCap z))
    (hρ_lo : Work.EKLC6Core.cellRad μ y j ≤ ρ)
    (hρ_hi : ρ ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε / 2))
    (hvz : v • z ∈ Work.EKLComp.Vball ρ (y j)) :
    z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε))
      (y j) := by
  classical
  obtain ⟨b, hb, hbeq⟩ := Work.EKLComp.mem_Vball.mp hvz
  obtain ⟨dd, hdd, hddeq⟩ := Work.EKLComp.mem_Vball.mp hz_in
  have hrjpos : 0 < cellRad μ y j := cellRad_pos hj
  have hrmpos : 0 < cellRad μ y m := cellRad_pos hm
  have hrjhi : cellRad μ y j ≤ cellHi (y j) := cellRad_le_cellHi hj
  have hrmhi : cellRad μ y m ≤ cellHi (y m) := cellRad_le_cellHi hm
  have hrj4096 : cellRad μ y j ≤ 1 / 4096 := le_trans hrjhi (cellHi_le (y j))
  have hrn2048 : cellRad μ y j ≤ injCap (y j) / 2048 := by simpa [cellHi] using hrjhi
  have hrm2048 : cellRad μ y m ≤ injCap (y m) / 2048 := by simpa [cellHi] using hrmhi
  have hrm_div8 : cellRad μ y m ≤ injCap (y m) / 8 := by
    have h := injCap_pos (y m); nlinarith [hrm2048, h]
  have hβj : injCap (y j) ≤ 4096 * cellRad μ y j := by
    have h := (cellRad_spec (μ := μ) hj).1
    rw [cellLo, div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)] at h
    linarith
  have hde : 0 ≤ deltac * ε := mul_nonneg (le_of_lt deltac_pos) (le_of_lt hε0)
  have hde1 : deltac * ε ≤ 1 := deltac_eps_le_one hε1
  have hε_le_one : ε ≤ 1 := by
    have h : epsZero ≤ 1 := by rw [epsZero, deltac]; norm_num
    linarith
  have ht_pos : 0 < ε * injCap z := mul_pos hε0 (injCap_pos z)
  have ht_le_one : ε * injCap z ≤ 1 := by
    have hh := injCap_le_half z; nlinarith [hε0, hε_le_one, hh, injCap_pos z]
  have hvinv : v⁻¹ ∈ V (30 * (ε * injCap z)) :=
    Work.Misiurewicz.V_mono (by linarith) (Work.EKLComp.inv_mem_V ht_pos ht_le_one hv)
  have hzrep : z = (v⁻¹ * b) • y j := by
    have h1 : v⁻¹ • (v • z) = z := by rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [← h1, ← hbeq, mul_smul]
  have hRpos : 0 < 30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ := by
    nlinarith [ht_pos, hρ_lo, hrjpos]
  have hRnn : 0 ≤ 30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ := le_of_lt hRpos
  have hρnn : 0 ≤ ρ := le_trans (le_of_lt hrjpos) hρ_lo
  have hc : v⁻¹ * b ∈ V (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ) :=
    V_mul_subset_V (s := 30 * (ε * injCap z)) (t := ρ)
      (by positivity) hρnn hvinv hb
  have hzc : z ∈ Work.EKLComp.Vball
      (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ) (y j) :=
    ⟨v⁻¹ * b, hc, hzrep.symm⟩
  by_cases hcase : 30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ ≤ injCap (y j) / 8
  · have hcy_j : injCap z ≤ 2 ^ 19 * injCap (y j) :=
      injCap_le_mul_of_mem_Vball (z := z) (y := y j)
        (r := 30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ) hRnn hcase hzc
    have hinjz : injCap z ≤ 2 ^ 35 * cellRad μ y j := by
      have h0 := le_trans hcy_j (mul_le_mul_of_nonneg_left hβj (by norm_num : (0:ℝ) ≤ 2 ^ 19))
      have hpow : (2 : ℝ) ^ 19 * 4096 = 2 ^ 31 := by norm_num
      have heq : (2 : ℝ) ^ 19 * (4096 * cellRad μ y j) = 2 ^ 31 * cellRad μ y j := by
        rw [← mul_assoc, hpow]
      rw [heq] at h0
      have h2 : (2 : ℝ) ^ 31 ≤ 2 ^ 35 := by norm_num
      exact le_trans h0 (mul_le_mul_of_nonneg_right h2 (le_of_lt hrjpos))
    have hRle := outColAlt_final (ρ := ρ) (rn := cellRad μ y j) (injz := injCap z)
      hε0 (injCap_pos z) hrjpos hrj4096 hde hde1 hρ_lo hρ_hi hinjz
    exact Work.Misiurewicz.Vball_mono (y j) hRle hzc
  · push_neg at hcase
    have hε_small : ε ≤ 1 / (1000000 * 2 ^ 19) := by
      have h : epsZero ≤ 1 / (1000000 * 2 ^ 19) := by rw [epsZero, deltac]; norm_num
      linarith
    have hcy_m : injCap z ≤ 2 ^ 19 * injCap (y m) :=
      injCap_le_mul_of_mem_Vball (z := z) (y := y m) (r := cellRad μ y m)
        (le_of_lt hrmpos) hrm_div8 hz_in
    obtain ⟨hR_le_one, ha_le, ha_half⟩ := outColAlt_caseB (ρ := ρ)
      (rn := cellRad μ y j) (rm := cellRad μ y m) (injz := injCap z)
      (injj := injCap (y j)) (injm := injCap (y m))
      hε0 (injCap_pos z) (injCap_pos (y m)) (injCap_le_half (y m)) hε_small
      hrjpos hrmpos hρ_lo hrj4096 hde1 hρ_hi hcase hrn2048 hrm2048 hcy_m
    have ha_pos : 0 < 30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ)
        + cellRad μ y m
        + 3 * (30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ))
            * cellRad μ y m := by
      nlinarith [hRpos, hrmpos]
    have hc_inv : (v⁻¹ * b)⁻¹ ∈ V (30 * (30 * (ε * injCap z) + ρ
        + 3 * (30 * (ε * injCap z)) * ρ)) :=
      Work.Misiurewicz.V_mono (by nlinarith [hRpos])
        (Work.EKLComp.inv_mem_V hRpos hR_le_one hc)
    have hcone : (v⁻¹ * b)⁻¹ * dd ∈ V (30 * (30 * (ε * injCap z) + ρ
        + 3 * (30 * (ε * injCap z)) * ρ) + cellRad μ y m
        + 3 * (30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ))
            * cellRad μ y m) :=
      V_mul_subset_V (s := 30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ))
        (t := cellRad μ y m) (by positivity) (le_of_lt hrmpos) hc_inv hdd
    have hcy : (v⁻¹ * b) • y j = dd • y m := hzrep.symm.trans hddeq.symm
    have hyj : ((v⁻¹ * b)⁻¹ * dd) • y m = y j := by
      rw [mul_smul, ← hcy, ← mul_smul, inv_mul_cancel, one_smul]
    have hl2 : injCap (y m) / 16 ≤ injCap (y j) := by
      have h := injCap_mem_V_le (x := y m)
        (a := 30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ)
          + cellRad μ y m
          + 3 * (30 * (30 * (ε * injCap z) + ρ + 3 * (30 * (ε * injCap z)) * ρ))
              * cellRad μ y m) ha_pos ha_half ha_le hcone
      rwa [hyj] at h
    have hinjz : injCap z ≤ 2 ^ 35 * cellRad μ y j := by
      have h1 : injCap z ≤ 16 * (2 ^ 19 * injCap (y j)) := by nlinarith [hcy_m, hl2]
      have h2 : 16 * (2 ^ 19 * injCap (y j)) ≤ 16 * (2 ^ 19 * (4096 * cellRad μ y j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβj (by norm_num)) (by norm_num)
      have h3 : injCap z ≤ (16 * 2 ^ 19 * 4096) * cellRad μ y j := by
        have hh := le_trans h1 h2
        rw [show (16 : ℝ) * (2 ^ 19 * (4096 * cellRad μ y j))
            = (16 * 2 ^ 19 * 4096) * cellRad μ y j from by ring] at hh
        exact hh
      have h4 : (16 : ℝ) * 2 ^ 19 * 4096 = 2 ^ 35 := by norm_num
      linarith [h3, h4]
    have hRle := outColAlt_final (ρ := ρ) (rn := cellRad μ y j) (injz := injCap z)
      hε0 (injCap_pos z) hrjpos hrj4096 hde hde1 hρ_lo hρ_hi hinjz
    exact Work.Misiurewicz.Vball_mono (y j) hRle hzc

end

end Work.EKLC6Core
