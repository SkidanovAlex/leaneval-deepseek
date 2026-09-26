import Mathlib
import Submission.Work.Asymptotics.Tile.SharpTB8
import Submission.Work.Asymptotics.Tile.KPlus24TileTail
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.funnel_divisor_lower

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics
open Work.Asymptotics.EtailE

noncomputable section

private lemma zdev_K24F : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖E4Fun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E4Fun z ^ 3 - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E2S z ^ 2 - K24F.S0 z ^ 2‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z‖ ≤ A * ‖qParamFun z‖ ∧
      ‖E6Fun z * E2S z / E4Fun z - K24F.S0 z + 24 * qParamFun z
          + 744 * qParamFun z * K24F.S0 z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E2S z - K24F.S0 z + 24 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖E4Fun z - 1 - 240 * qParamFun z‖ ≤ A * ‖qParamFun z‖ ^ 2 ∧
      ‖qParamFun z / DeltaFun z - 1‖ ≤ A * ‖qParamFun z‖ ∧
      ‖(DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24‖ ≤ A * ‖qParamFun z‖ ∧
      ‖1 - DeltaFun z / qParamFun z‖ ≤ A * ‖qParamFun z‖ ∧
      (1 / 2) * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ ∧
      ‖(DeltaFun z)⁻¹‖ ≤ A * ‖qParamFun z‖⁻¹ ∧
      ‖(E4Fun z)⁻¹‖ ≤ 2 ∧
      ‖E4Fun z‖ ≤ 3 / 2 ∧
      ‖K24F.S0 z‖ ≤ 3 := by
  obtain ⟨A, hAp, hA⟩ := K24Fsm.zdev
  refine ⟨A, hAp, fun z hz => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hA z hz
  exact ⟨a1, a2, by simpa only [← K24Fsm.S0_eq_S0c] using a3,
    by simpa only [← K24Fsm.S0_eq_S0c] using a4,
    by simpa only [← K24Fsm.S0_eq_S0c] using a5,
    by simpa only [← K24Fsm.S0_eq_S0c] using a6, a7, a8, a9,
    by simpa only [← K24Fsm.S0_eq_S0c] using a10, a11, a12, a13, a14,
    by simpa only [← K24Fsm.S0_eq_S0c] using a15⟩

/-! ## Conversion of the `q`-power bounds to `ZC3`/`ZCg3` -/

lemma ZC3.of_qpow1 {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖) :
    ZC3 0 2 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht3 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [norm_qParamFun, hzim]
  rw [hq] at h
  simpa using h

lemma ZC3.of_qpow2 {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖ ^ 2) :
    ZC3 0 4 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht3 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖ ^ 2 = Real.exp (-(4 * Real.pi * t)) := by
    rw [norm_qParamFun, hzim, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq] at h
  simpa using h

lemma ZC3.of_qbdd {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A) : ZC3 0 0 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht3 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  rw [show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero, Real.rpow_zero, mul_one, mul_one]
  exact h

lemma ZCg3.of_qinv {f : ℍ → ℂ}
    (h : ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ A * ‖qParamFun z‖⁻¹) :
    ZCg3 0 2 f := by
  obtain ⟨A, hA, hb⟩ := h
  refine ⟨A, hA, fun z t ht3 hz => ?_⟩
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; linarith
  have h := hb z hz3
  have hq : ‖qParamFun z‖⁻¹ = Real.exp (2 * Real.pi * t) := by
    rw [norm_qParamFun, hzim, ← Real.exp_neg]
    congr 1
    ring
  rw [hq] at h
  simpa using h

/-! ## The `z`-atoms -/

lemma ZC3.ktl24_q : ZC3 0 2 (fun z : ℍ => qParamFun z) := by
  refine ⟨1, one_pos, fun z t ht3 hz => ?_⟩
  rw [norm_qParamFun, K24F.im_of_coe_eq_axis hz]
  simp

lemma ZC3.ktl24_z : ZC3 1 0 (fun z : ℍ => (z : ℂ)) := by
  refine ⟨1, one_pos, fun z t ht3 hz => ?_⟩
  have hzt : ‖(z : ℂ)‖ = t := ktl_norm_coe (by linarith) hz
  rw [hzt, Real.rpow_one, show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero]
  simp only [mul_one]
  linarith

lemma ZC3.ktl24_zsq : ZC3 2 0 (fun z : ℍ => (z : ℂ) ^ 2) :=
  ZC3.congr ((ZC3.ktl24_z.mul ZC3.ktl24_z).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by ring)

lemma ZC3.ktl24_E4sub1 : ZC3 0 2 (fun z : ℍ => E4Fun z - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).1⟩

lemma ZC3.ktl24_E4cube_sub1 : ZC3 0 2 (fun z : ℍ => E4Fun z ^ 3 - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.1⟩

lemma ZC3.ktl24_E2Ssq_sub_S0sq :
    ZC3 0 2 (fun z : ℍ => E2S z ^ 2 - K24F.S0 z ^ 2) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.1⟩

lemma ZC3.ktl24_E6E2S_div_E4_sub_S0 :
    ZC3 0 2 (fun z : ℍ => E6Fun z * E2S z / E4Fun z - K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.1⟩

lemma ZC3.ktl24_X4 : ZC3 0 4 (fun z : ℍ => E6Fun z * E2S z / E4Fun z - K24F.S0 z
      + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow2 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.1⟩

lemma ZC3.ktl24_E4sub1_sub240q :
    ZC3 0 4 (fun z : ℍ => E4Fun z - 1 - 240 * qParamFun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow2 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_q_div_Delta_sub1 :
    ZC3 0 2 (fun z : ℍ => qParamFun z / DeltaFun z - 1) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_d1 :
    ZC3 0 2 (fun z : ℍ => (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_one_sub_Delta_div_q :
    ZC3 0 2 (fun z : ℍ => 1 - DeltaFun z / qParamFun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qpow1 ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.1⟩

lemma ZCg3.ktl24_Delta_inv : ZCg3 0 2 (fun z : ℍ => (DeltaFun z)⁻¹) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZCg3.of_qinv ⟨A, hAp, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_E4inv : ZC3 0 0 (fun z : ℍ => (E4Fun z)⁻¹) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qbdd ⟨2, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_E4 : ZC3 0 0 (fun z : ℍ => E4Fun z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qbdd ⟨3 / 2, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

lemma ZC3.ktl24_S0 : ZC3 0 0 (fun z : ℍ => K24F.S0 z) := by
  obtain ⟨A, hAp, hA⟩ := zdev_K24F
  exact ZC3.of_qbdd ⟨3, by norm_num, fun z hz => (hA z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

lemma ZC3.ktl24_B2 : ZC3 0 4 (fun z : ℍ => K24F.B2 z) := by
  obtain ⟨C, hC, hb⟩ := b2_le
  exact ZC3.of_qpow2 ⟨C, hC, hb⟩

/-- `Δ(z) = q(z) · (Δ(z)/q(z))`. -/
lemma ZC3.ktl24_Delta : ZC3 0 2 (fun z : ℍ => DeltaFun z) := by
  have h0 : ZC3 0 0 (fun z : ℍ => 1 - (1 - DeltaFun z / qParamFun z)) :=
    ((ZC3.const 0 le_rfl (1 : ℂ)).sub ZC3.ktl24_one_sub_Delta_div_q).mono
      (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h1 : ZC3 0 0 (fun z : ℍ => DeltaFun z / qParamFun z) :=
    h0.congr (fun z => by ring)
  refine ((ZC3.ktl24_q.mul h1).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num)).congr
    (fun z => ?_)
  rw [div_eq_mul_inv]
  field_simp

lemma ZC3.ktl24_one_sub_E4cube : ZC3 0 2 (fun z : ℍ => 1 - E4Fun z ^ 3) :=
  ZC3.ktl24_E4cube_sub1.neg.congr (fun z => by ring)

lemma ZC3.ktl24_E4cube : ZC3 0 0 (fun z : ℍ => E4Fun z ^ 3) :=
  (((ZC3.ktl24_E4.mul ZC3.ktl24_E4).mul ZC3.ktl24_E4).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)).congr (fun z => by ring)

lemma ZC3.ktl24_S0sq : ZC3 0 0 (fun z : ℍ => K24F.S0 z ^ 2) :=
  ((ZC3.ktl24_S0.mul ZC3.ktl24_S0).mono (m' := 0) (n' := 0) (by norm_num)
    (by norm_num)).congr (fun z => by ring)

lemma ZC3.ktl24_12_E2Ssq_sub_S0sq :
    ZC3 0 2 (fun z : ℍ => 12 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  ZC3.ktl24_E2Ssq_sub_S0sq.cmul 12

lemma ZC3.ktl24_12_E4sub1 : ZC3 0 2 (fun z : ℍ => 12 * (E4Fun z - 1)) :=
  ZC3.ktl24_E4sub1.cmul 12

lemma ZC3.ktl24_8640_E4sub1 : ZC3 0 2 (fun z : ℍ => 8640 * (E4Fun z - 1)) :=
  ZC3.ktl24_E4sub1.cmul 8640

lemma ZC3.ktl24_12096_E2Ssq_sub_S0sq :
    ZC3 0 2 (fun z : ℍ => 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  ZC3.ktl24_E2Ssq_sub_S0sq.cmul 12096

lemma ZC3.ktl24_E4sub1_sub_E2Ssq :
    ZC3 0 2 (fun z : ℍ => (E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  (ZC3.ktl24_E4sub1.sub ZC3.ktl24_E2Ssq_sub_S0sq).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_dev2 : ZC3 0 2 (fun z : ℍ =>
    12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1)) :=
  (ZC3.ktl24_12_E2Ssq_sub_S0sq.sub ZC3.ktl24_12_E4sub1).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_dev3 : ZC3 0 2 (fun z : ℍ =>
    8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) :=
  (ZC3.ktl24_8640_E4sub1.sub ZC3.ktl24_12096_E2Ssq_sub_S0sq).mono (m' := 0) (n' := 2)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_12_B2 : ZC3 0 4 (fun z : ℍ => 12 * K24F.B2 z) := ZC3.ktl24_B2.cmul 12

lemma ZC3.ktl24_12_E4sub1_sub240q :
    ZC3 0 4 (fun z : ℍ => 12 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  ZC3.ktl24_E4sub1_sub240q.cmul 12

lemma ZC3.ktl24_8640_E4sub1_sub240q :
    ZC3 0 4 (fun z : ℍ => 8640 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  ZC3.ktl24_E4sub1_sub240q.cmul 8640

lemma ZC3.ktl24_12096_B2 : ZC3 0 4 (fun z : ℍ => 12096 * K24F.B2 z) :=
  ZC3.ktl24_B2.cmul 12096

lemma ZC3.ktl24_devb1 : ZC3 0 4 (fun z : ℍ =>
    (E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z) :=
  (ZC3.ktl24_E4sub1_sub240q.sub ZC3.ktl24_B2).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_devb2 : ZC3 0 4 (fun z : ℍ =>
    12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z)) :=
  (ZC3.ktl24_12_B2.sub ZC3.ktl24_12_E4sub1_sub240q).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_devb3 : ZC3 0 4 (fun z : ℍ =>
    8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z) :=
  (ZC3.ktl24_8640_E4sub1_sub240q.sub ZC3.ktl24_12096_B2).mono (m' := 0) (n' := 4)
    (by norm_num) (by norm_num)

lemma ZC3.ktl24_Sm3bracket : ZC3 0 2 (fun z : ℍ =>
    K24F.S0 z * (E4Fun z ^ 3 - 1) - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)) :=
  ((ZC3.ktl24_S0.mul ZC3.ktl24_E4cube_sub1).sub ZC3.ktl24_E6E2S_div_E4_sub_S0).mono
    (m' := 0) (n' := 2) (by norm_num) (by norm_num)


lemma ZC3.ktl24_one_sub_S0sq : ZC3 0 0 (fun z : ℍ => 1 - K24F.S0 z ^ 2) :=
  ((ZC3.const 0 le_rfl (1 : ℂ)).sub ZC3.ktl24_S0sq).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)

/-! ## The `τ`-atoms on the tiles -/

lemma TBS.ktl24_r0 : TBS 0 0 (fun w n _ => K24F.r0 ((n : ℝ) +ᵥ w)) :=
  ((TBS.mul TBS.ktl8_tau TBS.E14).mono (by norm_num) (by norm_num)).congr
    (fun w n z => by simp only [K24F.r0])

lemma TBS.ktl24_r1 : TBS 0 0 (fun w n _ => K24F.r1 ((n : ℝ) +ᵥ w)) := by
  have h : TBS 0 0 (fun w n _ => Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TBS.mul TBS.phi0 TBS.Delta).mono (by linarith [Real.pi_pos]) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.r1, Compact.phi1, Work.Kernels.phi0])

lemma TBS.ktl24_E4cube : TBS 0 0 (fun w n _ => E4Fun ((n : ℝ) +ᵥ w) ^ 3) :=
  (((TBS.mul TBS.E4 TBS.E4).mul TBS.E4).mono (by norm_num) (by norm_num)).congr
    (fun w n z => by ring)

lemma TBS.ktl24_r2 : TBS 0 0 (fun w n _ => K24F.r2 ((n : ℝ) +ᵥ w)) := by
  have h : TBS 0 0 (fun w n _ => Work.Kernels.phi2 ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) := (TBS.mul TBS.phi2 TBS.E10).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.r2, Compact.phi2t, Work.Kernels.phi2])

lemma TBS.ktl24_R0 : TBS 0 0 (fun w n _ => K24F.R0 ((n : ℝ) +ᵥ w)) := by
  have h : TBS 0 0 (fun w n _ => Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * E4Fun ((n : ℝ) +ᵥ w) ^ 3) :=
    (TBS.mul TBS.phi0 TBS.ktl24_E4cube).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by simp only [K24F.R0, Compact.phi1, Work.Kernels.phi0])

lemma TBS.ktl24_j : TBS (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)) := TBS.j

/-! ## `Phiref`, `Q1`, `Uref`, `Th0` -/

lemma TBS.ktl24_Phiref : TBS 0 0 (fun w n z => K24F.Phiref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 0 (fun w n z => (1 - K24F.S0 z ^ 2)
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_one_sub_S0sq
      (TBS.const_mul 6 (TBS.add TBS.ktl24_r0 TBS.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TBS 0 0 (fun w n z => K24F.S0 z ^ 2
      * (12 * K24F.R0 ((n : ℝ) +ᵥ w) - 12096 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0sq
      (TBS.sub (TBS.const_mul 12 TBS.ktl24_R0) (TBS.const_mul 12096 TBS.ktl24_r1))).mono
      (le_refl 0) (by norm_num)
  have h3 : TBS 0 0 (fun w n z => -12 * K24F.R0 ((n : ℝ) +ᵥ w)
      + 8640 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TBS.add (TBS.const_mul (-12) TBS.ktl24_R0) (TBS.const_mul 8640 TBS.ktl24_r1)
  have h4 : TBS 0 0 (fun w n z => K24F.S0 z * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0 (TBS.const_mul 3456 TBS.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  exact (TBS.add (TBS.add (TBS.add h1 h2) h3) h4).congr (fun w n z => by
    rw [K24Fsm.phiref_jfree]; ring)

lemma TBS.ktl24_Q1 : TBS 0 0 (fun w n z => K24F.Q1 ((n : ℝ) +ᵥ w) z) := by
  have hz : ZC3 0 0 (fun z : ℍ => (1440 : ℂ) + 288 * K24F.S0 z) :=
    ((ZC3.const 0 le_rfl (1440 : ℂ)).add
      ((ZC3.const 0 le_rfl (288 : ℂ)).mul ZC3.ktl24_S0)).mono
      (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h1 : TBS 0 0 (fun w n z => ((1440 : ℂ) + 288 * K24F.S0 z)
      * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) hz (TBS.add TBS.ktl24_r0 TBS.ktl24_r2)).mono (le_refl 0) (by norm_num)
  have h2 : TBS 0 0 (fun w n z => -2880 * K24F.R0 ((n : ℝ) +ᵥ w)
      + 2073600 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TBS.add (TBS.const_mul (-2880) TBS.ktl24_R0) (TBS.const_mul 2073600 TBS.ktl24_r1)
  have h3 : TBS 0 0 (fun w n z => K24F.S0 z * (-576 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0 (TBS.const_mul (-576) TBS.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  have h4 : TBS 0 0 (fun w n z => K24F.S0 z * (580608 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0 (TBS.const_mul 580608 TBS.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  have h5 : TBS 0 0 (fun w n z => -82944 * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    TBS.const_mul (-82944) TBS.ktl24_r1
  have h6 : TBS 0 0 (fun w n z => K24F.S0 z * (2571264 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0 (TBS.const_mul 2571264 TBS.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  exact (TBS.sub (TBS.add (TBS.add (TBS.add (TBS.add h1 h2) h3) h4) h5) h6).congr
    (fun w n z => by rw [K24Fsm.q1_jfree]; ring)

lemma TBS.ktl24_Uref : TBS 0 0 (fun w n z => K24F.Uref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 0 (fun w n z => K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0sq (TBS.const_mul 1728 TBS.ktl24_r0)).mono
      (le_refl 0) (by norm_num)
  have h2 : TBS 0 0 (fun w n z => 1728 * K24F.r2 ((n : ℝ) +ᵥ w)) :=
    TBS.const_mul 1728 TBS.ktl24_r2
  exact (TBS.add h1 h2).congr (fun w n z => by simp only [K24F.Uref]; ring)

lemma TBS.ktl24_Th0 : TBS 0 0 (fun w n z => K24F.Th0 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 0 (fun w n z => K24F.S0 z * (3456 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0 (TBS.const_mul 3456 TBS.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  have h2 : TBS 0 0 (fun w n z => 24 * K24F.Phiref ((n : ℝ) +ᵥ w) z) :=
    TBS.const_mul 24 TBS.ktl24_Phiref
  exact (TBS.add (TBS.sub (TBS.add TBS.ktl24_Q1 h2) TBS.ktl24_Uref) h1).congr
    (fun w n z => by simp only [K24F.Th0]; ring)

/-! ## `Φ - Φref` and `Φ - Φref - q·Q⁽¹⁾` -/

private lemma ktl24_E4ne : ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) →
    w ∈ KEpsilon → (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
    E4Fun z ≠ 0 := by
  intro w n z t hn hw hz ht
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  exact K24F.E4_ne_zero_three z (by rw [hzim]; have h := hw.2; linarith)

lemma TBS.ktl24_Phi_sub_Phiref :
    TBS 0 2 (fun w n z => K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 2 (fun w n z => ((E4Fun z - 1) - (E2S z ^ 2 - K24F.S0 z ^ 2))
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E4sub1_sub_E2Ssq
      (TBS.const_mul 6 (TBS.add TBS.ktl24_r0 TBS.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TBS 0 2 (fun w n z => (12 * (E2S z ^ 2 - K24F.S0 z ^ 2) - 12 * (E4Fun z - 1))
      * K24F.R0 ((n : ℝ) +ᵥ w)) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_dev2 TBS.ktl24_R0).mono (le_refl 0) (by norm_num)
  have h3 : TBS 0 2 (fun w n z => (8640 * (E4Fun z - 1)
      - 12096 * (E2S z ^ 2 - K24F.S0 z ^ 2)) * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_dev3 TBS.ktl24_r1).mono (le_refl 0) (by norm_num)
  have h4 : TBS 0 2 (fun w n z => (E6Fun z * E2S z / E4Fun z - K24F.S0 z)
      * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E6E2S_div_E4_sub_S0
      (TBS.const_mul 3456 TBS.ktl24_r1)).mono (le_refl 0) (by norm_num)
  refine (TBS.add (TBS.add (TBS.add h1 h2) h3) h4).congr_tile (fun w n z t hn hw hz ht => ?_)
  rw [K24F.Phi_sub_Phiref_expanded ((n : ℝ) +ᵥ w) z (ktl24_E4ne w n z t hn hw hz ht)]
  ring

lemma TBS.ktl24_Phi_sub_Phiref_sub :
    TBS 0 4 (fun w n z => K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
      - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 4 (fun w n z => ((E4Fun z - 1 - 240 * qParamFun z) - K24F.B2 z)
      * (6 * (K24F.r0 ((n : ℝ) +ᵥ w) + K24F.r2 ((n : ℝ) +ᵥ w)))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_devb1
      (TBS.const_mul 6 (TBS.add TBS.ktl24_r0 TBS.ktl24_r2))).mono (le_refl 0) (by norm_num)
  have h2 : TBS 0 4 (fun w n z => (12 * K24F.B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
      * K24F.R0 ((n : ℝ) +ᵥ w)) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_devb2 TBS.ktl24_R0).mono (le_refl 0) (by norm_num)
  have h3 : TBS 0 4 (fun w n z => (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * K24F.B2 z)
      * K24F.r1 ((n : ℝ) +ᵥ w)) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_devb3 TBS.ktl24_r1).mono (le_refl 0) (by norm_num)
  have h4 : TBS 0 4 (fun w n z => (E6Fun z * E2S z / E4Fun z - K24F.S0 z
      + 24 * qParamFun z + 744 * qParamFun z * K24F.S0 z)
      * (3456 * K24F.r1 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_X4 (TBS.const_mul 3456 TBS.ktl24_r1)).mono
      (le_refl 0) (by norm_num)
  refine (TBS.add (TBS.add (TBS.add h1 h2) h3) h4).congr_tile (fun w n z t hn hw hz ht => ?_)
  rw [K24F.Phi_sub_Phiref_sub_expanded ((n : ℝ) +ᵥ w) z (ktl24_E4ne w n z t hn hw hz ht)]
  ring

/-! ## The five remainder groups -/

lemma TBS.ktl24_Sm1 :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm1 ((n : ℝ) +ᵥ w) z) := by
  have hA : TBS (2 * Real.pi) 2 (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w)
      * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z)) :=
    (TBS.mul TBS.ktl24_j TBS.ktl24_Phi_sub_Phiref).mono (by linarith [Real.pi_pos]) (by norm_num)
  have hB : TBS (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3
      * K24F.Q1 ((n : ℝ) +ᵥ w) z * (qParamFun z / DeltaFun z - 1)) := by
    have h0 : TBS 0 0 (fun w n z => E4Fun z ^ 3 * K24F.Q1 ((n : ℝ) +ᵥ w) z) :=
      (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E4cube TBS.ktl24_Q1).mono (le_refl 0) (by norm_num)
    have h1 : TBS 0 2 (fun w n z => (qParamFun z / DeltaFun z - 1)
        * (E4Fun z ^ 3 * K24F.Q1 ((n : ℝ) +ᵥ w) z)) :=
      (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_q_div_Delta_sub1 h0).mono (le_refl 0) (by norm_num)
    exact (h1.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  have hC : TBS (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3
      * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
          - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z) * (DeltaFun z)⁻¹) := by
    have h0 : TBS 0 2 (fun w n z => (DeltaFun z)⁻¹
        * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
            - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z)) :=
      (TBS.mul_ZCg3 (le_refl 0) ZCg3.ktl24_Delta_inv TBS.ktl24_Phi_sub_Phiref_sub).mono
        (le_refl 0) (by norm_num)
    have h1 : TBS 0 2 (fun w n z => E4Fun z ^ 3
        * ((DeltaFun z)⁻¹ * (K24F.Phi ((n : ℝ) +ᵥ w) z - K24F.Phiref ((n : ℝ) +ᵥ w) z
            - qParamFun z * K24F.Q1 ((n : ℝ) +ᵥ w) z))) :=
      (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E4cube h0).mono (le_refl 0) (by norm_num)
    exact (h1.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  exact (TBS.sub (TBS.sub hA hB) hC).congr (fun w n z => by simp only [K24F.Sm1]; ring)

lemma TBS.ktl24_Sm2 :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm2 ((n : ℝ) +ᵥ w) z) := by
  have hA : TBS (2 * Real.pi) 2 (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w)
      * K24F.Phiref ((n : ℝ) +ᵥ w) z * (1 - DeltaFun z / qParamFun z)) := by
    have h0 := TBS.mul TBS.ktl24_j TBS.ktl24_Phiref
    exact ((TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_one_sub_Delta_div_q h0).mono
      (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by ring)
  have hB : TBS (2 * Real.pi) 2 (fun w n z => E4Fun z ^ 3 * K24F.Phiref ((n : ℝ) +ᵥ w) z
      * ((DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24)) := by
    have h0 : TBS 0 0 (fun w n z => E4Fun z ^ 3 * K24F.Phiref ((n : ℝ) +ᵥ w) z) :=
      (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E4cube TBS.ktl24_Phiref).mono (le_refl 0) (by norm_num)
    exact ((TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_d1 h0).mono (by linarith [Real.pi_pos])
      (by norm_num)).congr (fun w n z => by ring)
  exact (TBS.sub hA hB).congr (fun w n z => by simp only [K24F.Sm2, K24F.d1])

lemma TBS.ktl24_Sm3 :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm3 ((n : ℝ) +ᵥ w) z) := by
  have h : TBS 0 2 (fun w n z => (K24F.S0 z * (E4Fun z ^ 3 - 1)
      - (E6Fun z * E2S z / E4Fun z - K24F.S0 z)) * (3456 * K24F.R0 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_Sm3bracket (TBS.const_mul 3456 TBS.ktl24_R0)).mono
      (le_refl 0) (by norm_num)
  exact (h.mono (by linarith [Real.pi_pos]) (by norm_num)).congr (fun w n z => by
    rw [K24F.Sm3_bracket]; ring)

lemma TBS.ktl24_Sm4 :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm4 ((n : ℝ) +ᵥ w) z) := by
  have h1 : TBS 0 2 (fun w n z => (E2S z ^ 2 - K24F.S0 z ^ 2)
      * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E2Ssq_sub_S0sq
      (TBS.const_mul 1728 TBS.ktl24_r0)).mono (le_refl 0) (by norm_num)
  have h2 : TBS 0 2 (fun w n z => (E4Fun z - 1) * (1728 * K24F.r2 ((n : ℝ) +ᵥ w))) :=
    (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_E4sub1 (TBS.const_mul 1728 TBS.ktl24_r2)).mono
      (le_refl 0) (by norm_num)
  have h3 : TBS 0 2 (fun w n z => (1 - E4Fun z ^ 3)
      * (K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))
        + 1728 * K24F.r2 ((n : ℝ) +ᵥ w))) := by
    have h0 : TBS 0 0 (fun w n z => K24F.S0 z ^ 2 * (1728 * K24F.r0 ((n : ℝ) +ᵥ w))
        + 1728 * K24F.r2 ((n : ℝ) +ᵥ w)) :=
      TBS.add ((TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_S0sq
        (TBS.const_mul 1728 TBS.ktl24_r0)).mono (le_refl 0) (by norm_num))
        (TBS.const_mul 1728 TBS.ktl24_r2)
    exact (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_one_sub_E4cube h0).mono (le_refl 0) (by norm_num)
  exact ((TBS.add (TBS.add h1 h2) h3).mono (by linarith [Real.pi_pos]) (by norm_num)).congr
    (fun w n z => by rw [K24F.Sm4_split]; ring)

lemma TBS.ktl24_Sm5 :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm5 ((n : ℝ) +ᵥ w) z) := by
  have h : TBS (2 * Real.pi) 2 (fun w n z => DeltaFun z * (-jInvariantFun ((n : ℝ) +ᵥ w))
      * K24F.Th0 ((n : ℝ) +ᵥ w) z) := by
    have h0 : TBS (2 * Real.pi) 2 (fun w n z =>
        DeltaFun z * (-jInvariantFun ((n : ℝ) +ᵥ w))) :=
      (TBS.mul_ZC3 (le_refl 0) ZC3.ktl24_Delta (TBS.neg TBS.ktl24_j)).mono
        (le_refl (2 * Real.pi)) (by norm_num)
    exact (TBS.mul h0 TBS.ktl24_Th0).mono (by linarith [Real.pi_pos]) (by norm_num)
  exact h.congr (fun w n z => by rw [K24F.Sm5_split]; simp only [K24F.Th0]; ring)

/-! ## The main theorem, `d = 24` -/

lemma TBS.ktl24_Sm_sum :
    TBS (2 * Real.pi) 2 (fun w n z => K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
      + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
      + K24F.Sm5 ((n : ℝ) +ᵥ w) z) :=
  (TBS.add (TBS.add (TBS.add (TBS.add TBS.ktl24_Sm1 TBS.ktl24_Sm2) TBS.ktl24_Sm3)
    TBS.ktl24_Sm4) TBS.ktl24_Sm5).congr (fun w n z => by ring)

theorem TBS24TileTail :
    TBS Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) z) := by
  have hZ : TBS (2 * Real.pi) (2 + 0) (fun w n z => (z : ℂ) ^ 2
      * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
        + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
        + K24F.Sm5 ((n : ℝ) +ᵥ w) z)) :=
    TBS.mul_ZC3 (by norm_num) ZC3.ktl24_zsq TBS.ktl24_Sm_sum
  have hmain : TBS (2 * Real.pi + 0) ((2 + 0) + 0) (fun w n z => K24F.c * (z : ℂ) ^ 2
      * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
        + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
        + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
      * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) := by
    have hZ' : TBS (2 * Real.pi) (2 + 0) (fun w n z => K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
          + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
          + K24F.Sm5 ((n : ℝ) +ᵥ w) z)) :=
      (TBS.const_mul K24F.c hZ).congr (fun w n z => by ring)
    exact TBS.mul hZ' TBS.ktl8_invdivisor
  refine (hmain.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_)
  have hzim : z.im = t := K24F.im_of_coe_eq_axis hz
  have hz3 : (3:ℝ) ≤ z.im := by rw [hzim]; have h := hw.2; linarith
  have hE4 : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz3
  have hd := tileDivisorLowerSharp w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hne : DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z) ≠ 0 :=
    mul_ne_zero hΔz hJ
  have hdiff := K24F.KPlus24_diff ((n : ℝ) +ᵥ w) z hJ hE4
  rw [show K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
          + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
          + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
        * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹
      = K24F.c * (z : ℂ) ^ 2
          * (K24F.Sm1 ((n : ℝ) +ᵥ w) z + K24F.Sm2 ((n : ℝ) +ᵥ w) z
            + K24F.Sm3 ((n : ℝ) +ᵥ w) z + K24F.Sm4 ((n : ℝ) +ᵥ w) z
            + K24F.Sm5 ((n : ℝ) +ᵥ w) z)
          / (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)) from by ring]
  rw [div_eq_iff hne, ← hdiff]
  ring


end

end Work.Asymptotics.Tile
