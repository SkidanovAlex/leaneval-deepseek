import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Asymptotics.KhatE1Core (Big)

noncomputable section

/-! ## Local notation -/

private def qF (τ : ℍ) : ℂ := Work.Kernels.qParamFun τ

private def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

private def E4F (τ : ℍ) : ℂ := Work.Kernels.E4Fun τ
private def E6F (τ : ℍ) : ℂ := Work.Kernels.E6Fun τ
private def E8F (τ : ℍ) : ℂ := E4F τ ^ 2
private def E10F (τ : ℍ) : ℂ := E4F τ * E6F τ
private def DeltaF (τ : ℍ) : ℂ := Work.Kernels.DeltaFun τ
private def jF (τ : ℍ) : ℂ := Work.Kernels.jInvariantFun τ
private def psi2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := Work.Kernels.psi2 ℓ τ
private def psi4F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := Work.Kernels.psi4 ℓ τ

private def W (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi2F ℓ τ * E10F τ - psi4F ℓ τ * E8F τ

private def M2q1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ
private def M4q1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ
private def M2f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ + (48 * LamF ℓ τ + 2636) * qF τ ^ 2
private def M4f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ - (1824 * LamF ℓ τ + 25972) * qF τ ^ 2
private def Q4 (τ : ℍ) : ℂ := 1 + 240 * qF τ + 2160 * qF τ ^ 2
private def Q6 (τ : ℍ) : ℂ := 1 - 504 * qF τ - 16632 * qF τ ^ 2
private def ME10 (τ : ℍ) : ℂ := Q4 τ * Q6 τ
private def ME8 (τ : ℍ) : ℂ := Q4 τ ^ 2
private def MW (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (1152 - 1152 * LamF ℓ τ) * qF τ + (-267264 * LamF ℓ τ + 278016) * qF τ ^ 2
private def modeljW (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (1152 - 1152 * LamF ℓ τ) * qF τ + (-1124352 * LamF ℓ τ + 1135104) * qF τ ^ 2
private def c1F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := 516096 - 442368 * LamF ℓ τ

private def rE4q2f (τ : ℍ) : ℂ := E4F τ - (1 + 240 * qF τ + 2160 * qF τ ^ 2)
private def rE6q2f (τ : ℍ) : ℂ := E6F τ - (1 - 504 * qF τ - 16632 * qF τ ^ 2)
private def rE4f (τ : ℍ) : ℂ := E4F τ - (1 + 240 * qF τ)
private def rE6f (τ : ℍ) : ℂ := E6F τ - (1 - 504 * qF τ)
private def rE10q1 (τ : ℍ) : ℂ := E10F τ - (1 - 264 * qF τ)
private def rE8q1 (τ : ℍ) : ℂ := E8F τ - (1 + 480 * qF τ)
private def rE10f (τ : ℍ) : ℂ := E10F τ - ME10 τ
private def rE8f (τ : ℍ) : ℂ := E8F τ - ME8 τ
private def rr2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi2F ℓ τ - M2f ℓ τ
private def rr4 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi4F ℓ τ - M4f ℓ τ
private def rr2q1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi2F ℓ τ - M2q1 ℓ τ
private def rr4q1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi4F ℓ τ - M4q1 ℓ τ

private def Rpoly (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (2582880 - 39168 * LamF ℓ τ)
    + (-50203872 + 80002944 * LamF ℓ τ) * qF τ
    + (2349803520 + 1266554880 * LamF ℓ τ) * qF τ ^ 2
    + (26476346880 + 6785648640 * LamF ℓ τ) * qF τ ^ 3

/-! ## Elementary facts about `q` -/

private lemma qF_ne_zero (τ : ℍ) : qF τ ≠ 0 := by
  simp only [qF, Work.Kernels.qParamFun]
  exact Complex.exp_ne_zero _

private lemma qF_eq_Ept_sq (τ : ℍ) : qF τ = Work.Residues.Ept τ ^ 2 := by
  rw [qF, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
  congr 1; ring

private lemma norm_qF (τ : ℍ) : ‖qF τ‖ = ‖Work.Residues.Ept τ‖ ^ 2 := by
  rw [qF, Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, sq, ← Real.exp_add]
  congr 1; ring

private lemma norm_qParam_eq (τ : ℍ) :
    ‖Work.Kernels.qParamFun τ‖ = ‖Work.Residues.Ept τ‖ ^ 2 := by
  simpa only [qF] using norm_qF τ

/-! ## The `Big` calculus conveniences -/

private lemma Big_add_same {k : ℕ} {f g : ℍ → ℂ} (hf : Big k f) (hg : Big k g) :
    Big k (fun τ => f τ + g τ) :=
  (Big.add hf hg).mono (l := k) (by simp)

private lemma Big_sub_same {k : ℕ} {f g : ℍ → ℂ} (hf : Big k f) (hg : Big k g) :
    Big k (fun τ => f τ - g τ) :=
  (Big.sub hf hg).mono (l := k) (by simp)

/-! ## The `Big` inputs -/

private lemma big_q1 : Big 1 (fun τ : ℍ => qF τ) :=
  ⟨1, 0, one_pos, le_rfl, fun τ _ => by simp [qF]⟩

private lemma big_q (k : ℕ) : Big k (fun τ : ℍ => qF τ ^ k) := by
  have h := Big.pow big_q1 k
  rwa [one_mul] at h

private lemma big_Lam (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => LamF ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (Real.pi : ℂ) * Complex.I * (τ : ℂ)) := by
    refine Big.of_scale (C := Real.pi) (N := 1) (by positivity) (by norm_num) (fun τ _ => ?_)
    rw [Real.rpow_one, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (Work.Kernels.coe_norm_le_scale τ) Real.pi_pos.le
  have h2 : Big 0 (fun _ : ℍ => Work.Asymptotics.Compact.cuspC ℓ) :=
    Big.const (Work.Asymptotics.Compact.cuspC ℓ)
  exact (Big_add_same h1 h2).congr (fun τ => by simp only [LamF]; try ring)

private lemma big_one_add (c : ℂ) : Big 0 (fun τ : ℍ => (1 : ℂ) + c * qF τ) := by
  have h := Big_add_same (Big.const (1 : ℂ))
    ((Big.const_mul c big_q1).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by ring)

private lemma big_one_sub (c : ℂ) : Big 0 (fun τ : ℍ => (1 : ℂ) - c * qF τ) := by
  have h := Big_sub_same (Big.const (1 : ℂ))
    ((Big.const_mul c big_q1).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by ring)

private lemma big_rE4q2f : Big 3 (fun τ : ℍ => rE4q2f τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.e4ThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖rE4q2f τ‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h' := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : rE4q2f τ = Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
      - 2160 * Work.Kernels.qParamFun τ ^ 2 := by
    simp only [rE4q2f, E4F, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  exact h'

private lemma big_rE6q2f : Big 3 (fun τ : ℍ => rE6q2f τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.e6ThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖rE6q2f τ‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h' := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : rE6q2f τ = Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
      + 16632 * Work.Kernels.qParamFun τ ^ 2 := by
    simp only [rE6q2f, E6F, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  exact h'

private lemma big_rE4f : Big 2 (fun τ : ℍ => rE4f τ) := by
  have h : Big 2 (fun τ : ℍ => rE4q2f τ + 2160 * qF τ ^ 2) :=
    Big_add_same (big_rE4q2f.mono (l := 2) (by norm_num))
      (Big.const_mul (2160 : ℂ) (big_q 2))
  exact h.congr (fun τ => by simp only [rE4f, rE4q2f]; try ring)

private lemma big_rE6f : Big 2 (fun τ : ℍ => rE6f τ) := by
  have h : Big 2 (fun τ : ℍ => rE6q2f τ - 16632 * qF τ ^ 2) :=
    Big_sub_same (big_rE6q2f.mono (l := 2) (by norm_num))
      (Big.const_mul (16632 : ℂ) (big_q 2))
  exact h.congr (fun τ => by simp only [rE6f, rE6q2f]; try ring)

private lemma big_rDelta : Big 2 (fun τ : ℍ => DeltaF τ - qF τ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.DeltaExpansion
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖DeltaF τ - qF τ‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 2
  have h' := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : DeltaF τ - qF τ = Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2 := by
    simp only [DeltaF]; rw [qF_eq_Ept_sq]
  have hq : ‖Work.Residues.Ept τ‖ ^ 4 = ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [norm_qParam_eq]; ring
  rw [h2, Real.rpow_zero, mul_one]
  calc ‖Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2‖
      ≤ C * ‖Work.Residues.Ept τ‖ ^ 4 := h'
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by rw [hq]

private lemma big_rjq : Big 2 (fun τ : ℍ => jF τ * qF τ - (1 + 744 * qF τ)) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.jq_second_order
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖jF τ * qF τ - (1 + 744 * qF τ)‖
      ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 2
  have h' := h τ hτ.2
  have h2 : jF τ * qF τ - (1 + 744 * qF τ)
      = Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
          - 744 * Work.Kernels.qParamFun τ := by
    simp only [jF, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  exact h'

private lemma big_rr2 (ℓ : Work.Kernels.LogLambdaData) : Big 3 (fun τ : ℍ => rr2 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  show ‖rr2 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h' := (h τ hτ).1
  have h2 : rr2 ℓ τ
      = Work.Kernels.psi2 ℓ τ
        - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
        - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 408)
            * Work.Kernels.qParamFun τ
        - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 2636)
            * Work.Kernels.qParamFun τ ^ 2 := by
    simp only [rr2, M2f, psi2F, LamF, qF]; ring
  rw [h2]; exact h'

private lemma big_rr4 (ℓ : Work.Kernels.LogLambdaData) : Big 3 (fun τ : ℍ => rr4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  show ‖rr4 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h' := (h τ hτ).2
  have h2 : rr4 ℓ τ
      = Work.Kernels.psi4 ℓ τ
        - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
        + (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 744)
            * Work.Kernels.qParamFun τ
        + (1824 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 25972)
            * Work.Kernels.qParamFun τ ^ 2 := by
    simp only [rr4, M4f, psi4F, LamF, qF]; ring
  rw [h2]; exact h'

private lemma big_Q4 : Big 0 (fun τ : ℍ => Q4 τ) := by
  have h := Big_add_same (big_one_add 240)
    ((Big.const_mul (2160 : ℂ) (big_q 2)).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [Q4]; try ring)

private lemma big_Q6 : Big 0 (fun τ : ℍ => Q6 τ) := by
  have h := Big_sub_same (big_one_sub 504)
    ((Big.const_mul (16632 : ℂ) (big_q 2)).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [Q6]; try ring)

private lemma big_ME10 : Big 0 (fun τ : ℍ => ME10 τ) :=
  (Big.mul big_Q4 big_Q6).congr (fun τ => by simp only [ME10]; try ring)

private lemma big_ME8 : Big 0 (fun τ : ℍ => ME8 τ) :=
  ((big_Q4).pow 2).congr (fun τ => by simp only [ME8]; try ring)

private lemma big_E4F : Big 0 (fun τ : ℍ => E4F τ) := by
  have h := Big_add_same (big_one_add 240) (big_rE4f.mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [rE4f, E4F]; try ring)

private lemma big_E6F : Big 0 (fun τ : ℍ => E6F τ) := by
  have h := Big_add_same (big_one_sub 504) (big_rE6f.mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [rE6f, E6F]; try ring)

private lemma big_E8F : Big 0 (fun τ : ℍ => E8F τ) :=
  ((big_E4F).pow 2).congr (fun τ => by simp only [E8F]; try ring)

private lemma big_E10F : Big 0 (fun τ : ℍ => E10F τ) :=
  (Big.mul big_E4F big_E6F).congr (fun τ => by simp only [E10F]; try ring)

private lemma big_M2q1 (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => M2q1 ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (2 : ℂ) * LamF ℓ τ) := Big.const_mul 2 (big_Lam ℓ)
  have h2 : Big 0 (fun τ : ℍ => (48 * LamF ℓ τ + 408) * qF τ) :=
    (Big.mul (Big_add_same (Big.const_mul 48 (big_Lam ℓ)) (Big.const (408 : ℂ))) big_q1).mono
      (l := 0) (by norm_num)
  exact (Big_add_same h1 h2).congr (fun τ => by simp only [M2q1]; try ring)

private lemma big_M4q1 (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => M4q1 ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (2 : ℂ) * LamF ℓ τ) := Big.const_mul 2 (big_Lam ℓ)
  have h2 : Big 0 (fun τ : ℍ => (288 * LamF ℓ τ + 744) * qF τ) :=
    (Big.mul (Big_add_same (Big.const_mul 288 (big_Lam ℓ)) (Big.const (744 : ℂ))) big_q1).mono
      (l := 0) (by norm_num)
  exact (Big_sub_same h1 h2).congr (fun τ => by simp only [M4q1]; try ring)

private lemma big_M2f (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => M2f ℓ τ) := by
  have h2 : Big 0 (fun τ : ℍ => (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    (Big.mul (Big_add_same (Big.const_mul 48 (big_Lam ℓ)) (Big.const (2636 : ℂ))) (big_q 2)).mono
      (l := 0) (by norm_num)
  exact (Big_add_same (big_M2q1 ℓ) h2).congr (fun τ => by simp only [M2f, M2q1]; try ring)

private lemma big_M4f (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => M4f ℓ τ) := by
  have h2 : Big 0 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    (Big.mul (Big_add_same (Big.const_mul 1824 (big_Lam ℓ)) (Big.const (25972 : ℂ))) (big_q 2)).mono
      (l := 0) (by norm_num)
  exact (Big_sub_same (big_M4q1 ℓ) h2).congr (fun τ => by simp only [M4f, M4q1]; try ring)

private lemma big_MW (ℓ : Work.Kernels.LogLambdaData) : Big 1 (fun τ : ℍ => MW ℓ τ) := by
  have h1 : Big 1 (fun τ : ℍ => (1152 - 1152 * LamF ℓ τ) * qF τ) :=
    Big.mul (Big_sub_same (Big.const (1152 : ℂ)) (Big.const_mul 1152 (big_Lam ℓ))) big_q1
  have h2 : Big 1 (fun τ : ℍ => (-267264 * LamF ℓ τ + 278016) * qF τ ^ 2) :=
    (Big.mul (Big_add_same (Big.const_mul (-267264) (big_Lam ℓ)) (Big.const (278016 : ℂ)))
      (big_q 2)).mono (l := 1) (by norm_num)
  exact (Big_add_same h1 h2).congr (fun τ => by simp only [MW]; try ring)

private lemma big_Rpoly (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Rpoly ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (2582880 : ℂ) - 39168 * LamF ℓ τ) :=
    Big_sub_same (Big.const (2582880 : ℂ)) (Big.const_mul 39168 (big_Lam ℓ))
  have h2 : Big 0 (fun τ : ℍ => (-50203872 + 80002944 * LamF ℓ τ) * qF τ) :=
    (Big.mul (Big_add_same (Big.const (-50203872 : ℂ)) (Big.const_mul 80002944 (big_Lam ℓ)))
      big_q1).mono (l := 0) (by norm_num)
  have h3 : Big 0 (fun τ : ℍ => (2349803520 + 1266554880 * LamF ℓ τ) * qF τ ^ 2) :=
    (Big.mul (Big_add_same (Big.const (2349803520 : ℂ)) (Big.const_mul 1266554880 (big_Lam ℓ)))
      (big_q 2)).mono (l := 0) (by norm_num)
  have h4 : Big 0 (fun τ : ℍ => (26476346880 + 6785648640 * LamF ℓ τ) * qF τ ^ 3) :=
    (Big.mul (Big_add_same (Big.const (26476346880 : ℂ)) (Big.const_mul 6785648640 (big_Lam ℓ)))
      (big_q 3)).mono (l := 0) (by norm_num)
  exact (Big_add_same (Big_add_same (Big_add_same h1 h2) h3) h4).congr
    (fun τ => by simp only [Rpoly]; try ring)

private lemma big_rr2q1 (ℓ : Work.Kernels.LogLambdaData) : Big 2 (fun τ : ℍ => rr2q1 ℓ τ) := by
  have h2 : Big 2 (fun τ : ℍ => (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    Big.mul (Big_add_same (Big.const_mul 48 (big_Lam ℓ)) (Big.const (2636 : ℂ))) (big_q 2)
  exact (Big_add_same ((big_rr2 ℓ).mono (l := 2) (by norm_num)) h2).congr
    (fun τ => by simp only [rr2, rr2q1, M2f, M2q1]; try ring)

private lemma big_rr4q1 (ℓ : Work.Kernels.LogLambdaData) : Big 2 (fun τ : ℍ => rr4q1 ℓ τ) := by
  have h2 : Big 2 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    Big.mul (Big_add_same (Big.const_mul 1824 (big_Lam ℓ)) (Big.const (25972 : ℂ))) (big_q 2)
  exact (Big_sub_same ((big_rr4 ℓ).mono (l := 2) (by norm_num)) h2).congr
    (fun τ => by simp only [rr4, rr4q1, M4f, M4q1]; try ring)

private lemma big_rE10f : Big 3 (fun τ : ℍ => rE10f τ) := by
  have h1 : Big 3 (fun τ : ℍ => rE4q2f τ * E6F τ) := Big.mul big_rE4q2f big_E6F
  have h2 : Big 3 (fun τ : ℍ => Q4 τ * rE6q2f τ) := Big.mul big_Q4 big_rE6q2f
  exact (Big_add_same h1 h2).congr
    (fun τ => by simp only [rE10f, ME10, rE4q2f, rE6q2f, Q4, Q6, E10F, E6F]; try ring)

private lemma big_rE8f : Big 3 (fun τ : ℍ => rE8f τ) := by
  have h1 : Big 3 (fun τ : ℍ => rE4q2f τ * (E4F τ + Q4 τ)) :=
    Big.mul big_rE4q2f (Big_add_same big_E4F big_Q4)
  exact h1.congr (fun τ => by simp only [rE8f, ME8, rE4q2f, Q4, E8F]; try ring)

private lemma big_rE10q1 : Big 2 (fun τ : ℍ => rE10q1 τ) := by
  have h1 : Big 2 (fun τ : ℍ => rE4f τ * E6F τ) := Big.mul big_rE4f big_E6F
  have h2 : Big 2 (fun τ : ℍ => (1 + 240 * qF τ) * rE6f τ) :=
    Big.mul (big_one_add 240) big_rE6f
  have h3 : Big 2 (fun τ : ℍ => (-120960 : ℂ) * qF τ ^ 2) :=
    Big.const_mul (-120960) (big_q 2)
  exact (Big_add_same (Big_add_same h1 h2) h3).congr
    (fun τ => by simp only [rE10q1, E10F, rE4f, rE6f]; try ring)

private lemma big_rE8q1 : Big 2 (fun τ : ℍ => rE8q1 τ) := by
  have h1 : Big 2 (fun τ : ℍ => rE4f τ * (E4F τ + (1 + 240 * qF τ))) :=
    Big.mul big_rE4f (Big_add_same big_E4F (big_one_add 240))
  have h2 : Big 2 (fun τ : ℍ => (57600 : ℂ) * qF τ ^ 2) := Big.const_mul 57600 (big_q 2)
  exact (Big_add_same h1 h2).congr
    (fun τ => by simp only [rE8q1, E8F, rE4f]; try ring)

private lemma big_psi2F (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => psi2F ℓ τ) := by
  have h : Big 0 (fun τ : ℍ => M2f ℓ τ + rr2 ℓ τ) :=
    Big_add_same (big_M2f ℓ) ((big_rr2 ℓ).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [rr2]; try ring)

private lemma big_psi4F (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => psi4F ℓ τ) := by
  have h : Big 0 (fun τ : ℍ => M4f ℓ τ + rr4 ℓ τ) :=
    Big_add_same (big_M4f ℓ) ((big_rr4 ℓ).mono (l := 0) (by norm_num))
  exact h.congr (fun τ => by simp only [rr4]; try ring)

private lemma big_W (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => W ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => psi2F ℓ τ * E10F τ) := Big.mul (big_psi2F ℓ) big_E10F
  have h2 : Big 0 (fun τ : ℍ => psi4F ℓ τ * E8F τ) := Big.mul (big_psi4F ℓ) big_E8F
  exact (Big_sub_same h1 h2).congr (fun τ => by simp only [W]; try ring)

/-! ## The algebraic identities -/

/-- The `q`-cleared first-order expansion of `E1combo24`, as an exact identity. -/
private lemma qE_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (qF τ * E1combo24 ℓ τ - c1F ℓ τ * qF τ ^ 2)
      = 27648 * (qF τ * (E4F τ ^ 3 - 1 - 720 * qF τ))
        - 24 * ((jF τ * qF τ) * W ℓ τ
            - ((1152 - 1152 * LamF ℓ τ) * qF τ + (-1124352 * LamF ℓ τ + 1135104) * qF τ ^ 2))
        - 20570112 * (qF τ * (DeltaF τ - qF τ))
        + 15744 * (qF τ * (psi2F ℓ τ * E10F τ
            - (2 * LamF ℓ τ + (408 - 480 * LamF ℓ τ) * qF τ)))
        - 29568 * (qF τ * (psi4F ℓ τ * E8F τ
            - (2 * LamF ℓ τ + (672 * LamF ℓ τ - 744) * qF τ))) := by
  have hjd : Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ
      = Work.Kernels.E4Fun τ ^ 3 := by
    rw [mul_comm]; exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  simp only [E1combo24, qF, LamF, E10F, E8F, E4F, E6F, jF, DeltaF, psi2F, psi4F, W, c1F,
    Work.Kernels.E8Fun, Work.Kernels.E10Fun]
  rw [hjd]
  ring

private lemma poly_p_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    qF τ ^ 3 * Rpoly ℓ τ
      = M2f ℓ τ * ME10 τ - M4f ℓ τ * ME8 τ - MW ℓ τ := by
  simp only [Rpoly, M2f, M4f, ME10, ME8, MW, Q4, Q6]
  ring

private lemma poly_q_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    744 * (-267264 * LamF ℓ τ + 278016) * qF τ ^ 3
      = (1 + 744 * qF τ) * MW ℓ τ - modeljW ℓ τ := by
  simp only [MW, modeljW]; ring

private lemma Wdiff_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (rr2 ℓ τ * E10F τ + M2f ℓ τ * rE10f τ) - (rr4 ℓ τ * E8F τ + M4f ℓ τ * rE8f τ)
        + (M2f ℓ τ * ME10 τ - M4f ℓ τ * ME8 τ - MW ℓ τ)
      = W ℓ τ - MW ℓ τ := by
  simp only [rr2, rr4, rE10f, rE8f, W, M2f, M4f, ME10, ME8]; ring

private lemma jWdiff_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (jF τ * qF τ - (1 + 744 * qF τ)) * MW ℓ τ
        + (jF τ * qF τ - (1 + 744 * qF τ)) * (W ℓ τ - MW ℓ τ)
        + (1 + 744 * qF τ) * (W ℓ τ - MW ℓ τ)
        + ((1 + 744 * qF τ) * MW ℓ τ - modeljW ℓ τ)
      = (jF τ * qF τ) * W ℓ τ - modeljW ℓ τ := by
  ring

/-! ## The `Big` estimates for the pieces -/

private lemma big_E4cube_diff : Big 2 (fun τ : ℍ => E4F τ ^ 3 - 1 - 720 * qF τ) := by
  have hbr : Big 0 (fun τ : ℍ => E4F τ ^ 2 + E4F τ * (1 + 240 * qF τ) + (1 + 240 * qF τ) ^ 2) :=
    Big_add_same (Big_add_same ((big_E4F).pow 2) (Big.mul big_E4F (big_one_add 240)))
      ((big_one_add 240).pow 2)
  have h1 : Big 2 (fun τ : ℍ => (E4F τ - (1 + 240 * qF τ))
      * (E4F τ ^ 2 + E4F τ * (1 + 240 * qF τ) + (1 + 240 * qF τ) ^ 2)) :=
    Big.mul big_rE4f hbr
  have h2 : Big 2 (fun τ : ℍ => (1 + 240 * qF τ) ^ 3 - (1 + 720 * qF τ)) := by
    have hb : Big 2 (fun τ : ℍ => (172800 : ℂ) * qF τ ^ 2) := Big.const_mul 172800 (big_q 2)
    have hc : Big 2 (fun τ : ℍ => (13824000 : ℂ) * qF τ ^ 3) :=
      (Big.const_mul 13824000 (big_q 3)).mono (l := 2) (by norm_num)
    exact (Big_add_same hb hc).congr (fun τ => by ring)
  exact (Big_add_same h1 h2).congr (fun τ => by ring)

private lemma big_psi2E10 (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => psi2F ℓ τ * E10F τ
      - (2 * LamF ℓ τ + (408 - 480 * LamF ℓ τ) * qF τ)) := by
  have h1 : Big 2 (fun τ : ℍ => rr2q1 ℓ τ * E10F τ) := Big.mul (big_rr2q1 ℓ) big_E10F
  have h2 : Big 2 (fun τ : ℍ => M2q1 ℓ τ * rE10q1 τ) := Big.mul (big_M2q1 ℓ) big_rE10q1
  have h3 : Big 2 (fun τ : ℍ => (-(12672 * LamF ℓ τ + 107712)) * qF τ ^ 2) :=
    Big.mul (Big.neg (Big_add_same (Big.const_mul 12672 (big_Lam ℓ)) (Big.const (107712 : ℂ))))
      (big_q 2)
  exact (Big_add_same (Big_add_same h1 h2) h3).congr
    (fun τ => by simp only [rr2q1, M2q1, rE10q1, E10F]; try ring)

private lemma big_psi4E8 (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => psi4F ℓ τ * E8F τ
      - (2 * LamF ℓ τ + (672 * LamF ℓ τ - 744) * qF τ)) := by
  have h1 : Big 2 (fun τ : ℍ => rr4q1 ℓ τ * E8F τ) := Big.mul (big_rr4q1 ℓ) big_E8F
  have h2 : Big 2 (fun τ : ℍ => M4q1 ℓ τ * rE8q1 τ) := Big.mul (big_M4q1 ℓ) big_rE8q1
  have h3 : Big 2 (fun τ : ℍ => (-(138240 * LamF ℓ τ + 357120)) * qF τ ^ 2) :=
    Big.mul (Big.neg (Big_add_same (Big.const_mul 138240 (big_Lam ℓ)) (Big.const (357120 : ℂ))))
      (big_q 2)
  exact (Big_add_same (Big_add_same h1 h2) h3).congr
    (fun τ => by simp only [rr4q1, M4q1, rE8q1, E8F]; try ring)

private lemma big_poly_p (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => M2f ℓ τ * ME10 τ - M4f ℓ τ * ME8 τ - MW ℓ τ) :=
  (Big.mul (big_q 3) (big_Rpoly ℓ)).congr (fun τ => (poly_p_identity ℓ τ))

private lemma big_poly_q (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => (1 + 744 * qF τ) * MW ℓ τ - modeljW ℓ τ) :=
  (Big.mul (Big.const_mul 744
      (Big_add_same (Big.const_mul (-267264) (big_Lam ℓ)) (Big.const (278016 : ℂ))))
    (big_q 3)).congr (fun τ => (poly_q_identity ℓ τ))

private lemma big_Wdiff (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => W ℓ τ - MW ℓ τ) := by
  have hA1 : Big 3 (fun τ : ℍ => rr2 ℓ τ * E10F τ) := Big.mul (big_rr2 ℓ) big_E10F
  have hA2 : Big 3 (fun τ : ℍ => M2f ℓ τ * rE10f τ) := Big.mul (big_M2f ℓ) big_rE10f
  have hA : Big 3 (fun τ : ℍ => rr2 ℓ τ * E10F τ + M2f ℓ τ * rE10f τ) := Big_add_same hA1 hA2
  have hB1 : Big 3 (fun τ : ℍ => rr4 ℓ τ * E8F τ) := Big.mul (big_rr4 ℓ) big_E8F
  have hB2 : Big 3 (fun τ : ℍ => M4f ℓ τ * rE8f τ) := Big.mul (big_M4f ℓ) big_rE8f
  have hB : Big 3 (fun τ : ℍ => rr4 ℓ τ * E8F τ + M4f ℓ τ * rE8f τ) := Big_add_same hB1 hB2
  exact (Big_add_same (Big_sub_same hA hB) (big_poly_p ℓ)).congr
    (fun τ => (Wdiff_identity ℓ τ))

private lemma big_jWdiff (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => (jF τ * qF τ) * W ℓ τ - modeljW ℓ τ) := by
  have hA : Big 3 (fun τ : ℍ => (jF τ * qF τ - (1 + 744 * qF τ)) * MW ℓ τ) :=
    Big.mul big_rjq (big_MW ℓ)
  have hB : Big 3 (fun τ : ℍ => (jF τ * qF τ - (1 + 744 * qF τ)) * (W ℓ τ - MW ℓ τ)) :=
    (Big.mul big_rjq (big_Wdiff ℓ)).mono (l := 3) (by norm_num)
  have hC : Big 3 (fun τ : ℍ => (1 + 744 * qF τ) * (W ℓ τ - MW ℓ τ)) :=
    Big.mul (big_one_add 744) (big_Wdiff ℓ)
  exact (Big_add_same (Big_add_same (Big_add_same hA hB) hC) (big_poly_q ℓ)).congr
    (fun τ => (jWdiff_identity ℓ τ))

/-! ## Assembly -/

private lemma big_qE (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => qF τ * E1combo24 ℓ τ - c1F ℓ τ * qF τ ^ 2) := by
  have h1 : Big 3 (fun τ : ℍ => 27648 * (qF τ * (E4F τ ^ 3 - 1 - 720 * qF τ))) :=
    Big.const_mul 27648 (Big.mul big_q1 big_E4cube_diff)
  have h2 : Big 3 (fun τ : ℍ => -24 * ((jF τ * qF τ) * W ℓ τ - modeljW ℓ τ)) :=
    Big.const_mul (-24) (big_jWdiff ℓ)
  have h3 : Big 3 (fun τ : ℍ => -20570112 * (qF τ * (DeltaF τ - qF τ))) :=
    Big.const_mul (-20570112) (Big.mul big_q1 big_rDelta)
  have h4 : Big 3 (fun τ : ℍ => 15744 * (qF τ * (psi2F ℓ τ * E10F τ
      - (2 * LamF ℓ τ + (408 - 480 * LamF ℓ τ) * qF τ)))) :=
    Big.const_mul 15744 (Big.mul big_q1 (big_psi2E10 ℓ))
  have h5 : Big 3 (fun τ : ℍ => -29568 * (qF τ * (psi4F ℓ τ * E8F τ
      - (2 * LamF ℓ τ + (672 * LamF ℓ τ - 744) * qF τ)))) :=
    Big.const_mul (-29568) (Big.mul big_q1 (big_psi4E8 ℓ))
  have h := Big_add_same (Big_add_same (Big_add_same (Big_add_same h1 h2) h3) h4) h5
  refine h.congr (fun τ => ?_)
  simp only [modeljW]
  rw [qE_identity ℓ τ]
  ring

private lemma Big_div_q {k : ℕ} {f : ℍ → ℂ} (h : Big (k + 1) f) :
    Big k (fun τ => f τ / qF τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have hqpos : 0 < ‖qF τ‖ := norm_pos_iff.mpr (qF_ne_zero τ)
  have h1 : ‖f τ‖ / ‖qF τ‖ ≤ (C * (Work.Kernels.scale τ) ^ N * ‖qF τ‖ ^ (k + 1)) / ‖qF τ‖ :=
    div_le_div_of_nonneg_right (hb τ hτ) hqpos.le
  have h2 : C * (Work.Kernels.scale τ) ^ N * ‖qF τ‖ ^ (k + 1) / ‖qF τ‖
      = C * (Work.Kernels.scale τ) ^ N * ‖qF τ‖ ^ k := by
    have hqne : ‖qF τ‖ ≠ 0 := ne_of_gt hqpos
    rw [pow_succ,
      show C * (Work.Kernels.scale τ) ^ N * (‖qF τ‖ ^ k * ‖qF τ‖)
        = (C * (Work.Kernels.scale τ) ^ N * ‖qF τ‖ ^ k) * ‖qF τ‖ by ring]
    exact mul_div_cancel_right₀ _ hqne
  rw [norm_div]
  calc ‖f τ‖ / ‖qF τ‖
      ≤ C * (Work.Kernels.scale τ) ^ N * ‖qF τ‖ ^ k := le_trans h1 (le_of_eq h2)
    _ = C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ k := by
        simp only [qF]

/-! ## The target -/

theorem E1combo24_first_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.E1combo24 ℓ τ
          - ((516096 : ℂ) - 442368 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                + Work.Asymptotics.Compact.cuspC ℓ)) * Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  have hdiv : Big 2 (fun τ : ℍ => (qF τ * E1combo24 ℓ τ - c1F ℓ τ * qF τ ^ 2) / qF τ) :=
    Big_div_q (big_qE ℓ)
  have h2 : Big 2 (fun τ : ℍ => E1combo24 ℓ τ - c1F ℓ τ * qF τ) := by
    refine hdiv.congr_on (fun τ _ => ?_)
    have hq := qF_ne_zero τ
    rw [div_eq_iff hq]
    ring
  obtain ⟨C, N, hC, hN, hb⟩ := h2
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have h := hb τ hτ
  simpa only [c1F, qF, LamF] using h

end

end Work.Asymptotics.KhatE1
