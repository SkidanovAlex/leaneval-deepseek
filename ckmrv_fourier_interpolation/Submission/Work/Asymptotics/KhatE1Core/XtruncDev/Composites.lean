import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.Defs
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.E10Tdev
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.WTdev
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.D2Tdev
import Submission.Work.Asymptotics.KhatE1Core.XtruncDev.dinvDeltaTdev
import Submission.Work.Asymptotics.KhatE1.Lfun_fifth_order
import Submission.Work.Asymptotics.zAtom_second_order_strip
import Submission.Work.Asymptotics.KhatE1Core.ZDevRefined
import Submission.Work.Asymptotics.KhatE1Core.KPlus24RemBound
import Submission.Work.Asymptotics.KhatE1Core.Sm1Split
import Submission.Work.Asymptotics.KhatE1Core.Sm2Split
import Submission.Work.Asymptotics.KhatE1Core.Sm3Split
import Submission.Work.Asymptotics.KhatE1Core.Sm45Split

namespace Work.Asymptotics.KhatE1Core.XtruncDev

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-- `BoundQ f n` implies `Bound2 f n 0`. -/
lemma Bound2.of_BoundQ {f : ℍ → ℍ → ℂ} {n : ℤ} (h : Work.Asymptotics.KhatE1Core.BoundQ f n) :
    Work.Asymptotics.KhatE1Core.Bound2 f n 0 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have := hb τ z t hF ht hz0 hz1 hzim
  simpa only [zpow_zero, mul_one, mul_assoc] using this

lemma B2_dLT5 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1Core.Bound2 (fun (_ : ℍ) (z : ℍ) => ℓ.L z - LT5 ℓ z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.KhatE1.Lfun_fifth_order
  refine Work.Asymptotics.KhatE1Core.Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0)
    hC le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz1' : (1 : ℝ) ≤ (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; have := hF.2; rw [hzim]; linarith
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) := by
    rw [Work.Asymptotics.Compact.cuspC]; exact Work.Asymptotics.CuspL_eq ℓ
  have hE2 : Work.Kernels.qParamFun z = (Ept z) ^ 2 :=
    Work.Asymptotics.K24F.qParamFun_eq_Ept_sq' z
  have hkey : ℓ.L z - LT5 ℓ z
      = Work.Kernels.LogLambda.Lfun (z : ℂ)
        - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
            - 8 * Ept z + 12 * (Ept z) ^ 2 - (32 / 3 : ℂ) * (Ept z) ^ 3
            + 6 * (Ept z) ^ 4 - (48 / 5 : ℂ) * (Ept z) ^ 5) := by
    rw [Work.Asymptotics.LogLambdaData_L_eq_Lfun ℓ z]
    simp only [LT5, LT, Tq, Te, Work.Asymptotics.Compact.Xc, hc, hE2]
    ring
  rw [hkey]
  have hE6 : ‖Complex.exp (Real.pi * Complex.I * (z : ℂ))‖ ^ 6
      = ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul]
    exact congrArg (fun x => x ^ 3) (norm_Ept_sq_eq_q z)
  have h := hb (z : ℂ) hz1'
  rw [hE6] at h
  have h' : ‖Work.Kernels.LogLambda.Lfun (z : ℂ)
      - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
          - 8 * Ept z + 12 * (Ept z) ^ 2 - (32 / 3 : ℂ) * (Ept z) ^ 3
          + 6 * (Ept z) ^ 4 - (48 / 5 : ℂ) * (Ept z) ^ 5)‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := h
  simpa using h'

/-! ## Helpers -/

lemma B2_of_le_qzK {f : ℍ → ℂ} {K : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ K) :
    Bound2 (fun (_ : ℍ) (z : ℍ) => f z) 0 (K : ℤ) := by
  refine Bound2.of_le_qz (K := K) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz1' : (1:ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa using h z hz1'

lemma B2_of_le_qzK3 {f : ℍ → ℂ} {K : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ K) :
    Bound2 (fun (_ : ℍ) (z : ℍ) => f z) 0 (K : ℤ) := by
  refine Bound2.of_le_qz (K := K) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz3 : (3:ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa using h z hz3

lemma B2_of_isSmH6 {f : ℍ → ℂ} (h : Work.Asymptotics.KhatE1.IsSmH 6 f) :
    Bound2 (fun (_ : ℍ) (z : ℍ) => f z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := h
  refine Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz1' : (1:ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h := hb z hz1'
  have hE6 : ‖Ept z‖ ^ 6 = ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [show (6:ℕ) = 2*3 by norm_num, pow_mul, norm_Ept_sq_eq_q]
  rw [hE6] at h
  simpa using h

/-! ## The `T`-atom deviations -/

lemma B2_dE4T : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E4Fun z - E4T z) 0 3 :=
  Bound2_dE4.congr (fun τ z => by simp only [dE4, E4T, Tq, E4Ref])

lemma B2_dE6T : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E6Fun z - E6T z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dE6_bound
  exact (B2_of_le_qzK hC (fun z hz => hb z hz)).congr
    (fun τ z => by simp only [dE6, E6T, Tq, E6Ref])

lemma B2_dE2ST : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E2S z - E2ST z) 0 3 :=
  Bound2_dE2S.congr (fun τ z => by
    simp only [dE2S, E2ST, Tq, E2SRef, Work.Asymptotics.K24F.S0, Work.Asymptotics.KhatE1.S0z])

lemma B2_dE14T : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E14Fun z - E14T z) 0 3 :=
  Bound2_dE14.congr (fun τ z => by simp only [dE14, E14T, Tq, E14Ref])

lemma B2_dI4T : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E4Fun z)⁻¹ ^ 3 - invE4cubeT z) 0 3 :=
  Bound2_dI4.congr (fun τ z => by simp only [dI4, invE4cubeT, Tq, I4Ref])

lemma B2_dE4cT : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E4Fun z ^ 3 - E4T z ^ 3) 0 3 :=
  Bound2_dE4c.congr (fun τ z => by simp only [dE4c, dE4, E4T, Tq, E4Ref]; ring)

lemma B2_dDeltaT : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.DeltaFun z - DeltaT z) 0 4 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.DeltaFun_fourth_order
  exact (B2_of_le_qzK hC (fun z hz => hb z hz)).congr
    (fun τ z => by simp only [DeltaT, Tq])

lemma B2_dinvE4T : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E4Fun z)⁻¹ - invE4T z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := InvE4SecondOrder
  exact (B2_of_le_qzK3 hC (fun z hz => hb z hz)).congr
    (fun τ z => by simp only [invE4T, Tq])

lemma B2_djzT : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.jInvariantFun z - jzT z) 0 2 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.jqParam_second_order
  refine B2_of_le_qzK hC (K := 2) (C := C) (fun z hz => ?_)
  have h1 := hb z hz
  have hqne : Work.Kernels.qParamFun z ≠ 0 := Work.Asymptotics.qParamFun_ne_zero' z
  have hqpos : (0:ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hsplit : Work.Kernels.jInvariantFun z - jzT z
      = (Work.Kernels.jInvariantFun z * Work.Kernels.qParamFun z - 1
          - 744 * Work.Kernels.qParamFun z
          - 196884 * (Work.Kernels.qParamFun z) ^ 2) * (Work.Kernels.qParamFun z)⁻¹ := by
    simp only [jzT, Tq]; field_simp; ring
  rw [hsplit, norm_mul, norm_inv]
  calc ‖Work.Kernels.jInvariantFun z * Work.Kernels.qParamFun z - 1
        - 744 * Work.Kernels.qParamFun z
        - 196884 * (Work.Kernels.qParamFun z) ^ 2‖ * (‖Work.Kernels.qParamFun z‖)⁻¹
      ≤ (C * ‖Work.Kernels.qParamFun z‖ ^ 3) * (‖Work.Kernels.qParamFun z‖)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hqpos.le)
    _ = C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
        rw [mul_assoc, show ‖Work.Kernels.qParamFun z‖ ^ 3
          = ‖Work.Kernels.qParamFun z‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ by ring,
          mul_assoc, mul_inv_cancel₀ (ne_of_gt hqpos), mul_one, mul_comm]

lemma B2_dDonly : Bound2 (fun (_ : ℍ) (z : ℍ) => Donly z - 324 * Work.Kernels.qParamFun z) 0 2 := by
  obtain ⟨C, hC, hb⟩ := Donly_leading
  exact (B2_of_le_qzK hC (fun z hz => hb z hz))

/-! ## The true `z`-atoms -/

lemma B2_E4Fun : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E4Fun z) 0 0 := by
  have h := B2_dE4T.add B2_E4T
  exact h.congr (fun τ z => by ring)

lemma B2_E6Fun : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E6Fun z) 0 0 := by
  have h := B2_dE6T.add B2_E6T
  exact h.congr (fun τ z => by ring)

lemma B2_E14Fun : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E14Fun z) 0 0 := by
  have h := B2_dE14T.add B2_E14T
  exact h.congr (fun τ z => by ring)

lemma B2_E2S : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E2S z) 0 0 := by
  have h := B2_dE2ST.add B2_E2ST
  exact h.congr (fun τ z => by ring)

lemma B2_invE4 : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E4Fun z)⁻¹) 0 0 := by
  have h := B2_dinvE4T.add B2_invE4T
  exact h.congr (fun τ z => by ring)

lemma B2_invE4cube : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.E4Fun z)⁻¹ ^ 3) 0 0 := by
  have h := B2_dI4T.add B2_I4T
  exact h.congr (fun τ z => by ring)

lemma B2_DeltaInv : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.DeltaFun z)⁻¹) 0 (-1) := by
  have h := (dinvDeltaTdev).add B2_invDeltaT
  exact h.congr (fun τ z => by ring)

lemma B2_E10Fun : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.E10Fun z) 0 0 := by
  have h := E10Tdev.add B2_E10T
  exact h.congr (fun τ z => by
    simp only [E10T, Tq, Work.Kernels.E10Fun]; ring)

lemma B2_U2V2 : Bound2 (fun (_ : ℍ) (z : ℍ) =>
    Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) 0 0 := by
  have h := (D2Tdev).add B2_D2T
  exact h.congr (fun τ z => by ring)

lemma B2_WFun : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.WFun z) 0 0 := by
  have h := (WTdev).add B2_WT
  exact h.congr (fun τ z => by ring)

lemma B2_jz : Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Kernels.jInvariantFun z) 0 (-1) := by
  have h := B2_djzT.add B2_jzT
  exact h.congr (fun τ z => by ring)

lemma B2_LT5 (ℓ : Work.Kernels.LogLambdaData) : Bound2 (fun (_ : ℍ) (z : ℍ) => LT5 ℓ z) 0 0 := by
  have h := (B2_LT ℓ).sub ((B2_Ept5).cmul (48/5))
  exact h.congr (fun τ z => by simp only [LT5])

lemma B2_L (ℓ : Work.Kernels.LogLambdaData) : Bound2 (fun (_ : ℍ) (z : ℍ) => ℓ.L z) 0 0 := by
  have h := (B2_dLT5 ℓ).add (B2_LT5 ℓ)
  exact h.congr (fun τ z => by rw [LT5]; ring)

/-! ## `τ`-side atoms -/

lemma B2_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.psi2 ℓ τ) 0 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.psi2 ℓ)

lemma B2_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.psi4 ℓ τ) 0 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.psi4 ℓ)

lemma B2_Deltatau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.DeltaFun τ) 0 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.mono (by norm_num : (0:ℤ) ≤ 1)
    (Work.Asymptotics.KhatE1Core.BoundQ.DeltaFun))

lemma B2_E4tau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E4Fun τ) 0 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.E4Fun)

lemma B2_E6tau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E6Fun τ) 0 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.E6Fun)

lemma B2_jtau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.jInvariantFun τ) (-1) 0 :=
  Bound2.of_BoundQ (Work.Asymptotics.KhatE1Core.BoundQ.jInvariantFun)

lemma B2_E8tau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E8Fun τ) 0 0 := by
  have h := B2_E4tau.mul B2_E4tau
  exact h.congr (fun τ z => by simp only [Work.Kernels.E8Fun]; ring)

lemma B2_E10tau : Bound2 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E10Fun τ) 0 0 := by
  have h := B2_E4tau.mul B2_E6tau
  exact h.congr (fun τ z => by simp only [Work.Kernels.E10Fun])



end

end Work.Asymptotics.KhatE1Core.XtruncDev
