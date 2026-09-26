import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1.KdevE2CoeffDefs
import Submission.Work.Asymptotics.KhatE1.B0Defs
import Submission.Work.Asymptotics.KhatE1.EptSmallDefs
import Submission.Work.Asymptotics.KhatE1.EptPsiExp
import Submission.Work.Asymptotics.KhatE1Core.psi_combo_first_order
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.KdevE2c2c1_bound

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-! ## A funnel-local `O((scale)^N ‖q‖^n)` calculus -/

/-- `IsBs f n` : `‖f τ‖ ≤ C (scale τ)^N ‖q(τ)‖^n` on the funnel. -/
def IsBs (f : UpperHalfPlane → ℂ) (n : ℕ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
    ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ n

lemma qnorm_le_one_of_funnel (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 :=
  Work.Asymptotics.norm_qParamFun_le_one τ (Work.Asymptotics.Funnel.im_one hτ)

lemma scale_rpow_nonneg_funnel (τ : UpperHalfPlane) (N : ℝ) :
    (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N

lemma IsBs.mono_of {f : UpperHalfPlane → ℂ} {m : ℕ} (h : IsBs f m) (n : ℕ) (hn : n ≤ m) :
    IsBs f n := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have hq : ‖Work.Kernels.qParamFun τ‖ ^ m ≤ ‖Work.Kernels.qParamFun τ‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) (qnorm_le_one_of_funnel τ hτ) hn
  exact le_trans (hb τ hτ)
    (mul_le_mul_of_nonneg_left hq (mul_nonneg hC.le (scale_rpow_nonneg_funnel τ N)))

lemma IsBs.add {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsBs f m) (hg : IsBs g n) :
    IsBs (fun τ => f τ + g τ) (min m n) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine ⟨C1 + C2 + 1, max N1 N2, by linarith, le_trans hN1 (le_max_left _ _), fun τ hτ => ?_⟩
  have hs : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hN1' : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
  have hN2' : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
  have hm1 : ‖Work.Kernels.qParamFun τ‖ ^ m
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) (qnorm_le_one_of_funnel τ hτ) (min_le_left _ _)
  have hn1 : ‖Work.Kernels.qParamFun τ‖ ^ n
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) (qnorm_le_one_of_funnel τ hτ) (min_le_right _ _)
  have hb1' : ‖f τ‖ ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2
      * ‖Work.Kernels.qParamFun τ‖ ^ min m n := by
    refine le_trans (hb1 τ hτ) ?_
    calc C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ m
        ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Kernels.qParamFun τ‖ ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1' hC1.le)
            (pow_nonneg (norm_nonneg _) m)
      _ ≤ C1 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
          mul_le_mul_of_nonneg_left hm1 (mul_nonneg hC1.le (scale_rpow_nonneg_funnel τ _))
  have hb2' : ‖g τ‖ ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2
      * ‖Work.Kernels.qParamFun τ‖ ^ min m n := by
    refine le_trans (hb2 τ hτ) ?_
    calc C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ ^ n
        ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Kernels.qParamFun τ‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2' hC2.le)
            (pow_nonneg (norm_nonneg _) n)
      _ ≤ C2 * (Work.Kernels.scale τ) ^ max N1 N2 * ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
          mul_le_mul_of_nonneg_left hn1 (mul_nonneg hC2.le (scale_rpow_nonneg_funnel τ _))
  have h0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ max N1 N2
      * ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    mul_nonneg (scale_rpow_nonneg_funnel τ _) (pow_nonneg (norm_nonneg _) _)
  calc ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ (C1 + C2) * (Work.Kernels.scale τ) ^ max N1 N2
          * ‖Work.Kernels.qParamFun τ‖ ^ min m n := by
        rw [add_mul, add_mul]
        exact add_le_add hb1' hb2'
    _ ≤ (C1 + C2 + 1) * (Work.Kernels.scale τ) ^ max N1 N2
          * ‖Work.Kernels.qParamFun τ‖ ^ min m n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
        exact mul_le_mul_of_nonneg_right (by linarith) (scale_rpow_nonneg_funnel τ _)

lemma IsBs.neg {f : UpperHalfPlane → ℂ} {n : ℕ} (hf : IsBs f n) :
    IsBs (fun τ => -f τ) n := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [norm_neg]; exact hb τ hτ⟩

lemma IsBs.congr {f g : UpperHalfPlane → ℂ} {n : ℕ} (h : IsBs f n)
    (hfg : ∀ τ, f τ = g τ) : IsBs g n := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [← hfg τ]; exact hb τ hτ⟩

lemma IsBs.sub {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsBs f m) (hg : IsBs g n) :
    IsBs (fun τ => f τ - g τ) (min m n) := by
  have h := IsBs.add hf (IsBs.neg hg)
  refine h.congr (fun τ => by simp [sub_eq_add_neg])

lemma IsBs.const_mul (c : ℂ) {f : UpperHalfPlane → ℂ} {n : ℕ} (hf : IsBs f n) :
    IsBs (fun τ => c * f τ) n := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨‖c‖ * C + 1, N, by nlinarith [norm_nonneg c, hC], hN, fun τ hτ => ?_⟩
  calc ‖c * f τ‖ = ‖c‖ * ‖f τ‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ n) :=
        mul_le_mul_of_nonneg_left (hb τ hτ) (norm_nonneg _)
    _ ≤ (‖c‖ * C + 1) * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ n := by
        have h0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ n :=
          mul_nonneg (scale_rpow_nonneg_funnel τ N) (pow_nonneg (norm_nonneg _) n)
        nlinarith [h0, norm_nonneg c]

lemma IsBs.const (c : ℂ) : IsBs (fun _ : UpperHalfPlane => c) 0 := by
  refine ⟨‖c‖ + 1, 0, by positivity, le_rfl, fun τ _ => ?_⟩
  have h0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (0:ℝ) := scale_rpow_nonneg_funnel τ 0
  rw [Real.rpow_zero, mul_one, pow_zero, mul_one]
  linarith [norm_nonneg c]

lemma IsBs.one : IsBs (fun _ : UpperHalfPlane => (1:ℂ)) 0 := by
  simpa using IsBs.const (1:ℂ)

lemma IsBs.mul {f g : UpperHalfPlane → ℂ} {m n : ℕ} (hf : IsBs f m) (hg : IsBs g n) :
    IsBs (fun τ => f τ * g τ) (m + n) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine ⟨C1 * C2, N1 + N2, by positivity, add_nonneg hN1 hN2, fun τ hτ => ?_⟩
  have h1 := hb1 τ hτ
  have h2 := hb2 τ hτ
  have hA : (0:ℝ) ≤ C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ m :=
    mul_nonneg (mul_nonneg hC1.le (scale_rpow_nonneg_funnel τ N1))
      (pow_nonneg (norm_nonneg _) m)
  rw [norm_mul]
  calc ‖f τ‖ * ‖g τ‖
      ≤ (C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ m)
        * (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ ^ n) :=
        mul_le_mul h1 h2 (norm_nonneg _) hA
    _ = C1 * C2 * (Work.Kernels.scale τ) ^ (N1 + N2)
          * ‖Work.Kernels.qParamFun τ‖ ^ (m + n) := by
        rw [Real.rpow_add (Work.Kernels.scale_pos τ), pow_add]
        ring

lemma IsBs.pow {f : UpperHalfPlane → ℂ} {m : ℕ} (hf : IsBs f m) (k : ℕ) :
    IsBs (fun τ => f τ ^ k) (m * k) := by
  induction k with
  | zero => simpa using IsBs.one
  | succ k ih =>
      have h := IsBs.mul hf ih
      have he : m + m * k = m * (k + 1) := by ring
      rw [he] at h
      exact h.congr (fun τ => by rw [pow_succ]; ring)

lemma IsBigOq.toIsBs {f : UpperHalfPlane → ℂ} {n : ℕ} (h : Work.Asymptotics.IsBigOq f n) :
    IsBs f n := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, 0, hC, le_rfl, fun τ hτ => by
    simpa using hb τ (Work.Asymptotics.Funnel.im_one hτ)⟩

lemma IsSmall.toIsBs {f : UpperHalfPlane → ℂ} {n : ℕ}
    (h : IsSmall f (2 * n)) : IsBs f n := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have h2 : ‖Work.Residues.Ept τ‖ ^ (2 * n) = ‖Work.Kernels.qParamFun τ‖ ^ n := by
    rw [pow_mul, ← Work.Asymptotics.KhatE1.norm_qParamFun_eq τ]
  rw [← h2]
  exact hb τ (Work.Asymptotics.Funnel.im_one hτ)


/-! ## The inputs on the funnel -/

/-- `Λ₀ = πiτ + cuspC`. -/
def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

def DU (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ

def DV (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ

def DD (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ

def A1 (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 3 - 1 - 216 * Work.Kernels.qParamFun τ

def A2 (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E4Fun τ ^ 4 - 1 - 960 * Work.Kernels.qParamFun τ

def A3 (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ - Work.Kernels.qParamFun τ

def A4 (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ

def B3 (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * Work.Kernels.qParamFun τ

def E14m (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.E14Fun τ - 1 + 24 * Work.Kernels.qParamFun τ

def Phi1 (τ : UpperHalfPlane) : ℂ := 2304 * E14m τ + 1152 * B3 τ - 746496 * DD τ

def Tf (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ - 6 * LamF ℓ τ
    + (192 * LamF ℓ τ - 72) * Work.Kernels.qParamFun τ

def Theta (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹ *
    (1152 * (Work.Kernels.psi2 ℓ τ - 2 * LamF ℓ τ) * (E14m τ - 24 * Work.Kernels.qParamFun τ)
      + 576 * (Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ) * (B3 τ + 720 * Work.Kernels.qParamFun τ)
      - 373248 * (Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ) * Work.Kernels.DeltaFun τ)

def RN (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  -(Complex.I * (τ : ℂ)) * A1 τ + 240 * (Complex.I * (τ : ℂ)) * A3 τ
    - (Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹) * A2 τ
    + (984 * Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹
        - 12 * (Real.pi : ℂ)⁻¹) * A4 τ

lemma isBs_qParam : IsBs Work.Kernels.qParamFun 1 :=
  IsBigOq.toIsBs Work.Asymptotics.qParamFun_isBigOq

lemma isBs_coe : IsBs (fun τ : UpperHalfPlane => (τ : ℂ)) 0 :=
  IsSmall.toIsBs (n := 0) (by simpa using isSmall_coe)

lemma isBs_Lam (ℓ : Work.Kernels.LogLambdaData) : IsBs (LamF ℓ) 0 := by
  have h : IsSmall (fun τ : UpperHalfPlane => (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      + Work.Asymptotics.Compact.cuspC ℓ) 0 := by simpa using isSmall_piItau ℓ
  exact (IsSmall.toIsBs (n := 0) h).congr (fun τ => rfl)

lemma isBs_E4 : IsBs Work.Kernels.E4Fun 0 := IsBigOq.toIsBs Work.Asymptotics.E4Fun_bdd
lemma isBs_E6 : IsBs Work.Kernels.E6Fun 0 := IsBigOq.toIsBs Work.Asymptotics.E6Fun_bdd
lemma isBs_Delta : IsBs Work.Kernels.DeltaFun 1 :=
  IsBigOq.toIsBs Work.Asymptotics.DeltaFun_isBigOq_one

lemma isBs_DU : IsBs DU 2 := IsBigOq.toIsBs Work.Asymptotics.E4Fun_isBigOq
lemma isBs_DV : IsBs DV 2 := IsBigOq.toIsBs Work.Asymptotics.E6Fun_isBigOq
lemma isBs_DD : IsBs DD 2 := IsBigOq.toIsBs Work.Asymptotics.DeltaFun_isBigOq

lemma isBs_E4sq : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 2) 0 :=
  (isBs_E4.pow 2).mono_of 0 (by decide)
lemma isBs_E4cu : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 3) 0 :=
  (isBs_E4.pow 3).mono_of 0 (by decide)
lemma isBs_E4qu : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 4) 0 :=
  (isBs_E4.pow 4).mono_of 0 (by decide)
lemma isBs_E14 : IsBs Work.Kernels.E14Fun 0 :=
  (isBs_E4sq.mul isBs_E6).mono_of 0 (by decide) |>.congr (fun τ => by
    simp only [Work.Kernels.E14Fun])

lemma isBs_one_plus_240 : IsBs (fun τ => (1 : ℂ) + 240 * Work.Kernels.qParamFun τ) 0 := by
  have h : IsBs (fun τ => (1 : ℂ) + 240 * Work.Kernels.qParamFun τ) (min 0 1) :=
    IsBs.add IsBs.one (isBs_qParam.const_mul 240)
  simpa using h

lemma isBs_one_plus_480 : IsBs (fun τ => (1 : ℂ) + 480 * Work.Kernels.qParamFun τ) 0 := by
  have h : IsBs (fun τ => (1 : ℂ) + 480 * Work.Kernels.qParamFun τ) (min 0 1) :=
    IsBs.add IsBs.one (isBs_qParam.const_mul 480)
  simpa using h

lemma isBs_E4sq_sub : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 2 - 1
    - 480 * Work.Kernels.qParamFun τ) 2 := by
  have h1 : IsBs (fun τ => (57600 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    (isBs_qParam.pow 2).const_mul (57600 : ℂ)
  have h2 : IsBs (fun τ => DU τ * (Work.Kernels.E4Fun τ + 1
      + 240 * Work.Kernels.qParamFun τ)) 2 := by
    have hb : IsBs (fun τ => Work.Kernels.E4Fun τ + 1
        + 240 * Work.Kernels.qParamFun τ) 0 := by
      have h : IsBs (fun τ => Work.Kernels.E4Fun τ + 1
          + 240 * Work.Kernels.qParamFun τ) (min (min 0 0) 1) := by
        refine IsBs.add (IsBs.add isBs_E4 IsBs.one) ?_
        simpa using (isBs_qParam.const_mul 240)
      simpa using h
    exact (isBs_DU.mul hb).mono_of 2 (by decide)
  refine (IsBs.add h1 h2).congr (fun τ => ?_)
  simp only [DU]; ring

lemma isBs_B3 : IsBs B3 2 := by
  have h1 : IsBs (fun τ => (172800 : ℂ) * Work.Kernels.qParamFun τ ^ 2
      + (13824000 : ℂ) * Work.Kernels.qParamFun τ ^ 3) 2 := by
    have ha : IsBs (fun τ => (172800 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
      (isBs_qParam.pow 2).const_mul (172800 : ℂ)
    have hb : IsBs (fun τ => (13824000 : ℂ) * Work.Kernels.qParamFun τ ^ 3) 3 :=
      (isBs_qParam.pow 3).const_mul (13824000 : ℂ)
    exact IsBs.add ha (hb.mono_of 2 (by decide))
  have h2 : IsBs (fun τ => DU τ * (Work.Kernels.E4Fun τ ^ 2 + Work.Kernels.E4Fun τ
      * (1 + 240 * Work.Kernels.qParamFun τ)
      + (1 + 240 * Work.Kernels.qParamFun τ) ^ 2)) 2 := by
    have hb : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 2 + Work.Kernels.E4Fun τ
        * (1 + 240 * Work.Kernels.qParamFun τ)
        + (1 + 240 * Work.Kernels.qParamFun τ) ^ 2) 0 := by
      have h : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 2 + Work.Kernels.E4Fun τ
          * (1 + 240 * Work.Kernels.qParamFun τ)
          + (1 + 240 * Work.Kernels.qParamFun τ) ^ 2) (min (min 0 0) 0) := by
        refine IsBs.add (IsBs.add isBs_E4sq ?_) ?_
        · simpa using (isBs_E4.mul isBs_one_plus_240).mono_of 0 (by decide)
        · simpa using ((isBs_one_plus_240.pow 2).mono_of 0 (by decide))
      simpa using h
    exact (isBs_DU.mul hb).mono_of 2 (by decide)
  refine (IsBs.add h1 h2).congr (fun τ => ?_)
  simp only [DU, B3]; ring

lemma isBs_A2 : IsBs A2 2 := by
  have h1 : IsBs (fun τ => (345600 : ℂ) * Work.Kernels.qParamFun τ ^ 2
      + (55296000 : ℂ) * Work.Kernels.qParamFun τ ^ 3
      + (3317760000 : ℂ) * Work.Kernels.qParamFun τ ^ 4) 2 := by
    have ha : IsBs (fun τ => (345600 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
      (isBs_qParam.pow 2).const_mul (345600 : ℂ)
    have hb : IsBs (fun τ => (55296000 : ℂ) * Work.Kernels.qParamFun τ ^ 3) 3 :=
      (isBs_qParam.pow 3).const_mul (55296000 : ℂ)
    have hc : IsBs (fun τ => (3317760000 : ℂ) * Work.Kernels.qParamFun τ ^ 4) 4 :=
      (isBs_qParam.pow 4).const_mul (3317760000 : ℂ)
    have h2 : IsBs (fun τ => (345600 : ℂ) * Work.Kernels.qParamFun τ ^ 2
        + (55296000 : ℂ) * Work.Kernels.qParamFun τ ^ 3) 2 :=
      IsBs.add ha (hb.mono_of 2 (by decide))
    exact IsBs.add h2 (hc.mono_of 2 (by decide))
  have h2 : IsBs (fun τ => DU τ * (Work.Kernels.E4Fun τ ^ 3
      + Work.Kernels.E4Fun τ ^ 2 * (1 + 240 * Work.Kernels.qParamFun τ)
      + Work.Kernels.E4Fun τ * (1 + 240 * Work.Kernels.qParamFun τ) ^ 2
      + (1 + 240 * Work.Kernels.qParamFun τ) ^ 3)) 2 := by
    have hb : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 3
        + Work.Kernels.E4Fun τ ^ 2 * (1 + 240 * Work.Kernels.qParamFun τ)
        + Work.Kernels.E4Fun τ * (1 + 240 * Work.Kernels.qParamFun τ) ^ 2
        + (1 + 240 * Work.Kernels.qParamFun τ) ^ 3) 0 := by
      have h : IsBs (fun τ => Work.Kernels.E4Fun τ ^ 3
          + Work.Kernels.E4Fun τ ^ 2 * (1 + 240 * Work.Kernels.qParamFun τ)
          + Work.Kernels.E4Fun τ * (1 + 240 * Work.Kernels.qParamFun τ) ^ 2
          + (1 + 240 * Work.Kernels.qParamFun τ) ^ 3) (min (min (min 0 0) 0) 0) := by
        refine IsBs.add (IsBs.add (IsBs.add isBs_E4cu ?_) ?_) ?_
        · simpa using (isBs_E4sq.mul isBs_one_plus_240).mono_of 0 (by decide)
        · simpa using (isBs_E4.mul ((isBs_one_plus_240.pow 2).mono_of 0 (by decide)))
        · simpa using ((isBs_one_plus_240.pow 3).mono_of 0 (by decide))
      simpa using h
    exact (isBs_DU.mul hb).mono_of 2 (by decide)
  refine (IsBs.add h1 h2).congr (fun τ => ?_)
  simp only [DU, A2]; ring

lemma isBs_E14m : IsBs E14m 2 := by
  have h1 : IsBs (fun τ => (Work.Kernels.E4Fun τ ^ 2 - 1
      - 480 * Work.Kernels.qParamFun τ) * Work.Kernels.E6Fun τ) 2 :=
    (isBs_E4sq_sub.mul isBs_E6).mono_of 2 (by decide)
  have h2 : IsBs (fun τ => - (241920 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    (isBs_qParam.pow 2).const_mul (-241920 : ℂ)
  have h3 : IsBs (fun τ => ((1 : ℂ) + 480 * Work.Kernels.qParamFun τ) * DV τ) 2 :=
    (isBs_one_plus_480.mul isBs_DV).mono_of 2 (by decide)
  refine (IsBs.add (IsBs.add h1 h2) h3).congr (fun τ => ?_)
  simp only [E14m, DV, Work.Kernels.E14Fun]; ring

lemma isBs_A1 : IsBs A1 2 := by
  have h1 : IsBs (fun τ => - (362880 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    (isBs_qParam.pow 2).const_mul (-362880 : ℂ)
  have h2 : IsBs (fun τ => (1 - 504 * Work.Kernels.qParamFun τ) * B3 τ) 2 := by
    have hb : IsBs (fun τ => (1 : ℂ) - 504 * Work.Kernels.qParamFun τ) 0 := by
      have h : IsBs (fun τ => (1 : ℂ) - 504 * Work.Kernels.qParamFun τ) (min 0 1) :=
        IsBs.sub IsBs.one (isBs_qParam.const_mul 504)
      simpa using h
    exact (hb.mul isBs_B3).mono_of 2 (by decide)
  have h3 : IsBs (fun τ => DV τ * Work.Kernels.E4Fun τ ^ 3) 2 :=
    (isBs_DV.mul isBs_E4cu).mono_of 2 (by decide)
  refine (IsBs.add (IsBs.add h1 h2) h3).congr (fun τ => ?_)
  simp only [A1, DV, B3]; ring

lemma isBs_A3 : IsBs A3 2 := by
  have h1 : IsBs (fun τ => - (504 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    (isBs_qParam.pow 2).const_mul (-504 : ℂ)
  have h2 : IsBs (fun τ => Work.Kernels.qParamFun τ * DV τ) 2 :=
    (isBs_qParam.mul isBs_DV).mono_of 2 (by decide)
  have h3 : IsBs (fun τ => DD τ * Work.Kernels.E6Fun τ) 2 :=
    (isBs_DD.mul isBs_E6).mono_of 2 (by decide)
  refine (IsBs.add (IsBs.add h1 h2) h3).congr (fun τ => ?_)
  simp only [A3, DV, DD]; ring

lemma isBs_A4 : IsBs A4 2 := by
  have h1 : IsBs (fun τ => (240 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    (isBs_qParam.pow 2).const_mul (240 : ℂ)
  have h2 : IsBs (fun τ => (1 + 240 * Work.Kernels.qParamFun τ) * DD τ) 2 :=
    (isBs_one_plus_240.mul isBs_DD).mono_of 2 (by decide)
  have h3 : IsBs (fun τ => DU τ * Work.Kernels.DeltaFun τ) 2 :=
    (isBs_DU.mul isBs_Delta).mono_of 2 (by decide)
  refine (IsBs.add (IsBs.add h1 h2) h3).congr (fun τ => ?_)
  simp only [A4, DU, DD]; ring

lemma isBs_Phi1 : IsBs Phi1 2 := by
  have h := IsBs.sub (IsBs.add (isBs_E14m.const_mul 2304) (isBs_B3.const_mul 1152))
    (isBs_DD.const_mul 746496)
  refine h.mono_of 2 (by decide) |>.congr (fun τ => ?_)
  simp only [Phi1]

lemma isBs_P2 (ℓ : Work.Kernels.LogLambdaData) :
    IsBs (fun τ => Work.Kernels.psi2 ℓ τ - 2 * LamF ℓ τ) 1 := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simpa [LamF] using (h τ hτ).1

lemma isBs_P4 (ℓ : Work.Kernels.LogLambdaData) :
    IsBs (fun τ => Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ) 1 := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simpa [LamF] using (h τ hτ).2

lemma isBs_Tf (ℓ : Work.Kernels.LogLambdaData) : IsBs (Tf ℓ) 2 := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_combo_first_order ℓ
  exact ⟨C, N, hC, hN, h⟩

lemma isBs_Theta (ℓ : Work.Kernels.LogLambdaData) : IsBs (Theta ℓ) 2 := by
  have h1 : IsBs (fun τ => 1152 * (Work.Kernels.psi2 ℓ τ - 2 * LamF ℓ τ)
      * (E14m τ - 24 * Work.Kernels.qParamFun τ)) 2 := by
    have hb : IsBs (fun τ => E14m τ - 24 * Work.Kernels.qParamFun τ) 1 :=
      (IsBs.sub isBs_E14m ((isBs_qParam.const_mul 24).mono_of 1 (by decide))).mono_of 1 (by decide)
    exact (((isBs_P2 ℓ).const_mul 1152).mul hb).mono_of 2 (by decide)
  have h2 : IsBs (fun τ => 576 * (Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ)
      * (B3 τ + 720 * Work.Kernels.qParamFun τ)) 2 := by
    have hb : IsBs (fun τ => B3 τ + 720 * Work.Kernels.qParamFun τ) 1 :=
      IsBs.add isBs_B3 (isBs_qParam.const_mul 720)
    exact (((isBs_P4 ℓ).const_mul 576).mul hb).mono_of 2 (by decide)
  have h3 : IsBs (fun τ => 373248 * (Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ)
      * Work.Kernels.DeltaFun τ) 2 :=
    (((isBs_P4 ℓ).const_mul 373248).mul isBs_Delta).mono_of 2 (by decide)
  have h := (IsBs.sub (IsBs.add h1 h2) h3).const_mul ((3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)
  refine h.mono_of 2 (by decide) |>.congr (fun τ => ?_)
  simp only [Theta]

lemma isBs_RN (ℓ : Work.Kernels.LogLambdaData) : IsBs (RN ℓ) 2 := by
  have hi : IsBs (fun τ : UpperHalfPlane => Complex.I * (τ : ℂ)) 0 :=
    isBs_coe.const_mul Complex.I
  have h1 : IsBs (fun τ => -(Complex.I * (τ : ℂ)) * A1 τ) 2 :=
    ((hi.neg.mul isBs_A1)).mono_of 2 (by decide) |>.congr (fun τ => by ring)
  have h2 : IsBs (fun τ => 240 * (Complex.I * (τ : ℂ)) * A3 τ) 2 :=
    ((hi.const_mul 240 |>.mul isBs_A3)).mono_of 2 (by decide) |>.congr (fun τ => by ring)
  have h3 : IsBs (fun τ => (Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹) * A2 τ) 2 :=
    (isBs_A2.const_mul (Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹)).mono_of 2
      (by decide)
  have h4 : IsBs (fun τ => (984 * Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹
      - 12 * (Real.pi : ℂ)⁻¹) * A4 τ) 2 :=
    (isBs_A4.const_mul (984 * Work.Asymptotics.Compact.cuspC ℓ * (Real.pi : ℂ)⁻¹
      - 12 * (Real.pi : ℂ)⁻¹)).mono_of 2 (by decide)
  refine (IsBs.add (IsBs.sub (IsBs.add h1 h2) h3) h4).mono_of 2 (by decide)
    |>.congr (fun τ => ?_)
  simp only [RN]

/-! ## The decomposition of `Δ·B0` -/

lemma Delta_mul_B0_decomp (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.KhatE1.B0 ℓ τ
      = (LamF ℓ τ * Phi1 τ * ((3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)
          + Tf ℓ τ * ((6 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹))
        + (Theta ℓ τ + RN ℓ τ) := by
  rw [Delta_mul_B0]
  rw [show (((3456 : ℂ) * (Real.pi : ℂ)))⁻¹
      = (3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹ from by rw [mul_inv]]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [LamF, Phi1, E14m, B3, DD, A1, A2, A3, A4, Theta, RN, Tf,
    Work.Kernels.E14Fun]
  field_simp
  ring

lemma isBs_Delta_mul_B0 (ℓ : Work.Kernels.LogLambdaData) :
    IsBs (fun τ => Work.Kernels.DeltaFun τ * Work.Asymptotics.KhatE1.B0 ℓ τ) 2 := by
  have h1 : IsBs (fun τ => LamF ℓ τ * Phi1 τ * ((3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)) 2 := by
    have hh : IsBs (fun τ => LamF ℓ τ * Phi1 τ) 2 :=
      ((isBs_Lam ℓ).mul isBs_Phi1).mono_of 2 (by decide)
    exact (hh.const_mul ((3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)).congr (fun τ => by ring)
  have h2 : IsBs (fun τ => Tf ℓ τ * ((6 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)) 2 :=
    ((isBs_Tf ℓ).const_mul ((6 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹)).congr (fun τ => by ring)
  have h3 : IsBs (fun τ => Theta ℓ τ) 2 := isBs_Theta ℓ
  have h4 : IsBs (fun τ => RN ℓ τ) 2 := isBs_RN ℓ
  refine (IsBs.add (IsBs.add h1 h2) (IsBs.add h3 h4)).congr (fun τ => ?_)
  exact (Delta_mul_B0_decomp ℓ τ).symm

/-! ## The bound on `B0` -/

lemma isBs_B0 (ℓ : Work.Kernels.LogLambdaData) : IsBs (Work.Asymptotics.KhatE1.B0 ℓ) 1 := by
  obtain ⟨C, N, hC, hN, h⟩ := isBs_Delta_mul_B0 ℓ
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  refine ⟨C / cd, N, by positivity, hN, fun τ hτ => ?_⟩
  have hDne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hDpos : (0:ℝ) < ‖Work.Kernels.DeltaFun τ‖ := norm_pos_iff.mpr hDne
  have hq : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Asymptotics.norm_qParamFun τ
  have hqpos : (0:ℝ) < ‖Work.Kernels.qParamFun τ‖ := by rw [hq]; exact Real.exp_pos _
  have hdτ : cd * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [hq]; exact hd τ hτ
  have hval : ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.KhatE1.B0 ℓ τ‖
      ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [← norm_mul]; exact h τ hτ
  have h1 : ‖Work.Asymptotics.KhatE1.B0 ℓ τ‖
      ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
        / ‖Work.Kernels.DeltaFun τ‖ := by
    rw [le_div_iff₀ hDpos, mul_comm]
    exact hval
  have hscale : (0:ℝ) ≤ (C / cd) * (Work.Kernels.scale τ) ^ N
      * ‖Work.Kernels.qParamFun τ‖ := by
    have h1' : (0:ℝ) < C / cd := div_pos hC hcd
    exact mul_nonneg (mul_nonneg h1'.le (scale_rpow_nonneg_funnel τ N)) hqpos.le
  have h2 : C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
        / ‖Work.Kernels.DeltaFun τ‖
      ≤ C / cd * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
    rw [div_le_iff₀ hDpos]
    calc C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
        = (C / cd) * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
            * (cd * ‖Work.Kernels.qParamFun τ‖) := by
          field_simp
      _ ≤ (C / cd) * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Kernels.DeltaFun τ‖ := mul_le_mul_of_nonneg_left hdτ hscale
  have hfin := le_trans h1 h2
  simpa using hfin


/-! ## `KdevE2c0` is `B0/2` -/

lemma KdevE2expr_eq_pi_Delta_B0 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    KdevE2expr ℓ τ = (Real.pi : ℂ) * (Work.Kernels.DeltaFun τ * B0 ℓ τ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Work.Asymptotics.KhatE1.Delta_mul_B0, Work.Asymptotics.KhatE1.KdevE2expr]
  rw [show (((3456 : ℂ) * (Real.pi : ℂ)))⁻¹
      = (3456 : ℂ)⁻¹ * (Real.pi : ℂ)⁻¹ from by rw [mul_inv]]
  field_simp
  ring

lemma KdevE2c0_eq_B0 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    KdevE2c0 ℓ τ = B0 ℓ τ / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hc : (Real.pi : ℂ) * Work.Kernels.DeltaFun τ ≠ 0 := mul_ne_zero hpi hD
  have h1 : 2 * (Real.pi : ℂ) * Work.Kernels.DeltaFun τ * KdevE2c0 ℓ τ = KdevE2expr ℓ τ :=
    Work.Asymptotics.KhatE1.KdevE2expr_eq ℓ τ
  rw [KdevE2expr_eq_pi_Delta_B0 ℓ τ] at h1
  have h2 : (2 : ℂ) * KdevE2c0 ℓ τ = B0 ℓ τ := by
    refine mul_left_cancel₀ hc ?_
    linear_combination (norm := ring) h1
  rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
  exact h2

lemma isBs_KdevE2c0 (ℓ : Work.Kernels.LogLambdaData) : IsBs (KdevE2c0 ℓ) 1 := by
  have h := (isBs_B0 ℓ).const_mul ((1/2 : ℂ))
  refine h.congr (fun τ => ?_)
  rw [KdevE2c0_eq_B0 ℓ τ]
  ring

/-! ## The assembly -/

private lemma assembly (ℓ : Work.Kernels.LogLambdaData) (hb2 : IsBs KdevE2c2 1)
    (hb1 : IsBs (KdevE2c1 ℓ) 1) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖KdevE2 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C2, N2, hC2, hN2, hf2⟩ := hb2
  obtain ⟨C1, N1, hC1, hN1, hf1⟩ := hb1
  obtain ⟨C0, N0, hC0, hN0, hf0⟩ := isBs_KdevE2c0 ℓ
  set N : ℝ := max (max N2 N1) N0 with hN
  refine ⟨9 * C2 + 3 * C1 + C0 + 1, N, 2, by positivity, ?_, by norm_num, ?_⟩
  · rw [hN]; exact le_trans hN2 (le_trans (le_max_left _ _) (le_max_left _ _))
  intro τ z t hτ ht hz1 hz2 hzim
  rw [Real.rpow_two]
  rw [show (9 * C2 + 3 * C1 + C0 + 1) * ‖Work.Kernels.qParamFun τ‖
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2
      = (9 * C2 + 3 * C1 + C0 + 1)
        * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2)
      from by ring]
  have htn : (0:ℝ) ≤ t := by have := hτ.2; linarith
  have h1t1 : (1:ℝ) ≤ 1 + t := by linarith
  have h1t0 : (0:ℝ) ≤ 1 + t := by linarith
  have hscale1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hS0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N := scale_rpow_nonneg_funnel τ N
  have hN2' : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ N := by
    refine Real.rpow_le_rpow_of_exponent_le hscale1 ?_
    rw [hN]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hN1' : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ N := by
    refine Real.rpow_le_rpow_of_exponent_le hscale1 ?_
    rw [hN]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hN0' : (Work.Kernels.scale τ) ^ N0 ≤ (Work.Kernels.scale τ) ^ N := by
    refine Real.rpow_le_rpow_of_exponent_le hscale1 ?_
    rw [hN]; exact le_max_right _ _
  have hzn : ‖(z : ℂ)‖ ≤ 3 * (1 + t) := by
    have hre : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith, hz2⟩
    have him' : |z.im| = t := by rw [hzim]; exact abs_of_nonneg htn
    calc ‖(z : ℂ)‖ ≤ |(z : ℂ).re| + |(z : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re| + |z.im| := by rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      _ ≤ 2 + t := by rw [him']; linarith
      _ ≤ 3 * (1 + t) := by linarith
  have hR0 : (0:ℝ) ≤ (1 + t) ^ 2 := pow_nonneg h1t0 2
  have hUR : (1 + t) ≤ (1 + t) ^ 2 := by nlinarith
  have h1R : (1:ℝ) ≤ (1 + t) ^ 2 := by nlinarith
  have h2le := hf2 τ hτ
  have h1le := hf1 τ hτ
  have h0le := hf0 τ hτ
  simp only [pow_one] at h2le h1le h0le
  have htri : ‖KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ) + KdevE2c0 ℓ τ‖
      ≤ ‖KdevE2c2 τ * (z : ℂ) ^ 2‖ + ‖KdevE2c1 ℓ τ * (z : ℂ)‖ + ‖KdevE2c0 ℓ τ‖ := by
    have h₂ := norm_add_le (KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ)) (KdevE2c0 ℓ τ)
    have h₁ := norm_add_le (KdevE2c2 τ * (z : ℂ) ^ 2) (KdevE2c1 ℓ τ * (z : ℂ))
    linarith
  have hA : ‖KdevE2c2 τ‖ * ‖(z : ℂ)‖ ^ 2
      ≤ 9 * (C2 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ 2)) := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) hzn 2
    have h1 : ‖KdevE2c2 τ‖ * ‖(z : ℂ)‖ ^ 2
        ≤ (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖)
            * (3 * (1 + t)) ^ 2 :=
      mul_le_mul h2le hp (pow_nonneg (norm_nonneg _) 2)
        (mul_nonneg (mul_nonneg hC2.le (scale_rpow_nonneg_funnel τ N2)) hq0)
    refine le_trans h1 ?_
    rw [show (3 * (1 + t)) ^ 2 = 9 * (1 + t) ^ 2 by ring]
    have hm : (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ 2
        ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2 :=
      mul_le_mul_of_nonneg_right hN2' hR0
    have h2 : (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖)
          * (9 * (1 + t) ^ 2)
        = 9 * C2 * ‖Work.Kernels.qParamFun τ‖
            * ((Work.Kernels.scale τ) ^ N2 * (1 + t) ^ 2) := by ring
    have h3 : 9 * (C2 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ 2))
        = 9 * C2 * ‖Work.Kernels.qParamFun τ‖
            * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left hm
      (mul_nonneg (mul_nonneg (by norm_num) hC2.le) hq0)
  have hB : ‖KdevE2c1 ℓ τ‖ * ‖(z : ℂ)‖
      ≤ 3 * (C1 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ 2)) := by
    have h1 : ‖KdevE2c1 ℓ τ‖ * ‖(z : ℂ)‖
        ≤ (C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖) * (3 * (1 + t)) :=
      mul_le_mul h1le hzn (norm_nonneg _)
        (mul_nonneg (mul_nonneg hC1.le (scale_rpow_nonneg_funnel τ N1)) hq0)
    refine le_trans h1 ?_
    have hm : (Work.Kernels.scale τ) ^ N1 * (1 + t)
        ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2 := by
      have h2 : (Work.Kernels.scale τ) ^ N1 * (1 + t) ≤ (Work.Kernels.scale τ) ^ N * (1 + t) :=
        mul_le_mul_of_nonneg_right hN1' h1t0
      have h3 : (Work.Kernels.scale τ) ^ N * (1 + t)
          ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2 := mul_le_mul_of_nonneg_left hUR hS0
      linarith
    have h2 : (C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖)
          * (3 * (1 + t))
        = 3 * C1 * ‖Work.Kernels.qParamFun τ‖
            * ((Work.Kernels.scale τ) ^ N1 * (1 + t)) := by ring
    have h3 : 3 * (C1 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ 2))
        = 3 * C1 * ‖Work.Kernels.qParamFun τ‖
            * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left hm
      (mul_nonneg (mul_nonneg (by norm_num) hC1.le) hq0)
  have hC : ‖KdevE2c0 ℓ τ‖
      ≤ C0 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by
    refine le_trans h0le ?_
    have hm : (Work.Kernels.scale τ) ^ N0 ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2 := by
      have h3 : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h1R hS0
        simpa using this
      linarith
    calc C0 * (Work.Kernels.scale τ) ^ N0 * ‖Work.Kernels.qParamFun τ‖
        = C0 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N0 := by ring
      _ ≤ C0 * ‖Work.Kernels.qParamFun τ‖ * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) :=
          mul_le_mul_of_nonneg_left hm (mul_nonneg hC0.le hq0)
      _ = C0 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by
          ring
  rw [KdevE2_eq_poly ℓ τ z]
  calc ‖KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ) + KdevE2c0 ℓ τ‖
      ≤ ‖KdevE2c2 τ * (z : ℂ) ^ 2‖ + ‖KdevE2c1 ℓ τ * (z : ℂ)‖ + ‖KdevE2c0 ℓ τ‖ := htri
    _ = ‖KdevE2c2 τ‖ * ‖(z : ℂ)‖ ^ 2 + ‖KdevE2c1 ℓ τ‖ * ‖(z : ℂ)‖ + ‖KdevE2c0 ℓ τ‖ := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ 9 * (C2 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2))
          + 3 * (C1 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2))
          + C0 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) :=
        add_le_add (add_le_add hA hB) hC
    _ = (9 * C2 + 3 * C1 + C0)
          * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by ring
    _ ≤ (9 * C2 + 3 * C1 + C0 + 1)
          * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ 2) := by
        have hfac : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ 2 := mul_nonneg (mul_nonneg hq0 hS0) hR0
        exact mul_le_mul_of_nonneg_right
          (by linarith : (9 * C2 + 3 * C1 + C0) ≤ 9 * C2 + 3 * C1 + C0 + 1) hfac


/-! ## The target -/

theorem KdevE2fun_funnel (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, hC, hN, hin, hkn⟩ := Work.Asymptotics.KhatE1.KdevE2c2c1_bound ℓ
  have h2 : IsBs KdevE2c2 1 :=
    ⟨C, N, hC, hN, fun τ hτ => by simpa using hin τ hτ⟩
  have h1 : IsBs (KdevE2c1 ℓ) 1 :=
    ⟨C, N, hC, hN, fun τ hτ => by simpa using hkn τ hτ⟩
  exact assembly ℓ h2 h1

end

end Work.Asymptotics.KhatE1