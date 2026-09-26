import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KPlus8TileTail
import Submission.Work.Asymptotics.Tile.tileDivisorSharp

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics
open Work.Asymptotics.EtailE

noncomputable section

def TBS (a b : ℝ) (F : ℍ → ℤ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
        ‖F w n z‖ ≤ C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)

namespace TBS

variable {a a₁ a₂ b b₁ b₂ : ℝ} {F G : ℍ → ℤ → ℍ → ℂ}

lemma mono (h : TBS a b F) (ha : a ≤ a₁) (hb : b₁ ≤ b) : TBS a₁ b₁ F := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  refine le_trans (hbnd w n z t hn hw hz ht) ?_
  have hH : 0 ≤ (ModularGroup.S • w).im := by have := hw.2; linarith
  have ht0 : 0 ≤ t := by have := hw.2; linarith
  have hexp : Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      ≤ Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have h1 : a * (ModularGroup.S • w).im ≤ a₁ * (ModularGroup.S • w).im :=
      mul_le_mul_of_nonneg_right ha hH
    have h2 : b₁ * Real.pi * t ≤ b * Real.pi * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (le_of_lt Real.pi_pos)) ht0
    linarith
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _))

lemma add (hF : TBS a b F) (hG : TBS a b G) : TBS a b (fun w n z => F w n z + G w n z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun w n z t hn hw hz ht => ?_⟩
  have hH : 0 ≤ (ModularGroup.S • w).im := by have := hw.2; linarith
  have ht0 : 0 ≤ t := by have := hw.2; linarith
  have hH1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have ht1 : (1:ℝ) ≤ 1 + t := by linarith
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hH1 (le_max_right _ _)
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  set E : ℝ := Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have s1 : ‖F w n z‖ ≤ C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by
    refine le_trans (hb1 w n z t hn hw hz ht) ?_
    have h2 : (scale w) ^ N1 * (1 + t) ^ M1
        ≤ (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN1' hM1' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C1 * (scale w) ^ N1 * (1 + t) ^ M1 * E
        = C1 * ((scale w) ^ N1 * (1 + t) ^ M1 * E) := by ring
      _ ≤ C1 * ((scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hE0.le) hC1.le
      _ = C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by ring
  have s2 : ‖G w n z‖ ≤ C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by
    refine le_trans (hb2 w n z t hn hw hz ht) ?_
    have h2 : (scale w) ^ N2 * (1 + t) ^ M2
        ≤ (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN2' hM2' (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    calc C2 * (scale w) ^ N2 * (1 + t) ^ M2 * E
        = C2 * ((scale w) ^ N2 * (1 + t) ^ M2 * E) := by ring
      _ ≤ C2 * ((scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hE0.le) hC2.le
      _ = C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E := by ring
  refine le_trans (norm_add_le _ _) ?_
  rw [show (C1 + C2) * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E
      = C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E
        + C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * E from by ring]
  exact add_le_add s1 s2

lemma neg (hF : TBS a b F) : TBS a b (fun w n z => -F w n z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [norm_neg]; exact hb w n z t hn hw hz ht⟩

lemma sub (hF : TBS a b F) (hG : TBS a b G) : TBS a b (fun w n z => F w n z - G w n z) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma const_mul (c : ℂ) (hF : TBS a b F) : TBS a b (fun w n z => c * F w n z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  refine ⟨(‖c‖ + 1) * C, N, M, by positivity, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (hb w n z t hn hw hz ht) (norm_nonneg c)) ?_
  have htw : (0:ℝ) ≤ 1 + t := by have := hw.2; linarith
  have hbase : (0:ℝ) ≤ (scale w) ^ N * (1 + t) ^ M
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
      (Real.rpow_nonneg htw _)) (Real.exp_pos _).le
  calc ‖c‖ * (C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = (‖c‖ * C) * ((scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) := by ring
    _ ≤ ((‖c‖ + 1) * C) * ((scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) := by
        refine mul_le_mul_of_nonneg_right ?_ hbase
        nlinarith [hC.le, norm_nonneg c]
    _ = (‖c‖ + 1) * C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) := by ring

lemma congr {F G : ℍ → ℤ → ℍ → ℂ} (hFG : ∀ w n z, F w n z = G w n z) (hF : TBS a b F) :
    TBS a b G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [← hFG]
    exact hb w n z t hn hw hz ht⟩

lemma const (c : ℂ) : TBS 0 0 (fun _ _ _ => c) := by
  refine ⟨‖c‖ + 1, 0, 0, by positivity, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero, Real.rpow_zero]
  simp only [mul_one]
  linarith [norm_nonneg c]

lemma one : TBS 0 0 (fun _ _ _ => (1 : ℂ)) := by
  simpa using const (1 : ℂ)

lemma mul (hF : TBS a₁ b₁ F) (hG : TBS a₂ b₂ G) :
    TBS (a₁ + a₂) (b₁ + b₂) (fun w n z => F w n z * G w n z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by positivity, by positivity,
    fun w n z t hn hw hz ht => ?_⟩
  have ht0 : 0 ≤ t := by have := hw.2; linarith
  have hs0 : (0:ℝ) < scale w := Work.Kernels.scale_pos w
  have ht1 : (0:ℝ) < 1 + t := by linarith
  rw [norm_mul]
  have hr1 : (scale w) ^ N1 * (scale w) ^ N2 = (scale w) ^ (N1 + N2) :=
    (Real.rpow_add hs0 N1 N2).symm
  have hr2 : (1 + t) ^ M1 * (1 + t) ^ M2 = (1 + t) ^ (M1 + M2) :=
    (Real.rpow_add ht1 M1 M2).symm
  have hr3 : Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t)
      * Real.exp (a₂ * (ModularGroup.S • w).im - b₂ * Real.pi * t)
      = Real.exp ((a₁ + a₂) * (ModularGroup.S • w).im - (b₁ + b₂) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsplit : (C1 * (scale w) ^ N1 * (1 + t) ^ M1
        * Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t))
      * (C2 * (scale w) ^ N2 * (1 + t) ^ M2
        * Real.exp (a₂ * (ModularGroup.S • w).im - b₂ * Real.pi * t))
      = C1 * C2 * (scale w) ^ (N1 + N2) * (1 + t) ^ (M1 + M2)
        * Real.exp ((a₁ + a₂) * (ModularGroup.S • w).im - (b₁ + b₂) * Real.pi * t) := by
    rw [← hr1, ← hr2, ← hr3]
    ring
  have htw : (0:ℝ) ≤ 1 + t := by linarith
  have hF0 : (0:ℝ) ≤ C1 * (scale w) ^ N1 * (1 + t) ^ M1
      * Real.exp (a₁ * (ModularGroup.S • w).im - b₁ * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1.le
      (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)) (Real.rpow_nonneg htw _))
      (Real.exp_pos _).le
  have hprod := mul_le_mul (hb1 w n z t hn hw hz ht) (hb2 w n z t hn hw hz ht) (norm_nonneg _) hF0
  rw [hsplit] at hprod
  exact hprod

end TBS

/-- Transport of a `T`-periodic `Bdd c` bound to the tiles: `F (n+w) = F w` for `n = ±1`. -/
lemma TBS.of_bdd {c : ℝ} {F : ℍ → ℂ} (h : Bdd c F)
    (hper : ∀ τ : ℍ, F ((1:ℝ)+ᵥτ) = F τ) : TBS c 0 (fun w n _ => F ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have hvn : F ((n:ℝ)+ᵥw) = F w := by
    rcases hn with h | h
    · rw [h, Int.cast_one]; exact hper w
    · rw [h, Int.cast_neg, Int.cast_one]
      have h3 : (1:ℝ) +ᵥ ((-1:ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
      have h4 := hper ((-1:ℝ) +ᵥ w)
      rw [h3] at h4
      exact h4.symm
  change ‖F ((n:ℝ)+ᵥw)‖ ≤ C * (scale w) ^ N * (1 + t) ^ (0:ℝ)
      * Real.exp (c * (ModularGroup.S • w).im - 0 * Real.pi * t)
  rw [hvn]
  refine le_trans (hb w hw) ?_
  rw [show c * (ModularGroup.S • w).im - 0 * Real.pi * t = c * (ModularGroup.S • w).im from by ring,
    Real.rpow_zero, mul_one]

/-- Transport of a `Bdd` bound with a `T`-cocycle `F(τ+1) = F τ + G τ` to the tiles. -/
lemma TBS.of_bdd_cocycle {c c' : ℝ} {F G : ℍ → ℂ} (hF : Bdd c F) (hG : Bdd c' G)
    (hcoc : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → F ((n:ℝ)+ᵥw) = F w + (n:ℂ) * G w) :
    TBS (max c c') 0 (fun w n _ => F ((n:ℝ)+ᵥw)) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, 0, by positivity, le_max_of_le_left hN1, le_refl 0,
    fun w n z t hn hw hz ht => ?_⟩
  rw [Real.rpow_zero, mul_one]
  have hH0 : 0 ≤ (ModularGroup.S • w).im := by linarith [hw.2]
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hmn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have h1 := hb1 w hw
  have h2 := hb2 w hw
  have hc1 : Real.exp (c * (ModularGroup.S • w).im)
      ≤ Real.exp (max c c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hH0)
  have hc2 : Real.exp (c' * (ModularGroup.S • w).im)
      ≤ Real.exp (max c c' * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hH0)
  have hb1' : ‖F w‖ ≤ C1 * (scale w) ^ (max N1 N2)
      * Real.exp (max c c' * (ModularGroup.S • w).im) := by
    refine le_trans h1 ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN1' hC1.le) hc1 (Real.exp_pos _).le
      (mul_nonneg hC1.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hb2' : ‖G w‖ ≤ C2 * (scale w) ^ (max N1 N2)
      * Real.exp (max c c' * (ModularGroup.S • w).im) := by
    refine le_trans h2 ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN2' hC2.le) hc2 (Real.exp_pos _).le
      (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  calc ‖F ((n:ℝ)+ᵥw)‖ = ‖F w + (n:ℂ) * G w‖ := by rw [hcoc w n hn]
    _ ≤ ‖F w‖ + ‖G w‖ := by
        refine le_trans (norm_add_le _ _) (le_of_eq ?_)
        rw [norm_mul, hmn, one_mul]
    _ ≤ C1 * (scale w) ^ (max N1 N2) * Real.exp (max c c' * (ModularGroup.S • w).im)
        + C2 * (scale w) ^ (max N1 N2) * Real.exp (max c c' * (ModularGroup.S • w).im) :=
        add_le_add hb1' hb2'
    _ = (C1 + C2) * (scale w) ^ (max N1 N2)
        * Real.exp (max c c' * (ModularGroup.S • w).im - 0 * Real.pi * t) := by
        ring

/-! ## The `τ`-atoms on the tiles -/

lemma TBS.E4 : TBS 0 0 (fun w n _ => Work.Kernels.E4Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E4 (fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ)

lemma TBS.E6 : TBS 0 0 (fun w n _ => Work.Kernels.E6Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E6 (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ)

lemma TBS.E8 : TBS 0 0 (fun w n _ => Work.Kernels.E8Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E8 (fun τ => Work.Kernels.KernelFacts.E8Fun_vadd_one τ)

lemma TBS.E10 : TBS 0 0 (fun w n _ => Work.Kernels.E10Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E10 (fun τ => Work.Kernels.KernelFacts.E10Fun_vadd_one τ)

lemma TBS.E14 : TBS 0 0 (fun w n _ => Work.Kernels.E14Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E14 (fun τ => Work.Kernels.KernelFacts.E14Fun_vadd_one τ)

lemma TBS.Delta : TBS (-(2*Real.pi)) 0 (fun w n _ => Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_Delta (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ)

lemma TBS.invDelta : TBS (2*Real.pi) 0 (fun w n _ => (Work.Kernels.DeltaFun ((n:ℝ)+ᵥw))⁻¹) :=
  TBS.of_bdd EtailE.E_bdd_invDelta (fun τ => by rw [Work.Kernels.KernelFacts.DeltaFun_vadd_one])

lemma TBS.j : TBS (2*Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_j (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ)

lemma TBS.E14_div_Delta (ℓ : Work.Kernels.LogLambdaData) :
    TBS (2*Real.pi) 0
      (fun w n _ => Work.Kernels.E14Fun ((n:ℝ)+ᵥw) / Work.Kernels.DeltaFun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd (EtailE.E_bdd_E14_div_Delta ℓ)
    (fun τ => by
      rw [Work.Kernels.KernelFacts.E14Fun_vadd_one, Work.Kernels.KernelFacts.DeltaFun_vadd_one])

lemma TBS.E2 : TBS 0 0 (fun w n _ => Work.Kernels.E2Fun ((n:ℝ)+ᵥw)) :=
  TBS.of_bdd EtailE.E_bdd_E2 (fun τ => Work.Kernels.E2Fun_vadd_one τ)

/-! ### The `φ`-atoms -/

private lemma phiNeg2_vadd_one (τ : ℍ) :
    Work.Kernels.phiVec ((1:ℝ)+ᵥτ) 0 = Work.Kernels.phiVec τ 0 + (1:ℝ) := by
  simp only [Work.Kernels.phiVec, Work.Kernels.phiNeg2, Matrix.cons_val_zero]
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

private lemma phi0_vadd_one (τ : ℍ) :
    Work.Kernels.phi0 ((1:ℝ)+ᵥτ) = Work.Kernels.phi0 τ + Work.Kernels.E2Fun τ := by
  simp only [Work.Kernels.phi0, UpperHalfPlane.coe_vadd, Work.Kernels.E2Fun_vadd_one]
  push_cast
  ring

private lemma phi2_vadd_one (τ : ℍ) :
    Work.Kernels.phi2 ((1:ℝ)+ᵥτ) = Work.Kernels.phi2 τ + Work.Kernels.E2Fun τ ^ 2 := by
  simp only [Work.Kernels.phi2, UpperHalfPlane.coe_vadd, Work.Kernels.E2Fun_vadd_one]
  push_cast
  ring

private lemma phiNeg2_vadd_neg_one (τ : ℍ) :
    Work.Kernels.phiVec ((-1:ℝ)+ᵥτ) 0 = Work.Kernels.phiVec τ 0 - 1 := by
  simp only [Work.Kernels.phiVec, Work.Kernels.phiNeg2, Matrix.cons_val_zero]
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

private lemma E2_vadd_neg_one (τ : ℍ) : Work.Kernels.E2Fun ((-1:ℝ)+ᵥτ) = Work.Kernels.E2Fun τ := by
  have h := Work.Kernels.E2Fun_vadd_one ((-1:ℝ)+ᵥτ)
  rw [show (1:ℝ) +ᵥ ((-1:ℝ)+ᵥτ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

private lemma phi0_vadd_neg_one (τ : ℍ) :
    Work.Kernels.phi0 ((-1:ℝ)+ᵥτ) = Work.Kernels.phi0 τ - Work.Kernels.E2Fun τ := by
  have h := phi0_vadd_one ((-1:ℝ)+ᵥτ)
  rw [show (1:ℝ) +ᵥ ((-1:ℝ)+ᵥτ) = τ from by rw [← add_vadd]; norm_num, E2_vadd_neg_one] at h
  linear_combination -h

private lemma phi2_vadd_neg_one (τ : ℍ) :
    Work.Kernels.phi2 ((-1:ℝ)+ᵥτ) = Work.Kernels.phi2 τ - Work.Kernels.E2Fun τ ^ 2 := by
  have h := phi2_vadd_one ((-1:ℝ)+ᵥτ)
  rw [show (1:ℝ) +ᵥ ((-1:ℝ)+ᵥτ) = τ from by rw [← add_vadd]; norm_num, E2_vadd_neg_one] at h
  linear_combination -h

/-- `(w:ℂ) + n` on the tiles. -/
lemma TBS.phiNeg2 : TBS 0 0 (fun w n _ => (w : ℂ) + (n : ℂ)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := EtailE.E_bdd_phi0
  refine ⟨C + 1, N, 0, by positivity, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero]
  simp only [mul_one]
  have h1 : ‖(w : ℂ)‖ ≤ C * (scale w) ^ N := by
    have h := hb w hw
    simpa only [Work.Kernels.phiVec, Work.Kernels.phiNeg2, Matrix.cons_val_zero,
      EtailE.exp_zero_im, mul_one] using h
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hN1 : (1:ℝ) ≤ (scale w) ^ N := Real.one_le_rpow hs1 hN
  have hmn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have h2 : ‖(w : ℂ) + (n : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
    have h := norm_add_le (w : ℂ) (n : ℂ)
    rwa [hmn] at h
  have h3 : (0:ℝ) ≤ (scale w) ^ N := Real.rpow_nonneg (Work.Kernels.scale_pos w).le N
  nlinarith [h1, hN1, hC.le, h2, h3]

/-- `φ₀` on the tiles. -/
lemma TBS.phi0 : TBS 0 0 (fun w n _ => Work.Kernels.phi0 ((n:ℝ)+ᵥw)) := by
  have h := TBS.of_bdd_cocycle (c := 0) (c' := 0)
    (F := fun w => Work.Kernels.phiVec w 1) (G := fun w => Work.Kernels.E2Fun w)
    EtailE.E_bdd_phi1 EtailE.E_bdd_E2 ?_
  · have h1 : TBS 0 0 (fun w n _ => Work.Kernels.phiVec ((n:ℝ)+ᵥw) 1) := by
      simpa using h
    exact h1.congr (fun w n z => by simp [Work.Kernels.phiVec])
  · intro w n hn
    rcases hn with hh | hh
    · rw [hh, Int.cast_one]; push_cast; rw [one_mul]
      exact phi0_vadd_one w
    · rw [hh, Int.cast_neg, Int.cast_one]; push_cast; rw [neg_one_mul]
      exact phi0_vadd_neg_one w

/-- `φ₂` on the tiles. -/
lemma TBS.phi2 : TBS 0 0 (fun w n _ => Work.Kernels.phi2 ((n:ℝ)+ᵥw)) := by
  have hsq : Bdd 0 (fun w => Work.Kernels.E2Fun w ^ 2) := by
    have h2 := EtailE.E_bdd_E2.mul EtailE.E_bdd_E2
    simpa [pow_two] using h2
  have h := TBS.of_bdd_cocycle (c := 0) (c' := 0)
    (F := fun w => Work.Kernels.phiVec w 2) (G := fun w => Work.Kernels.E2Fun w ^ 2)
    EtailE.E_bdd_phi2 hsq ?_
  · have h1 : TBS 0 0 (fun w n _ => Work.Kernels.phiVec ((n:ℝ)+ᵥw) 2) := by
      simpa using h
    exact h1.congr (fun w n z => by simp [Work.Kernels.phiVec])
  · intro w n hn
    rcases hn with hh | hh
    · rw [hh, Int.cast_one]; push_cast; rw [one_mul]
      exact phi2_vadd_one w
    · rw [hh, Int.cast_neg, Int.cast_one]; push_cast; rw [neg_one_mul]
      exact phi2_vadd_neg_one w

/-! ### The `ψ`-atoms and `Λ` -/

lemma TBS.psi2 (ℓ : Work.Kernels.LogLambdaData) :
    TBS 0 0 (fun w n _ => Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := tile_tau_atoms ℓ
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  obtain ⟨_, _, _, _, _, hpsi2, _, _, _⟩ := hbd w n hn hw
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero]
  simp only [mul_one]
  exact hpsi2

lemma TBS.psi4 (ℓ : Work.Kernels.LogLambdaData) :
    TBS 0 0 (fun w n _ => Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hbd⟩ := tile_tau_atoms ℓ
  refine ⟨C, N, 0, hC, hN, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  obtain ⟨_, _, _, _, _, _, hpsi4, _, _⟩ := hbd w n hn hw
  rw [show (0:ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring, Real.exp_zero,
    Real.rpow_zero]
  simp only [mul_one]
  exact hpsi4

/-- `ψ₄E₈ - ψ₂E₁₀` on the tiles, by the `T`-cocycle: it is `O(e^{-π Im(Sw)})`. -/
lemma TBS.psi_combo (ℓ : Work.Kernels.LogLambdaData) :
    TBS (-(Real.pi)) 0 (fun w n _ => psiCombo ℓ ((n:ℝ)+ᵥw)) := by
  have hG : Bdd (-(Real.pi)) (fun w => (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
    obtain ⟨C, N, hC, hN, hb⟩ := E_bdd_Xfun
    refine ⟨Real.pi * C, N, by positivity, hN, fun w hw => ?_⟩
    have h := hb w hw
    rw [norm_mul, norm_mul, EtailE.norm_pi, Complex.norm_I, mul_one]
    calc Real.pi * ‖Work.Residues.Xfun w‖
        ≤ Real.pi * (C * (scale w) ^ N * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) :=
          mul_le_mul_of_nonneg_left h Real.pi_pos.le
      _ = Real.pi * C * (scale w) ^ N * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
  have h := TBS.of_bdd_cocycle (c := -(2 * Real.pi)) (c' := -(Real.pi))
    (F := fun w => psiCombo ℓ w)
    (G := fun w => (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)
    (EtailE.E_bdd_psi4E8_sub ℓ) hG ?_
  · have hmax : max (-(2 * Real.pi)) (-(Real.pi)) = -(Real.pi) := by
      rw [max_eq_right]; linarith [Real.pi_pos]
    rwa [hmax] at h
  · intro w n hn
    rcases hn with hh | hh
    · rw [hh, Int.cast_one]; push_cast; rw [one_mul]
      exact psiCombo_vadd_one ℓ w
    · rw [hh, Int.cast_neg, Int.cast_one]; push_cast; rw [neg_one_mul]
      exact psiCombo_vadd_neg_one ℓ w

private lemma lamb_eq_aux (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Residues.Lamb ℓ τ
      = Work.Kernels.E4Fun τ * psiCombo ℓ τ / Work.Kernels.DeltaFun τ := by
  rw [Work.Residues.Lamb_eq]
  simp only [psiCombo, Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun]
  ring

/-- `Λ = E₄(ψ₄E₈ - ψ₂E₁₀)/Δ` on the tiles is `O(e^{π Im(Sw)})`. -/
lemma TBS.lamb (ℓ : Work.Kernels.LogLambdaData) :
    TBS Real.pi 0 (fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) := by
  have h : TBS (0 + -(Real.pi) + 2 * Real.pi) 0 (fun w n z =>
      Work.Kernels.E4Fun ((n:ℝ)+ᵥw) * psiCombo ℓ ((n:ℝ)+ᵥw)
        * (Work.Kernels.DeltaFun ((n:ℝ)+ᵥw))⁻¹) := by
    have h := (TBS.E4.mul (TBS.psi_combo ℓ)).mul TBS.invDelta
    simpa using h
  have h2 : TBS (0 + -(Real.pi) + 2 * Real.pi) 0
      (fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) :=
    h.congr (G := fun w n _ => Work.Residues.Lamb ℓ ((n:ℝ)+ᵥw)) (fun w n z => by
      rw [lamb_eq_aux ℓ ((n:ℝ)+ᵥw)]; ring)
  exact h2.mono (by linarith) (le_refl 0)

/-- **Sharp absorption.**  With the sharp threshold `Im (S•w) + 1 ≤ t` the exponents
`(a, b)` with `a ≤ b π` and `1 ≤ b` are dominated by the target exponents `(π, 1)`, since
`(a - π) Im(Sw) ≤ (b - 1) π Im(Sw) ≤ (b - 1) π t`. -/
lemma TBS.absorb_gen {F : ℍ → ℤ → ℍ → ℂ} {a b : ℝ} (h : TBS a b F) (hb : 1 ≤ b)
    (ha : a ≤ b * Real.pi) : TBS Real.pi 1 F := by
  obtain ⟨C, N, M, hC, hN, hM, hbnd⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => ?_⟩
  refine le_trans (hbnd w n z t hn hw hz ht) ?_
  have hH0 : 0 ≤ (ModularGroup.S • w).im := by linarith [hw.2]
  have hHt : (ModularGroup.S • w).im ≤ t := by linarith [ht]
  have hcoef : 0 ≤ (b - 1) * Real.pi := mul_nonneg (by linarith) Real.pi_pos.le
  have hstep : (a - Real.pi) * (ModularGroup.S • w).im ≤ (b - 1) * Real.pi * t := by
    have h1 : a - Real.pi ≤ (b - 1) * Real.pi := by nlinarith [ha, Real.pi_pos]
    have h2 : (b - 1) * Real.pi * (ModularGroup.S • w).im ≤ (b - 1) * Real.pi * t :=
      mul_le_mul_of_nonneg_left hHt hcoef
    nlinarith [h1, hH0, h2]
  have hexp : Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      ≤ Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t) := by
    rw [Real.exp_le_exp]; nlinarith [hstep]
  exact mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith [hw.2]) _))

/-- Transport of a `TBS` bound along an equality valid on the tiles (sharp threshold). -/
lemma TBS.congr_tile {a b : ℝ} {F G : ℍ → ℤ → ℍ → ℂ} (h : TBS a b F)
    (hFG : ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      (z : ℂ) = (t : ℂ) * Complex.I → (ModularGroup.S • w).im + 1 ≤ t →
      F w n z = G w n z) : TBS a b G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [← hFG w n z t hn hw hz ht]
    exact hb w n z t hn hw hz ht⟩

/-- Glue a decaying `z`-atom to a `TBS` bound. -/
lemma TBS.mul_ZC {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZC m n f) (hG : TBS a b G) : TBS a (b + n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1:ℝ) ≤ t := by linarith [hw.2]
  rw [norm_mul]
  have hfz := hb1 z t ht1 hz
  have hS := hb2 w k z t hk hw hz ht
  have hS0 : (0:ℝ) ≤ C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (-(n * Real.pi * t))
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b + n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (-(n * Real.pi * t))
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

/-- Glue a growing `z`-atom to a `TBS` bound. -/
lemma TBS.mul_ZCg {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZCg m n f) (hG : TBS a b G) : TBS a (b - n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1:ℝ) ≤ t := by linarith [hw.2]
  rw [norm_mul]
  have hfz := hb1 z t ht1 hz
  have hS := hb2 w k z t hk hw hz ht
  have hS0 : (0:ℝ) ≤ C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
      (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (n * Real.pi * t)
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b - n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (n * Real.pi * t))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (n * Real.pi * t)
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

def ZC3 (m n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : ℍ) (t : ℝ), 3 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
    ‖f z‖ ≤ C * (1 + t) ^ m * Real.exp (-(n * Real.pi * t))

/-- `ZCg3 m n f`: `‖f z‖ ≤ C (1+t)^m e^{nπt}` on the contour `z = i t`, for `t ≥ 5`. -/
def ZCg3 (m n : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (z : ℍ) (t : ℝ), 3 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
    ‖f z‖ ≤ C * (1 + t) ^ m * Real.exp (n * Real.pi * t)

namespace ZC3

variable {m n m' n' : ℝ} {f g : ℍ → ℂ}

lemma mono (h : ZC3 m n f) (hm : m ≤ m') (hn : n' ≤ n) : ZC3 m' n' f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ m' := Real.rpow_le_rpow_of_exponent_le (by linarith) hm
  have h2 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (-(n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : n' * (Real.pi * t) ≤ n * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) h2 (Real.exp_pos _).le
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

lemma add (hf : ZC3 m n f) (hg : ZC3 m' n' g) : ZC3 (max m m') (min n n') (fun z => f z + g z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, hC2, hb2⟩ := hg
  refine ⟨C1 + C2, by positivity, fun z t ht hz => ?_⟩
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ (max m m') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have h2 : (1 + t) ^ m' ≤ (1 + t) ^ (max m m') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hm1 : (0:ℝ) ≤ (1 + t) ^ (max m m') := Real.rpow_nonneg (by linarith) _
  have h3 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (-(min n n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : min n n' * (Real.pi * t) ≤ n * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right (min_le_left n n') (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  have h4 : Real.exp (-(n' * Real.pi * t)) ≤ Real.exp (-(min n n' * Real.pi * t)) := by
    rw [Real.exp_le_exp]
    have hmul : min n n' * (Real.pi * t) ≤ n' * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right (min_le_right n n') (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  have hb1' : ‖f z‖ ≤ C1 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) :=
    le_trans (hb1 z t ht hz) (mul_le_mul (mul_le_mul_of_nonneg_left h1 hC1.le) h3
      (Real.exp_pos _).le (mul_nonneg hC1.le hm1))
  have hb2' : ‖g z‖ ≤ C2 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) :=
    le_trans (hb2 z t ht hz) (mul_le_mul (mul_le_mul_of_nonneg_left h2 hC2.le) h4
      (Real.exp_pos _).le (mul_nonneg hC2.le hm1))
  refine le_trans (norm_add_le _ _) ?_
  rw [show (C1 + C2) * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t))
      = C1 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t))
        + C2 * (1 + t) ^ (max m m') * Real.exp (-(min n n' * Real.pi * t)) from by ring]
  exact add_le_add hb1' hb2'

lemma mul (hf : ZC3 m n f) (hg : ZC3 m' n' g) : ZC3 (m + m') (n + n') (fun z => f z * g z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, hC2, hb2⟩ := hg
  refine ⟨C1 * C2, by positivity, fun z t ht hz => ?_⟩
  rw [norm_mul]
  have h1 := hb1 z t ht hz
  have h2 := hb2 z t ht hz
  have hr : (1 + t) ^ m * (1 + t) ^ m' = (1 + t) ^ (m + m') :=
    (Real.rpow_add (by linarith : (0:ℝ) < 1 + t) m m').symm
  have hexp : Real.exp (-(n * Real.pi * t)) * Real.exp (-(n' * Real.pi * t))
      = Real.exp (-((n + n') * Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : (0:ℝ) ≤ C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)) :=
    mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
  calc ‖f z‖ * ‖g z‖
      ≤ (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (1 + t) ^ m' * Real.exp (-(n' * Real.pi * t))) :=
        mul_le_mul h1 h2 (norm_nonneg _) h3
    _ = C1 * C2 * (1 + t) ^ (m + m') * Real.exp (-((n + n') * Real.pi * t)) := by
        rw [← hr, ← hexp]; ring

lemma neg (hf : ZC3 m n f) : ZC3 m n (fun z => -f z) := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, fun z t ht hz => by rw [norm_neg]; exact hb z t ht hz⟩

lemma sub (hf : ZC3 m n f) (hg : ZC3 m' n' g) : ZC3 (max m m') (min n n') (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma congr (h : ZC3 m n f) (hfg : ∀ z, f z = g z) : ZC3 m n g := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun z t ht hz => by rw [← hfg]; exact hb z t ht hz⟩

lemma const (m : ℝ) (hm : 0 ≤ m) (c : ℂ) : ZC3 m 0 (fun _ => c) := by
  refine ⟨‖c‖ + 1, by positivity, fun z t ht hz => ?_⟩
  rw [show -(0 * Real.pi * t) = 0 from by ring, Real.exp_zero, mul_one]
  have h1 : (1:ℝ) ≤ (1 + t) ^ m := Real.one_le_rpow (by linarith) hm
  have h0 : (0:ℝ) ≤ (1 + t) ^ m := Real.rpow_nonneg (by linarith) m
  nlinarith [norm_nonneg c, h1, h0]

lemma cmul (c : ℂ) (h : ZC3 m n f) : ZC3 m n (fun z => c * f z) :=
  ((const 0 le_rfl c).mul h).mono (m' := m) (n' := n) (by linarith) (by linarith)

end ZC3

namespace ZCg3

variable {m n m' n' : ℝ} {f g : ℍ → ℂ}

lemma mono (h : ZCg3 m n f) (hm : m ≤ m') (hn : n ≤ n') : ZCg3 m' n' f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : (1 + t) ^ m ≤ (1 + t) ^ m' := Real.rpow_le_rpow_of_exponent_le (by linarith) hm
  have h2 : Real.exp (n * Real.pi * t) ≤ Real.exp (n' * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have hmul : n * (Real.pi * t) ≤ n' * (Real.pi * t) :=
      mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le (by linarith))
    nlinarith [hmul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC.le) h2 (Real.exp_pos _).le
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

lemma congr (h : ZCg3 m n f) (hfg : ∀ z, f z = g z) : ZCg3 m n g := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun z t ht hz => by rw [← hfg]; exact hb z t ht hz⟩

lemma of_ZC (h : ZC3 m n f) (hn : 0 ≤ n) : ZCg3 m n f := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  refine le_trans (hb z t ht hz) ?_
  have h1 : Real.exp (-(n * Real.pi * t)) ≤ Real.exp (n * Real.pi * t) := by
    rw [Real.exp_le_exp]
    have hnt : 0 ≤ n * (Real.pi * t) := mul_nonneg hn (mul_nonneg Real.pi_pos.le (by linarith))
    linarith
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))

end ZCg3

/-- Glue a decaying `z`-atom to a `TBS` bound (threshold `5`). -/
lemma TBS.mul_ZC3 {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZC3 m n f) (hG : TBS a b G) : TBS a (b + n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht3 : (3:ℝ) ≤ t := by have h := hw.2; linarith
  rw [norm_mul]
  have hfz := hb1 z t ht3 hz
  have hS := hb2 w k z t hk hw hz ht
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (-(n * Real.pi * t))
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b + n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (-(n * Real.pi * t)))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (-(n * Real.pi * t))
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

/-- Glue a growing `z`-atom to a `TBS` bound (threshold `5`). -/
lemma TBS.mul_ZCg3 {m n : ℝ} (hm : 0 ≤ m) {f : ℍ → ℂ} {G : ℍ → ℤ → ℍ → ℂ} {a b : ℝ}
    (hf : ZCg3 m n f) (hG : TBS a b G) : TBS a (b - n) (fun w k z => f z * G w k z) := by
  obtain ⟨C1, hC1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hG
  refine ⟨C1 * C2, N2, M2 + m, by positivity, hN2, by linarith,
    fun w k z t hk hw hz ht => ?_⟩
  have ht3 : (3:ℝ) ≤ t := by have h := hw.2; linarith
  rw [norm_mul]
  have hfz := hb1 z t ht3 hz
  have hS := hb2 w k z t hk hw hz ht
  refine le_trans (mul_le_mul hfz hS (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)) ?_
  have hr : (1 + t) ^ m * (1 + t) ^ M2 = (1 + t) ^ (M2 + m) := by
    rw [mul_comm, ← Real.rpow_add (by linarith : (0:ℝ) < 1 + t) M2 m]
  have hexp : Real.exp (n * Real.pi * t)
      * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)
      = Real.exp (a * (ModularGroup.S • w).im - (b - n) * Real.pi * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show (C1 * (1 + t) ^ m * Real.exp (n * Real.pi * t))
        * (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t))
      = C1 * C2 * (Work.Kernels.scale w) ^ N2 * ((1 + t) ^ m * (1 + t) ^ M2)
        * (Real.exp (n * Real.pi * t)
          * Real.exp (a * (ModularGroup.S • w).im - b * Real.pi * t)) from by ring,
    hr, hexp]

end

end Work.Asymptotics.Tile
