import Mathlib
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_main
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KMFDTauAtoms
import Submission.Work.Asymptotics.KMFDZDevs
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Funnel24Tail.ShSinvrefFunnelBound
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelMainBound

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics.EtailE

open Work.Kernels
open Work.Residues (Ept)

lemma E_bdd_psi2E10 (ℓ : LogLambdaData) :
    Bdd 0 (fun w => psi2 ℓ w * E10Fun w) := by
  simpa using (E_bdd_psi2 ℓ).mul (E_bdd_E10)

lemma E_bdd_psi4E8 (ℓ : LogLambdaData) :
    Bdd 0 (fun w => psi4 ℓ w * E8Fun w) := by
  simpa using (E_bdd_psi4 ℓ).mul (E_bdd_E8)

lemma E_bdd_j_psi_sub (ℓ : LogLambdaData) :
    Bdd 0 (fun w => jInvariantFun w * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w)) := by
  have h := (E_bdd_j).mul (E_bdd_psi4E8_sub ℓ)
  convert h using 1
  ring

lemma E_bdd_j_Delta :
    Bdd 0 (fun w => jInvariantFun w * DeltaFun w) := by
  have h := (E_bdd_j).mul (E_bdd_Delta)
  convert h using 1
  ring

lemma E_bdd_j_psi2E10 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => jInvariantFun w * (psi2 ℓ w * E10Fun w)) := by
  simpa using (E_bdd_j).mul (E_bdd_psi2E10 ℓ)

lemma E_bdd_j_psi4E8 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => jInvariantFun w * (psi4 ℓ w * E8Fun w)) := by
  simpa using (E_bdd_j).mul (E_bdd_psi4E8 ℓ)

lemma E_bdd_j2_psi_sub (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi)
      (fun w => jInvariantFun w ^ 2 * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w)) := by
  have h := ((E_bdd_j).mul E_bdd_j).mul (E_bdd_psi4E8_sub ℓ)
  have h2 : Bdd ((2 * Real.pi + 2 * Real.pi) + -(2 * Real.pi))
      (fun w => jInvariantFun w ^ 2 * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w)) :=
    Bdd.congr (funext fun w => by ring) h
  have hc : ((2 * Real.pi + 2 * Real.pi) + -(2 * Real.pi)) = 2 * Real.pi := by ring
  rw [hc] at h2
  exact h2


/-! ## Elementary contour facts -/

lemma two_im_S_le {w : ℍ} {t : ℝ} (ht : Ethresh w t) :
    2 * (ModularGroup.S • w).im ≤ t := by
  have h := ht; simp only [Ethresh] at h; linarith

lemma E_im_S_nonneg' {w : ℍ} (hw : w ∈ KEpsilon) : 0 ≤ (ModularGroup.S • w).im :=
  E_im_S_nonneg hw

lemma E_t_nonneg {w : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t) : 0 ≤ t := by
  have := two_im_S_le ht; linarith [hw.2]

lemma E_t_one_le {w : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t) :
    (1:ℝ) ≤ 1 + t := by linarith [E_t_nonneg hw ht]

/-- `‖Ept z‖^k = e^{-kπt}` on the contour. -/
lemma Ept_pow_norm {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) (k : ℕ) :
    ‖(Ept z) ^ k‖ = Real.exp (-((k : ℝ) * Real.pi * t)) := by
  rw [norm_pow, Work.Asymptotics.kmfd_norm_Ept_of_contour hz, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Absorption: `e^{-kπt} · e^{c·Im(Sw)} ≤ e^{-πt}` when `c ≤ 2π(k-1)`. -/
lemma E_exp_absorb {c : ℝ} {k : ℕ} (hk : 1 ≤ k) (hc : c ≤ 2 * Real.pi * ((k : ℝ) - 1))
    {w : ℍ} (hw : w ∈ KEpsilon) {t : ℝ} (ht : Ethresh w t) :
    Real.exp (-((k : ℝ) * Real.pi * t)) * Real.exp (c * (ModularGroup.S • w).im)
      ≤ Real.exp (-(Real.pi * t)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : 2 * (ModularGroup.S • w).im ≤ t := two_im_S_le ht
  have hI : 0 ≤ (ModularGroup.S • w).im := E_im_S_nonneg hw
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
  have h1 : c * (ModularGroup.S • w).im
      ≤ (2 * Real.pi * ((k:ℝ) - 1)) * (ModularGroup.S • w).im :=
    mul_le_mul_of_nonneg_right hc hI
  have h3 : 2 * Real.pi * ((k:ℝ) - 1) * (ModularGroup.S • w).im
      ≤ Real.pi * ((k:ℝ) - 1) * t := by
    calc 2 * Real.pi * ((k:ℝ) - 1) * (ModularGroup.S • w).im
        = (Real.pi * ((k:ℝ) - 1)) * (2 * (ModularGroup.S • w).im) := by ring
      _ ≤ (Real.pi * ((k:ℝ) - 1)) * t :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg Real.pi_pos.le hk0)
      _ = Real.pi * ((k:ℝ) - 1) * t := by ring
  have h4 : c * (ModularGroup.S • w).im ≤ Real.pi * ((k:ℝ) - 1) * t := le_trans h1 h3
  have hkey : -((k:ℝ) * Real.pi * t) + Real.pi * ((k:ℝ) - 1) * t = -(Real.pi * t) := by ring
  linarith [h4, hkey]

/-- The main monomial step: `Ept z^k · G w` inherits the shape of `G`. -/
lemma Ept_pow_mul_bound {G : ℍ → ℂ} {k : ℕ} {c Cg Ng Mg : ℝ}
    (hk : 1 ≤ k) (hCg : 0 ≤ Cg) (hMg : 0 ≤ Mg) (hc : c ≤ 2 * Real.pi * ((k:ℝ) - 1))
    {w z : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I)
    (hb : ‖G w‖ ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg
      * Real.exp (c * (ModularGroup.S • w).im)) :
    ‖(Ept z) ^ k * G w‖ ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg
      * Real.exp (-(Real.pi * t)) := by
  rw [norm_mul, Ept_pow_norm hz k]
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  have h1 : (0:ℝ) ≤ Real.exp (-((k:ℝ) * Real.pi * t)) := (Real.exp_pos _).le
  have h2 : (0:ℝ) ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg :=
    mul_nonneg (mul_nonneg hCg (E_rpow_nonneg w Ng)) (Real.rpow_nonneg h01t Mg)
  calc Real.exp (-((k:ℝ) * Real.pi * t)) * ‖G w‖
      ≤ Real.exp (-((k:ℝ) * Real.pi * t))
          * (Cg * (scale w) ^ Ng * (1 + t) ^ Mg
            * Real.exp (c * (ModularGroup.S • w).im)) := mul_le_mul_of_nonneg_left hb h1
    _ = Cg * (scale w) ^ Ng * (1 + t) ^ Mg
          * (Real.exp (-((k:ℝ) * Real.pi * t)) * Real.exp (c * (ModularGroup.S • w).im)) := by ring
    _ ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg * Real.exp (-(Real.pi * t)) :=
        mul_le_mul_of_nonneg_left (E_exp_absorb hk hc hw ht) h2

/-! ## The `E`-tail shape -/

/-- The shape of the `E`-tail estimates. -/
def EBnd (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon →
    Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
    ‖F w z‖ ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))

lemma EBnd.add {F G : ℍ → ℍ → ℂ} (hF : EBnd F) (hG : EBnd G) :
    EBnd (fun w z => F w z + G w z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun w z t hw ht hz => ?_⟩
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  have hs1 : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) := E_rpow_mono w (le_max_left _ _)
  have hs2 : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) := E_rpow_mono w (le_max_right _ _)
  have hm1 : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le h1t (le_max_left _ _)
  have hm2 : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le h1t (le_max_right _ _)
  have hE0 : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
  have h1' : ‖F w z‖ ≤ C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
      * Real.exp (-(Real.pi * t)) := by
    refine le_trans (h1 w z t hw ht hz) ?_
    have hnb : (0:ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg h01t M1
    have : C1 * (scale w) ^ N1 * (1 + t) ^ M1
        ≤ C1 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs1 hC1.le) hm1 hnb
        (mul_nonneg hC1.le (Real.rpow_nonneg (scale_pos w).le _))
    exact mul_le_mul_of_nonneg_right this hE0
  have h2' : ‖G w z‖ ≤ C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
      * Real.exp (-(Real.pi * t)) := by
    refine le_trans (h2 w z t hw ht hz) ?_
    have hnb : (0:ℝ) ≤ (1 + t) ^ M2 := Real.rpow_nonneg h01t M2
    have : C2 * (scale w) ^ N2 * (1 + t) ^ M2
        ≤ C2 * (scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs2 hC2.le) hm2 hnb
        (mul_nonneg hC2.le (Real.rpow_nonneg (scale_pos w).le _))
    exact mul_le_mul_of_nonneg_right this hE0
  refine le_trans (norm_add_le _ _) ?_
  have hcomb : C1 * (scale w) ^ max N1 N2 * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))
      + C2 * (scale w) ^ max N1 N2 * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))
      = (C1 + C2) * (scale w) ^ max N1 N2 * (1 + t) ^ max M1 M2
        * Real.exp (-(Real.pi * t)) := by ring
  linarith [h1', h2', hcomb]

lemma EBnd.const_mul (d : ℂ) {F : ℍ → ℍ → ℂ} (hF : EBnd F) :
    EBnd (fun w z => d * F w z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hF
  refine ⟨‖d‖ * C + 1, N, M, by positivity, hN, hM, fun w z t hw ht hz => ?_⟩
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (hb w z t hw ht hz) (norm_nonneg d)) ?_
  have h0 : (0:ℝ) ≤ (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    mul_nonneg (mul_nonneg (E_rpow_nonneg w N) (Real.rpow_nonneg h01t M)) (Real.exp_pos _).le
  nlinarith [h0, norm_nonneg d, hC]

lemma EBnd.congr {F G : ℍ → ℍ → ℂ} (h : EBnd F) (hfg : ∀ w z, F w z = G w z) : EBnd G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun w z t hw ht hz => by rw [← hfg w z]; exact hb w z t hw ht hz⟩


lemma E_bdd_R24_p0 (ℓ : LogLambdaData) :
    Bdd (0) (fun w => Compact.R24_p0 ℓ w) := by
  have hD : Bdd (0) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (0) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (0) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (0) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (0) (fun w : ℍ => (-29568 : ℂ) * (psi4 ℓ w * E8Fun w) + (15744 : ℂ) * (psi2 ℓ w * E10Fun w) + (-20570112 : ℂ) * (DeltaFun w) + (24 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w)) + (27648 : ℂ) * (jInvariantFun w * DeltaFun w)) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (-29568 : ℂ) (hP4)) (Bdd.const_mul (15744 : ℂ) (hP2))) (Bdd.const_mul (-20570112 : ℂ) (hD))) (Bdd.const_mul (24 : ℂ) (E_bdd_j_psi_sub ℓ))) (Bdd.const_mul (27648 : ℂ) (E_bdd_j_Delta))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p0]; try ring) hSum

lemma E_bdd_R24_p1 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => Compact.R24_p1 ℓ w) := by
  have hD : Bdd (2 * Real.pi) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (2 * Real.pi) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (2 * Real.pi) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (2 * Real.pi) (fun w : ℍ => (-896832 : ℂ) * (psi4 ℓ w * E8Fun w) + (-305856 : ℂ) * (psi2 ℓ w * E10Fun w) + (31850496 : ℂ) * (DeltaFun w) + (2040 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w)) + (-312 : ℂ) * (jInvariantFun w * (psi2 ℓ w * E10Fun w)) + (-41472 : ℂ) * (jInvariantFun w * DeltaFun w) + (-1 : ℂ) * (jInvariantFun w ^ 2 * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w))) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (-896832 : ℂ) (hP4)) (Bdd.const_mul (-305856 : ℂ) (hP2))) (Bdd.const_mul (31850496 : ℂ) (hD))) (Bdd.const_mul (2040 : ℂ) (E_bdd_j_psi4E8 ℓ))) (Bdd.const_mul (-312 : ℂ) (E_bdd_j_psi2E10 ℓ))) (Bdd.const_mul (-41472 : ℂ) (hjD))) (Bdd.const_mul (-1 : ℂ) (E_bdd_j2_psi_sub ℓ))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p1]; try ring) hSum

lemma E_bdd_R24_p2 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => Compact.R24_p2 ℓ w) := by
  have hD : Bdd (2 * Real.pi) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (2 * Real.pi) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (2 * Real.pi) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (2 * Real.pi) (fun w : ℍ => (12616704 : ℂ) * (psi4 ℓ w * E8Fun w) + (-2663424 : ℂ) * (psi2 ℓ w * E10Fun w) + (-15925248 : ℂ) * (DeltaFun w) + (-23424 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w)) + (9600 : ℂ) * (jInvariantFun w * (psi2 ℓ w * E10Fun w)) + (8 : ℂ) * (jInvariantFun w ^ 2 * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w))) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (12616704 : ℂ) (hP4)) (Bdd.const_mul (-2663424 : ℂ) (hP2))) (Bdd.const_mul (-15925248 : ℂ) (hD))) (Bdd.const_mul (-23424 : ℂ) (E_bdd_j_psi4E8 ℓ))) (Bdd.const_mul (9600 : ℂ) (E_bdd_j_psi2E10 ℓ))) (Bdd.const_mul (8 : ℂ) (E_bdd_j2_psi_sub ℓ))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p2]; try ring) hSum

lemma E_bdd_R24_p3 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => Compact.R24_p3 ℓ w) := by
  have hD : Bdd (2 * Real.pi) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (2 * Real.pi) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (2 * Real.pi) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (2 * Real.pi) (fun w : ℍ => (-49268736 : ℂ) * (psi4 ℓ w * E8Fun w) + (19408896 : ℂ) * (psi2 ℓ w * E10Fun w) + (23887872 : ℂ) * (DeltaFun w) + (86976 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w)) + (-45504 : ℂ) * (jInvariantFun w * (psi2 ℓ w * E10Fun w)) + (-24 : ℂ) * (jInvariantFun w ^ 2 * (psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w))) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (-49268736 : ℂ) (hP4)) (Bdd.const_mul (19408896 : ℂ) (hP2))) (Bdd.const_mul (23887872 : ℂ) (hD))) (Bdd.const_mul (86976 : ℂ) (E_bdd_j_psi4E8 ℓ))) (Bdd.const_mul (-45504 : ℂ) (E_bdd_j_psi2E10 ℓ))) (Bdd.const_mul (-24 : ℂ) (E_bdd_j2_psi_sub ℓ))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p3]; try ring) hSum

lemma E_bdd_R24_p4 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => Compact.R24_p4 ℓ w) := by
  have hD : Bdd (2 * Real.pi) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (2 * Real.pi) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (2 * Real.pi) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (2 * Real.pi) (fun w : ℍ => (72990720 : ℂ) * (psi4 ℓ w * E8Fun w) + (-72990720 : ℂ) * (psi2 ℓ w * E10Fun w) + (11466178560 : ℂ) * (DeltaFun w) + (-101376 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w)) + (101376 : ℂ) * (jInvariantFun w * (psi2 ℓ w * E10Fun w)) + (-15925248 : ℂ) * (jInvariantFun w * DeltaFun w)) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (72990720 : ℂ) (hP4)) (Bdd.const_mul (-72990720 : ℂ) (hP2))) (Bdd.const_mul (11466178560 : ℂ) (hD))) (Bdd.const_mul (-101376 : ℂ) (E_bdd_j_psi4E8 ℓ))) (Bdd.const_mul (101376 : ℂ) (E_bdd_j_psi2E10 ℓ))) (Bdd.const_mul (-15925248 : ℂ) (hjD))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p4]; try ring) hSum

lemma E_bdd_R24_p5 (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w => Compact.R24_p5 ℓ w) := by
  have hD : Bdd (2 * Real.pi) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (2 * Real.pi) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (2 * Real.pi) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (2 * Real.pi) (fun w : ℍ => (-656916480 : ℂ) * (psi4 ℓ w * E8Fun w) + (656916480 : ℂ) * (psi2 ℓ w * E10Fun w) + (-17199267840 : ℂ) * (DeltaFun w) + (912384 : ℂ) * (jInvariantFun w * (psi4 ℓ w * E8Fun w)) + (-912384 : ℂ) * (jInvariantFun w * (psi2 ℓ w * E10Fun w)) + (23887872 : ℂ) * (jInvariantFun w * DeltaFun w)) :=
    Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.add (Bdd.const_mul (-656916480 : ℂ) (hP4)) (Bdd.const_mul (656916480 : ℂ) (hP2))) (Bdd.const_mul (-17199267840 : ℂ) (hD))) (Bdd.const_mul (912384 : ℂ) (E_bdd_j_psi4E8 ℓ))) (Bdd.const_mul (-912384 : ℂ) (E_bdd_j_psi2E10 ℓ))) (Bdd.const_mul (23887872 : ℂ) (hjD))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_p5]; try ring) hSum

lemma E_bdd_R24_q1 (ℓ : LogLambdaData) :
    Bdd (0) (fun w => Compact.R24_q1 ℓ w) := by
  have hD : Bdd (0) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (0) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (0) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (0) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (0) (fun w : ℍ => (1990656 : ℂ) * (DeltaFun w)) :=
    Bdd.const_mul (1990656 : ℂ) (hD)
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_q1]; try ring) hSum

lemma E_bdd_R24_q3 (ℓ : LogLambdaData) :
    Bdd (0) (fun w => Compact.R24_q3 ℓ w) := by
  have hD : Bdd (0) (fun w : ℍ => DeltaFun w) :=
    E_bdd_Delta.mono (by linarith [Real.pi_pos])
  have hP4 : Bdd (0) (fun w : ℍ => psi4 ℓ w * E8Fun w) :=
    (E_bdd_psi4E8 ℓ).mono (by linarith [Real.pi_pos])
  have hP2 : Bdd (0) (fun w : ℍ => psi2 ℓ w * E10Fun w) :=
    (E_bdd_psi2E10 ℓ).mono (by linarith [Real.pi_pos])
  have hjD : Bdd (0) (fun w : ℍ => jInvariantFun w * DeltaFun w) :=
    (E_bdd_j_Delta).mono (by linarith [Real.pi_pos])
  have hSum : Bdd (0) (fun w : ℍ => (-1433272320 : ℂ) * (DeltaFun w) + (1990656 : ℂ) * (jInvariantFun w * DeltaFun w)) :=
    Bdd.add (Bdd.const_mul (-1433272320 : ℂ) (hD)) (Bdd.const_mul (1990656 : ℂ) (E_bdd_j_Delta))
  exact Bdd.congr (funext fun w => by simp only [Compact.R24_q3]; try ring) hSum

/-! ## Inflation and coefficient helpers -/

lemma inflate_E {F : ℍ → ℂ} {Cg Ng Mg C N M : ℝ} {w : ℍ} {t : ℝ}
    (hC : Cg ≤ C) (hN : Ng ≤ N) (hM : Mg ≤ M) (hC0 : 0 ≤ C)
    (ht1 : (1:ℝ) ≤ 1 + t)
    (h : ‖F w‖ ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg * Real.exp (-(Real.pi * t))) :
    ‖F w‖ ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  have h0 : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
  have hs : (scale w) ^ Ng ≤ (scale w) ^ N := E_rpow_mono w hN
  have hm : (1 + t) ^ Mg ≤ (1 + t) ^ M := Real.rpow_le_rpow_of_exponent_le ht1 hM
  have hinner : Cg * (scale w) ^ Ng * (1 + t) ^ Mg ≤ C * (scale w) ^ N * (1 + t) ^ M :=
    mul_le_mul (mul_le_mul hC hs (E_rpow_nonneg w Ng) hC0) hm
      (Real.rpow_nonneg h01t Mg) (mul_nonneg hC0 (E_rpow_nonneg w N))
  calc ‖F w‖ ≤ Cg * (scale w) ^ Ng * (1 + t) ^ Mg * Real.exp (-(Real.pi * t)) := h
    _ ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
        mul_le_mul_of_nonneg_right hinner h0

lemma norm_six_sum_le {a b c d e f : ℂ} {A B C D E F : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) : ‖a + b + c + d + e + f‖ ≤ A + B + C + D + E + F := by
  have h1 := norm_add_le (a + b + c + d + e) f
  have h2 := norm_add_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith

/-- The combined bound for the coefficient `Xc·q + p` on `E`. -/
lemma E_coeff_le (ℓ : LogLambdaData) {w z : ℍ} {t : ℝ} {q p : ℂ} {Cq Nq Cp Np : ℝ}
    (hw : w ∈ KEpsilon) (ht : Ethresh w t) (hz : (z : ℂ) = (t : ℂ) * Complex.I)
    (hCq : 0 ≤ Cq) (hNq : 0 ≤ Nq) (hCp : 0 ≤ Cp) (hNp : 0 ≤ Np)
    (hq : ‖q‖ ≤ Cq * (scale w) ^ Nq)
    (hp : ‖p‖ ≤ Cp * (scale w) ^ Np * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :
    ‖Compact.Xc ℓ z * q + p‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq + Cp) * (scale w) ^ (Nq + Np + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
  set Kx : ℝ := Real.pi + ‖Compact.cuspC ℓ‖ with hKxdef
  have ht0 : 0 ≤ t := E_t_nonneg hw ht
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  have hKx0 : 0 ≤ Kx := by rw [hKxdef]; positivity
  have hE1 : (1:ℝ) ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    Real.one_le_exp (by positivity)
  have hE0 : (0:ℝ) ≤ Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := (Real.exp_pos _).le
  have hXc : ‖Compact.Xc ℓ z‖ ≤ Kx * (1 + t) := by
    have h := Compact.kaux_norm_Xc_le ℓ z
    rw [Work.Asymptotics.kmfd_norm_coe_of_contour hz ht0] at h
    rw [hKxdef]; exact h
  have hsNq : (scale w) ^ Nq ≤ (scale w) ^ (Nq + Np + 1) := E_rpow_mono w (by linarith)
  have hsNp : (scale w) ^ Np ≤ (scale w) ^ (Nq + Np + 1) := E_rpow_mono w (by linarith)
  have hA : ‖Compact.Xc ℓ z‖ * ‖q‖
      ≤ Kx * Cq * (scale w) ^ (Nq + Np + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have h1 : ‖Compact.Xc ℓ z‖ * ‖q‖ ≤ (Kx * (1 + t)) * (Cq * (scale w) ^ Nq) :=
      mul_le_mul hXc hq (norm_nonneg _) (mul_nonneg hKx0 h01t)
    refine le_trans h1 ?_
    have hkey : (scale w) ^ Nq * 1
        ≤ (scale w) ^ (Nq + Np + 1) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
      mul_le_mul hsNq hE1 (by norm_num) (E_rpow_nonneg w _)
    calc Kx * (1 + t) * (Cq * (scale w) ^ Nq)
        = Kx * Cq * (1 + t) * ((scale w) ^ Nq * 1) := by ring
      _ ≤ Kx * Cq * (1 + t)
            * ((scale w) ^ (Nq + Np + 1) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg hKx0 hCq) h01t)
      _ = Kx * Cq * (scale w) ^ (Nq + Np + 1) * (1 + t)
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by ring
  have hB : ‖p‖ ≤ Cp * (scale w) ^ (Nq + Np + 1) * (1 + t)
      * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    refine le_trans hp ?_
    have hkey : (scale w) ^ Np * 1 ≤ (scale w) ^ (Nq + Np + 1) * (1 + t) :=
      mul_le_mul hsNp h1t (by norm_num) (E_rpow_nonneg w _)
    calc Cp * (scale w) ^ Np * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Cp * ((scale w) ^ Np * 1) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by ring
      _ ≤ Cp * ((scale w) ^ (Nq + Np + 1) * (1 + t))
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hCp) hE0
      _ = Cp * (scale w) ^ (Nq + Np + 1) * (1 + t)
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by ring
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have hcomb : Kx * Cq * (scale w) ^ (Nq + Np + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
      + Cp * (scale w) ^ (Nq + Np + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
      = (Kx * Cq + Cp) * (scale w) ^ (Nq + Np + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by ring
  linarith [hA, hB, hcomb]

/-! ## The reference part `Tref24` on `E` -/

lemma E_Tref24_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Tref24 ℓ w z) := by
  obtain ⟨Cp0, Np0, hCp0, hNp0, hp0⟩ := E_bdd_R24_p0 ℓ
  obtain ⟨Cq1, Nq1, hCq1, hNq1, hq1⟩ := E_bdd_R24_q1 ℓ
  obtain ⟨Cp1, Np1, hCp1, hNp1, hp1⟩ := E_bdd_R24_p1 ℓ
  obtain ⟨Cq3, Nq3, hCq3, hNq3, hq3⟩ := E_bdd_R24_q3 ℓ
  obtain ⟨Cp2, Np2, hCp2, hNp2, hp2⟩ := E_bdd_R24_p2 ℓ
  obtain ⟨Cp3, Np3, hCp3, hNp3, hp3⟩ := E_bdd_R24_p3 ℓ
  obtain ⟨Cp4, Np4, hCp4, hNp4, hp4⟩ := E_bdd_R24_p4 ℓ
  obtain ⟨Cp5, Np5, hCp5, hNp5, hp5⟩ := E_bdd_R24_p5 ℓ
  have hKxnn : (0:ℝ) ≤ Real.pi + ‖Compact.cuspC ℓ‖ := by positivity
  have h1nn : 0 ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1 :=
    by linarith [mul_nonneg hKxnn hCq1.le, hCp1.le]
  have h2nn : 0 ≤ (Real.pi + ‖Compact.cuspC ℓ‖) + Cp2 := by linarith [hKxnn, hCp2.le]
  have h3nn : 0 ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3 :=
    by linarith [mul_nonneg hKxnn hCq3.le, hCp3.le]
  have h4nn : 0 ≤ (Real.pi + ‖Compact.cuspC ℓ‖) + Cp4 := by linarith [hKxnn, hCp4.le]
  have h5nn : 0 ≤ (Real.pi + ‖Compact.cuspC ℓ‖) + Cp5 := by linarith [hKxnn, hCp5.le]
  have hN1nn : 0 ≤ Nq1 + Np1 + 1 := by linarith
  have hN2nn : 0 ≤ Np2 + 1 := by linarith
  have hN3nn : 0 ≤ Nq3 + Np3 + 1 := by linarith
  have hN4nn : 0 ≤ Np4 + 1 := by linarith
  have hN5nn : 0 ≤ Np5 + 1 := by linarith
  set C : ℝ := Cp0 + ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1)
      + ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2)
      + ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3)
      + ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4)
      + ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) + 1 with hCdef
  set N : ℝ := Np0 + (Nq1 + Np1 + 1) + (Np2 + 1) + (Nq3 + Np3 + 1) + (Np4 + 1) + (Np5 + 1) + 1
    with hNdef
  have hCpos : 0 < C := by rw [hCdef]; linarith [hCp0, h1nn, h2nn, h3nn, h4nn, h5nn]
  have hNpos : 0 ≤ N := by rw [hNdef]; linarith [hNp0, hN1nn, hN2nn, hN3nn, hN4nn, hN5nn]
  have hCle0 : Cp0 ≤ C := by rw [hCdef]; linarith [h1nn, h2nn, h3nn, h4nn, h5nn]
  have hCle1 : (Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1 ≤ C :=
    by rw [hCdef]; linarith [hCp0, h2nn, h3nn, h4nn, h5nn]
  have hCle2 : (Real.pi + ‖Compact.cuspC ℓ‖) + Cp2 ≤ C :=
    by rw [hCdef]; linarith [hCp0, h1nn, h3nn, h4nn, h5nn]
  have hCle3 : (Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3 ≤ C :=
    by rw [hCdef]; linarith [hCp0, h1nn, h2nn, h4nn, h5nn]
  have hCle4 : (Real.pi + ‖Compact.cuspC ℓ‖) + Cp4 ≤ C :=
    by rw [hCdef]; linarith [hCp0, h1nn, h2nn, h3nn, h5nn]
  have hCle5 : (Real.pi + ‖Compact.cuspC ℓ‖) + Cp5 ≤ C :=
    by rw [hCdef]; linarith [hCp0, h1nn, h2nn, h3nn, h4nn]
  have hNle0 : Np0 ≤ N := by rw [hNdef]; linarith [hN1nn, hN2nn, hN3nn, hN4nn, hN5nn]
  have hNle1 : Nq1 + Np1 + 1 ≤ N := by rw [hNdef]; linarith [hNp0, hN2nn, hN3nn, hN4nn, hN5nn]
  have hNle2 : Np2 + 1 ≤ N := by rw [hNdef]; linarith [hNp0, hN1nn, hN3nn, hN4nn, hN5nn]
  have hNle3 : Nq3 + Np3 + 1 ≤ N := by rw [hNdef]; linarith [hNp0, hN1nn, hN2nn, hN4nn, hN5nn]
  have hNle4 : Np4 + 1 ≤ N := by rw [hNdef]; linarith [hNp0, hN1nn, hN2nn, hN3nn, hN5nn]
  have hNle5 : Np5 + 1 ≤ N := by rw [hNdef]; linarith [hNp0, hN1nn, hN2nn, hN3nn, hN4nn]
  refine ⟨C, N, 1, hCpos, hNpos, by norm_num, fun w z t hw ht hz => ?_⟩
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have hb0 : ‖Compact.Xc ℓ z * Compact.R24_q0 ℓ w + Compact.R24_p0 ℓ w‖
      ≤ Cp0 * (scale w) ^ Np0 * (1 + t) ^ (0:ℝ)
        * Real.exp (0 * (ModularGroup.S • w).im) := by
    have h := hp0 w hw
    simpa only [Compact.R24_q0, mul_zero, zero_add, Real.rpow_zero, mul_one] using h
  have cb1 : ‖Compact.Xc ℓ z * Compact.R24_q1 ℓ w + Compact.R24_p1 ℓ w‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1) * (scale w) ^ (Nq1 + Np1 + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    E_coeff_le ℓ hw ht hz hCq1.le hNq1 hCp1.le hNp1 (by simpa using hq1 w hw) (hp1 w hw)
  have cb2 : ‖Compact.Xc ℓ z * Compact.R24_q2 ℓ w + Compact.R24_p2 ℓ w‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2) * (scale w) ^ (Np2 + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have hq2 : ‖Compact.R24_q2 ℓ w‖ ≤ (1:ℝ) * (scale w) ^ (0:ℝ) := by simp [Compact.R24_q2]
    simpa only [mul_one, zero_add] using E_coeff_le ℓ hw ht hz (by norm_num : (0:ℝ) ≤ 1) (le_refl 0) hCp2.le hNp2 hq2 (hp2 w hw)
  have cb3 : ‖Compact.Xc ℓ z * Compact.R24_q3 ℓ w + Compact.R24_p3 ℓ w‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3) * (scale w) ^ (Nq3 + Np3 + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    E_coeff_le ℓ hw ht hz hCq3.le hNq3 hCp3.le hNp3 (by simpa using hq3 w hw) (hp3 w hw)
  have cb4 : ‖Compact.Xc ℓ z * Compact.R24_q4 ℓ w + Compact.R24_p4 ℓ w‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4) * (scale w) ^ (Np4 + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have hq4 : ‖Compact.R24_q4 ℓ w‖ ≤ (1:ℝ) * (scale w) ^ (0:ℝ) := by simp [Compact.R24_q4]
    simpa only [mul_one, zero_add] using E_coeff_le ℓ hw ht hz (by norm_num : (0:ℝ) ≤ 1) (le_refl 0) hCp4.le hNp4 hq4 (hp4 w hw)
  have cb5 : ‖Compact.Xc ℓ z * Compact.R24_q5 ℓ w + Compact.R24_p5 ℓ w‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) * (scale w) ^ (Np5 + 1) * (1 + t)
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have hq5 : ‖Compact.R24_q5 ℓ w‖ ≤ (1:ℝ) * (scale w) ^ (0:ℝ) := by simp [Compact.R24_q5]
    simpa only [mul_one, zero_add] using E_coeff_le ℓ hw ht hz (by norm_num : (0:ℝ) ≤ 1) (le_refl 0) hCp5.le hNp5 hq5 (hp5 w hw)
  have m0 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q0 ℓ w
      + Compact.R24_p0 ℓ w) (k := 1) (c := 0) (Cg := Cp0) (Ng := Np0) (Mg := 0)
    le_rfl hCp0.le (le_refl 0) (by norm_num) hw ht hz hb0
  have hT0 : ‖(Ept z) * (Compact.Xc ℓ z * Compact.R24_q0 ℓ w + Compact.R24_p0 ℓ w)‖
      ≤ Cp0 * (scale w) ^ N * (1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => Ept z * (Compact.Xc ℓ z * Compact.R24_q0 ℓ w
        + Compact.R24_p0 ℓ w)) (Cg := Cp0) (Ng := Np0) (Mg := 0) (C := Cp0) (N := N) (M := 1)
      (le_refl Cp0) hNle0 (by norm_num) hCp0.le h1t (by simpa using m0)
  have m1 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q1 ℓ w
      + Compact.R24_p1 ℓ w) (k := 2) (c := 2 * Real.pi)
    (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1) (Ng := Nq1 + Np1 + 1) (Mg := 1)
    (by norm_num) h1nn (by norm_num) (by push_cast; nlinarith [Real.pi_pos]) hw ht hz
    (by simpa only [Real.rpow_one] using cb1)
  have hT1 : ‖(Ept z) ^ (2:ℕ) * (Compact.Xc ℓ z * Compact.R24_q1 ℓ w + Compact.R24_p1 ℓ w)‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1) * (scale w) ^ N * (1 + t) ^ (1:ℝ)
        * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => (Ept z) ^ (2:ℕ) * (Compact.Xc ℓ z * Compact.R24_q1 ℓ w + Compact.R24_p1 ℓ w)) (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1) (Ng := Nq1 + Np1 + 1) (Mg := 1)
      (C := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1) (N := N) (M := 1)
      (le_refl _) hNle1 (le_refl 1) h1nn h1t m1
  have m2 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q2 ℓ w
      + Compact.R24_p2 ℓ w) (k := 3) (c := 2 * Real.pi)
    (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp2) (Ng := Np2 + 1) (Mg := 1)
    (by norm_num) h2nn (by norm_num) (by push_cast; nlinarith [Real.pi_pos]) hw ht hz
    (by simpa only [Real.rpow_one] using cb2)
  have hT2 : ‖(Ept z) ^ (3:ℕ) * (Compact.Xc ℓ z * Compact.R24_q2 ℓ w + Compact.R24_p2 ℓ w)‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2) * (scale w) ^ N * (1 + t) ^ (1:ℝ)
        * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => (Ept z) ^ (3:ℕ) * (Compact.Xc ℓ z * Compact.R24_q2 ℓ w + Compact.R24_p2 ℓ w)) (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp2) (Ng := Np2 + 1) (Mg := 1)
      (C := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp2) (N := N) (M := 1)
      (le_refl _) hNle2 (le_refl 1) h2nn h1t m2
  have m3 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q3 ℓ w
      + Compact.R24_p3 ℓ w) (k := 4) (c := 2 * Real.pi)
    (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3) (Ng := Nq3 + Np3 + 1) (Mg := 1)
    (by norm_num) h3nn (by norm_num) (by push_cast; nlinarith [Real.pi_pos]) hw ht hz
    (by simpa only [Real.rpow_one] using cb3)
  have hT3 : ‖(Ept z) ^ (4:ℕ) * (Compact.Xc ℓ z * Compact.R24_q3 ℓ w + Compact.R24_p3 ℓ w)‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3) * (scale w) ^ N * (1 + t) ^ (1:ℝ)
        * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => (Ept z) ^ (4:ℕ) * (Compact.Xc ℓ z * Compact.R24_q3 ℓ w + Compact.R24_p3 ℓ w)) (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3) (Ng := Nq3 + Np3 + 1) (Mg := 1)
      (C := (Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3) (N := N) (M := 1)
      (le_refl _) hNle3 (le_refl 1) h3nn h1t m3
  have m4 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q4 ℓ w
      + Compact.R24_p4 ℓ w) (k := 5) (c := 2 * Real.pi)
    (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp4) (Ng := Np4 + 1) (Mg := 1)
    (by norm_num) h4nn (by norm_num) (by push_cast; nlinarith [Real.pi_pos]) hw ht hz
    (by simpa only [Real.rpow_one] using cb4)
  have hT4 : ‖(Ept z) ^ (5:ℕ) * (Compact.Xc ℓ z * Compact.R24_q4 ℓ w + Compact.R24_p4 ℓ w)‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4) * (scale w) ^ N * (1 + t) ^ (1:ℝ)
        * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => (Ept z) ^ (5:ℕ) * (Compact.Xc ℓ z * Compact.R24_q4 ℓ w + Compact.R24_p4 ℓ w)) (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp4) (Ng := Np4 + 1) (Mg := 1)
      (C := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp4) (N := N) (M := 1)
      (le_refl _) hNle4 (le_refl 1) h4nn h1t m4
  have m5 := Ept_pow_mul_bound (G := fun w => Compact.Xc ℓ z * Compact.R24_q5 ℓ w
      + Compact.R24_p5 ℓ w) (k := 6) (c := 2 * Real.pi)
    (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) (Ng := Np5 + 1) (Mg := 1)
    (by norm_num) h5nn (by norm_num) (by push_cast; nlinarith [Real.pi_pos]) hw ht hz
    (by simpa only [Real.rpow_one] using cb5)
  have hT5 : ‖(Ept z) ^ (6:ℕ) * (Compact.Xc ℓ z * Compact.R24_q5 ℓ w + Compact.R24_p5 ℓ w)‖
      ≤ ((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) * (scale w) ^ N * (1 + t) ^ (1:ℝ)
        * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun w => (Ept z) ^ (6:ℕ) * (Compact.Xc ℓ z * Compact.R24_q5 ℓ w + Compact.R24_p5 ℓ w)) (Cg := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) (Ng := Np5 + 1) (Mg := 1)
      (C := (Real.pi + ‖Compact.cuspC ℓ‖) + Cp5) (N := N) (M := 1)
      (le_refl _) hNle5 (le_refl 1) h5nn h1t m5
  have hexp : Compact.Tref24 ℓ w z
      = Ept z * (Compact.Xc ℓ z * Compact.R24_q0 ℓ w + Compact.R24_p0 ℓ w)
        + (Ept z) ^ 2 * (Compact.Xc ℓ z * Compact.R24_q1 ℓ w + Compact.R24_p1 ℓ w)
        + (Ept z) ^ 3 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ w + Compact.R24_p2 ℓ w)
        + (Ept z) ^ 4 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ w + Compact.R24_p3 ℓ w)
        + (Ept z) ^ 5 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ w + Compact.R24_p4 ℓ w)
        + (Ept z) ^ 6 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ w + Compact.R24_p5 ℓ w) := by
    rw [Compact.Tref24_eq, Compact.R24]; ring
  have hsum := norm_six_sum_le hT0 hT1 hT2 hT3 hT4 hT5
  have hCe : Cp0 + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2)) + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5)) ≤ C := by rw [hCdef]; linarith
  have hfin : ‖Ept z * (Compact.Xc ℓ z * Compact.R24_q0 ℓ w + Compact.R24_p0 ℓ w)
        + (Ept z) ^ 2 * (Compact.Xc ℓ z * Compact.R24_q1 ℓ w + Compact.R24_p1 ℓ w)
        + (Ept z) ^ 3 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ w + Compact.R24_p2 ℓ w)
        + (Ept z) ^ 4 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ w + Compact.R24_p3 ℓ w)
        + (Ept z) ^ 5 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ w + Compact.R24_p4 ℓ w)
        + (Ept z) ^ 6 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ w + Compact.R24_p5 ℓ w)‖
      ≤ (Cp0 + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2)) + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5))) * (scale w) ^ N * (1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t)) := by
    refine le_trans hsum (le_of_eq ?_)
    ring
  change ‖Compact.Tref24 ℓ w z‖ ≤ C * (scale w) ^ N * (1 + t) ^ (1:ℝ)
    * Real.exp (-(Real.pi * t))
  rw [hexp]
  refine le_trans hfin ?_
  have hX0' : (0:ℝ) ≤ (1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) 1) (Real.exp_pos _).le
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe (E_rpow_nonneg w N)) hX0'
  calc (Cp0 + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2)) + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5))) * (scale w) ^ N * (1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t))
      = ((Cp0 + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq1 + Cp1)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp2)) + (((Real.pi + ‖Compact.cuspC ℓ‖) * Cq3 + Cp3)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp4)) + (((Real.pi + ‖Compact.cuspC ℓ‖) + Cp5))) * (scale w) ^ N) * ((1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t))) := by ring
    _ ≤ (C * (scale w) ^ N) * ((1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t))) := h2
    _ = C * (scale w) ^ N * (1 + t) ^ (1:ℝ) * Real.exp (-(Real.pi * t)) := by ring

/-! ## The exponential shape on `E` -/

/-- `EExp w t k b = e^{-kπt} e^{bπ Im (S w)}` on the contour. -/
def EExp (w : ℍ) (t k b : ℝ) : ℝ :=
  Real.exp (-(k * Real.pi * t)) * Real.exp (b * Real.pi * (ModularGroup.S • w).im)

lemma EExp_nonneg {w : ℍ} (t k b : ℝ) : 0 ≤ EExp w t k b :=
  mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

lemma EExp_mul {w : ℍ} (t k1 b1 k2 b2 : ℝ) :
    EExp w t k1 b1 * EExp w t k2 b2 = EExp w t (k1 + k2) (b1 + b2) := by
  simp only [EExp, ← Real.exp_add]
  congr 1
  ring

lemma EExp_zero_zero {w : ℍ} (t : ℝ) : EExp w t 0 0 = 1 := by
  simp [EExp]

lemma EExp_nat {w : ℍ} (t k : ℝ) : EExp w t k 0 = Real.exp (-(k * Real.pi * t)) := by
  simp [EExp]

lemma E_t_pos {w : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t) : 0 < t := by
  have h := two_im_S_le ht; linarith [hw.2]

lemma EExp_le {w : ℍ} {t k b : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hk : 1 ≤ k - b / 2) (hb : 0 ≤ b) :
    EExp w t k b ≤ Real.exp (-(Real.pi * t)) := by
  unfold EExp
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : 2 * (ModularGroup.S • w).im ≤ t := two_im_S_le ht
  have hb2 : b * Real.pi * (ModularGroup.S • w).im ≤ b * Real.pi * (t / 2) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb Real.pi_pos.le)
    linarith
  have hkey : -(k * Real.pi * t) + b * Real.pi * (t / 2) = -(Real.pi * t) * (k - b / 2) := by
    ring
  have ht0 : 0 < t := E_t_pos hw ht
  have hp : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
  have hfin : -(Real.pi * t) * (k - b / 2) ≤ -(Real.pi * t) := by
    nlinarith [mul_le_mul_of_nonneg_left hk hp.le]
  linarith

/-- `‖Ept z‖^n = EExp w t n 0` on the contour. -/
lemma Ept_pow_EExp {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) (w : ℍ) (n : ℕ) :
    ‖Ept z‖ ^ n = EExp w t (n : ℝ) 0 := by
  rw [Work.Asymptotics.kmfd_norm_Ept_of_contour hz, ← Real.exp_nat_mul]
  simp only [EExp, zero_mul, Real.exp_zero, mul_one]
  congr 1
  push_cast
  ring

/-- `(‖Ept z‖²)⁻¹ = EExp w t (-2) 0` on the contour. -/
lemma Ept_sq_inv_EExp {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) (w : ℍ) :
    (‖Ept z‖ ^ 2)⁻¹ = EExp w t (-2) 0 := by
  rw [Work.Asymptotics.kmfd_norm_Ept_of_contour hz, ← Real.exp_nat_mul, ← Real.exp_neg]
  simp only [EExp, zero_mul, Real.exp_zero, mul_one]
  congr 1
  push_cast
  ring

/-! ## The `z`-atoms on the contour -/

lemma E_zdevs (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.dDelta z‖ ≤ C * EExp w t 2 0 ∧
      ‖Compact.dW z‖ ≤ C * EExp w t 3 0 ∧
      ‖Compact.dD2 z‖ ≤ C * EExp w t 3 0 ∧
      ‖Compact.dL ℓ z‖ ≤ C * EExp w t 3 0 ∧
      ‖Compact.dE14 z‖ ≤ C * EExp w t 4 0 ∧
      ‖Compact.dE10 z‖ ≤ C * EExp w t 4 0 ∧
      ‖ℓ.L z‖ ≤ C * (1 + t) ∧
      ‖WFun z‖ ≤ C ∧
      ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C ∧
      ‖Compact.E10ref z‖ ≤ C ∧
      ‖Compact.E14ref z‖ ≤ C ∧
      ‖Compact.Dref z‖ ≤ C * EExp w t (-2) 0 ∧
      ‖E4Fun z ^ 3 - kmfd_E4refc z‖ ≤ C * EExp w t 4 0 ∧
      ‖DeltaFun z - (Ept z) ^ 2‖ ≤ C * EExp w t 4 0 ∧
      ‖jInvariantFun z - kmfd_jref z‖ ≤ C * EExp w t 2 0 := by
  obtain ⟨C0, hC0, hz⟩ := kmfd_zdevs ℓ
  refine ⟨C0, hC0, fun w z t hw ht hcont => ?_⟩
  have hz1 : (1:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hcont]; linarith [two_im_S_le ht, hw.2]
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17⟩ := hz z hz1
  have hzt : ‖(z : ℂ)‖ = t := Work.Asymptotics.kmfd_norm_coe_of_contour hcont (E_t_nonneg hw ht)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [Ept_pow_EExp hcont w 2] at h1; exact h1
  · rw [Ept_pow_EExp hcont w 3] at h2; exact h2
  · rw [Ept_pow_EExp hcont w 3] at h3; exact h3
  · rw [Ept_pow_EExp hcont w 3] at h4; exact h4
  · rw [Ept_pow_EExp hcont w 4] at h5; exact h5
  · rw [Ept_pow_EExp hcont w 4] at h6; exact h6
  · rw [hzt] at h10; exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · rw [Ept_sq_inv_EExp hcont w] at h15; exact h15
  · rw [Ept_pow_EExp hcont w 4] at h7; exact h7
  · rw [Ept_pow_EExp hcont w 4] at h8; exact h8
  · rw [Ept_pow_EExp hcont w 2] at h9; exact h9

/-! ## `w`-atoms and model coefficients on `E` -/

lemma Ept_sq_EExp {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) (w : ℍ) :
    ‖(Ept z) ^ 2‖ = EExp w t 2 0 := by
  rw [norm_pow]; exact Ept_pow_EExp hz w 2

lemma EExp_nat_le_one {w : ℍ} {t k : ℝ} (hk : 0 ≤ k) (hw : w ∈ KEpsilon) (ht : Ethresh w t) :
    EExp w t k 0 ≤ 1 := by
  rw [EExp_nat, Real.exp_le_one_iff]
  have ht0 : 0 ≤ t := E_t_nonneg hw ht
  have h : 0 ≤ k * Real.pi * t := mul_nonneg (mul_nonneg hk Real.pi_pos.le) ht0
  linarith

lemma EExp_absorb {w : ℍ} {t b k : ℝ} (hb : 0 ≤ b) (hbk : b ≤ k) (hw : w ∈ KEpsilon)
    (ht : Ethresh w t) :
    Real.exp (b * Real.pi * (ModularGroup.S • w).im) * EExp w t k 0 ≤ 1 := by
  rw [EExp_nat, ← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  have h2 : (ModularGroup.S • w).im ≤ t := by
    have := two_im_S_le ht; linarith [E_im_S_nonneg hw]
  have ht0 : 0 ≤ t := E_t_nonneg hw ht
  have h1 : b * Real.pi * (ModularGroup.S • w).im ≤ b * Real.pi * t :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hb Real.pi_pos.le)
  have h3 : b * Real.pi * t ≤ k * Real.pi * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbk Real.pi_pos.le) ht0
  linarith

/-- Scale-power inflation in the `EExp` shape. -/
lemma EExp_mono_scale {w : ℍ} {t k b C N N' : ℝ} (hC : 0 ≤ C) (hN : N ≤ N') :
    C * (scale w) ^ N * EExp w t k b ≤ C * (scale w) ^ N' * EExp w t k b :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (E_rpow_mono w hN) hC) (EExp_nonneg t k b)

lemma EExp_shape_nonneg {w : ℍ} {t k b C N : ℝ} (hC : 0 ≤ C) :
    (0:ℝ) ≤ C * (scale w) ^ N * EExp w t k b :=
  mul_nonneg (mul_nonneg hC (E_rpow_nonneg w N)) (EExp_nonneg t k b)

lemma EExp_zero_neg2 {w : ℍ} (t : ℝ) :
    EExp w t 0 (-2) = Real.exp ((-(2:ℝ)) * Real.pi * (ModularGroup.S • w).im) := by
  rw [EExp]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]

lemma E_Sinvref_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.Sinvref w z‖ ≤ C * (scale w) ^ N := by
  obtain ⟨Cj, Nj, hCj, hNj, hj⟩ := E_bdd_j
  refine ⟨1 + Cj + 720, Nj, by positivity, hNj, fun w z t hw ht hz => ?_⟩
  have hjw := hj w hw
  have hjw' : ‖jInvariantFun w - 720‖
      ≤ Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) + 720 := by
    have h := norm_sub_le (jInvariantFun w) (720 : ℂ)
    have h720 : ‖(720 : ℂ)‖ = 720 := by norm_num
    rw [h720] at h
    linarith [hjw]
  have hq : ‖(Ept z) ^ 2‖ = EExp w t 2 0 := Ept_sq_EExp hz w
  have hA : Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * EExp w t 2 0 ≤ 1 :=
    EExp_absorb (by norm_num) (le_refl 2) hw ht
  have hB : EExp w t 2 0 ≤ 1 := EExp_nat_le_one (by norm_num) hw ht
  have hprod : ‖(jInvariantFun w - 720) * (Ept z) ^ 2‖ ≤ Cj * (scale w) ^ Nj + 720 := by
    rw [norm_mul, hq]
    calc ‖jInvariantFun w - 720‖ * EExp w t 2 0
        ≤ (Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) + 720)
            * EExp w t 2 0 := mul_le_mul_of_nonneg_right hjw' (EExp_nonneg t 2 0)
      _ = Cj * (scale w) ^ Nj
            * (Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * EExp w t 2 0)
            + 720 * EExp w t 2 0 := by ring
      _ ≤ Cj * (scale w) ^ Nj * 1 + 720 * 1 := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hA (mul_nonneg hCj.le (E_rpow_nonneg w Nj))
          · exact mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = Cj * (scale w) ^ Nj + 720 := by ring
  rw [show Compact.Sinvref w z = 1 + (jInvariantFun w - 720) * (Ept z) ^ 2 from rfl]
  calc ‖1 + (jInvariantFun w - 720) * (Ept z) ^ 2‖
      ≤ 1 + ‖(jInvariantFun w - 720) * (Ept z) ^ 2‖ := by
        have h := norm_add_le (1 : ℂ) ((jInvariantFun w - 720) * (Ept z) ^ 2)
        simpa using h
    _ ≤ 1 + (Cj * (scale w) ^ Nj + 720) := add_le_add le_rfl hprod
    _ ≤ (1 + Cj + 720) * (scale w) ^ Nj := by
        have hs1 : (1:ℝ) ≤ (scale w) ^ Nj := E_one_le_rpow w hNj
        have hs0 : (0:ℝ) ≤ (scale w) ^ Nj := E_rpow_nonneg w Nj
        nlinarith [hs1, hs0, hCj.le]

lemma E_of_Bdd_neg2pi {F : ℍ → ℂ} (h : Bdd (-(2 * Real.pi)) F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖F w‖ ≤ C * (scale w) ^ N * EExp w t 0 (-2) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w z t hw ht hz => ?_⟩
  have h := hb w hw
  rw [show Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) = EExp w t 0 (-2) from by
    rw [EExp_zero_neg2]; congr 1; ring] at h
  exact h

lemma E_B24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.B24 ℓ w‖ ≤ C * (scale w) ^ N * EExp w t 0 (-2) := by
  apply E_of_Bdd_neg2pi
  refine Bdd.congr (funext fun w => ?_)
    (Bdd.add (Bdd.const_mul (-3456) E_bdd_Delta)
      (Bdd.const_mul (-2) (E_bdd_psi4E8_sub ℓ)))
  simp only [Compact.B24]; ring

lemma E_bdd_C24 (ℓ : LogLambdaData) : Bdd 0 (fun w => Compact.C24 ℓ w) := by
  refine Bdd.congr (funext fun w => ?_)
    (Bdd.add (Bdd.const_mul (-1) (E_bdd_j_psi_sub ℓ))
      (Bdd.const_mul 1728 (E_bdd_psi4E8 ℓ)))
  simp only [Compact.C24]; ring

lemma E_C24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.C24 ℓ w‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := E_bdd_C24 ℓ
  refine ⟨C, N, hC, hN, fun w z t hw ht hz => ?_⟩
  have h := hb w hw
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact h

lemma E_A24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.A24 ℓ w z‖ ≤ C * (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by
  obtain ⟨CΔ, NΔ, hCΔ, hNΔ, hΔ⟩ := E_of_Bdd_neg2pi E_bdd_Delta
  obtain ⟨CP, NP, hCP, hNP, hP⟩ := E_of_Bdd_neg2pi (E_bdd_psi4E8_sub ℓ)
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  obtain ⟨C14, hC14, h14⟩ := Funnel24.norm_E14_le
  obtain ⟨C10, hC10, h10⟩ := Funnel24.norm_E10_le
  set N : ℝ := max NΔ NP with hNdef
  set K : ℝ := 3456 * CΔ * C14 * Cz + CP * C10 * Cz with hKdef
  refine ⟨K, N, by rw [hKdef]; positivity, le_max_of_le_left hNΔ, fun w z t hw ht hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, hL, -, hD2, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have hz2 : (2:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hz]; linarith [two_im_S_le ht, hw.2]
  have hbΔ : ‖DeltaFun w‖ ≤ CΔ * (scale w) ^ N * EExp w t 0 (-2) :=
    le_trans (hΔ w z t hw ht hz) (EExp_mono_scale hCΔ.le (le_max_left _ _))
  have hbP : ‖psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w‖
      ≤ CP * (scale w) ^ N * EExp w t 0 (-2) := by
    rw [show psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w
        = -(psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w) from by ring, norm_neg]
    exact le_trans (hP w z t hw ht hz) (EExp_mono_scale hCP.le (le_max_right _ _))
  have hNn : (0:ℝ) ≤ (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by
    have h1t : (0:ℝ) ≤ 1 + t := le_trans zero_le_one (E_t_one_le hw ht)
    exact mul_nonneg (mul_nonneg (E_rpow_nonneg w N) h1t) (EExp_nonneg t 0 (-2))
  have hT1 : ‖(-3456 : ℂ) * DeltaFun w * E14Fun z * ℓ.L z‖
      ≤ 3456 * CΔ * C14 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by
    rw [norm_mul, norm_mul, norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    have h14' : ‖E14Fun z‖ ≤ C14 := h14 z hz2
    have hn1 : (0:ℝ) ≤ 3456 * (CΔ * (scale w) ^ N * EExp w t 0 (-2)) :=
      mul_nonneg (by norm_num) (EExp_shape_nonneg hCΔ.le)
    have hn2 : (0:ℝ) ≤ 3456 * (CΔ * (scale w) ^ N * EExp w t 0 (-2)) * C14 :=
      mul_nonneg hn1 hC14.le
    calc 3456 * ‖DeltaFun w‖ * ‖E14Fun z‖ * ‖ℓ.L z‖
        ≤ 3456 * (CΔ * (scale w) ^ N * EExp w t 0 (-2)) * C14 * (Cz * (1 + t)) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hbΔ (by norm_num)) h14'
            (norm_nonneg _) hn1) hL (norm_nonneg _) hn2
      _ = 3456 * CΔ * C14 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by ring
  have hT2 : ‖(psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w) * E10Fun z
        * (UFun z ^ 2 - VFun z ^ 2)‖
      ≤ CP * C10 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by
    rw [norm_mul, norm_mul]
    have h10' : ‖E10Fun z‖ ≤ C10 := h10 z hz2
    have hn1 : (0:ℝ) ≤ CP * (scale w) ^ N * EExp w t 0 (-2) := EExp_shape_nonneg hCP.le
    have hn2 : (0:ℝ) ≤ (CP * (scale w) ^ N * EExp w t 0 (-2)) * C10 := mul_nonneg hn1 hC10.le
    calc ‖psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w‖ * ‖E10Fun z‖
          * ‖UFun z ^ 2 - VFun z ^ 2‖
        ≤ (CP * (scale w) ^ N * EExp w t 0 (-2)) * C10 * Cz :=
          mul_le_mul (mul_le_mul hbP h10' (norm_nonneg _) hn1) hD2 (norm_nonneg _) hn2
      _ ≤ CP * C10 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2) := by
          have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
          have h0 : (0:ℝ) ≤ CP * C10 * Cz * (scale w) ^ N * EExp w t 0 (-2) :=
            EExp_shape_nonneg (mul_nonneg (mul_nonneg hCP.le hC10.le) hCz.le)
          nlinarith [h1t, h0]
  have hEq : Compact.A24 ℓ w z = -3456 * DeltaFun w * E14Fun z * ℓ.L z
      - (psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w) * E10Fun z
        * (UFun z ^ 2 - VFun z ^ 2) := rfl
  rw [hEq]
  refine le_trans (le_trans (norm_sub_le _ _) (add_le_add hT1 hT2)) ?_
  have hcomb : 3456 * CΔ * C14 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2)
      + CP * C10 * Cz * (scale w) ^ N * (1 + t) * EExp w t 0 (-2)
      = (3456 * CΔ * C14 * Cz + CP * C10 * Cz) * (scale w) ^ N * (1 + t)
        * EExp w t 0 (-2) := by ring
  rw [hcomb, hKdef]

/-! ## `Sh`, `Sinvref`, `dSinv` and the difference `A24 - A24ref` -/

lemma EExp_k_le {w : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    {k k' b b' : ℝ} (hk : k' ≤ k) (hb : b ≤ b') :
    EExp w t k b ≤ EExp w t k' b' := by
  unfold EExp
  have ht0 : 0 ≤ t := E_t_nonneg hw ht
  have hI : 0 ≤ (ModularGroup.S • w).im := E_im_S_nonneg hw
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have h : k' * Real.pi * t ≤ k * Real.pi * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk Real.pi_pos.le) ht0
    linarith
  · apply Real.exp_le_exp.mpr
    have h : b * Real.pi * (ModularGroup.S • w).im ≤ b' * Real.pi * (ModularGroup.S • w).im :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb Real.pi_pos.le) hI
    linarith

lemma Sh_Sw (w z : ℍ) : Compact.Sh (ModularGroup.S • w) z = Compact.Sh w z := by
  simp only [Compact.Sh, jInvariantFun_Ssmul]

lemma Sinvref_Sw (w z : ℍ) :
    Compact.Sinvref (ModularGroup.S • w) z = Compact.Sinvref w z := by
  simp only [Compact.Sinvref, jInvariantFun_Ssmul]

lemma E_Sh_ge {w z : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) : (1 / 16 : ℝ) ≤ ‖Compact.Sh w z‖ := by
  have hτ : Work.Asymptotics.Funnel (ModularGroup.S • w) := E_S_mem_Funnel hw
  have hτt : (ModularGroup.S • w).im + 1 ≤ t := by
    have h1 := two_im_S_le ht; linarith [h1, hw.2]
  rw [← Sh_Sw w z]
  exact Work.Asymptotics.funnel_Sh_ge (ModularGroup.S • w) z t hτ hτt hz

lemma E_Sh_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.Sh w z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.ShFunnelBound
  refine ⟨C, hC, fun w z t hw ht hz => ?_⟩
  rw [← Sh_Sw w z]
  exact hb (ModularGroup.S • w) z t (E_S_mem_Funnel hw)
    (by have h1 := two_im_S_le ht; linarith [h1, hw.2]) hz

lemma E_Sh_inv_bound {w z : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) : ‖(Compact.Sh w z)⁻¹‖ ≤ 16 := by
  have h := E_Sh_ge hw ht hz
  have hpos : 0 < ‖Compact.Sh w z‖ := lt_of_lt_of_le (by norm_num) h
  rw [norm_inv, inv_le_iff_one_le_mul₀ hpos]
  linarith

lemma E_ShSinvref_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh w z * Compact.Sinvref w z - 1‖ ≤ C * EExp w t 4 4 := by
  obtain ⟨Chm, hChm, hb⟩ := Funnel24Tail.ShSinvrefFunnelBound
  refine ⟨Chm, hChm, fun w z t hw ht hz => ?_⟩
  have hτ : Work.Asymptotics.Funnel (ModularGroup.S • w) := E_S_mem_Funnel hw
  have hτt : (ModularGroup.S • w).im + 1 ≤ t := by
    have h1 := two_im_S_le ht; linarith [h1, hw.2]
  have h := hb (ModularGroup.S • w) z t hτ hτt hz
  rw [show Compact.Sh (ModularGroup.S • w) z * Compact.Sinvref (ModularGroup.S • w) z - 1
      = Compact.Sh w z * Compact.Sinvref w z - 1 from by rw [Sh_Sw, Sinvref_Sw]] at h
  have heq : (‖Ept z‖ ^ 2 * (‖Ept (ModularGroup.S • w)‖ ^ 2)⁻¹) ^ 2 = EExp w t 4 4 := by
    have e1 : Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (-(Real.pi * (ModularGroup.S • w).im)) ^ 2
        = Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
        = Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
      rw [← Real.exp_neg]; congr 1; try ring
    have e4 : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Real.exp (-(2 * Real.pi * t) + 2 * Real.pi * (ModularGroup.S • w).im) :=
      (Real.exp_add _ _).symm
    have e5 : (Real.exp (-(2 * Real.pi * t) + 2 * Real.pi * (ModularGroup.S • w).im)) ^ 2
        = Real.exp (2 * (-(2 * Real.pi * t) + 2 * Real.pi * (ModularGroup.S • w).im)) :=
      (Real.exp_nat_mul _ 2).symm
    have e6 : Real.exp (2 * (-(2 * Real.pi * t) + 2 * Real.pi * (ModularGroup.S • w).im))
        = EExp w t 4 4 := by
      rw [EExp, ← Real.exp_add]; congr 1; try ring
    rw [Work.Asymptotics.kmfd_norm_Ept_of_contour hz, Work.Residues.norm_Ept]
    rw [e1, e2, e3, e4, e5, e6]
  rw [heq] at h
  exact h

lemma E_dSinv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I → ‖Compact.dSinv w z‖ ≤ C * EExp w t 4 4 := by
  obtain ⟨Chm, hChm, hb⟩ := E_ShSinvref_bound
  refine ⟨16 * Chm, by positivity, fun w z t hw ht hz => ?_⟩
  have hge := E_Sh_ge hw ht hz
  have hne : Compact.Sh w z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hge; norm_num at hge
  have hsplit : Compact.dSinv w z
      = (Compact.Sh w z)⁻¹ * (1 - Compact.Sh w z * Compact.Sinvref w z) := by
    show (Compact.Sh w z)⁻¹ - Compact.Sinvref w z = _
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hsplit, norm_mul]
  have h2 : ‖1 - Compact.Sh w z * Compact.Sinvref w z‖ ≤ Chm * EExp w t 4 4 := by
    rw [show (1 : ℂ) - Compact.Sh w z * Compact.Sinvref w z
        = -(Compact.Sh w z * Compact.Sinvref w z - 1) from by ring, norm_neg]
    exact hb w z t hw ht hz
  calc ‖(Compact.Sh w z)⁻¹‖ * ‖1 - Compact.Sh w z * Compact.Sinvref w z‖
      ≤ 16 * (Chm * EExp w t 4 4) :=
        mul_le_mul (E_Sh_inv_bound hw ht hz) h2 (norm_nonneg _) (by norm_num)
    _ = 16 * Chm * EExp w t 4 4 := by ring

lemma E_A24diff_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.A24 ℓ w z - Compact.A24ref ℓ w z‖
        ≤ C * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by
  obtain ⟨CΔ, NΔ, hCΔ, hNΔ, hΔ⟩ := E_of_Bdd_neg2pi E_bdd_Delta
  obtain ⟨CP, NP, hCP, hNP, hP⟩ := E_of_Bdd_neg2pi (E_bdd_psi4E8_sub ℓ)
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  set N : ℝ := max NΔ NP with hNdef
  set Kc : ℝ := 2 * Cz * Cz with hKc
  refine ⟨3456 * CΔ * Kc + CP * Kc + 1, N, by rw [hKc]; positivity, le_max_of_le_left hNΔ,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨-, -, hdD2, hdL, hdE14, hdE10, hL, -, hD2, hE10r, hE14r, -, -, -, -⟩ := hzv w z t hw ht hz
  have hz2 : (2:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hz]; linarith [two_im_S_le ht, hw.2]
  have h1t : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have h01t : (0:ℝ) ≤ 1 + t := by linarith
  have hdE14' : ‖E14Fun z - Compact.E14ref z‖ ≤ Cz * EExp w t 4 0 := hdE14
  have hdE10' : ‖E10Fun z - Compact.E10ref z‖ ≤ Cz * EExp w t 4 0 := hdE10
  have hdL' : ‖ℓ.L z - Compact.Lref ℓ z‖ ≤ Cz * EExp w t 3 0 := hdL
  have hdd' : ‖(UFun z ^ 2 - VFun z ^ 2) - Compact.D2ref z‖ ≤ Cz * EExp w t 3 0 := hdD2
  have hbΔ : ‖DeltaFun w‖ ≤ CΔ * (scale w) ^ N * EExp w t 0 (-2) :=
    le_trans (hΔ w z t hw ht hz) (EExp_mono_scale hCΔ.le (le_max_left _ _))
  have hbP : ‖psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w‖
      ≤ CP * (scale w) ^ N * EExp w t 0 (-2) := by
    rw [show psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w
        = -(psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w) from by ring, norm_neg]
    exact le_trans (hP w z t hw ht hz) (EExp_mono_scale hCP.le (le_max_right _ _))
  have hle43 : EExp w t 4 0 ≤ EExp w t 3 0 := EExp_k_le hw ht (by norm_num) (le_refl (0:ℝ))
  have hDL : ‖E14Fun z * ℓ.L z - Compact.E14ref z * Compact.Lref ℓ z‖
      ≤ Kc * (1 + t) * EExp w t 3 0 := by
    have hsplit : E14Fun z * ℓ.L z - Compact.E14ref z * Compact.Lref ℓ z
        = (E14Fun z - Compact.E14ref z) * ℓ.L z
          + Compact.E14ref z * (ℓ.L z - Compact.Lref ℓ z) := by ring
    rw [hsplit]
    have h1 : ‖(E14Fun z - Compact.E14ref z) * ℓ.L z‖ ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
      rw [norm_mul]
      calc ‖E14Fun z - Compact.E14ref z‖ * ‖ℓ.L z‖
          ≤ (Cz * EExp w t 4 0) * (Cz * (1 + t)) :=
            mul_le_mul hdE14' hL (norm_nonneg _) (mul_nonneg hCz.le (EExp_nonneg t 4 0))
        _ = Cz * Cz * (1 + t) * EExp w t 4 0 := by ring
        _ ≤ Cz * Cz * (1 + t) * EExp w t 3 0 :=
            mul_le_mul_of_nonneg_left hle43
              (mul_nonneg (mul_nonneg hCz.le hCz.le) h01t)
    have h2 : ‖Compact.E14ref z * (ℓ.L z - Compact.Lref ℓ z)‖
        ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
      rw [norm_mul]
      calc ‖Compact.E14ref z‖ * ‖ℓ.L z - Compact.Lref ℓ z‖
          ≤ Cz * (Cz * EExp w t 3 0) := mul_le_mul hE14r hdL' (norm_nonneg _) hCz.le
        _ = Cz * Cz * EExp w t 3 0 := by ring
        _ ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
            have h0 : (0:ℝ) ≤ Cz * Cz * EExp w t 3 0 :=
              mul_nonneg (mul_nonneg hCz.le hCz.le) (EExp_nonneg t 3 0)
            nlinarith [h1t, h0]
    have hsum : Cz * Cz * (1 + t) * EExp w t 3 0 + Cz * Cz * (1 + t) * EExp w t 3 0
        = Kc * (1 + t) * EExp w t 3 0 := by rw [hKc]; ring
    linarith [le_trans (norm_add_le _ _) (add_le_add h1 h2)]
  have hDD : ‖E10Fun z * (UFun z ^ 2 - VFun z ^ 2) - Compact.E10ref z * Compact.D2ref z‖
      ≤ Kc * (1 + t) * EExp w t 3 0 := by
    have hsplit : E10Fun z * (UFun z ^ 2 - VFun z ^ 2) - Compact.E10ref z * Compact.D2ref z
        = (E10Fun z - Compact.E10ref z) * (UFun z ^ 2 - VFun z ^ 2)
          + Compact.E10ref z * ((UFun z ^ 2 - VFun z ^ 2) - Compact.D2ref z) := by ring
    rw [hsplit]
    have h1 : ‖(E10Fun z - Compact.E10ref z) * (UFun z ^ 2 - VFun z ^ 2)‖
        ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
      rw [norm_mul]
      calc ‖E10Fun z - Compact.E10ref z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖
          ≤ (Cz * EExp w t 4 0) * Cz :=
            mul_le_mul hdE10' hD2 (norm_nonneg _) (mul_nonneg hCz.le (EExp_nonneg t 4 0))
        _ = Cz * Cz * EExp w t 4 0 := by ring
        _ ≤ Cz * Cz * EExp w t 3 0 := mul_le_mul_of_nonneg_left hle43 (mul_nonneg hCz.le hCz.le)
        _ ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
            have h0 : (0:ℝ) ≤ Cz * Cz * EExp w t 3 0 :=
              mul_nonneg (mul_nonneg hCz.le hCz.le) (EExp_nonneg t 3 0)
            nlinarith [h1t, h0]
    have h2 : ‖Compact.E10ref z * ((UFun z ^ 2 - VFun z ^ 2) - Compact.D2ref z)‖
        ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
      rw [norm_mul]
      calc ‖Compact.E10ref z‖ * ‖(UFun z ^ 2 - VFun z ^ 2) - Compact.D2ref z‖
          ≤ Cz * (Cz * EExp w t 3 0) := mul_le_mul hE10r hdd' (norm_nonneg _) hCz.le
        _ = Cz * Cz * EExp w t 3 0 := by ring
        _ ≤ Cz * Cz * (1 + t) * EExp w t 3 0 := by
            have h0 : (0:ℝ) ≤ Cz * Cz * EExp w t 3 0 :=
              mul_nonneg (mul_nonneg hCz.le hCz.le) (EExp_nonneg t 3 0)
            nlinarith [h1t, h0]
    have hsum : Cz * Cz * (1 + t) * EExp w t 3 0 + Cz * Cz * (1 + t) * EExp w t 3 0
        = Kc * (1 + t) * EExp w t 3 0 := by rw [hKc]; ring
    linarith [le_trans (norm_add_le _ _) (add_le_add h1 h2)]
  have hEq : Compact.A24 ℓ w z - Compact.A24ref ℓ w z
      = -3456 * DeltaFun w * (E14Fun z * ℓ.L z - Compact.E14ref z * Compact.Lref ℓ z)
        - (psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w)
          * (E10Fun z * (UFun z ^ 2 - VFun z ^ 2) - Compact.E10ref z * Compact.D2ref z) := by
    simp only [Compact.A24, Compact.A24ref]; ring
  rw [hEq]
  have hT1 : ‖(-3456 : ℂ) * DeltaFun w
        * (E14Fun z * ℓ.L z - Compact.E14ref z * Compact.Lref ℓ z)‖
      ≤ 3456 * CΔ * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by
    rw [norm_mul, norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    calc 3456 * ‖DeltaFun w‖
          * ‖E14Fun z * ℓ.L z - Compact.E14ref z * Compact.Lref ℓ z‖
        ≤ 3456 * (CΔ * (scale w) ^ N * EExp w t 0 (-2)) * (Kc * (1 + t) * EExp w t 3 0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbΔ (by norm_num)) hDL (norm_nonneg _)
            (mul_nonneg (by norm_num) (EExp_shape_nonneg hCΔ.le))
      _ = 3456 * CΔ * Kc * (scale w) ^ N * (1 + t) * (EExp w t 0 (-2) * EExp w t 3 0) := by ring
      _ = 3456 * CΔ * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by
          rw [EExp_mul, zero_add, add_zero]
  have hT2 : ‖(psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w)
        * (E10Fun z * (UFun z ^ 2 - VFun z ^ 2) - Compact.E10ref z * Compact.D2ref z)‖
      ≤ CP * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by
    rw [norm_mul]
    calc ‖psi2 ℓ w * E10Fun w - psi4 ℓ w * E8Fun w‖
          * ‖E10Fun z * (UFun z ^ 2 - VFun z ^ 2) - Compact.E10ref z * Compact.D2ref z‖
        ≤ (CP * (scale w) ^ N * EExp w t 0 (-2)) * (Kc * (1 + t) * EExp w t 3 0) :=
          mul_le_mul hbP hDD (norm_nonneg _) (EExp_shape_nonneg hCP.le)
      _ = CP * Kc * (scale w) ^ N * (1 + t) * (EExp w t 0 (-2) * EExp w t 3 0) := by ring
      _ = CP * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by
          rw [EExp_mul, zero_add, add_zero]
  refine le_trans (le_trans (norm_sub_le _ _) (add_le_add hT1 hT2)) ?_
  have hcomb : 3456 * CΔ * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2)
      + CP * Kc * (scale w) ^ N * (1 + t) * EExp w t 3 (-2)
      = (3456 * CΔ * Kc + CP * Kc) * (scale w) ^ N * (1 + t) * EExp w t 3 (-2) := by ring
  rw [hcomb]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) (E_rpow_nonneg w N)) h01t)
    (EExp_nonneg t 3 (-2))

/-! ## Closing the exponential and products -/

lemma EExp_le_neg {w : ℍ} {t k b : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hk : 1 ≤ k) (hb : b ≤ 0) : EExp w t k b ≤ Real.exp (-(Real.pi * t)) := by
  unfold EExp
  have hI : 0 ≤ (ModularGroup.S • w).im := E_im_S_nonneg hw
  have ht0 : 0 ≤ t := E_t_nonneg hw ht
  have h2 : Real.exp (b * Real.pi * (ModularGroup.S • w).im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hb Real.pi_pos.le) hI
  have h1 : Real.exp (-(k * Real.pi * t)) ≤ Real.exp (-(Real.pi * t)) := by
    apply Real.exp_le_exp.mpr
    have h : Real.pi * t * 1 ≤ Real.pi * t * k :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg Real.pi_pos.le ht0)
    linarith
  calc Real.exp (-(k * Real.pi * t)) * Real.exp (b * Real.pi * (ModularGroup.S • w).im)
      ≤ Real.exp (-(k * Real.pi * t)) * 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-(k * Real.pi * t)) := mul_one _
    _ ≤ Real.exp (-(Real.pi * t)) := h1

/-- Product of three `EExp`-shaped bounds. -/
lemma Ebnd3m {X Y Z : ℂ} {C1 C2 C3 N1 N2 N3 M1 M2 M3 k1 k2 k3 b1 b2 b3 : ℝ}
    {w : ℍ} {t : ℝ} (ht0 : (0:ℝ) < 1 + t)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hX : ‖X‖ ≤ C1 * (scale w) ^ N1 * (1 + t) ^ M1 * EExp w t k1 b1)
    (hY : ‖Y‖ ≤ C2 * (scale w) ^ N2 * (1 + t) ^ M2 * EExp w t k2 b2)
    (hZ : ‖Z‖ ≤ C3 * (scale w) ^ N3 * (1 + t) ^ M3 * EExp w t k3 b3) :
    ‖X * Y * Z‖ ≤ C1 * C2 * C3 * (scale w) ^ (N1 + N2 + N3) * (1 + t) ^ (M1 + M2 + M3)
      * EExp w t (k1 + k2 + k3) (b1 + b2 + b3) := by
  rw [norm_mul, norm_mul]
  have hX0 : (0:ℝ) ≤ C1 * (scale w) ^ N1 * (1 + t) ^ M1 * EExp w t k1 b1 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 (E_rpow_nonneg w N1)) (Real.rpow_nonneg ht0.le M1))
      (EExp_nonneg t k1 b1)
  have hY0 : (0:ℝ) ≤ C2 * (scale w) ^ N2 * (1 + t) ^ M2 * EExp w t k2 b2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC2 (E_rpow_nonneg w N2)) (Real.rpow_nonneg ht0.le M2))
      (EExp_nonneg t k2 b2)
  have hZ0 : (0:ℝ) ≤ C3 * (scale w) ^ N3 * (1 + t) ^ M3 * EExp w t k3 b3 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC3 (E_rpow_nonneg w N3)) (Real.rpow_nonneg ht0.le M3))
      (EExp_nonneg t k3 b3)
  refine le_trans (mul_le_mul (mul_le_mul hX hY (norm_nonneg _) hX0) hZ (norm_nonneg _)
    (mul_nonneg hX0 hY0)) (le_of_eq ?_)
  have htpos : (0:ℝ) < 1 + t := ht0
  rw [show C1 * (scale w) ^ N1 * (1 + t) ^ M1 * EExp w t k1 b1
        * (C2 * (scale w) ^ N2 * (1 + t) ^ M2 * EExp w t k2 b2)
        * (C3 * (scale w) ^ N3 * (1 + t) ^ M3 * EExp w t k3 b3)
      = C1 * C2 * C3 * ((scale w) ^ N1 * (scale w) ^ N2 * (scale w) ^ N3)
        * ((1 + t) ^ M1 * (1 + t) ^ M2 * (1 + t) ^ M3)
        * (EExp w t k1 b1 * EExp w t k2 b2 * EExp w t k3 b3) from by ring,
    show (scale w) ^ N1 * (scale w) ^ N2 * (scale w) ^ N3 = (scale w) ^ (N1 + N2 + N3) from by
      rw [← Real.rpow_add (scale_pos w), ← Real.rpow_add (scale_pos w)],
    show (1 + t) ^ M1 * (1 + t) ^ M2 * (1 + t) ^ M3 = (1 + t) ^ (M1 + M2 + M3) from by
      rw [← Real.rpow_add htpos, ← Real.rpow_add htpos],
    show EExp w t k1 b1 * EExp w t k2 b2 * EExp w t k3 b3
        = EExp w t (k1 + k2 + k3) (b1 + b2 + b3) from by rw [EExp_mul, EExp_mul]]


/-! ## The seven deviation terms -/

lemma E_Dev1_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev1 ℓ w z) := by
  obtain ⟨Cs, Ns, hCs, hNs, hs⟩ := E_Sinvref_bound ℓ
  obtain ⟨Ca, Na, hCa, hNa, ha⟩ := E_A24diff_bound ℓ
  refine ⟨Cs * 25 * Ca, Ns + 0 + Na, 0 + 0 + 1, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hz1 : (1:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hz]; linarith [two_im_S_le ht, hw.2]
  have hq : ‖Compact.Sinvref w z‖ ≤ Cs * (scale w) ^ Ns * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using hs w z t hw ht hz
  have hr : ‖Compact.Dref z‖ ≤ 25 * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
    have h := Funnel24.norm_Dref_le (z := z) hz1
    rw [Ept_sq_inv_EExp hz w] at h
    have h1 : (1:ℝ) ≤ EExp w t (-2) 0 := by
      rw [EExp_nat, show -((-2) * Real.pi * t) = 2 * (Real.pi * t) by ring]
      exact Real.one_le_exp (mul_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le (E_t_nonneg hw ht)))
    calc ‖Compact.Dref z‖ ≤ EExp w t (-2) 0 + 24 := h
      _ ≤ 25 * EExp w t (-2) 0 := by linarith
      _ = 25 * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
          rw [Real.rpow_zero, Real.rpow_zero]; ring
  have hz2 : ‖Compact.A24 ℓ w z - Compact.A24ref ℓ w z‖
      ≤ Ca * (scale w) ^ Na * (1 + t) ^ (1:ℝ) * EExp w t 3 (-2) := by
    rw [Real.rpow_one]; exact ha w z t hw ht hz
  change ‖Compact.Dev1 ℓ w z‖ ≤ Cs * 25 * Ca * (scale w) ^ (Ns + 0 + Na)
    * (1 + t) ^ (0 + 0 + 1) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev1 ℓ w z
      = Compact.Sinvref w z * Compact.Dref z * (Compact.A24 ℓ w z - Compact.A24ref ℓ w z)
      from rfl]
  refine le_trans (Ebnd3m ht0 hCs.le (by norm_num) hCa.le hq hr hz2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le_neg hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs.le (by norm_num)) hCa.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dev2_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev2 ℓ w z) := by
  obtain ⟨Cs, Ns, hCs, hNs, hs⟩ := E_Sinvref_bound ℓ
  obtain ⟨Ca, Na, hCa, hNa, ha⟩ := E_A24_bound ℓ
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  refine ⟨Cs * Cz * Ca, Ns + 0 + Na, 0 + 0 + 1, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hdd := (hzv w z t hw ht hz).1
  have hq : ‖Compact.Sinvref w z‖ ≤ Cs * (scale w) ^ Ns * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using hs w z t hw ht hz
  have hr : ‖Compact.dDelta z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 2 0 := by
    rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]; exact hdd
  have hz2 : ‖Compact.A24 ℓ w z‖ ≤ Ca * (scale w) ^ Na * (1 + t) ^ (1:ℝ) * EExp w t 0 (-2) := by
    rw [Real.rpow_one]; exact ha w z t hw ht hz
  change ‖Compact.Dev2 ℓ w z‖ ≤ Cs * Cz * Ca * (scale w) ^ (Ns + 0 + Na)
    * (1 + t) ^ (0 + 0 + 1) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev2 ℓ w z = Compact.Sinvref w z * Compact.dDelta z * Compact.A24 ℓ w z
      from rfl]
  refine le_trans (Ebnd3m ht0 hCs.le hCz.le hCa.le hq hr hz2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le_neg hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs.le hCz.le) hCa.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dref_bound {w z : ℍ} {t : ℝ} (hw : w ∈ KEpsilon) (ht : Ethresh w t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Compact.Dref z‖ ≤ 25 * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
  have hz1 : (1:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hz]; linarith [two_im_S_le ht, hw.2]
  have h := Funnel24.norm_Dref_le (z := z) hz1
  rw [Ept_sq_inv_EExp hz w] at h
  have h1 : (1:ℝ) ≤ EExp w t (-2) 0 := by
    rw [EExp_nat, show -((-2) * Real.pi * t) = 2 * (Real.pi * t) by ring]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le (E_t_nonneg hw ht)))
  calc ‖Compact.Dref z‖ ≤ EExp w t (-2) 0 + 24 := h
    _ ≤ 25 * EExp w t (-2) 0 := by linarith
    _ = 25 * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
        rw [Real.rpow_zero, Real.rpow_zero]; ring

lemma E_invDelta_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w z : ℍ) (t : ℝ), w ∈ KEpsilon → Ethresh w t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖(DeltaFun z)⁻¹‖ ≤ (1 + K) * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
  obtain ⟨K, hK, hKb⟩ := Funnel24.norm_invDelta_bound
  refine ⟨K, hK, fun w z t hw ht hz => ?_⟩
  have hz1 : (1:ℝ) ≤ z.im := by
    rw [Work.Asymptotics.kmfd_im_of_contour hz]; linarith [two_im_S_le ht, hw.2]
  have h := hKb z hz1
  rw [Ept_sq_inv_EExp hz w] at h
  have h1 : (1:ℝ) ≤ EExp w t (-2) 0 := by
    rw [EExp_nat, show -((-2) * Real.pi * t) = 2 * (Real.pi * t) by ring]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le (E_t_nonneg hw ht)))
  calc ‖(DeltaFun z)⁻¹‖ ≤ EExp w t (-2) 0 + K := h
    _ ≤ (1 + K) * EExp w t (-2) 0 := by
        have h2 : K ≤ K * EExp w t (-2) 0 := le_mul_of_one_le_right hK h1
        linarith
    _ = (1 + K) * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 := by
        rw [Real.rpow_zero, Real.rpow_zero]; ring

lemma E_Dev3_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev3 ℓ w z) := by
  obtain ⟨Cd, hCd, hd⟩ := E_dSinv_bound
  obtain ⟨Ca, Na, hCa, hNa, ha⟩ := E_A24_bound ℓ
  obtain ⟨K, hK, hKb⟩ := E_invDelta_bound
  refine ⟨Cd * (1 + K) * Ca, 0 + 0 + Na, 0 + 0 + 1, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hq : ‖Compact.dSinv w z‖ ≤ Cd * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 4 4 := by
    simpa only [Real.rpow_zero, mul_one] using hd w z t hw ht hz
  have hr : ‖(DeltaFun z)⁻¹‖ ≤ (1 + K) * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 :=
    hKb w z t hw ht hz
  have hs : ‖Compact.A24 ℓ w z‖ ≤ Ca * (scale w) ^ Na * (1 + t) ^ (1:ℝ) * EExp w t 0 (-2) := by
    rw [Real.rpow_one]; exact ha w z t hw ht hz
  change ‖Compact.Dev3 ℓ w z‖ ≤ Cd * (1 + K) * Ca * (scale w) ^ (0 + 0 + Na)
    * (1 + t) ^ (0 + 0 + 1) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev3 ℓ w z = Compact.dSinv w z * (DeltaFun z)⁻¹ * Compact.A24 ℓ w z
      from rfl]
  refine le_trans (Ebnd3m ht0 hCd.le (by positivity) hCa.le hq hr hs) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd.le (by positivity)) hCa.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dev4_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev4 ℓ w z) := by
  obtain ⟨Cs, Ns, hCs, hNs, hs⟩ := E_Sinvref_bound ℓ
  obtain ⟨CC, NC, hCC, hNC, hC⟩ := E_C24_bound ℓ
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  refine ⟨Cs * CC * Cz, Ns + NC + 0, 0 + 0 + 0, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨-, hdW, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hq : ‖Compact.Sinvref w z‖ ≤ Cs * (scale w) ^ Ns * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using hs w z t hw ht hz
  have hr : ‖Compact.C24 ℓ w‖ ≤ CC * (scale w) ^ NC * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    have h := hC w z t hw ht hz
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using h
  have hs2 : ‖Compact.dW z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 3 0 := by
    simpa only [Real.rpow_zero, mul_one] using hdW
  change ‖Compact.Dev4 ℓ w z‖ ≤ Cs * CC * Cz * (scale w) ^ (Ns + NC + 0)
    * (1 + t) ^ (0 + 0 + 0) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev4 ℓ w z = Compact.Sinvref w z * Compact.C24 ℓ w * Compact.dW z from rfl]
  refine le_trans (Ebnd3m ht0 hCs.le hCC.le hCz.le hq hr hs2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs.le hCC.le) hCz.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dev5_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev5 ℓ w z) := by
  obtain ⟨Cd, hCd, hd⟩ := E_dSinv_bound
  obtain ⟨CC, NC, hCC, hNC, hC⟩ := E_C24_bound ℓ
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  refine ⟨Cd * CC * Cz, 0 + NC + 0, 0 + 0 + 0, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hW, -, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hq : ‖Compact.dSinv w z‖ ≤ Cd * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 4 4 := by
    simpa only [Real.rpow_zero, mul_one] using hd w z t hw ht hz
  have hr : ‖Compact.C24 ℓ w‖ ≤ CC * (scale w) ^ NC * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    have h := hC w z t hw ht hz
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using h
  have hs2 : ‖WFun z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using hW
  change ‖Compact.Dev5 ℓ w z‖ ≤ Cd * CC * Cz * (scale w) ^ (0 + NC + 0)
    * (1 + t) ^ (0 + 0 + 0) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev5 ℓ w z = Compact.dSinv w z * Compact.C24 ℓ w * WFun z from rfl]
  refine le_trans (Ebnd3m ht0 hCd.le hCC.le hCz.le hq hr hs2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd.le hCC.le) hCz.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dev6_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev6 ℓ w z) := by
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  obtain ⟨CB, NB, hCB, hNB, hB⟩ := E_B24_bound ℓ
  refine ⟨25 * Cz * CB, 0 + 0 + NB, 0 + 0 + 0, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨-, hdW, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hdr : ‖Compact.Dref z‖ ≤ 25 * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t (-2) 0 :=
    E_Dref_bound hw ht hz
  have hr : ‖Compact.dW z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 3 0 := by
    simpa only [Real.rpow_zero, mul_one] using hdW
  have hs2 : ‖Compact.B24 ℓ w‖ ≤ CB * (scale w) ^ NB * (1 + t) ^ (0:ℝ) * EExp w t 0 (-2) := by
    simpa only [Real.rpow_zero, mul_one] using hB w z t hw ht hz
  change ‖Compact.Dev6 ℓ w z‖ ≤ 25 * Cz * CB * (scale w) ^ (0 + 0 + NB)
    * (1 + t) ^ (0 + 0 + 0) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev6 ℓ w z = -(Compact.Dref z * Compact.dW z * Compact.B24 ℓ w) from by
    simp only [Compact.Dev6]; ring, norm_neg]
  refine le_trans (Ebnd3m ht0 (by norm_num) hCz.le hCB.le hdr hr hs2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le_neg hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCz.le) hCB.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

lemma E_Dev7_bound (ℓ : LogLambdaData) : EBnd (fun w z => Compact.Dev7 ℓ w z) := by
  obtain ⟨Cz, hCz, hzv⟩ := E_zdevs ℓ
  obtain ⟨CB, NB, hCB, hNB, hB⟩ := E_B24_bound ℓ
  refine ⟨Cz * Cz * CB, 0 + 0 + NB, 0 + 0 + 0, by positivity, by linarith, by norm_num,
    fun w z t hw ht hz => ?_⟩
  obtain ⟨hdd, -, -, -, -, -, -, hW, -, -, -, -, -, -, -⟩ := hzv w z t hw ht hz
  have ht0 : (0:ℝ) < 1 + t := by linarith [E_t_one_le hw ht]
  have hdr : ‖Compact.dDelta z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 2 0 := by
    simpa only [Real.rpow_zero, mul_one] using hdd
  have hr : ‖WFun z‖ ≤ Cz * (scale w) ^ (0:ℝ) * (1 + t) ^ (0:ℝ) * EExp w t 0 0 := by
    simpa only [Real.rpow_zero, mul_one, EExp_zero_zero] using hW
  have hs2 : ‖Compact.B24 ℓ w‖ ≤ CB * (scale w) ^ NB * (1 + t) ^ (0:ℝ) * EExp w t 0 (-2) := by
    simpa only [Real.rpow_zero, mul_one] using hB w z t hw ht hz
  change ‖Compact.Dev7 ℓ w z‖ ≤ Cz * Cz * CB * (scale w) ^ (0 + 0 + NB)
    * (1 + t) ^ (0 + 0 + 0) * Real.exp (-(Real.pi * t))
  rw [show Compact.Dev7 ℓ w z = -(Compact.dDelta z * WFun z * Compact.B24 ℓ w) from by
    simp only [Compact.Dev7]; ring, norm_neg]
  refine le_trans (Ebnd3m ht0 hCz.le hCz.le hCB.le hdr hr hs2) ?_
  refine mul_le_mul_of_nonneg_left (EExp_le_neg hw ht (by norm_num) (by norm_num)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCz.le hCz.le) hCB.le)
    (E_rpow_nonneg w _)) (Real.rpow_nonneg ht0.le _)

theorem EtailE_KMinus24 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        Work.Asymptotics.EtailE.Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KMinus ℓ 24 w z - Work.Asymptotics.Compact.Gminus 24 ℓ w z‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨CT, NT, MT, hCT, hNT, hMT, hTref⟩ := E_Tref24_bound ℓ
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hB1⟩ := E_Dev1_bound ℓ
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hB2⟩ := E_Dev2_bound ℓ
  obtain ⟨C3, N3, M3, hC3, hN3, hM3, hB3⟩ := E_Dev3_bound ℓ
  obtain ⟨C4, N4, M4, hC4, hN4, hM4, hB4⟩ := E_Dev4_bound ℓ
  obtain ⟨C5, N5, M5, hC5, hN5, hM5, hB5⟩ := E_Dev5_bound ℓ
  obtain ⟨C6, N6, M6, hC6, hN6, hM6, hB6⟩ := E_Dev6_bound ℓ
  obtain ⟨C7, N7, M7, hC7, hN7, hM7, hB7⟩ := E_Dev7_bound ℓ
  obtain ⟨CSh, hCSh, hShb⟩ := E_Sh_bound
  set Cs : ℝ := C1 + (C2 + (C3 + (C4 + (C5 + (C6 + C7))))) with hCsdef
  set C : ℝ := CSh * (CT + Cs) + 1 with hCdef
  set N : ℝ := NT + (N1 + (N2 + (N3 + (N4 + (N5 + (N6 + N7)))))) + 1 with hNdef
  set M : ℝ := MT + (M1 + (M2 + (M3 + (M4 + (M5 + (M6 + M7)))))) + 1 with hMdef
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]; linarith [hC1.le, hC2.le, hC3.le, hC4.le, hC5.le, hC6.le, hC7.le]
  have hN0 : 0 ≤ N := by
    rw [hNdef]; linarith [hNT, hN1, hN2, hN3, hN4, hN5, hN6, hN7]
  have hM0 : 0 ≤ M := by
    rw [hMdef]; linarith [hMT, hM1, hM2, hM3, hM4, hM5, hM6, hM7]
  refine ⟨(3456 * Real.pi)⁻¹ * 16 * C, N, M, by positivity, hN0, hM0,
    fun w z t hw ht hz => ?_⟩
  have ht1 : (1:ℝ) ≤ 1 + t := E_t_one_le hw ht
  have hTlen : NT ≤ N := by rw [hNdef]; linarith [hN1, hN2, hN3, hN4, hN5, hN6, hN7]
  have hN1len : N1 ≤ N := by rw [hNdef]; linarith [hNT, hN2, hN3, hN4, hN5, hN6, hN7]
  have hN2len : N2 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN3, hN4, hN5, hN6, hN7]
  have hN3len : N3 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN2, hN4, hN5, hN6, hN7]
  have hN4len : N4 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN2, hN3, hN5, hN6, hN7]
  have hN5len : N5 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN2, hN3, hN4, hN6, hN7]
  have hN6len : N6 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN2, hN3, hN4, hN5, hN7]
  have hN7len : N7 ≤ N := by rw [hNdef]; linarith [hNT, hN1, hN2, hN3, hN4, hN5, hN6]
  have hTlenM : MT ≤ M := by rw [hMdef]; linarith [hM1, hM2, hM3, hM4, hM5, hM6, hM7]
  have hM1len : M1 ≤ M := by rw [hMdef]; linarith [hMT, hM2, hM3, hM4, hM5, hM6, hM7]
  have hM2len : M2 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM3, hM4, hM5, hM6, hM7]
  have hM3len : M3 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM2, hM4, hM5, hM6, hM7]
  have hM4len : M4 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM2, hM3, hM5, hM6, hM7]
  have hM5len : M5 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM2, hM3, hM4, hM6, hM7]
  have hM6len : M6 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM2, hM3, hM4, hM5, hM7]
  have hM7len : M7 ≤ M := by rw [hMdef]; linarith [hMT, hM1, hM2, hM3, hM4, hM5, hM6]
  have hT : ‖Compact.Tref24 ℓ w z‖ ≤ CT * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Tref24 ℓ x z) (le_refl CT) hTlen hTlenM hCT.le ht1
      (hTref w z t hw ht hz)
  have hD1 : ‖Compact.Dev1 ℓ w z‖ ≤ C1 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev1 ℓ x z) (le_refl C1) hN1len hM1len hC1.le ht1
      (hB1 w z t hw ht hz)
  have hD2 : ‖Compact.Dev2 ℓ w z‖ ≤ C2 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev2 ℓ x z) (le_refl C2) hN2len hM2len hC2.le ht1
      (hB2 w z t hw ht hz)
  have hD3 : ‖Compact.Dev3 ℓ w z‖ ≤ C3 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev3 ℓ x z) (le_refl C3) hN3len hM3len hC3.le ht1
      (hB3 w z t hw ht hz)
  have hD4 : ‖Compact.Dev4 ℓ w z‖ ≤ C4 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev4 ℓ x z) (le_refl C4) hN4len hM4len hC4.le ht1
      (hB4 w z t hw ht hz)
  have hD5 : ‖Compact.Dev5 ℓ w z‖ ≤ C5 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev5 ℓ x z) (le_refl C5) hN5len hM5len hC5.le ht1
      (hB5 w z t hw ht hz)
  have hD6 : ‖Compact.Dev6 ℓ w z‖ ≤ C6 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev6 ℓ x z) (le_refl C6) hN6len hM6len hC6.le ht1
      (hB6 w z t hw ht hz)
  have hD7 : ‖Compact.Dev7 ℓ w z‖ ≤ C7 * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
    inflate_E (F := fun x => Compact.Dev7 ℓ x z) (le_refl C7) hN7len hM7len hC7.le ht1
      (hB7 w z t hw ht hz)
  set X : ℝ := (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (E_rpow_nonneg w N)
      (Real.rpow_nonneg (le_trans zero_le_one ht1) M)) (Real.exp_pos _).le
  have hreas : ∀ c : ℝ, c * X = c * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
    intro c; rw [hXdef]; ring
  have hT' : ‖Compact.Tref24 ℓ w z‖ ≤ CT * X := by rw [hreas CT]; exact hT
  have hD1' : ‖Compact.Dev1 ℓ w z‖ ≤ C1 * X := by rw [hreas C1]; exact hD1
  have hD2' : ‖Compact.Dev2 ℓ w z‖ ≤ C2 * X := by rw [hreas C2]; exact hD2
  have hD3' : ‖Compact.Dev3 ℓ w z‖ ≤ C3 * X := by rw [hreas C3]; exact hD3
  have hD4' : ‖Compact.Dev4 ℓ w z‖ ≤ C4 * X := by rw [hreas C4]; exact hD4
  have hD5' : ‖Compact.Dev5 ℓ w z‖ ≤ C5 * X := by rw [hreas C5]; exact hD5
  have hD6' : ‖Compact.Dev6 ℓ w z‖ ≤ C6 * X := by rw [hreas C6]; exact hD6
  have hD7' : ‖Compact.Dev7 ℓ w z‖ ≤ C7 * X := by rw [hreas C7]; exact hD7
  have hDsum : ‖Compact.Dev24Sum ℓ w z‖ ≤ Cs * X := by
    rw [show Compact.Dev24Sum ℓ w z = Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z
        + Compact.Dev3 ℓ w z + Compact.Dev4 ℓ w z + Compact.Dev5 ℓ w z
        + Compact.Dev6 ℓ w z + Compact.Dev7 ℓ w z from rfl]
    have a1 := norm_add_le (Compact.Dev1 ℓ w z) (Compact.Dev2 ℓ w z)
    have a2 := norm_add_le (Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z) (Compact.Dev3 ℓ w z)
    have a3 := norm_add_le (Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z + Compact.Dev3 ℓ w z)
      (Compact.Dev4 ℓ w z)
    have a4 := norm_add_le (Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z + Compact.Dev3 ℓ w z
      + Compact.Dev4 ℓ w z) (Compact.Dev5 ℓ w z)
    have a5 := norm_add_le (Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z + Compact.Dev3 ℓ w z
      + Compact.Dev4 ℓ w z + Compact.Dev5 ℓ w z) (Compact.Dev6 ℓ w z)
    have a6 := norm_add_le (Compact.Dev1 ℓ w z + Compact.Dev2 ℓ w z + Compact.Dev3 ℓ w z
      + Compact.Dev4 ℓ w z + Compact.Dev5 ℓ w z + Compact.Dev6 ℓ w z) (Compact.Dev7 ℓ w z)
    have hcomb : C1 * X + C2 * X + C3 * X + C4 * X + C5 * X + C6 * X + C7 * X = Cs * X := by
      rw [hCsdef]; ring
    linarith [a1, a2, a3, a4, a5, a6, hD1', hD2', hD3', hD4', hD5', hD6', hD7', hcomb]
  have hTR : ‖Compact.Tref24 ℓ w z + Compact.Dev24Sum ℓ w z‖ ≤ (CT + Cs) * X := by
    have h := norm_add_le (Compact.Tref24 ℓ w z) (Compact.Dev24Sum ℓ w z)
    have hcomb : CT * X + Cs * X = (CT + Cs) * X := by ring
    linarith [h, hT', hDsum, hcomb]
  have hshge := E_Sh_ge hw ht hz
  have hshne : Compact.Sh w z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hshge; norm_num at hshge
  have hdec := Compact.decomp24_sum ℓ w z hshne
  have hQ : Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z
      = Compact.Sh w z * (Compact.Tref24 ℓ w z + Compact.Dev24Sum ℓ w z) := by
    have h2 : Compact.Sh w z * ((Compact.Sh w z)⁻¹
        * (Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z))
        = Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z := by
      rw [← mul_assoc, mul_inv_cancel₀ hshne, one_mul]
    rw [← h2, hdec]
  have hQb : ‖Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z‖
      ≤ CSh * (CT + Cs) * X := by
    rw [hQ, norm_mul]
    have h1 : ‖Compact.Sh w z‖ ≤ CSh := hShb w z t hw ht hz
    have h2 : ‖Compact.Tref24 ℓ w z + Compact.Dev24Sum ℓ w z‖ ≤ (CT + Cs) * X := hTR
    have h3 : (0:ℝ) ≤ (CT + Cs) * X := mul_nonneg (by linarith [hCT.le, hCs0]) hX0
    exact le_trans (mul_le_mul h1 h2 (norm_nonneg _) hCSh.le) (le_of_eq (by ring))
  have htail := Compact.tail_identity ℓ 24 (Or.inr rfl) w z hshne
  have hnorm : ((3456 : ℝ) * Real.pi)
      * ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
      = ‖(Compact.Sh w z)⁻¹
          * (Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z)‖ := by
    have h2 : ‖((3456 : ℂ) * (Real.pi : ℂ))
        * (Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z)‖
        = ((3456 : ℝ) * Real.pi) * ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖ := by
      rw [norm_mul, norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      try ring
    calc ((3456 : ℝ) * Real.pi)
          * ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
        = ‖((3456 : ℂ) * (Real.pi : ℂ))
            * (Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z)‖ := h2.symm
      _ = ‖-((Compact.Sh w z)⁻¹
            * (Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z))‖ := by
          rw [htail]
      _ = ‖(Compact.Sh w z)⁻¹
            * (Compact.brMinus ℓ 24 w z + Compact.Sh w z * Compact.br0 24 ℓ w z)‖ := by
          rw [norm_neg]
  have hstep : ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
      ≤ (3456 * Real.pi)⁻¹ * (16 * (CSh * (CT + Cs) * X)) := by
    have hmult : ((3456 : ℝ) * Real.pi)
        * ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
        ≤ 16 * (CSh * (CT + Cs) * X) := by
      rw [hnorm]
      exact le_trans (le_trans (norm_mul_le _ _) (mul_le_mul (E_Sh_inv_bound hw ht hz) (le_refl _)
        (norm_nonneg _) (by norm_num))) (mul_le_mul_of_nonneg_left hQb (by norm_num))
    calc ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
        = (3456 * Real.pi)⁻¹ * (((3456 : ℝ) * Real.pi)
            * ‖Work.Kernels.KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (3456 * Real.pi) ≠ 0), one_mul]
      _ ≤ (3456 * Real.pi)⁻¹ * (16 * (CSh * (CT + Cs) * X)) :=
          mul_le_mul_of_nonneg_left hmult (by positivity)
  have hCX : CSh * (CT + Cs) ≤ C := by rw [hCdef]; linarith
  have hmain : (3456 * Real.pi)⁻¹ * (16 * (CSh * (CT + Cs) * X))
      ≤ (3456 * Real.pi)⁻¹ * 16 * C * X := by
    have h1 : CSh * (CT + Cs) * X ≤ C * X := mul_le_mul_of_nonneg_right hCX hX0
    have h2 : 16 * (CSh * (CT + Cs) * X) ≤ 16 * (C * X) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (3456 * Real.pi)⁻¹)
    calc (3456 * Real.pi)⁻¹ * (16 * (CSh * (CT + Cs) * X))
        ≤ (3456 * Real.pi)⁻¹ * (16 * (C * X)) := h3
      _ = (3456 * Real.pi)⁻¹ * 16 * C * X := by ring
  have hgoal : (3456 * Real.pi)⁻¹ * 16 * C * X
      = (3456 * Real.pi)⁻¹ * 16 * C * (scale w) ^ N * (1 + t) ^ M
        * Real.exp (-(Real.pi * t)) := by
    rw [hXdef]; ring
  rw [← hgoal]
  exact le_trans hstep hmain
end Work.Asymptotics.EtailE
