import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.CuspL_eq

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

private lemma norm_Utail (e : ℂ) {ρ : ℝ} (he : ‖e‖ = ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖1 + 8*e + 24*e^2 + 32*e^3 + 24*e^4‖ ≤ 89 := by
  have h1 : ‖(8:ℂ)*e‖ = 8*ρ := by rw [norm_mul, Complex.norm_ofNat, he]
  have h2 : ‖(24:ℂ)*e^2‖ = 24*ρ^2 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have h3 : ‖(32:ℂ)*e^3‖ = 32*ρ^3 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have h4 : ‖(24:ℂ)*e^4‖ = 24*ρ^4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have d := norm_add_le (1:ℂ) ((8:ℂ)*e)
  have c := norm_add_le ((1:ℂ) + 8*e) ((24:ℂ)*e^2)
  have b := norm_add_le ((1:ℂ) + 8*e + 24*e^2) ((32:ℂ)*e^3)
  have a := norm_add_le ((1:ℂ) + 8*e + 24*e^2 + 32*e^3) ((24:ℂ)*e^4)
  rw [norm_one, h1] at d
  rw [h2] at c
  rw [h3] at b
  rw [h4] at a
  have hp2 : ρ^2 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 2)
  have hp3 : ρ^3 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 3)
  have hp4 : ρ^4 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 4)
  nlinarith [a, b, c, d, hp2, hp3, hp4, hρ0, hρ1]

private lemma norm_Vtail (e : ℂ) {ρ : ℝ} (he : ‖e‖ = ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖16*e + 64*e^3‖ ≤ 80 := by
  have h1 : ‖(16:ℂ)*e‖ = 16*ρ := by rw [norm_mul, Complex.norm_ofNat, he]
  have h3 : ‖(64:ℂ)*e^3‖ = 64*ρ^3 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have a := norm_add_le ((16:ℂ)*e) ((64:ℂ)*e^3)
  rw [h1, h3] at a
  have hp3 : ρ^3 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 3)
  nlinarith [a, hp3, hρ0]

private lemma norm_polytail (e : ℂ) {ρ : ℝ} (he : ‖e‖ = ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖e^5 * (1920 - 1920*e + 1536*e^2 + 576*e^3)‖ ≤ 5952 * ρ^5 := by
  have h1 : ‖(1920:ℂ)*e‖ = 1920*ρ := by rw [norm_mul, Complex.norm_ofNat, he]
  have h2 : ‖(1536:ℂ)*e^2‖ = 1536*ρ^2 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have h3 : ‖(576:ℂ)*e^3‖ = 576*ρ^3 := by rw [norm_mul, Complex.norm_ofNat, norm_pow, he]
  have h0 : ‖(1920:ℂ)‖ = 1920 := by norm_num
  have a := norm_add_le ((1920:ℂ) - 1920*e + 1536*e^2) ((576:ℂ)*e^3)
  have b := norm_add_le ((1920:ℂ) - 1920*e) ((1536:ℂ)*e^2)
  have c := norm_sub_le (1920:ℂ) (1920*e)
  rw [h0, h1] at c
  rw [h2] at b
  rw [h3] at a
  have hp2 : ρ^2 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 2)
  have hp3 : ρ^3 ≤ 1 := pow_le_one₀ hρ0 hρ1 (n := 3)
  have hp5 : 0 ≤ ρ^5 := by positivity
  have hnorm : ‖(1920:ℂ) - 1920*e + 1536*e^2 + 576*e^3‖
      ≤ 1920 + 1920*ρ + 1536*ρ^2 + 576*ρ^3 := by
    nlinarith [a, b, c, hρ0]
  rw [norm_mul, norm_pow, he]
  calc ρ^5 * ‖(1920:ℂ) - 1920*e + 1536*e^2 + 576*e^3‖
      ≤ ρ^5 * (1920 + 1920*ρ + 1536*ρ^2 + 576*ρ^3) :=
        mul_le_mul_of_nonneg_left hnorm hp5
    _ ≤ ρ^5 * 5952 := by
        apply mul_le_mul_of_nonneg_left _ hp5
        nlinarith [hρ0, hρ1, hp2, hp3]
    _ = 5952 * ρ^5 := by ring

private lemma dD2_aux {u v e : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (he : ‖e‖ = ρ)
    (hU : ‖u - (1 + 8*e + 24*e^2 + 32*e^3 + 24*e^4)‖ ≤ 10000 * ρ^5)
    (hV : ‖v - (16*e + 64*e^3)‖ ≤ 10000 * ρ^5) :
    ‖u^2 - v^2 - (1 + 16*e - 144*e^2 + 448*e^3 - 912*e^4)‖ ≤ 300000000 * ρ^5 := by
  set P : ℂ := 1 + 8*e + 24*e^2 + 32*e^3 + 24*e^4 with hP
  set Q : ℂ := 16*e + 64*e^3 with hQ
  set T : ℂ := 1 + 16*e - 144*e^2 + 448*e^3 - 912*e^4 with hT
  set A : ℂ := u - P with hA
  set B : ℂ := v - Q with hB
  have hAρ : ‖A‖ ≤ 10000 * ρ^5 := by rw [hA, hP]; exact hU
  have hBρ : ‖B‖ ≤ 10000 * ρ^5 := by rw [hB, hQ]; exact hV
  have hu : u = P + A := by rw [hA]; ring
  have hv : v = Q + B := by rw [hB]; ring
  have hkey : u^2 - v^2 - T = (P^2 - Q^2 - T) + (2*P*A + A^2) - (2*Q*B + B^2) := by
    rw [hu, hv]; ring
  have hpoly : P^2 - Q^2 - T = e^5 * (1920 - 1920*e + 1536*e^2 + 576*e^3) := by
    rw [hP, hQ, hT]; ring
  have hPn : ‖P‖ ≤ 89 := by rw [hP]; exact norm_Utail e he hρ0 hρ1
  have hQn : ‖Q‖ ≤ 80 := by rw [hQ]; exact norm_Vtail e he hρ0 hρ1
  have hpt : ‖P^2 - Q^2 - T‖ ≤ 5952 * ρ^5 := by
    rw [hpoly]; exact norm_polytail e he hρ0 hρ1
  have hT1 : ‖(2:ℂ)*P*A‖ ≤ 1780000 * ρ^5 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖P‖ * ‖A‖ ≤ 2 * 89 * (10000 * ρ^5) := by
          apply mul_le_mul
          · nlinarith [hPn]
          · exact hAρ
          · exact norm_nonneg A
          · norm_num
      _ = 1780000 * ρ^5 := by ring
  have hT2 : ‖A^2‖ ≤ 100000000 * ρ^5 := by
    rw [norm_pow]
    have h10 : ρ^10 ≤ ρ^5 := pow_le_pow_of_le_one hρ0 hρ1 (by norm_num)
    have h : ‖A‖^2 ≤ (10000 * ρ^5)^2 := pow_le_pow_left₀ (norm_nonneg A) hAρ 2
    calc ‖A‖^2 ≤ (10000 * ρ^5)^2 := h
      _ = 10000^2 * ρ^10 := by ring
      _ ≤ 10000^2 * ρ^5 := mul_le_mul_of_nonneg_left h10 (by positivity)
      _ = 100000000 * ρ^5 := by norm_num
  have hT3 : ‖(2:ℂ)*Q*B‖ ≤ 1600000 * ρ^5 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖Q‖ * ‖B‖ ≤ 2 * 80 * (10000 * ρ^5) := by
          apply mul_le_mul
          · nlinarith [hQn]
          · exact hBρ
          · exact norm_nonneg B
          · norm_num
      _ = 1600000 * ρ^5 := by ring
  have hT4 : ‖B^2‖ ≤ 100000000 * ρ^5 := by
    rw [norm_pow]
    have h10 : ρ^10 ≤ ρ^5 := pow_le_pow_of_le_one hρ0 hρ1 (by norm_num)
    have h : ‖B‖^2 ≤ (10000 * ρ^5)^2 := pow_le_pow_left₀ (norm_nonneg B) hBρ 2
    calc ‖B‖^2 ≤ (10000 * ρ^5)^2 := h
      _ = 10000^2 * ρ^10 := by ring
      _ ≤ 10000^2 * ρ^5 := mul_le_mul_of_nonneg_left h10 (by positivity)
      _ = 100000000 * ρ^5 := by norm_num
  rw [hkey]
  have hsum : ‖(P^2 - Q^2 - T) + (2*P*A + A^2) - (2*Q*B + B^2)‖
      ≤ 5952 * ρ^5 + (1780000 * ρ^5 + 100000000 * ρ^5) + 1600000 * ρ^5
          + 100000000 * ρ^5 := by
    have e1 := norm_sub_le ((P^2 - Q^2 - T) + (2*P*A + A^2)) ((2*Q*B + B^2))
    have e2 := norm_add_le (P^2 - Q^2 - T) ((2:ℂ)*P*A + A^2)
    have e3 := norm_add_le ((2:ℂ)*P*A) (A^2)
    have e4 := norm_add_le ((2:ℂ)*Q*B) (B^2)
    nlinarith [e1, e2, e3, e4, hpt, hT1, hT2, hT3, hT4]
  have hp5 : 0 ≤ ρ^5 := by positivity
  linarith [hsum]

theorem zAtomDevFourthOrder (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, 2 ≤ UpperHalfPlane.im z →
        ‖Work.Asymptotics.Compact.dL ℓ z + (32 / 3 : ℂ) * (Work.Residues.Ept z) ^ 3
          - 6 * (Work.Residues.Ept z) ^ 4‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 5) ∧
      (∀ z : UpperHalfPlane, 2 ≤ UpperHalfPlane.im z →
        ‖Work.Asymptotics.Compact.dW z + 32 * (Work.Residues.Ept z) ^ 3
          - 24 * (Work.Residues.Ept z) ^ 4‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 5) ∧
      (∀ z : UpperHalfPlane, 2 ≤ UpperHalfPlane.im z →
        ‖Work.Asymptotics.Compact.dD2 z - 448 * (Work.Residues.Ept z) ^ 3
          + 912 * (Work.Residues.Ept z) ^ 4‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 5) := by
  obtain ⟨CL, hCL, hLb⟩ := Work.Asymptotics.KhatE1.cusp_L_fourth ℓ
  refine ⟨CL + 10000 + 300000000, by positivity, ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : (1 : ℝ) ≤ z.im := by linarith
    have h := hLb z hz1
    have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
      (show Work.Asymptotics.Compact.cuspC ℓ = Work.Asymptotics.cuspL ℓ from rfl).trans
        (Work.Asymptotics.CuspL_eq ℓ)
    have hgoal : Work.Asymptotics.Compact.dL ℓ z + (32 / 3 : ℂ) * (Work.Residues.Ept z) ^ 3
          - 6 * (Work.Residues.Ept z) ^ 4
        = ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
            - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
            - (32 / 3 : ℂ) * (Work.Residues.Ept z) ^ 3
            + 6 * (Work.Residues.Ept z) ^ 4) := by
      rw [Work.Asymptotics.Compact.dL, Work.Asymptotics.Compact.Lref,
        Work.Asymptotics.Compact.Xc, hc]
      ring
    rw [hgoal]
    calc ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
            - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
            - (32 / 3 : ℂ) * (Work.Residues.Ept z) ^ 3
            + 6 * (Work.Residues.Ept z) ^ 4)‖
        ≤ CL * ‖Work.Residues.Ept z‖ ^ 5 := h
      _ ≤ (CL + 10000 + 300000000) * ‖Work.Residues.Ept z‖ ^ 5 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  · intro z hz
    have h := Work.Asymptotics.WFun_qexp z hz
    have hgoal : Work.Asymptotics.Compact.dW z + 32 * (Work.Residues.Ept z) ^ 3
          - 24 * (Work.Residues.Ept z) ^ 4
        = Work.Kernels.WFun z - (1 - 8 * Work.Asymptotics.nomeE z
            + 24 * (Work.Asymptotics.nomeE z) ^ 2 - 32 * (Work.Asymptotics.nomeE z) ^ 3
            + 24 * (Work.Asymptotics.nomeE z) ^ 4) := by
      simp only [Work.Asymptotics.Compact.dW, Work.Asymptotics.Compact.Wref,
        Work.Asymptotics.nomeE]
      ring
    rw [hgoal]
    calc ‖Work.Kernels.WFun z - (1 - 8 * Work.Asymptotics.nomeE z
            + 24 * (Work.Asymptotics.nomeE z) ^ 2 - 32 * (Work.Asymptotics.nomeE z) ^ 3
            + 24 * (Work.Asymptotics.nomeE z) ^ 4)‖
        ≤ 10000 * ‖Work.Asymptotics.nomeE z‖ ^ 5 := h
      _ = 10000 * ‖Work.Residues.Ept z‖ ^ 5 := rfl
      _ ≤ (CL + 10000 + 300000000) * ‖Work.Residues.Ept z‖ ^ 5 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  · intro z hz
    have hU := Work.Asymptotics.UFun_qexp z hz
    have hV := Work.Asymptotics.VFun_qexp z hz
    have hU' : ‖Work.Kernels.UFun z - (1 + 8 * Work.Residues.Ept z
          + 24 * (Work.Residues.Ept z) ^ 2 + 32 * (Work.Residues.Ept z) ^ 3
          + 24 * (Work.Residues.Ept z) ^ 4)‖ ≤ 10000 * ‖Work.Residues.Ept z‖ ^ 5 := by
      simpa only [Work.Asymptotics.nomeE] using hU
    have hV' : ‖Work.Kernels.VFun z - (16 * Work.Residues.Ept z
          + 64 * (Work.Residues.Ept z) ^ 3)‖ ≤ 10000 * ‖Work.Residues.Ept z‖ ^ 5 := by
      simpa only [Work.Asymptotics.nomeE] using hV
    have hgoal : Work.Asymptotics.Compact.dD2 z - 448 * (Work.Residues.Ept z) ^ 3
          + 912 * (Work.Residues.Ept z) ^ 4
        = (Work.Kernels.UFun z) ^ 2 - (Work.Kernels.VFun z) ^ 2
            - (1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2
              + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Residues.Ept z) ^ 4) := by
      simp only [Work.Asymptotics.Compact.dD2, Work.Asymptotics.Compact.D2ref]
      ring
    rw [hgoal]
    refine le_trans (dD2_aux (u := Work.Kernels.UFun z) (v := Work.Kernels.VFun z)
      (e := Work.Residues.Ept z) (ρ := ‖Work.Residues.Ept z‖) (norm_nonneg _)
      (le_of_lt (Work.Residues.norm_Ept_lt_one z)) rfl hU' hV') ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith

end Work.Asymptotics.KhatE1Core
