import Mathlib
import Submission.Work.CNum.DAux.Helper
import Submission.Work.CNum.DAux.Geo
import Submission.Work.CNum.DAux.ChordLow
import Submission.Work.CNum.DAux.Grid
import Submission.Work.CNum.DAux.Small
import Submission.Work.CNum.DAux.Jlow
import Submission.Work.CNum.DAux.PhiSteps
import Submission.Work.CNum.DAux.PsiSteps
import Submission.Work.CNum.DistSpec
import Submission.Work.CNum.ChordSpec

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

namespace Work.CNum

open Work.ANum

/-- `m2r` commutes with `max`. -/
lemma DAux_m2r_max (a b : ℤ) : m2r (max a b) = max (m2r a) (m2r b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (m2r_le h)]
  · rw [max_eq_left h, max_eq_left (m2r_le h)]

lemma m2r_dWup_nonneg (a b : Cpx) : 0 ≤ m2r (dWup a b) := by
  have hd0 : (0:ℤ) ≤ distUp a b * 4 := by
    have : 0 ≤ distUp a b := by unfold distUp sqUp; positivity
    linarith
  have h1 : (0:ℝ) ≤ m2r (divU (distUp a b * 4) 3) := by
    have h := divU_ge (k := 3) (by norm_num) (distUp a b * 4)
    have h2 : 0 ≤ m2r (distUp a b * 4) := m2r_nonneg hd0
    linarith
  have h3 : m2r (dWup a b) = m2r (divU (distUp a b * 4) 3) + m2r 4096 := by
    unfold dWup; rw [m2r_add]
  have h4 : (0:ℝ) ≤ m2r (4096:ℤ) := m2r_nonneg (by norm_num)
  rw [h3]; linarith

lemma m2r_dVup_nonneg (a b : Cpx) : 0 ≤ m2r (dVup a b) := by
  have hd0 : (0:ℤ) ≤ distUp a b * 143 := by
    have : 0 ≤ distUp a b := by unfold distUp sqUp; positivity
    linarith
  have h1 : (0:ℝ) ≤ m2r (divU (distUp a b * 143) 115) := by
    have h := divU_ge (k := 115) (by norm_num) (distUp a b * 143)
    have h2 : 0 ≤ m2r (distUp a b * 143) := m2r_nonneg hd0
    linarith
  have h3 : m2r (dVup a b) = m2r (divU (distUp a b * 143) 115) + m2r 4096 := by
    unfold dVup; rw [m2r_add]
  have h4 : (0:ℝ) ≤ m2r (4096:ℤ) := m2r_nonneg (by norm_num)
  rw [h3]; linarith

lemma chord1_ineq {Δ : ℝ} {D : ℤ} (hD0 : 0 ≤ m2r D) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ)) :
    400 * Δ ^ 2 ≤ m2r (chord1 D) := by
  have hspec := ChordSpec.1 D hD0
  have hpow : 0 ≤ (m2r D) ^ 3 / 12 := div_nonneg (by positivity) (by norm_num)
  have h4 : (0 : ℝ) < 4096 / (SC : ℝ) := div_pos (by norm_num) SC_posR
  have h3 : 0 ≤ m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ) := by linarith
  have hsq : Δ ^ 2 ≤ (m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2 := by
    nlinarith [hΔ0, hΔ, h3]
  linarith [hspec, hsq]

lemma chord2_ineq {Δ : ℝ} {D : ℤ} (hD0 : 0 ≤ m2r D) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ)) :
    1000 * Δ ^ 2 ≤ m2r (chord2 D) := by
  have hspec := ChordSpec.2 D hD0
  have hpow : 0 ≤ (m2r D) ^ 3 / 12 := div_nonneg (by positivity) (by norm_num)
  have h4 : (0 : ℝ) < 4096 / (SC : ℝ) := div_pos (by norm_num) SC_posR
  have h3 : 0 ≤ m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ) := by linarith
  have hsq : Δ ^ 2 ≤ (m2r D + (m2r D) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2 := by
    nlinarith [hΔ0, hΔ, h3]
  linarith [hspec, hsq]

/-- `wf u - wf v = uJ (e^{iu} - e^{iv})`. -/
lemma wf_sub (u v : ℝ) :
    wf u - wf v = ((uJ : ℝ) : ℂ) *
      (Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (v : ℂ))) := by
  unfold wf; ring

/-- The `C₂` parameter angle. -/
noncomputable def psiArg (θ : ℝ) : ℝ := C2Psi (θ / 2) - Real.pi

/-! ## Cusp angles -/

lemma exp_cuspAngA : Complex.exp (Complex.I * (cuspAngA : ℂ)) = zCuspA := by
  have hsplit : Complex.I * (cuspAngA : ℂ) =
      Complex.I * ((alpR / 2 : ℝ) : ℂ) + Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ) := by
    rw [cuspAngA]; push_cast; ring
  have h1 : Complex.exp (Complex.I * ((alpR / 2 : ℝ) : ℂ)) =
      (C2C : ℂ) + (C2σ : ℂ) * Complex.I := by
    rw [show Complex.I * ((alpR / 2 : ℝ) : ℂ) = ((alpR / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, cos_half_alpR, ← Complex.ofReal_sin, sin_half_alpR]
  have h3 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, ← Complex.ofReal_sin,
      Real.sin_pi_div_two]
    simp
  have h2 : Complex.exp (Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
    have hs : Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hs, Complex.exp_add, Complex.exp_pi_mul_I, h3]; ring
  have hC : (C2C : ℂ) = (460 / 629 : ℂ) := by rw [C2C]; norm_num
  have hS : (C2σ : ℂ) = (429 / 629 : ℂ) := by rw [C2σ]; norm_num
  rw [hsplit, Complex.exp_add, h1, h2, hC, hS]
  calc ((460 / 629 : ℂ) + (429 / 629 : ℂ) * Complex.I) * (-Complex.I)
      = -(460 / 629 : ℂ) * Complex.I - (429 / 629 : ℂ) * (Complex.I * Complex.I) := by ring
    _ = -(460 / 629 : ℂ) * Complex.I + (429 / 629 : ℂ) := by rw [Complex.I_mul_I]; ring
    _ = zCuspA := by unfold zCuspA; ring

lemma psiC_cuspA_ang : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) =
    (3 / 4 : ℂ) * Complex.exp (Complex.I * (cuspAngA : ℂ)) := by
  rw [psiC_cuspA, exp_cuspAngA]
  rw [show ((((3 : ℝ) / 4 : ℝ)) : ℂ) = (3 / 4 : ℂ) by norm_num]
  ring

lemma zCuspA_mul_zCuspB : zCuspA * zCuspB = 1 := by
  apply Complex.ext
  · simp only [zCuspA, zCuspB, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
      add_zero, zero_add, mul_neg, neg_mul, neg_neg]
    norm_num
  · simp only [zCuspA, zCuspB, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero,
      add_zero, zero_add, mul_neg, neg_mul, neg_neg]
    norm_num

lemma exp_cuspAngB : Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) = zCuspB := by
  have hsplit : Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ) =
      Complex.I * ((4 * Real.pi : ℝ) : ℂ) + Complex.I * ((-cuspAngA : ℝ) : ℂ) := by
    push_cast; ring
  have h4 : Complex.exp (Complex.I * ((4 * Real.pi : ℝ) : ℂ)) = 1 := by
    have h4' : Complex.exp (Complex.I * ((4 * Real.pi : ℝ) : ℂ)) =
        Complex.exp (2 * (2 * (Real.pi : ℂ) * Complex.I)) := by
      congr 1; push_cast; ring
    rw [h4', show (2 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I) + (2 * (Real.pi : ℂ) * Complex.I) by ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
    ring
  have hneg : Complex.exp (Complex.I * ((-cuspAngA : ℝ) : ℂ)) = (zCuspA)⁻¹ := by
    rw [show Complex.I * ((-cuspAngA : ℝ) : ℂ) = -(Complex.I * (cuspAngA : ℂ)) by push_cast; ring,
      Complex.exp_neg, exp_cuspAngA]
  rw [hsplit, Complex.exp_add, h4, one_mul, hneg]
  exact inv_eq_of_mul_eq_one_left (by rw [mul_comm]; exact zCuspA_mul_zCuspB)

lemma psiC_cuspB_ang :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) =
      (3 / 4 : ℂ) * Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) := by
  have hexp : Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ))) := by
    congr 1; push_cast; ring
  rw [hexp, psiC_cuspB, exp_cuspAngB]
  rw [show ((((3 : ℝ) / 4 : ℝ)) : ℂ) = (3 / 4 : ℂ) by norm_num]
  ring

lemma cl_cuspA : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC
    (alpR / (2 * Real.pi)) = Hfun cuspAngA := by
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((alpR / (2 * Real.pi) : ℝ)) : ℂ)) =
      Complex.exp (Complex.I * (alpR : ℂ)) := by
    congr 1; push_cast; field_simp; try ring
  rw [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, hexp, psiC_cuspA_ang,
    log_norm_hauptH_circle]

lemma cl_cuspB : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC
    ((2 * Real.pi - alpR) / (2 * Real.pi)) = Hfun (4 * Real.pi - cuspAngA) := by
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((((2 * Real.pi - alpR) / (2 * Real.pi) : ℝ)) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) := by
    congr 1; push_cast; field_simp; try ring
  rw [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, hexp, psiC_cuspB_ang,
    log_norm_hauptH_circle]

/-! ## Grid forms for the two outer arcs -/

lemma cl_grid_Hfun4 {j : ℕ} (h1 : 780 ≤ j) (h2 : j ≤ 1024) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC ((j:ℝ)/1024) =
      Hfun (4 * Real.pi - phiR (thetaK (1024 - j))) := by
  have h := cl_eq_Hfun4_of_mem (thetaK_mem_Ioo_C1b h1 h2)
  rw [thetaK_div] at h
  rwa [show 2 * Real.pi - thetaK j = thetaK (1024 - j) by
    unfold thetaK; push_cast [Nat.cast_sub h2]; ring] at h

lemma two_pi_sub_thetaK {k : ℕ} (hk : k ≤ 1024) :
    2 * Real.pi - thetaK k = thetaK (1024 - k) := by
  unfold thetaK; push_cast [Nat.cast_sub hk]; ring

/-! ## The `Jfun` value at the cusps -/

lemma psiArg_alpR : psiArg alpR = alpR / 2 - Real.pi := by
  unfold psiArg; rw [C2Psi_alpR_half]

lemma psiArg_cuspB : psiArg (2 * Real.pi - alpR) = -alpR / 2 - Real.pi := by
  have h : C2Psi ((2 * Real.pi - alpR) / 2) = -alpR / 2 := by
    have h1 : (2 * Real.pi - alpR) / 2 = Real.pi - alpR / 2 := by ring
    rw [h1]
    unfold C2Psi
    rw [show Real.cos (Real.pi - alpR/2) = -Real.cos (alpR/2) by rw [Real.cos_pi_sub],
      cos_half_alpR, show -C2C / C2C = -1 by rw [neg_div, div_self C2C_ne_zero],
      Real.arcsin_neg, Real.arcsin_one]
    ring
  unfold psiArg
  rw [h]

lemma wf_cuspB_aux : wf (-alpR / 2 - Real.pi) =
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) := by
  have hcJ : ((cJ : ℝ) : ℂ) = (cenC2 : ℂ) := by rw [cJ, cenC2_eq]
  have huJ : ((uJ : ℝ) : ℂ) = (Real.sqrt rho2sq : ℂ) := by rw [uJ, sqrt_rho2sq]
  have hC : (C2C : ℂ) = (460 / 629 : ℂ) := by rw [C2C]; norm_num
  have hS : (C2σ : ℂ) = (429 / 629 : ℂ) := by rw [C2σ]; norm_num
  have hpsi : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) =
      (3 / 4 : ℂ) * Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) :=
    psiC_cuspB_ang
  rw [wf, hcJ, huJ, hpsi]
  have hexp : Complex.exp (Complex.I * ((-alpR / 2 - Real.pi : ℝ) : ℂ)) =
      -(((C2C : ℂ) - (C2σ : ℂ) * Complex.I)) := by
    have h1 : ((-alpR / 2 - Real.pi : ℝ) : ℂ) = (-(alpR/2) : ℂ) + (-(Real.pi : ℂ)) := by
      push_cast; ring
    have h2 : Complex.I * ((-(alpR/2) : ℂ) + (-(Real.pi : ℂ))) =
        Complex.I * (-(alpR/2) : ℂ) + Complex.I * (-(Real.pi : ℂ)) := by ring
    rw [h1, h2, Complex.exp_add]
    have h3 : Complex.exp (Complex.I * (-(alpR/2) : ℂ)) =
        (C2C : ℂ) - (C2σ : ℂ) * Complex.I := by
      rw [show Complex.I * (-(alpR/2) : ℂ) = -(((alpR/2 : ℝ) : ℂ) * Complex.I) by
        push_cast; ring, Complex.exp_neg,
        show Complex.exp (((alpR/2 : ℝ) : ℂ) * Complex.I) =
          (C2C : ℂ) + (C2σ : ℂ) * Complex.I by
          rw [Complex.exp_mul_I, ← Complex.ofReal_cos, cos_half_alpR, ← Complex.ofReal_sin,
            sin_half_alpR]]
      have hsum : (C2C : ℂ) ^ 2 + (C2σ : ℂ) ^ 2 = 1 := by
        rw [show ((C2C : ℝ) : ℂ) = (460/629 : ℂ) by rw [C2C]; norm_num,
            show ((C2σ : ℝ) : ℂ) = (429/629 : ℂ) by rw [C2σ]; norm_num]
        norm_num
      have hmul : ((C2C : ℂ) + (C2σ : ℂ) * Complex.I) * ((C2C : ℂ) - (C2σ : ℂ) * Complex.I) = 1 := by
        rw [← hsum]
        calc (↑C2C + ↑C2σ * Complex.I) * (↑C2C - ↑C2σ * Complex.I)
            = ↑C2C * ↑C2C - (↑C2σ * Complex.I) * (↑C2σ * Complex.I) := by ring
          _ = ↑C2C ^ 2 + ↑C2σ ^ 2 := by
              rw [show (↑C2σ * Complex.I) * (↑C2σ * Complex.I) =
                ↑C2σ ^ 2 * (Complex.I * Complex.I) by ring, Complex.I_mul_I]
              ring
      exact inv_eq_of_mul_eq_one_left (by rw [mul_comm]; exact hmul)
    have h4 : Complex.exp (Complex.I * (-(Real.pi : ℂ))) = -1 := by
      rw [show Complex.I * (-(Real.pi : ℂ)) = -((Real.pi : ℂ) * Complex.I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    rw [h3, h4]; ring
  rw [hexp]
  have hC3 : Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) = zCuspB := exp_cuspAngB
  rw [hC3]
  unfold zCuspB
  rw [hC, hS, cenC2_eq, sqrt_rho2sq]
  push_cast
  ring_nf

lemma wf_cuspA : wf (alpR / 2 - Real.pi) =
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) := by
  have hcJ : ((cJ : ℝ) : ℂ) = (cenC2 : ℂ) := by rw [cJ, cenC2_eq]
  have huJ : ((uJ : ℝ) : ℂ) = (Real.sqrt rho2sq : ℂ) := by rw [uJ, sqrt_rho2sq]
  have hC : (C2C : ℂ) = (460 / 629 : ℂ) := by rw [C2C]; norm_num
  have hS : (C2σ : ℂ) = (429 / 629 : ℂ) := by rw [C2σ]; norm_num
  rw [wf, hcJ, huJ, psiC_cuspA_ang]
  have hexp : Complex.exp (Complex.I * (((alpR / 2 - Real.pi : ℝ)) : ℂ)) =
      -((C2C : ℂ) + (C2σ : ℂ) * Complex.I) := by
    have h1 : ((alpR / 2 - Real.pi : ℝ) : ℂ) = (alpR/2 : ℂ) + (-(Real.pi : ℂ)) := by
      push_cast; ring
    have h2 : Complex.I * ((alpR/2 : ℂ) + (-(Real.pi : ℂ))) =
        Complex.I * (alpR/2 : ℂ) + Complex.I * (-(Real.pi : ℂ)) := by ring
    rw [h1, h2, Complex.exp_add]
    have h3 : Complex.exp (Complex.I * (alpR/2 : ℂ)) = (C2C : ℂ) + (C2σ : ℂ) * Complex.I := by
      rw [show Complex.I * (alpR/2 : ℂ) = ((alpR/2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, cos_half_alpR, ← Complex.ofReal_sin, sin_half_alpR]
    have h4 : Complex.exp (Complex.I * (-(Real.pi : ℂ))) = -1 := by
      rw [show Complex.I * (-(Real.pi : ℂ)) = -((Real.pi : ℂ) * Complex.I) by ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    rw [h3, h4]; ring
  rw [hexp, exp_cuspAngA]
  unfold zCuspA
  rw [hC, hS, cenC2_eq, sqrt_rho2sq]
  push_cast
  ring_nf

lemma Jfun_cuspA' : Jfun (psiArg alpR) = Hfun cuspAngA := by
  rw [psiArg_alpR, Jfun_eq_log_norm']
  · rw [wf_cuspA]
    have h1 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) =
        (3 / 4 : ℂ) * Complex.exp (Complex.I * (cuspAngA : ℂ)) := psiC_cuspA_ang
    rw [h1, log_norm_hauptH_circle]
  · rw [wf_cuspA]; exact Work.CPsi.psiC_norm_le (by rw [Complex.norm_exp]; simp)
  · rw [wf_cuspA]
    intro h0; exact Complex.exp_ne_zero _ (Work.CPsi.psiC_eq_zero h0)

lemma Jfun_cuspB' : Jfun (psiArg (2 * Real.pi - alpR)) = Hfun (4 * Real.pi - cuspAngA) := by
  rw [psiArg_cuspB, Jfun_eq_log_norm']
  · rw [wf_cuspB_aux, psiC_cuspB_ang, log_norm_hauptH_circle]
  · rw [wf_cuspB_aux]; exact Work.CPsi.psiC_norm_le (by rw [Complex.norm_exp]; simp)
  · rw [wf_cuspB_aux]
    intro h0; exact Complex.exp_ne_zero _ (Work.CPsi.psiC_eq_zero h0)

lemma ptOf_mem_thetaK (k : ℕ) (hk : k ≤ 1024) :
    (ptOf k).Mem (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ)))) := by
  have h := ptOf_mem k hk
  have heq : Complex.exp (Complex.I * (thetaK k : ℂ)) =
      Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)) := by
    rw [thetaK]; push_cast; ring
  rwa [heq]

/-! ## The five arc steps -/

theorem arcStepC1 (k : ℕ) (hk : k ≤ 243) :
    ∀ t ∈ Set.Icc ((k:ℝ)/1024) (((k:ℝ)+1)/1024),
      m2r (gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  intro t ht
  rw [Set.mem_Icc] at ht
  have hgv : gv k = min (svDn (ptOf k)) (svDn (ptOf (k+1))) -
      chord1 (dWup (ptOf k) (ptOf (k+1))) := by
    rw [gv]; simp only [if_pos hk]
  rw [hgv, m2r_sub, DAux_m2r_min]
  have hga : m2r (svDn (ptOf k)) ≤ Hfun (phiR (thetaK k)) := by
    have h := gridDn k (by omega)
    rw [cl_grid_Hfun (j := k) (by omega)] at h
    exact h
  have hgb : m2r (svDn (ptOf (k+1))) ≤ Hfun (phiR (thetaK (k+1))) := by
    have h := gridDn (k+1) (by omega)
    rw [cl_grid_Hfun (j := k+1) (by omega)] at h
    exact h
  have ht1 : t ≤ (244:ℝ)/1024 := by
    have hkR : (k:ℝ) ≤ 243 := by exact_mod_cast hk
    linarith [ht.2]
  have ht0 : 0 ≤ t := by
    have : (0:ℝ) ≤ (k:ℝ)/1024 := by positivity
    linarith [ht.1]
  have hθ0 : 0 ≤ 2 * Real.pi * t := by
    have hp : (0:ℝ) < Real.pi := Real.pi_pos
    nlinarith
  have hθ1 : 2 * Real.pi * t ≤ thetaK 244 := by
    have h2 : 2 * Real.pi * t ≤ 2 * Real.pi * ((244:ℝ)/1024) := by
      have hp : (0:ℝ) < Real.pi := Real.pi_pos
      nlinarith [ht1]
    have h3 : thetaK 244 = 2 * Real.pi * ((244:ℝ)/1024) := by unfold thetaK; push_cast; ring
    linarith
  have hmemt : 2 * Real.pi * t ∈ Set.Ioo (-alpR) alpR := mem_Ioo_of_le_theta244 hθ0 hθ1
  have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
      Hfun (phiR (2 * Real.pi * t)) := by
    have h := cl_eq_Hfun_of_mem hmemt
    rwa [show 2 * Real.pi * t / (2 * Real.pi) = t by field_simp; try ring] at h
  have hmemk : thetaK k ∈ Set.Ioo (-alpR) alpR :=
    mem_Ioo_of_le_theta244 (thetaK_nonneg k) (thetaK_mono (by omega))
  have hmemk1 : thetaK (k+1) ∈ Set.Ioo (-alpR) alpR :=
    mem_Ioo_of_le_theta244 (thetaK_nonneg (k+1)) (thetaK_mono (by omega))
  have htheta : thetaK k ≤ thetaK (k+1) := thetaK_mono (by omega)
  have hmono : phiR (thetaK k) ≤ phiR (thetaK (k+1)) :=
    phi_strictMono.monotoneOn hmemk hmemk1 htheta
  have hmemφ : phiR (2 * Real.pi * t) ∈ Set.Icc (phiR (thetaK k)) (phiR (thetaK (k+1))) := by
    constructor
    · apply phi_strictMono.monotoneOn hmemk hmemt
      unfold thetaK; push_cast
      nlinarith [Real.pi_pos, ht.1]
    · apply phi_strictMono.monotoneOn hmemt hmemk1
      unfold thetaK; push_cast
      nlinarith [Real.pi_pos, ht.2]
  have hchord := Hfun_chord_lower hmono (phiR (2 * Real.pi * t)) hmemφ
  have hΔ0 : 0 ≤ phiR (thetaK (k+1)) - phiR (thetaK k) := by linarith
  have hD0 : 0 ≤ m2r (dWup (ptOf k) (ptOf (k+1))) := m2r_dWup_nonneg _ _
  have hstep : phiR (thetaK (k+1)) - phiR (thetaK k) ≤ 1 := by
    have h1 : thetaK (k+1) ≤ 2 * Real.pi * 244 / 1024 := by
      have h := thetaK_mono (by omega : k+1 ≤ 244)
      have h244 : thetaK 244 = 2 * Real.pi * 244 / 1024 := by unfold thetaK; push_cast; ring
      linarith
    have h2 : thetaK (k+1) - thetaK k ≤ 2 * Real.pi / 1024 := le_of_eq (thetaK_succ k)
    exact DAux.PhiSteps.1 (thetaK k) (thetaK (k+1)) (thetaK_nonneg k) htheta h1 h2
  have hdist := DistSpec.2.1 (ptOf k) (ptOf (k+1))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ))))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ))))
      (small_ptOf k (by omega)) (small_ptOf (k+1) (by omega))
      (ptOf_mem_thetaK k (by omega)) (ptOf_mem_thetaK (k+1) (by omega))
  have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ))) -
      Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ)))‖ =
      (3/4) * ‖Complex.exp (Complex.I * ((phiR (thetaK k) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((phiR (thetaK (k+1)) : ℝ) : ℂ))‖ := by
    have h34 : ‖(3/4 : ℂ)‖ = 3/4 := by
      rw [show (3/4 : ℂ) = ((3/4 : ℝ) : ℂ) by norm_num, norm_ofReal_daux,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4)]
    rw [psiC_eq_smul_exp hmemk, psiC_eq_smul_exp hmemk1, ← mul_sub, norm_mul, h34]
  have hDW : ‖Complex.exp (Complex.I * ((phiR (thetaK k) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((phiR (thetaK (k+1)) : ℝ) : ℂ))‖ ≤
      m2r (dWup (ptOf k) (ptOf (k+1))) := by
    rw [hnorm] at hdist
    nlinarith [hdist]
  have hstep2 : phiR (thetaK (k+1)) - phiR (thetaK k) ≤
      m2r (dWup (ptOf k) (ptOf (k+1))) + (m2r (dWup (ptOf k) (ptOf (k+1))))^3/12 +
        4096/(SC:ℝ) := by
    have h := arc_le_chord (a := phiR (thetaK k)) (b := phiR (thetaK (k+1))) hΔ0 hstep
    have h3 : ‖Complex.exp (Complex.I * ((phiR (thetaK k) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((phiR (thetaK (k+1)) : ℝ) : ℂ))‖^3/12 ≤
        (m2r (dWup (ptOf k) (ptOf (k+1))))^3/12 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW 3) (by norm_num)
    linarith [h, h3]
  have hD := chord1_ineq hD0 hΔ0 hstep2
  have hmin : min (m2r (svDn (ptOf k))) (m2r (svDn (ptOf (k+1)))) ≤
      min (Hfun (phiR (thetaK k))) (Hfun (phiR (thetaK (k+1)))) := min_le_min hga hgb
  have hcl' : Hfun (phiR (2 * Real.pi * t)) =
      Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := hcl.symm
  linarith [hmin, hchord, hD, hcl']

lemma cuspADn' : m2r (svDn ptCuspA) ≤ Hfun cuspAngA := by
  have h := cuspADn
  rw [psiC_cuspA_ang] at h
  rwa [log_norm_hauptH_circle] at h

lemma cuspBDn' : m2r (svDn ptCuspB) ≤ Hfun (4 * Real.pi - cuspAngA) := by
  have h := cuspBDn
  rw [show Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ))) =
    Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) by congr 1; push_cast; ring] at h
  rw [psiC_cuspB_ang] at h
  rwa [log_norm_hauptH_circle] at h

lemma psiArg_le_of_lt {u v : ℝ} (h1 : alpR < u) (h2 : v < 2 * Real.pi - alpR) (huv : u ≤ v) :
    psiArg v ≤ psiArg u := by
  unfold psiArg
  have hu : u/2 ∈ Set.Ioo (alpR/2) (Real.pi - alpR/2) :=
    ⟨by linarith, by linarith⟩
  have hv : v/2 ∈ Set.Ioo (alpR/2) (Real.pi - alpR/2) :=
    ⟨by linarith, by linarith⟩
  have h := C2_Psi_antitone.antitoneOn hu hv (by linarith : u/2 ≤ v/2)
  linarith

lemma C2Psi_pi_sub (t : ℝ) : C2Psi (Real.pi - t) = - C2Psi t := by
  unfold C2Psi
  rw [Real.cos_pi_sub, neg_div, Real.arcsin_neg]
  ring

lemma C2Psi_le_alphaHalf {t : ℝ} (h1 : alpR / 2 ≤ t) (h2 : t ≤ alpR / 2 + Real.pi / 2) :
    C2Psi t ≤ C2Psi (alpR / 2) := by
  rw [C2Psi_alpR_half]
  set s : ℝ := t - alpR / 2 with hs
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ Real.pi / 2 := by linarith
  have ht : t = s + alpR / 2 := by rw [hs]; ring
  have hct : Real.cos t = Real.cos s * C2C - Real.sin s * C2σ := by
    rw [ht, Real.cos_add, cos_half_alpR, sin_half_alpR]
  have hu : Real.cos t / C2C = Real.cos s - (C2σ / C2C) * Real.sin s := by
    rw [hct, sub_div]
    have h1 : Real.cos s * C2C / C2C = Real.cos s := by
      rw [mul_div_assoc, div_self (ne_of_gt C2C_pos), mul_one]
    have h2 : Real.sin s * C2σ / C2C = (C2σ / C2C) * Real.sin s := by
      rw [mul_div_assoc]
      ring
    rw [h1, h2]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [Real.pi_pos])
  have hle : Real.cos t / C2C ≤ Real.cos s := by
    rw [hu]
    have hσ : 0 ≤ C2σ / C2C := le_of_lt (div_pos C2σ_pos C2C_pos)
    have : 0 ≤ (C2σ / C2C) * Real.sin s := mul_nonneg hσ hsin0
    linarith
  have hcu : Real.cos t ≤ C2C := by
    have h := Real.antitoneOn_cos
      (show alpR/2 ∈ Set.Icc (0:ℝ) Real.pi from
        ⟨by linarith [alpR_pos], by linarith [alpR_lt_pi, Real.pi_pos]⟩)
      (show t ∈ Set.Icc (0:ℝ) Real.pi from ⟨by linarith [alpR_pos], by linarith [Real.pi_pos, alpR_lt_pi]⟩)
      h1
    rwa [cos_half_alpR] at h
  have hcl : -C2σ ≤ Real.cos t := by
    have h := Real.antitoneOn_cos
      (show t ∈ Set.Icc (0:ℝ) Real.pi from ⟨by linarith [alpR_pos], by linarith [Real.pi_pos, alpR_lt_pi]⟩)
      (show alpR/2 + Real.pi/2 ∈ Set.Icc (0:ℝ) Real.pi from
        ⟨by linarith [alpR_pos], by linarith [Real.pi_pos, alpR_lt_pi]⟩) h2
    rw [show Real.cos (alpR/2 + Real.pi/2) = -C2σ by
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, cos_half_alpR, sin_half_alpR]
      ring] at h
    exact h
  have hxmem : Real.cos t / C2C ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ C2C_pos]
      nlinarith [hcl, C2σ_pos, C2C_pos, C2σ_lt_C2C]
    · rw [div_le_iff₀ C2C_pos]
      nlinarith [hcu, C2C_pos]
  have hkey : Real.arcsin (Real.cos t / C2C) ≤ Real.pi / 2 - s := by
    rw [Real.arcsin_le_iff_le_sin hxmem ⟨by linarith, by linarith⟩, Real.sin_pi_div_two_sub]
    exact hle
  unfold C2Psi
  have hteq : t - Real.pi / 2 = s + alpR / 2 - Real.pi / 2 := by rw [ht]
  linarith [hkey, hteq]

lemma psiArg_le_cuspA {u : ℝ} (h1 : alpR ≤ u) (h2 : u ≤ alpR + Real.pi) :
    psiArg u ≤ psiArg alpR := by
  unfold psiArg
  rw [C2Psi_alpR_half]
  have h := C2Psi_le_alphaHalf (t := u/2) (by linarith) (by linarith)
  rw [C2Psi_alpR_half] at h
  linarith

lemma psiArg_ge_cuspB {u : ℝ} (h1 : Real.pi - alpR ≤ u) (h2 : u ≤ 2 * Real.pi - alpR) :
    psiArg (2 * Real.pi - alpR) ≤ psiArg u := by
  unfold psiArg
  have hcusp : C2Psi ((2 * Real.pi - alpR)/2) = -C2Psi (alpR/2) := by
    rw [show (2 * Real.pi - alpR)/2 = Real.pi - alpR/2 by ring, C2Psi_pi_sub]
  rw [hcusp, C2Psi_alpR_half]
  have hpi : C2Psi (u/2) = - C2Psi (Real.pi - u/2) := by
    have hh := C2Psi_pi_sub (Real.pi - u/2)
    rw [show Real.pi - (Real.pi - u/2) = u/2 by ring] at hh
    exact hh
  have h := C2Psi_le_alphaHalf (t := Real.pi - u/2) (by linarith) (by linarith)
  rw [C2Psi_alpR_half] at h
  linarith

theorem arcStepC1b (k : ℕ) (h1 : 780 ≤ k) (hk : k ≤ 1023) :
    ∀ t ∈ Set.Icc ((k:ℝ)/1024) (((k:ℝ)+1)/1024),
      m2r (gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  intro t ht
  rw [Set.mem_Icc] at ht
  have hk1024 : k ≤ 1024 := by omega
  have hgv : gv k = min (svDn (ptOf k)) (svDn (ptOf (k+1))) -
      chord1 (dWup (ptOf k) (ptOf (k+1))) := by
    rw [gv]
    simp only [if_neg (by omega : ¬ k ≤ 243), if_neg (by omega : k ≠ 244),
      if_neg (by omega : ¬ k ≤ 778), if_neg (by omega : k ≠ 779)]
  rw [hgv, m2r_sub, DAux_m2r_min]
  have hga : m2r (svDn (ptOf k)) ≤ Hfun (4 * Real.pi - phiR (thetaK (1024 - k))) := by
    have h := gridDn k hk1024
    rw [cl_grid_Hfun4 h1 hk1024] at h
    exact h
  have hgb : m2r (svDn (ptOf (k+1))) ≤ Hfun (4 * Real.pi - phiR (thetaK (1024 - (k+1)))) := by
    have h := gridDn (k+1) (by omega)
    rw [cl_grid_Hfun4 (by omega) (by omega)] at h
    exact h
  have h1t_lo : ((1023 - k : ℕ) : ℝ)/1024 ≤ 1 - t := by
    have hcast : ((1023 - k : ℕ) : ℝ) = 1023 - (k:ℝ) := by
      push_cast [Nat.cast_sub (by omega : k ≤ 1023)]; ring
    rw [hcast]
    linarith [ht.2]
  have h1t_hi : 1 - t ≤ ((1024 - k : ℕ) : ℝ)/1024 := by
    have hcast : ((1024 - k : ℕ) : ℝ) = 1024 - (k:ℝ) := by
      push_cast [Nat.cast_sub hk1024]; ring
    rw [hcast]
    linarith [ht.1]
  have hs0 : 0 ≤ 2 * Real.pi * (1 - t) := by
    have : 0 ≤ 1 - t := by
      have h : ((1023 - k : ℕ) : ℝ)/1024 ≥ 0 := by positivity
      linarith
    positivity
  have hs1 : 2 * Real.pi * (1 - t) ≤ thetaK 244 := by
    have hle : 1 - t ≤ (244:ℝ)/1024 := by
      have h : ((1024 - k : ℕ) : ℝ) ≤ 244 := by
        have := (by omega : 1024 - k ≤ 244)
        exact_mod_cast this
      linarith
    have h2 : 2 * Real.pi * (1 - t) ≤ 2 * Real.pi * ((244:ℝ)/1024) := by
      nlinarith [Real.pi_pos]
    have h3 : thetaK 244 = 2 * Real.pi * ((244:ℝ)/1024) := by unfold thetaK; push_cast; ring
    linarith
  have hmemt : 2 * Real.pi * t - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR := by
    have heq : 2 * Real.pi * t - 2 * Real.pi = -(2 * Real.pi * (1 - t)) := by ring
    rw [heq]
    exact ⟨by linarith [hs1, theta244_lt_alpR], by linarith [alpR_pos, hs0]⟩
  have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
      Hfun (4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t)) := by
    have h := cl_eq_Hfun4_of_mem hmemt
    rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
  have hA0 : thetaK (1023 - k) ≤ 2 * Real.pi - 2 * Real.pi * t := by
    have hcast : ((1023 - k : ℕ) : ℝ) = 1023 - (k:ℝ) := by
      push_cast [Nat.cast_sub (by omega : k ≤ 1023)]; ring
    unfold thetaK
    rw [hcast]
    nlinarith [Real.pi_pos]
  have hA1 : 2 * Real.pi - 2 * Real.pi * t ≤ thetaK (1024 - k) := by
    have hcast : ((1024 - k : ℕ) : ℝ) = 1024 - (k:ℝ) := by
      push_cast [Nat.cast_sub hk1024]; ring
    unfold thetaK
    rw [hcast]
    nlinarith [Real.pi_pos]
  have hAk : thetaK (1023 - k) ∈ Set.Ioo (-alpR) alpR :=
    mem_Ioo_of_le_theta244 (thetaK_nonneg _) (thetaK_mono (by omega))
  have hAk1 : thetaK (1024 - k) ∈ Set.Ioo (-alpR) alpR :=
    mem_Ioo_of_le_theta244 (thetaK_nonneg _) (thetaK_mono (by omega))
  have hAt : 2 * Real.pi - 2 * Real.pi * t ∈ Set.Ioo (-alpR) alpR := by
    have h1' : 0 ≤ 2 * Real.pi - 2 * Real.pi * t := by linarith [hA0, thetaK_nonneg (1023 - k)]
    have h2' : 2 * Real.pi - 2 * Real.pi * t ≤ thetaK 244 := by
      have := thetaK_le244 (by omega : 1024 - k ≤ 244)
      linarith
    exact mem_Ioo_of_le_theta244 h1' h2'
  have hmono : 4 * Real.pi - phiR (thetaK (1024 - k)) ≤
      4 * Real.pi - phiR (thetaK (1024 - (k+1))) := by
    have h1023 : 1024 - (k+1) = 1023 - k := by omega
    rw [h1023]
    have := phi_strictMono.monotoneOn hAk hAk1 (thetaK_mono (by omega))
    linarith
  have hmemφ : 4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t) ∈
      Set.Icc (4 * Real.pi - phiR (thetaK (1024 - k)))
        (4 * Real.pi - phiR (thetaK (1024 - (k+1)))) := by
    have h1023 : 1024 - (k+1) = 1023 - k := by omega
    rw [h1023]
    have h := phi_strictMono.monotoneOn hAk hAt hA0
    have h2 := phi_strictMono.monotoneOn hAt hAk1 hA1
    exact ⟨by linarith, by linarith⟩
  have hchord := Hfun_chord_lower hmono
    (4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t)) hmemφ
  have hΔ0 : 0 ≤ (4 * Real.pi - phiR (thetaK (1024 - (k+1)))) -
      (4 * Real.pi - phiR (thetaK (1024 - k))) := by
    have h1023 : 1024 - (k+1) = 1023 - k := by omega
    rw [h1023]
    have := phi_strictMono.monotoneOn hAk hAk1 (thetaK_mono (by omega))
    linarith
  have hD0 : 0 ≤ m2r (dWup (ptOf k) (ptOf (k+1))) := m2r_dWup_nonneg _ _
  have hstep : (4 * Real.pi - phiR (thetaK (1024 - (k+1)))) -
      (4 * Real.pi - phiR (thetaK (1024 - k))) ≤ 1 := by
    have h1023 : 1024 - (k+1) = 1023 - k := by omega
    rw [h1023]
    have hb1 : thetaK (1024 - k) ≤ 2 * Real.pi * 244 / 1024 := by
      have h := thetaK_mono (by omega : 1024 - k ≤ 244)
      have h244 : thetaK 244 = 2 * Real.pi * 244 / 1024 := by unfold thetaK; push_cast; ring
      linarith
    have hb2 : thetaK (1024 - k) - thetaK (1023 - k) ≤ 2 * Real.pi / 1024 := by
      have hsk : thetaK (1024 - k) = thetaK (1023 - k) + 2 * Real.pi / 1024 := by
        have hs := thetaK_succ (1023 - k)
        have heq : 1023 - k + 1 = 1024 - k := by omega
        rw [heq] at hs
        linarith
      linarith
    have := DAux.PhiSteps.1 (thetaK (1023 - k)) (thetaK (1024 - k)) (thetaK_nonneg _)
      (thetaK_mono (by omega)) hb1 hb2
    linarith
  have hdist := DistSpec.2.1 (ptOf k) (ptOf (k+1))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ))))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ))))
      (small_ptOf k (by omega)) (small_ptOf (k+1) (by omega))
      (ptOf_mem_thetaK k (by omega)) (ptOf_mem_thetaK (k+1) (by omega))
  have h34 : ‖(3/4 : ℂ)‖ = 3/4 := by
    rw [show (3/4 : ℂ) = ((3/4 : ℝ) : ℂ) by norm_num, norm_ofReal_daux,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4)]
  have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ))) -
      Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ)))‖ =
      (3/4) * ‖Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK (1024 - k)) : ℝ) : ℂ)) -
        Complex.exp (Complex.I *
          ((4 * Real.pi - phiR (thetaK (1024 - (k+1))) : ℝ) : ℂ))‖ := by
    rw [psiC_eq_smul_exp4 (thetaK_mem_Ioo_C1b (by omega) (by omega)),
      psiC_eq_smul_exp4 (thetaK_mem_Ioo_C1b (by omega) (by omega))]
    rw [two_pi_sub_thetaK hk1024, two_pi_sub_thetaK (by omega : k+1 ≤ 1024)]
    rw [← mul_sub, norm_mul, h34]
  have hDW : ‖Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK (1024 - k)) : ℝ) : ℂ)) -
      Complex.exp (Complex.I *
        ((4 * Real.pi - phiR (thetaK (1024 - (k+1))) : ℝ) : ℂ))‖ ≤
      m2r (dWup (ptOf k) (ptOf (k+1))) := by
    rw [hnorm] at hdist
    nlinarith [hdist]
  have hstep2 : (4 * Real.pi - phiR (thetaK (1024 - (k+1)))) -
      (4 * Real.pi - phiR (thetaK (1024 - k))) ≤
      m2r (dWup (ptOf k) (ptOf (k+1))) + (m2r (dWup (ptOf k) (ptOf (k+1))))^3/12 +
        4096/(SC:ℝ) := by
    have h := arc_le_chord (a := 4 * Real.pi - phiR (thetaK (1024 - k)))
      (b := 4 * Real.pi - phiR (thetaK (1024 - (k+1)))) hΔ0 hstep
    have h3 : ‖Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK (1024 - k)) : ℝ) : ℂ)) -
        Complex.exp (Complex.I *
          ((4 * Real.pi - phiR (thetaK (1024 - (k+1))) : ℝ) : ℂ))‖^3/12 ≤
        (m2r (dWup (ptOf k) (ptOf (k+1))))^3/12 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW 3) (by norm_num)
    linarith [h, h3]
  have hD := chord1_ineq hD0 hΔ0 hstep2
  have hmin : min (m2r (svDn (ptOf k))) (m2r (svDn (ptOf (k+1)))) ≤
      min (Hfun (4 * Real.pi - phiR (thetaK (1024 - k))))
        (Hfun (4 * Real.pi - phiR (thetaK (1024 - (k+1))))) := min_le_min hga hgb
  have hcl' : Hfun (4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t)) =
      Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := hcl.symm
  linarith [hmin, hchord, hD, hcl']

lemma h34norm : ‖(3/4 : ℂ)‖ = 3/4 := by
  rw [show (3/4 : ℂ) = ((3/4 : ℝ) : ℂ) by norm_num, norm_ofReal_daux,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4)]

theorem arcStepC2 (k : ℕ) (h1 : 245 ≤ k) (h2 : k ≤ 778) :
    ∀ t ∈ Set.Icc ((k:ℝ)/1024) (((k:ℝ)+1)/1024),
      m2r (gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  intro t ht
  rw [Set.mem_Icc] at ht
  have hgv : gv k = min (svDn (ptOf k)) (svDn (ptOf (k+1))) -
      chord2 (dVup (ptOf k) (ptOf (k+1))) := by
    rw [gv]
    simp only [if_neg (by omega : ¬ k ≤ 243), if_neg (by omega : k ≠ 244), if_pos h2]
  rw [hgv, m2r_sub, DAux_m2r_min]
  have hmemk : thetaK k ∈ Set.Ioo alpR (2 * Real.pi - alpR) := thetaK_mem_Ioo_C2 h1 (by omega)
  have hmemk1 : thetaK (k+1) ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
    thetaK_mem_Ioo_C2 (by omega) (by omega)
  have hga : m2r (svDn (ptOf k)) ≤ Jfun (psiArg (thetaK k)) := by
    have h := gridDn k (by omega)
    rw [Jfun_grid h1 (by omega)] at h
    exact h
  have hgb : m2r (svDn (ptOf (k+1))) ≤ Jfun (psiArg (thetaK (k+1))) := by
    have h := gridDn (k+1) (by omega)
    rw [Jfun_grid (by omega) (by omega)] at h
    exact h
  have hθ1 : thetaK k ≤ 2 * Real.pi * t := by
    unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.1]
  have hθ2 : 2 * Real.pi * t ≤ thetaK (k+1) := by
    unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.2]
  have hmemt : 2 * Real.pi * t ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
    ⟨by linarith [hmemk.1, hθ1], by linarith [hmemk1.2, hθ2]⟩
  have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
      Jfun (psiArg (2 * Real.pi * t)) := by
    have h := cl_eq_Jfun_of_mem hmemt
    rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
  have hmemψ : psiArg (2 * Real.pi * t) ∈ Set.Icc (psiArg (thetaK (k+1))) (psiArg (thetaK k)) := by
    constructor
    · exact psiArg_le_of_lt hmemt.1 hmemk1.2 hθ2
    · exact psiArg_le_of_lt hmemk.1 hmemt.2 hθ1
  have hmono : psiArg (thetaK (k+1)) ≤ psiArg (thetaK k) :=
    psiArg_le_of_lt hmemk.1 hmemk1.2 (thetaK_mono (by omega))
  have ha : -3.9 ≤ psiArg (thetaK (k+1)) :=
    (PsiRange (le_of_lt hmemk1.1) (le_of_lt hmemk1.2)).1
  have hb : psiArg (thetaK k) ≤ -2.39 :=
    (PsiRange (le_of_lt hmemk.1) (le_of_lt hmemk.2)).2
  have hJ := DAux.Jlow hmono ha hb (psiArg (2 * Real.pi * t)) hmemψ
  have hΔ0 : 0 ≤ psiArg (thetaK k) - psiArg (thetaK (k+1)) := by linarith
  have hD0 : 0 ≤ m2r (dVup (ptOf k) (ptOf (k+1))) := m2r_dVup_nonneg _ _
  have hstep : psiArg (thetaK k) - psiArg (thetaK (k+1)) ≤ 1 := by
    have hk245 : 2 * Real.pi * 245 / 1024 ≤ thetaK k := by
      have hm := thetaK_mono h1
      have h245 : thetaK 245 = 2 * Real.pi * 245 / 1024 := by unfold thetaK; push_cast; ring
      linarith
    have hb1 : thetaK (k+1) ≤ 2 * Real.pi * 779 / 1024 := by
      have hm := thetaK_mono (by omega : k+1 ≤ 779)
      have h779 : thetaK 779 = 2 * Real.pi * 779 / 1024 := by unfold thetaK; push_cast; ring
      linarith
    have hb2 : thetaK (k+1) - thetaK k ≤ 2 * Real.pi / 1024 := le_of_eq (thetaK_succ k)
    have h := DAux.PsiSteps.1 (thetaK k) (thetaK (k+1)) hk245 (thetaK_mono (by omega)) hb1 hb2
    simpa [psiArg] using h
  have hdist := DistSpec.2.2.1 (ptOf k) (ptOf (k+1))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ))))
      (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ))))
      (small_ptOf k (by omega)) (small_ptOf (k+1) (by omega))
      (ptOf_mem_thetaK k (by omega)) (ptOf_mem_thetaK (k+1) (by omega))
  have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK (k+1) : ℂ))) -
      Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK k : ℂ)))‖ =
      (115/143) * ‖Complex.exp (Complex.I * ((psiArg (thetaK (k+1)) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((psiArg (thetaK k) : ℝ) : ℂ))‖ := by
    rw [psiC_eq_wf hmemk1, psiC_eq_wf hmemk]
    rw [wf_sub, norm_mul, norm_ofReal_daux, uJ, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 115/143)]
    simp only [psiArg]
  have hDW : ‖Complex.exp (Complex.I * ((psiArg (thetaK (k+1)) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((psiArg (thetaK k) : ℝ) : ℂ))‖ ≤
      m2r (dVup (ptOf k) (ptOf (k+1))) := by
    have h := hdist
    rw [norm_sub_rev] at h
    rw [hnorm] at h
    nlinarith [h]
  have hstep2 : psiArg (thetaK k) - psiArg (thetaK (k+1)) ≤
      m2r (dVup (ptOf k) (ptOf (k+1))) + (m2r (dVup (ptOf k) (ptOf (k+1))))^3/12 +
        4096/(SC:ℝ) := by
    have h := arc_le_chord (a := psiArg (thetaK (k+1))) (b := psiArg (thetaK k)) hΔ0 hstep
    have h3 : ‖Complex.exp (Complex.I * ((psiArg (thetaK (k+1)) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((psiArg (thetaK k) : ℝ) : ℂ))‖^3/12 ≤
        (m2r (dVup (ptOf k) (ptOf (k+1))))^3/12 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW 3) (by norm_num)
    linarith [h, h3]
  have hD := chord2_ineq hD0 hΔ0 hstep2
  have hmin : min (m2r (svDn (ptOf k))) (m2r (svDn (ptOf (k+1)))) ≤
      min (Jfun (psiArg (thetaK (k+1)))) (Jfun (psiArg (thetaK k))) :=
    le_trans (le_of_eq (min_comm _ _)) (min_le_min hgb hga)
  have hcl' : Jfun (psiArg (2 * Real.pi * t)) =
      Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := hcl.symm
  linarith [hmin, hJ, hD, hcl']

theorem arcStepCuspA : ∀ t ∈ Set.Icc ((244:ℝ)/1024) (((244:ℝ)+1)/1024),
    m2r (gv 244) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  intro t ht
  rw [Set.mem_Icc] at ht
  have hgv : gv 244 = min (min (svDn (ptOf 244)) (svDn ptCuspA))
      (min (svDn (ptOf 245)) (svDn ptCuspA)) -
      max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA)) := by
    have h1 : ¬ (244:ℕ) ≤ 243 := by norm_num
    have h2 : (244:ℕ) = 244 := rfl
    rw [gv, if_neg h1, if_pos h2]
  rw [hgv, m2r_sub, DAux_m2r_max]
  simp only [DAux_m2r_min]
  have hga : m2r (svDn (ptOf 244)) ≤ Hfun (phiR (thetaK 244)) := by
    have h := gridDn 244 (by norm_num)
    rw [cl_grid_Hfun (j := 244) (by norm_num)] at h
    exact h
  have hgb : m2r (svDn ptCuspA) ≤ Hfun cuspAngA := cuspADn'
  have hgc : m2r (svDn (ptOf 245)) ≤ Jfun (psiArg (thetaK 245)) := by
    have h := gridDn 245 (by norm_num)
    rw [Jfun_grid (by norm_num) (by norm_num)] at h
    exact h
  have hM0 : 0 ≤ max (m2r (chord1 (dWup (ptOf 244) ptCuspA)))
      (m2r (chord2 (dVup (ptOf 245) ptCuspA))) := by
    have h1 : (0:ℝ) ≤ m2r (chord1 (dWup (ptOf 244) ptCuspA)) := by
      have hspec := ChordSpec.1 (dWup (ptOf 244) ptCuspA) (m2r_dWup_nonneg _ _)
      have hpos : (0:ℝ) ≤ 400 * (m2r (dWup (ptOf 244) ptCuspA) +
          (m2r (dWup (ptOf 244) ptCuspA))^3/12 + 4096/(SC:ℝ))^2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      linarith
    exact le_trans h1 (le_max_left _ _)
  by_cases hlt : 2 * Real.pi * t < alpR
  · -- first arc side
    have hθ0 : 0 ≤ 2 * Real.pi * t := by
      have : 0 ≤ t := by linarith [ht.1]
      nlinarith [Real.pi_pos]
    have hmemt : 2 * Real.pi * t ∈ Set.Ioo (-alpR) alpR := ⟨by linarith [alpR_pos], hlt⟩
    have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
        Hfun (phiR (2 * Real.pi * t)) := by
      have h := cl_eq_Hfun_of_mem hmemt
      rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
    have hArith : phiR (2 * Real.pi * t) ≤ cuspAngA := by
      have h1 : phiR (2 * Real.pi * t) < (2 * Real.pi * t)/2 + 3 * Real.pi/2 := by
        unfold phiR
        have := Real.arctan_lt_pi_div_two (QR (2 * Real.pi * t) / PR (2 * Real.pi * t))
        linarith
      have h2 : (2 * Real.pi * t)/2 ≤ alpR/2 := by linarith
      rw [cuspAngA]; linarith
    have hmono : phiR (thetaK 244) ≤ cuspAngA := by
      have h1 : phiR (thetaK 244) < thetaK 244/2 + 3 * Real.pi/2 := by
        unfold phiR
        have := Real.arctan_lt_pi_div_two (QR (thetaK 244) / PR (thetaK 244))
        linarith
      have h2 : thetaK 244/2 ≤ alpR/2 := by linarith [le_of_lt theta244_lt_alpR]
      rw [cuspAngA]; linarith
    have hmem244 : thetaK 244 ∈ Set.Ioo (-alpR) alpR :=
      mem_Ioo_of_le_theta244 (thetaK_nonneg 244) (le_refl _)
    have hAk_le : thetaK 244 ≤ 2 * Real.pi * t := by
      unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.1]
    have hmemφ : phiR (2 * Real.pi * t) ∈ Set.Icc (phiR (thetaK 244)) cuspAngA :=
      ⟨phi_strictMono.monotoneOn hmem244 hmemt hAk_le, hArith⟩
    have hchord := Hfun_chord_lower hmono (phiR (2 * Real.pi * t)) hmemφ
    have hΔ0 : 0 ≤ cuspAngA - phiR (thetaK 244) := by linarith
    have hstep : cuspAngA - phiR (thetaK 244) ≤ 1 := DAux.PhiSteps.2
    have hdist := DistSpec.2.1 (ptOf 244) ptCuspA
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 244 : ℂ))))
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))))
        (small_ptOf 244 (by norm_num)) small_ptOf_cusp.1
        (ptOf_mem_thetaK 244 (by norm_num)) CuspPoints.1
    have hmem244' : thetaK 244 ∈ Set.Ioo (-alpR) alpR :=
      mem_Ioo_of_le_theta244 (thetaK_nonneg 244) (le_refl _)
    have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 244 : ℂ))) -
        Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ)))‖ =
        (3/4) * ‖Complex.exp (Complex.I * ((phiR (thetaK 244) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (cuspAngA : ℂ))‖ := by
      rw [psiC_eq_smul_exp hmem244', psiC_cuspA_ang, ← mul_sub, norm_mul, h34norm]
    have hDW : ‖Complex.exp (Complex.I * ((phiR (thetaK 244) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * (cuspAngA : ℂ))‖ ≤ m2r (dWup (ptOf 244) ptCuspA) := by
      rw [hnorm] at hdist
      nlinarith [hdist]
    have hD0 : 0 ≤ m2r (dWup (ptOf 244) ptCuspA) := m2r_dWup_nonneg _ _
    have hstep2 : cuspAngA - phiR (thetaK 244) ≤ m2r (dWup (ptOf 244) ptCuspA) +
        (m2r (dWup (ptOf 244) ptCuspA))^3/12 + 4096/(SC:ℝ) := by
      have h := arc_le_chord (a := phiR (thetaK 244)) (b := cuspAngA) hΔ0 hstep
      have h3 : ‖Complex.exp (Complex.I * ((phiR (thetaK 244) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (cuspAngA : ℂ))‖^3/12 ≤
          (m2r (dWup (ptOf 244) ptCuspA))^3/12 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW 3) (by norm_num)
      linarith [h, h3]
    have hD1 := chord1_ineq hD0 hΔ0 hstep2
    have hmax1 : m2r (chord1 (dWup (ptOf 244) ptCuspA)) ≤
        max (m2r (chord1 (dWup (ptOf 244) ptCuspA)))
          (m2r (chord2 (dVup (ptOf 245) ptCuspA))) := le_max_left _ _
    have hmin1 : min (min (m2r (svDn (ptOf 244))) (m2r (svDn ptCuspA)))
        (min (m2r (svDn (ptOf 245))) (m2r (svDn ptCuspA))) ≤
        min (Hfun (phiR (thetaK 244))) (Hfun cuspAngA) :=
      le_trans (min_le_left _ _) (min_le_min hga hgb)
    linarith [hmin1, hchord, hD1, hmax1, hcl]
  · by_cases hgt : alpR < 2 * Real.pi * t
    · -- second arc side
      have hθ1 : 2 * Real.pi * t ≤ thetaK 245 := by
        unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.2]
      have hmemt : 2 * Real.pi * t ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
        ⟨hgt, by
          have := (thetaK_mem_Ioo_C2 (by norm_num : 245 ≤ 245) (by norm_num : 245 ≤ 779)).2
          linarith⟩
      have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
          Jfun (psiArg (2 * Real.pi * t)) := by
        have h := cl_eq_Jfun_of_mem hmemt
        rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
      have hmem245 : thetaK 245 ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
        thetaK_mem_Ioo_C2 (by norm_num) (by norm_num)
      have hmemψ : psiArg (2 * Real.pi * t) ∈ Set.Icc (psiArg (thetaK 245))
          (psiArg alpR) := by
        constructor
        · exact psiArg_le_of_lt hgt hmem245.2 hθ1
        · exact psiArg_le_cuspA (le_of_lt hgt) (by
            have h245 : thetaK 245 ≤ 1.50331 := by unfold thetaK; nlinarith [Real.pi_lt_d6]
            linarith [hθ1, AlpBound.1, Real.pi_gt_d6])
      have hmono : psiArg (thetaK 245) ≤ psiArg alpR :=
        psiArg_le_cuspA (le_of_lt hmem245.1) (by
          have h245 : thetaK 245 ≤ 1.50331 := by unfold thetaK; nlinarith [Real.pi_lt_d6]
          linarith [AlpBound.1, Real.pi_gt_d6])
      have ha : -3.9 ≤ psiArg (thetaK 245) :=
        (PsiRange (le_of_lt hmem245.1) (le_of_lt hmem245.2)).1
      have hb : psiArg alpR ≤ -2.39 :=
        (PsiRange (le_refl alpR) (by linarith [alpR_pos, alpR_lt_pi])).2
      have hJ := DAux.Jlow hmono ha hb (psiArg (2 * Real.pi * t)) hmemψ
      have hΔ0 : 0 ≤ psiArg alpR - psiArg (thetaK 245) := by linarith
      have hstep : psiArg alpR - psiArg (thetaK 245) ≤ 1 := by
        have h := DAux.PsiSteps.2.1
        simpa [psiArg, thetaK] using h
      have hdist := DistSpec.2.2.1 (ptOf 245) ptCuspA
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 245 : ℂ))))
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))))
          (small_ptOf 245 (by norm_num)) small_ptOf_cusp.1
          (ptOf_mem_thetaK 245 (by norm_num)) CuspPoints.1
      have h1 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 245 : ℂ))) =
          wf (psiArg (thetaK 245)) := psiC_eq_wf hmem245
      have h2 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ))) =
          wf (psiArg alpR) := by rw [psiArg_alpR]; exact wf_cuspA.symm
      have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 245 : ℂ))) -
          Submission.CDTPlan.psiC (Complex.exp (Complex.I * (alpR : ℂ)))‖ =
          (115/143) * ‖Complex.exp (Complex.I * ((psiArg (thetaK 245) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((psiArg alpR : ℝ) : ℂ))‖ := by
        rw [h1, h2, wf_sub, norm_mul, norm_ofReal_daux, uJ,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 115/143)]
      have hDW : ‖Complex.exp (Complex.I * ((psiArg (thetaK 245) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((psiArg alpR : ℝ) : ℂ))‖ ≤
          m2r (dVup (ptOf 245) ptCuspA) := by
        rw [hnorm] at hdist
        nlinarith [hdist]
      have hD0 : 0 ≤ m2r (dVup (ptOf 245) ptCuspA) := m2r_dVup_nonneg _ _
      have hstep2 : psiArg alpR - psiArg (thetaK 245) ≤ m2r (dVup (ptOf 245) ptCuspA) +
          (m2r (dVup (ptOf 245) ptCuspA))^3/12 + 4096/(SC:ℝ) := by
        have h := arc_le_chord (a := psiArg (thetaK 245)) (b := psiArg alpR) hΔ0 hstep
        have h3 : ‖Complex.exp (Complex.I * ((psiArg (thetaK 245) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((psiArg alpR : ℝ) : ℂ))‖^3/12 ≤
            (m2r (dVup (ptOf 245) ptCuspA))^3/12 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW 3) (by norm_num)
        linarith [h, h3]
      have hD2 := chord2_ineq hD0 hΔ0 hstep2
      have hmax2 : m2r (chord2 (dVup (ptOf 245) ptCuspA)) ≤
          max (m2r (chord1 (dWup (ptOf 244) ptCuspA)))
            (m2r (chord2 (dVup (ptOf 245) ptCuspA))) := le_max_right _ _
      have hC' : m2r (svDn ptCuspA) ≤ Jfun (psiArg alpR) := by
        rw [Jfun_cuspA']; exact hgb
      have hmin2 : min (min (m2r (svDn (ptOf 244))) (m2r (svDn ptCuspA)))
          (min (m2r (svDn (ptOf 245))) (m2r (svDn ptCuspA))) ≤
          min (Jfun (psiArg (thetaK 245))) (Jfun (psiArg alpR)) :=
        le_trans (min_le_right _ _) (min_le_min hgc hC')
      linarith [hmin2, hJ, hD2, hmax2, hcl]
    · -- the cusp itself
      have hθeq : 2 * Real.pi * t = alpR := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t = Hfun cuspAngA := by
        have ht' : t = alpR / (2 * Real.pi) := by
          field_simp
          linarith
        rw [ht', cl_cuspA]
      have hmin1 : min (min (m2r (svDn (ptOf 244))) (m2r (svDn ptCuspA)))
          (min (m2r (svDn (ptOf 245))) (m2r (svDn ptCuspA))) ≤ Hfun cuspAngA :=
        le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hgb
      linarith [hmin1, hcl, hM0]

theorem arcStepCuspB : ∀ t ∈ Set.Icc ((779:ℝ)/1024) (((779:ℝ)+1)/1024),
    m2r (gv 779) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  intro t ht
  rw [Set.mem_Icc] at ht
  have hgv : gv 779 = min (min (svDn (ptOf 779)) (svDn ptCuspB))
      (min (svDn (ptOf 780)) (svDn ptCuspB)) -
      max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB)) := by
    have h1 : ¬ (779:ℕ) ≤ 243 := by norm_num
    have h2 : (779:ℕ) ≠ 244 := by norm_num
    have h3 : ¬ (779:ℕ) ≤ 778 := by norm_num
    have h4 : (779:ℕ) = 779 := rfl
    rw [gv, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  rw [hgv, m2r_sub, DAux_m2r_max]
  simp only [DAux_m2r_min]
  have hga : m2r (svDn (ptOf 779)) ≤ Jfun (psiArg (thetaK 779)) := by
    have h := gridDn 779 (by norm_num)
    rw [Jfun_grid (by norm_num) (by norm_num)] at h
    exact h
  have hgb : m2r (svDn ptCuspB) ≤ Hfun (4 * Real.pi - cuspAngA) := cuspBDn'
  have hgbJ : m2r (svDn ptCuspB) ≤ Jfun (psiArg (2 * Real.pi - alpR)) := by
    rw [Jfun_cuspB']; exact hgb
  have hgc : m2r (svDn (ptOf 780)) ≤ Hfun (4 * Real.pi - phiR (thetaK 244)) := by
    have h := gridDn 780 (by norm_num)
    rw [cl_grid_Hfun4 (by norm_num) (by norm_num)] at h
    rwa [show 1024 - 780 = 244 by norm_num] at h
  have hM0 : 0 ≤ max (m2r (chord2 (dVup (ptOf 779) ptCuspB)))
      (m2r (chord1 (dWup (ptOf 780) ptCuspB))) := by
    have h1 : (0:ℝ) ≤ m2r (chord2 (dVup (ptOf 779) ptCuspB)) := by
      have hspec := ChordSpec.2 (dVup (ptOf 779) ptCuspB) (m2r_dVup_nonneg _ _)
      have hpos : (0:ℝ) ≤ 1000 * (m2r (dVup (ptOf 779) ptCuspB) +
          (m2r (dVup (ptOf 779) ptCuspB))^3/12 + 4096/(SC:ℝ))^2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      linarith
    exact le_trans h1 (le_max_left _ _)
  have h779 : thetaK 779 ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
    thetaK_mem_Ioo_C2 (by norm_num) (by norm_num)
  have hθ_lo : thetaK 779 ≤ 2 * Real.pi * t := by
    unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.1]
  have hθ_hi : 2 * Real.pi * t ≤ thetaK 780 := by
    unfold thetaK; push_cast; nlinarith [Real.pi_pos, ht.2]
  have hbig : (4.77:ℝ) ≤ thetaK 779 := by unfold thetaK; push_cast; nlinarith [Real.pi_gt_d6]
  by_cases hlt : 2 * Real.pi * t < 2 * Real.pi - alpR
  · -- second arc side
    have hmemt : 2 * Real.pi * t ∈ Set.Ioo alpR (2 * Real.pi - alpR) :=
      ⟨by linarith [h779.1, hθ_lo], hlt⟩
    have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
        Jfun (psiArg (2 * Real.pi * t)) := by
      have h := cl_eq_Jfun_of_mem hmemt
      rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
    have hmemψ : psiArg (2 * Real.pi * t) ∈ Set.Icc (psiArg (2 * Real.pi - alpR))
        (psiArg (thetaK 779)) := by
      constructor
      · exact psiArg_ge_cuspB (by linarith [hθ_lo, hbig, AlpBound.1, Real.pi_lt_d6]) (le_of_lt hlt)
      · exact psiArg_le_of_lt h779.1 hlt hθ_lo
    have hmono : psiArg (2 * Real.pi - alpR) ≤ psiArg (thetaK 779) :=
      psiArg_ge_cuspB (by linarith [hbig, AlpBound.1, Real.pi_lt_d6]) (le_of_lt h779.2)
    have ha : -3.9 ≤ psiArg (2 * Real.pi - alpR) :=
      (PsiRange (by linarith [alpR_pos, alpR_lt_pi]) (le_refl _)).1
    have hb : psiArg (thetaK 779) ≤ -2.39 :=
      (PsiRange (le_of_lt h779.1) (le_of_lt h779.2)).2
    have hJ := DAux.Jlow hmono ha hb (psiArg (2 * Real.pi * t)) hmemψ
    have hΔ0 : 0 ≤ psiArg (thetaK 779) - psiArg (2 * Real.pi - alpR) := by linarith
    have hstep : psiArg (thetaK 779) - psiArg (2 * Real.pi - alpR) ≤ 1 := by
      have h := DAux.PsiSteps.2.2
      simpa [psiArg, thetaK] using h
    have hdist := DistSpec.2.2.1 (ptOf 779) ptCuspB
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 779 : ℂ))))
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))))
        (small_ptOf 779 (by norm_num)) small_ptOf_cusp.2
        (ptOf_mem_thetaK 779 (by norm_num)) (by
          have h := CuspPoints.2
          rwa [show Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ))) =
            Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) by
            simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]] at h)
    have h1 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 779 : ℂ))) =
        wf (psiArg (thetaK 779)) := psiC_eq_wf h779
    have h2 : Submission.CDTPlan.psiC
        (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) =
        wf (psiArg (2 * Real.pi - alpR)) := by
      rw [psiArg_cuspB]; exact wf_cuspB_aux.symm
    have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 779 : ℂ))) -
        Submission.CDTPlan.psiC
          (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)))‖ =
        (115/143) * ‖Complex.exp (Complex.I * ((psiArg (thetaK 779) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((psiArg (2 * Real.pi - alpR) : ℝ) : ℂ))‖ := by
      rw [h1, h2, wf_sub, norm_mul, norm_ofReal_daux, uJ,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 115/143)]
    have hDW : ‖Complex.exp (Complex.I * ((psiArg (thetaK 779) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((psiArg (2 * Real.pi - alpR) : ℝ) : ℂ))‖ ≤
        m2r (dVup (ptOf 779) ptCuspB) := by
      rw [hnorm] at hdist
      nlinarith [hdist]
    have hD0 : 0 ≤ m2r (dVup (ptOf 779) ptCuspB) := m2r_dVup_nonneg _ _
    have hstep2 : psiArg (thetaK 779) - psiArg (2 * Real.pi - alpR) ≤
        m2r (dVup (ptOf 779) ptCuspB) + (m2r (dVup (ptOf 779) ptCuspB))^3/12 +
          4096/(SC:ℝ) := by
      have hDW' : ‖Complex.exp (Complex.I * ((psiArg (2 * Real.pi - alpR) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((psiArg (thetaK 779) : ℝ) : ℂ))‖ ≤
          m2r (dVup (ptOf 779) ptCuspB) := by
        rw [norm_sub_rev]; exact hDW
      have h := arc_le_chord (a := psiArg (2 * Real.pi - alpR)) (b := psiArg (thetaK 779))
        hΔ0 hstep
      have h3 : ‖Complex.exp (Complex.I * ((psiArg (2 * Real.pi - alpR) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((psiArg (thetaK 779) : ℝ) : ℂ))‖^3/12 ≤
          (m2r (dVup (ptOf 779) ptCuspB))^3/12 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW' 3) (by norm_num)
      linarith [h, h3]
    have hD := chord2_ineq hD0 hΔ0 hstep2
    have hmax2 : m2r (chord2 (dVup (ptOf 779) ptCuspB)) ≤
        max (m2r (chord2 (dVup (ptOf 779) ptCuspB)))
          (m2r (chord1 (dWup (ptOf 780) ptCuspB))) := le_max_left _ _
    have hmin : min (min (m2r (svDn (ptOf 779))) (m2r (svDn ptCuspB)))
        (min (m2r (svDn (ptOf 780))) (m2r (svDn ptCuspB))) ≤
        min (Jfun (psiArg (2 * Real.pi - alpR))) (Jfun (psiArg (thetaK 779))) := by
      refine le_trans (min_le_left _ _) ?_
      rw [min_comm (m2r (svDn (ptOf 779))) (m2r (svDn ptCuspB))]
      exact min_le_min hgbJ hga
    linarith [hmin, hJ, hD, hmax2, hcl]
  · by_cases hgt : 2 * Real.pi - alpR < 2 * Real.pi * t
    · -- fourth arc side
      have hmemt : 2 * Real.pi * t - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR := by
        have h780' : thetaK 780 = 2 * Real.pi - thetaK 244 := by
          have h := two_pi_sub_thetaK (by norm_num : 244 ≤ 1024)
          rw [show 1024 - 244 = 780 by norm_num] at h
          exact h.symm
        constructor
        · linarith
        · have : 2 * Real.pi * t - 2 * Real.pi ≤ -thetaK 244 := by linarith
          linarith [theta244_lt_alpR, alpR_pos, thetaK_nonneg 244]
      have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
          Hfun (4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t)) := by
        have h := cl_eq_Hfun4_of_mem hmemt
        rwa [show (2 * Real.pi * t) / (2 * Real.pi) = t by field_simp] at h
      have hcomp : thetaK 244 ≤ 2 * Real.pi - 2 * Real.pi * t := by
        have h780' : thetaK 780 = 2 * Real.pi - thetaK 244 := by
          have h := two_pi_sub_thetaK (by norm_num : 244 ≤ 1024)
          rw [show 1024 - 244 = 780 by norm_num] at h
          exact h.symm
        linarith
      have hArith : phiR (2 * Real.pi - 2 * Real.pi * t) ≤ cuspAngA := by
        have h1 : phiR (2 * Real.pi - 2 * Real.pi * t) <
            (2 * Real.pi - 2 * Real.pi * t)/2 + 3 * Real.pi/2 := by
          unfold phiR
          have := Real.arctan_lt_pi_div_two (QR (2 * Real.pi - 2 * Real.pi * t) /
            PR (2 * Real.pi - 2 * Real.pi * t))
          linarith
        have h2 : (2 * Real.pi - 2 * Real.pi * t)/2 < alpR/2 := by
          have hlt' : 2 * Real.pi - 2 * Real.pi * t < alpR := by linarith
          linarith
        rw [cuspAngA]; linarith
      have hmono : 4 * Real.pi - cuspAngA ≤ 4 * Real.pi - phiR (thetaK 244) := by
        have h1 : phiR (thetaK 244) < thetaK 244/2 + 3 * Real.pi/2 := by
          unfold phiR
          have := Real.arctan_lt_pi_div_two (QR (thetaK 244) / PR (thetaK 244))
          linarith
        have h2 : thetaK 244/2 ≤ alpR/2 := by linarith [le_of_lt theta244_lt_alpR]
        rw [cuspAngA]; linarith
      have hmem244 : thetaK 244 ∈ Set.Ioo (-alpR) alpR :=
        mem_Ioo_of_le_theta244 (thetaK_nonneg 244) (le_refl _)
      have hAt : 2 * Real.pi - 2 * Real.pi * t ∈ Set.Ioo (-alpR) alpR :=
        ⟨by linarith [hcomp, thetaK_nonneg 244, alpR_pos], by linarith [hgt]⟩
      have hmemφ : 4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t) ∈
          Set.Icc (4 * Real.pi - cuspAngA) (4 * Real.pi - phiR (thetaK 244)) :=
        ⟨by linarith [hArith], by
          have h := phi_strictMono.monotoneOn hmem244 hAt hcomp
          linarith⟩
      have hchord := Hfun_chord_lower hmono
        (4 * Real.pi - phiR (2 * Real.pi - 2 * Real.pi * t)) hmemφ
      have hΔ0 : 0 ≤ (4 * Real.pi - phiR (thetaK 244)) - (4 * Real.pi - cuspAngA) := by
        linarith [hmono]
      have hstep : (4 * Real.pi - phiR (thetaK 244)) - (4 * Real.pi - cuspAngA) ≤ 1 := by
        have h := DAux.PhiSteps.2
        simpa [cuspAngA, thetaK] using h
      have hdist := DistSpec.2.1 (ptOf 780) ptCuspB
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 780 : ℂ))))
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))))
          (small_ptOf 780 (by norm_num)) small_ptOf_cusp.2
          (ptOf_mem_thetaK 780 (by norm_num)) (by
            have h := CuspPoints.2
            rwa [show Complex.exp (Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ))) =
              Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)) by
              simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]] at h)
      have h1 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 780 : ℂ))) =
          (3/4 : ℂ) * Complex.exp
            (Complex.I * ((4 * Real.pi - phiR (thetaK 244) : ℝ) : ℂ)) := by
        have h2pi : 2 * Real.pi - thetaK 780 = thetaK 244 := by
          have h := two_pi_sub_thetaK (by norm_num : 780 ≤ 1024)
          rwa [show 1024 - 780 = 244 by norm_num] at h
        rw [psiC_eq_smul_exp4 (thetaK_mem_Ioo_C1b (by norm_num) (by norm_num)), h2pi]
      have h2 : Submission.CDTPlan.psiC
          (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ))) =
          (3/4 : ℂ) * Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) :=
        psiC_cuspB_ang
      have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (thetaK 780 : ℂ))) -
          Submission.CDTPlan.psiC
            (Complex.exp (Complex.I * ((2 * Real.pi - alpR : ℝ) : ℂ)))‖ =
          (3/4) * ‖Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK 244) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ))‖ := by
        rw [h1, h2, ← mul_sub, norm_mul, h34norm]
      have hDW : ‖Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK 244) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ))‖ ≤
          m2r (dWup (ptOf 780) ptCuspB) := by
        rw [hnorm] at hdist
        nlinarith [hdist]
      have hD0 : 0 ≤ m2r (dWup (ptOf 780) ptCuspB) := m2r_dWup_nonneg _ _
      have hstep2 : (4 * Real.pi - phiR (thetaK 244)) - (4 * Real.pi - cuspAngA) ≤
          m2r (dWup (ptOf 780) ptCuspB) + (m2r (dWup (ptOf 780) ptCuspB))^3/12 +
            4096/(SC:ℝ) := by
        have hDW' : ‖Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK 244) : ℝ) : ℂ))‖ ≤
            m2r (dWup (ptOf 780) ptCuspB) := by
          rw [norm_sub_rev]; exact hDW
        have h := arc_le_chord (a := 4 * Real.pi - cuspAngA) (b := 4 * Real.pi - phiR (thetaK 244))
          hΔ0 hstep
        have h3 : ‖Complex.exp (Complex.I * ((4 * Real.pi - cuspAngA : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((4 * Real.pi - phiR (thetaK 244) : ℝ) : ℂ))‖^3/12 ≤
            (m2r (dWup (ptOf 780) ptCuspB))^3/12 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hDW' 3) (by norm_num)
        linarith [h, h3]
      have hD := chord1_ineq hD0 hΔ0 hstep2
      have hmax1 : m2r (chord1 (dWup (ptOf 780) ptCuspB)) ≤
          max (m2r (chord2 (dVup (ptOf 779) ptCuspB)))
            (m2r (chord1 (dWup (ptOf 780) ptCuspB))) := le_max_right _ _
      have hmin : min (min (m2r (svDn (ptOf 779))) (m2r (svDn ptCuspB)))
          (min (m2r (svDn (ptOf 780))) (m2r (svDn ptCuspB))) ≤
          min (Hfun (4 * Real.pi - cuspAngA))
            (Hfun (4 * Real.pi - phiR (thetaK 244))) := by
        refine le_trans (min_le_right _ _) ?_
        rw [min_comm (m2r (svDn (ptOf 780))) (m2r (svDn ptCuspB))]
        exact min_le_min hgb hgc
      linarith [hmin, hchord, hD, hmax1, hcl]
    · -- the cusp itself
      have hθeq : 2 * Real.pi * t = 2 * Real.pi - alpR :=
        le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      have hcl : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
          Hfun (4 * Real.pi - cuspAngA) := by
        have ht' : t = (2 * Real.pi - alpR) / (2 * Real.pi) := by
          field_simp
          linarith
        rw [ht', cl_cuspB]
      have hmin : min (min (m2r (svDn (ptOf 779))) (m2r (svDn ptCuspB)))
          (min (m2r (svDn (ptOf 780))) (m2r (svDn ptCuspB))) ≤
          Hfun (4 * Real.pi - cuspAngA) :=
        le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hgb
      linarith [hmin, hcl, hM0]

theorem ArcDnMain (k : ℕ) (hk : k < 1024) :
    ∀ t ∈ Set.Icc ((k:ℝ)/1024) (((k:ℝ)+1)/1024),
      m2r (gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t := by
  by_cases h1 : k ≤ 243
  · exact arcStepC1 k h1
  · by_cases h2 : k = 244
    · subst h2; exact arcStepCuspA
    · by_cases h3 : k ≤ 778
      · exact arcStepC2 k (by omega) h3
      · by_cases h4 : k = 779
        · subst h4; exact arcStepCuspB
        · exact arcStepC1b k (by omega) (by omega)

end Work.CNum
