import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.Jfun_defs
import Submission.Work.CNum.phi_strictMono
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.C2_clockwise
import Submission.Work.CNum.C2_ratio_eq
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.PsiRange
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.circleLog_eq_Hfun
import Submission.Work.CNum.log_norm_hauptH
import Submission.Work.CNum.AlpBound
import Submission.Work.CNum.CuspPoints
import Submission.Work.CPsi.psiC_facts
import Submission.Work.CNum.DAux.Arc4Ang

set_option maxHeartbeats 800000

namespace Work.CNum

open Work.ANum

/-- `θ_k = 2πk/1024`. -/
noncomputable def thetaK (k : ℕ) : ℝ := 2 * Real.pi * (k : ℝ) / 1024

/-- The angle of `ψ_C(e^{iθ})` in the limit `θ → α`. -/
noncomputable def cuspAngA : ℝ := alpR / 2 + 3 * Real.pi / 2
/-- The angle of `ψ_C(e^{iθ})` in the limit `θ → 2π - α`. -/
noncomputable def cuspAngB : ℝ := -(alpR / 2 + 3 * Real.pi / 2)

lemma thetaK_mono : Monotone thetaK := by
  intro a b hab
  unfold thetaK
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have : (a:ℝ)/1024 ≤ (b:ℝ)/1024 := by linarith
  nlinarith [hp]

lemma thetaK_nonneg (k : ℕ) : 0 ≤ thetaK k := by unfold thetaK; positivity

lemma thetaK_succ (k : ℕ) : thetaK (k+1) - thetaK k = 2 * Real.pi / 1024 := by
  unfold thetaK; push_cast; ring

lemma thetaK_div (k : ℕ) : thetaK k / (2 * Real.pi) = (k:ℝ)/1024 := by
  unfold thetaK; field_simp; try ring

lemma thetaK_le244 {k : ℕ} (hk : k ≤ 244) : thetaK k ≤ 61 * Real.pi / 128 := by
  have h := thetaK_mono hk
  have h244 : thetaK 244 = 61 * Real.pi / 128 := by unfold thetaK; push_cast; ring
  rwa [h244] at h

lemma theta244_lt_alpR : thetaK 244 < alpR := by
  have h := thetaK_le244 (le_refl 244)
  have h2 : (61:ℝ) * Real.pi / 128 < 1.4973 := by
    have hp := Real.pi_lt_d6
    nlinarith
  linarith [AlpBound.1]

lemma mem_Ioo_of_le_theta244 {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ thetaK 244) :
    θ ∈ Set.Ioo (-alpR) alpR := by
  have h2 : θ ≤ 61 * Real.pi / 128 := le_trans h1 (thetaK_le244 (le_refl 244))
  exact ⟨by linarith [alpR_pos], by linarith [theta244_lt_alpR]⟩

lemma lt_alpR_of_lt_theta244 {θ : ℝ} (h1 : θ ≤ thetaK 244) : θ < alpR :=
  lt_of_le_of_lt h1 theta244_lt_alpR

lemma thetaK_mem_Ioo_C2 {k : ℕ} (h1 : 245 ≤ k) (h2 : k ≤ 779) :
    thetaK k ∈ Set.Ioo alpR (2 * Real.pi - alpR) := by
  have hk1 : thetaK 245 ≤ thetaK k := thetaK_mono h1
  have hk2 : thetaK k ≤ thetaK 779 := thetaK_mono h2
  have h245 : (1.5031 : ℝ) < thetaK 245 := by
    unfold thetaK
    have hbase : (1.5031 : ℝ) < 2 * 3.141592 * (245:ℝ) / 1024 := by norm_num
    have hc : 2 * (3.141592 : ℝ) * (245:ℝ) / 1024 ≤ 2 * Real.pi * (245:ℝ) / 1024 := by
      have hpi : (3.141592:ℝ) ≤ Real.pi := Real.pi_gt_d6.le
      nlinarith
    linarith
  have h779 : thetaK 779 < 2 * Real.pi - 1.5031 := by
    have heq : thetaK 779 = 2 * Real.pi - 2 * Real.pi * (245:ℝ) / 1024 := by
      unfold thetaK; push_cast; ring
    rw [heq]
    have hbase : (1.5031 : ℝ) < 2 * 3.141592 * (245:ℝ) / 1024 := by norm_num
    have hc : 2 * (3.141592 : ℝ) * (245:ℝ) / 1024 ≤ 2 * Real.pi * (245:ℝ) / 1024 := by
      have hpi : (3.141592:ℝ) ≤ Real.pi := Real.pi_gt_d6.le
      nlinarith
    linarith
  exact ⟨by linarith [AlpBound.2], by linarith [AlpBound.2]⟩

lemma thetaK_mem_Ioo_C1b {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) :
    thetaK k - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR := by
  have hm : thetaK k - 2 * Real.pi = -(2 * Real.pi * ((1024 - k : ℕ) : ℝ) / 1024) := by
    unfold thetaK; push_cast [Nat.cast_sub h2]; ring
  have hk : 1024 - k ≤ 244 := by omega
  have hle : 2 * Real.pi * ((1024 - k : ℕ) : ℝ) / 1024 < alpR := by
    have hle' : 2 * Real.pi * ((1024 - k : ℕ) : ℝ) / 1024 ≤ 61 * Real.pi / 128 := by
      have h := thetaK_le244 hk
      unfold thetaK at h; push_cast at h; exact h
    have h3 : (61:ℝ) * Real.pi / 128 < alpR := by
      have hh : thetaK 244 = 61 * Real.pi / 128 := by unfold thetaK; push_cast; ring
      linarith [theta244_lt_alpR]
    linarith
  have hnn : 0 ≤ 2 * Real.pi * ((1024 - k : ℕ) : ℝ) / 1024 := by positivity
  constructor
  · rw [hm]; linarith
  · rw [hm]; linarith [alpR_pos]

/-- `Hfun`-form of `circleLog` on the first arc. -/
lemma cl_eq_Hfun_of_mem {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi)) = Hfun (phiR θ) :=
  circleLog_eq_Hfun h

/-- `Hfun`-form of `circleLog` at a grid point of the first arc. -/
lemma cl_grid_Hfun {j : ℕ} (hj : j ≤ 244) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC ((j:ℝ)/1024) = Hfun (phiR (thetaK j)) := by
  have h := cl_eq_Hfun_of_mem (mem_Ioo_of_le_theta244 (thetaK_nonneg j) (thetaK_mono hj))
  rwa [thetaK_div] at h

/-- `ψ_C(e^{iθ}) = (3/4) e^{i φ(θ)}` on the first arc. -/
lemma psiC_eq_smul_exp {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) =
      (3 / 4 : ℂ) * Complex.exp (Complex.I * (phiR θ : ℂ)) := by
  rw [psiC_eq_threequarters_Wfun, ← exp_phi_eq h]

/-- `ψ_C(e^{iθ}) = (3/4) e^{i φ~}` on the fourth arc. -/
lemma psiC_eq_smul_exp4 {θ : ℝ} (h : θ - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR) :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) =
      (3 / 4 : ℂ) * Complex.exp (Complex.I * ((4 * Real.pi - phiR (2 * Real.pi - θ) : ℝ) : ℂ)) :=
  DAux.Arc4Ang h

/-- `Hfun`-form of `circleLog` on the fourth arc. -/
lemma cl_eq_Hfun4_of_mem {θ : ℝ} (h : θ - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi)) =
      Hfun (4 * Real.pi - phiR (2 * Real.pi - θ)) := by
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((θ / (2 * Real.pi) : ℝ)) : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    congr 1
    push_cast
    field_simp
    try ring
  rw [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, hexp, psiC_eq_smul_exp4 h,
    log_norm_hauptH_circle]

/-- `psiC (e^{iθ}) = wf (C2Psi (θ/2) - π)` on the second arc. -/
lemma psiC_eq_wf {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) = wf (C2Psi (θ / 2) - Real.pi) := by
  have hVof : Vof θ = - Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) := by
    rw [C2_Vof_explicit h, C2_ratio_eq h]
  have hne : (Real.sqrt rho2sq : ℂ) ≠ 0 := by
    rw [sqrt_rho2sq]; norm_num
  have hpsiC : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) =
      (cenC2 : ℂ) + (Real.sqrt rho2sq : ℂ) * Vof θ := by
    rw [psiC_eq_threequarters_Wfun]
    unfold Vof
    field_simp
    try ring
  have hexp : Complex.exp (Complex.I * (((C2Psi (θ / 2) - Real.pi : ℝ)) : ℂ)) =
      - Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) := by
    have h1 : ((C2Psi (θ / 2) - Real.pi : ℝ) : ℂ) =
        (C2Psi (θ / 2) : ℂ) - (Real.pi : ℂ) := by push_cast; ring
    have hpi : Complex.exp (Complex.I * (-(Real.pi : ℂ))) = -1 := by
      rw [show Complex.I * (-(Real.pi : ℂ)) = -((Real.pi : ℂ) * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h1, show Complex.I * ((C2Psi (θ / 2) : ℂ) - (Real.pi : ℂ)) =
      Complex.I * (C2Psi (θ / 2) : ℂ) + Complex.I * (-(Real.pi : ℂ)) by ring,
      Complex.exp_add, hpi]
    ring
  have hcJ : ((cJ : ℝ) : ℂ) = (cenC2 : ℂ) := by rw [cJ, cenC2_eq]
  have huJ : ((uJ : ℝ) : ℂ) = (Real.sqrt rho2sq : ℂ) := by rw [uJ, sqrt_rho2sq]
  rw [hpsiC, wf, hcJ, huJ, hexp, hVof]

lemma C2Psi_alpR_half : C2Psi (alpR / 2) = alpR / 2 := by
  unfold C2Psi
  rw [cos_half_alpR, div_self C2C_ne_zero, Real.arcsin_one]
  ring

/-- `wf ψ = log ‖h‖` identity: `Jfun ψ = log ‖h (wf ψ)‖`. -/
lemma Jfun_eq_log_norm' {ψ : ℝ} (h1 : ‖wf ψ‖ ≤ 3 / 4) (h2 : wf ψ ≠ 0) :
    Jfun ψ = Real.log ‖Submission.CDTPlan.hauptH (wf ψ)‖ := by
  have hwf : wf ψ = (cenC2 : ℂ) + (Real.sqrt rho2sq : ℂ) * Complex.exp (Complex.I * (ψ : ℂ)) := by
    rw [wf]
    have h1' : (cJ : ℂ) = (cenC2 : ℂ) := by rw [cJ, cenC2_eq]
    have h2' : (uJ : ℂ) = (Real.sqrt rho2sq : ℂ) := by rw [uJ, sqrt_rho2sq]
    rw [h1', h2']
  rw [show Jfun ψ = Real.log 256 + Real.log ‖(cenC2 : ℂ) +
        (Real.sqrt rho2sq : ℂ) * Complex.exp (Complex.I * (ψ : ℂ))‖ +
        ∑' n : ℕ, 24 * Real.log ‖1 + ((cenC2 : ℂ) +
          (Real.sqrt rho2sq : ℂ) * Complex.exp (Complex.I * (ψ : ℂ))) ^ (n + 1)‖ from rfl]
  rw [← hwf, log_norm_hauptH h1 h2]

/-- `circleLog` at a second-arc point, in `Jfun` form. -/
lemma cl_eq_Jfun_of_mem {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi)) =
      Jfun (C2Psi (θ / 2) - Real.pi) := by
  have hθexp : ‖Complex.exp (Complex.I * (θ : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]; simp
  have hne : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hn : ‖wf (C2Psi (θ / 2) - Real.pi)‖ ≤ 3 / 4 := by
    rw [← psiC_eq_wf h]
    exact Work.CPsi.psiC_norm_le hθexp
  have hne' : wf (C2Psi (θ / 2) - Real.pi) ≠ 0 := by
    rw [← psiC_eq_wf h]
    exact fun h0 => hne (Work.CPsi.psiC_eq_zero h0)
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((θ / (2 * Real.pi) : ℝ)) : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
    congr 1
    push_cast
    field_simp
    try ring
  rw [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC, hexp, psiC_eq_wf h,
    Jfun_eq_log_norm' hn hne']

lemma Jfun_grid {j : ℕ} (h1 : 245 ≤ j) (h2 : j ≤ 779) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC ((j:ℝ)/1024) =
      Jfun (C2Psi (thetaK j / 2) - Real.pi) := by
  have h := cl_eq_Jfun_of_mem (thetaK_mem_Ioo_C2 h1 h2)
  rwa [thetaK_div] at h

end Work.CNum
