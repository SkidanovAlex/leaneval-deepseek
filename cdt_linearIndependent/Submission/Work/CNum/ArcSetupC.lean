import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.BoxSideDefs
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.SerUpSpecR
import Submission.Work.CNum.DistSpec
import Submission.Work.CNum.GridFacts
import Submission.Work.CNum.PtC1Spec
import Submission.Work.CNum.PtC2Spec
import Submission.Work.CNum.PtC1bSpec
import Submission.Work.CNum.CuspPoints
import Submission.Work.CNum.PsiRange
import Submission.Work.CNum.PhiChord
import Submission.Work.CNum.PsiChord
import Submission.Work.CNum.Hfun_chord
import Submission.Work.CNum.Jfun_chord
import Submission.Work.CNum.circleLog_eq_Hfun
import Submission.Work.CNum.circleLog_eq_Jfun
import Submission.Work.CNum.phi_strictMono
import Submission.Work.CNum.C2_Psi_antitone
import Submission.Work.CNum.C2Psi_deriv_neg
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.AlpBound
import Submission.Work.CNum.ArcsinChord
import Submission.Work.CNum.log_norm_hauptH
import Submission.Work.CNum.C2VofClosed
import Submission.Work.CNum.arc_bounds
import Submission.Work.CNum.WfunArc4
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.SerTailBound
import Submission.Work.CNum.LgInfra
import Submission.Work.ANum.HLog

namespace Work.CNum

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

open Work.ANum
open Complex Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

/-! ## 0. The grid angles `θ_k = 2πk/1024` -/

/-- `θ_k = 2πk/1024 = kπ/512`, the grid angles of the `1024`-arc subdivision. -/
def arcθ (k : ℕ) : ℝ := (k : ℝ) * Real.pi / 512

lemma arcθ_alt (k : ℕ) : arcθ k = 2 * Real.pi * (k : ℝ) / 1024 := by
  rw [arcθ]; ring

lemma arcθ_mono : Monotone arcθ := by
  intro a b h
  rw [arcθ, arcθ]
  gcongr

lemma arcθ_zero : arcθ 0 = 0 := by simp [arcθ]

lemma arcθ_1024 : arcθ 1024 = 2 * Real.pi := by
  rw [arcθ]; norm_num; ring

/-- `e^{2πi k/1024} = e^{i θ_k}`. -/
lemma exp_arcθ (k : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((((k : ℝ) / 1024 : ℝ)) : ℂ))
      = Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)) := by
  congr 1
  rw [arcθ]
  push_cast
  ring

/-- `e^{iθ_k}` as it appears in the interval tables. -/
lemma arcθ_spec (k : ℕ) : 2 * (Real.pi : ℂ) * (k : ℂ) / 1024 = ((arcθ k : ℝ) : ℂ) := by
  rw [arcθ]; push_cast; ring

lemma arcθ_244_lt_alpR : arcθ 244 < alpR := by
  have h1 := AlpBound.1
  have h2 : arcθ 244 < (1.4973 : ℝ) := by
    rw [arcθ]; nlinarith [Real.pi_lt_d4]
  linarith

lemma arcθ_245_gt_alpR : alpR < arcθ 245 := by
  have h1 := AlpBound.2
  have h2 : (1.5031 : ℝ) < arcθ 245 := by
    rw [arcθ]; nlinarith [Real.pi_gt_d4]
  linarith

/-- `θ_k ∈ (-α, α)` for `k ≤ 244`. -/
lemma arcθ_mem_Ioo {k : ℕ} (h1 : k ≤ 244) : arcθ k ∈ Set.Ioo (-alpR) alpR := by
  have h0 : (0 : ℝ) ≤ arcθ k := by rw [arcθ]; positivity
  exact ⟨by linarith [alpR_pos], lt_of_le_of_lt (arcθ_mono h1) arcθ_244_lt_alpR⟩

/-! ## 1. Pointwise bounds from the series certificate -/

lemma log_h_le_svUp {p : Cpx} (hOK : BoxOK p) {z : ℂ} (hz : p.Mem z) :
    Real.log ‖Submission.CDTPlan.hauptH z‖ ≤ m2r (svUp p) := by
  obtain ⟨hball, -⟩ := GridFacts
  have h1 : ‖z - bpt (toPB p)‖ ≤ m2r (toPB p).e := hball p z hz
  have h2 : ‖z - ((↑(toPB p).x : ℝ) + (↑(toPB p).y : ℝ) * Complex.I) / (SC : ℝ)‖
      ≤ m2r (toPB p).e := by
    simpa only [bpt] using h1
  have hkey := SerUpSpecR (x := (toPB p).x) (y := (toPB p).y) (e := (toPB p).e) (w := z)
    (BoxOK.e_nonneg hOK) (BoxOK.natAbs_x hOK) (BoxOK.natAbs_y hOK)
    (lt_of_le_of_lt (BoxOK.sigma_le_real hOK) (by norm_num))
    (BoxOK.e_lt_real hOK)
    (le_trans (BoxOK.sigma_le_real hOK) (by norm_num))
    (le_trans (BoxOK.e_le_real hOK) (by norm_num)) h2
  simpa only [svUp] using hkey

lemma log_h_cuspA_le :
    Real.log ‖Submission.CDTPlan.hauptH (zCuspA * ((3 / 4 : ℝ) : ℂ))‖
      ≤ m2r (svUp ptCuspA) := by
  obtain ⟨-, -, hBA, -⟩ := GridFacts
  have hmem : (⟨ratIv 429 629, ratIv (-460) 629⟩ : Cpx).Mem zCuspA := mem_zCuspA
  have h34 : (ratIv 3 4).Mem ((3 : ℝ) / 4) := RatIvSpec (p := 3) (q := 4) (by norm_num)
  have h := mem_mulr hmem h34
  have hpt : ptCuspA.Mem (zCuspA * ((3 / 4 : ℝ) : ℂ)) := by
    simpa only [ptCuspA] using h
  exact log_h_le_svUp hBA hpt

lemma log_h_cuspB_le :
    Real.log ‖Submission.CDTPlan.hauptH (zCuspB * ((3 / 4 : ℝ) : ℂ))‖
      ≤ m2r (svUp ptCuspB) := by
  obtain ⟨-, -, -, hBB, -⟩ := GridFacts
  have hmem : (⟨ratIv 429 629, ratIv 460 629⟩ : Cpx).Mem zCuspB := mem_zCuspB
  have h34 : (ratIv 3 4).Mem ((3 : ℝ) / 4) := RatIvSpec (p := 3) (q := 4) (by norm_num)
  have h := mem_mulr hmem h34
  have hpt : ptCuspB.Mem (zCuspB * ((3 / 4 : ℝ) : ℂ)) := by
    simpa only [ptCuspB] using h
  exact log_h_le_svUp hBB hpt

/-- The point `ψ_C (e^{iθ_j})` lies in the corresponding box. -/
lemma mem_ptOf (j : ℕ) (hj : j ≤ 1024) :
    (ptOf j).Mem (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ j : ℝ) : ℂ)))) := by
  by_cases h1 : j ≤ 244
  · have hspec := PtC1Spec h1
    rw [show ptOf j = ptC1 j from by rw [ptOf]; exact if_pos h1]
    rwa [arcθ_spec j] at hspec
  · by_cases h2 : 780 ≤ j
    · have hspec := PtC1bSpec h2 hj
      rw [show ptOf j = ptC1b j from by rw [ptOf]; rw [if_neg h1]; exact if_pos h2]
      rwa [arcθ_spec j] at hspec
    · have hspec := PtC2Spec (k := j) (by omega) (by omega)
      rw [show ptOf j = ptC2 j from by rw [ptOf]; rw [if_neg h1]; exact if_neg h2]
      rwa [arcθ_spec j] at hspec

/-- At a grid point `θ_j`, `log ‖h (ψ_C (e^{iθ_j}))‖ ≤ svUp` of the corresponding box. -/
lemma log_h_grid_le (j : ℕ) (hj : j ≤ 1024) :
    Real.log ‖Submission.CDTPlan.hauptH
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ j : ℝ) : ℂ))))‖
      ≤ m2r (svUp (ptOf j)) := by
  obtain ⟨-, hBOX, -⟩ := GridFacts
  exact log_h_le_svUp (hBOX j hj) (mem_ptOf j hj)

lemma m2r_maxZ (a b : ℤ) : m2r (max a b) = max (m2r a) (m2r b) := Iv.m2r_max a b

lemma phiR_mono {a b : ℝ} (ha : a ∈ Set.Ioo (-alpR) alpR) (hb : b ∈ Set.Ioo (-alpR) alpR)
    (hab : a ≤ b) : phiR a ≤ phiR b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [← h]
  · exact le_of_lt (phi_strictMono ha hb h)

/-! ## 2. Parametrisations -/

/-- On the cusp arc `(-α, α)`, `log ‖h ∘ ψ_C‖ = Hfun ∘ phiR`. -/
lemma log_h_eq_Hfun {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    Real.log ‖Submission.CDTPlan.hauptH
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))))‖ = Hfun (phiR θ) := by
  have h1 := circleLog_eq_Hfun (θ := θ) hθ
  have h2 : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC (θ / (2 * Real.pi))
      = Real.log ‖Submission.CDTPlan.hauptH
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))))‖ := by
    simp only [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC]
    congr 1
    congr 1
    push_cast
    field_simp
  rw [h2] at h1
  exact h1

/-- `circleLog phiC t = log ‖h (ψ_C (e^{2πit}))‖`, in the angle variable `θ = 2πt`. -/
lemma circleLog_phiC_eq {t θ : ℝ} (hθ : θ = 2 * Real.pi * t) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
      = Real.log ‖Submission.CDTPlan.hauptH
          (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))))‖ := by
  simp only [Submission.CDTPlan.circleLog, Submission.CDTPlan.phiC]
  congr 1
  rw [hθ]; push_cast; ring

/-- `log ‖h‖` is invariant under complex conjugation. -/
lemma log_h_conj {w : ℂ} (hw : ‖w‖ < 1) :
    Real.log ‖Submission.CDTPlan.hauptH (conj w)‖ = Real.log ‖Submission.CDTPlan.hauptH w‖ := by
  by_cases h0 : w = 0
  · rw [h0]
    simp [Submission.CDTPlan.hauptH]
  · have hcw : conj w ≠ 0 := by
      intro hc
      exact h0 (by rw [← Complex.conj_conj w, hc, map_zero])
    rw [log_norm_hauptH_of_norm_lt_one (by simpa [Complex.norm_conj] using hw) hcw,
      log_norm_hauptH_of_norm_lt_one hw h0, Complex.norm_conj]
    have hsum : (∑' n : ℕ, 24 * Real.log ‖(1 : ℂ) + conj w ^ (n + 1)‖)
        = ∑' n : ℕ, 24 * Real.log ‖(1 : ℂ) + w ^ (n + 1)‖ := by
      refine tsum_congr (fun n => ?_)
      congr 1
      rw [← Complex.norm_conj ((1 : ℂ) + w ^ (n + 1)), map_add, map_one, map_pow]
    rw [hsum]

/-- `ψ_C (e^{iθ}) = conj (ψ_C (e^{i(2π-θ)}))` on the fourth arc. -/
lemma psiC_arc4_conj {θ : ℝ} (hθ : θ ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi)) :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
      = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - θ : ℝ) : ℂ)))) := by
  set θ' : ℝ := 2 * Real.pi - θ with hθ'def
  have hA : θ - 2 * Real.pi ∈ Set.Ioo (-alpR) alpR := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, alpR_pos]⟩
  have hB : θ' ∈ Set.Ioo (-alpR) alpR := by
    rw [Set.mem_Ioo]
    exact ⟨by rw [hθ'def]; linarith [hθ.2, alpR_pos],
      by rw [hθ'def]; linarith [hθ.1]⟩
  have hPR : PR θ = PR θ' := by
    rw [PR, PR, show Real.cos θ = Real.cos θ' by rw [hθ'def, Real.cos_two_pi_sub]]
  have hQR : QR θ = QR θ' := by
    rw [QR, QR, show θ / 2 = Real.pi - θ' / 2 by rw [hθ'def]; ring, Real.sin_pi_sub]
  set P : ℂ := (PR θ : ℂ) with hP
  set Q : ℂ := (QR θ : ℂ) with hQ
  set D : ℂ := (dR : ℂ) with hD
  set E : ℂ := Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) with hE
  set E' : ℂ := Complex.exp (Complex.I * ((θ' / 2 : ℝ) : ℂ)) with hE'
  have hπ : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
    simpa [mul_comm] using Complex.exp_pi_mul_I
  have hDc : conj D = D := by rw [hD]; exact Complex.conj_ofReal dR
  have hPc : conj P = P := by rw [hP]; exact Complex.conj_ofReal _
  have hQc : conj Q = Q := by rw [hQ]; exact Complex.conj_ofReal _
  have hconjE' : conj E' = -E := by
    rw [hE', ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, hE]
    rw [show -(Complex.I) * ((θ' / 2 : ℝ) : ℂ)
        = Complex.I * ((θ / 2 : ℝ) : ℂ) + (-((Real.pi : ℂ) * Complex.I)) by
      rw [show θ / 2 = Real.pi - θ' / 2 by rw [hθ'def]; ring]
      push_cast
      ring]
    rw [Complex.exp_add, Complex.exp_neg, hπ]
    ring
  have hL : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
      = (3 / 4 : ℂ) * (((P - Complex.I * Q) * E) / D) := by
    rw [psiC_eq_threequarters_Wfun, WfunArc4 hA, ← hP, ← hQ, ← hD, ← hE]
  have hR : conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((θ' : ℝ) : ℂ))))
      = (3 / 4 : ℂ) * (((P - Complex.I * Q) * E) / D) := by
    rw [psiC_eq_threequarters_Wfun, Wfun_exp hB, ← hPR, ← hQR, ← hP, ← hQ, ← hD, ← hE']
    have h34 : (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by norm_num
    rw [h34]
    simp only [map_mul, Complex.conj_ofReal, map_div₀, map_neg, map_add, Complex.conj_I,
      hconjE', hDc, hPc, hQc]
    ring
  rw [hL, hR]

/-- On the fourth arc, `log ‖h ∘ ψ_C‖` equals `Hfun ∘ phiR` at the reflected angle. -/
lemma log_h_arc4 {θ' : ℝ} (h0 : 0 ≤ θ') (h1 : θ' < alpR) :
    Real.log ‖Submission.CDTPlan.hauptH (Submission.CDTPlan.psiC
        (Complex.exp (Complex.I * (((2 * Real.pi - θ' : ℝ)) : ℂ))))‖ = Hfun (phiR θ') := by
  have hθ' : θ' ∈ Set.Ioo (-alpR) alpR := ⟨by linarith [alpR_pos], h1⟩
  have h4 : (2 * Real.pi - θ') ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) :=
    ⟨by linarith, by linarith⟩
  have hc := psiC_arc4_conj h4
  rw [show 2 * Real.pi - (2 * Real.pi - θ') = θ' by ring] at hc
  have hnorm : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ' : ℂ)))‖ ≤ 3 / 4 :=
    Work.CPsi.psiC_norm_le (le_of_eq (by
      rw [show Complex.I * (θ' : ℂ) = (θ' : ℂ) * Complex.I by ring]
      exact Complex.norm_exp_ofReal_mul_I θ'))
  have hlt : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ' : ℂ)))‖ < 1 :=
    lt_of_le_of_lt hnorm (by norm_num)
  rw [hc, log_h_conj hlt, log_h_eq_Hfun hθ']

lemma cJ_eq_cenC2 : cJ = cenC2 := by
  simp only [cJ, cenC2, aR, bR, kR, cR]; norm_num

lemma uJ_eq_sqrt_rho2sq : uJ = Real.sqrt rho2sq := by
  have hsq : rho2sq = ((115 : ℝ) / 143) ^ 2 := by
    simp only [rho2sq, aR, bR, c0R, kR, cR]; norm_num
  rw [hsq, Real.sqrt_sq (by norm_num)]
  simp only [uJ]

/-- `wf` at the `C₂`-parameter of `θ` is `ψ_C (e^{iθ})`. -/
lemma wf_Vof_eq {θ : ℝ} (h1 : alpR ≤ θ) (h2 : θ ≤ 2 * Real.pi - alpR) :
    wf (C2Psi (θ / 2) - Real.pi)
      = Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) := by
  have hV := C2VofClosed h1 h2
  have hcJ := cJ_eq_cenC2
  have huJ := uJ_eq_sqrt_rho2sq
  have hπ : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
    simpa [mul_comm] using Complex.exp_pi_mul_I
  have hexp : Complex.exp (Complex.I * (((C2Psi (θ / 2) - Real.pi : ℝ)) : ℂ))
      = - Complex.exp (Complex.I * ((C2Psi (θ / 2) : ℝ) : ℂ)) := by
    rw [show Complex.I * (((C2Psi (θ / 2) - Real.pi : ℝ)) : ℂ)
        = Complex.I * ((C2Psi (θ / 2) : ℝ) : ℂ) + (-((Real.pi : ℂ) * Complex.I)) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_neg, hπ]
    ring
  have hρ : ((Real.sqrt rho2sq : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sqrt_rho2sq_pos.ne'
  rw [wf, hcJ, huJ, hexp, ← hV, Vof, psiC_eq_threequarters_Wfun]
  field_simp
  ring

/-- `Jfun` is `log ‖h‖` at the corresponding point of the circle `C₂`. -/
lemma Jfun_eq_log_h {ψ : ℝ} (h : ‖wf ψ‖ < 1) :
    Jfun ψ = Real.log ‖Submission.CDTPlan.hauptH (wf ψ)‖ := by
  have hne : wf ψ ≠ 0 := by
    intro hc
    have h3 : (cJ : ℂ) + (uJ : ℂ) * Complex.exp (Complex.I * (ψ : ℂ)) = 0 := by
      rw [← wf]; exact hc
    have h4 : (cJ : ℂ) = -((uJ : ℂ) * Complex.exp (Complex.I * (ψ : ℂ))) := by
      linear_combination h3
    have h5 := congrArg norm h4
    have h6 : ‖((uJ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ : ℂ))‖ = uJ := by
      rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one]
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (by norm_num [uJ] : (0 : ℝ) ≤ uJ)]
    have h7 : ‖((cJ : ℝ) : ℂ)‖ = cJ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (by norm_num [cJ] : (0 : ℝ) ≤ cJ)]
    rw [h7] at h5
    rw [norm_neg, h6] at h5
    rw [cJ, uJ] at h5
    norm_num at h5
  have hcJ := cJ_eq_cenC2
  have huJ := uJ_eq_sqrt_rho2sq
  rw [log_norm_hauptH_of_norm_lt_one h hne]
  simp only [Jfun, wf]
  rw [← hcJ, ← huJ]

/-! ## 3. Monotonicity of the `C₂`-parameter -/

lemma continuous_C2Psi : Continuous C2Psi := by
  unfold C2Psi
  exact (continuous_id.sub continuous_const).add
    (Real.continuous_arcsin.comp (Real.continuous_cos.div_const _))

/-- `C2Psi y ≤ C2Psi (α/2)` for `y` inside the arc (limit at the left endpoint). -/
lemma C2Psi_le_left {y : ℝ} (hy : alpR / 2 < y) (hy2 : y < Real.pi - alpR / 2) :
    C2Psi y ≤ C2Psi (alpR / 2) := by
  rcases eq_or_lt_of_le hy.le with h | h
  · rw [← h]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcont : ContinuousAt C2Psi (alpR / 2) := continuous_C2Psi.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ0, hδ⟩ := hcont ε hε
    set z : ℝ := alpR / 2 + min (δ / 2) ((y - alpR / 2) / 2) with hzdef
    have hmin0 : 0 < min (δ / 2) ((y - alpR / 2) / 2) :=
      lt_min (by linarith) (by linarith)
    have hz1 : alpR / 2 < z := by rw [hzdef]; linarith
    have hz2 : z < y := by
      have hle : min (δ / 2) ((y - alpR / 2) / 2) ≤ (y - alpR / 2) / 2 := min_le_right _ _
      rw [hzdef]; linarith
    have hz3 : dist z (alpR / 2) < δ := by
      rw [Real.dist_eq, abs_lt]
      have hle : min (δ / 2) ((y - alpR / 2) / 2) ≤ δ / 2 := min_le_left _ _
      refine ⟨by rw [hzdef]; linarith, by rw [hzdef]; linarith⟩
    have h1 : dist (C2Psi z) (C2Psi (alpR / 2)) < ε := hδ hz3
    rw [Real.dist_eq] at h1
    have h2 : C2Psi y ≤ C2Psi z :=
      le_of_lt (C2_Psi_antitone ⟨hz1, by linarith [hz2]⟩ ⟨hy, hy2⟩ hz2)
    linarith [abs_lt.mp h1]

/-- `C2Psi (π - α/2) ≤ C2Psi x` for `x` inside the arc (limit at the right endpoint). -/
lemma C2Psi_le_right {x : ℝ} (hx : alpR / 2 < x) (hx2 : x < Real.pi - alpR / 2) :
    C2Psi (Real.pi - alpR / 2) ≤ C2Psi x := by
  rcases eq_or_lt_of_le hx2.le with h | h
  · rw [← h]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcont : ContinuousAt C2Psi (Real.pi - alpR / 2) := continuous_C2Psi.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ0, hδ⟩ := hcont ε hε
    set z : ℝ := Real.pi - alpR / 2 - min (δ / 2) ((Real.pi - alpR / 2 - x) / 2) with hzdef
    have hmin0 : 0 < min (δ / 2) ((Real.pi - alpR / 2 - x) / 2) :=
      lt_min (by linarith) (by linarith)
    have hz1 : x < z := by
      have hle : min (δ / 2) ((Real.pi - alpR / 2 - x) / 2) ≤ (Real.pi - alpR / 2 - x) / 2 :=
        min_le_right _ _
      rw [hzdef]; linarith
    have hz2 : z < Real.pi - alpR / 2 := by rw [hzdef]; linarith
    have hz3 : dist z (Real.pi - alpR / 2) < δ := by
      rw [Real.dist_eq, abs_lt]
      have hle : min (δ / 2) ((Real.pi - alpR / 2 - x) / 2) ≤ δ / 2 := min_le_left _ _
      refine ⟨by rw [hzdef]; linarith, by rw [hzdef]; linarith⟩
    have h1 : dist (C2Psi z) (C2Psi (Real.pi - alpR / 2)) < ε := hδ hz3
    rw [Real.dist_eq] at h1
    have h2 : C2Psi z ≤ C2Psi x :=
      le_of_lt (C2_Psi_antitone ⟨hx, hx2⟩ ⟨by linarith [hx, hz1], hz2⟩ hz1)
    have h3 := (abs_lt.mp h1).1
    linarith

/-! ## 4. Chord estimates -/

lemma sqUp_nonneg (n : ℤ) : 0 ≤ sqUp n := by rw [sqUp]; exact Int.natCast_nonneg _

lemma distUp_nonneg (a b : Cpx) : 0 ≤ distUp a b := by
  rw [distUp]; exact sqUp_nonneg _

lemma dWup_nonneg (a b : Cpx) : 0 ≤ dWup a b := by
  rw [dWup]
  refine add_nonneg ?_ (by norm_num)
  apply nonneg_of_m2r_nonneg
  refine le_trans ?_ (divU_ge (k := 3) (by norm_num) (distUp a b * 4))
  exact div_nonneg (m2r_nonneg (mul_nonneg (distUp_nonneg a b) (by norm_num))) (by norm_num)

lemma dVup_nonneg (a b : Cpx) : 0 ≤ dVup a b := by
  rw [dVup]
  refine add_nonneg ?_ (by norm_num)
  apply nonneg_of_m2r_nonneg
  refine le_trans ?_ (divU_ge (k := 115) (by norm_num) (distUp a b * 143))
  exact div_nonneg (m2r_nonneg (mul_nonneg (distUp_nonneg a b) (by norm_num))) (by norm_num)

/-- `5 d ≤ SC` gives `m2r d ≤ 1/5`. -/
lemma m2r_le_fifth {d : ℤ} (hd : 5 * d ≤ SC) : m2r d ≤ 1 / 5 := by
  have h5 : m2r (5 * d) ≤ m2r SC := m2r_le hd
  rw [m2r_mul, m2r_SC] at h5
  have h5' : m2r (5 : ℤ) = 5 / (SC : ℝ) := by simp [m2r]
  rw [h5'] at h5
  have hSC : (SC : ℝ) ≠ 0 := ne_of_gt SC_posR
  have hkey : (SC : ℝ) * (5 / (SC : ℝ) * m2r d) = 5 * m2r d := by field_simp
  rw [hkey] at h5
  linarith

lemma five_pow_le : ((1 : ℝ) / 5) ^ 5 / 160 ≤ 4096 / (SC : ℝ) := by
  have h1 : (4096 : ℝ) / (SC : ℝ) = 1 / 262144 := by
    rw [show (SC : ℝ) = 1073741824 by norm_num [Work.ANum.SC]]
    norm_num
  rw [h1]; norm_num

/-- The elementary `D ^ 5` correction is dominated by the certificate's slack. -/
lemma pow5_slack {D e : ℝ} (hD0 : 0 ≤ D) (hDe : D ≤ e) (he : e ≤ 1 / 5) :
    D ^ 5 / 160 ≤ 4096 / (SC : ℝ) := by
  have h1 : D ^ 5 ≤ ((1 : ℝ) / 5) ^ 5 := pow_le_pow_left₀ hD0 (le_trans hDe he) 5
  have h2 : D ^ 5 / 160 ≤ ((1 : ℝ) / 5) ^ 5 / 160 := by gcongr
  exact le_trans h2 five_pow_le

/-- The `C₁`-arc chord estimate: `phiR` increases by at most the chord plus corrections. -/
lemma phiR_chord_le {d : ℤ} {θ₁ θ₂ : ℝ} (h1 : θ₁ ∈ Set.Ioo (-alpR) alpR)
    (h2 : θ₂ ∈ Set.Ioo (-alpR) alpR) (h12 : θ₁ ≤ θ₂)
    (hD : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ)))
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ ≤ m2r d)
    (hd : 5 * d ≤ SC) :
    phiR θ₂ - phiR θ₁ ≤ m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ) := by
  set D : ℝ := (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ)))
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have hd0 : 0 ≤ m2r d := le_trans hD0 hD
  have h15 : m2r d ≤ 1 / 5 := m2r_le_fifth hd
  have hDhalf : D ≤ 1 / 2 := by linarith [hD, h15]
  have hphi := PhiChord h1 h2 h12 (by simpa only [hDdef] using hDhalf)
  rw [← hDdef] at hphi
  have hmono : D ^ 3 / 12 ≤ (m2r d) ^ 3 / 12 := by gcongr
  have hfive : D ^ 5 / 160 ≤ 4096 / (SC : ℝ) := pow5_slack hD0 hD h15
  linarith

/-- The `C₂`-arc chord estimate. -/
lemma psiChord_le {d : ℤ} {θ₁ θ₂ : ℝ} (h1 : alpR ≤ θ₁)
    (h2 : θ₂ ≤ 2 * Real.pi - alpR) (h12 : θ₁ ≤ θ₂)
    (hD : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ)))
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ ≤ m2r d)
    (hd : 5 * d ≤ SC) :
    C2Psi (θ₁ / 2) - C2Psi (θ₂ / 2) ≤ m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ) := by
  set D : ℝ := (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ)))
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have hd0 : 0 ≤ m2r d := le_trans hD0 hD
  have h15 : m2r d ≤ 1 / 5 := m2r_le_fifth hd
  have hpsi := PsiChord h1 h2 h12
  rw [← hDdef] at hpsi
  have hmono : D ^ 3 / 12 ≤ (m2r d) ^ 3 / 12 := by gcongr
  have hfive : D ^ 5 / 160 ≤ 4096 / (SC : ℝ) := pow5_slack hD0 hD h15
  linarith

/-! ## 5. The cusp geometry -/

/-- `phiR θ ≤ α/2 + 3π/2` for `θ ≤ α`. -/
lemma phiR_le_lim {θ : ℝ} (hθ : θ ≤ alpR) : phiR θ ≤ alpR / 2 + 3 * Real.pi / 2 := by
  have h : Real.arctan (QR θ / PR θ) ≤ Real.pi / 2 :=
    le_of_lt (Real.arctan_lt_pi_div_two _)
  simp only [phiR]
  linarith

/-- `QR θ ≥ 0` for `θ ∈ [0, 2π]`. -/
lemma QR_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi) : 0 ≤ QR θ := by
  rw [QR]
  refine mul_nonneg (by rw [cR]; norm_num) ?_
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- `exp (i (α/2 + 3π/2)) = zCuspA`. -/
lemma exp_I_cuspA :
    Complex.exp (Complex.I * ((alpR / 2 + 3 * Real.pi / 2 : ℝ) : ℂ)) = zCuspA := by
  have h1 : Complex.exp (Complex.I * ((alpR / 2 : ℝ) : ℂ))
      = (C2C : ℂ) + (C2σ : ℂ) * Complex.I := by
    rw [show Complex.I * ((alpR / 2 : ℝ) : ℂ) = ((alpR / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I, cos_half_alpR, sin_half_alpR]
  have h2 : Complex.exp (Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
    rw [show Complex.I * (((Real.pi + Real.pi / 2 : ℝ)) : ℂ)
        = Complex.I * ((Real.pi : ℝ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.exp_add, show Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 by
      simpa [mul_comm] using Complex.exp_pi_mul_I,
      show Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I by
        rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
          ring, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp]
    ring
  rw [show Complex.I * ((alpR / 2 + 3 * Real.pi / 2 : ℝ) : ℂ)
      = Complex.I * ((alpR / 2 : ℝ) : ℂ) + Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.exp_add, h1, h2]
  rw [C2C, C2σ, zCuspA]
  push_cast
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- The angle `Δ = α/2 + 3π/2 - phiR (θ_244)` and the cusp chord. -/
lemma cuspA_chord_eq :
    2 * Real.sin ((alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244)) / 2)
      = (4 / 3) * ‖zCuspA * ((3 / 4 : ℝ) : ℂ)
          - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))‖ := by
  set B : ℝ := phiR (arcθ 244) with hB
  set A : ℝ := alpR / 2 + 3 * Real.pi / 2 with hA
  have hA34 : (zCuspA : ℂ) * ((3 / 4 : ℝ) : ℂ)
      = ((3 / 4 : ℝ) : ℂ) * Complex.exp (Complex.I * (A : ℂ)) := by
    rw [hA, exp_I_cuspA]; ring
  have hB34 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))
      = ((3 / 4 : ℝ) : ℂ) * Complex.exp (Complex.I * (B : ℂ)) := by
    rw [psiC_eq_threequarters_Wfun, ← exp_phi_eq (arcθ_mem_Ioo (by norm_num)), ← hB]
    norm_num
  have harc244 : arcθ 244 ≤ 2 * Real.pi := by
    rw [← arcθ_1024]; exact arcθ_mono (by norm_num)
  have harm : 0 ≤ Real.arctan (QR (arcθ 244) / PR (arcθ 244)) :=
    Real.arctan_nonneg.mpr (div_nonneg (QR_nonneg (by rw [arcθ]; positivity) harc244)
      (Real.sqrt_nonneg _))
  have harm2 : Real.arctan (QR (arcθ 244) / PR (arcθ 244)) ≤ Real.pi / 2 :=
    le_of_lt (Real.arctan_lt_pi_div_two _)
  have hΔ0 : 0 ≤ A - B := by
    have h5 : A - B = (alpR - arcθ 244) / 2 + Real.pi / 2
        - Real.arctan (QR (arcθ 244) / PR (arcθ 244)) := by
      rw [hA, hB, phiR]; ring
    have h3 : arcθ 244 < alpR := arcθ_244_lt_alpR
    rw [h5]; linarith
  have hΔπ : A - B ≤ Real.pi := by
    have h2 : (0 : ℝ) < arcθ 244 := by rw [arcθ]; positivity
    have h3 : arcθ 244 < alpR := arcθ_244_lt_alpR
    have h4 : alpR < Real.pi := alpR_lt_pi
    have h5 : A - B = (alpR - arcθ 244) / 2 + Real.pi / 2
        - Real.arctan (QR (arcθ 244) / PR (arcθ 244)) := by
      rw [hA, hB, phiR]; ring
    rw [h5]; linarith
  rw [hA34, hB34]
  rw [show ((((3 : ℝ) / 4 : ℝ)) : ℂ) * Complex.exp (Complex.I * (A : ℂ))
        - ((3 / 4 : ℝ) : ℂ) * Complex.exp (Complex.I * (B : ℂ))
      = ((3 / 4 : ℝ) : ℂ) * (Complex.exp (Complex.I * (A : ℂ))
          - Complex.exp (Complex.I * (B : ℂ))) by ring]
  rw [norm_mul, show ‖((((3 : ℝ) / 4 : ℝ)) : ℂ)‖ = 3 / 4 by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)]]
  rw [phiChord_chord_norm A B]
  have hsin : |Real.sin ((A - B) / 2)| = Real.sin ((A - B) / 2) := by
    rw [abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [hsin]
  ring

/-- The cusp chord estimate at `α`. -/
lemma cuspA_delta_le {d : ℤ} (hd : 5 * d ≤ SC)
    (hD : (4 / 3) * ‖zCuspA * ((3 / 4 : ℝ) : ℂ)
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))‖ ≤ m2r d) :
    alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244)
      ≤ m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ) := by
  set Δ : ℝ := alpR / 2 + 3 * Real.pi / 2 - phiR (arcθ 244) with hΔ
  set D : ℝ := (4 / 3) * ‖zCuspA * ((3 / 4 : ℝ) : ℂ)
        - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))‖ with hDdef
  have hid : 2 * Real.sin (Δ / 2) = D := by
    rw [hΔ, hDdef]
    exact cuspA_chord_eq
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have hd0 : 0 ≤ m2r d := le_trans hD0 hD
  have h15 : m2r d ≤ 1 / 5 := m2r_le_fifth hd
  have harc244 : arcθ 244 ≤ 2 * Real.pi := by
    rw [← arcθ_1024]; exact arcθ_mono (by norm_num)
  have harm : 0 ≤ Real.arctan (QR (arcθ 244) / PR (arcθ 244)) :=
    Real.arctan_nonneg.mpr (div_nonneg (QR_nonneg (by rw [arcθ]; positivity) harc244)
      (Real.sqrt_nonneg _))
  have harm2 : Real.arctan (QR (arcθ 244) / PR (arcθ 244)) ≤ Real.pi / 2 :=
    le_of_lt (Real.arctan_lt_pi_div_two _)
  have hΔ0 : 0 ≤ Δ := by
    have h5 : Δ = (alpR - arcθ 244) / 2 + Real.pi / 2
        - Real.arctan (QR (arcθ 244) / PR (arcθ 244)) := by
      rw [hΔ, phiR]; ring
    have h3 : arcθ 244 < alpR := arcθ_244_lt_alpR
    rw [h5]; linarith
  have hΔπ : Δ ≤ Real.pi := by
    have h2 : (0 : ℝ) < arcθ 244 := by rw [arcθ]; positivity
    have h3 : arcθ 244 < alpR := arcθ_244_lt_alpR
    have h4 : alpR < Real.pi := alpR_lt_pi
    have h5 : Δ = (alpR - arcθ 244) / 2 + Real.pi / 2
        - Real.arctan (QR (arcθ 244) / PR (arcθ 244)) := by
      rw [hΔ, phiR]; ring
    rw [h5]; linarith
  have hsin : Real.sin (Δ / 2) = D / 2 := by linarith
  have hquarter : D / 2 ≤ 1 / 4 := by linarith
  have h0 : 0 ≤ D / 2 := by linarith
  have harc : Real.arcsin (D / 2) = Δ / 2 := by
    rw [← hsin]
    exact Real.arcsin_sin (by linarith) (by linarith)
  have hchord := ArcsinChord h0 hquarter
  rw [harc] at hchord
  have h3 : (D / 2) ^ 3 / 3 = D ^ 3 / 24 := by ring
  have h5 : (D / 2) ^ 5 / 5 = D ^ 5 / 160 := by ring
  rw [h3, h5] at hchord
  have hmono1 : D ^ 3 / 24 ≤ (m2r d) ^ 3 / 24 := by gcongr
  have hmono2 : (m2r d) ^ 3 / 24 ≤ (m2r d) ^ 3 / 12 := by
    have := pow_nonneg hd0 3
    linarith
  have hfive : D ^ 5 / 160 ≤ 4096 / (SC : ℝ) := pow5_slack hD0 hD h15
  linarith

/-- The cusp value at `α` equals `Hfun` of the limiting angle. -/
lemma psiC_cuspB_real :
    Submission.CDTPlan.psiC (Complex.exp (Complex.I * (((2 * Real.pi - alpR : ℝ)) : ℂ)))
      = zCuspB * ((3 / 4 : ℝ) : ℂ) := by
  rw [show Complex.I * (((2 * Real.pi - alpR : ℝ)) : ℂ)
      = Complex.I * (2 * (Real.pi : ℂ) - (alpR : ℂ)) by push_cast; ring]
  exact psiC_cuspB

lemma Hfun_cuspA : Hfun (alpR / 2 + 3 * Real.pi / 2)
    = Real.log ‖Submission.CDTPlan.hauptH (zCuspA * ((3 / 4 : ℝ) : ℂ))‖ := by
  rw [← log_norm_hauptH_circle]
  have h : (3 / 4 : ℂ) * Complex.exp (Complex.I * ((alpR / 2 + 3 * Real.pi / 2 : ℝ) : ℂ))
      = zCuspA * ((3 / 4 : ℝ) : ℂ) := by
    rw [exp_I_cuspA]
    push_cast
    ring
  rw [h]

/-! ## 6. The arc bounds -/

lemma arcθ_le_of_div {k : ℕ} {t : ℝ} (ht : (k : ℝ) / 1024 ≤ t) :
    arcθ k ≤ 2 * Real.pi * t := by
  rw [arcθ]
  calc (k : ℝ) * Real.pi / 512 = 2 * Real.pi * ((k : ℝ) / 1024) := by ring
    _ ≤ 2 * Real.pi * t := mul_le_mul_of_nonneg_left ht (by positivity)

lemma le_arcθ_of_div {k : ℕ} {t : ℝ} (ht : t ≤ ((k : ℝ) + 1) / 1024) :
    2 * Real.pi * t ≤ arcθ (k + 1) := by
  rw [arcθ]
  push_cast
  calc 2 * Real.pi * t ≤ 2 * Real.pi * (((k : ℝ) + 1) / 1024) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = ((k : ℝ) + 1) * Real.pi / 512 := by ring

lemma wf_norm_lt_one_of_range {ψ : ℝ} (h : ψ ∈ Set.Icc (-3.9 : ℝ) (-2.39)) : ‖wf ψ‖ < 1 := by
  have h' : ψ ∈ Set.Ioo (-3.905 : ℝ) (-2.385) := ⟨by linarith [h.1], by linarith [h.2]⟩
  have := (arc_bounds h').2
  rw [rJ] at this
  linarith

lemma arc_bound_C1 (k : ℕ) (hk : k ≤ 243) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ m2r (Gv k) := by
  obtain ⟨hball, hBOX, hBA, hBB, hSmall, hSA, hSB, hWup, hVup, hWA, hWB, hVA, hVB⟩ := GridFacts
  obtain ⟨hdist, hdW, hdV, hch1, hch2⟩ := DistSpec
  have hGv : Gv k = max (svUp (ptOf k)) (svUp (ptOf (k + 1)))
      + chord1 (dWup (ptOf k) (ptOf (k + 1))) := by
    rw [Gv]; exact if_pos hk
  set θ : ℝ := 2 * Real.pi * t with hθdef
  have hθlo : arcθ k ≤ θ := by rw [hθdef]; exact arcθ_le_of_div ht.1
  have hθhi : θ ≤ arcθ (k + 1) := by rw [hθdef]; exact le_arcθ_of_div ht.2
  have hkIoo : arcθ k ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (by omega)
  have hk1Ioo : arcθ (k + 1) ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (by omega)
  have hθIoo : θ ∈ Set.Ioo (-alpR) alpR :=
    ⟨by linarith [hθlo, hkIoo.1], by linarith [hθhi, hk1Ioo.2]⟩
  have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t = Hfun (phiR θ) := by
    rw [circleLog_phiC_eq hθdef, log_h_eq_Hfun hθIoo]
  have hva : Hfun (phiR (arcθ k)) ≤ m2r (svUp (ptOf k)) := by
    rw [← log_h_eq_Hfun hkIoo]; exact log_h_grid_le k (by omega)
  have hvb : Hfun (phiR (arcθ (k + 1))) ≤ m2r (svUp (ptOf (k + 1))) := by
    rw [← log_h_eq_Hfun hk1Ioo]; exact log_h_grid_le (k + 1) (by omega)
  have hab : phiR (arcθ k) ≤ phiR (arcθ (k + 1)) :=
    phiR_mono hkIoo hk1Ioo (arcθ_mono (by omega))
  have hmemphi : phiR θ ∈ Set.Icc (phiR (arcθ k)) (phiR (arcθ (k + 1))) :=
    ⟨phiR_mono hkIoo hθIoo hθlo, phiR_mono hθIoo hk1Ioo hθhi⟩
  have hH := Hfun_chord hab (phiR θ) hmemphi
  have hD := hdW (ptOf k) (ptOf (k + 1))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ))))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ))))
    (hSmall k (by omega)) (hSmall (k + 1) (by omega))
    (mem_ptOf k (by omega)) (mem_ptOf (k + 1) (by omega))
  have hD' : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ)))
      - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)))‖
      ≤ m2r (dWup (ptOf k) (ptOf (k + 1))) := by
    simpa only [norm_sub_rev] using hD
  have hstep := phiR_chord_le hkIoo hk1Ioo (arcθ_mono (by omega)) hD' (hWup k (by omega))
  have hnn : 0 ≤ m2r (dWup (ptOf k) (ptOf (k + 1))) :=
    m2r_nonneg (dWup_nonneg _ _)
  have h400 : 400 * (phiR (arcθ (k + 1)) - phiR (arcθ k)) ^ 2
      ≤ m2r (chord1 (dWup (ptOf k) (ptOf (k + 1)))) := by
    have hc := hch1 (dWup (ptOf k) (ptOf (k + 1))) hnn
    have hnn2 : 0 ≤ phiR (arcθ (k + 1)) - phiR (arcθ k) := by linarith
    have hsq := pow_le_pow_left₀ hnn2 hstep 2
    linarith
  have hmain : Hfun (phiR θ) ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1))))
      + m2r (chord1 (dWup (ptOf k) (ptOf (k + 1)))) := by
    have hm : max (Hfun (phiR (arcθ k))) (Hfun (phiR (arcθ (k + 1))))
        ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1)))) :=
      max_le (le_trans hva (le_max_left _ _)) (le_trans hvb (le_max_right _ _))
    linarith
  rw [hGv, m2r_add, m2r_maxZ]
  linarith [hlog, hmain]

lemma arc_bound_C2 (k : ℕ) (hk1 : 245 ≤ k) (hk2 : k ≤ 778) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ m2r (Gv k) := by
  obtain ⟨hball, hBOX, hBA, hBB, hSmall, hSA, hSB, hWup, hVup, hWA, hWB, hVA, hVB⟩ := GridFacts
  obtain ⟨hdist, hdW, hdV, hch1, hch2⟩ := DistSpec
  have hGv : Gv k = max (svUp (ptOf k)) (svUp (ptOf (k + 1)))
      + chord2 (dVup (ptOf k) (ptOf (k + 1))) := by
    rw [Gv]
    rw [if_neg (by omega : ¬ (k ≤ 243)), if_neg (by omega : ¬ (k = 244)), if_pos hk2]
  set θ : ℝ := 2 * Real.pi * t with hθdef
  have hθlo : arcθ k ≤ θ := by rw [hθdef]; exact arcθ_le_of_div ht.1
  have hθhi : θ ≤ arcθ (k + 1) := by rw [hθdef]; exact le_arcθ_of_div ht.2
  have hkα : alpR ≤ arcθ k := le_of_lt (lt_of_lt_of_le arcθ_245_gt_alpR (arcθ_mono hk1))
  have hk1β : arcθ (k + 1) < 2 * Real.pi - alpR := by
    have h : arcθ (k + 1) ≤ arcθ 779 := arcθ_mono (by omega)
    have h2 : arcθ 779 = 2 * Real.pi - arcθ 245 := by rw [arcθ, arcθ]; ring
    rw [h2] at h
    linarith [arcθ_245_gt_alpR]
  have hθα : alpR ≤ θ := le_trans hkα hθlo
  have hθβ : θ ≤ 2 * Real.pi - alpR := le_trans hθhi (le_of_lt hk1β)
  have hθβ' : θ < 2 * Real.pi - alpR := lt_of_le_of_lt hθhi hk1β
  -- the Jfun identity
  have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t
      = Jfun (C2Psi (θ / 2) - Real.pi) := by
    rw [circleLog_phiC_eq hθdef]
    rw [show Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
        = wf (C2Psi (θ / 2) - Real.pi) from (wf_Vof_eq hθα hθβ).symm]
    exact (Jfun_eq_log_h (wf_norm_lt_one_of_range (PsiRange hθα hθβ))).symm
  -- the ψ-interval
  have hαk : alpR < arcθ k := lt_of_lt_of_le arcθ_245_gt_alpR (arcθ_mono hk1)
  have hαk1 : alpR < arcθ (k + 1) := lt_of_lt_of_le arcθ_245_gt_alpR (arcθ_mono (by omega))
  have hθint : θ / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith [lt_of_lt_of_le hαk hθlo], by linarith [hθβ]⟩
  have hkint : arcθ k / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith [hαk], by linarith [hk1β]⟩
  have hk1int : arcθ (k + 1) / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith [hαk1], by linarith [hk1β]⟩
  have hψlo : C2Psi (arcθ (k + 1) / 2) ≤ C2Psi (θ / 2) := by
    rcases eq_or_lt_of_le hθhi with h | h
    · rw [h]
    · exact le_of_lt (C2_Psi_antitone hθint hk1int (by linarith))
  have hψhi : C2Psi (θ / 2) ≤ C2Psi (arcθ k / 2) := by
    rcases eq_or_lt_of_le hθlo with h | h
    · rw [← h]
    · exact le_of_lt (C2_Psi_antitone hkint hθint (by linarith))
  have hψmem : C2Psi (θ / 2) - Real.pi ∈
      Set.Icc (C2Psi (arcθ (k + 1) / 2) - Real.pi) (C2Psi (arcθ k / 2) - Real.pi) :=
    ⟨by linarith, by linarith⟩
  have hab : C2Psi (arcθ (k + 1) / 2) - Real.pi ≤ C2Psi (arcθ k / 2) - Real.pi :=
    by linarith
  have hra := (PsiRange (le_trans hkα (arcθ_mono (by omega))) (le_of_lt hk1β))
  have hrb := (PsiRange hkα (le_trans (arcθ_mono (by omega)) (le_of_lt hk1β)))
  have hJ := Jfun_chord hab hra.1 hrb.2 (C2Psi (θ / 2) - Real.pi) hψmem
  -- endpoint values
  have hva : Jfun (C2Psi (arcθ (k + 1) / 2) - Real.pi) ≤ m2r (svUp (ptOf (k + 1))) := by
    rw [Jfun_eq_log_h (wf_norm_lt_one_of_range hra),
      wf_Vof_eq (le_trans hkα (arcθ_mono (by omega))) (le_of_lt hk1β)]
    exact log_h_grid_le (k + 1) (by omega)
  have hvb : Jfun (C2Psi (arcθ k / 2) - Real.pi) ≤ m2r (svUp (ptOf k)) := by
    rw [Jfun_eq_log_h (wf_norm_lt_one_of_range hrb),
      wf_Vof_eq hkα (le_trans (arcθ_mono (by omega)) (le_of_lt hk1β))]
    exact log_h_grid_le k (by omega)
  have hD := hdV (ptOf k) (ptOf (k + 1))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ))))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ))))
    (hSmall k (by omega)) (hSmall (k + 1) (by omega))
    (mem_ptOf k (by omega)) (mem_ptOf (k + 1) (by omega))
  have hD' : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ)))
      - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)))‖
      ≤ m2r (dVup (ptOf k) (ptOf (k + 1))) := by
    simpa only [norm_sub_rev] using hD
  have hstep := psiChord_le hkα (le_of_lt hk1β) (arcθ_mono (by omega)) hD' (hVup k (by omega))
  have hnn : 0 ≤ m2r (dVup (ptOf k) (ptOf (k + 1))) := m2r_nonneg (dVup_nonneg _ _)
  have h1000 : 1000 * (C2Psi (arcθ k / 2) - C2Psi (arcθ (k + 1) / 2)) ^ 2
      ≤ m2r (chord2 (dVup (ptOf k) (ptOf (k + 1)))) := by
    have hc := hch2 (dVup (ptOf k) (ptOf (k + 1))) hnn
    have hnn2 : 0 ≤ C2Psi (arcθ k / 2) - C2Psi (arcθ (k + 1) / 2) := by linarith
    have hsq := pow_le_pow_left₀ hnn2 hstep 2
    linarith
  have hmain : Jfun (C2Psi (θ / 2) - Real.pi)
      ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1))))
        + m2r (chord2 (dVup (ptOf k) (ptOf (k + 1)))) := by
    have hm : max (Jfun (C2Psi (arcθ (k + 1) / 2) - Real.pi))
        (Jfun (C2Psi (arcθ k / 2) - Real.pi))
        ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1)))) := max_le (le_trans hva (le_max_right _ _)) (le_trans hvb (le_max_left _ _))
    linarith
  rw [hGv, m2r_add, m2r_maxZ]
  linarith [hlog, hmain]

lemma arcθ_sub (j : ℕ) (hj : j ≤ 1024) : arcθ (1024 - j) = 2 * Real.pi - arcθ j := by
  rw [arcθ, arcθ, Nat.cast_sub hj]
  push_cast
  ring

lemma psiC_conj_eq {θ : ℝ} (hθ : θ ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi)) :
    conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))))
      = Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((2 * Real.pi - θ : ℝ) : ℂ))) := by
  rw [psiC_arc4_conj hθ, Complex.conj_conj]

lemma norm_psiC_lt_one (θ : ℝ) : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))‖ < 1 := by
  have h := Work.CPsi.psiC_norm_le (z := Complex.exp (Complex.I * (θ : ℂ))) (le_of_eq (by
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I θ))
  linarith

lemma arc_bound_C1b (k : ℕ) (hk1 : 780 ≤ k) (hk2 : k ≤ 1023) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024)) :
    Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ m2r (Gv k) := by
  obtain ⟨hball, hBOX, hBA, hBB, hSmall, hSA, hSB, hWup, hVup, hWA, hWB, hVA, hVB⟩ := GridFacts
  obtain ⟨hdist, hdW, hdV, hch1, hch2⟩ := DistSpec
  have hGv : Gv k = max (svUp (ptOf k)) (svUp (ptOf (k + 1)))
      + chord1 (dWup (ptOf k) (ptOf (k + 1))) := by
    rw [Gv]
    rw [if_neg (by omega : ¬ (k ≤ 243)), if_neg (by omega : ¬ (k = 244)),
      if_neg (by omega : ¬ (k ≤ 778)), if_neg (by omega : ¬ (k = 779))]
  set θ : ℝ := 2 * Real.pi * t with hθdef
  have hθlo : arcθ k ≤ θ := by rw [hθdef]; exact arcθ_le_of_div ht.1
  have hθhi : θ ≤ arcθ (k + 1) := by rw [hθdef]; exact le_arcθ_of_div ht.2
  set θ' : ℝ := 2 * Real.pi - θ with hθ'def
  -- the reflecting index arithmetic
  have h1023 : 1023 - k = 1024 - (k + 1) := by omega
  have hθ'lo : arcθ (1023 - k) ≤ θ' := by
    rw [hθ'def, h1023, arcθ_sub (k + 1) (by omega)]
    linarith [hθhi]
  have hθ'hi : θ' ≤ arcθ (1024 - k) := by
    rw [hθ'def, arcθ_sub k (by omega)]
    linarith [hθlo]
  have hθ'Ioo : θ' ∈ Set.Ioo (-alpR) alpR := by
    have h1 : arcθ (1023 - k) ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (by omega)
    have h2 : arcθ (1024 - k) ∈ Set.Ioo (-alpR) alpR := arcθ_mem_Ioo (by omega)
    exact ⟨by linarith [hθ'lo, h1.1], by linarith [hθ'hi, h2.2]⟩
  -- `θ` lies on the fourth arc
  have hθoc : θ ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) := by
    constructor
    · have h780 : 2 * Real.pi - alpR < arcθ 780 := by
        rw [show (780 : ℕ) = 1024 - 244 by norm_num, arcθ_sub 244 (by norm_num)]
        linarith [arcθ_244_lt_alpR]
      exact lt_of_lt_of_le h780 (le_trans (arcθ_mono hk1) hθlo)
    · have h : θ ≤ arcθ 1024 := le_trans hθhi (arcθ_mono (by omega))
      rwa [arcθ_1024] at h
  -- the parametrisation
  have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t = Hfun (phiR θ') := by
    rw [circleLog_phiC_eq hθdef]
    rw [show Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ)))
        = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ' : ℂ)))) from by
      rw [hθ'def]; exact psiC_arc4_conj hθoc]
    rw [log_h_conj (norm_psiC_lt_one θ')]
    exact log_h_eq_Hfun hθ'Ioo
  -- endpoint values
  have hθoc1 : arcθ (k + 1) ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) := by
    constructor
    · have h780 : 2 * Real.pi - alpR < arcθ 780 := by
        rw [show (780 : ℕ) = 1024 - 244 by norm_num, arcθ_sub 244 (by norm_num)]
        linarith [arcθ_244_lt_alpR]
      exact lt_of_lt_of_le h780 (arcθ_mono (by omega))
    · have h : arcθ (k + 1) ≤ arcθ 1024 := arcθ_mono (by omega)
      rwa [arcθ_1024] at h
  have hθoc0 : arcθ k ∈ Set.Ioc (2 * Real.pi - alpR) (2 * Real.pi) := by
    constructor
    · have h780 : 2 * Real.pi - alpR < arcθ 780 := by
        rw [show (780 : ℕ) = 1024 - 244 by norm_num, arcθ_sub 244 (by norm_num)]
        linarith [arcθ_244_lt_alpR]
      exact lt_of_lt_of_le h780 (arcθ_mono hk1)
    · have h : arcθ k ≤ arcθ 1024 := arcθ_mono (by omega)
      rwa [arcθ_1024] at h
  have hva : Hfun (phiR (arcθ (1023 - k))) ≤ m2r (svUp (ptOf (k + 1))) := by
    rw [← log_h_eq_Hfun (arcθ_mem_Ioo (by omega))]
    have hconj : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1023 - k) : ℝ) : ℂ)))
        = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ)))) := by
      rw [show arcθ (1023 - k) = 2 * Real.pi - arcθ (k + 1) from by
        rw [h1023]; exact arcθ_sub (k + 1) (by omega)]
      exact (psiC_conj_eq hθoc1).symm
    rw [hconj, log_h_conj (norm_psiC_lt_one (arcθ (k + 1)))]
    exact log_h_grid_le (k + 1) (by omega)
  have hvb : Hfun (phiR (arcθ (1024 - k))) ≤ m2r (svUp (ptOf k)) := by
    rw [← log_h_eq_Hfun (arcθ_mem_Ioo (by omega))]
    have hconj : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1024 - k) : ℝ) : ℂ)))
        = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)))) := by
      rw [show arcθ (1024 - k) = 2 * Real.pi - arcθ k from arcθ_sub k (by omega)]
      exact (psiC_conj_eq hθoc0).symm
    rw [hconj, log_h_conj (norm_psiC_lt_one (arcθ k))]
    exact log_h_grid_le k (by omega)
  have hab : phiR (arcθ (1023 - k)) ≤ phiR (arcθ (1024 - k)) :=
    phiR_mono (arcθ_mem_Ioo (by omega)) (arcθ_mem_Ioo (by omega)) (arcθ_mono (by omega))
  have hmemphi : phiR θ' ∈ Set.Icc (phiR (arcθ (1023 - k))) (phiR (arcθ (1024 - k))) :=
    ⟨phiR_mono (arcθ_mem_Ioo (by omega)) hθ'Ioo hθ'lo,
      phiR_mono hθ'Ioo (arcθ_mem_Ioo (by omega)) hθ'hi⟩
  have hH := Hfun_chord hab (phiR θ') hmemphi
  -- the chord, reflected to the arc `k`
  have hD := hdW (ptOf k) (ptOf (k + 1))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ))))
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ))))
    (hSmall k (by omega)) (hSmall (k + 1) (by omega))
    (mem_ptOf k (by omega)) (mem_ptOf (k + 1) (by omega))
  have hconj1 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1024 - k) : ℝ) : ℂ)))
      = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)))) := by
    rw [show arcθ (1024 - k) = 2 * Real.pi - arcθ k from arcθ_sub k (by omega)]
    exact (psiC_conj_eq hθoc0).symm
  have hconj2 : Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1023 - k) : ℝ) : ℂ)))
      = conj (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ)))) := by
    rw [show arcθ (1023 - k) = 2 * Real.pi - arcθ (k + 1) from by
      rw [h1023]; exact arcθ_sub (k + 1) (by omega)]
    exact (psiC_conj_eq hθoc1).symm
  have hD'' : ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1024 - k) : ℝ) : ℂ)))
      - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1023 - k) : ℝ) : ℂ)))‖
      = ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ k : ℝ) : ℂ)))
      - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (k + 1) : ℝ) : ℂ)))‖ := by
    rw [hconj1, hconj2, ← map_sub, Complex.norm_conj]
  have hD' : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1024 - k) : ℝ) : ℂ)))
      - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ (1023 - k) : ℝ) : ℂ)))‖
      ≤ m2r (dWup (ptOf k) (ptOf (k + 1))) := by
    rw [hD'']
    exact hD
  have hstep := phiR_chord_le (arcθ_mem_Ioo (by omega)) (arcθ_mem_Ioo (by omega))
    (arcθ_mono (by omega)) hD' (hWup k (by omega))
  have hnn : 0 ≤ m2r (dWup (ptOf k) (ptOf (k + 1))) := m2r_nonneg (dWup_nonneg _ _)
  have h400 : 400 * (phiR (arcθ (1024 - k)) - phiR (arcθ (1023 - k))) ^ 2
      ≤ m2r (chord1 (dWup (ptOf k) (ptOf (k + 1)))) := by
    have hc := hch1 (dWup (ptOf k) (ptOf (k + 1))) hnn
    have hnn2 : 0 ≤ phiR (arcθ (1024 - k)) - phiR (arcθ (1023 - k)) := by linarith
    have hsq := pow_le_pow_left₀ hnn2 hstep 2
    linarith
  have hmain : Hfun (phiR θ') ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1))))
      + m2r (chord1 (dWup (ptOf k) (ptOf (k + 1)))) := by
    have hm : max (Hfun (phiR (arcθ (1023 - k)))) (Hfun (phiR (arcθ (1024 - k))))
        ≤ max (m2r (svUp (ptOf k))) (m2r (svUp (ptOf (k + 1)))) :=
      max_le (le_trans hva (le_max_right _ _)) (le_trans hvb (le_max_left _ _))
    linarith
  rw [hGv, m2r_add, m2r_maxZ]
  linarith [hlog, hmain]

lemma mulU_nonnegZ {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mulU a b :=
  mulU_nonneg ha hb

lemma divU_nonnegZ {a : ℤ} {k : ℕ} (hk : 0 < k) (ha : 0 ≤ a) : 0 ≤ divU a k :=
  divUz_nonneg ha (by exact_mod_cast hk)

lemma chord1_nonneg (d : ℤ) (hd : 0 ≤ d) : 0 ≤ chord1 d := by
  have hu : 0 ≤ d + divU (mulU (mulU d d) d) 12 + 4096 :=
    add_nonneg (add_nonneg hd (divU_nonnegZ (by norm_num) (mulU_nonnegZ (mulU_nonnegZ hd hd) hd)))
      (by norm_num)
  have hSC : 0 ≤ (400 : ℤ) * SC := by have := SC_pos; positivity
  unfold chord1
  exact mulU_nonnegZ (mulU_nonnegZ hu hu) hSC

lemma chord2_nonneg (d : ℤ) (hd : 0 ≤ d) : 0 ≤ chord2 d := by
  have hu : 0 ≤ d + divU (mulU (mulU d d) d) 12 + 4096 :=
    add_nonneg (add_nonneg hd (divU_nonnegZ (by norm_num) (mulU_nonnegZ (mulU_nonnegZ hd hd) hd)))
      (by norm_num)
  have hSC : 0 ≤ (1000 : ℤ) * SC := by have := SC_pos; positivity
  unfold chord2
  exact mulU_nonnegZ (mulU_nonnegZ hu hu) hSC

lemma conj_zCuspA : conj (zCuspA : ℂ) = zCuspB := by
  simp only [zCuspA, zCuspB, map_add, map_mul, map_div₀, map_ofNat, map_neg,
    Complex.conj_I, Complex.conj_ofReal]
  ring

lemma norm_zCuspA : ‖(zCuspA : ℂ)‖ = 1 := by
  rw [← exp_I_cuspA, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma norm_zCuspB : ‖(zCuspB : ℂ)‖ = 1 := by
  rw [← conj_zCuspA, Complex.norm_conj, norm_zCuspA]

lemma conj_cuspA : conj (zCuspA * ((3 / 4 : ℝ) : ℂ))
    = zCuspB * ((3 / 4 : ℝ) : ℂ) := by
  rw [map_mul, conj_zCuspA, Complex.conj_ofReal]

lemma cuspA_eq_conj_cuspB : zCuspA * ((3 / 4 : ℝ) : ℂ)
    = conj (zCuspB * ((3 / 4 : ℝ) : ℂ)) := by
  have := congrArg conj conj_cuspA
  simpa using this

lemma norm_cuspB_lt_one : ‖zCuspB * ((3 / 4 : ℝ) : ℂ)‖ < 1 := by
  rw [norm_mul, norm_zCuspB,
    show ‖((((3 : ℝ) / 4 : ℝ)) : ℂ)‖ = 3 / 4 by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 4)]]
  norm_num



/-! ## 7. The cusp boxes and the two cusp chord distances -/

lemma mem_cuspA : ptCuspA.Mem (zCuspA * ((3 / 4 : ℝ) : ℂ)) := by
  have hmem : (⟨ratIv 429 629, ratIv (-460) 629⟩ : Cpx).Mem zCuspA := mem_zCuspA
  have h34 : (ratIv 3 4).Mem ((3 : ℝ) / 4) := RatIvSpec (p := 3) (q := 4) (by norm_num)
  have h := mem_mulr hmem h34
  simpa only [ptCuspA] using h

lemma mem_cuspB : ptCuspB.Mem (zCuspB * ((3 / 4 : ℝ) : ℂ)) := by
  have hmem : (⟨ratIv 429 629, ratIv 460 629⟩ : Cpx).Mem zCuspB := mem_zCuspB
  have h34 : (ratIv 3 4).Mem ((3 : ℝ) / 4) := RatIvSpec (p := 3) (q := 4) (by norm_num)
  have h := mem_mulr hmem h34
  simpa only [ptCuspB] using h

lemma small_ptOf244 : Small (ptOf 244) := GridFacts.2.2.2.2.1 244 (by norm_num)
lemma small_ptOf245 : Small (ptOf 245) := GridFacts.2.2.2.2.1 245 (by norm_num)
lemma small_ptOf779 : Small (ptOf 779) := GridFacts.2.2.2.2.1 779 (by norm_num)
lemma small_ptOf780 : Small (ptOf 780) := GridFacts.2.2.2.2.1 780 (by norm_num)
lemma small_ptCuspA : Small ptCuspA := GridFacts.2.2.2.2.2.1
lemma small_ptCuspB : Small ptCuspB := GridFacts.2.2.2.2.2.2.1

lemma mem_ptOf244 : (ptOf 244).Mem
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))) :=
  mem_ptOf 244 (by norm_num)
lemma mem_ptOf245 : (ptOf 245).Mem
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 245 : ℝ) : ℂ)))) :=
  mem_ptOf 245 (by norm_num)
lemma mem_ptOf779 : (ptOf 779).Mem
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 779 : ℝ) : ℂ)))) :=
  mem_ptOf 779 (by norm_num)
lemma mem_ptOf780 : (ptOf 780).Mem
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 780 : ℝ) : ℂ)))) :=
  mem_ptOf 780 (by norm_num)

lemma dist_cuspA : (4 / 3) * ‖zCuspA * ((3 / 4 : ℝ) : ℂ)
    - Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ)))‖
    ≤ m2r (dWup (ptOf 244) ptCuspA) := by
  obtain ⟨-, hdW, -⟩ := DistSpec
  have h := hdW (ptOf 244) ptCuspA
    (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 244 : ℝ) : ℂ))))
    (zCuspA * ((3 / 4 : ℝ) : ℂ)) small_ptOf244 small_ptCuspA mem_ptOf244 mem_cuspA
  simpa only [norm_sub_rev] using h

lemma dist_cuspA2 : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 245 : ℝ) : ℂ)))
    - zCuspA * ((3 / 4 : ℝ) : ℂ)‖ ≤ m2r (dVup (ptOf 245) ptCuspA) :=
  (by obtain ⟨-, -, hdV, -⟩ := DistSpec
      exact hdV (ptOf 245) ptCuspA
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 245 : ℝ) : ℂ))))
        (zCuspA * ((3 / 4 : ℝ) : ℂ)) small_ptOf245 small_ptCuspA mem_ptOf245 mem_cuspA)

lemma dist_cuspB : (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 779 : ℝ) : ℂ)))
    - zCuspB * ((3 / 4 : ℝ) : ℂ)‖ ≤ m2r (dVup (ptOf 779) ptCuspB) :=
  (by obtain ⟨-, -, hdV, -⟩ := DistSpec
      exact hdV (ptOf 779) ptCuspB
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 779 : ℝ) : ℂ))))
        (zCuspB * ((3 / 4 : ℝ) : ℂ)) small_ptOf779 small_ptCuspB mem_ptOf779 mem_cuspB)

lemma dist_cuspB2 : (4 / 3) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 780 : ℝ) : ℂ)))
    - zCuspB * ((3 / 4 : ℝ) : ℂ)‖ ≤ m2r (dWup (ptOf 780) ptCuspB) :=
  (by obtain ⟨-, hdW, -⟩ := DistSpec
      exact hdW (ptOf 780) ptCuspB
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * ((arcθ 780 : ℝ) : ℂ))))
        (zCuspB * ((3 / 4 : ℝ) : ℂ)) small_ptOf780 small_ptCuspB mem_ptOf780 mem_cuspB)

lemma nonneg_dWup244 : 0 ≤ m2r (dWup (ptOf 244) ptCuspA) := m2r_nonneg (dWup_nonneg _ _)
lemma nonneg_dVup245 : 0 ≤ m2r (dVup (ptOf 245) ptCuspA) := m2r_nonneg (dVup_nonneg _ _)
lemma nonneg_dVup779 : 0 ≤ m2r (dVup (ptOf 779) ptCuspB) := m2r_nonneg (dVup_nonneg _ _)
lemma nonneg_dWup780 : 0 ≤ m2r (dWup (ptOf 780) ptCuspB) := m2r_nonneg (dWup_nonneg _ _)
lemma nonneg_ch1cuspA : 0 ≤ m2r (chord1 (dWup (ptOf 244) ptCuspA)) :=
  m2r_nonneg (chord1_nonneg _ (dWup_nonneg _ _))
lemma nonneg_ch2cuspA : 0 ≤ m2r (chord2 (dVup (ptOf 245) ptCuspA)) :=
  m2r_nonneg (chord2_nonneg _ (dVup_nonneg _ _))
lemma nonneg_ch2cuspB : 0 ≤ m2r (chord2 (dVup (ptOf 779) ptCuspB)) :=
  m2r_nonneg (chord2_nonneg _ (dVup_nonneg _ _))
lemma nonneg_ch1cuspB : 0 ≤ m2r (chord1 (dWup (ptOf 780) ptCuspB)) :=
  m2r_nonneg (chord1_nonneg _ (dWup_nonneg _ _))

lemma chord1_sound (d : ℤ) (hd : 0 ≤ m2r d) :
    400 * (m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2 ≤ m2r (chord1 d) :=
  DistSpec.2.2.2.1 d hd

lemma chord2_sound (d : ℤ) (hd : 0 ≤ m2r d) :
    1000 * (m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2 ≤ m2r (chord2 d) :=
  DistSpec.2.2.2.2 d hd

lemma Gv244_eq : Gv 244 = max (max (svUp (ptOf 244)) (svUp ptCuspA))
    (max (svUp (ptOf 245)) (svUp ptCuspA))
    + max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA)) := by
  rw [Gv]
  rw [if_neg (by norm_num : ¬ ((244 : ℕ) ≤ 243)), if_pos rfl]

lemma Gv779_eq : Gv 779 = max (max (svUp (ptOf 779)) (svUp ptCuspB))
    (max (svUp (ptOf 780)) (svUp ptCuspB))
    + max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB)) := by
  rw [Gv]
  rw [if_neg (by norm_num : ¬ ((779 : ℕ) ≤ 243)), if_neg (by norm_num : ¬ ((779 : ℕ) = 244)),
    if_neg (by norm_num : ¬ ((779 : ℕ) ≤ 778)), if_pos rfl]

end

end Work.CNum
