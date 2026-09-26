import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRectCl
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.differentiableOn_AfunFun_fst
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Residues.phiPlus_crossed_translates_eq_zero
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Kernels.KernelFacts.KPlus_T2

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane Filter Matrix

open scoped Topology MatrixGroups

noncomputable section

open Work.Kernels Work.Residues

/-! ## Toolbox -/

/-- The lift of `j` to the upper half plane is complex differentiable. -/
lemma diffAt_jLift_of (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) z := by
  have hmd := Work.Asymptotics.mdifferentiable_jInvariantFun (UpperHalfPlane.ofComplex z)
  have h := (UpperHalfPlane.mdifferentiableAt_iff (f := Work.Kernels.jInvariantFun)
    (τ := UpperHalfPlane.ofComplex z)).mp hmd
  simp only [Function.comp_def] at h
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk] at h
  exact h

/-- The lift of `AfunFun` (in the second variable) is complex differentiable. -/
lemma diffAt_afunLift_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w : ℂ => Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) z := by
  have hmd := Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ (UpperHalfPlane.ofComplex z)
  have h := (UpperHalfPlane.mdifferentiableAt_iff
    (f := fun w : UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d τ w)
    (τ := UpperHalfPlane.ofComplex z)).mp hmd
  simp only [Function.comp_def] at h
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk] at h
  exact h

/-- **The principal part at a simple pole in the second variable.**  Let `w₁` be a point with
`j w₁ = j τ` and `j' w₁ ≠ 0`.  Then `z ↦ K^{(d)}(τ, z)` has at `z₁ = w₁` a simple pole with
residue `-AfunFun ℓ d τ w₁ / j' w₁` and a holomorphic (hence locally bounded) remainder. -/
theorem localPrincipalPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ w₁ : UpperHalfPlane) (hJ : Work.Kernels.jInvariantFun w₁ = Work.Kernels.jInvariantFun τ)
    (hnz : Work.Residues.jprime w₁ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im → z ≠ (w₁ : ℂ) →
      ‖z - (w₁ : ℂ)‖ < r →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)
        - (-(Work.Asymptotics.AfunFun ℓ d τ w₁) / Work.Residues.jprime w₁) / (z - (w₁ : ℂ))‖ ≤ M := by
  set z₁ : ℂ := (w₁ : ℂ) with hz₁
  have hz₁im : 0 < z₁.im := w₁.im_pos
  set J : ℂ → ℂ := fun z => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) with hJdef
  set A : ℂ → ℂ := fun z => Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex z) with hAdef
  set ρ₀ : ℝ := z₁.im / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hball_im : Metric.ball z₁ ρ₀ ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_im_le_norm (z - z₁)
    rw [Complex.sub_im] at h
    have habs : |z.im - z₁.im| < ρ₀ := lt_of_le_of_lt h hz
    have h2 : z₁.im - ρ₀ < z.im := by
      have := (abs_lt.mp habs).1
      linarith
    show 0 < z.im
    rw [hρ₀def] at h2
    linarith
  have hJdiff : DifferentiableOn ℂ J (Metric.ball z₁ ρ₀) := fun z hz =>
    (diffAt_jLift_of z (hball_im hz)).differentiableWithinAt
  have hAdiff : DifferentiableOn ℂ A (Metric.ball z₁ ρ₀) := fun z hz =>
    (diffAt_afunLift_of ℓ d hd τ z (hball_im hz)).differentiableWithinAt
  have hmem₀ : Metric.ball z₁ ρ₀ ∈ 𝓝 z₁ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ₀pos)
  have hJcomp : J = Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex := by
    rw [hJdef]; funext z; rfl
  have hΔDdiff : DifferentiableOn ℂ (dslope J z₁) (Metric.ball z₁ ρ₀) :=
    (Complex.differentiableOn_dslope (f := J) (c := z₁) (s := Metric.ball z₁ ρ₀) hmem₀).mpr hJdiff
  have hΔDz₁ : dslope J z₁ z₁ = Work.Residues.jprime w₁ := by
    rw [dslope_same, hJcomp, hz₁]
    exact Work.Asymptotics.deriv_jInvariantFun_ofComplex w₁
  have hΔDne : dslope J z₁ z₁ ≠ 0 := by rw [hΔDz₁]; exact hnz
  have hnormpos : 0 < ‖Work.Residues.jprime w₁‖ := norm_pos_iff.mpr hnz
  -- a radius on which the slope of `j` stays away from zero
  obtain ⟨δ₀, hδ₀pos, hδ₀bd⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ z : ℂ, dist z z₁ < δ₀ →
      ‖Work.Residues.jprime w₁‖ / 2 ≤ ‖dslope J z₁ z‖ := by
    have hcont : ContinuousAt (dslope J z₁) z₁ := (hΔDdiff.differentiableAt hmem₀).continuousAt
    have hev : ∀ᶠ z in 𝓝 z₁,
        ‖dslope J z₁ z - dslope J z₁ z₁‖ < ‖Work.Residues.jprime w₁‖ / 2 := by
      have h0 : Tendsto (fun z : ℂ => dslope J z₁ z - dslope J z₁ z₁) (𝓝 z₁) (𝓝 0) := by
        simpa using hcont.tendsto.sub_const (dslope J z₁ z₁)
      exact h0.norm.eventually (eventually_lt_nhds (by simp only [norm_zero]; linarith))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀, hbd⟩ := hev
    refine ⟨δ₀, hδ₀, fun z hz => ?_⟩
    have h1 : ‖dslope J z₁ z - dslope J z₁ z₁‖ < ‖Work.Residues.jprime w₁‖ / 2 := hbd hz
    rw [hΔDz₁] at h1
    have h2 : ‖Work.Residues.jprime w₁‖
        ≤ ‖dslope J z₁ z‖ + ‖dslope J z₁ z - Work.Residues.jprime w₁‖ := by
      calc ‖Work.Residues.jprime w₁‖
            = ‖(Work.Residues.jprime w₁ - dslope J z₁ z) + dslope J z₁ z‖ := by
              rw [sub_add_cancel]
        _ ≤ ‖Work.Residues.jprime w₁ - dslope J z₁ z‖ + ‖dslope J z₁ z‖ := norm_add_le _ _
        _ = ‖dslope J z₁ z - Work.Residues.jprime w₁‖ + ‖dslope J z₁ z‖ := by rw [norm_sub_rev]
        _ = ‖dslope J z₁ z‖ + ‖dslope J z₁ z - Work.Residues.jprime w₁‖ := by ring
    linarith
  set ρ : ℝ := min ρ₀ δ₀ with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos hδ₀pos
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρδ₀ : ρ ≤ δ₀ := min_le_right _ _
  set H : ℂ → ℂ := fun z => -(A z) / dslope J z₁ z with hHdef
  have hHdiffAt : DifferentiableAt ℂ H z₁ := by
    have hA₁ : DifferentiableAt ℂ A z₁ := hAdiff.differentiableAt hmem₀
    have hD₁ : DifferentiableAt ℂ (dslope J z₁) z₁ := hΔDdiff.differentiableAt hmem₀
    have h : DifferentiableAt ℂ (fun z => -(A z) / dslope J z₁ z) z₁ := (hA₁.neg).div hD₁ hΔDne
    simpa [hHdef] using h
  have hAz₁ : A z₁ = Work.Asymptotics.AfunFun ℓ d τ w₁ := by
    simp only [hAdef]
    rw [hz₁, UpperHalfPlane.ofComplex_apply]
  have hHvalue : H z₁ = -(Work.Asymptotics.AfunFun ℓ d τ w₁) / Work.Residues.jprime w₁ := by
    rw [show H z₁ = -(A z₁) / dslope J z₁ z₁ from by simp only [hHdef], hΔDz₁, hAz₁]
  have hcont : ContinuousAt (dslope H z₁) z₁ := continuousAt_dslope_same.mpr hHdiffAt
  obtain ⟨r, hrpos, hbdH⟩ : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, dist z z₁ < r →
      ‖dslope H z₁ z - deriv H z₁‖ < 1 := by
    obtain ⟨r, hr, hbd⟩ := Metric.continuousAt_iff.mp hcont (1 : ℝ) one_pos
    refine ⟨r, hr, fun z hz => ?_⟩
    have h1 := hbd hz
    rwa [dslope_same, dist_eq_norm] at h1
  refine ⟨min r ρ, lt_min hrpos hρpos, ‖deriv H z₁‖ + 1, by positivity, ?_⟩
  intro z hzim hzne hzlt
  have hzρ : ‖z - z₁‖ < ρ := lt_of_lt_of_le hzlt (min_le_right _ _)
  have hzr : ‖z - z₁‖ < r := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hdist : dist z z₁ < r := by rw [dist_eq_norm]; exact hzr
  have hΔDz_nz : dslope J z₁ z ≠ 0 := by
    have h1 : ‖Work.Residues.jprime w₁‖ / 2 ≤ ‖dslope J z₁ z‖ :=
      hδ₀bd z (by rw [dist_eq_norm]; exact lt_of_lt_of_le hzρ hρδ₀)
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  have hJz : J z ≠ J z₁ := by
    intro h
    have hsub := sub_smul_dslope J z₁ z
    rw [smul_eq_mul, h, sub_self] at hsub
    rcases mul_eq_zero.mp hsub with h1 | h1
    · exact hzne (sub_eq_zero.mp h1)
    · exact hΔDz_nz h1
  have hJz₁eq : J z₁ = Work.Kernels.jInvariantFun τ := by
    simp only [hJdef, hz₁, UpperHalfPlane.ofComplex_apply]
    exact hJ
  have hjne : Work.Kernels.jInvariantFun τ
      ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) := by
    intro h
    have h1 : J z = Work.Kernels.jInvariantFun τ := by
      show Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) = Work.Kernels.jInvariantFun τ
      rw [← h]
    exact hJz (by rw [h1, hJz₁eq])
  have hmas : Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z) * (J z₁ - J z) = A z := by
    have h := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ (UpperHalfPlane.ofComplex z) hjne
    rw [← hJz₁eq] at h
    exact h
  have hJsub : J z - J z₁ = (z - z₁) * dslope J z₁ z := by
    have hsub := sub_smul_dslope J z₁ z
    rw [smul_eq_mul] at hsub
    exact hsub.symm
  have hkey : Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)
      - (-(Work.Asymptotics.AfunFun ℓ d τ w₁) / Work.Residues.jprime w₁) / (z - z₁)
      = dslope H z₁ z := by
    have hznez : z - z₁ ≠ 0 := sub_ne_zero.mpr hzne
    have hprod : (z - z₁) * dslope J z₁ z ≠ 0 := mul_ne_zero hznez hΔDz_nz
    have hk : Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)
        = -A z / ((z - z₁) * dslope J z₁ z) := by
      have h1 : J z₁ - J z = -((z - z₁) * dslope J z₁ z) := by rw [← hJsub]; ring
      rw [eq_div_iff hprod]
      rw [h1] at hmas
      linear_combination -hmas
    have hHz : H z = -(A z) / dslope J z₁ z := by simp only [hHdef]
    have hdsl : dslope H z₁ z = (H z - H z₁) / (z - z₁) := by
      rw [dslope_of_ne H hzne, slope_def_field]
    rw [hdsl, hk, hHz, hHvalue]
    field_simp
  rw [hkey]
  have hb := hbdH z hdist
  have h2 : ‖dslope H z₁ z‖ ≤ ‖dslope H z₁ z - deriv H z₁‖ + ‖deriv H z₁‖ := by
    have h := norm_add_le (dslope H z₁ z - deriv H z₁) (deriv H z₁)
    rwa [sub_add_cancel] at h
  linarith

/-- The order-three elliptic point `ρ = -1/2 + (√3/2)i = e^{2πi/3}`. -/
def rhoH : ℍ :=
  ⟨(-(1/2) : ℝ) + ((Real.sqrt 3) / 2 : ℝ) * Complex.I, by
    have h : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith⟩

lemma rhoH_coe_eq : (rhoH : ℂ) = ((-(1/2) : ℝ) : ℂ) + (((Real.sqrt 3) / 2 : ℝ) : ℂ) * Complex.I := rfl

lemma rhoH_re : (rhoH : ℂ).re = -(1/2) := by
  rw [rhoH_coe_eq]; simp

lemma rhoH_im : (rhoH : ℂ).im = Real.sqrt 3 / 2 := by
  rw [rhoH_coe_eq]; simp

lemma rhoH_sqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)

lemma rhoH_quad : (rhoH : ℂ) ^ 2 + (rhoH : ℂ) + 1 = 0 := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, pow_two, Complex.mul_re, rhoH_re, rhoH_im,
      Complex.zero_re]
    nlinarith [rhoH_sqrt_sq]
  · simp only [Complex.add_im, Complex.one_im, pow_two, Complex.mul_im, rhoH_re, rhoH_im,
      Complex.zero_im]
    ring

lemma rhoH_cube : (rhoH : ℂ) ^ 3 = 1 := by
  have h := rhoH_quad
  have hh : (rhoH : ℂ) ^ 3 - 1 = ((rhoH : ℂ) - 1) * ((rhoH : ℂ) ^ 2 + (rhoH : ℂ) + 1) := by ring
  rw [h, mul_zero] at hh
  linear_combination hh

lemma S_smul_rhoH_eq_T : ModularGroup.S • rhoH = ModularGroup.T • rhoH := by
  have hρ : (rhoH : ℂ) ≠ 0 := rhoH.ne_zero
  have h2 : (rhoH : ℂ) ^ 2 + (rhoH : ℂ) = -1 := by
    have h := rhoH_quad; linear_combination h
  have hkey : (-1 : ℂ) / (rhoH : ℂ) = 1 + (rhoH : ℂ) := by
    rw [div_eq_iff hρ, ← h2]; ring
  apply UpperHalfPlane.ext
  rw [S_coe_eq, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  simpa only [Complex.ofReal_one] using hkey

lemma E4Fun_rhoH : E4Fun rhoH = 0 := by
  set u : ℂ := UFun rhoH with hu
  set v : ℂ := VFun rhoH with hv
  set w : ℂ := WFun rhoH with hw
  have hU1 : UFun (ModularGroup.S • rhoH) = -((rhoH : ℂ) ^ 2) * UFun rhoH :=
    Work.Rigidity.UFun_S rhoH
  have hU2 : UFun (ModularGroup.T • rhoH) = WFun rhoH := Work.Rigidity.UFun_T rhoH
  have hW1 : WFun (ModularGroup.S • rhoH) = -((rhoH : ℂ) ^ 2) * VFun rhoH :=
    Work.Rigidity.WFun_S rhoH
  have hW2 : WFun (ModularGroup.T • rhoH) = UFun rhoH := Work.Rigidity.WFun_T rhoH
  rw [S_smul_rhoH_eq_T] at hU1 hW1
  have hUW : w = -((rhoH : ℂ) ^ 2) * u := by
    rw [hw, hu]
    exact (hU1.symm.trans hU2).symm
  have hU : u = -((rhoH : ℂ)) * w := by
    have h2 : (-((rhoH : ℂ))) * (-((rhoH : ℂ) ^ 2) * u) = (-((rhoH : ℂ))) * w := by
      rw [hUW.symm]
    have h3 : (-((rhoH : ℂ))) * (-((rhoH : ℂ) ^ 2) * u) = u := by
      rw [show (-((rhoH : ℂ))) * (-((rhoH : ℂ) ^ 2) * u) = ((rhoH : ℂ) ^ 3) * u from by ring]
      rw [rhoH_cube, one_mul]
    rw [h3] at h2
    exact h2
  have hWV : u = -((rhoH : ℂ) ^ 2) * v := by
    rw [hu, hv]
    exact (hW1.symm.trans hW2).symm
  have hV : v = ((rhoH : ℂ) ^ 2) * w := by
    have h1 : -((rhoH : ℂ) ^ 2) * v = -((rhoH : ℂ)) * w := by
      rw [← hU]; exact hWV.symm
    have h2 : ((rhoH : ℂ) ^ 2) * v = ((rhoH : ℂ)) * w := by
      calc ((rhoH : ℂ) ^ 2) * v = -(-((rhoH : ℂ) ^ 2) * v) := by ring
        _ = -(-((rhoH : ℂ)) * w) := by rw [h1]
        _ = ((rhoH : ℂ)) * w := by ring
    have h3 : ((rhoH : ℂ) ^ 3) * v = ((rhoH : ℂ) ^ 2) * w := by
      calc ((rhoH : ℂ) ^ 3) * v = ((rhoH : ℂ)) * (((rhoH : ℂ) ^ 2) * v) := by ring
        _ = ((rhoH : ℂ)) * (((rhoH : ℂ)) * w) := by rw [h2]
        _ = ((rhoH : ℂ) ^ 2) * w := by ring
    rw [rhoH_cube, one_mul] at h3
    exact h3
  have hsq : ((rhoH : ℂ) ^ 2) ^ 2 = (rhoH : ℂ) := by
    calc ((rhoH : ℂ) ^ 2) ^ 2 = (rhoH : ℂ) ^ 4 := by ring
      _ = (rhoH : ℂ) ^ 3 * (rhoH : ℂ) := by ring
      _ = (rhoH : ℂ) := by rw [rhoH_cube, one_mul]
  have htheta := Work.Residues.KMinusT_E4Fun_eq_theta rhoH
  rw [show UFun rhoH = u from hu.symm, show VFun rhoH = v from hv.symm,
    show WFun rhoH = w from hw.symm] at htheta
  rw [htheta, hU, hV]
  rw [show (-((rhoH : ℂ)) * w) ^ 2 + (((rhoH : ℂ) ^ 2) * w) ^ 2 + w ^ 2
      = w ^ 2 * (((rhoH : ℂ) ^ 2) + ((rhoH : ℂ) ^ 2) ^ 2 + 1) from by ring]
  rw [hsq, rhoH_quad, mul_zero, zero_div]

lemma jInvariantFun_rhoH : jInvariantFun rhoH = 0 := by
  have h : jInvariantFun rhoH = E4Fun rhoH ^ 3 / DeltaFun rhoH := rfl
  rw [h, E4Fun_rhoH]
  norm_num

lemma jInvariantFun_eq_1728_of_E6Fun_eq_zero {z : ℍ} (h : E6Fun z = 0) :
    jInvariantFun z = 1728 := by
  have h1 : DeltaFun z * jInvariantFun z = E4Fun z ^ 3 :=
    ClassicalFacts.DeltaFun_mul_jInvariantFun z
  have h2 : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 :=
    Work.Residues.KMinusClearTS.disc_eq z
  have h3 : E4Fun z ^ 3 = 1728 * DeltaFun z := by rw [h2, h]; ring
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [h3] at h1
  exact mul_left_cancel₀ hD (by rw [h1]; ring)

lemma E6Fun_I_eq_zero : E6Fun (UpperHalfPlane.I) = 0 := by
  have hS : ModularGroup.S • (UpperHalfPlane.I) = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [S_coe_eq, UpperHalfPlane.coe_I]
    rw [div_eq_iff Complex.I_ne_zero, Complex.I_mul_I]
  have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
  rw [hS] at h
  have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
    rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [hI6, neg_one_mul] at h
  have h2 : (2 : ℂ) * E6Fun UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

lemma jInvariantFun_I : jInvariantFun (UpperHalfPlane.I) = 1728 :=
  jInvariantFun_eq_1728_of_E6Fun_eq_zero E6Fun_I_eq_zero

/-! ### The orbit coordinates -/

lemma rho_sqrt_mul : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
  rw [← sq]; exact rhoH_sqrt_sq

lemma coe_sl2_rho (γ : SL(2,ℤ)) :
    ((γ • rhoH : ℍ) : ℂ)
      = (((γ 0 0 : ℤ) : ℂ) * (rhoH : ℂ) + ((γ 0 1 : ℤ) : ℂ))
        / (((γ 1 0 : ℤ) : ℂ) * (rhoH : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq]
  simp

lemma aff_re (c d : ℤ) :
    ((((c : ℤ) : ℂ) * (rhoH : ℂ) + ((d : ℤ) : ℂ)).re) = (d : ℝ) - (c : ℝ) / 2 := by
  rw [Complex.add_re, Complex.mul_re, rhoH_re, rhoH_im]
  have h1 : ((c : ℤ) : ℂ).re = (c : ℝ) := by simp
  have h2 : ((c : ℤ) : ℂ).im = 0 := by simp
  have h3 : ((d : ℤ) : ℂ).re = (d : ℝ) := by simp
  rw [h1, h2, h3]; ring

lemma aff_im (c d : ℤ) :
    ((((c : ℤ) : ℂ) * (rhoH : ℂ) + ((d : ℤ) : ℂ)).im) = (c : ℝ) * (Real.sqrt 3 / 2) := by
  rw [Complex.add_im, Complex.mul_im, rhoH_re, rhoH_im]
  have h1 : ((c : ℤ) : ℂ).re = (c : ℝ) := by simp
  have h2 : ((c : ℤ) : ℂ).im = 0 := by simp
  have h3 : ((d : ℤ) : ℂ).im = 0 := by simp
  rw [h1, h2, h3]; ring

lemma aff_normSq (c d : ℤ) :
    Complex.normSq (((c : ℤ) : ℂ) * (rhoH : ℂ) + ((d : ℤ) : ℂ))
      = (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    rhoH_re, rhoH_im]
  have h1 : ((c : ℤ) : ℂ).re = (c : ℝ) := by simp
  have h2 : ((c : ℤ) : ℂ).im = 0 := by simp
  have h3 : ((d : ℤ) : ℂ).re = (d : ℝ) := by simp
  have h4 : ((d : ℤ) : ℂ).im = 0 := by simp
  rw [h1, h2, h3, h4]
  nlinarith [rho_sqrt_mul]

lemma det_eq_one (γ : SL(2,ℤ)) :
    ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
  have h := γ.2
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

lemma orbit_im_rhoH (γ : SL(2,ℤ)) :
    ((γ • rhoH : ℍ) : ℂ).im = (Real.sqrt 3 / 2) /
      (((γ 1 0 : ℤ) : ℝ) ^ 2 - (((γ 1 0 : ℤ) : ℝ)) * (((γ 1 1 : ℤ) : ℝ))
        + (((γ 1 1 : ℤ) : ℝ)) ^ 2) := by
  rw [coe_sl2_rho γ, Complex.div_im, aff_im, aff_re, aff_im, aff_re, aff_normSq]
  rw [div_sub_div_same]
  congr 1
  linear_combination (Real.sqrt 3 / 2) * det_eq_one γ

lemma orbit_re_rhoH (γ : SL(2,ℤ)) :
    ((γ • rhoH : ℍ) : ℂ).re
      = ((((γ 0 0 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) + ((γ 0 1 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ))
          - (((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
              + ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ)) / 2)
        / (((γ 1 0 : ℤ) : ℝ) ^ 2 - ((γ 1 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
            + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
  rw [coe_sl2_rho γ, Complex.div_re, aff_re, aff_im, aff_re, aff_im, aff_normSq]
  rw [← add_div]
  congr 1
  ring_nf
  rw [rhoH_sqrt_sq]
  ring

/-! ### The orbit coordinates of `i` -/

lemma coe_sl2_I (γ : SL(2,ℤ)) :
    ((γ • UpperHalfPlane.I : ℍ) : ℂ)
      = (((γ 0 0 : ℤ) : ℂ) * Complex.I + ((γ 0 1 : ℤ) : ℂ))
        / (((γ 1 0 : ℤ) : ℂ) * Complex.I + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq]
  rw [UpperHalfPlane.coe_I]
  simp

lemma Iaff_re (c d : ℤ) : ((((c : ℤ) : ℂ) * Complex.I + ((d : ℤ) : ℂ)).re) = (d : ℝ) := by
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h1 : ((c : ℤ) : ℂ).im = 0 := by simp
  have h3 : ((d : ℤ) : ℂ).re = (d : ℝ) := by simp
  rw [h1, h3]; ring

lemma Iaff_im (c d : ℤ) : ((((c : ℤ) : ℂ) * Complex.I + ((d : ℤ) : ℂ)).im) = (c : ℝ) := by
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 : ((c : ℤ) : ℂ).re = (c : ℝ) := by simp
  have h3 : ((d : ℤ) : ℂ).im = 0 := by simp
  rw [h1, h3]; ring

lemma Iaff_normSq (c d : ℤ) :
    Complex.normSq (((c : ℤ) : ℂ) * Complex.I + ((d : ℤ) : ℂ))
      = (c : ℝ) ^ 2 + (d : ℝ) ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  have h1 : ((c : ℤ) : ℂ).re = (c : ℝ) := by simp
  have h2 : ((c : ℤ) : ℂ).im = 0 := by simp
  have h3 : ((d : ℤ) : ℂ).re = (d : ℝ) := by simp
  have h4 : ((d : ℤ) : ℂ).im = 0 := by simp
  rw [h1, h2, h3, h4]; ring

lemma orbit_im_I (γ : SL(2,ℤ)) :
    ((γ • UpperHalfPlane.I : ℍ) : ℂ).im
      = 1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
  rw [coe_sl2_I γ, Complex.div_im, Iaff_im, Iaff_re, Iaff_im, Iaff_re, Iaff_normSq]
  rw [div_sub_div_same]
  congr 1
  linear_combination det_eq_one γ

lemma orbit_re_I (γ : SL(2,ℤ)) :
    ((γ • UpperHalfPlane.I : ℍ) : ℂ).re
      = (((γ 0 0 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) + ((γ 0 1 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ))
        / (((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
  rw [coe_sl2_I γ, Complex.div_re, Iaff_re, Iaff_im, Iaff_re, Iaff_im, Iaff_normSq]
  rw [← add_div]
  congr 1
  ring

/-! ### Non-vanishing of `j'` at the first pole -/

lemma sq_ge_one (x : ℤ) (h : x ≠ 0) : (1 : ℤ) ≤ x * x := by
  by_cases h1 : 1 ≤ x
  · nlinarith
  · have h2 : x ≤ -1 := by omega
    nlinarith

lemma form_ge_one (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) : (1 : ℤ) ≤ c ^ 2 - c * d + d ^ 2 := by
  have h2 : (2 : ℤ) * (c ^ 2 - c * d + d ^ 2) = c ^ 2 + d ^ 2 + (c - d) ^ 2 := by ring
  have h3 : (1 : ℤ) ≤ c ^ 2 + d ^ 2 + (c - d) ^ 2 := by
    rcases h with hc | hd
    · have hc1 : (1 : ℤ) ≤ c * c := sq_ge_one c hc
      nlinarith [sq_nonneg d, sq_nonneg (c - d)]
    · have hd1 : (1 : ℤ) ≤ d * d := sq_ge_one d hd
      nlinarith [sq_nonneg c, sq_nonneg (c - d)]
  omega

lemma bottom_row_ne (γ : SL(2,ℤ)) : γ 1 0 ≠ 0 ∨ γ 1 1 ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hd := γ.2
  rw [Matrix.det_fin_two, h1, h2] at hd
  norm_num at hd

lemma sqrt3_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]

lemma E4Fun_poleOne_ne_zero (τ : ℍ) (hτ : τ ∈ ctanRegion) : E4Fun (poleOne τ) ≠ 0 := by
  intro h0
  have hj0 : jInvariantFun (poleOne τ) = 0 := by
    have h : jInvariantFun (poleOne τ) = E4Fun (poleOne τ) ^ 3 / DeltaFun (poleOne τ) := rfl
    rw [h, h0]; norm_num
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq (τ := poleOne τ) (w := rhoH)
    (by rw [hj0, jInvariantFun_rhoH])
  have him := orbit_im_rhoH γ
  rw [hγ, UpperHalfPlane.coe_im] at him
  have hgeo := tangPoleGeom τ hτ
  set c : ℤ := γ 1 0 with hc
  set d : ℤ := γ 1 1 with hd
  have hXeq : (((γ 1 0 : ℤ) : ℝ) ^ 2 - ((γ 1 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
        + ((γ 1 1 : ℤ) : ℝ) ^ 2) = ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℝ) := by
    rw [hc, hd]; push_cast; ring
  rw [hXeq] at him
  have hXpos : 0 < ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℝ) := by
    have : (0 : ℤ) < c ^ 2 - c * d + d ^ 2 := by
      have := form_ge_one c d (bottom_row_ne γ); omega
    exact_mod_cast this
  have hXlt : ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℝ) < Real.sqrt 3 := by
    have h1 : (1 / 2 : ℝ) < (poleOne τ).im := hgeo.2.2.1
    rw [him, lt_div_iff₀ hXpos] at h1
    nlinarith [h1]
  have hn_eq : c ^ 2 - c * d + d ^ 2 = 1 := by
    have h2 : ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℝ) < 2 := lt_trans hXlt sqrt3_lt_two
    have h3 : c ^ 2 - c * d + d ^ 2 < 2 := by exact_mod_cast h2
    have h4 : (1 : ℤ) ≤ c ^ 2 - c * d + d ^ 2 := form_ge_one c d (bottom_row_ne γ)
    omega
  have hre := orbit_re_rhoH γ
  rw [hγ, UpperHalfPlane.coe_re, hXeq, show ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℝ) = 1 from by
    rw [hn_eq]; norm_num, div_one] at hre
  set m : ℤ := 2 * (γ 0 0 : ℤ) * (γ 1 0 : ℤ) + 2 * (γ 0 1 : ℤ) * (γ 1 1 : ℤ)
    - (γ 0 0 : ℤ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) with hm
  have h2re : 2 * (poleOne τ).re = (m : ℝ) := by
    rw [hre, hm]; push_cast; ring
  have hmpos : 0 < m := by
    by_contra h
    push_neg at h
    have : (m : ℝ) ≤ 0 := by exact_mod_cast h
    linarith [hgeo.1, h2re]
  have hmlt : m < 1 := by
    by_contra h
    push_neg at h
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith [hgeo.2.1, h2re]
  omega

lemma E6Fun_poleOne_ne_zero (τ : ℍ) (hτ : τ ∈ ctanRegion) : E6Fun (poleOne τ) ≠ 0 := by
  intro h0
  have hj0 : jInvariantFun (poleOne τ) = 1728 := jInvariantFun_eq_1728_of_E6Fun_eq_zero h0
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq (τ := poleOne τ) (w := UpperHalfPlane.I)
    (by rw [hj0, jInvariantFun_I])
  have him := orbit_im_I γ
  rw [hγ, UpperHalfPlane.coe_im] at him
  have hgeo := tangPoleGeom τ hτ
  set c : ℤ := γ 1 0 with hc
  set d : ℤ := γ 1 1 with hd
  have hXeq : (((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) = ((c ^ 2 + d ^ 2 : ℤ) : ℝ) := by
    rw [hc, hd]; push_cast; ring
  rw [hXeq] at him
  have hXpos : 0 < ((c ^ 2 + d ^ 2 : ℤ) : ℝ) := by
    have h := bottom_row_ne γ
    have : (0 : ℤ) < c ^ 2 + d ^ 2 := by
      rcases h with hc0 | hd0
      · have := sq_ge_one c hc0; nlinarith [sq_nonneg d]
      · have := sq_ge_one d hd0; nlinarith [sq_nonneg c]
    exact_mod_cast this
  have hXlt : ((c ^ 2 + d ^ 2 : ℤ) : ℝ) < 2 := by
    have h1 : (1 / 2 : ℝ) < (poleOne τ).im := hgeo.2.2.1
    rw [him, lt_div_iff₀ hXpos] at h1
    linarith
  have hn_eq : c ^ 2 + d ^ 2 = 1 := by
    have h3 : c ^ 2 + d ^ 2 < 2 := by exact_mod_cast hXlt
    have h4 : (1 : ℤ) ≤ c ^ 2 + d ^ 2 := by
      have h := bottom_row_ne γ
      rcases h with hc0 | hd0
      · have := sq_ge_one c hc0; nlinarith [sq_nonneg d]
      · have := sq_ge_one d hd0; nlinarith [sq_nonneg c]
    omega
  have hre := orbit_re_I γ
  rw [hγ, UpperHalfPlane.coe_re, hXeq,
    show ((c ^ 2 + d ^ 2 : ℤ) : ℝ) = 1 from by rw [hn_eq]; norm_num, div_one] at hre
  set m : ℤ := (γ 0 0 : ℤ) * (γ 1 0 : ℤ) + (γ 0 1 : ℤ) * (γ 1 1 : ℤ) with hm
  have hre' : (poleOne τ).re = (m : ℝ) := by
    rw [hre, hm]; push_cast; ring
  have hmpos : 0 < m := by
    by_contra h
    push_neg at h
    have : (m : ℝ) ≤ 0 := by exact_mod_cast h
    linarith [hgeo.1, hre']
  have hmlt : m < 1 := by
    by_contra h
    push_neg at h
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith [hgeo.2.1, hre']
  omega

theorem jprimePoleOneNeZero (τ : UpperHalfPlane)
    (hτ : τ ∈ Work.Asymptotics.HalfFunnel.ctanRegion) :
    Work.Residues.jprime (Work.Asymptotics.HalfFunnel.poleOne τ) ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff]
  exact mul_ne_zero (E4Fun_poleOne_ne_zero τ hτ) (E6Fun_poleOne_ne_zero τ hτ)

/-! ### The cleared kernel vanishes at the first pole -/

lemma phiMinus_eq_sigmaR (x : Work.Kernels.R) :
    Work.Residues.phiMinus x = (Work.Residues.sigmaR x) 0 1 + (Work.Residues.sigmaR x) 0 4 := by
  have h := Work.Residues.rowDiff_mem_of_idealI x 0
  rw [Work.Residues.rowDiff, Work.Residues.M6_zero, one_mul] at h
  have h' : x - ∑ j, (Work.Residues.sigmaR x) 0 j • Work.Residues.M6 j
      ∈ Work.Residues.idealIm := Work.Residues.idealI_le_idealIm h
  have hkey : Work.Residues.phiMinus x
      = Work.Residues.phiMinus (∑ j, (Work.Residues.sigmaR x) 0 j • Work.Residues.M6 j) := by
    have h0 : Work.Residues.phiMinus
        (x - ∑ j, (Work.Residues.sigmaR x) 0 j • Work.Residues.M6 j) = 0 :=
      Work.Residues.phiMinus_eq_zero_of_mem_idealIm h'
    have hsub := map_sub (Work.Residues.phiMinus) x
      (∑ j, (Work.Residues.sigmaR x) 0 j • Work.Residues.M6 j)
    rw [h0] at hsub
    exact sub_eq_zero.mp hsub.symm
  rw [hkey, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Fin.sum_univ_six]
  simp only [Work.Residues.M6_zero, Work.Residues.M6_one, Work.Residues.M6_two,
    Work.Residues.M6_three, Work.Residues.M6_four, Work.Residues.M6_five,
    Work.Residues.phiMinus_one, Work.Residues.phiMinus_R_T, Work.Residues.phiMinus_TS,
    Work.Residues.phiMinus_R_S, Work.Residues.phiMinus_ST, Work.Residues.phiMinus_STS]
  ring

lemma phiPlus_add_phiMinus_eq (x : Work.Kernels.R) :
    (Work.Residues.phiPlus x + Work.Residues.phiMinus x : ℂ) = 2 * Work.Residues.phi x := by
  rw [Work.Residues.phiPlus_eq_sigmaR, phiMinus_eq_sigmaR, Work.Residues.phi_eq_sigmaR]
  ring

lemma AfunFun_poleOne_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    Work.Asymptotics.AfunFun ℓ d τ (poleOne τ) = 0 := by
  have hnz := jprimePoleOneNeZero τ hτ
  have key : Work.Kernels.KfunClear ℓ d τ (poleOne τ) = 0 := by
    rcases lt_or_ge τ.re 0 with hneg | hpos
    · have hpo : poleOne τ = (ModularGroup.T * ModularGroup.S * ModularGroup.T) • τ := by
        rw [poleOne, if_pos hneg]
      have hδ : Work.Residues.phiPlus
            (MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹)
              (1 : ℂ))
          + Work.Residues.phiMinus
            (MonoidAlgebra.single ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹)
              (1 : ℂ)) = 0 := by
        have h := (Work.Residues.phi_Tpow_mul_inv_eq_zero (-1)).1
        rw [_root_.zpow_neg_one, MonoidAlgebra.single_mul_single] at h
        have h2 : (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹
            = ModularGroup.T⁻¹ * (ModularGroup.T * ModularGroup.S)⁻¹ := by group
        rw [← h2, show (1 * 1 : ℂ) = 1 from by norm_num] at h
        rw [phiPlus_add_phiMinus_eq, h, mul_zero]
      have hres := Work.Asymptotics.KfunClear_vanish_of_phiPair ℓ d hd
        ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) hδ (poleOne τ) hnz
      rw [show ((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • (poleOne τ) = τ from by
        rw [hpo, inv_smul_smul]] at hres
      exact hres
    · have hpo : poleOne τ = (ModularGroup.T * ModularGroup.S) • τ := by
        rw [poleOne, if_neg (not_lt.mpr hpos), mul_smul, UpperHalfPlane.modular_T_smul]
      have hδ : Work.Residues.phiPlus
            (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S)⁻¹ (1 : ℂ))
          + Work.Residues.phiMinus
            (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S)⁻¹ (1 : ℂ)) = 0 := by
        have h := (Work.Residues.phi_Tpow_mul_inv_eq_zero 0).1
        have h0 : Work.Residues.phi
            (MonoidAlgebra.single (ModularGroup.T * ModularGroup.S)⁻¹ (1 : ℂ)) = 0 := by
          simpa using h
        rw [phiPlus_add_phiMinus_eq, h0, mul_zero]
      have hres := Work.Asymptotics.KfunClear_vanish_of_phiPair ℓ d hd
        ((ModularGroup.T * ModularGroup.S)⁻¹) hδ (poleOne τ) hnz
      rw [show ((ModularGroup.T * ModularGroup.S)⁻¹) • (poleOne τ) = τ from by
        rw [hpo, inv_smul_smul]] at hres
      exact hres
  have hfac := Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d τ (poleOne τ)
  rw [hfac] at key
  exact (mul_eq_zero.mp key).resolve_left
    (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero (poleOne τ))))

/-! ## The principal part at the first pole -/

/-- **The principal part of the kernel at the first pole.**

`∃ C ≥ 0` such that for every `τ ∈ ctanRegion` there is `c : ℂ` with `‖c‖ ≤ C` and a radius
`r > 0` and a bound `M ≥ 0` with `‖Kfun ℓ d τ (ofComplex z) - c/(z - z₁)‖ ≤ M` for all `z` with
`0 < Im z`, `z ≠ z₁`, `‖z - z₁‖ < r`, where `z₁ = poleOne τ`.

Here `z₁ = poleOne τ` is the point of the `SL(2,ℤ)`-orbit of `τ` that crosses the contour, and
its *residue* is `-AfunFun ℓ d τ (poleOne τ) / j'(poleOne τ)`, which vanishes by
`AfunFun_poleOne_eq_zero`; `C = 0` therefore suffices. -/
theorem tangPrincipalPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.HalfFunnel.ctanRegion →
      ∃ c : ℂ, ‖c‖ ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 < z.im →
        z ≠ ((Work.Asymptotics.HalfFunnel.poleOne τ : UpperHalfPlane) : ℂ) →
        ‖z - ((Work.Asymptotics.HalfFunnel.poleOne τ : UpperHalfPlane) : ℂ)‖ < r →
        ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)
          - c / (z - ((Work.Asymptotics.HalfFunnel.poleOne τ : UpperHalfPlane) : ℂ))‖ ≤ M := by
  refine ⟨0, le_refl 0, fun τ hτ => ?_⟩
  obtain ⟨r, hr, M, hM, hbound⟩ :=
    localPrincipalPart ℓ d hd τ (poleOne τ) (jInvariantFun_poleOne τ)
      (jprimePoleOneNeZero τ hτ)
  refine ⟨-(AfunFun ℓ d τ (poleOne τ)) / jprime (poleOne τ), ?_, r, hr, M, hM, ?_⟩
  · rw [AfunFun_poleOne_eq_zero ℓ d hd τ hτ]; simp
  · intro z hz hzne hzlt
    exact hbound z hz hzne hzlt

end

end Work.Asymptotics.HalfFunnel
