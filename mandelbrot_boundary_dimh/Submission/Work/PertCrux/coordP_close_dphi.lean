import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.exhaust_level_bound
import Submission.Work.Pert.Ksub2.Engine
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Setup2
import Submission.Work.Pert.Ksub2.Geom
import Submission.Work.Pert.Ksub2.exists_anchor_sharp
import Submission.Work.Pert.Ksub2.defect_le_fix
import Submission.Work.Pert.Ksub2.deriv_diff_le
import Submission.Work.Pert.Ksub2.iterate_two_seed
import Submission.Work.Pert.Ksub2.shadow_defect_le
import Submission.Work.Pert.Ksub2.shadow_orbit_le
import Submission.Work.Pert.Ksub2.f0_iterate_lipschitz_uniform_D
import Submission.Work.Pert.Ksub2.tauC_tau0_close_sharp
import Submission.Work.Pert.Ksub2.abel_on_gate
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.Ksub2.Xc_bounds_on_strip
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.Ksub2.exists_lipschitzOn_of_compact
import Submission.Work.Pert.Ksub2.exists_ball_local_inverse
import Submission.Work.Pert.Ksub2.exists_ball_subset_of_forall_mem
import Submission.Work.Pert.Ksub2.anchor_scale_deriv
import Submission.Work.Pert.Ksub2.anchor_scale_close
import Submission.Work.Pert.Ksub2.anchor_scale_geom
import Submission.Work.Pert.Ksub2.f0_iterate_lipschitz_uniform
import Submission.Work.Pert.Ksub2.F0f_near_translation_anchor
import Submission.Work.Pert.closedBall_subset_Qm
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.inv_close_of_deriv_close
import Submission.Work.Pert.tools
import Submission.Work.Pert.qadm
import Submission.Work.Pert.normalform_radius
import Submission.Work.Pert.coordP_level_eq
import Submission.Work.Pert.pin_shift
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Parab.inversion.exists_mul_log_lt
import Submission.Work.PertCrux.dev_le_of_deriv_diff_le
import Submission.Work.PertCrux.Xc_strip_log_bounds
import Submission.Work.PertCrux.tauC_ge_of_mem_Qm
import Submission.Work.PertCrux.tauC_tau0_close_of_far
import Submission.Work.PertCrux.f0_amp_uniform_K
import Submission.Work.PertCrux.orbit_nhd_uniform
import Submission.Work.PertCrux.exists_model_data
import Submission.Work.PertCrux.defect_le_of_trap

namespace Work.PertCrux

set_option maxHeartbeats 32000000

open MandelDim Complex Set Metric
open scoped Topology

noncomputable section

private theorem ball_subset_ball_of_dist {c c' : ℂ} {r r' : ℝ} (h : dist c c' + r ≤ r') :
    Metric.ball c r ⊆ Metric.ball c' r' := by
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  calc dist z c' ≤ dist z c + dist c c' := dist_triangle _ _ _
    _ < r + dist c c' := by linarith
    _ = dist c c' + r := by ring
    _ ≤ r' := h

private theorem le_of_small_bound {a δ₀ ηu_def Csm ρs rr Ξ : ℝ}
    (hU1 : a ≤ Csm * (δ₀ / ρs ^ 2 + δ₀ / (ρs * rr)))
    (hδ₀ηu : δ₀ ≤ ηu_def / (4 * Csm * max (1 / ρs ^ 2) (16 * Ξ / ρs)))
    (hρspos : 0 < ρs) (hrr : 0 < rr) (hCsmp : 0 < Csm) (hηupos : 0 < ηu_def)
    (hΞ : 0 < Ξ) (hrrge : 1 / (16 * Ξ) < rr) : a ≤ ηu_def := by
  set Mx : ℝ := max (1 / ρs ^ 2) (16 * Ξ / ρs) with hMx
  have hMxpos : 0 < Mx := by
    rw [hMx]; exact lt_max_of_lt_left (div_pos one_pos (pow_pos hρspos 2))
  have hδ₀ηu' : δ₀ ≤ ηu_def / (4 * Csm * Mx) := hδ₀ηu
  have hrr16 : (1:ℝ) / rr ≤ 16 * Ξ := by
    have h0 := hrrge
    rw [div_lt_iff₀ (by linarith [hΞ] : (0:ℝ) < 16 * Ξ)] at h0
    rw [div_le_iff₀ hrr]
    linarith
  have hm1 : (1:ℝ) ≤ Mx * ρs ^ 2 := by
    have h : (1 / ρs ^ 2) ≤ Mx := by
      have h1 := le_max_left (1 / ρs ^ 2) (16 * Ξ / ρs)
      rw [← hMx] at h1; exact h1
    have h2 : (1 / ρs ^ 2) * ρs ^ 2 = 1 := by
      rw [one_div, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hρspos))]
    have h3 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ ρs ^ 2)
    rwa [h2] at h3
  have hm2 : (1:ℝ) ≤ Mx * (ρs * rr) := by
    have h4 : (16 * Ξ / ρs) * (ρs * rr) ≤ Mx * (ρs * rr) := by
      have h1 := le_max_right (1 / ρs ^ 2) (16 * Ξ / ρs)
      rw [← hMx] at h1
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : (16 * Ξ / ρs) * (ρs * rr) = 16 * Ξ * rr := by
      field_simp
    have h6 : (1:ℝ) ≤ 16 * Ξ * rr := by
      have h7 := hrrge
      rw [div_lt_iff₀ (by linarith [hΞ] : (0:ℝ) < 16 * Ξ)] at h7
      linarith [h7]
    linarith [h4, h5, h6]
  have hK1 : δ₀ * (4 * Csm * Mx) ≤ ηu_def := by
    have hden : 0 < 4 * Csm * Mx := mul_pos (mul_pos (by norm_num) hCsmp) hMxpos
    have h := mul_le_mul_of_nonneg_right hδ₀ηu' hden.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at h
  have hC4pos : (0:ℝ) < 4 * Csm := mul_pos (by norm_num) hCsmp
  have hA : δ₀ / ρs ^ 2 ≤ ηu_def / (4 * Csm) := by
    rw [div_le_div_iff₀ (pow_pos hρspos 2) hC4pos]
    have h2 : δ₀ * (4 * Csm) ≤ ηu_def / Mx := by
      rw [le_div_iff₀ hMxpos]
      calc δ₀ * (4 * Csm) * Mx = δ₀ * (4 * Csm * Mx) := by ring
        _ ≤ ηu_def := hK1
    have h3 : (1:ℝ) ≤ ρs ^ 2 * Mx := by linarith [hm1, mul_comm Mx (ρs ^ 2)]
    calc δ₀ * (4 * Csm) ≤ ηu_def / Mx := h2
      _ ≤ ηu_def * ρs ^ 2 := by
          rw [div_le_iff₀ hMxpos]
          calc ηu_def = ηu_def * 1 := by ring
            _ ≤ ηu_def * (ρs ^ 2 * Mx) := mul_le_mul_of_nonneg_left h3 hηupos.le
            _ = ηu_def * ρs ^ 2 * Mx := by ring
  have hB : δ₀ / (ρs * rr) ≤ ηu_def / (4 * Csm) := by
    rw [div_le_div_iff₀ (mul_pos hρspos hrr) hC4pos]
    have h2 : δ₀ * (4 * Csm) ≤ ηu_def / Mx := by
      rw [le_div_iff₀ hMxpos]
      calc δ₀ * (4 * Csm) * Mx = δ₀ * (4 * Csm * Mx) := by ring
        _ ≤ ηu_def := hK1
    have h3 : (1:ℝ) ≤ ρs * rr * Mx := by linarith [hm2, mul_comm Mx (ρs * rr)]
    calc δ₀ * (4 * Csm) ≤ ηu_def / Mx := h2
      _ ≤ ηu_def * (ρs * rr) := by
          rw [div_le_iff₀ hMxpos]
          calc ηu_def = ηu_def * 1 := by ring
            _ ≤ ηu_def * (ρs * rr * Mx) := mul_le_mul_of_nonneg_left h3 hηupos.le
            _ = ηu_def * (ρs * rr) * Mx := by ring
  have h2C : Csm * (ηu_def / (4 * Csm)) = ηu_def / 4 := by
    field_simp
  refine le_trans hU1 ?_
  calc Csm * (δ₀ / ρs ^ 2 + δ₀ / (ρs * rr))
      = Csm * (δ₀ / ρs ^ 2) + Csm * (δ₀ / (ρs * rr)) := by ring
    _ ≤ Csm * (ηu_def / (4 * Csm)) + Csm * (ηu_def / (4 * Csm)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hCsmp.le)
          (mul_le_mul_of_nonneg_left hB hCsmp.le)
    _ = ηu_def / 2 := by rw [h2C]; ring
    _ ≤ ηu_def := by linarith [hηupos]

private theorem nearOn_mono {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hL : L' ⊆ L) (hδ : δ ≤ δ') :
    MandelDim.NearOn f₀ f Df L' δ' :=
  ⟨h.1, hL.trans h.2.1, h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z (hL hz)) hδ⟩

/-- Reverse triangle: `‖a - b‖ ≤ r` gives `‖b‖ - r ≤ ‖a‖`. -/
private theorem norm_lower_of_norm_sub_le {a b : ℂ} {r : ℝ} (h : ‖a - b‖ ≤ r) :
    ‖b‖ - r ≤ ‖a‖ := by
  have h1 := norm_sub_le a (a - b)
  rw [sub_sub_cancel] at h1
  linarith

/-- Division is monotone in both arguments (cross-multiplied form). -/
private theorem div_le_div_of_pos {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  have h1 : a / b * d ≤ c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    exact h
  rw [le_div_iff₀ hd]
  exact h1

/-- The anchor ball of radius `M/8` (the compact set on which the defect is estimated). -/
private def Danchor8 (M : ℝ) : Set ℂ := Metric.closedBall (((-M : ℝ) : ℂ)) (M / 8)

theorem coordP_close_of_sub_Dphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 0 < Ξ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.Dφ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∃ Φm : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) ∧
          K ⊆ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) ∧
          ∀ w ∈ K, ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w - d.φ w‖ < δ := by
  -- ################ the fixed constants
  obtain ⟨T, hTpos, hTK, CeA, ccA, MA, Kk, hCeA, hccA, hMA, hKk, hamp⟩ :=
    f0_amp_uniform_K d hKc hK
  obtain ⟨hFm, ρg, Dg, hρgpos, hρg8, hDgnn, hroomg, hFm0, hfe, hFd, hFl, hFb⟩ :=
    exists_model_data hd
  obtain ⟨r0, hr0pos, hroom0, Csm, hCsmp, hsmallOf⟩ := Work.Pert.small_of_nearOn hd
  obtain ⟨CX, MX, hCXpos, hMXpos, hXcb⟩ := Xc_strip_log_bounds d
  obtain ⟨Cdev, hCdevpos, hdevA⟩ := dev_le_of_deriv_diff_le hF.2.2.2.2.1
  obtain ⟨Cseed, hCseedpos, hseedD⟩ := tauC_tau0_close_of_far
  obtain ⟨Rde, C1, C2, hRdepos, hC1pos, hC2pos, hDEest⟩ := hF.2.2.2.2.1
  obtain ⟨Ras, hRaspos, hRasLem⟩ := Work.Pert.Ksub2.anchor_scale_deriv d
  obtain ⟨M0F0, hM0F0pos, hF0nt⟩ := Work.Pert.Ksub2.F0f_near_translation_anchor (D := Dg) d hρgpos hρg8 hroomg hfe hFm0 hFd
  obtain ⟨Robt, hRobtpos, hRobtD₀⟩ := orbit_nhd_uniform hd d hKc hK
  set ρs : ℝ := min ρg r0 with hρs
  have hρspos : 0 < ρs := lt_min hρgpos hr0pos
  have hρsρg : ρs ≤ ρg := min_le_left _ _
  have hρsr0 : ρs ≤ r0 := min_le_right _ _
  have hroom_s : Metric.closedBall (0 : ℂ) ρs ⊆ D₀ :=
    (Metric.closedBall_subset_closedBall hρsρg).trans hroomg
  -- ################ the fixed positive constant of the targets
  set Ky : ℝ := min (δ * ccA / (256 * CeA * Cseed))
      (min (ccA / (16 * Kk * Cseed)) (Robt * ccA / (128 * CeA * Cseed))) with hKy
  have hKypos : 0 < Ky := by
    rw [hKy]
    exact lt_min (div_pos (mul_pos hδ hccA) (mul_pos (mul_pos (by norm_num) hCeA) hCseedpos))
      (lt_min (div_pos hccA (mul_pos (mul_pos (by norm_num) hKk) hCseedpos))
        (div_pos (mul_pos hRobtpos hccA) (mul_pos (mul_pos (by norm_num) hCeA) hCseedpos)))
  have hKy1 : Ky ≤ δ * ccA / (256 * CeA * Cseed) := by rw [hKy]; exact min_le_left _ _
  have hKy2 : Ky ≤ ccA / (16 * Kk * Cseed) := by
    rw [hKy]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hKy3 : Ky ≤ Robt * ccA / (128 * CeA * Cseed) := by
    rw [hKy]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨RL1, hRL1pos, hRL1⟩ := Work.Parab.inversion.exists_mul_log_lt_aux (a := 80 * Cdev * CX)
      (b := 80 * Cdev * CX * (1 + T)) (c := 3 * Ky / 4) (by linarith [hKypos, hCdevpos, hCXpos, hTpos])
  obtain ⟨RL2, hRL2pos, hRL2⟩ := Work.Parab.inversion.exists_mul_log_lt_aux (a := CX)
      (b := CX * (1 + T)) (c := 1 / 320) (by norm_num)
  set R₁ : ℝ := max Rde (64 * C2) with hR1
  have hR1pos : 0 < R₁ := lt_max_of_lt_left hRdepos
  set thrs : Finset ℝ :=
    {MA, MX, 81, 2, Ξ + 1, 8 * Ξ + 8, 160 * T, 64 / (7 * ρg), Ras, 4 * R₁, M0F0, 64 * Ky,
      80 * Cdev, RL1, RL2, 1} with hthrs
  have hthrsne : thrs.Nonempty := ⟨1, by simp [hthrs]⟩
  set M₀ : ℝ := thrs.sup' hthrsne id with hM₀
  have hthr : ∀ a ∈ thrs, a ≤ M₀ := fun a ha => Finset.le_sup' (f := id) ha
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le one_pos (hthr 1 (by simp [hthrs]))
  obtain ⟨M, hMM₀, hMpos, Φ₀, hΦ₀an, hΦ₀inv, hΦ₀pin, hXcM⟩ :=
    Work.Pert.Ksub2.exists_anchor_sharp d M₀
  have hMle : ∀ a ∈ thrs, a ≤ M := fun a ha => le_trans (hthr a ha) hMM₀
  have hMA' : MA ≤ M := hMle MA (by simp [hthrs])
  have hMX' : MX ≤ M := hMle MX (by simp [hthrs])
  have h81 : (81 : ℝ) ≤ M := hMle 81 (by simp [hthrs])
  have hM2 : (2 : ℝ) ≤ M := hMle 2 (by simp [hthrs])
  have hMΞ : Ξ + 1 ≤ M := hMle (Ξ + 1) (by simp [hthrs])
  have hMΞ8 : 8 * Ξ + 8 ≤ M := hMle (8 * Ξ + 8) (by simp [hthrs])
  have hMT : 160 * T ≤ M := hMle (160 * T) (by simp [hthrs])
  have hMρg : 64 / (7 * ρg) ≤ M := hMle (64 / (7 * ρg)) (by simp [hthrs])
  have hMRas : Ras ≤ M := hMle Ras (by simp [hthrs])
  have hMR1 : 4 * R₁ ≤ M := hMle (4 * R₁) (by simp [hthrs])
  have hMM0F0 : M0F0 ≤ M := hMle M0F0 (by simp [hthrs])
  have hMKy : 64 * Ky ≤ M := hMle (64 * Ky) (by simp [hthrs])
  have hMCdev : 80 * Cdev ≤ M := hMle (80 * Cdev) (by simp [hthrs])
  have hlog1 : 80 * Cdev * (CX * (1 + T + Real.log M)) ≤ (3 * Ky / 4) * M := by
    have h := hRL1 M (hMle RL1 (by simp [hthrs]))
    have hlog : Real.log M ≤ Real.log (2 * M) := Real.log_le_log hMpos (by linarith)
    have hc : (0 : ℝ) ≤ 80 * Cdev * CX := by
      exact mul_nonneg (mul_nonneg (by norm_num) hCdevpos.le) hCXpos.le
    have hst : 80 * Cdev * CX * Real.log M ≤ 80 * Cdev * CX * Real.log (2 * M) :=
      mul_le_mul_of_nonneg_left hlog hc
    have hkey : 80 * Cdev * (CX * (1 + T + Real.log M))
        = 80 * Cdev * CX * Real.log M + 80 * Cdev * CX * (1 + T) := by ring
    rw [hkey]; linarith
  have hlog2 : CX * (1 + T + Real.log M) ≤ M / 320 := by
    have h := hRL2 M (hMle RL2 (by simp [hthrs]))
    have hlog : Real.log M ≤ Real.log (2 * M) := Real.log_le_log hMpos (by linarith)
    have hc : (0 : ℝ) ≤ CX := hCXpos.le
    have hst : CX * Real.log M ≤ CX * Real.log (2 * M) := mul_le_mul_of_nonneg_left hlog hc
    have hkey : CX * (1 + T + Real.log M) = CX * Real.log M + CX * (1 + T) := by ring
    rw [hkey]; linarith
  set Ugrow : ℝ := CX * (1 + T + Real.log M) with hUgrow
  have hUgrowpos : 0 < Ugrow := by
    rw [hUgrow]
    refine mul_pos hCXpos (by linarith [Real.log_nonneg (show (1:ℝ) ≤ M by linarith), hTpos])
  have hUgrowM : Ugrow ≤ M / 320 := hlog2
  have hTnonneg : 0 ≤ T := hTpos.le
  have hTleM : T ≤ M := by linarith [hMT, hTpos]
  have hTM4 : T + 1 ≤ M / 4 := by linarith [hMT, hM2]
  have hstrip_norm : ∀ z ∈ Work.Pert.Dstrip M T, ‖z + (M : ℂ)‖ ≤ M / 4 := by
    intro z hz
    have h1 := Complex.norm_le_abs_re_add_abs_im (z + (M : ℂ))
    have h2 : (z + (M : ℂ)).re = z.re + M := by simp
    have h3 : (z + (M : ℂ)).im = z.im := by simp
    have h4 : |z.re + M| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2.1]
    have h5 : |z.im| ≤ T := hz.2.2
    rw [h2, h3] at h1
    linarith [h1, h4, h5, hTM4]
  have hstrip4 : ∀ z ∈ Work.Pert.Dstrip M T, ‖z - ((((-M : ℝ)) : ℂ))‖ ≤ M / 4 := by
    intro z hz
    have h1 := hstrip_norm z hz
    have h2 : z - ((((-M : ℝ)) : ℂ)) = z + (M : ℂ) := by
      rw [show ((((-M : ℝ)) : ℂ)) = -((M : ℝ) : ℂ) from by simp]; ring
    rw [h2]; exact h1
  have hTM4s : T + 1 < M / 4 := by linarith [hMT, hM2, hTpos]
  have hstrip_lt : ∀ z ∈ Work.Pert.Dstrip M T, ‖z - ((((-M : ℝ)) : ℂ))‖ < M / 4 := by
    intro z hz
    have h1 := hstrip_norm z hz
    have h2 : z - ((((-M : ℝ)) : ℂ)) = z + (M : ℂ) := by
      rw [show ((((-M : ℝ)) : ℂ)) = -((M : ℝ) : ℂ) from by simp]; ring
    rw [h2]
    have h3 : ‖z + (M : ℂ)‖ ≤ T + 1 := by
      have h4 := Complex.norm_le_abs_re_add_abs_im (z + (M : ℂ))
      have h5 : (z + (M : ℂ)).re = z.re + M := by simp
      have h6 : (z + (M : ℂ)).im = z.im := by simp
      have h7 : |z.re + M| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hz.1, hz.2.1]
      rw [h5, h6] at h4
      linarith [h4, h7, hz.2.2]
    linarith [h3, hTM4s]
  have hballdef : Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (M / 40) ⊆ Danchor8 M := by
    refine subset_trans (ball_subset_ball_of_dist (c := Work.Pert.Xc d ((((-M : ℝ)) : ℂ)))
      (c' := ((((-M : ℝ)) : ℂ))) (r := M / 40) (r' := M / 8) ?_) Metric.ball_subset_closedBall
    rw [dist_eq_norm]
    linarith [hXcM]
  -- ################ the level bound
  set N : ℕ := (⌈T + M + 1⌉).toNat with hN
  have hNge : T + M + 1 ≤ (N : ℝ) := by
    have hpos0 : (0 : ℤ) < ⌈T + M + 1⌉ := Int.ceil_pos.mpr (by linarith : (0:ℝ) < T + M + 1)
    have hcast : ((⌈T + M + 1⌉).toNat : ℝ) = (⌈T + M + 1⌉ : ℝ) := by
      have h1 : ((⌈T + M + 1⌉).toNat : ℤ) = ⌈T + M + 1⌉ := Int.toNat_of_nonneg hpos0.le
      have h2 : ((⌈T + M + 1⌉).toNat : ℝ) = (((⌈T + M + 1⌉).toNat : ℤ) : ℝ) := by push_cast; ring
      rw [h2, h1]
    rw [hN, hcast]
    exact Int.le_ceil _
  -- ################ the targets of the seed comparison and of the defect
  set Θ : ℝ := 2 * CeA * M * M / ccA with hΘ
  have hΘpos : 0 < Θ := by
    rw [hΘ]
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCeA) hMpos) hMpos) hccA
  set eT : ℝ := 8 * Cseed * Ky / (M * M) with heT
  have heTpos : 0 < eT := by
    rw [heT]
    exact div_pos (mul_pos (mul_pos (by norm_num) hCseedpos) hKypos) (mul_pos hMpos hMpos)
  have hCseedKy : Cseed * Ky / (M * M) = eT / 8 := by
    rw [heT]; field_simp
  have heT1 : eT ≤ δ / (16 * Θ) := by
    have h1 : Ky * (8 * Cseed) * (32 * CeA) ≤ δ * ccA := by
      calc Ky * (8 * Cseed) * (32 * CeA)
          ≤ (δ * ccA / (256 * CeA * Cseed)) * (8 * Cseed) * (32 * CeA) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKy1 ?_) ?_
            · exact mul_nonneg (by norm_num) hCseedpos.le
            · exact mul_nonneg (by norm_num) hCeA.le
        _ = δ * ccA := by field_simp; ring
    have hkey : δ / (16 * Θ) = δ * ccA / (32 * CeA * M * M) := by
      rw [hΘ]; field_simp; ring
    rw [hkey, heT, div_le_iff₀ (mul_pos hMpos hMpos)]
    have h2 : δ * ccA / (32 * CeA * M * M) * (M * M) = δ * ccA / (32 * CeA) := by
      field_simp
    rw [h2, le_div_iff₀ (by linarith [hCeA] : (0:ℝ) < 32 * CeA)]
    nlinarith [h1]
  have heT2 : eT ≤ ccA / (2 * Kk * M * M) := by
    have h1 : Ky * (8 * Cseed) * (2 * Kk) ≤ ccA := by
      calc Ky * (8 * Cseed) * (2 * Kk) ≤ (ccA / (16 * Kk * Cseed)) * (8 * Cseed) * (2 * Kk) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKy2 ?_) ?_
            · exact mul_nonneg (by norm_num) hCseedpos.le
            · exact mul_nonneg (by norm_num) hKk.le
        _ = ccA := by field_simp; ring
    rw [heT, div_le_iff₀ (mul_pos hMpos hMpos)]
    have h2 : ccA / (2 * Kk * M * M) * (M * M) = ccA / (2 * Kk) := by field_simp
    rw [h2, le_div_iff₀ (by linarith [hKk] : (0:ℝ) < 2 * Kk)]
    nlinarith [h1]
  have heT3 : eT ≤ Robt / (8 * Θ) := by
    have h1 : Ky * (8 * Cseed) * (16 * CeA) ≤ Robt * ccA := by
      calc Ky * (8 * Cseed) * (16 * CeA)
          ≤ (Robt * ccA / (128 * CeA * Cseed)) * (8 * Cseed) * (16 * CeA) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKy3 ?_) ?_
            · exact mul_nonneg (by norm_num) hCseedpos.le
            · exact mul_nonneg (by norm_num) hCeA.le
        _ = Robt * ccA := by field_simp; ring
    have hkey : Robt / (8 * Θ) = Robt * ccA / (16 * CeA * M * M) := by
      rw [hΘ]; field_simp; ring
    rw [hkey, heT, div_le_iff₀ (mul_pos hMpos hMpos)]
    have h2 : Robt * ccA / (16 * CeA * M * M) * (M * M) = Robt * ccA / (16 * CeA) := by
      field_simp
    rw [h2, le_div_iff₀ (by linarith [hCeA] : (0:ℝ) < 16 * CeA)]
    nlinarith [h1]
  set E : ℝ := Ky / (16 * Ugrow) with hE
  have hEpos : 0 < E := by rw [hE]; exact div_pos hKypos (mul_pos (by norm_num) hUgrowpos)
  have hdevKy : (80 * Cdev / M + 4 * E) * Ugrow ≤ Ky := by
    have h1 : 80 * Cdev / M * Ugrow ≤ 3 * Ky / 4 := by
      rw [show 80 * Cdev / M * Ugrow = 80 * Cdev * (CX * (1 + T + Real.log M)) / M from by
        rw [hUgrow]; ring]
      rw [div_le_iff₀ hMpos]
      linarith [hlog1]
    have h2 : 4 * E * Ugrow = Ky / 4 := by
      rw [hE]; field_simp; ring
    have hsum : (80 * Cdev / M + 4 * E) * Ugrow = 80 * Cdev / M * Ugrow + 4 * E * Ugrow := by ring
    rw [hsum, h2]
    linarith
  have hdevM : (80 * Cdev / M + 4 * E) * Ugrow ≤ M / 64 := by
    have h1 : 80 * Cdev / M * Ugrow ≤ 3 * Ky / 4 := by
      rw [show 80 * Cdev / M * Ugrow = 80 * Cdev * (CX * (1 + T + Real.log M)) / M from by
        rw [hUgrow]; ring]
      rw [div_le_iff₀ hMpos]
      linarith [hlog1]
    have h2 : 4 * E * Ugrow = Ky / 4 := by
      rw [hE]; field_simp; ring
    have hsum : (80 * Cdev / M + 4 * E) * Ugrow = 80 * Cdev / M * Ugrow + 4 * E * Ugrow := by ring
    rw [hsum, h2]
    linarith [hMKy, hKypos]
  -- ################ the defect bound `E` on the anchor ball
  have hDanch : ∀ z ∈ Danchor8 M, ‖z - (((-M : ℝ)) : ℂ)‖ ≤ M / 8 := by
    intro z hz
    simpa [Danchor8, Metric.mem_closedBall, dist_eq_norm] using hz
  have hMKd : ∀ z ∈ Danchor8 M, 7 * M / 8 ≤ ‖z‖ := by
    intro z hz
    have h1 := hDanch z hz
    have h2 : ‖((( -M : ℝ)) : ℂ)‖ = M := by simp [hMpos.le]
    have h3 : ‖((( -M : ℝ)) : ℂ)‖ ≤ ‖z - (((-M : ℝ)) : ℂ)‖ + ‖z‖ := by
      have h := norm_add_le z (-(z - (((-M : ℝ)) : ℂ)))
      have he : z + -(z - (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) := by ring
      rw [he, norm_neg] at h
      linarith [h]
    rw [h2] at h3
    linarith
  have hKdsub : Danchor8 M ⊆ MandelDim.Qreg none (some (-(((M / 4 : ℝ) : ℂ)))) := by
    intro z hz
    have hzre : z.re ≤ -M + M / 8 := by
      have h2 : z.re - (-M) ≤ |((z - (((-M : ℝ)) : ℂ))).re| := by
        rw [Complex.sub_re, Complex.ofReal_re]
        exact le_abs_self _
      have h3 : |((z - (((-M : ℝ)) : ℂ))).re| ≤ ‖z - (((-M : ℝ)) : ℂ)‖ := Complex.abs_re_le_norm _
      linarith [h2, h3, hDanch z hz]
    refine ⟨?_, ?_⟩
    · intro b hb; simp at hb
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      have h3 : (z + ((M / 4 : ℝ) : ℂ)).re < 0 := by
        rw [Complex.add_re, Complex.ofReal_re]; linarith
      have h4 : 0 ≤ |(z + ((M / 4 : ℝ) : ℂ)).im| := abs_nonneg _
      have hsame : z - -(((M / 4 : ℝ) : ℂ)) = z + ((M / 4 : ℝ) : ℂ) := by ring
      rw [hsame]
      rcases eq_or_lt_of_le h4 with h5 | h5
      · rw [← h5]; exact h3
      · linarith [h3, h5]
  have hfar8 : ∀ z ∈ Danchor8 M, 1 < ‖z‖ := by
    intro z hz
    have h1 := hMKd z hz
    linarith [hM2]
  have hdepth8 : ∀ z ∈ Danchor8 M, ‖MandelDim.tau0 z‖ ≤ ρg / 8 := by
    intro z hz
    have h1 : 7 * M / 8 ≤ ‖z‖ := hMKd z hz
    have h5 : ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by simp [MandelDim.tau0]
    rw [h5]
    have h6 : 1 / ‖z‖ ≤ 1 / (7 * M / 8) := one_div_le_one_div_of_le (by linarith) h1
    have h7 : 1 / (7 * M / 8) ≤ ρg / 8 := by
      have h8 : 7 * M / 8 * (ρg / 8) = 7 * M * ρg / 64 := by ring
      have h9 : 64 / (7 * ρg) * (7 * ρg / 64) = 1 := by field_simp
      have h10 : (1:ℝ) ≤ 7 * M / 8 * (ρg / 8) := by
        have := mul_le_mul_of_nonneg_right hMρg (le_of_lt (by linarith : (0:ℝ) < 7 * ρg / 64))
        rw [h9] at this
        linarith [this]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 7 * M / 8)]
      linarith
    linarith
  have hKdc : IsCompact (Danchor8 M) := isCompact_closedBall _ _
  obtain ⟨Ldef, hLdefc, hLdefD, δdef, ηdef, hδdefpos, hηdefpos, hdefectLe⟩ :=
    Work.Pert.Ksub2.defect_le_fix hd (ξ := M / 4) (by linarith) hKdc hKdsub hfar8 hρgpos hρg8
      hDgnn hfe hFd hFl hFb hroomg hdepth8 E hEpos
  -- ################ the seed-error target numbers
  set ηu_def : ℝ := min (Ky / M) (min ηdef (1 / 4)) with hηu
  have hηupos : 0 < ηu_def := by
    rw [hηu]
    exact lt_min (div_pos hKypos hMpos) (lt_min hηdefpos (by norm_num))
  set ηα_def : ℝ := min (Ky / (M * M))
      (min ηdef (min (1 / (2 * (2 * M + Ξ + 2))) (min (1 / (8 * Real.pi * M))
        (min (1 / (4 * Real.pi)) (1 / (16 * Real.pi * Ξ)))))) with hηα
  have hηαpos : 0 < ηα_def := by
    rw [hηα]
    refine lt_min (div_pos hKypos (mul_pos hMpos hMpos)) (lt_min hηdefpos
      (lt_min (div_pos one_pos (by linarith : (0:ℝ) < 2 * (2 * M + Ξ + 2)))
        (lt_min (div_pos one_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hMpos))
          (lt_min (div_pos one_pos (mul_pos (by norm_num) Real.pi_pos))
            (div_pos one_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hΞ))))))
  have hηα_le : ηα_def ≤ 1 / (2 * (2 * M + Ξ + 2)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηα_4π : ηα_def ≤ 1 / (4 * Real.pi) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hηα_πΞ : ηα_def ≤ 1 / (16 * Real.pi * Ξ) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hηα_πM : ηα_def ≤ 1 / (8 * Real.pi * M) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hηα_def_le : ηα_def ≤ ηdef :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hηu_def_le : ηu_def ≤ ηdef :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hηu_14 : ηu_def ≤ 1 / 4 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hηuT : ηu_def ≤ Ky / M := min_le_left _ _
  have hηαT : ηα_def ≤ Ky / (M * M) := min_le_left _ _
  -- ################ the orbit region and its neighbourhood
  set Z : Set ℂ := ⋃ m ∈ {m : ℕ | 1 ≤ m ∧ m ≤ N},
      d.φ '' ((fun z : ℂ => z - (m : ℂ)) '' K) with hZ
  have hZmem : ∀ w ∈ K, ∀ m : ℕ, 1 ≤ m → m ≤ N → d.φ (w - (m : ℂ)) ∈ Z := by
    intro w hw m hm1 hmN
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨⟨hm1, hmN⟩, ?_⟩⟩
    exact ⟨w - (m : ℂ), ⟨w, hw, rfl⟩, rfl⟩
  have hZc : IsCompact Z := by
    rw [hZ]
    refine Set.Finite.isCompact_biUnion (Set.finite_Icc 1 N) ?_
    intro m hm
    obtain ⟨hm1, hmN⟩ := hm
    have hKm : IsCompact ((fun z : ℂ => z - (m : ℂ)) '' K) :=
      hKc.image (continuous_id.sub continuous_const)
    refine hKm.image_of_continuousOn ?_
    refine d.φ_holo.continuousOn.mono ?_
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact Work.Pert.sub_nat_mem_Dφ d (hK hw) m
  set V : Set ℂ := Metric.cthickening (Robt / 2) Z with hV
  have hVc : IsCompact V := by rw [hV]; exact hZc.cthickening
  have hVD₀ : V ⊆ D₀ := by
    rw [hV]
    refine subset_trans (Metric.cthickening_mono (by linarith : Robt / 2 ≤ Robt) Z) ?_
    rw [hZc.cthickening_eq_biUnion_closedBall hRobtpos.le]
    intro x hx
    obtain ⟨z, hz1⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hzZ, hxz⟩ := Set.mem_iUnion.mp hz1
    rw [Metric.mem_closedBall, dist_comm] at hxz
    rw [hZ] at hzZ
    obtain ⟨m, hm1⟩ := Set.mem_iUnion.mp hzZ
    obtain ⟨hm, hz2⟩ := Set.mem_iUnion.mp hm1
    obtain ⟨y, hy, hyz⟩ := hz2
    obtain ⟨w, hw, hwy⟩ := hy
    subst hwy
    rw [← hyz] at hxz
    rw [dist_comm] at hxz
    exact hRobtD₀ w hw m hm.1 (Metric.mem_closedBall.mpr hxz)
  obtain ⟨Lf₀, hLf₀nn, hLf₀⟩ := Work.Pert.Ksub2.exists_lipschitzOn_of_compact
    (f := f₀) (D := D₀) (V := V) (hd.1) hVc hVD₀ hd.2.2.1
  set Lf : ℝ := max Lf₀ 1 with hLf
  have hLf1 : 1 ≤ Lf := le_max_right _ _
  have hLfL : ∀ z ∈ V, ∀ z' ∈ V, ‖f₀ z - f₀ z'‖ ≤ Lf * ‖z - z'‖ := by
    intro z hz z' hz'
    exact le_trans (hLf₀ z hz z' hz') (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- ################ the neighbourhood and the `δ₀` thresholds
  have hNLfpos : (0:ℝ) < 4 * (N : ℝ) * Lf ^ N := by
    refine mul_pos (mul_pos (by norm_num) ?_) (pow_pos (by linarith : (0:ℝ) < Lf) N)
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro h0
      have := hNge
      rw [h0] at this
      simp at this
      linarith [hMpos])
  have hNLfN : (0:ℝ) < (N : ℝ) * Lf ^ N := by
    refine mul_pos ?_ (pow_pos (by linarith : (0:ℝ) < Lf) N)
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro h0
      have := hNge
      rw [h0] at this
      simp at this
      linarith [hMpos])
  have hNLfpos8 : (0:ℝ) < 8 * (N : ℝ) * Lf ^ N := by
    have := mul_pos (by norm_num : (0:ℝ) < 2) hNLfpos
    linarith [this]
  set δs : Finset ℝ := {δdef, 1, ρs / 2, ηu_def / (4 * Csm * max (1 / ρs ^ 2) (16 * Ξ / ρs)),
      ηα_def * ρs / (2 * Csm), δ / (4 * (N : ℝ) * Lf ^ N),
      (Robt / 2) / (8 * (N : ℝ) * Lf ^ N)} with hδs
  have hδsne : δs.Nonempty := ⟨δdef, by simp [hδs]⟩
  set δ₀ : ℝ := δs.min' hδsne with hδ₀
  have hδ₀le : ∀ a ∈ δs, δ₀ ≤ a := fun a ha => Finset.min'_le _ _ ha
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_min'_iff]
    intro y hy
    simp only [hδs, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hδdefpos
    · norm_num
    · linarith
    · exact div_pos hηupos (mul_pos (mul_pos (by norm_num) hCsmp)
        (lt_max_of_lt_left (div_pos one_pos (pow_pos hρspos 2))))
    · exact div_pos (mul_pos hηαpos hρspos) (mul_pos (by norm_num) hCsmp)
    · exact div_pos hδ hNLfpos
    · exact div_pos (by linarith) hNLfpos8
  have hδdefm : δdef ∈ δs := by simp [hδs]
  have hδ₀δdef : δ₀ ≤ δdef := hδ₀le δdef hδdefm
  have hδ₀1 : δ₀ ≤ 1 := hδ₀le 1 (by simp [hδs])
  have hδ₀2ρ : 2 * δ₀ ≤ ρs := by
    have h := hδ₀le (ρs / 2) (by simp [hδs])
    linarith
  have hδ₀ηu : δ₀ ≤ ηu_def / (4 * Csm * max (1 / ρs ^ 2) (16 * Ξ / ρs)) :=
    hδ₀le _ (by simp [hδs])
  have hδ₀ηα : δ₀ ≤ ηα_def * ρs / (2 * Csm) := hδ₀le _ (by simp [hδs])
  have hδ₀δ : δ₀ ≤ δ / (4 * (N : ℝ) * Lf ^ N) := hδ₀le _ (by simp [hδs])
  have hδ₀rob : δ₀ ≤ (Robt / 2) / (8 * (N : ℝ) * Lf ^ N) := hδ₀le _ (by simp [hδs])
  set L : Set ℂ := Ldef ∪ V ∪ Metric.closedBall (0 : ℂ) ρs with hL
  have hLc : IsCompact L := by
    rw [hL]
    exact (hLdefc.union hVc).union (isCompact_closedBall _ _)
  have hLD : L ⊆ D₀ := by
    rw [hL]
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hLdefD hx
    · exact hVD₀ hx
    · exact hroom_s hx
  have hΘeT_rob : Θ * eT ≤ Robt / 8 := by
    have h := mul_le_mul_of_nonneg_left heT3 hΘpos.le
    have h2 : Θ * (Robt / (8 * Θ)) = Robt / 8 := by field_simp
    linarith [h, h2]
  have hΘeT_δ : Θ * eT ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left heT1 hΘpos.le
    have h2 : Θ * (δ / (16 * Θ)) = δ / 16 := by field_simp
    linarith [h, h2]
  have hVball : ∀ w ∈ K, ∀ m : ℕ, 1 ≤ m → m ≤ N →
      Metric.closedBall (d.φ (w - (m : ℂ))) (Robt / 2) ⊆ V := by
    intro w hw m hm1 hmN z hz
    rw [hV]
    rw [Metric.mem_closedBall] at hz
    exact Work.Pert.Ksub2.mem_cthickening_of_dist_le (hZmem w hw m hm1 hmN) hz
  refine ⟨L, hLc, hLD, δ₀, hδ₀pos, ?_⟩
  intro f Df rr u σ α hnear h0 hInF1 hαeq hrr hud hbnd hform hnorm htQ hQAdm hNT
  have hF1α : MandelDim.InF1 α := hαeq ▸ hInF1
  have hα : α ≠ 0 := by
    intro hz; rw [hz] at hF1α; simp [MandelDim.InF1] at hF1α
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hLclρ : Metric.closedBall (0 : ℂ) ρs ⊆ L := by
    rw [hL]; intro x hx; exact Or.inr hx
  have hLdefL : Ldef ⊆ L := by rw [hL]; intro x hx; exact Or.inl (Or.inl hx)
  have hVL : V ⊆ L := by rw [hL]; intro x hx; exact Or.inl (Or.inr hx)
  have hnearS : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρs) δ₀ :=
    nearOn_mono hnear hLclρ le_rfl
  obtain ⟨hU1, hσ1, hA1⟩ := hsmallOf hρspos hρsr0 hδ₀pos hδ₀2ρ hrr hnearS h0 hud hbnd hform
  have hmaxpos : 0 < max (1 / ρs ^ 2) (16 * Ξ / ρs) :=
    lt_max_of_lt_left (div_pos one_pos (pow_pos hρspos 2))
  have hαη : ‖α‖ ≤ ηα_def := by
    rw [hαeq]
    refine le_trans hA1 ?_
    have h1 : Csm * δ₀ ≤ ηα_def * ρs / 2 := by
      calc Csm * δ₀ ≤ Csm * (ηα_def * ρs / (2 * Csm)) :=
            mul_le_mul_of_nonneg_left hδ₀ηα hCsmp.le
        _ = ηα_def * ρs / 2 := by field_simp
    rw [div_le_iff₀ hρspos]
    nlinarith [h1, hρspos, hCsmp]
  have hb0 : 1 / 2 ≤ ‖u 0‖ ∧ ‖u 0‖ ≤ 2 := hbnd 0 (Metric.mem_ball_self hrr)
  have hReα : 2 * M + Ξ + 2 < (1 / α).re := by
    have h1 : 1 / (2 * ‖α‖) < (1 / α).re := Work.Pert.inv_re_lower hF1α
    have h2 : 2 * M + Ξ + 2 ≤ 1 / (2 * ‖α‖) := by
      have h3 : ‖α‖ ≤ 1 / (2 * (2 * M + Ξ + 2)) := le_trans hαη hηα_le
      have h4 : (2 * M + Ξ + 2) * ‖α‖ ≤ 1 / 2 := by
        have h5 := mul_le_mul_of_nonneg_left h3
          (by linarith [hMpos, hΞ] : (0:ℝ) ≤ 2 * M + Ξ + 2)
        have h6 : (2 * M + Ξ + 2) * (1 / (2 * (2 * M + Ξ + 2))) = 1 / 2 := by
          field_simp
        linarith [h5, h6]
      rw [le_div_iff₀ (mul_pos (by norm_num) hαpos)]
      linarith [h4]
    linarith
  have hrr_ge : 1 / (16 * Ξ) < rr := by
    have h2pi : 2 * Real.pi * ‖α‖ ≤ 1 / 2 := by
      have h1 : ‖α‖ ≤ 1 / (4 * Real.pi) := le_trans hαη hηα_4π
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)
      have h3 : 2 * Real.pi * (1 / (4 * Real.pi)) = 1 / 2 := by field_simp; ring
      linarith [h2, h3]
    have h8pi : 8 * Real.pi * ‖α‖ * Ξ ≤ 1 / 2 := by
      have h1 : ‖α‖ ≤ 1 / (16 * Real.pi * Ξ) := le_trans hαη hηα_πΞ
      have h2 := mul_le_mul_of_nonneg_left h1
        (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos] : (0:ℝ) ≤ 8) Real.pi_pos.le) hΞ.le)
      have h3 : 8 * Real.pi * Ξ * (1 / (16 * Real.pi * Ξ)) = 1 / 2 := by field_simp; ring
      have h4 : 8 * Real.pi * ‖α‖ * Ξ = 8 * Real.pi * Ξ * ‖α‖ := by ring
      rw [h4]; linarith [h2, h3]
    obtain ⟨z, hzQ, hzge⟩ := tauC_ge_of_mem_Qm hΞ hα h2pi h8pi (by linarith [hReα]) hb0.1 hb0.2 hnorm
    have h2 : ‖Work.Pert.tauC σ α z‖ < rr := by
      have h3 := htQ z hzQ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h3
      exact h3
    linarith
  have hUη : ‖u 0 - 1‖ ≤ ηu_def :=
    le_of_small_bound hU1 hδ₀ηu hρspos hrr hCsmp hηupos hΞ hrr_ge
  -- ### the gate geometry
  have hballu : ∀ z ∈ Work.Pert.Dstrip M T, Metric.ball z (7 * M / 8) ⊆ Work.Pert.Qm Ξ α := by
    intro z hz
    refine Work.Pert.Ksub2.ball_sub_Qm ?_ ?_
    · have h1 : -M - 1 ≤ z.re := hz.1
      linarith
    · have h1 : z.re ≤ -M := hz.2.1
      have h2 : Ξ < 7 * M / 8 := by linarith [hMΞ8]
      linarith
  have hnegM : ((((-M : ℝ)) : ℂ)) ∈ Work.Pert.Dstrip M T := by
    refine ⟨?_, ?_, ?_⟩
    · change -M - 1 ≤ -M
      linarith
    · change -M ≤ -M
      linarith
    · change |(0:ℝ)| ≤ T
      simp only [abs_zero]; linarith [hTpos]
  have hballNegM : Metric.ball ((((-M : ℝ)) : ℂ)) (7 * M / 8) ⊆ Work.Pert.Qm Ξ α :=
    hballu _ hnegM
  have hQmball40 : Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (M / 40) ⊆ Work.Pert.Qm Ξ α := by
    refine subset_trans (ball_subset_ball_of_dist ?_) hballNegM
    rw [dist_eq_norm]
    linarith [hXcM]
  have hQmball : Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (2 * (M / 80)) ⊆ Work.Pert.Qm Ξ α :=
    subset_trans (Metric.ball_subset_ball (by linarith)) hQmball40
  have hKdQm : Danchor8 M ⊆ Work.Pert.Qm Ξ α := by
    refine subset_trans (Metric.closedBall_subset_ball (by linarith : M / 8 < M / 4)) ?_
    exact Work.Pert.Ksub2.ball_sub_Qm (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith [hMΞ8])
  have hDstripQm : ∀ z ∈ Work.Pert.Dstrip M T, z ∈ Work.Pert.Qm Ξ α :=
    Work.Pert.Dstrip_sub_Qm hΞ hMΞ (by linarith)
  -- ### the defect estimate on the anchor ball
  have hdefect : ∀ z ∈ Danchor8 M, ‖Work.Pert.liftF u σ α z - Work.Pert.F0f f₀ z‖ ≤ E := by
    refine hdefectLe f Df rr u σ α (nearOn_mono hnear hLdefL hδ₀δdef) h0 hα
      (le_trans hαη hηα_def_le) hrr hud hbnd hform ?_ (le_trans hUη hηu_def_le) hnorm
    intro z hz
    exact htQ z (hKdQm hz)
  -- ### the pinned Fatou coordinate
  obtain ⟨Φbase, hΦbase, -⟩ :=
    hF.1 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) hQAdm hNT.1
  set Φm : ℂ → ℂ := fun z => Φbase z + Work.Pert.Ksub2.pinC d M Φbase with hΦmdef
  have hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) :=
    Work.Pert.Ksub2.isFatouCoordOn_add_const hΦbase _
  have hpin : Φm (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) = ((((-M : ℝ)) : ℂ)) :=
    Work.Pert.Ksub2.pinC_pin d M Φbase
  -- ### the deviation on the anchor ball and on the strip
  have hrad : 2 * (M / 80) = M / 40 := by ring
  have hF0nt' : ∀ w ∈ Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (2 * (M / 80)),
      ‖Work.Pert.F0f f₀ w - (w + 1)‖ < 1 / 4 := by
    rw [hrad]; exact (hF0nt M hMM0F0).2
  have hF0diff : DifferentiableOn ℂ (Work.Pert.F0f f₀)
      (Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (2 * (M / 80))) := by
    rw [hrad]; exact (hF0nt M hMM0F0).1
  have hΦ₀an' : MandelDim.IsFatouCoordOn (Work.Pert.F0f f₀) Φ₀
      (Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (2 * (M / 80))) := by
    rw [hrad]; exact hΦ₀an
  have hdevA' : ∀ z ∈ Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (M / 80),
      ‖Φm z - Φ₀ z‖ ≤ (Cdev / (M / 80) + 4 * E)
        * ‖z - Work.Pert.Xc d ((((-M : ℝ)) : ℂ))‖ := by
    refine hdevA (F := Work.Pert.liftF u σ α) (F₀ := Work.Pert.F0f f₀) (Φ := Φm) (Φ₀ := Φ₀)
      (c := Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (R := M / 80) (E := E)
      (by linarith [hMCdev] : Cdev ≤ M / 80) hEpos.le ?_ hF0diff ?_ hΦ₀an' ?_ hF0nt' ?_ ?_
    · exact hNT.1.1.mono hQmball
    · exact ⟨hΦm.1.mono hQmball, hΦm.2.1.mono hQmball, fun z hz hFz =>
        hΦm.2.2 z (hQmball hz) (hQmball hFz)⟩
    · intro w hw
      exact lt_of_le_of_lt (hNT.1.2 w (hQmball hw)).1 (by norm_num)
    · intro w hw
      rw [hrad] at hw
      exact hdefect w (hballdef hw)
    · rw [hpin, hΦ₀pin]
  have hXcAnchor : ∀ z ∈ Work.Pert.Dstrip M T,
      Work.Pert.Xc d z ∈ Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (M / 80) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have h := (hXcb M hMX' T hTnonneg hTleM z hz).2
    rw [← hUgrow] at h
    linarith [h, hUgrowM]
  have hXcAnchor40 : ∀ z ∈ Work.Pert.Dstrip M T,
      Work.Pert.Xc d z ∈ Metric.ball (Work.Pert.Xc d ((((-M : ℝ)) : ℂ))) (M / 40) :=
    fun z hz => Metric.ball_subset_ball (by linarith) (hXcAnchor z hz)
  have hΦ₀id : ∀ z ∈ Work.Pert.Dstrip M T, Φ₀ (Work.Pert.Xc d z) = z := by
    refine Work.Pert.Ksub2.Phi0_inv_on_Dstrip d ?_ ?_ ?_ ?_ ?_
    · exact fun u hu => hRasLem M hMRas u hu
    · exact fun ζ hζ => (hΦ₀inv ζ hζ).1
    · exact hXcAnchor40
    · intro z hz
      rw [Metric.mem_ball, dist_eq_norm]
      exact hstrip_lt z hz
    · intro z hz
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖Φ₀ (Work.Pert.Xc d z) - Work.Pert.Xc d z‖ ≤ M / 40 :=
        (hΦ₀inv _ (hXcAnchor40 z hz)).2
      have h2 : ‖Work.Pert.Xc d z - ((((-M : ℝ)) : ℂ))‖ ≤ M / 40 + M / 40 := by
        calc ‖Work.Pert.Xc d z - ((((-M : ℝ)) : ℂ))‖
            ≤ ‖Work.Pert.Xc d z - Work.Pert.Xc d ((((-M : ℝ)) : ℂ))‖
              + ‖Work.Pert.Xc d ((((-M : ℝ)) : ℂ)) - ((((-M : ℝ)) : ℂ))‖ := by
              have h := norm_add_le (Work.Pert.Xc d z - Work.Pert.Xc d ((((-M : ℝ)) : ℂ)))
                (Work.Pert.Xc d ((((-M : ℝ)) : ℂ)) - ((((-M : ℝ)) : ℂ)))
              rw [sub_add_sub_cancel] at h
              exact h
          _ ≤ M / 40 + M / 40 := by
              have h3 : ‖Work.Pert.Xc d z - Work.Pert.Xc d ((((-M : ℝ)) : ℂ))‖ ≤ M / 40 := by
                have h4 := (hXcb M hMX' T hTnonneg hTleM z hz).2
                rw [← hUgrow] at h4
                linarith [h4, hUgrowM]
              linarith [h3, hXcM]
      have h3 : ‖Φ₀ (Work.Pert.Xc d z) - ((((-M : ℝ)) : ℂ))‖
          ≤ ‖Φ₀ (Work.Pert.Xc d z) - Work.Pert.Xc d z‖
            + ‖Work.Pert.Xc d z - ((((-M : ℝ)) : ℂ))‖ := by
        have h := norm_add_le (Φ₀ (Work.Pert.Xc d z) - Work.Pert.Xc d z)
          (Work.Pert.Xc d z - ((((-M : ℝ)) : ℂ)))
        rw [sub_add_sub_cancel] at h
        exact h
      linarith [h1, h2, h3, hMpos]
  have hdevstrip : ∀ z ∈ Work.Pert.Dstrip M T,
      ‖Φm (Work.Pert.Xc d z) - z‖ ≤ (Cdev / (M / 80) + 4 * E) * Ugrow := by
    intro z hz
    have h1 := hdevA' _ (hXcAnchor z hz)
    rw [hΦ₀id z hz] at h1
    have h2 := (hXcb M hMX' T hTnonneg hTleM z hz).2
    rw [← hUgrow] at h2
    refine le_trans h1 (mul_le_mul_of_nonneg_left h2 ?_)
    exact add_nonneg (div_nonneg hCdevpos.le (by linarith)) (by linarith [hEpos])
  have hper : ∀ w ∈ K, Work.Pert.GoodP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w ∧
      ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w - d.φ w‖ < δ := by
    intro w hw
    have hlev : ∃ n : ℕ, w - (n : ℂ) ∈ Work.Pert.Dstrip M T := by
      refine Work.Pert.exists_nat_sub_mem_Dstrip ?_ ?_
      · have h1 : |w.re| ≤ T := le_trans (Complex.abs_re_le_norm w) (hTK w hw)
        linarith [(abs_le.mp h1).1, hTleM]
      · exact le_trans (Complex.abs_im_le_norm w) (hTK w hw)
    set nn : ℕ := Work.Pert.Ksub2.nw M T w with hnn
    set uu : ℂ := Work.Pert.Ksub2.uw M T w with huu
    have huuD : uu ∈ Work.Pert.Dstrip M T := Work.Pert.Ksub2.uw_mem_Dstrip hlev
    have huuD' : uu ∈ Work.Pert.Dstrip M (T + 1) := ⟨huuD.1, huuD.2.1, by linarith [huuD.2.2]⟩
    have huuw : uu + (nn : ℂ) = w := by
      rw [huu, hnn, Work.Pert.Ksub2.uw]; ring
    have hnN : nn ≤ N := by
      have h1 : (nn : ℝ) ≤ w.re + M + 1 := by
        rw [hnn]; simpa using Work.Pert.Ksub2.nw_le hlev
      have h2 : w.re ≤ T := (abs_le.mp (le_trans (Complex.abs_re_le_norm w) (hTK w hw))).2
      have h3 : (nn : ℝ) ≤ (N : ℝ) := by linarith [h1, h2, hNge]
      exact_mod_cast h3
    have hwalk : ∀ i : ℕ, i ≤ nn → uu + (i : ℂ) ∈ d.Dφ := by
      intro i hi
      have h1 : uu + (i : ℂ) = w - ((nn - i : ℕ) : ℂ) := by
        have h2 : uu + (((nn - i : ℕ) : ℂ) + (i : ℂ)) = w := by
          rw [← Nat.cast_add, Nat.sub_add_cancel hi]; exact huuw
        rw [← h2]; ring
      rw [h1]
      exact Work.Pert.sub_nat_mem_Dφ d (hK hw) (nn - i)
    have hkeyw : ∀ j : ℕ, j < nn → uu + (j : ℂ) = w - ((nn - j : ℕ) : ℂ) := by
      intro j hj
      have h2 : uu + (((nn - j : ℕ) : ℂ) + (j : ℂ)) = w := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (le_of_lt hj)]; exact huuw
      rw [← h2]; ring
    have hderPhi : ∀ z ∈ Metric.ball (Work.Pert.Xc d uu) (M / 2), ‖deriv Φm z - 1‖ ≤ 1 / 2 := by
      intro z hz
      set v : ℂ → ℂ := fun w => Work.Pert.liftF u σ α w - w with hv
      have hzM : ‖z - Work.Pert.Xc d uu‖ < M / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      have hXcuu : ‖Work.Pert.Xc d uu - uu‖ ≤ M / 40 := by
        have h3 := (hXcb M hMX' T hTnonneg hTleM uu huuD).1
        have h4 : CX * (1 + Real.log M) ≤ Ugrow := by
          rw [hUgrow]
          refine mul_le_mul_of_nonneg_left ?_ hCXpos.le
          linarith
        linarith [h3, h4, hUgrowM]
      have hzQ : Metric.ball z (M / 4) ⊆ Work.Pert.Qm Ξ α := by
        refine subset_trans (ball_subset_ball_of_dist ?_) (hballu uu huuD)
        rw [dist_eq_norm]
        have h4 : ‖z - uu‖ ≤ ‖z - Work.Pert.Xc d uu‖ + ‖Work.Pert.Xc d uu - uu‖ := by
          have h := norm_add_le (z - Work.Pert.Xc d uu) (Work.Pert.Xc d uu - uu)
          rw [sub_add_sub_cancel] at h; exact h
        nlinarith [h4, hzM, hXcuu, hMpos]
      have hvdiff : DifferentiableOn ℂ v (Metric.ball z (M / 4)) := by
        rw [hv]
        exact (hNT.1.1.mono hzQ).sub differentiableOn_id
      have hvnear : ∀ w ∈ Metric.ball z (M / 4), ‖v w - 1‖ < 1 / 4 := by
        intro w hw
        have h1 : ‖v w - 1‖ ≤ 1 / 32 := by
          have he : v w - 1 = Work.Pert.liftF u σ α w - (w + 1) := by simp only [hv]; ring
          rw [he]; exact (hNT.1.2 w (hzQ hw)).1
        linarith
      have habel : ∀ w ∈ Metric.ball z (M / 4), w + v w ∈ Metric.ball z (M / 4) →
          Φm (w + v w) = Φm w + 1 := by
        intro w hw hwv
        have he : w + v w = Work.Pert.liftF u σ α w := by simp only [hv]; ring
        have h := hΦm.2.2 w (hzQ hw) (by rw [← he]; exact hzQ hwv)
        rwa [← he] at h
      have hRde_le : Rde ≤ R₁ := by rw [hR1]; exact le_max_left _ _
      have h64C2_le : 64 * C2 ≤ R₁ := by rw [hR1]; exact le_max_right _ _
      obtain ⟨-, hb2⟩ := hDEest Φm v z (M / 4)
        (by linarith only [hMR1, hRde_le])
        (hΦm.1.mono hzQ) (hΦm.2.1.mono hzQ) hvdiff hvnear habel
      have hC2R : C2 / (M / 4) ≤ 1 / 64 := by
        rw [div_le_iff₀ (by linarith only [hMpos] : (0:ℝ) < M / 4)]
        nlinarith only [hMR1, h64C2_le]
      have hvinv : ‖1 / v z - 1‖ ≤ 1 / 31 := by
        have hvz : ‖v z - 1‖ ≤ 1 / 32 := by
          have he : v z - 1 = Work.Pert.liftF u σ α z - (z + 1) := by simp only [hv]; ring
          rw [he]; exact (hNT.1.2 z (hzQ (Metric.mem_ball_self (by linarith)))).1
        have h1 : ‖1 - v z‖ ≤ 1 / 32 := by rw [norm_sub_rev]; exact hvz
        have h2 : (31:ℝ) / 32 ≤ ‖v z‖ := by
          have h3 : (1:ℝ) ≤ ‖v z‖ + ‖1 - v z‖ := by
            have he : (1:ℂ) = v z + (1 - v z) := by ring
            calc (1:ℝ) = ‖(1:ℂ)‖ := by simp
              _ = ‖v z + (1 - v z)‖ := congrArg (fun x : ℂ => ‖x‖) he
              _ ≤ ‖v z‖ + ‖1 - v z‖ := norm_add_le _ _
          linarith [h3, h1]
        have hne : v z ≠ 0 := by
          intro h0; rw [h0, norm_zero] at h2; norm_num at h2
        rw [div_sub_one hne, norm_div]
        have h4 : ‖1 - v z‖ / ‖v z‖ ≤ (1/32) / (31/32) :=
          div_le_div₀ (by norm_num) h1 (by norm_num) h2
        nlinarith [h4]
      have htri : ‖deriv Φm z - 1‖ ≤ ‖deriv Φm z - 1 / v z‖ + ‖1 / v z - 1‖ := by
        have he : deriv Φm z - 1 = (deriv Φm z - 1 / v z) + (1 / v z - 1) := by ring
        rw [he]; exact norm_add_le _ _
      nlinarith [hb2, hC2R, hvinv, htri]
    have hCdevk : Cdev / (M / 80) = 80 * Cdev / M := by ring
    have hdevuu : ‖Φm (Work.Pert.Xc d uu) - uu‖ ≤ Ky := by
      have hds : ‖Φm (Work.Pert.Xc d uu) - uu‖ ≤ (80 * Cdev / M + 4 * E) * Ugrow := by
        rw [hCdevk] at hdevstrip
        exact hdevstrip uu huuD
      exact le_trans hds hdevKy
    have hKyM64 : Ky ≤ M / 64 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 64)]
      nlinarith only [hMKy]
    have hcover : Metric.ball (Φm (Work.Pert.Xc d uu)) (M / 16) ⊆
        Φm '' Metric.closedBall (Work.Pert.Xc d uu) (M / 4) := by
      have hr4 : (0 : ℝ) < M / 4 := by linarith [hMpos]
      have hsub := Work.Pert.image_cover_centered (Φ := Φm) (z₀ := Work.Pert.Xc d uu)
        (r := M / 4) hr4
        (fun z hz => Work.Pert.Ksub2.differentiableAt_of_norm_deriv_sub_one_le
          (hderPhi z (Metric.closedBall_subset_ball (by linarith [hMpos]) hz)))
        (fun z hz => hderPhi z (Metric.closedBall_subset_ball (by linarith [hMpos]) hz))
      have hr : (M / 4) / 4 = M / 16 := by ring
      rwa [hr] at hsub
    have huu_cover : uu ∈ Metric.ball (Φm (Work.Pert.Xc d uu)) (M / 16) := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev,
        lt_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      have h1 : ‖Φm (Work.Pert.Xc d uu) - uu‖ * 16 ≤ Ky * 16 :=
        mul_le_mul_of_nonneg_right hdevuu (by norm_num)
      have h2 : Ky * 16 ≤ M / 4 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
        nlinarith only [hMKy]
      linarith only [h1, h2, hMpos]
    obtain ⟨ζ, hζball, hζeq⟩ := hcover huu_cover
    have hζQm : ζ ∈ Work.Pert.Qm Ξ α := by
      apply hballu uu huuD
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖ζ - Work.Pert.Xc d uu‖ ≤ M / 4 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hζball
      have h2 : ‖Work.Pert.Xc d uu - uu‖ ≤ M / 40 := by
        have h3 := (hXcb M hMX' T hTnonneg hTleM uu huuD).1
        have h4 : CX * (1 + Real.log M) ≤ Ugrow := by
          rw [hUgrow]
          refine mul_le_mul_of_nonneg_left ?_ hCXpos.le
          linarith
        linarith [h3, h4, hUgrowM]
      have h5 : ‖ζ - uu‖ ≤ ‖ζ - Work.Pert.Xc d uu‖ + ‖Work.Pert.Xc d uu - uu‖ := by
        have h := norm_add_le (ζ - Work.Pert.Xc d uu) (Work.Pert.Xc d uu - uu)
        rw [sub_add_sub_cancel] at h; exact h
      linarith [h1, h2, h5, hMpos]
    set ς : ℂ := Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) uu with hς
    have hu_mem : ∃ z ∈ Work.Pert.Qm Ξ α, Φm z = uu := ⟨ζ, hζQm, hζeq⟩
    have hςQm : ς ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hu_mem
    have hςspec : Φm ς = uu := Work.Pert.invOn_spec hu_mem
    have hςeq : ς = ζ := Work.Pert.invOn_eq hΦm.2.1 hu_mem hζQm hζeq
    have hςball : ς ∈ Metric.closedBall (Work.Pert.Xc d uu) (M / 4) := by
      rw [hςeq]; exact hζball
    have hςclose : ‖ς - Work.Pert.Xc d uu‖ ≤ 2 * ‖Φm (Work.Pert.Xc d uu) - uu‖ := by
      have h1 : ‖ς - Work.Pert.Xc d uu‖ ≤ 2 * ‖Φm ς - Φm (Work.Pert.Xc d uu)‖ := by
        have hsubQ : Metric.ball (Work.Pert.Xc d uu) (3 * M / 8) ⊆ Work.Pert.Qm Ξ α :=
          subset_trans (ball_subset_ball_of_dist (by
            rw [dist_eq_norm]
            have h3 := (hXcb M hMX' T hTnonneg hTleM uu huuD).1
            have h4 : CX * (1 + Real.log M) ≤ Ugrow := by
              rw [hUgrow]
              refine mul_le_mul_of_nonneg_left ?_ hCXpos.le
              linarith
            linarith [h3, h4, hUgrowM, hMpos])) (hballu uu huuD)
        exact Work.Pert.inv_close_of_deriv_close
          (Q := Metric.ball (Work.Pert.Xc d uu) (3 * M / 8))
          Metric.isOpen_ball (convex_ball _ _) (hΦm.1.mono hsubQ)
          (fun z hz => hderPhi z (Metric.ball_subset_ball (by linarith [hMpos]) hz))
          ς (by rw [hςeq]; exact Metric.closedBall_subset_ball (by linarith [hMpos]) hζball)
          (Work.Pert.Xc d uu) (Metric.mem_ball_self (by linarith [hMpos] : (0:ℝ) < 3 * M / 8))
      rw [hςspec] at h1
      rw [norm_sub_rev uu (Φm (Work.Pert.Xc d uu))] at h1
      exact h1
    have hXcuu40 : ‖Work.Pert.Xc d uu - uu‖ ≤ M / 40 := by
      have h3 := (hXcb M hMX' T hTnonneg hTleM uu huuD).1
      have h4 : CX * (1 + Real.log M) ≤ Ugrow := by
        rw [hUgrow]
        refine mul_le_mul_of_nonneg_left ?_ hCXpos.le
        linarith
      linarith [h3, h4, hUgrowM]
    have huunorm : M ≤ ‖uu‖ := by
      have h3 : ‖uu‖ ≥ -uu.re := by
        have := Complex.re_le_norm uu
        have h4 : -uu.re ≤ ‖uu‖ := by
          have h5 : ‖uu‖ = ‖-uu‖ := by simp
          calc -uu.re ≤ |uu.re| := neg_le_abs _
            _ ≤ ‖uu‖ := Complex.abs_re_le_norm uu
        exact h4
      linarith only [huuD.2.1, h3]
    have hςlow : M / 2 ≤ ‖ς‖ := by
      have h1 : ‖ς - Work.Pert.Xc d uu‖ ≤ M / 4 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hςball
      have h5 : ‖Work.Pert.Xc d uu‖ ≥ M - M / 40 := by
        have h := norm_lower_of_norm_sub_le (a := Work.Pert.Xc d uu) (b := uu) hXcuu40
        linarith only [h, huunorm]
      have h6 : ‖ς‖ ≥ (M - M / 40) - M / 4 := by
        have h := norm_lower_of_norm_sub_le (a := ς) (b := Work.Pert.Xc d uu) h1
        linarith only [h, h5]
      linarith only [h6, hMpos]
    have hςhigh : ‖ς‖ ≤ 2 * M := by
      have h1 : ‖ς - Work.Pert.Xc d uu‖ ≤ M / 4 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hςball
      have h3 : ‖uu + M‖ ≤ M / 4 := hstrip_norm uu huuD
      have h4 : ‖uu‖ ≤ M + M / 4 := by
        have hnormM : ‖((M : ℝ) : ℂ)‖ = M := by
          rw [Complex.norm_real, Real.norm_of_nonneg hMpos.le]
        have h := norm_add_le (uu + (M : ℂ)) (-(M : ℂ))
        rw [add_neg_cancel_right, norm_neg] at h
        linarith only [h, h3, hnormM]
      have h5 : ‖Work.Pert.Xc d uu‖ ≤ M + M / 4 + M / 40 := by
        have h := norm_add_le uu (Work.Pert.Xc d uu - uu)
        rw [add_sub_cancel] at h
        linarith only [h, hXcuu40, h4]
      have h6 : ‖ς‖ ≤ ‖Work.Pert.Xc d uu‖ + ‖ς - Work.Pert.Xc d uu‖ := by
        simpa only [add_sub_cancel] using norm_add_le (Work.Pert.Xc d uu) (ς - Work.Pert.Xc d uu)
      linarith only [h6, h1, h5, hMpos]
    have h4πle : (1 : ℝ) / (4 * Real.pi) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith [Real.pi_pos] : (0:ℝ) < 4 * Real.pi)]
      linarith only [Real.pi_gt_three]
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0] at hNLfN
        simp at hNLfN
      · exact_mod_cast h0
    have hLfpos : (0 : ℝ) < Lf := by linarith only [hLf1]
    have hLfNpos : (0 : ℝ) < Lf ^ N := pow_pos hLfpos N
    have hLfNnz : Lf ^ N ≠ 0 := ne_of_gt hLfNpos
    have hηseed : ‖Work.Pert.tauC σ α ς - d.φ uu‖ ≤ 3 * Cseed * Ky / (M * M) := by
      have h1 : ‖Work.Pert.tauC σ α ς - MandelDim.tau0 (Work.Pert.Xc d uu)‖
          ≤ Cseed * (‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) + ‖u 0 - 1‖ / M + ‖α‖) := by
        refine hseedD (u := u) hMpos (by linarith [hM2]) (norm_nonneg _) hςlow ?_ hςclose ?_
          hnorm hα (le_trans hUη hηu_14) (le_trans (le_trans hαη hηα_4π) h4πle)
        · have h := norm_lower_of_norm_sub_le (a := Work.Pert.Xc d uu) (b := uu) hXcuu40
          linarith only [h, huunorm, hMpos]
        · have hα8M : ‖α‖ ≤ 1 / (8 * Real.pi * M) := le_trans hαη hηα_πM
          have hA : 2 * Real.pi * ‖α‖ ≤ 1 / (4 * M) := by
            have h := mul_le_mul_of_nonneg_left hα8M
              (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)
            have he : 2 * Real.pi * (1 / (8 * Real.pi * M)) = 1 / (4 * M) := by
              field_simp
              ring
            rw [he] at h
            exact h
          have hB : (0 : ℝ) ≤ 1 / (4 * M) :=
            div_nonneg zero_le_one (by linarith only [hMpos] : (0:ℝ) ≤ 4 * M)
          calc 2 * Real.pi * ‖α‖ * ‖ς‖ ≤ (1 / (4 * M)) * ‖ς‖ :=
                mul_le_mul_of_nonneg_right hA (norm_nonneg ς)
            _ ≤ (1 / (4 * M)) * (2 * M) := mul_le_mul_of_nonneg_left hςhigh hB
            _ = 1 / 2 := by field_simp; ring
      have htau0arg : MandelDim.tau0 (Work.Pert.Xc d uu) = d.φ uu := by
        rw [Work.Pert.Xc, Work.Pert.tau0_tau0]
      rw [htau0arg] at h1
      refine le_trans h1 ?_
      have h2 : ‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) ≤ Ky / (M * M) :=
        div_le_div_of_nonneg_right hdevuu (mul_pos hMpos hMpos).le
      have h3 : ‖u 0 - 1‖ / M ≤ Ky / (M * M) := by
        have h4 : Ky / M / M = Ky / (M * M) := by ring
        calc ‖u 0 - 1‖ / M ≤ Ky / M / M :=
              div_le_div_of_nonneg_right (le_trans hUη hηuT) hMpos.le
          _ = Ky / (M * M) := h4
      have h4 : ‖α‖ ≤ Ky / (M * M) := le_trans hαη hηαT
      have hsum : ‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) + ‖u 0 - 1‖ / M + ‖α‖
          ≤ 3 * Ky / (M * M) := by
        have h12 : ‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) + ‖u 0 - 1‖ / M
            ≤ Ky / (M * M) + Ky / (M * M) := add_le_add h2 h3
        have h123 : ‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) + ‖u 0 - 1‖ / M + ‖α‖
            ≤ Ky / (M * M) + Ky / (M * M) + Ky / (M * M) := add_le_add h12 h4
        have heq : Ky / (M * M) + Ky / (M * M) + Ky / (M * M) = 3 * Ky / (M * M) := by ring
        rw [heq] at h123
        exact h123
      have h5 : Cseed * (‖Φm (Work.Pert.Xc d uu) - uu‖ / (M * M) + ‖u 0 - 1‖ / M + ‖α‖)
          ≤ Cseed * (3 * Ky / (M * M)) := mul_le_mul_of_nonneg_left hsum hCseedpos.le
      have h6 : Cseed * (3 * Ky / (M * M)) = 3 * Cseed * Ky / (M * M) := by ring
      exact le_trans h5 (le_of_eq h6)
    have hnp : ∀ j : ℕ, j ≤ nn → f₀^[j] (d.φ uu) = d.φ (uu + (j : ℂ)) := fun j hj =>
      Work.Pert.Ksub2.iterate_phi_of_mem d (fun i hi => hwalk i (le_trans hi hj))
    have happ' : ∀ k : ℕ, k ≤ nn → ∀ z : ℂ, ‖z - d.φ uu‖ < ccA / (Kk * M * M) →
        ‖f₀^[k] z - f₀^[k] (d.φ uu)‖ ≤ Θ * ‖z - d.φ uu‖ := by
      intro k hk z hz
      have h1 := hamp M hMA' w hw uu huuD' nn huuw k hk z hz
      have h2 : 2 * CeA * M * M / ccA = Θ := by rw [hΘ]
      rwa [h2] at h1
    have hseed_small : ‖Work.Pert.tauC σ α ς - d.φ uu‖ < ccA / (Kk * M * M) := by
      have hM2 : (0 : ℝ) < M * M := mul_pos hMpos hMpos
      have hkk : (0 : ℝ) < (Kk * M) * M := mul_pos (mul_pos hKk hMpos) hMpos
      have hden : (0 : ℝ) < 4 * (Kk * M * M) := mul_pos (by norm_num) hkk
      have hden2 : (0 : ℝ) < Kk * M * M := hkk
      have h1 : 3 * Cseed * Ky / (M * M) ≤ ccA / (4 * (Kk * M * M)) := by
        refine div_le_div_of_pos hM2 hden ?_
        have hden16 : (0 : ℝ) < 16 * Kk * Cseed := by
          have h := mul_pos (mul_pos (by norm_num : (0:ℝ) < 16) hKk) hCseedpos
          linarith only [h]
        have hKy2' : Ky * (16 * Kk * Cseed) ≤ ccA := by
          rw [le_div_iff₀ hden16] at hKy2
          exact hKy2
        have hX : (0 : ℝ) ≤ Cseed * Kk * Ky := by
          have h := mul_pos (mul_pos hCseedpos hKk) hKypos
          linarith only [h]
        have h12 : 12 * Cseed * Kk * Ky ≤ ccA := by nlinarith only [hKy2', hX]
        have h12' : (12 * Cseed * Kk * Ky) * (M * M) ≤ ccA * (M * M) :=
          mul_le_mul_of_nonneg_right h12 hM2.le
        have heq : (3 * Cseed * Ky) * (4 * (Kk * M * M))
            = (12 * Cseed * Kk * Ky) * (M * M) := by ring
        rw [heq]; exact h12'
      have h2 : ccA / (4 * (Kk * M * M)) < ccA / (Kk * M * M) := by
        rw [div_lt_div_iff₀ hden hden2]
        nlinarith only [mul_pos hccA hden2]
      exact lt_of_le_of_lt (le_trans hηseed h1) h2
    have hf0trap : ∀ j : ℕ, j ≤ nn →
        ‖f₀^[j] (Work.Pert.tauC σ α ς) - d.φ (uu + (j : ℂ))‖ ≤ (Robt / 2) / 4 := by
      intro j hj
      have h1 := happ' j hj (Work.Pert.tauC σ α ς) hseed_small
      rw [hnp j hj] at h1
      have h3 : Θ * ‖Work.Pert.tauC σ α ς - d.φ uu‖ ≤ Θ * (3 * Cseed * Ky / (M * M)) :=
        mul_le_mul_of_nonneg_left hηseed hΘpos.le
      have h4 : Θ * (3 * Cseed * Ky / (M * M)) = 3 * (Θ * eT) / 8 := by
        rw [heT]; field_simp
      have h5 : 3 * (Θ * eT) / 8 ≤ (Robt / 2) / 4 := by linarith only [hΘeT_rob, hRobtpos]
      exact le_trans (le_trans (le_trans h1 h3) (le_of_eq h4)) h5
    have hLip : ∀ j : ℕ, j < nn → ∀ x y : ℂ, ‖x - d.φ (uu + (j : ℂ))‖ ≤ Robt / 2 →
        ‖y - d.φ (uu + (j : ℂ))‖ ≤ Robt / 2 → ‖f₀ x - f₀ y‖ ≤ Lf * ‖x - y‖ := by
      intro j hj x y hx hy
      rw [hkeyw j hj] at hx hy
      refine hLfL x (hVball w hw (nn - j) (by omega) (by omega) ?_)
        y (hVball w hw (nn - j) (by omega) (by omega) ?_)
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
    have hclose : ∀ j : ℕ, j < nn → ∀ x : ℂ,
        ‖x - d.φ (uu + (j : ℂ))‖ ≤ Robt / 2 → ‖f x - f₀ x‖ ≤ δ₀ := by
      intro j hj x hx
      rw [hkeyw j hj] at hx
      refine le_of_lt (hnear.2.2.2 x (hVL (hVball w hw (nn - j) (by omega) (by omega) ?_)))
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hx
    have hsmall : δ₀ * (nn : ℝ) * Lf ^ nn ≤ (Robt / 2) / 4 := by
      have h2 : Lf ^ nn ≤ Lf ^ N := pow_le_pow_right₀ hLf1 hnN
      have h3 : (nn : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      have h4 : δ₀ * (nn : ℝ) * Lf ^ nn
          ≤ ((Robt / 2) / (8 * (N : ℝ) * Lf ^ N)) * (N : ℝ) * Lf ^ N := by
        refine mul_le_mul (mul_le_mul hδ₀rob h3 (Nat.cast_nonneg nn)
          (le_trans hδ₀pos.le hδ₀rob)) h2 (pow_nonneg hLfpos.le nn)
          (mul_nonneg (le_trans hδ₀pos.le hδ₀rob) (Nat.cast_nonneg N))
      have h5 : ((Robt / 2) / (8 * (N : ℝ) * Lf ^ N)) * (N : ℝ) * Lf ^ N
          = (Robt / 2) / 8 := by
        have hNnz : (N : ℝ) ≠ 0 := ne_of_gt hNpos
        field_simp
      have h6 : (Robt / 2) / 8 ≤ (Robt / 2) / 4 := by linarith only [hRobtpos]
      exact le_trans (le_trans h4 (le_of_eq h5)) h6
    obtain ⟨htrap, hdef⟩ := defect_le_of_trap (p := fun j => d.φ (uu + (j : ℂ)))
      (a := Work.Pert.tauC σ α ς) (n := nn) (L := Lf) (ε := δ₀) (R := Robt / 2)
      (by linarith only [hRobtpos]) (le_of_lt hδ₀pos) hLf1 hLip hclose hf0trap hsmall
    have hiter_amp : ‖f₀^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (d.φ uu)‖ ≤ δ / 4 := by
      have h1 := happ' nn le_rfl (Work.Pert.tauC σ α ς) hseed_small
      have h2 : Θ * ‖Work.Pert.tauC σ α ς - d.φ uu‖ ≤ Θ * (3 * Cseed * Ky / (M * M)) :=
        mul_le_mul_of_nonneg_left hηseed hΘpos.le
      have h3 : Θ * (3 * Cseed * Ky / (M * M)) = 3 * (Θ * eT) / 8 := by
        rw [heT]; field_simp
      have h4 : 3 * (Θ * eT) / 8 ≤ δ / 4 := by linarith only [hΘeT_δ, hδ]
      exact le_trans (le_trans (le_trans h1 h2) (le_of_eq h3)) h4
    have hwsub : w - (nn : ℂ) = uu := by rw [← huuw, add_sub_cancel_right]
    have hdphi : d.φ w = f₀^[nn] (d.φ uu) := by
      have h1 := Work.Pert.φ_iterate_sub d nn (hK hw)
      rw [hwsub] at h1
      exact h1
    have hseedP_eq : Work.Pert.seedP (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α)
        (w - (nn : ℂ)) = Work.Pert.tauC σ α ς := by
      rw [Work.Pert.seedP, hwsub, hς]
    have htailorb : ∀ j : ℕ, j < nn → f^[j] (Work.Pert.tauC σ α ς) ∈ Df := by
      intro j hj
      refine hnear.2.1 (hVL (hVball w hw (nn - j) (by omega) (by omega) ?_))
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact by simpa only [hkeyw j hj] using htrap j (le_of_lt hj)
    have hGoodP : Work.Pert.GoodP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w := by
      refine ⟨nn, ⟨ς, hςQm, ?_⟩, fun j hj => by rw [hseedP_eq]; exact htailorb j hj⟩
      rw [hwsub]; exact hςspec
    have hτF : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α (Work.Pert.liftF u σ α z)
        = f (Work.Pert.tauC σ α z) :=
      Work.Pert.Ksub2.abel_on_gate hrr hΞ hNT htQ hform hα hnorm (fun z hz => (hbnd z hz).1)
    have hOrb := hF.2.1 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) Φm
      hQAdm hNT.1 hΦm
    have hcoord : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w
        = f^[nn] (Work.Pert.tauC σ α ς) :=
      Work.Pert.coordP_level_eq hΦm.2.1 hΦm.2.2 hτF hOrb hGoodP hςQm
        (by rw [hwsub]; exact hςspec) htailorb
    have hfinal : ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w
        - d.φ w‖ < δ := by
      rw [hcoord, hdphi]
      have h1 : ‖f^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (d.φ uu)‖
          ≤ ‖f^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (Work.Pert.tauC σ α ς)‖
            + ‖f₀^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (d.φ uu)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h2 : ‖f^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (Work.Pert.tauC σ α ς)‖ ≤ δ / 4 := by
        have h3 : δ₀ * (nn : ℝ) * Lf ^ nn ≤ δ₀ * (N : ℝ) * Lf ^ N :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) hδ₀pos.le)
            (pow_le_pow_right₀ hLf1 hnN) (pow_nonneg hLfpos.le nn)
            (mul_nonneg hδ₀pos.le (Nat.cast_nonneg N))
        have h4 : δ₀ * (N : ℝ) * Lf ^ N ≤ δ / 4 := by
          have hden : (0 : ℝ) < 4 * (N : ℝ) * Lf ^ N :=
            mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNpos) hLfNpos
          have h7 := hδ₀δ
          rw [le_div_iff₀ hden] at h7
          nlinarith only [h7]
        exact le_trans (le_trans hdef h3) h4
      have hsum : ‖f^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (Work.Pert.tauC σ α ς)‖
            + ‖f₀^[nn] (Work.Pert.tauC σ α ς) - f₀^[nn] (d.φ uu)‖ ≤ δ / 4 + δ / 4 :=
        add_le_add h2 hiter_amp
      have hlt : δ / 4 + δ / 4 < δ := by linarith only [hδ]
      exact lt_of_le_of_lt (le_trans h1 hsum) hlt
    exact ⟨hGoodP, hfinal⟩
  exact ⟨Φm, hΦm, fun w hw => (hper w hw).1, fun w hw => (hper w hw).2⟩


/-- **The requested lemma.**  `coordP_close_dphi`: the same statement as
`coordP_close_of_sub_Dphi` but with the compact set `K` only assumed to lie in `d.DE` (which is
contained in `d.Dφ` by definition of `ParabData.DE`). -/
theorem coordP_close_dphi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 0 < Ξ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∃ Φm : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) ∧
          K ⊆ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) ∧
          ∀ w ∈ K, ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w
            - d.φ w‖ < ε :=
  coordP_close_of_sub_Dphi d hF hd Ξ hΞ hKc (fun w hw => (hK hw).1) ε hε

end
end Work.PertCrux
