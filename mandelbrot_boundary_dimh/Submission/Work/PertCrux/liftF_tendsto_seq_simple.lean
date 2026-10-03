import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates
import Submission.Work.Pert.scale_tau
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.Qreg_norm_lower
import Submission.Work.Pert.limitCoord_plus_exists
import Submission.Work.Pert.qadm
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.Ksub2.liftF_sub_model_le_pointwise
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.PertCrux.gate_tauC_lower
import Submission.Work.PertCrux.tauC_close_tau0_seq
import Submission.Work.PertCrux.alpha_u0_tendsto_zero_seq
import Submission.Work.PertCrux.u_close_of_nearOn_explicit

namespace Work.PertCrux

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

/-! ## Helpers -/

/-- `NearOn` is monotone in the compact set and in the tolerance. -/
theorem NearOn_mono {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ} (hL : L' ⊆ L) (hδ : δ ≤ δ')
    (h : MandelDim.NearOn f₀ f Df L δ) : MandelDim.NearOn f₀ f Df L' δ' :=
  ⟨h.1, fun z hz => h.2.1 (hL hz), h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z (hL hz)) hδ⟩

/-- The unperturbed model identity: if `f₀ z = z + z ^ 2 * hF z` at `z = τ₀ w = -1/w`, then
`τ₀ (f₀ (τ₀ w)) = w + hF (τ₀ w) / (1 + τ₀ w · hF (τ₀ w))`. -/
theorem tau0_comp_eq {f₀ hF : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hfe : f₀ (MandelDim.tau0 w)
      = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w))
    (hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0) :
    MandelDim.tau0 (f₀ (MandelDim.tau0 w))
      = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
  set t := MandelDim.tau0 w with ht
  have hwt : w * t = -1 := by rw [ht, MandelDim.tau0]; field_simp [hw]
  have ht0 : t ≠ 0 := by
    intro h; rw [h, mul_zero] at hwt; exact absurd hwt (by norm_num)
  have hA : 1 + t * hF t ≠ 0 := hden
  have htinv : -1 / t = w := by rw [div_eq_iff ht0]; rw [hwt]
  have hfe' : f₀ t = t * (1 + t * hF t) := by rw [hfe]; ring
  have htau : MandelDim.tau0 (t * (1 + t * hF t)) = -1 / (t * (1 + t * hF t)) := by
    simp [MandelDim.tau0]
  have step1 : -1 / (t * (1 + t * hF t)) = (-1 / t) / (1 + t * hF t) := by rw [div_div]
  have step2 : w + hF t / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    rw [add_div, mul_div_cancel_right₀ _ hA]
  have h3 : w * (1 + t * hF t) + hF t = w := by linear_combination (hF t) * hwt
  have h4 : w / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    refine mul_right_cancel₀ hA ?_
    rw [div_mul_cancel₀ w hA, div_mul_cancel₀ _ hA, h3]
  rw [hfe', htau, step1, htinv, step2]
  exact h4

/-! ## The main theorem -/

theorem liftF_tendsto_seq_simple {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none →
      ∀ (δ : ℕ → ℝ), (∀ n, 0 < δ n) → Filter.Tendsto δ Filter.atTop (nhds 0) →
      ∀ (f : ℕ → ℂ → ℂ) (Df : ℕ → Set ℂ) (rr : ℕ → ℝ) (u : ℕ → ℂ → ℂ) (σ α : ℕ → ℂ),
        (∀ n, MandelDim.NearOn f₀ (f n) (Df n) (Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ'))
          (δ n)) →
        (∀ n, f n 0 = 0) →
        (∀ n, MandelDim.InF1 (MandelDim.rotOf (f n))) →
        (∀ n, α n = MandelDim.rotOf (f n)) →
        (∀ n, 0 < rr n) →
        (∀ n, 1 / (4 * (Ξ' + 1)) ≤ rr n) →
        (∀ n, ‖α n‖ ≤ 1 / 64) →
        (∀ n, DifferentiableOn ℂ (u n) (Metric.ball 0 (rr n))) →
        (∀ n z, z ∈ Metric.ball 0 (rr n) → 1 / 2 ≤ ‖u n z‖ ∧ ‖u n z‖ ≤ 2) →
        (∀ n z, z ∈ Metric.ball 0 (rr n) → f n z = z + z * (z - σ n) * u n z) →
        (∀ n, 1 - σ n * u n 0 = Complex.exp (2 * Real.pi * Complex.I * α n)) →
        (∀ n, MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α n))) →
        (∀ n, ∀ z ∈ Work.Pert.Qp Ξ' (α n), Work.Pert.tauC (σ n) (α n) z ∈ Metric.ball 0 (rr n)) →
        TendstoUniformlyOn
          (fun n : ℕ => fun w : ℂ => Work.Pert.liftF (u n) (σ n) (α n) w)
          (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Filter.atTop K := by
  have hgerm : MandelDim.IsParabolicGerm f₀ D₀ := hd
  obtain ⟨hD0open, h0D0, hdiff0, hf00, hd1, hd2⟩ := hgerm
  have hFan : AnalyticAt ℂ f₀ 0 := hdiff0.analyticAt (hD0open.mem_nhds h0D0)
  have hF1 : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hF2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]; exact hd2
  set b : ℂ := iteratedDeriv 3 f₀ 0 / 6 with hbdef
  obtain ⟨hF, r', A'', A''', hr'pos, hA''nn, hA'''nn, hFeq, hFdiff, hFclose, hFbnd, hFderiv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := b) hFan hf00 hF1 hF2
      (by rw [hbdef]; ring)
  obtain ⟨r₀, hr₀pos, hr₀sub, C, hCpos, hsm⟩ := Work.Pert.small_of_nearOn hd
  set ρ : ℝ := min r' (min (1 / 4) (1 / (4 * (A'' + ‖b‖ + 1)))) with hρdef
  have hBpos : 0 < A'' + ‖b‖ + 1 := by linarith [hA''nn, norm_nonneg b]
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min hr'pos (lt_min (by norm_num) (by positivity))
  have hρ4 : ρ ≤ 1 / 4 := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρr' : ρ ≤ r' := by rw [hρdef]; exact min_le_left _ _
  have hρbig : (A'' + ‖b‖) * ρ ≤ 1 / 4 := by
    have h1 : ρ ≤ 1 / (4 * (A'' + ‖b‖ + 1)) := by
      rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : (A'' + ‖b‖) * ρ ≤ (A'' + ‖b‖) * (1 / (4 * (A'' + ‖b‖ + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith [hA''nn, norm_nonneg b])
    have h3 : (A'' + ‖b‖) * (1 / (4 * (A'' + ‖b‖ + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hA''nn, norm_nonneg b])]
      nlinarith [hA''nn, norm_nonneg b]
    linarith
  have hFd : DifferentiableOn ℂ hF (Metric.ball 0 ρ) := hFdiff.mono (Metric.ball_subset_ball hρr')
  have hFL : ∀ z ∈ Metric.ball 0 ρ, ‖deriv hF z‖ ≤ A''' :=
    fun z hz => hFderiv z (Metric.ball_subset_ball hρr' hz)
  have hF0 : hF 0 = 1 := by
    have h := hFclose 0 (by simpa using hr'pos)
    have h2 : ‖hF 0 - 1‖ ≤ 0 := by simpa using h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h2 (norm_nonneg _)))
  have hFb2 : ∀ z ∈ Metric.ball 0 ρ, ‖hF z‖ ≤ 3 / 2 := by
    intro z hz
    have hzmem : z ∈ Metric.ball 0 r' := Metric.ball_subset_ball hρr' hz
    have hzle : ‖z‖ ≤ ρ := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    have h1 : ‖hF z - 1 - b * z‖ ≤ A'' * ‖z‖ ^ 2 := hFclose z hzmem
    have h2 : ‖hF z - 1‖ ≤ (A'' + ‖b‖) * ρ := by
      have h3 : ‖hF z - 1‖ ≤ ‖hF z - 1 - b * z‖ + ‖b * z‖ := by
        have hh := norm_add_le (hF z - 1 - b * z) (b * z)
        rwa [show (hF z - 1 - b * z) + b * z = hF z - 1 by ring] at hh
      have h4 : ‖b * z‖ ≤ ‖b‖ * ρ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hzle (norm_nonneg b)
      have h5 : A'' * ‖z‖ ^ 2 ≤ A'' * ρ := by
        refine mul_le_mul_of_nonneg_left ?_ hA''nn
        nlinarith [norm_nonneg z, hzle, hρpos]
      linarith
    have h7 : ‖hF z‖ ≤ ‖hF z - 1‖ + 1 := by
      have hh := norm_add_le (hF z - 1) (1 : ℂ)
      simpa using hh
    linarith
  refine ⟨max 128 (max (16 * Real.pi / ρ) (16 * Real.pi / r₀)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro Ξ' hΞ'
    have hΞ'128 : (128 : ℝ) ≤ Ξ' := le_trans (le_max_left _ _) hΞ'
    have hΞ'64 : (64 : ℝ) ≤ Ξ' := by linarith
    have hΞ'pos : 0 < Ξ' := by linarith
    have harg : max (16 * Real.pi / ρ) (16 * Real.pi / r₀) ≤ Ξ' :=
      le_trans (le_max_right _ _) hΞ'
    have h16ρ : 16 * Real.pi / ρ ≤ Ξ' := le_trans (le_max_left _ _) harg
    have h16r : 16 * Real.pi / r₀ ≤ Ξ' := le_trans (le_max_right _ _) harg
    have hA1 : 16 * Real.pi ≤ ρ * Ξ' := by
      rw [div_le_iff₀ hρpos] at h16ρ; linarith
    have hA2 : 16 * Real.pi ≤ r₀ * Ξ' := by
      rw [div_le_iff₀ hr₀pos] at h16r; linarith
    have hδ₁ρ : 2 / Ξ' ≤ ρ / 8 := by
      rw [div_le_div_iff₀ hΞ'pos (by norm_num : (0 : ℝ) < 8)]
      linarith [Real.pi_gt_three]
    have h8πρ : 8 * Real.pi / Ξ' < ρ := by
      have h2 : 8 * Real.pi / Ξ' ≤ ρ / 2 := by
        rw [div_le_div_iff₀ hΞ'pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      linarith
    have h8πr : 8 * Real.pi / Ξ' < r₀ := by
      have h2 : 8 * Real.pi / Ξ' ≤ r₀ / 2 := by
        rw [div_le_div_iff₀ hΞ'pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      linarith
    have h8π16 : 8 * Real.pi / Ξ' < 16 * Real.pi / Ξ' := by
      rw [div_lt_div_iff_of_pos_right hΞ'pos]; linarith [Real.pi_pos]
    intro K hKc hKcone δ hδpos hδ0 f Df rr u σ α hNear hf0 hInF1 hαeq hrrpos hrrlb hα64
      hudiff hubnd hform hnorm hQAdm hτC
    have hInF1α : ∀ n, MandelDim.InF1 (α n) := fun n => by rw [hαeq n]; exact hInF1 n
    have hαne : ∀ n, α n ≠ 0 := fun n => by
      have h := hInF1α n
      simp only [MandelDim.InF1] at h
      intro h0
      rw [h0] at h
      simp at h
    have hαpos : ∀ n, 0 < ‖α n‖ := fun n => by
      have h := hInF1α n
      simp only [MandelDim.InF1] at h
      exact norm_pos_iff.mpr (fun h0 => by rw [h0] at h; simp at h)
    obtain ⟨hαtend, hu0tend⟩ :=
      alpha_u0_tendsto_zero_seq (f₀ := f₀) (D₀ := D₀) hd hΞ'pos hδpos hδ0 hNear hf0 hαeq hrrpos hrrlb
        hudiff hubnd hform
    obtain ⟨M₀, hM₀⟩ := hKc.isBounded.exists_norm_le
    set M : ℝ := max M₀ 1 with hMdef
    have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hMle : ∀ w ∈ K, ‖w‖ ≤ M := fun w hw => le_trans (hM₀ w hw) (le_max_left _ _)
    have hre : ∀ R : ℝ, ∀ᶠ n in atTop, R ≤ (1 / α n).re := by
      intro R
      rcases lt_or_ge 0 R with hR | hR
      · have h2 : (0 : ℝ) < 1 / (2 * R) := by positivity
        filter_upwards [hαtend.eventually (isOpen_Iio.mem_nhds h2)] with n hn
        have h1 := Work.Pert.inv_re_lower (hInF1α n)
        have h3 : R < 1 / (2 * ‖α n‖) := by
          rw [lt_div_iff₀ (by have hp := hαpos n; positivity : (0 : ℝ) < 2 * ‖α n‖)]
          rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * R)] at hn
          linarith
        linarith
      · refine Filter.Eventually.of_forall (fun n => ?_)
        have h1 := Work.Pert.inv_re_lower (hInF1α n)
        have h2 : (0 : ℝ) < 1 / (2 * ‖α n‖) := by
          have hp := hαpos n
          positivity
        linarith
    have hKQp : ∀ᶠ n in atTop, ∀ w ∈ K, w ∈ Work.Pert.Qp Ξ' (α n) := by
      obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ z ∈ K, z.re ≤ C := by
        obtain ⟨a, ha⟩ := hKc.image Complex.continuous_re |>.bddAbove
        exact ⟨a, fun z hz => ha ⟨z, hz, rfl⟩⟩
      set C₁ : ℝ := C₀ + Ξ' + 1 with hC₁def
      filter_upwards [hre C₁] with n hn
      intro w hw
      rw [Work.Pert.Qp_mem_iff]
      have hcone : Ξ' - |w.im| < w.re := by
        have h1 := hKcone hw
        rw [Work.Pert.mem_Qreg_cone] at h1
        linarith
      refine ⟨hcone, ?_⟩
      have h2 : w.re ≤ C₀ := hC₀ w hw
      have h3 : C₁ ≤ (1 / α n).re := hn
      have h4 : (0 : ℝ) ≤ |w.im - (1 / α n).im| := abs_nonneg _
      linarith
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ₂ : ℝ := min (ρ / 8) (ε / (4000 * (A''' + 1))) with hδ₂def
    set η : ℝ := min (1 / 1000) (ε / (4000 * (A''' + 1))) with hηdef
    have hA'''1 : 0 < A''' + 1 := by linarith
    have hδ₂pos : 0 < δ₂ := by
      rw [hδ₂def]; exact lt_min (by positivity) (by positivity)
    have hδ₂leρ : δ₂ ≤ ρ / 8 := by rw [hδ₂def]; exact min_le_left _ _
    have hηpos : 0 < η := by rw [hηdef]; exact lt_min (by norm_num) (by positivity)
    have hη1000 : η ≤ 1 / 1000 := by rw [hηdef]; exact min_le_left _ _
    have hηleε : η ≤ ε / (4000 * (A''' + 1)) := by rw [hηdef]; exact min_le_right _ _
    have hδ₂leε : δ₂ ≤ ε / (4000 * (A''' + 1)) := by rw [hδ₂def]; exact min_le_right _ _
    have hsum : 2 / Ξ' + δ₂ ≤ ρ / 4 := by linarith
    have hfin : 1000 * (A''' + 1) * (η + δ₂) < ε := by
      have h2 : η + δ₂ ≤ 2 * (ε / (4000 * (A''' + 1))) := by linarith
      have h3 : 1000 * (A''' + 1) * (2 * (ε / (4000 * (A''' + 1)))) = ε / 2 := by
        field_simp
        ring
      have h4 : 1000 * (A''' + 1) * (η + δ₂)
          ≤ 1000 * (A''' + 1) * (2 * (ε / (4000 * (A''' + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      rw [h3] at h4
      linarith
    obtain ⟨hT1, hT2⟩ :=
      tauC_close_tau0_seq (Ξ' := Ξ') hΞ'64 hKc hKcone hInF1α hnorm hαtend hu0tend (ε := δ₂) hδ₂pos
    set rbar : ℝ := min ρ (min r₀ (16 * Real.pi / Ξ')) with hrbardef
    have hrbarpos : 0 < rbar := by
      rw [hrbardef]
      exact lt_min hρpos (lt_min hr₀pos (by positivity))
    have hrbarleρ : rbar ≤ ρ := by rw [hrbardef]; exact min_le_left _ _
    have hrbarler₀ : rbar ≤ r₀ := by
      rw [hrbardef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hrbarle16 : rbar ≤ 16 * Real.pi / Ξ' := by
      rw [hrbardef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hrbarsub : Metric.closedBall (0 : ℂ) rbar ⊆ D₀ :=
      (Metric.closedBall_subset_closedBall hrbarler₀).trans hr₀sub
    set c : ℝ := min (1 / (4 * (Ξ' + 1))) rbar with hcdef
    have hcpos : 0 < c := by rw [hcdef]; exact lt_min (by positivity) hrbarpos
    have h8πrbar : 8 * Real.pi / Ξ' < rbar :=
      lt_min h8πρ (lt_min h8πr h8π16)
    filter_upwards [hT1, hT2, hKQp,
      hαtend.eventually (isOpen_Iio.mem_nhds hηpos),
      hu0tend.eventually (isOpen_Iio.mem_nhds hηpos),
      hαtend.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * M))),
      hδ0.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < (η / 2) * c ^ 2 / 10))]
      with n hT1n hT2n hKQpn hαη hu0η hαM hδtiny
    intro w hw
    have hwfar : Ξ' / 2 < ‖w‖ := (Work.Pert.Qreg_norm_lower hΞ'pos).1 w (hKcone hw)
    have hwne : w ≠ 0 := by
      intro h; rw [h] at hwfar; simp at hwfar; linarith
    have hτ0 : ‖MandelDim.tau0 w‖ ≤ 2 / Ξ' := by
      rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < ‖w‖) hΞ'pos]
      linarith
    have hδ₁64 : 2 / Ξ' ≤ 1 / 64 := by
      rw [div_le_iff₀ hΞ'pos]; linarith
    have hδ₂W : ‖Work.Pert.tauC (σ n) (α n) w - MandelDim.tau0 w‖ ≤ δ₂ := hT1n w hw
    have hWsmall : ‖Work.Pert.tauC (σ n) (α n) w‖ ≤ 8 * Real.pi / Ξ' := hT2n w hw
    have hWltρ : ‖Work.Pert.tauC (σ n) (α n) w‖ < ρ := lt_of_le_of_lt hWsmall h8πρ
    have hWmemρ : Work.Pert.tauC (σ n) (α n) w ∈ Metric.ball (0 : ℂ) ρ := by
      rwa [Metric.mem_ball, dist_zero_right]
    set W : ℂ := Work.Pert.tauC (σ n) (α n) w with hWdef
    have hWlt_rr : ‖W‖ < rr n := by
      have h := hτC n w (hKQpn w hw)
      rw [Metric.mem_ball, dist_zero_right] at h
      simpa [hWdef] using h
    have hWsmall' : ‖W‖ ≤ 8 * Real.pi / Ξ' := by simpa [hWdef] using hWsmall
    have hWmem : W ∈ Metric.ball (0 : ℂ) (min (rr n) rbar) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_min hWlt_rr (lt_of_le_of_lt hWsmall' h8πrbar)
    have hc_le : c ≤ min (rr n) rbar := by
      rw [hcdef]
      exact le_min (le_trans (min_le_left _ _) (hrrlb n)) (min_le_right _ _)
    have hδc_ge : δ n < η / 2 * (min (rr n) rbar) ^ 2 / 10 := by
      have h1 : c ^ 2 ≤ (min (rr n) rbar) ^ 2 := pow_le_pow_left₀ hcpos.le hc_le 2
      have h2 : (η / 2) * c ^ 2 / 10 ≤ η / 2 * (min (rr n) rbar) ^ 2 / 10 := by
        nlinarith [h1, hηpos]
      linarith
    have huc := u_close_of_nearOn_explicit (f₀ := f₀) (D₀ := D₀) hd (ρ := min (rr n) rbar)
      (lt_min (hrrpos n) hrbarpos) (η := η / 2) (by positivity)
      (f n) (Df n) (Metric.closedBall (0 : ℂ) rbar) (u n) (σ n)
      (isCompact_closedBall (x := (0 : ℂ)) (r := rbar))
      (Metric.closedBall_subset_closedBall (min_le_right _ _))
      hrbarsub
      (NearOn_mono (Metric.closedBall_subset_closedBall hrbarle16) hδc_ge.le (hNear n))
      (hf0 n)
      ((hudiff n).mono (Metric.ball_subset_ball (min_le_left _ _)))
      (fun z hz => hubnd n z (Metric.ball_subset_ball (min_le_left _ _) hz))
      (fun z hz => hform n z (Metric.ball_subset_ball (min_le_left _ _) hz))
    have hut : ‖u n W - hF W‖ ≤ η := by
      rcases eq_or_ne W 0 with hW0 | hWne
      · rw [hW0, hF0]
        exact hu0η.le
      · have hp := huc W hWmem hWne
        have hident : (f₀ W - W) / W ^ 2 = hF W := by
          have hfe : f₀ W = W + W ^ 2 * hF W := hFeq W (Metric.ball_subset_ball hρr' hWmemρ)
          rw [hfe]
          field_simp
          ring
        rw [hident] at hp
        linarith [hp, hηpos]
    have hαπ : ‖α n‖ ≤ 1 / (2 * Real.pi) := by
      refine le_trans hαη.le (le_trans hη1000 ?_)
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1000) (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_lt_four]
    have hwu : ‖α n‖ * ‖w‖ ≤ 1 / 2 := by
      have h1 : ‖α n‖ * M ≤ (1 / (2 * M)) * M :=
        mul_le_mul_of_nonneg_right hαM.le hMpos.le
      have h2 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
      have h3 : ‖α n‖ * ‖w‖ ≤ ‖α n‖ * M :=
        mul_le_mul_of_nonneg_left (hMle w hw) (norm_nonneg _)
      linarith
    have hkey := Work.Pert.Ksub2.liftF_sub_model_le_pointwise (u := u n) (hF := hF)
      (σ := σ n) (α := α n) (w := w) (ρ := ρ) (D := A''') (η := η) (δ₁ := 2 / Ξ') (δ₂ := δ₂)
      hρpos hρ4 hA'''nn hηpos hη1000 hτ0 hδ₁64 hδ₂W hδ₂pos.le hsum hFd hFL hFb2 hut hu0η.le
      (hαne n) hαη.le hαπ (hnorm n) hwne hwu
    have hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
      intro h
      have h1 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ = 1 := by
        have h2 : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by linear_combination h
        rw [h2, norm_neg, norm_one]
      have hτ0mem : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        linarith [hτ0, hδ₁ρ, hρpos]
      have hb := hFb2 (MandelDim.tau0 w) hτ0mem
      have h3 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ < 1 := by
        rw [norm_mul]
        calc ‖MandelDim.tau0 w‖ * ‖hF (MandelDim.tau0 w)‖ ≤ (1 / 64) * (3 / 2) :=
              mul_le_mul (le_trans hτ0 hδ₁64) hb (norm_nonneg _) (by norm_num)
          _ < 1 := by norm_num
      linarith
    have hmodel : MandelDim.tau0 (f₀ (MandelDim.tau0 w))
        = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) :=
      tau0_comp_eq (f₀ := f₀) (hF := hF) hwne
        (hFeq (MandelDim.tau0 w) (Metric.ball_subset_ball hρr' (by
          rw [Metric.mem_ball, dist_zero_right]
          linarith [hτ0, hδ₁ρ, hρpos]))) hden
    rw [dist_eq_norm, hmodel, norm_sub_rev]
    linarith [hkey, hfin]

end

end Work.PertCrux
