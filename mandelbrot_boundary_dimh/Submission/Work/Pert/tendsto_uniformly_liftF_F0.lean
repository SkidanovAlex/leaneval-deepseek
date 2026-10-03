import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Basic
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.liftF_sub_model_le

namespace Work.Pert

set_option maxHeartbeats 1000000

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Helper lemmas for `tendsto_uniformly_liftF_F0` -/

/-- Maximum modulus principle, closed-ball form: a function holomorphic on `closedBall 0 R` that is
bounded by `M` on the sphere of radius `R` is bounded by `M` on the closed ball. -/
private lemma norm_le_of_forall_mem_sphere {u : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hu : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ u z)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖u z‖ ≤ M) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖u z‖ ≤ M := by
  have hd : DiffContOnCl ℂ u (Metric.ball (0 : ℂ) R) := by
    refine ⟨fun z hz => (hu z (Metric.ball_subset_closedBall hz)).differentiableWithinAt, ?_⟩
    rw [closure_ball (0 : ℂ) hR.ne']
    exact fun z hz => (hu z hz).continuousAt.continuousWithinAt
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)) hd (fun w hw => ?_) ?_
  · rw [frontier_ball (0 : ℂ) hR.ne'] at hw
    exact hM w hw
  · rwa [closure_ball (0 : ℂ) hR.ne']

/-- The algebra identity behind the limit: if `f₀ z = z + z² hF z` at `z = τ₀ w = -1/w`, then
`τ₀ (f₀ (τ₀ w)) = w + hF(τ₀ w)/(1 + τ₀ w · hF(τ₀ w))`. -/
private lemma tau0_comp_of_eq {f₀ hF : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hfe : f₀ (MandelDim.tau0 w) = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w))
    (hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0) :
    MandelDim.tau0 (f₀ (MandelDim.tau0 w))
      = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
  set t := MandelDim.tau0 w with ht
  have hwt : w * t = -1 := by
    rw [ht, MandelDim.tau0]
    field_simp [hw]
  have ht0 : t ≠ 0 := by
    intro h; rw [h, mul_zero] at hwt
    exact absurd hwt (by norm_num)
  have hA : 1 + t * hF t ≠ 0 := hden
  have htinv : -1 / t = w := by
    rw [div_eq_iff ht0]
    rw [hwt]
  have hfe' : f₀ t = t * (1 + t * hF t) := by rw [hfe]; ring
  have htau : MandelDim.tau0 (t * (1 + t * hF t)) = -1 / (t * (1 + t * hF t)) := by
    simp [MandelDim.tau0]
  have step1 : -1 / (t * (1 + t * hF t)) = (-1 / t) / (1 + t * hF t) := by
    rw [div_div]
  have step2 : w + hF t / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    rw [add_div, mul_div_cancel_right₀ _ hA]
  have h3 : w * (1 + t * hF t) + hF t = w := by
    linear_combination (hF t) * hwt
  have h4 : w / (1 + t * hF t) = (w * (1 + t * hF t) + hF t) / (1 + t * hF t) := by
    refine mul_right_cancel₀ hA ?_
    rw [div_mul_cancel₀ w hA, div_mul_cancel₀ _ hA, h3]
  rw [hfe', htau, step1, htinv, step2]
  exact h4

/-! ## The limit of the perturbed lift -/

theorem tendsto_uniformly_liftF_F0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg (some (ξ : ℂ)) none →
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {u : ℂ → ℂ} {σ α : ℂ}, α ≠ 0 → ‖α‖ ≤ η →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) r) →
        (∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → ‖u z - (f₀ z - z) / z ^ 2‖ < η) →
        ∀ w ∈ K, ‖Work.Pert.liftF u σ α w - MandelDim.tau0 (f₀ (MandelDim.tau0 w))‖ < ε := by
  obtain ⟨hD0open, h0D0, hdiff0, hf00, hd1, hd2⟩ := h₀
  have hFan : AnalyticAt ℂ f₀ 0 := hdiff0.analyticAt (hD0open.mem_nhds h0D0)
  have hF1 : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hF2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]; exact hd2
  set b : ℂ := iteratedDeriv 3 f₀ 0 / 6 with hb
  obtain ⟨hF, r', A'', A''', hr'pos, hA''nn, hA'''nn, hFeq, hFdiff, hFclose, hFbnd, hFderiv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := b) hFan hf00 hF1 hF2
      (by rw [hb]; ring)
  have hbpos : 0 < A'' + ‖b‖ + 1 := by linarith [hA''nn, norm_nonneg b]
  -- ## a radius where `hF` is holomorphic, `‖hF - 1‖ ≤ 1/4` and `‖hF‖ ≤ 3/2`
  set ρ : ℝ := min r' (min (1 / 4) (1 / (4 * (A'' + ‖b‖ + 1)))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hr'pos (lt_min (by norm_num) (div_pos one_pos (by linarith)))
  have hρle' : ρ ≤ r' := by rw [hρdef]; exact min_le_left _ _
  have hρ4 : ρ ≤ 1 / 4 := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρbig : (A'' + ‖b‖) * ρ ≤ 1 / 4 := by
    have h1 : ρ ≤ 1 / (4 * (A'' + ‖b‖ + 1)) := by
      rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : (A'' + ‖b‖) * ρ ≤ (A'' + ‖b‖) * (1 / (4 * (A'' + ‖b‖ + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith [norm_nonneg b, hA''nn])
    have h3 : (A'' + ‖b‖) * (1 / (4 * (A'' + ‖b‖ + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg b, hA''nn]
    linarith
  have hFd' : DifferentiableOn ℂ hF (Metric.ball 0 ρ) :=
    hFdiff.mono (Metric.ball_subset_ball hρle')
  have hFL : ∀ z ∈ Metric.ball 0 ρ, ‖deriv hF z‖ ≤ A''' :=
    fun z hz => hFderiv z (Metric.ball_subset_ball hρle' hz)
  have hF0 : hF 0 = 1 := by
    have h := hFclose 0 (by simpa using hr'pos)
    have h2 : ‖hF 0 - 1‖ ≤ 0 := by simpa using h
    have h3 : ‖hF 0 - 1‖ = 0 := le_antisymm h2 (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hFb2 : ∀ z ∈ Metric.ball 0 ρ, ‖hF z‖ ≤ 3 / 2 := by
    intro z hz
    have h := hFclose z (Metric.ball_subset_ball hρle' hz)
    have hzρ : ‖z‖ < ρ := by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
    have h1 : ‖hF z - 1‖ ≤ (A'' + ‖b‖) * ‖z‖ := by
      have hsplit : hF z - 1 = (hF z - 1 - b * z) + b * z := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      have hz2 : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z, hzρ, hρ4]
      have hA'' : A'' * ‖z‖ ^ 2 ≤ A'' * ‖z‖ := mul_le_mul_of_nonneg_left hz2 hA''nn
      nlinarith [h, hA'', norm_nonneg b, norm_nonneg z]
    have h2 : (A'' + ‖b‖) * ‖z‖ ≤ 1 / 4 := by
      have h3 : (A'' + ‖b‖) * ‖z‖ ≤ (A'' + ‖b‖) * ρ :=
        mul_le_mul_of_nonneg_left hzρ.le (by linarith [norm_nonneg b, hA''nn])
      linarith
    have h4 : ‖hF z‖ ≤ ‖hF z - 1‖ + 1 := by
      have := norm_add_le (hF z - 1) 1
      simpa using this
    linarith
  -- ## the region parameter
  set ξ : ℝ := max 128 (16 / ρ) with hξdef
  have hξ1 : 128 ≤ ξ := le_max_left _ _
  have hξ2 : 16 / ρ ≤ ξ := le_max_right _ _
  have hξpos : 0 < ξ := lt_of_lt_of_le (by norm_num) hξ1
  have hδ1le : 2 / ξ ≤ 1 / 64 := by
    rw [div_le_iff₀ hξpos]; linarith
  have hδ1ρ : 2 / ξ ≤ ρ / 8 := by
    rw [div_le_iff₀ hξpos]
    have h1 : (16 / ρ) * (ρ / 8) ≤ ξ * (ρ / 8) :=
      mul_le_mul_of_nonneg_right hξ2 (by positivity)
    have h2 : (16 / ρ) * (ρ / 8) = 2 := by field_simp; norm_num
    linarith [h1, h2.le, h2.ge]
  refine ⟨ξ, hξpos, ?_⟩
  intro K hK hKQ ε hε
  obtain ⟨M, hMpos, hM⟩ := hK.isBounded.exists_pos_norm_le
  set C : ℝ := 1000 * (A''' + 1) * (4 * Real.pi + 2) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set η₁ : ℝ := min (1 / 1000)
      (min (1 / (2 * Real.pi)) (min (1 / (4 * Real.pi * M)) (ρ / (8 * (4 * Real.pi + 1)))))
    with hη₁def
  have hη₁pos : 0 < η₁ := by
    rw [hη₁def]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hη₁a : η₁ ≤ 1 / 1000 := by rw [hη₁def]; exact min_le_left _ _
  have hη₁b : η₁ ≤ 1 / (2 * Real.pi) := by
    rw [hη₁def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη₁c : η₁ ≤ 1 / (4 * Real.pi * M) := by
    rw [hη₁def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη₁d : η₁ ≤ ρ / (8 * (4 * Real.pi + 1)) := by
    rw [hη₁def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set η : ℝ := min η₁ (ε / (2 * C)) with hηdef
  have hηpos : 0 < η := lt_min hη₁pos (by positivity)
  have hηa : η ≤ 1 / 1000 := le_trans (min_le_left _ _) hη₁a
  have hηb : η ≤ 1 / (2 * Real.pi) := le_trans (min_le_left _ _) hη₁b
  have hηc : η ≤ 1 / (4 * Real.pi * M) := le_trans (min_le_left _ _) hη₁c
  have hηd : η ≤ ρ / (8 * (4 * Real.pi + 1)) := le_trans (min_le_left _ _) hη₁d
  have hηε : η ≤ ε / (2 * C) := min_le_right _ _
  refine ⟨ρ, hρpos, η, hηpos, ?_⟩
  intro u σ α hα hαη hnorm hu hud
  -- ## `u 0` is close to `1` (maximum modulus on the punctured ball)
  have hu0 : ‖u 0 - 1‖ ≤ η := by
    have hR : 0 < ρ / 2 := by linarith
    have hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
        DifferentiableAt ℂ (fun z => u z - hF z) z := by
      intro z hz
      have hzρ : z ∈ Metric.ball (0 : ℂ) ρ :=
        Metric.closedBall_subset_ball (by linarith : ρ / 2 < ρ) hz
      exact ((hu z hzρ).differentiableAt (Metric.isOpen_ball.mem_nhds hzρ)).sub
        ((hFd' z hzρ).differentiableAt (Metric.isOpen_ball.mem_nhds hzρ))
    have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) (ρ / 2), ‖u z - hF z‖ ≤ η := by
      intro z hz
      have hzn : z ≠ 0 := by
        intro h; rw [h] at hz
        simp only [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
        linarith
      have hzρ : z ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_sphere, dist_zero_right] at hz
        exact Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith)
      have h1 := hud z hzρ hzn
      have hfe := hFeq z (Metric.ball_subset_ball hρle' hzρ)
      have heq : (f₀ z - z) / z ^ 2 = hF z := by rw [hfe]; field_simp; try ring
      rw [heq] at h1
      exact h1.le
    have h := norm_le_of_forall_mem_sphere hR hdiff hbd 0
      (by simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]; linarith)
    simpa [hF0] using h
  intro w hwK
  have hwQ := hKQ hwK
  -- ## geometry of the region
  have hwre : ξ < w.re + |w.im| := by
    have h := hwQ.1 (ξ : ℂ) rfl
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      at h
    linarith
  have hwnorm : ξ / 2 < ‖w‖ := by
    have h2 : w.re ≤ |w.re| := le_abs_self _
    have h3 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h4 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    linarith
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hwnorm
    simp only [norm_zero] at hwnorm
    linarith
  -- ## `τ₀ w` is small
  have hnorm_tau : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by
    simp [MandelDim.tau0]
  have ht : ‖MandelDim.tau0 w‖ ≤ 2 / ξ := by
    rw [hnorm_tau]
    have h2 : (2 / ξ) * (ξ / 2) = 1 := by field_simp
    have h : 1 ≤ (2 / ξ) * ‖w‖ := by
      calc (1 : ℝ) = (2 / ξ) * (ξ / 2) := h2.symm
        _ ≤ (2 / ξ) * ‖w‖ := mul_le_mul_of_nonneg_left hwnorm.le (by positivity)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖)).mpr h
  have htρ : ‖MandelDim.tau0 w‖ ≤ ρ / 4 :=
    le_trans ht (le_trans hδ1ρ (by linarith [hρpos]))
  have htball : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρ :=
    Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith [htρ, hρpos])
  have htball' : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) r' := Metric.ball_subset_ball hρle' htball
  have hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
    intro h
    have htG : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by linear_combination h
    have h1 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ < 1 := by
      rw [norm_mul]
      calc ‖MandelDim.tau0 w‖ * ‖hF (MandelDim.tau0 w)‖
          ≤ (ρ / 4) * (3 / 2) :=
            mul_le_mul htρ (hFb2 _ htball) (norm_nonneg _) (by positivity)
        _ < 1 := by nlinarith [hρ4]
    rw [htG, norm_neg, norm_one] at h1
    exact absurd h1 (by norm_num)
  -- ## the bound on `σ`
  have hu0half : ‖u 0 - 1‖ ≤ 1 / 2 := le_trans hu0 (by linarith [hηa])
  have hα2pi : ‖α‖ ≤ 1 / (2 * Real.pi) := le_trans hαη hηb
  have hσ1 : ‖σ / α + 2 * Real.pi * Complex.I‖ ≤ (8 * Real.pi ^ 2 + 4 * Real.pi) * η := by
    have h := (sigma_alpha_close hα hα2pi hu0half hnorm).1
    have h1 : 8 * Real.pi ^ 2 * ‖α‖ ≤ 8 * Real.pi ^ 2 * η :=
      mul_le_mul_of_nonneg_left hαη (by positivity)
    have h2 : 4 * Real.pi * ‖u 0 - 1‖ ≤ 4 * Real.pi * η :=
      mul_le_mul_of_nonneg_left hu0 (by positivity)
    linarith
  -- ## `‖α‖ ‖w‖ ≤ 1/2`
  have hMw : ‖α‖ * ‖w‖ ≤ 1 / (4 * Real.pi) := by
    have h1 : η * M ≤ 1 / (4 * Real.pi) := by
      have h2 : η * M ≤ (1 / (4 * Real.pi * M)) * M :=
        mul_le_mul_of_nonneg_right hηc hMpos.le
      have h3 : (1 / (4 * Real.pi * M)) * M = 1 / (4 * Real.pi) := by field_simp; try ring
      linarith [h2, h3.le, h3.ge]
    exact le_trans (mul_le_mul hαη (hM w hwK) (norm_nonneg _) hηpos.le) h1
  have hαw : ‖α‖ * ‖w‖ ≤ 1 / 2 := by
    have : 1 / (4 * Real.pi) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    linarith
  have hsmall : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2 := by
    have h1 : 2 * Real.pi * (‖α‖ * ‖w‖) ≤ 2 * Real.pi * (1 / (4 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hMw (by positivity)
    have h2 : 2 * Real.pi * (1 / (4 * Real.pi)) = 1 / 2 := by field_simp; try ring
    linarith [h1, h2.le, h2.ge]
  -- ## `τ_f w` is close to `τ₀ w`
  have hδ2 : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ (4 * Real.pi + 1) * η := by
    have h := Work.Pert.tauC_add_inv_le σ α w hα hwne (m := ξ / 2)
      (by linarith [hξpos]) (le_of_lt hwnorm) hsmall
    have h2 : Work.Pert.tauC σ α w - MandelDim.tau0 w = Work.Pert.tauC σ α w + 1 / w := by
      rw [MandelDim.tau0]; ring
    rw [h2]
    have hA : ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * (ξ / 2)) ≤ η := by
      rw [div_le_iff₀ (by positivity)]
      have hAx : 8 * Real.pi ^ 2 + 4 * Real.pi ≤ Real.pi * (ξ / 2) := by
        nlinarith [hξ1, Real.pi_pos, Real.pi_lt_four]
      have h3 : (8 * Real.pi ^ 2 + 4 * Real.pi) * η ≤ (Real.pi * (ξ / 2)) * η :=
        mul_le_mul_of_nonneg_right hAx hηpos.le
      linarith [hσ1, h3]
    have hB : (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi ≤ 4 * Real.pi * η := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hαη, Real.pi_pos]
    refine le_trans h (le_trans (add_le_add hA hB) ?_)
    linarith
  -- ## closeness on the punctured ball, in terms of `hF`
  have huc : ∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 → ‖u z - hF z‖ ≤ η := by
    intro z hz hz0
    have h1 := hud z hz hz0
    have hfe := hFeq z (Metric.ball_subset_ball hρle' hz)
    have heq : (f₀ z - z) / z ^ 2 = hF z := by rw [hfe]; field_simp; try ring
    rw [heq] at h1
    exact h1.le
  -- ## the pointwise estimate
  have hδsum : 2 / ξ + (4 * Real.pi + 1) * η ≤ ρ / 4 := by
    have h4 : (4 * Real.pi + 1) * η ≤ ρ / 8 := by
      have h5 : (4 * Real.pi + 1) * η ≤ (4 * Real.pi + 1) * (ρ / (8 * (4 * Real.pi + 1))) :=
        mul_le_mul_of_nonneg_left hηd (by positivity)
      have h6 : (4 * Real.pi + 1) * (ρ / (8 * (4 * Real.pi + 1))) = ρ / 8 := by
        field_simp; try ring
      linarith [h5, h6.le, h6.ge]
    linarith [hδ1ρ, h4]
  have hmain : ‖Work.Pert.liftF u σ α w
      - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖
      ≤ 1000 * (A''' + 1) * (η + (4 * Real.pi + 1) * η) :=
    liftF_sub_model_le (hρ := hρpos) (hρ4 := hρ4) (hD := hA'''nn)
      (hη := hηpos) (hη1 := hηa)
      (hδ1 := ht) (hδ1' := hδ1le)
      (hδ2 := hδ2) (hδ2' := by positivity)
      (hδsum := hδsum)
      (hFd := hFd') (hFl := hFL) (hFb := hFb2)
      (hu := hu) (huc := huc) (hu0 := hu0)
      (hα := hα) (hαη := hαη) (hαπ := hα2pi)
      (hnorm := hnorm) (hw := hwne) (hwu := hαw)
  -- ## assemble
  have hid := tau0_comp_of_eq (hF := hF) hwne (hFeq (MandelDim.tau0 w) htball') hden
  calc ‖Work.Pert.liftF u σ α w - MandelDim.tau0 (f₀ (MandelDim.tau0 w))‖
      = ‖Work.Pert.liftF u σ α w
          - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖ := by
        rw [hid]
    _ ≤ 1000 * (A''' + 1) * (η + (4 * Real.pi + 1) * η) := hmain
    _ = C * η := by rw [hCdef]; ring
    _ ≤ ε / 2 := by
        calc C * η ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left hηε hCpos.le
          _ = ε / 2 := by field_simp
    _ < ε := by linarith

end

end Work.Pert
