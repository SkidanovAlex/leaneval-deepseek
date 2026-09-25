/-
Cutting off a `C^∞` function vanishing at the origin: the sup norm and the `α`-Hölder
constant of the product with a bump of radius `δ` are as small as desired for `δ` small.
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy

noncomputable section

namespace Work.Beltrami

open scoped ContDiff Topology

set_option maxHeartbeats 4000000 in
/-- Cutting off a `C^∞` function vanishing at `0` by a bump of radius `δ` makes its sup norm and
its `α`-Hölder constant as small as desired, uniformly in the cut-off function. -/
theorem cutoff_estimates {μ₀ : ℂ → ℂ} {ρ α ε κ : ℝ} (hρ : 0 < ρ)
    (hμ : ContDiffOn ℝ ∞ μ₀ (Metric.ball 0 ρ)) (h0 : μ₀ 0 = 0)
    (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ (δ : ℝ) (μ : ℂ → ℂ), 0 < δ ∧ δ < ρ ∧
      ContDiff ℝ ∞ μ ∧ HasCompactSupport μ ∧
      (∀ z, δ ≤ ‖z‖ → μ z = 0) ∧
      (∀ z, ‖z‖ < δ / 2 → μ z = μ₀ z) ∧
      (∀ z, ‖μ z‖ ≤ ε) ∧
      (∀ x y : ℂ, ‖μ x - μ y‖ ≤ κ * ‖x - y‖ ^ α) := by
  classical
  have hcoe : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => RCLike.norm_ofReal r
  have hβs : ContDiff ℝ ∞ (fun z : ℂ => (bumpC z : ℂ)) := bumpC_contDiffC
  have hβcs : HasCompactSupport (fun z : ℂ => (bumpC z : ℂ)) := bumpC_hasCompactSupport
  obtain ⟨Cnn, hβlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβcs hβs (by decide)
  have hC1 : ContDiffAt ℝ 1 μ₀ 0 := (hμ.contDiffAt (Metric.ball_mem_nhds 0 hρ)).of_le (by simp)
  obtain ⟨Knn, t, ht, hKt⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨r₁, hr₁, hr₁t⟩ := Metric.mem_nhds_iff.mp ht
  set Cb : ℝ := (Cnn : ℝ) with hCbdef
  set K : ℝ := (Knn : ℝ) with hKdef
  have hCb0 : 0 ≤ Cb := by rw [hCbdef]; positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set L : ℝ := K + 1 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hLK : K ≤ L := by rw [hLdef]; linarith
  set M₁ : ℝ := (Cb + 1) * L with hM₁def
  have hM₁pos : 0 < M₁ := by rw [hM₁def]; exact mul_pos (by linarith) hLpos
  set e : ℝ := 1 / (1 - α) with hedef
  have hden : (1:ℝ) - α ≠ 0 := ne_of_gt (by linarith)
  have hepos : 0 < e := by rw [hedef]; exact div_pos one_pos (by linarith)
  set c₁ : ℝ := (κ / M₁) ^ e / 2 with hc₁def
  set c₂ : ℝ := (κ * 2 ^ α / (2 * L)) ^ e with hc₂def
  have h2α : 0 < (2:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hc₁pos : 0 < c₁ := by
    rw [hc₁def]; exact div_pos (Real.rpow_pos_of_pos (div_pos hκ hM₁pos) e) (by norm_num)
  have hc₂pos : 0 < c₂ := by
    rw [hc₂def]; exact Real.rpow_pos_of_pos (div_pos (mul_pos hκ h2α) (by linarith)) e
  set X : ℝ := min (min ρ r₁) (min (ε / L) (min c₁ c₂)) with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    exact lt_min (lt_min hρ hr₁) (lt_min (div_pos hε hLpos) (lt_min hc₁pos hc₂pos))
  set δ : ℝ := X / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδρ : δ < ρ := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ ρ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδr₁ : δ ≤ r₁ := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ r₁ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hδr₁' : δ < r₁ := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ r₁ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hδε : δ ≤ ε / L := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ ε/L :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδc₁ : δ ≤ c₁ := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ c₁ :=
      le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
    linarith
  have hδc₂ : δ ≤ c₂ := by
    rw [hδdef, hXdef]
    have : min (min ρ r₁) (min (ε/L) (min c₁ c₂)) ≤ c₂ :=
      le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)
    linarith
  set b : ℂ → ℂ := fun w => (bumpC (w / δ) : ℂ) with hbdef
  set μ : ℂ → ℂ := fun z => (bumpC (z / δ) : ℂ) * μ₀ z with hμdef
  have hLδ : L * δ ≤ ε := by
    have h := mul_le_mul_of_nonneg_left hδε (le_of_lt hLpos)
    rwa [mul_div_cancel₀ ε (ne_of_gt hLpos)] at h
  have hμ₀_lip : ∀ x ∈ Metric.ball (0:ℂ) r₁, ∀ y ∈ Metric.ball 0 r₁,
      ‖μ₀ x - μ₀ y‖ ≤ K * ‖x - y‖ := by
    intro x hx y hy
    have h := (hKt.mono hr₁t).dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm, ← hKdef] at h
    exact h
  have hμ₀_bound : ∀ z ∈ Metric.ball (0:ℂ) r₁, ‖μ₀ z‖ ≤ K * ‖z‖ := by
    intro z hz
    have h := hμ₀_lip z hz 0 (by simpa using hr₁)
    simpa [h0, sub_zero] using h
  have hb_lip : ∀ x y : ℂ, ‖b x - b y‖ ≤ (Cb/δ) * ‖x - y‖ := by
    intro x y
    have h := hβlip.dist_le_mul (x/δ) (y/δ)
    rw [dist_eq_norm, dist_eq_norm] at h
    have hsub : x / δ - y / δ = (x - y) / δ := by ring
    rw [hsub, norm_div, hcoe δ, abs_of_nonneg (le_of_lt hδpos), ← hCbdef] at h
    have h2 : Cb * (‖x - y‖ / δ) = (Cb / δ) * ‖x - y‖ := by ring
    linarith [h, h2]
  have hμzero : ∀ z, δ ≤ ‖z‖ → μ z = 0 := by
    intro z hz
    have hz' : 1 ≤ ‖z / δ‖ := by
      rw [norm_div, hcoe δ, abs_of_nonneg (le_of_lt hδpos), le_div_iff₀ hδpos]
      linarith
    show (bumpC (z / δ) : ℂ) * μ₀ z = 0
    rw [bumpC_eq_zero hz']
    simp
  have hagree : ∀ z, ‖z‖ < δ / 2 → μ z = μ₀ z := by
    intro z hz
    have hz' : ‖z / δ‖ ≤ 1 / 2 := by
      rw [norm_div, hcoe δ, abs_of_nonneg (le_of_lt hδpos), div_le_iff₀ hδpos]
      linarith
    show (bumpC (z / δ) : ℂ) * μ₀ z = μ₀ z
    rw [bumpC_eq_one hz']
    simp
  have hbs : ContDiff ℝ ∞ b := by
    rw [hbdef]
    have h1 : ContDiff ℝ ∞ (fun z : ℂ => z / δ) :=
      (contDiff_id : ContDiff ℝ ∞ (id : ℂ → ℂ)).div_const (δ : ℂ)
    simpa [Function.comp_def] using hβs.comp h1
  have hμbound' : ∀ z, ‖μ z‖ ≤ L * δ := by
    intro z
    by_cases hz : ‖z‖ < δ
    · have hzr₁ : z ∈ Metric.ball (0:ℂ) r₁ := by
        rw [Metric.mem_ball, dist_zero_right]; linarith
      have hb1 : ‖(bumpC (z / δ) : ℂ)‖ ≤ 1 := by
        rw [hcoe, abs_of_nonneg (bumpC_nonneg _)]; exact bumpC_le_one _
      have h1 : ‖μ z‖ ≤ 1 * (K * ‖z‖) := by
        rw [hμdef]
        show ‖(fun z => (bumpC (z / δ) : ℂ) * μ₀ z) z‖ ≤ 1 * (K * ‖z‖)
        rw [norm_mul]
        exact mul_le_mul hb1 (hμ₀_bound z hzr₁) (norm_nonneg _) (by norm_num)
      have h2 : K * ‖z‖ ≤ L * δ := by nlinarith [hK0, hLK, le_of_lt hz, hLpos]
      linarith
    · rw [hμzero z (le_of_not_gt hz)]
      simp only [norm_zero]
      exact mul_nonneg (le_of_lt hLpos) (le_of_lt hδpos)
  have hμb : ∀ z, ‖μ z‖ ≤ ε := by
    intro z
    have h1 := hμbound' z
    linarith [hLδ]
  have hμderiv : ∀ z : ℂ, ‖fderiv ℝ μ z‖ ≤ M₁ := by
    intro z
    by_cases hz : ‖z‖ ≤ δ
    · have hzr₁ : z ∈ Metric.ball (0:ℂ) r₁ := by rw [Metric.mem_ball, dist_zero_right]; linarith
      have hzρ : z ∈ Metric.ball (0:ℂ) ρ := by rw [Metric.mem_ball, dist_zero_right]; linarith
      have hμ₀d : DifferentiableAt ℝ μ₀ z :=
        (hμ.contDiffAt (Metric.isOpen_ball.mem_nhds hzρ)).differentiableAt (by simp)
      have hbd : DifferentiableAt ℝ b z := (hbs.contDiffAt).differentiableAt (by simp)
      have hfd : fderiv ℝ μ z = fderiv ℝ (b * μ₀) z := by
        rw [hμdef]
        apply congrArg (fun g => fderiv ℝ g z)
        funext w
        simp [hbdef, Pi.mul_apply]
      rw [hfd, fderiv_mul hbd hμ₀d]
      have hb1 : ‖b z‖ ≤ 1 := by
        rw [hbdef]; show ‖(bumpC (z / δ) : ℂ)‖ ≤ 1
        rw [hcoe, abs_of_nonneg (bumpC_nonneg _)]; exact bumpC_le_one _
      have h2 : ‖fderiv ℝ μ₀ z‖ ≤ K := by
        have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hzr₁) (hKt.mono hr₁t)
        rwa [← hKdef] at this
      have h3 : ‖b z • fderiv ℝ μ₀ z‖ ≤ K := by
        rw [norm_smul]
        calc ‖b z‖ * ‖fderiv ℝ μ₀ z‖ ≤ 1 * K := mul_le_mul hb1 h2 (norm_nonneg _) (by norm_num)
          _ = K := one_mul K
      have h5 : ‖fderiv ℝ b z‖ ≤ Cb/δ :=
        norm_fderiv_le_of_lip' ℝ (by positivity) (Filter.Eventually.of_forall (fun w => hb_lip w z))
      have h4 : ‖μ₀ z‖ ≤ K * δ := by
        have := hμ₀_bound z hzr₁; nlinarith [hK0, hz]
      have h6 : ‖μ₀ z • fderiv ℝ b z‖ ≤ K * Cb := by
        rw [norm_smul]
        have h7 : ‖μ₀ z‖ * ‖fderiv ℝ b z‖ ≤ (K * δ) * (Cb / δ) :=
          mul_le_mul h4 h5 (norm_nonneg _) (by positivity)
        have h8 : (K * δ) * (Cb / δ) = K * Cb := by field_simp
        linarith [h7, h8]
      calc ‖b z • fderiv ℝ μ₀ z + μ₀ z • fderiv ℝ b z‖
          ≤ ‖b z • fderiv ℝ μ₀ z‖ + ‖μ₀ z • fderiv ℝ b z‖ := norm_add_le _ _
        _ ≤ K + K * Cb := add_le_add h3 h6
        _ = K * (1 + Cb) := by ring
        _ ≤ L * (1 + Cb) := mul_le_mul_of_nonneg_right hLK (by linarith)
        _ = M₁ := by rw [hM₁def]; ring
    · have hzgt : δ < ‖z‖ := lt_of_not_ge hz
      have hopen : IsOpen {w : ℂ | δ < ‖w‖} := isOpen_lt continuous_const continuous_norm
      have hev : μ =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen.mem_nhds hzgt] with w hw
        exact hμzero w (le_of_lt hw)
      have h0' : fderiv ℝ μ z = 0 := by
        rw [hev.fderiv_eq]
        exact fderiv_const_apply (0 : ℂ)
      rw [h0']
      simp only [norm_zero]
      linarith [hM₁pos]
  have hμs : ContDiff ℝ ∞ μ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hzδ : ‖z‖ ≤ δ
    · have hzρ : z ∈ Metric.ball (0:ℂ) ρ := by rw [Metric.mem_ball, dist_zero_right]; linarith
      have h1 : ContDiffAt ℝ ∞ μ₀ z := hμ.contDiffAt (Metric.isOpen_ball.mem_nhds hzρ)
      have h2 : ContDiffAt ℝ ∞ b z := hbs.contDiffAt
      rw [hμdef]
      exact h2.mul h1
    · have hzgt : δ < ‖z‖ := lt_of_not_ge hzδ
      have hopen : IsOpen {w : ℂ | δ < ‖w‖} := isOpen_lt continuous_const continuous_norm
      have hev : (fun z => (bumpC (z / δ) : ℂ) * μ₀ z) =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen.mem_nhds hzgt] with w hw
        have := hμzero w (le_of_lt hw)
        rw [hμdef] at this
        exact this
      rw [hμdef]
      exact (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq hev
  have hμc : HasCompactSupport μ := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 δ) (fun w hw => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    push Not at hw
    exact hμzero w (le_of_lt hw)
  have hμ_lip : ∀ x y : ℂ, ‖μ x - μ y‖ ≤ M₁ * ‖x - y‖ := by
    intro x y
    have hdiff : ∀ z ∈ (Set.univ : Set ℂ), DifferentiableAt ℝ μ z :=
      fun z _ => hμs.differentiable (by simp) |>.differentiableAt
    have hbnd : ∀ z ∈ (Set.univ : Set ℂ), ‖fderiv ℝ μ z‖ ≤ M₁ := fun z _ => hμderiv z
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbnd convex_univ
      (Set.mem_univ y) (Set.mem_univ x)
    simpa using h
  have hfar : 2 * (L * δ) ≤ κ * (2 * δ) ^ α := by
    have hpos : 0 < κ * 2 ^ α / (2 * L) := div_pos (mul_pos hκ h2α) (by linarith)
    have hδ' : δ ≤ (κ * 2 ^ α / (2 * L)) ^ e := by rw [← hc₂def]; exact hδc₂
    have h1 : δ ^ (1 - α) ≤ κ * 2 ^ α / (2 * L) := by
      calc δ ^ (1 - α) ≤ ((κ * 2 ^ α / (2 * L)) ^ e) ^ (1 - α) :=
            Real.rpow_le_rpow (le_of_lt hδpos) hδ' (by linarith)
        _ = (κ * 2 ^ α / (2 * L)) ^ (e * (1 - α)) := (Real.rpow_mul (le_of_lt hpos) e (1 - α)).symm
        _ = (κ * 2 ^ α / (2 * L)) ^ (1:ℝ) := by congr 1; rw [hedef, div_mul_cancel₀ 1 hden]
        _ = κ * 2 ^ α / (2 * L) := Real.rpow_one _
    have h2 : 2 * L * δ ^ (1 - α) ≤ κ * 2 ^ α := by
      have h := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * L)
      rwa [mul_div_cancel₀ _ (ne_of_gt (by linarith : (0:ℝ) < 2 * L))] at h
    have h3 : (2 * L * δ ^ (1 - α)) * δ ^ α ≤ (κ * 2 ^ α) * δ ^ α :=
      mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hδpos) α)
    have h4 : (2 * L * δ ^ (1 - α)) * δ ^ α = 2 * L * δ := by
      rw [mul_assoc, ← Real.rpow_add hδpos, show (1 - α) + α = 1 by ring, Real.rpow_one]
    have h5 : (κ * 2 ^ α) * δ ^ α = κ * (2 * δ) ^ α := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt hδpos)]; ring
    rw [h4, h5] at h3
    linarith [h3]
  refine ⟨δ, μ, hδpos, hδρ, hμs, hμc, hμzero, hagree, hμb, ?_⟩
  intro x y
  by_cases hxy : ‖x - y‖ ≤ 2 * δ
  · by_cases ht : ‖x - y‖ = 0
    · have h0' : ‖μ x - μ y‖ = 0 := by
        have h := hμ_lip x y
        rw [ht, mul_zero] at h
        exact le_antisymm h (norm_nonneg _)
      rw [ht, Real.zero_rpow (ne_of_gt hα), mul_zero]
      exact le_of_eq h0'
    · have htpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht)
      have h2 : ‖x - y‖ ^ (1 - α) ≤ (2 * δ) ^ (1 - α) :=
        Real.rpow_le_rpow (norm_nonneg _) hxy (by linarith)
      have h3 : (2 * δ) ^ (1 - α) ≤ κ / M₁ := by
        have hδ'' : 2 * δ ≤ (κ / M₁) ^ e := by
          rw [hc₁def] at hδc₁; linarith
        calc (2 * δ) ^ (1 - α) ≤ ((κ / M₁) ^ e) ^ (1 - α) :=
              Real.rpow_le_rpow (by positivity) hδ'' (by linarith)
          _ = (κ / M₁) ^ (e * (1 - α)) := (Real.rpow_mul (le_of_lt (div_pos hκ hM₁pos)) e (1 - α)).symm
          _ = (κ / M₁) ^ (1:ℝ) := by congr 1; rw [hedef, div_mul_cancel₀ 1 hden]
          _ = κ / M₁ := Real.rpow_one _
      have hsplit : ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
        rw [← Real.rpow_add htpos]; norm_num
      calc ‖μ x - μ y‖ ≤ M₁ * ‖x - y‖ := hμ_lip x y
        _ = M₁ * (‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α) := congrArg (fun t => M₁ * t) hsplit
        _ ≤ M₁ * ((κ / M₁) * ‖x - y‖ ^ α) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hM₁pos)
              exact mul_le_mul_of_nonneg_right (le_trans h2 h3) (Real.rpow_nonneg (norm_nonneg _) α)
        _ = κ * ‖x - y‖ ^ α := by field_simp
  · push Not at hxy
    have hsup : ‖μ x - μ y‖ ≤ 2 * (L * δ) := by
      have hx := hμbound' x
      have hy := hμbound' y
      calc ‖μ x - μ y‖ ≤ ‖μ x‖ + ‖μ y‖ := norm_sub_le _ _
        _ ≤ 2 * (L * δ) := by linarith
    have h2 : (2 * δ) ^ α ≤ ‖x - y‖ ^ α :=
      Real.rpow_le_rpow (by positivity) (le_of_lt hxy) (le_of_lt hα)
    have h3 : κ * (2 * δ) ^ α ≤ κ * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left h2 (le_of_lt hκ)
    linarith [hsup, hfar, h3]

end Work.Beltrami
