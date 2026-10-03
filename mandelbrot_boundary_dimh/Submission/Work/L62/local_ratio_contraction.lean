import Mathlib
import Submission.Work.L62.holomorphic_second_order_remainder
import Submission.Work.L62.deriv_lipschitz_of_second_order

/-!
# `Work.L62.local_ratio_contraction`

Shishikura, Lemma 6.2 (local part), in the abstract form used by `Work.L62.l62c`: a
`β`-family of holomorphic self-maps `H β` of an open `Ω ∋ 0`, each fixing `0` with multiplier
of norm in `[lam0, lam1]`, `lam1 < 1`, jointly continuous on `Λ ×ˢ Ω` with `Λ` compact, is
*uniformly* contracting on a small ball around `0`, and the ratio `H β u / (deriv (H β) u * u)`
is uniformly `1 + O(‖u‖)` there.

The uniformity in `β` is the only non-trivial point: it comes from a uniform bound `M` on
`‖H β z‖` for `(β, z) ∈ Λ × closedBall 0 R` (compactness of `Λ` + joint continuity), which
turns Cauchy's integral formula into the second order estimate of
`Work.L62.holomorphic_second_order_remainder` with constants independent of `β`.
-/

namespace Work.L62

theorem local_ratio_contraction {Ω Λ : Set ℂ} {H : ℂ → ℂ → ℂ} {lam0 lam1 : ℝ}
    (hΩo : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω) (hΛc : IsCompact Λ)
    (hlam0 : 0 < lam0) (hlam1 : lam1 < 1)
    (hlam : ∀ β ∈ Λ, lam0 ≤ ‖deriv (H β) 0‖ ∧ ‖deriv (H β) 0‖ ≤ lam1)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hfix : ∀ β ∈ Λ, H β 0 = 0)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω)) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ Ω ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ < 1 ∧
      (∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ ρ → ‖H β u‖ ≤ μ * ‖u‖) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ β ∈ Λ, ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ ρ →
        ‖deriv (H β) u * u / (H β u) - 1‖ ≤ L * ‖u‖ := by
  classical
  -- ## Step 1: a disc of radius `R` around `0` contained in `Ω`.
  obtain ⟨r, hr0, hrΩ⟩ := Metric.isOpen_iff.mp hΩo 0 h0
  set R : ℝ := r / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRsub : Metric.closedBall (0 : ℂ) R ⊆ Ω := by
    intro z hz
    refine hrΩ ?_
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    rw [hRdef] at h1
    linarith
  -- ## Step 2: the uniform bound `M` on `Λ × closedBall 0 R`.
  have hcomp : IsCompact (Λ ×ˢ Metric.closedBall (0 : ℂ) R) :=
    hΛc.prod (isCompact_closedBall 0 R)
  have hcontR : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2)
      (Λ ×ˢ Metric.closedBall (0 : ℂ) R) :=
    hcont.mono (Set.prod_mono_right hRsub)
  obtain ⟨M₀, hM₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp (hcomp.image_of_continuousOn hcontR).isBounded
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMbound : ∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ R → ‖H β u‖ ≤ M := by
    intro β hβ u hu
    have hmem : H β u ∈ (fun p : ℂ × ℂ => H p.1 p.2) '' (Λ ×ˢ Metric.closedBall (0 : ℂ) R) :=
      ⟨(β, u), by
        rw [Set.mem_prod]
        exact ⟨hβ, by rwa [Metric.mem_closedBall, dist_zero_right]⟩, rfl⟩
    have h1 : ‖H β u‖ ≤ M₀ := by
      have h := hM₀ hmem
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    exact le_trans h1 (by rw [hMdef]; exact le_max_left _ _)
  have hR2pos : 0 < R ^ 2 := by positivity
  -- ## Step 3: the numerical constants.
  set μ : ℝ := (1 + max lam1 0) / 2 with hμdef
  have hμ0 : 0 ≤ μ := by rw [hμdef]; have := le_max_right lam1 0; linarith
  have hμ1 : μ < 1 := by rw [hμdef]; have := max_lt hlam1 zero_lt_one; linarith
  have hμgt : lam1 < μ := by
    rw [hμdef]
    rcases le_total 0 lam1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  set B : ℝ := 16 * M / R ^ 2 + 1 with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    have h : 0 ≤ 16 * M / R ^ 2 := div_nonneg (by linarith) (le_of_lt hR2pos)
    linarith
  have hBM2 : 2 * M / R ^ 2 ≤ B := by
    rw [hBdef]
    have h : 2 * M / R ^ 2 ≤ 16 * M / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hR2pos)
      linarith
    linarith
  have hBM16 : 16 * M / R ^ 2 ≤ B := by rw [hBdef]; linarith
  set ρ : ℝ := min (R / 4) (min ((μ - lam1) / B) (lam0 / (2 * B))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    refine lt_min (by linarith) (lt_min ?_ ?_)
    · exact div_pos (by linarith) hBpos
    · exact div_pos hlam0 (by linarith)
  have hρR : ρ ≤ R / 4 := by rw [hρdef]; exact min_le_left _ _
  have hρμ : ρ ≤ (μ - lam1) / B := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρlam : ρ ≤ lam0 / (2 * B) := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- ## Step 4: the two conclusions.
  have hballΩ : Metric.ball (0 : ℂ) ρ ⊆ Ω := by
    intro z hz
    refine hRsub (Metric.closedBall_subset_closedBall ?_ (Metric.ball_subset_closedBall hz))
    linarith
  have hcontr : ∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ ρ → ‖H β u‖ ≤ μ * ‖u‖ := by
    intro β hβ u hu
    have huR : ‖u‖ ≤ R / 2 := le_trans hu (by linarith)
    have hfβ : DifferentiableOn ℂ (H β) (Metric.closedBall (0 : ℂ) R) :=
      (hHdiff β hβ).mono hRsub
    have hMβ : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖H β z‖ ≤ M := by
      intro z hz
      have hz' : ‖z‖ = R := by
        have h := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm, sub_zero] at h
      exact hMbound β hβ z (le_of_eq hz')
    have hrem := _root_.Work.L62.holomorphic_second_order_remainder hRpos hM0 hfβ hMβ u (by simpa using huR)
    have hrem' : ‖H β u - deriv (H β) 0 * u‖ ≤ (2 * M / R ^ 2) * ‖u‖ ^ 2 := by
      simpa [hfix β hβ, sub_zero] using hrem
    have hsplit : ‖H β u‖ ≤ ‖H β u - deriv (H β) 0 * u‖ + ‖deriv (H β) 0 * u‖ := by
      calc ‖H β u‖ = ‖(H β u - deriv (H β) 0 * u) + deriv (H β) 0 * u‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hlin : ‖deriv (H β) 0 * u‖ ≤ lam1 * ‖u‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hlam β hβ).2 (norm_nonneg u)
    have hstep : ‖H β u‖ ≤ (2 * M / R ^ 2) * ‖u‖ ^ 2 + lam1 * ‖u‖ := by linarith
    have hsq : ‖u‖ ^ 2 = ‖u‖ * ‖u‖ := by ring
    have hBu : B * ‖u‖ ≤ μ - lam1 := by
      have h := (le_div_iff₀ hBpos).mp (le_trans hu hρμ)
      linarith
    have hkey : (2 * M / R ^ 2) * ‖u‖ ^ 2 ≤ B * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hBM2 (by positivity)
    calc ‖H β u‖ ≤ (2 * M / R ^ 2) * ‖u‖ ^ 2 + lam1 * ‖u‖ := hstep
      _ ≤ B * ‖u‖ ^ 2 + lam1 * ‖u‖ := by linarith
      _ = (B * ‖u‖ + lam1) * ‖u‖ := by ring
      _ ≤ μ * ‖u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
          linarith
  have hL0 : 0 ≤ 4 * B / lam0 := by positivity
  have hL : ∀ β ∈ Λ, ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ ρ →
      ‖deriv (H β) u * u / (H β u) - 1‖ ≤ (4 * B / lam0) * ‖u‖ := by
    intro β hβ u hu0 hu
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have huR2 : ‖u‖ ≤ R / 2 := le_trans hu (by linarith)
    have huR4 : ‖u‖ ≤ R / 4 := le_trans hu hρR
    have hfβ : DifferentiableOn ℂ (H β) (Metric.closedBall (0 : ℂ) R) :=
      (hHdiff β hβ).mono hRsub
    have hMβ : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖H β z‖ ≤ M := by
      intro z hz
      have hz' : ‖z‖ = R := by
        have h := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm, sub_zero] at h
      exact hMbound β hβ z (le_of_eq hz')
    have hK0 : 0 ≤ 2 * M / R ^ 2 := div_nonneg (by linarith) (le_of_lt hR2pos)
    have h2 : ∀ v : ℂ, ‖v - 0‖ ≤ R / 2 →
        ‖H β v - H β 0 - deriv (H β) 0 * (v - 0)‖ ≤ (2 * M / R ^ 2) * ‖v - 0‖ ^ 2 :=
      fun v hv => _root_.Work.L62.holomorphic_second_order_remainder hRpos hM0 hfβ hMβ v (by simpa using hv)
    have hder := _root_.Work.L62.deriv_lipschitz_of_second_order hRpos hK0 hfβ h2 u (by simpa using huR4)
    have hder' : ‖deriv (H β) u - deriv (H β) 0‖ ≤ (16 * M / R ^ 2) * ‖u‖ := by
      have h1 : (8 * (2 * M / R ^ 2)) * ‖u - 0‖ = (16 * M / R ^ 2) * ‖u‖ := by
        rw [sub_zero]; ring
      rwa [h1] at hder
    have hrec : ‖H β u - deriv (H β) 0 * u‖ ≤ (2 * M / R ^ 2) * ‖u‖ ^ 2 := by
      simpa [hfix β hβ, sub_zero] using
        _root_.Work.L62.holomorphic_second_order_remainder hRpos hM0 hfβ hMβ u (by simpa using huR2)
    -- lower bound for `‖H β u‖`
    have hlow : (lam0 / 2) * ‖u‖ ≤ ‖H β u‖ := by
      have h2' : lam0 * ‖u‖ ≤ ‖deriv (H β) 0 * u‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hlam β hβ).1 (norm_nonneg u)
      have h3 : ‖deriv (H β) 0 * u‖ - ‖H β u - deriv (H β) 0 * u‖ ≤ ‖H β u‖ := by
        have h4 := (abs_le.mp (abs_norm_sub_norm_le (deriv (H β) 0 * u) (H β u))).2
        rw [norm_sub_rev] at h4
        linarith
      have h5 : (2 * M / R ^ 2) * ‖u‖ ^ 2 ≤ (lam0 / 2) * ‖u‖ := by
        have hBu : B * ‖u‖ ≤ lam0 / 2 := by
          have h := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * B)).mp (le_trans hu hρlam)
          linarith
        have h5a : (2 * M / R ^ 2) * ‖u‖ ≤ B * ‖u‖ :=
          mul_le_mul_of_nonneg_right hBM2 (norm_nonneg u)
        nlinarith [h5a, hBu, hupos, norm_nonneg u, sq_nonneg ‖u‖]
      linarith
    have hbne : H β u ≠ 0 := by
      intro hzero
      have hzero' : ‖H β u‖ = 0 := by rw [hzero, norm_zero]
      have := hlow
      rw [hzero'] at this
      nlinarith [hlam0, hupos]
    -- upper bound for the numerator `deriv (H β) u * u - H β u`
    have hnum : ‖deriv (H β) u * u - H β u‖ ≤ (2 * B) * ‖u‖ ^ 2 := by
      have hsplit : deriv (H β) u * u - H β u
          = (deriv (H β) u - deriv (H β) 0) * u + (deriv (H β) 0 * u - H β u) := by ring
      rw [hsplit]
      have h1 : ‖(deriv (H β) u - deriv (H β) 0) * u‖ ≤ (16 * M / R ^ 2) * ‖u‖ ^ 2 := by
        rw [norm_mul]
        calc ‖deriv (H β) u - deriv (H β) 0‖ * ‖u‖
            ≤ ((16 * M / R ^ 2) * ‖u‖) * ‖u‖ :=
              mul_le_mul_of_nonneg_right hder' (norm_nonneg u)
          _ = (16 * M / R ^ 2) * ‖u‖ ^ 2 := by ring
      have h2 : ‖deriv (H β) 0 * u - H β u‖ ≤ (2 * M / R ^ 2) * ‖u‖ ^ 2 := by
        rw [norm_sub_rev]; exact hrec
      have hsum : (16 * M / R ^ 2) * ‖u‖ ^ 2 + (2 * M / R ^ 2) * ‖u‖ ^ 2
          ≤ (2 * B) * ‖u‖ ^ 2 := by
        have hB2 : (16 * M / R ^ 2) + (2 * M / R ^ 2) ≤ 2 * B := by linarith
        have hnn : 0 ≤ ‖u‖ ^ 2 := by positivity
        nlinarith [hB2, hnn]
      calc ‖(deriv (H β) u - deriv (H β) 0) * u + (deriv (H β) 0 * u - H β u)‖
          ≤ ‖(deriv (H β) u - deriv (H β) 0) * u‖ + ‖deriv (H β) 0 * u - H β u‖ :=
            norm_add_le _ _
        _ ≤ (2 * B) * ‖u‖ ^ 2 := by linarith
    have hdiveq : deriv (H β) u * u / (H β u) - 1
        = (deriv (H β) u * u - H β u) / (H β u) := div_sub_one hbne
    rw [hdiveq, norm_div]
    have hlowpos : 0 < (lam0 / 2) * ‖u‖ := by nlinarith [hlam0, hupos]
    calc ‖deriv (H β) u * u - H β u‖ / ‖H β u‖
        ≤ (2 * B * ‖u‖ ^ 2) / ((lam0 / 2) * ‖u‖) :=
          div_le_div₀ (by positivity) hnum hlowpos hlow
      _ = (4 * B / lam0) * ‖u‖ := by
          field_simp
          ring
  exact ⟨ρ, hρpos, hballΩ, μ, hμ0, hμ1, hcontr, 4 * B / lam0, hL0, hL⟩

end Work.L62
