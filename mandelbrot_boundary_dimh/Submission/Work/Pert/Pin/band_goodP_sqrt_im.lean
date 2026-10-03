import Mathlib
import Submission.Work.Pert.Pin.band_goodP_sqrt

namespace Work.Pert.Pin

set_option maxHeartbeats 8000000

/-- **`Work.Pert.Pin.band_goodP_sqrt` with the two trap hypotheses restricted to the actual walk
point** (`v.im = w.im`): the caller can only produce the trap tube around `d.φ (v₀ + j)` for the walk
point `v₀ = uw M Tb w` (satisfying `v.im = w.im`), not for all `v ∈ Dstrip M Tb`.  Copy the (already
complete) proof of `band_goodP_sqrt` and insert the extra argument `hv₀im` at its three call sites;
see `Submission/Work/Pert/Pin/NOTES_band_goodP_sqrt_im.md`.  (`{w : ℂ}` is declared earlier here so
that `hLlip`/`hLtrap` can mention it.) -/
theorem band_goodP_sqrt_im
    {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ rr y₁ Tb M Xdev Cdev Cseed Camp Csm r₀ δ₀ E ηd δd R Lf mρ C₂ : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hy₁ : d.η₀ < y₁) (hy₁Tb : y₁ ≤ Tb) (hTb0 : 0 ≤ Tb)
    (hXdev0 : 0 ≤ Xdev) (hCdev : 0 < Cdev) (hCseed : 0 < Cseed) (hCseed1 : 1 ≤ Cseed)
    (hCamp1 : 1 ≤ Camp) (hLf1 : 1 ≤ Lf) (hRpos : 0 < R) (hR4 : R ≤ 4)
    (hr₀ : 0 < r₀) (hCsm : 0 < Csm) (hmρ : 0 < mρ) (hmρr₀ : mρ ≤ r₀) (hmρrr : mρ ≤ rr)
    (hM8 : 8 ≤ M) (hMΞ : 8 * Ξ + 8 ≤ M) (hTbM : Tb ≤ M / 160) (hXdevM : Xdev ≤ M / 320)
    (hXc40 : 2 * Xdev + 1 + Tb < M / 40) (hXc80 : 2 * Xdev + 1 + Tb + Xdev < M / 80)
    (hXc8 : Xdev + (1 + Tb) + Xdev ≤ M / 8)
    (hCampTb : Camp * (1 + Tb) ≤ M) (hCdevM : Cdev ≤ M / 80) (hC₂M : 64 * C₂ ≤ M)
    {R₁ : ℝ} (hR₁M : R₁ ≤ M / 8)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hE : 0 ≤ E) (hδ₀ : 0 < δ₀) (hηd : 0 < ηd) (hδd : 0 < δd)
    (hδ₀2 : 2 * δ₀ ≤ mρ)
    (hδ₀α : Csm * δ₀ / mρ
      ≤ min (min (1 / (32 * (M + 2))) (R / (24 * Cseed * Camp * M * M))) ηd)
    (hδ₀u : Csm * (δ₀ / mρ ^ 2 + δ₀ / (mρ * rr))
      ≤ min (1 / 4) (min ηd (R / (24 * Cseed * Camp * M))))
    (hdevcov : (3 / 2) * Xdev + (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb) < M / 32)
    (hdevR : Cseed * (2 * ((Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb)) / (M * M))
      ≤ R / (12 * Camp * M * M))
    (hδ₀δd : δ₀ ≤ δd)
    (hδ₀trap : δ₀ * ((⌈M⌉₊ + 2 : ℕ) : ℝ) * Lf ^ (⌈M⌉₊ + 2) ≤ R / 4)
    (hsmallA : ∀ {f : ℂ → ℂ} {Df : Set ℂ} {ρ δ : ℝ} {u : ℂ → ℂ} {σ : ℂ},
      0 < ρ → ρ ≤ r₀ → 0 < δ → 2 * δ ≤ ρ → 0 < rr →
      MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      ‖u 0 - 1‖ ≤ Csm * (δ / ρ ^ 2 + δ / (ρ * rr)) ∧ ‖σ‖ ≤ Csm * δ / ρ ∧
        ‖MandelDim.rotOf f‖ ≤ Csm * δ / ρ)
    (hdevA : ∀ {F F₀ Φ Φ₀ : ℂ → ℂ} {c : ℂ} {R' E' : ℝ}, Cdev ≤ R' → 0 ≤ E' →
      DifferentiableOn ℂ F (Metric.ball c (2 * R')) →
      DifferentiableOn ℂ F₀ (Metric.ball c (2 * R')) →
      MandelDim.IsFatouCoordOn F Φ (Metric.ball c (2 * R')) →
      MandelDim.IsFatouCoordOn F₀ Φ₀ (Metric.ball c (2 * R')) →
      (∀ w ∈ Metric.ball c (2 * R'), ‖F w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c (2 * R'), ‖F₀ w - (w + 1)‖ < 1 / 4) →
      (∀ w ∈ Metric.ball c (2 * R'), ‖F w - F₀ w‖ ≤ E') → Φ c = Φ₀ c →
      ∀ z ∈ Metric.ball c R', ‖Φ z - Φ₀ z‖ ≤ (Cdev / R' + 4 * E') * ‖z - c‖)
    (hseedA : ∀ {u : ℂ → ℂ} {σ α ς y : ℂ} {M' dev : ℝ}, 0 < M' → 1 ≤ M' → 0 ≤ dev →
      M' / 2 ≤ ‖ς‖ → M' / 2 ≤ ‖y‖ → ‖ς - y‖ ≤ 2 * dev → 2 * Real.pi * ‖α‖ * ‖ς‖ ≤ 1 / 2 →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) → α ≠ 0 →
      ‖u 0 - 1‖ ≤ 1 / 4 → ‖α‖ ≤ 1 / 4 →
      ‖Work.Pert.tauC σ α ς - MandelDim.tau0 y‖
        ≤ Cseed * (dev / (M' * M') + ‖u 0 - 1‖ / M' + ‖α‖))
    (hampA : ∀ M' Tb', Camp * (1 + Tb') ≤ M' → y₁ ≤ Tb' →
      ∀ w : ℂ, |w.re| ≤ 1 → y₁ ≤ |w.im| → |w.im| ≤ Tb' →
      ∀ u : ℂ, u ∈ Work.Pert.Dstrip M' Tb' → ∀ n : ℕ, u + (n : ℂ) = w → ∀ k : ℕ, k ≤ n →
        ∀ z : ℂ, ‖z - d.φ u‖ < 1 / (Camp * M' * M') →
          ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ Camp * M' * M' * ‖z - d.φ u‖)
    {Φ₀ : ℂ → ℂ}
    (hΦ₀ : MandelDim.IsFatouCoordOn (Work.Pert.F0f f₀) Φ₀
      (Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40)))
    (hΦ₀inv : ∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
      Work.Pert.Xc d (Φ₀ ζ) = ζ)
    (hΦ₀dev : ∀ ζ ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
      ‖Φ₀ ζ - ζ‖ ≤ M / 40)
    (hΦ₀pin : Φ₀ (Work.Pert.Xc d (((-M : ℝ) : ℂ))) = (((-M : ℝ)) : ℂ))
    (hF0d : DifferentiableOn ℂ (Work.Pert.F0f f₀)
      (Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40)))
    (hF0nt : ∀ w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
      ‖Work.Pert.F0f f₀ w - (w + 1)‖ < 1 / 4)
    (hXcsv : ∀ v ∈ Work.Pert.Dstrip M Tb, ‖Work.Pert.Xc d v - v‖ ≤ Xdev)
    (hXcM : ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ ≤ Xdev)
    (hTaud : ∀ u ∈ Metric.ball (((-M : ℝ)) : ℂ) (M / 4),
      ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2)
    {Ld : Set ℂ}
    (hdefect : ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
      MandelDim.NearOn f₀ f Df Ld δd → f 0 = 0 → MandelDim.InF1 α → ‖α‖ ≤ ηd → 0 < rr →
      DifferentiableOn ℂ u (Metric.ball 0 rr) →
      (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
      (∀ w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
        Work.Pert.tauC σ α w ∈ Metric.ball 0 rr) →
      ‖u 0 - 1‖ ≤ ηd →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
      ∀ w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ) : ℂ))) (M / 40),
        ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ E)
    {w : ℂ} {L : Set ℂ} (hLdL : Ld ⊆ L) (hLrr : Metric.closedBall (0 : ℂ) rr ⊆ L)
    (hLlip : ∀ j : ℕ, j ≤ ⌈M⌉₊ + 2 → ∀ v ∈ Work.Pert.Dstrip M Tb, v.im = w.im →
      ∀ x y : ℂ, ‖x - d.φ (v + (j : ℂ))‖ ≤ R → ‖y - d.φ (v + (j : ℂ))‖ ≤ R →
        ‖f₀ x - f₀ y‖ ≤ Lf * ‖x - y‖)
    (hLtrap : ∀ j : ℕ, j ≤ ⌈M⌉₊ + 2 → ∀ v ∈ Work.Pert.Dstrip M Tb, v.im = w.im →
      Metric.closedBall (d.φ (v + (j : ℂ))) R ⊆ L)
    {f : ℂ → ℂ} {Df : Set ℂ} {u : ℂ → ℂ} {σ α : ℂ} {Φm : ℂ → ℂ}
    (hNear : MandelDim.NearOn f₀ f Df L δ₀) (hf0 : f 0 = 0)
    (hInF1 : MandelDim.InF1 (MandelDim.rotOf f)) (hα : α = MandelDim.rotOf f)
    (hud : DifferentiableOn ℂ u (Metric.ball 0 rr))
    (hub : ∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hform : ∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hpin : Φm (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ))
    (hre : |w.re| ≤ 1) (him1 : y₁ ≤ |w.im|) (him2 : |w.im| ≤ Tb) :
    Work.Pert.GoodP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) w := by
  -- ## 0. the smallness of the perturbation data
  have hMpos : 0 < M := by linarith
  have hNearρ : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) mρ) δ₀ :=
    ⟨hNear.1, fun z hz => hNear.2.1 (hLrr (Metric.closedBall_subset_closedBall hmρrr hz)),
      hNear.2.2.1,
      fun z hz => hNear.2.2.2 z (hLrr (Metric.closedBall_subset_closedBall hmρrr hz))⟩
  obtain ⟨hu0b, hσb, hαb⟩ :=
    hsmallA hmρ hmρr₀ hδ₀ hδ₀2 hrr hNearρ hf0 hud hub hform
  have hαle : ‖α‖ ≤ Csm * δ₀ / mρ := by rw [hα]; exact hαb
  have hα32 : ‖α‖ ≤ 1 / (32 * (M + 2)) :=
    le_trans hαle (le_trans hδ₀α (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hαR : ‖α‖ ≤ R / (24 * Cseed * Camp * M * M) :=
    le_trans hαle (le_trans hδ₀α (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hu0le : ‖u 0 - 1‖ ≤ Csm * (δ₀ / mρ ^ 2 + δ₀ / (mρ * rr)) := hu0b
  have hmid : ‖u 0 - 1‖ ≤ min (1 / 4) (min ηd (R / (24 * Cseed * Camp * M))) :=
    le_trans hu0le hδ₀u
  have hu0ηd : ‖u 0 - 1‖ ≤ ηd :=
    le_trans hmid (le_trans (min_le_right _ _) (min_le_left _ _))
  have hu0quarter : ‖u 0 - 1‖ ≤ 1 / 4 := le_trans hmid (min_le_left _ _)
  have hu0R : ‖u 0 - 1‖ ≤ R / (24 * Cseed * Camp * M) :=
    le_trans hmid (le_trans (min_le_right _ _) (min_le_right _ _))
  have hInF1α : MandelDim.InF1 α := by rw [hα]; exact hInF1
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hInF1α
    simp [MandelDim.InF1] at hInF1α
  have hαquarter : ‖α‖ ≤ 1 / 4 := by
    have h1 : 1 / (32 * (M + 2)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 32 * (M + 2)) (by norm_num : (0 : ℝ) < 4)]
      linarith
    linarith
  have hroom : 16 * (M + 2) ≤ (1 / α).re := by
    have h1 : 1 / (2 * ‖α‖) < (1 / α).re := Work.Pert.inv_re_lower hInF1α
    have h3 : ‖α‖ * (32 * (M + 2)) ≤ 1 :=
      (le_div_iff₀ (by linarith : (0 : ℝ) < 32 * (M + 2))).mp hα32
    have h2 : 16 * (M + 2) ≤ 1 / (2 * ‖α‖) := by
      have hna : 0 < ‖α‖ := norm_pos_iff.mpr hαne
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ‖α‖)]
      nlinarith [h3]
    exact le_of_lt (lt_of_le_of_lt h2 h1)
  have hXdev' : Xdev ≤ M / 320 := hXdevM
  have hXcM' : ‖Work.Pert.Xc d (((-M : ℝ)) : ℂ) - (((-M : ℝ)) : ℂ)‖ ≤ Xdev := hXcM
  -- ## 1. the gate geometry around the anchor and around the deep strip
  set c : ℂ := Work.Pert.Xc d (((-M : ℝ)) : ℂ) with hcdef
  have hΞle : Ξ ≤ M / 8 := by linarith
  have hcre₁ : c.re ≤ -M + Xdev := by
    have h1 : |(c - (((-M : ℝ)) : ℂ)).re| ≤ ‖c - (((-M : ℝ)) : ℂ)‖ :=
      Complex.abs_re_le_norm _
    have h2 : (c - (((-M : ℝ)) : ℂ)).re = c.re + M := by simp
    rw [h2] at h1
    have h3 := (abs_le.mp (le_trans h1 hXcM)).2
    linarith
  have hcre₂ : -M - Xdev ≤ c.re := by
    have h1 : |(c - (((-M : ℝ)) : ℂ)).re| ≤ ‖c - (((-M : ℝ)) : ℂ)‖ :=
      Complex.abs_re_le_norm _
    have h2 : (c - (((-M : ℝ)) : ℂ)).re = c.re + M := by simp
    rw [h2] at h1
    have h3 := (abs_le.mp (le_trans h1 hXcM)).1
    linarith
  have hballanc : Metric.ball c (M / 40) ⊆ Work.Pert.Qm Ξ α := by
    refine Work.Pert.Ksub2.ball_sub_Qm ?_ ?_
    · linarith
    · linarith
  have hQdu : ∀ u ∈ Work.Pert.Dstrip M Tb, Metric.ball u (M / 4) ⊆ Work.Pert.Qm Ξ α := by
    intro v hv
    refine Work.Pert.Ksub2.ball_sub_Qm ?_ ?_
    · have h1 : -M - 1 ≤ v.re := hv.1
      linarith
    · have h2 : v.re ≤ -M := hv.2.1
      linarith
  have hQmopen : IsOpen (Work.Pert.Qm Ξ α) := Work.Pert.isOpen_Qm' Ξ α
  -- ## 2. the data of the two maps on the anchor ball
  have hΦmanc : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Metric.ball c (M / 40)) :=
    ⟨hΦm.1.mono hballanc, hΦm.2.1.mono hballanc,
      fun z hz hFz => hΦm.2.2 z (hballanc hz) (hballanc hFz)⟩
  have hntF : ∀ w ∈ Metric.ball c (M / 40), ‖Work.Pert.liftF u σ α w - (w + 1)‖ < 1 / 4 := by
    intro w hw
    have h := (hNT.1.2 w (hballanc hw)).1
    linarith
  have hαηd : ‖α‖ ≤ ηd :=
    le_trans hαle (le_trans hδ₀α (min_le_right _ _))
  have hdef : ∀ w ∈ Metric.ball c (M / 40),
      ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ E := by
    intro w hw
    refine hdefect f Df u σ α ?_ hf0 hInF1α hαηd hrr hud hub hform ?_ hu0ηd hnorm w hw
    · exact ⟨hNear.1, fun z hz => hNear.2.1 (hLdL hz), hNear.2.2.1,
        fun z hz => lt_of_lt_of_le (hNear.2.2.2 z (hLdL hz)) hδ₀δd⟩
    · intro z hz
      exact hτQ z (hballanc hz)
  -- ## 3. the anchor inverts the curve on the deep strip
  have hΦ₀inv' : ∀ u ∈ Work.Pert.Dstrip M Tb, Φ₀ (Work.Pert.Xc d u) = u := by
    refine Work.Pert.Ksub2.Phi0_inv_on_Dstrip d hTaud hΦ₀inv ?_ ?_ ?_
    · intro v hv
      have h1 : ‖Work.Pert.Xc d v - v‖ ≤ Xdev := hXcsv v hv
      have h2 : ‖v - (((-M : ℝ)) : ℂ)‖ ≤ 1 + Tb := Work.Pert.Ksub2.norm_sub_negM_le hv
      refine mem_ball_of_norm_lt ?_
      have h8 := norm_Xc_sub_Xc_le d hv h1 h2 (by rw [← hcdef]; exact hXcM')
      rw [← hcdef] at h8
      have h9 : ‖Work.Pert.Xc d v - c‖ ≤ 2 * Xdev + 1 + Tb := by linarith [h8]
      linarith [h9, hXc40]
    · intro v hv
      have h2 : ‖v - (((-M : ℝ)) : ℂ)‖ ≤ 1 + Tb := Work.Pert.Ksub2.norm_sub_negM_le hv
      refine mem_ball_of_norm_lt ?_
      linarith [h2, hTbM]
    · intro v hv
      have h1 : ‖Work.Pert.Xc d v - v‖ ≤ Xdev := hXcsv v hv
      have h2 : ‖v - (((-M : ℝ)) : ℂ)‖ ≤ 1 + Tb := Work.Pert.Ksub2.norm_sub_negM_le hv
      have h3 : Work.Pert.Xc d v ∈ Metric.ball c (M / 40) := by
        refine mem_ball_of_norm_lt ?_
        have h8 := norm_Xc_sub_Xc_le d hv h1 h2 (by rw [← hcdef]; exact hXcM')
        rw [← hcdef] at h8
        have h9 : ‖Work.Pert.Xc d v - c‖ ≤ 2 * Xdev + 1 + Tb := by linarith [h8]
        linarith [h9, hXc40]
      have h5 := hΦ₀dev (Work.Pert.Xc d v) h3
      have h10 : ‖Φ₀ (Work.Pert.Xc d v) - (((-M : ℝ)) : ℂ)‖
          ≤ ‖Φ₀ (Work.Pert.Xc d v) - Work.Pert.Xc d v‖
            + ‖Work.Pert.Xc d v - (((-M : ℝ)) : ℂ)‖ := by
        have h11 := norm_add_le (Φ₀ (Work.Pert.Xc d v) - Work.Pert.Xc d v)
          (Work.Pert.Xc d v - (((-M : ℝ)) : ℂ))
        rw [sub_add_sub_cancel] at h11
        exact h11
      have h12 : ‖Work.Pert.Xc d v - (((-M : ℝ)) : ℂ)‖ ≤ Xdev + (1 + Tb) :=
        norm_Xc_sub_negM_le d hv h1 h2
      refine mem_ball_of_norm_lt ?_
      linarith [h5, h10, h12, hTbM, hXdev']
  -- ## 4. the deviation bound at the deep strip
  have hdevXc : ∀ u ∈ Work.Pert.Dstrip M Tb,
      ‖Φm (Work.Pert.Xc d u) - u‖ ≤ (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := by
    intro v hv
    have h1 : ‖Work.Pert.Xc d v - v‖ ≤ Xdev := hXcsv v hv
    have h2 : ‖v - (((-M : ℝ)) : ℂ)‖ ≤ 1 + Tb := Work.Pert.Ksub2.norm_sub_negM_le hv
    have hz : Work.Pert.Xc d v ∈ Metric.ball c (M / 80) := by
      refine mem_ball_of_norm_lt ?_
      have h8 := norm_Xc_sub_Xc_le d hv h1 h2 (by rw [← hcdef]; exact hXcM')
      rw [← hcdef] at h8
      have h9 : ‖Work.Pert.Xc d v - c‖ ≤ 2 * Xdev + 1 + Tb := by linarith [h8]
      linarith [h9, hXc80]
    have h2M : 2 * (M / 80) = M / 40 := by ring
    have hballanc' : Metric.ball c (2 * (M / 80)) ⊆ Work.Pert.Qm Ξ α := by
      rw [h2M]; exact hballanc
    have h1' := hdevA (F := fun z => Work.Pert.liftF u σ α z) (F₀ := Work.Pert.F0f f₀)
      (Φ := Φm) (Φ₀ := Φ₀) (c := c) (R' := M / 80) (E' := E)
      hCdevM hE (hNT.1.1.mono hballanc')
      (by rw [h2M]; exact hF0d)
      ⟨hΦm.1.mono hballanc', hΦm.2.1.mono hballanc',
        fun z hz hFz => hΦm.2.2 z (hballanc' hz) (hballanc' hFz)⟩
      (by rw [h2M]; exact hΦ₀)
      (fun w hw => by rw [h2M] at hw; exact hntF w hw)
      (fun w hw => by rw [h2M] at hw; exact hF0nt w hw)
      (fun w hw => by rw [h2M] at hw; exact hdef w hw)
      (by rw [hpin, hΦ₀pin]) (Work.Pert.Xc d v) hz
    have h2' : Φ₀ (Work.Pert.Xc d v) = v := hΦ₀inv' v hv
    have h3' : ‖Φm (Work.Pert.Xc d v) - v‖
        ≤ ‖Φm (Work.Pert.Xc d v) - Φ₀ (Work.Pert.Xc d v)‖
          + ‖Φ₀ (Work.Pert.Xc d v) - v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4' : ‖Φ₀ (Work.Pert.Xc d v) - v‖ = 0 := by rw [h2', sub_self, norm_zero]
    have h12' : Cdev / (M / 80) + 4 * E = Cdev * 80 / M + 4 * E := by
      field_simp
    rw [h12'] at h1'
    have h13 : 0 ≤ Cdev * 80 / M + 4 * E := by
      have h14 : 0 ≤ Cdev * 80 / M := div_nonneg (by linarith) (by linarith)
      linarith
    calc ‖Φm (Work.Pert.Xc d v) - v‖
        ≤ ‖Φm (Work.Pert.Xc d v) - Φ₀ (Work.Pert.Xc d v)‖
          + ‖Φ₀ (Work.Pert.Xc d v) - v‖ := h3'
      _ ≤ (Cdev * 80 / M + 4 * E) * ‖Work.Pert.Xc d v - c‖ + 0 := by rw [h4']; linarith
      _ ≤ (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := by
          have h15 := norm_Xc_sub_Xc_le d hv h1 h2 (by rw [← hcdef]; exact hXcM')
          rw [← hcdef] at h15
          have h16 : ‖Work.Pert.Xc d v - c‖ ≤ 2 * Xdev + 1 + Tb := by linarith [h15]
          linarith [mul_le_mul_of_nonneg_left h16 h13]
  -- ## 5. the deep point of the band and its level
  have hlev : ∃ m : ℕ, w - (m : ℂ) ∈ Work.Pert.Dstrip M Tb := by
    refine Work.Pert.exists_nat_sub_mem_Dstrip ?_ him2
    have h1 : -1 ≤ w.re := (abs_le.mp hre).1
    linarith
  set n : ℕ := Work.Pert.Ksub2.nw M Tb w with hndef
  set v₀ : ℂ := Work.Pert.Ksub2.uw M Tb w with hv₀def
  have hv₀strip : v₀ ∈ Work.Pert.Dstrip M Tb := Work.Pert.Ksub2.uw_mem_Dstrip hlev
  have hv₀add : v₀ + (n : ℂ) = w := by
    rw [hv₀def, hndef, Work.Pert.Ksub2.uw]
    ring
  have hv₀re : v₀.re ≤ -M := hv₀strip.2.1
  have hv₀im : v₀.im = w.im := by rw [hv₀def, Work.Pert.Ksub2.uw]; simp
  have hnM : n ≤ ⌈M⌉₊ + 2 := by
    have h1 : (n : ℝ) ≤ w.re + M + 1 := Work.Pert.Ksub2.nw_le hlev
    have h2 : w.re ≤ 1 := (abs_le.mp hre).2
    have h3 : (n : ℝ) ≤ (⌈M⌉₊ : ℝ) + 2 := by
      have h4 : (M : ℝ) ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
      linarith
    exact_mod_cast h3
  have hN2 : (n : ℝ) ≤ ((⌈M⌉₊ + 2 : ℕ) : ℝ) := by exact_mod_cast hnM
  -- ## 6. the derivative bound on the deep ball
  have hclosed_sub_ball : Metric.closedBall v₀ (M / 8) ⊆ Work.Pert.Qm Ξ α :=
    fun z hz => hQdu v₀ hv₀strip (Metric.closedBall_subset_ball (by linarith) hz)
  have hderballQ : ∀ z ∈ Metric.closedBall v₀ (M / 8), DifferentiableAt ℂ Φm z := fun z hz =>
    hΦm.1.differentiableAt (hQmopen.mem_nhds (hclosed_sub_ball hz))
  have hderball : ∀ z ∈ Metric.closedBall v₀ (M / 8), ‖deriv Φm z - 1‖ ≤ 1 / 2 := by
    intro z hz
    set vv : ℂ → ℂ := fun y => Work.Pert.liftF u σ α y - y with hvv
    have hzQ : Metric.ball z (M / 8) ⊆ Work.Pert.Qm Ξ α := by
      refine subset_trans ?_ (hQdu v₀ hv₀strip)
      intro y hy
      have h1 : ‖y - v₀‖ < M / 4 := by
        have h2 : ‖y - z‖ < M / 8 := by
          rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy
        have h3 : ‖z - v₀‖ ≤ M / 8 := by
          rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
        calc ‖y - v₀‖ ≤ ‖y - z‖ + ‖z - v₀‖ := by
              have h4 := norm_add_le (y - z) (z - v₀)
              rw [sub_add_sub_cancel] at h4
              exact h4
          _ < M / 4 := by linarith
      rw [Metric.mem_ball, dist_eq_norm]
      exact h1
    have hvdiff : DifferentiableOn ℂ vv (Metric.ball z (M / 8)) := by
      rw [hvv]
      exact ((hNT.1.1.mono hzQ).sub differentiableOn_id)
    have hvnear : ∀ y ∈ Metric.ball z (M / 8), ‖vv y - 1‖ < 1 / 4 := by
      intro y hy
      have h1 : ‖vv y - 1‖ ≤ 1 / 32 := by
        have he : vv y - 1 = Work.Pert.liftF u σ α y - (y + 1) := by simp only [hvv]; ring
        rw [he]
        exact (hNT.1.2 y (hzQ hy)).1
      linarith
    have habel : ∀ y ∈ Metric.ball z (M / 8), y + vv y ∈ Metric.ball z (M / 8) →
        Φm (y + vv y) = Φm y + 1 := by
      intro y hy hyv
      have he : y + vv y = Work.Pert.liftF u σ α y := by simp only [hvv]; ring
      have h1 := hΦm.2.2 y (hzQ hy) (by rw [← he]; exact hzQ hyv)
      rwa [← he] at h1
    have hb2 := hDE Φm vv z (M / 8) hR₁M (hΦm.1.mono hzQ) (hΦm.2.1.mono hzQ)
      hvdiff hvnear habel
    have hvz : ‖vv z - 1‖ ≤ 1 / 32 := by
      have he : vv z - 1 = Work.Pert.liftF u σ α z - (z + 1) := by simp only [hvv]; ring
      rw [he]
      exact (hNT.1.2 z (hzQ (Metric.mem_ball_self (by linarith)))).1
    have hvinv : ‖1 / vv z - 1‖ ≤ 1 / 31 := by
      have h1 : ‖1 - vv z‖ ≤ 1 / 32 := by rw [norm_sub_rev]; exact hvz
      have h2 : (31 : ℝ) / 32 ≤ ‖vv z‖ := by
        have h3 : (1 : ℝ) ≤ ‖vv z‖ + ‖1 - vv z‖ := by
          have he : (1 : ℂ) = vv z + (1 - vv z) := by ring
          calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
            _ = ‖vv z + (1 - vv z)‖ := congrArg (fun x : ℂ => ‖x‖) he
            _ ≤ ‖vv z‖ + ‖1 - vv z‖ := norm_add_le _ _
        linarith
      have hne : vv z ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h2; norm_num at h2
      rw [div_sub_one hne, norm_div]
      have h4 : ‖1 - vv z‖ / ‖vv z‖ ≤ (1 / 32) / (31 / 32) :=
        div_le_div₀ (by norm_num) h1 (by norm_num) h2
      nlinarith [h4]
    have hC2R : C₂ / (M / 8) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < M / 8)]
      nlinarith [hC₂M]
    have htri : ‖deriv Φm z - 1‖ ≤ ‖deriv Φm z - 1 / vv z‖ + ‖1 / vv z - 1‖ := by
      have h := norm_add_le (deriv Φm z - 1 / vv z) (1 / vv z - 1)
      rwa [sub_add_sub_cancel] at h
    linarith [htri, hb2, hvinv, hC2R]
  -- ## 7. the mean value bound `‖Φm - id‖` on the deep ball
  have hsh₂ : ‖Φm v₀ - v₀‖ < M / 32 := by
    have hx : v₀ ∈ Metric.closedBall v₀ (M / 8) := Metric.mem_closedBall_self (by linarith)
    have hy : Work.Pert.Xc d v₀ ∈ Metric.closedBall v₀ (M / 8) := by
      refine mem_closedBall_of_norm_le ?_
      have h2 : Xdev ≤ M / 8 := by linarith
      linarith [hXcsv v₀ hv₀strip]
    have hdiff : ∀ z ∈ Metric.closedBall v₀ (M / 8),
        DifferentiableAt ℂ (fun z => Φm z - z) z :=
      fun z hz => (hderballQ z hz).sub (differentiableAt_id (x := z))
    have hb : ∀ z ∈ Metric.closedBall v₀ (M / 8),
        ‖deriv (fun z => Φm z - z) z‖ ≤ 1 / 2 := by
      intro z hz
      have hde : deriv (fun z : ℂ => Φm z - z) z = deriv Φm z - deriv (id : ℂ → ℂ) z :=
        deriv_sub (hderballQ z hz) (differentiableAt_id (x := z))
      rw [hde, deriv_id]
      exact hderball z hz
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z => Φm z - z)
      (C := 1 / 2) (s := Metric.closedBall v₀ (M / 8)) (x := Work.Pert.Xc d v₀) (y := v₀)
      hdiff hb (convex_closedBall v₀ (M / 8)) hy hx
    have h1 : ‖(Φm v₀ - v₀) - (Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀)‖
        ≤ (1 / 2) * ‖v₀ - Work.Pert.Xc d v₀‖ := by simpa using hmv
    have hXcv₀ : ‖Work.Pert.Xc d v₀ - v₀‖ ≤ Xdev := hXcsv v₀ hv₀strip
    have hXcv₀' : ‖v₀ - Work.Pert.Xc d v₀‖ ≤ Xdev := by rw [norm_sub_rev]; exact hXcv₀
    have hdev_v : ‖Φm (Work.Pert.Xc d v₀) - v₀‖
        ≤ (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := hdevXc v₀ hv₀strip
    have h11 : ‖Φm v₀ - v₀‖ ≤ ‖(Φm v₀ - v₀) - (Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀)‖
        + ‖Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀‖ := by
      have h := norm_add_le ((Φm v₀ - v₀) - (Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀))
        (Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀)
      rwa [sub_add_cancel] at h
    have h12 : ‖Φm (Work.Pert.Xc d v₀) - Work.Pert.Xc d v₀‖
        ≤ Xdev + (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := by
      have h := norm_sub_le_norm_sub_add_norm_sub (Φm (Work.Pert.Xc d v₀)) v₀
        (Work.Pert.Xc d v₀)
      linarith [h, hdev_v, hXcv₀']
    have h7 : (3 / 2) * Xdev + (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb)
        ≤ (3 / 2) * Xdev + (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb) := by
      have h8 : 0 ≤ Cdev * 80 / M + 4 * E := by
        have h9 : 0 ≤ Cdev * 80 / M := div_nonneg (by linarith) (by linarith)
        linarith
      have h9 : 2 * Xdev + 1 + Tb ≤ 3 * Xdev + 1 + Tb := by linarith
      linarith [mul_le_mul_of_nonneg_left h9 h8]
    linarith [h1, h11, h12, hXcv₀', hdevcov, h7]
  -- ## 8. the covering and the preimage
  have hcov := image_cover_centered (Φ := Φm) (z₀ := v₀) (r := M / 8)
    (by linarith : (0 : ℝ) < M / 8) (fun z hz => hderballQ z hz) hderball
  have hdevv : ‖Φm v₀ - v₀‖ < M / 8 / 4 := by
    have h1 : M / 8 / 4 = M / 32 := by ring
    rw [h1]; exact hsh₂
  have hmemv : v₀ ∈ Metric.ball (Φm v₀) (M / 8 / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact hdevv
  obtain ⟨ς, hςball, hςΦ⟩ := hcov hmemv
  have hςQ : ς ∈ Work.Pert.Qm Ξ α := hclosed_sub_ball hςball
  have hςXc : Work.Pert.Xc d v₀ ∈ Metric.closedBall v₀ (M / 8) := by
    refine mem_closedBall_of_norm_le ?_
    have h2 : Xdev ≤ M / 8 := by linarith
    linarith [hXcsv v₀ hv₀strip]
  have hcoer : ‖ς - Work.Pert.Xc d v₀‖ ≤ 2 * ‖Φm ς - Φm (Work.Pert.Xc d v₀)‖ :=
    norm_sub_le_two_mul_of_image_sub_le (Φ := Φm) (c := v₀) (r := M / 8)
      (fun z hz => hderballQ z hz) hderball hςball hςXc
  have hςdev : ‖ς - Work.Pert.Xc d v₀‖
      ≤ 2 * ((Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb)) := by
    have h1 : ‖Φm ς - Φm (Work.Pert.Xc d v₀)‖ = ‖v₀ - Φm (Work.Pert.Xc d v₀)‖ := by
      rw [hςΦ]
    rw [h1] at hcoer
    have h2 : ‖v₀ - Φm (Work.Pert.Xc d v₀)‖
        ≤ (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := by
      rw [norm_sub_rev]
      exact hdevXc v₀ hv₀strip
    linarith
  -- ## 9. the seed error
  have hv₀norm : M ≤ ‖v₀‖ := by
    have h1 : v₀.re ≤ -M := hv₀re
    have h2 : |v₀.re| ≤ ‖v₀‖ := Complex.abs_re_le_norm _
    have h3 : |v₀.re| = -v₀.re := abs_of_nonpos (by linarith)
    linarith
  have hςnorm : M / 2 ≤ ‖ς‖ := by
    have h1 : ‖ς - v₀‖ ≤ M / 8 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hςball
      exact hςball
    have h2 : ‖v₀‖ ≤ ‖ς‖ + ‖v₀ - ς‖ := by
      have h3 := norm_add_le ς (v₀ - ς)
      rw [add_sub_cancel] at h3
      exact h3
    have h4 : ‖v₀ - ς‖ = ‖ς - v₀‖ := norm_sub_rev v₀ ς
    linarith
  have hXcnorm : M / 2 ≤ ‖Work.Pert.Xc d v₀‖ := by
    have h1 : ‖v₀‖ ≤ ‖Work.Pert.Xc d v₀‖ + ‖v₀ - Work.Pert.Xc d v₀‖ := by
      have h2 := norm_add_le (Work.Pert.Xc d v₀) (v₀ - Work.Pert.Xc d v₀)
      rw [add_sub_cancel] at h2
      exact h2
    have h3 : ‖v₀ - Work.Pert.Xc d v₀‖ ≤ Xdev := by rw [norm_sub_rev]; exact hXcsv v₀ hv₀strip
    have h4 : Xdev ≤ M / 2 := by linarith
    linarith
  have harg : 2 * Real.pi * ‖α‖ * ‖ς‖ ≤ 1 / 2 := by
    have h1 : ‖ς‖ ≤ 2 * M := by
      have h2 : ‖ς - v₀‖ ≤ M / 8 := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hςball
        exact hςball
      have h3 : ‖v₀‖ ≤ M + 1 + Tb := by
        have h4 : ‖v₀ - (((-M : ℝ)) : ℂ)‖ ≤ 1 + Tb := Work.Pert.Ksub2.norm_sub_negM_le hv₀strip
        have h5 : ‖(((-M : ℝ)) : ℂ)‖ = M := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ M)]
        have h6 := norm_add_le (v₀ - (((-M : ℝ)) : ℂ)) ((((-M : ℝ)) : ℂ))
        rw [sub_add_cancel, h5] at h6
        linarith
      have h7 : ‖ς‖ ≤ ‖v₀‖ + ‖ς - v₀‖ := by
        have h8 := norm_add_le v₀ (ς - v₀)
        rw [add_sub_cancel] at h8
        exact h8
      have h9 : Tb ≤ M / 160 := hTbM
      linarith
    have h10 : 2 * Real.pi * ‖α‖ * (2 * M) ≤ 1 / 2 := by
      have h11 : ‖α‖ * (32 * (M + 2)) ≤ 1 :=
        (le_div_iff₀ (by linarith : (0 : ℝ) < 32 * (M + 2))).mp hα32
      have h12 : 2 * Real.pi * ‖α‖ * (2 * M) ≤ 1 / 2 := by
        have h15 : 2 * Real.pi * ‖α‖ * (2 * M) ≤ 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M) := by
          have h16 : 0 ≤ 2 * Real.pi * (2 * M) := by positivity
          nlinarith [hα32, hMpos, norm_nonneg α, Real.pi_pos]
        have h17 : 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M) ≤ 1 / 2 := by
          have h19 : (M : ℝ) / (M + 2) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          have h20 : 2 * Real.pi * (1 / (32 * (M + 2))) * (2 * M)
              = Real.pi / 8 * (M / (M + 2)) := by
            field_simp
            ring
          rw [h20]
          nlinarith [h19, Real.pi_lt_four, Real.pi_pos]
        linarith
      linarith [h1, h12, hMpos]
    nlinarith [h1, h10, Real.pi_pos, norm_nonneg α]
  have hseedErr : ‖Work.Pert.tauC σ α ς - d.φ v₀‖
      ≤ Cseed * (((Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb)) / (M * M)
        + ‖u 0 - 1‖ / M + ‖α‖) := by
    have hdevnn' : 0 ≤ (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb) := by
      have h2 : 0 ≤ Cdev * 80 / M := div_nonneg (by linarith) (by linarith)
      have h3 : 0 ≤ 2 * Xdev + 1 + Tb := by linarith
      positivity
    have h1 := hseedA (u := u) (σ := σ) (α := α) (ς := ς) (y := Work.Pert.Xc d v₀)
      (M' := M) (dev := (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb))
      hMpos (by linarith) hdevnn' hςnorm hXcnorm hςdev harg hnorm hαne hu0quarter hαquarter
    have h2 : MandelDim.tau0 (Work.Pert.Xc d v₀) = d.φ v₀ := by
      rw [show Work.Pert.Xc d v₀ = MandelDim.tau0 (d.φ v₀) from rfl, tau0_involutive]
    rw [h2] at h1
    exact h1
  have hdevnn : 0 ≤ (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb) := by
    have h1 : 0 ≤ Cdev * 80 / M := div_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 3 * Xdev + 1 + Tb := by linarith
    positivity
  have hCMMpos : 0 < Camp * M * M := by nlinarith [hCamp1, hMpos]
  have hA23 : (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb)
      ≤ (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb) := by
    have h2 : 0 ≤ Cdev * 80 / M + 4 * E := by
      have h4 : 0 ≤ Cdev * 80 / M := div_nonneg (by linarith) (by linarith)
      linarith
    have h3 : 2 * Xdev + 1 + Tb ≤ 3 * Xdev + 1 + Tb := by linarith
    exact mul_le_mul_of_nonneg_left h3 h2
  have hdevR' : Cseed * (2 * (((Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb)) / (M * M)))
      ≤ R / (12 * Camp * M * M) := by
    simpa only [mul_div_assoc] using hdevR
  obtain ⟨hseedBnd, htrapc, hsmallc⟩ :=
    seed_bound_arith (A2 := (Cdev * 80 / M + 4 * E) * (2 * Xdev + 1 + Tb))
      (A3 := (Cdev * 80 / M + 4 * E) * (3 * Xdev + 1 + Tb))
      (u0v := ‖u 0 - 1‖) (av := ‖α‖)
      hMpos hCamp1 hCseed hRpos hR4 hA23 hdevR' hu0R hαR
  have hseedTrap : Camp * M * M * ‖Work.Pert.tauC σ α ς - d.φ v₀‖ ≤ R / 4 := by
    have h := mul_le_mul_of_nonneg_left (le_trans hseedErr hseedBnd) hCMMpos.le
    linarith
  have hseedSmall : ‖Work.Pert.tauC σ α ς - d.φ v₀‖ < 1 / (Camp * M * M) :=
    lt_of_le_of_lt (le_trans hseedErr hseedBnd) hsmallc
  -- ## 10. the trap
  have hLfn : Lf ^ n ≤ Lf ^ (⌈M⌉₊ + 2) := pow_le_pow_right₀ hLf1 hnM
  have hsmalltrap : δ₀ * (n : ℝ) * Lf ^ n ≤ R / 4 := by
    have h1 : δ₀ * (n : ℝ) * Lf ^ n
        ≤ δ₀ * ((⌈M⌉₊ + 2 : ℕ) : ℝ) * Lf ^ (⌈M⌉₊ + 2) := by
      have h2 : δ₀ * (n : ℝ) ≤ δ₀ * ((⌈M⌉₊ + 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hN2 (by linarith)
      calc δ₀ * (n : ℝ) * Lf ^ n ≤ δ₀ * ((⌈M⌉₊ + 2 : ℕ) : ℝ) * Lf ^ n :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg (by linarith) n)
        _ ≤ δ₀ * ((⌈M⌉₊ + 2 : ℕ) : ℝ) * Lf ^ (⌈M⌉₊ + 2) :=
            mul_le_mul_of_nonneg_left hLfn (mul_nonneg (by linarith) (by positivity))
    linarith
  have htrap := Work.PertCrux.defect_le_of_trap (f₀ := f₀) (f := f)
    (p := fun k : ℕ => d.φ (v₀ + (k : ℂ))) (a := Work.Pert.tauC σ α ς) (n := n)
    (L := Lf) (ε := δ₀) (R := R) (by linarith) (by linarith) hLf1
    (fun k hk x y hx hy => hLlip k (le_trans (Nat.le_of_lt hk) hnM) v₀ hv₀strip hv₀im x y hx hy)
    (fun k hk x hx => le_of_lt (hNear.2.2.2 x (hLtrap k (le_trans (Nat.le_of_lt hk) hnM)
      v₀ hv₀strip hv₀im (mem_closedBall_of_norm_le hx))))
    (fun k hk => by
      have h1 := hampA M Tb hCampTb hy₁Tb w hre him1 him2 v₀ hv₀strip n hv₀add k hk
        (Work.Pert.tauC σ α ς) hseedSmall
      have h2 : f₀^[k] (d.φ v₀) = d.φ (v₀ + (k : ℂ)) :=
        Work.Pert.Ksub2.iterate_phi_of_mem d (fun i hi => (d.ends_sub (v₀ + (i : ℂ))
          (by rw [show (v₀ + (i : ℂ)).im = v₀.im by simp, hv₀im]; linarith)).1)
      rw [h2] at h1
      linarith [h1, hseedTrap])
    hsmalltrap
  -- ## 11. `GoodP`
  have hseedP : Work.Pert.seedP (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) (w - (n : ℂ))
      = Work.Pert.tauC σ α ς := by
    have h1 : w - (n : ℂ) = v₀ := by rw [← hv₀add]; ring
    rw [Work.Pert.seedP, h1]
    congr 1
    exact Work.Pert.invOn_eq hΦm.2.1 ⟨ς, hςQ, hςΦ⟩ hςQ hςΦ
  refine Work.Pert.mem_DphiP.mpr ⟨n, ⟨ς, hςQ, hςΦ⟩, fun j hj => ?_⟩
  have h1 := htrap.1 j (le_of_lt hj)
  rw [hseedP]
  exact hNear.2.1 (hLtrap j (le_trans (Nat.le_of_lt hj) hnM) v₀ hv₀strip hv₀im
    (mem_closedBall_of_norm_le h1))

end Work.Pert.Pin
