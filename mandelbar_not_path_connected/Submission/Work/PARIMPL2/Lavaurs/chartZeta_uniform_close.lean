import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

/-- A uniform bound for the incoming geometric window: every point of `WinG P R H` lies within
`max 1 (‖P.s c₀‖ / 8)` of the parabolic point `d.z₁`.  Indeed, either `H < 0` and the window is
empty (because `|(w0 P z).im| ≤ H < 0` is impossible), or `H ≥ 0` and hence `8 ≤ R`, so that
`Re (w0 P z) ≥ R ≥ 8` and `‖z - d.z₁‖ = ‖P.s c₀‖ / ‖w0 P z‖ ≤ ‖P.s c₀‖/8`. -/
theorem winG_norm_sub_z₁_le {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (R H : ℝ) (hH : R ≥ 8 * (H + 1)) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WinG P R H) :
    ‖z - d.z₁‖ ≤ max 1 (‖P.s c₀‖ / 8) := by
  have hHnn : 0 ≤ H := by
    by_contra h
    have hlt : H < 0 := not_le.mp h
    have h1 := hz.2.2
    have h2 : (0 : ℝ) ≤ |(Work.PARIMPL2.w0 P z).im| := abs_nonneg _
    linarith
  have hR8 : 8 ≤ R := by have := hH; nlinarith
  have hw : R ≤ ‖Work.PARIMPL2.w0 P z‖ := by
    have h1 : R ≤ (Work.PARIMPL2.w0 P z).re := hz.2.1.1
    have h2 : (Work.PARIMPL2.w0 P z).re ≤ ‖Work.PARIMPL2.w0 P z‖ := Complex.re_le_norm _
    linarith
  have h8w : (8 : ℝ) ≤ ‖Work.PARIMPL2.w0 P z‖ := le_trans hR8 hw
  have hz1 : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz.1
  have hprod : Work.PARIMPL2.w0 P z * (z - d.z₁) = -P.s c₀ := by
    rw [Work.PARIMPL2.w0]; field_simp
  have hnorm : ‖Work.PARIMPL2.w0 P z‖ * ‖z - d.z₁‖ = ‖P.s c₀‖ := by
    have := congrArg norm hprod
    rwa [norm_mul, norm_neg] at this
  have hle : 8 * ‖z - d.z₁‖ ≤ ‖P.s c₀‖ := by
    rw [← hnorm]
    exact mul_le_mul_of_nonneg_right h8w (norm_nonneg _)
  have hfin : ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / 8 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  exact le_trans hfin (le_max_right _ _)

/-- **The chart coordinate of the incoming window depends uniformly continuously on `(c, z')`.**
For a fixed depth `R` (with `R ≥ 8 (H+1)`) and every `η > 0` there are `ρ, δ > 0` such that for
every parameter `c ∈ P.Nm` within `ρ` of `c₀`, every `z` in the incoming window `WinG P R H` and
every `z'` within `δ` of `z`,

  `‖ζ_c(z') − ζ_{c₀}(z)‖ ≤ η`,  where `ζ_c(z) = chartZeta P c z = (z − P.m c)/P.s c`.

The point is that `δ` is **uniform over the whole window**: `WinG` is compact (it is the
`w₀`-preimage of the compact rectangle `[R,R+2] × [−H,H]`, i.e. `‖z − d.z₁‖ = ‖P.s c₀‖/‖w₀ z‖ ≤
‖P.s c₀‖/R`), and `P.m c → P.m c₀ = d.z₁`, `P.s c → P.s c₀ ≠ 0` as `c → c₀` (`P.cont_m`, `P.cont_s`,
`P.m₀`, `P.s_ne`).  Here `d : Work.EL.RootParabolic c₀` and `P : Work.PARIMPL.ParNormal d`. -/
theorem chartZeta_uniform_close {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (R H η : ℝ) (hH : R ≥ 8 * (H + 1)) (hη : 0 < η) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      ∀ z ∈ Work.PARIMPL2.WinG P R H, ∀ z' : ℂ, ‖z' - z‖ ≤ δ →
        ‖Work.PARIMPL.chartZeta P c z' - Work.PARIMPL.chartZeta P c₀ z‖ ≤ η := by
  have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  have hμpos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs0
  have hμne : ‖P.s c₀‖ ≠ 0 := ne_of_gt hμpos
  -- the tolerances: `d₁` for `‖z' - z‖` and for `‖P.m c - d.z₁‖`, and `ε₂` for `‖P.s c - P.s c₀‖`
  set d₁ : ℝ := min 1 (η * ‖P.s c₀‖ / 4) with hd₁
  have hd₁pos : 0 < d₁ := by rw [hd₁]; exact lt_min zero_lt_one (by positivity)
  have hd₁le : d₁ ≤ η * ‖P.s c₀‖ / 4 := by rw [hd₁]; exact min_le_right _ _
  set B : ℝ := max 1 (‖P.s c₀‖ / 8) with hB
  have hBpos : 0 < B := by rw [hB]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBwin : ∀ z ∈ Work.PARIMPL2.WinG P R H, ‖z - d.z₁‖ ≤ B := by
    intro z hz
    have h := winG_norm_sub_z₁_le P R H hH hz
    rwa [← hB] at h
  set C : ℝ := d₁ + B + d₁ with hC
  have hCpos : 0 < C := by rw [hC]; linarith
  have hCne : C ≠ 0 := ne_of_gt hCpos
  set ε₂ : ℝ := min (‖P.s c₀‖ / 2) (η * ‖P.s c₀‖ ^ 2 / (4 * C)) with hε₂
  have hε₂pos : 0 < ε₂ := by rw [hε₂]; exact lt_min (by positivity) (by positivity)
  have hε₂half : ε₂ ≤ ‖P.s c₀‖ / 2 := by rw [hε₂]; exact min_le_left _ _
  have hε₂η : ε₂ ≤ η * ‖P.s c₀‖ ^ 2 / (4 * C) := by rw [hε₂]; exact min_le_right _ _
  -- continuity of `P.m` and `P.s` at `c₀`
  obtain ⟨dm, hdmpos, hdm⟩ :=
    Metric.continuousOn_iff.mp P.cont_m c₀ (Metric.mem_ball_self P.hρ₀) d₁ hd₁pos
  obtain ⟨ds, hdspos, hds⟩ :=
    Metric.continuousOn_iff.mp P.cont_s c₀ (Metric.mem_ball_self P.hρ₀) ε₂ hε₂pos
  refine ⟨min P.ρ₀ (min dm ds), d₁, ?_, hd₁pos, ?_⟩
  · exact lt_min P.hρ₀ (lt_min hdmpos hdspos)
  intro c hc z hz z' hz'
  have hcρ : dist c c₀ < min P.ρ₀ (min dm ds) := hc.2
  have hcmem : c ∈ Metric.ball c₀ P.ρ₀ := lt_of_lt_of_le hcρ (min_le_left _ _)
  have hcdm : dist c c₀ < dm :=
    lt_of_lt_of_le hcρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcds : dist c c₀ < ds :=
    lt_of_lt_of_le hcρ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hmclose : ‖P.m c - d.z₁‖ < d₁ := by
    have h := hdm c hcmem hcdm
    rw [P.m₀, dist_eq_norm] at h
    exact h
  have hsclose : ‖P.s c - P.s c₀‖ < ε₂ := by
    have h := hds c hcmem hcds
    rwa [dist_eq_norm] at h
  have hsc : P.s c ≠ 0 := P.s_ne c hcmem
  -- the algebraic decomposition of the difference of the two chart coordinates
  have hdecomp : Work.PARIMPL.chartZeta P c z' - Work.PARIMPL.chartZeta P c₀ z =
      (z' - z) / P.s c₀ + (d.z₁ - P.m c) / P.s c₀ +
        (z' - P.m c) * (1 / P.s c - 1 / P.s c₀) := by
    simp only [Work.PARIMPL.chartZeta, P.m₀]
    field_simp
    ring
  -- the first two terms
  have ht1 : ‖(z' - z) / P.s c₀‖ ≤ η / 4 := by
    rw [norm_div]
    have h1 : ‖z' - z‖ / ‖P.s c₀‖ ≤ d₁ / ‖P.s c₀‖ :=
      div_le_div_of_nonneg_right hz' hμpos.le
    have h2 : d₁ / ‖P.s c₀‖ ≤ η / 4 := by
      rw [div_le_iff₀ hμpos]; nlinarith
    linarith
  have ht2 : ‖(d.z₁ - P.m c) / P.s c₀‖ ≤ η / 4 := by
    rw [norm_div, norm_sub_rev]
    have h1 : ‖P.m c - d.z₁‖ / ‖P.s c₀‖ ≤ d₁ / ‖P.s c₀‖ :=
      div_le_div_of_nonneg_right hmclose.le hμpos.le
    have h2 : d₁ / ‖P.s c₀‖ ≤ η / 4 := by
      rw [div_le_iff₀ hμpos]; nlinarith
    linarith
  -- the third term
  have hscge : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := by
    have h1 : |‖P.s c₀‖ - ‖P.s c‖| ≤ ‖P.s c₀ - P.s c‖ := abs_norm_sub_norm_le _ _
    have h2 : ‖P.s c₀ - P.s c‖ ≤ ε₂ := by rw [norm_sub_rev]; exact hsclose.le
    have h3 : ‖P.s c₀‖ - ‖P.s c‖ ≤ ε₂ := le_trans (le_abs_self _) (le_trans h1 h2)
    linarith
  have ht3 : ‖(z' - P.m c) * (1 / P.s c - 1 / P.s c₀)‖ ≤ η / 2 := by
    rw [norm_mul]
    have hrew : 1 / P.s c - 1 / P.s c₀ = (P.s c₀ - P.s c) / (P.s c * P.s c₀) := by
      field_simp
    have hinv : ‖1 / P.s c - 1 / P.s c₀‖ ≤ 2 * ε₂ / ‖P.s c₀‖ ^ 2 := by
      rw [hrew, norm_div, norm_mul]
      have hnum : ‖P.s c₀ - P.s c‖ ≤ ε₂ := by rw [norm_sub_rev]; exact hsclose.le
      have hc2 : ‖P.s c₀‖ / 2 * ‖P.s c₀‖ ≤ ‖P.s c‖ * ‖P.s c₀‖ :=
        mul_le_mul_of_nonneg_right hscge hμpos.le
      calc ‖P.s c₀ - P.s c‖ / (‖P.s c‖ * ‖P.s c₀‖)
          ≤ ε₂ / (‖P.s c₀‖ / 2 * ‖P.s c₀‖) :=
            div_le_div₀ hε₂pos.le hnum (by positivity) hc2
        _ = 2 * ε₂ / ‖P.s c₀‖ ^ 2 := by field_simp
    have hz'm : ‖z' - P.m c‖ ≤ C := by
      rw [hC]
      have h1 : ‖z' - P.m c‖ ≤ ‖z' - z‖ + ‖z - P.m c‖ := by
        have := norm_add_le (z' - z) (z - P.m c); simpa using this
      have h2 : ‖z - P.m c‖ ≤ ‖z - d.z₁‖ + ‖d.z₁ - P.m c‖ := by
        have := norm_add_le (z - d.z₁) (d.z₁ - P.m c); simpa using this
      have h3 : ‖d.z₁ - P.m c‖ = ‖P.m c - d.z₁‖ := norm_sub_rev _ _
      linarith [hBwin z hz, hmclose.le]
    have hstep : C * (2 * ε₂ / ‖P.s c₀‖ ^ 2) ≤ η / 2 := by
      have h3 : 0 < 2 * C / ‖P.s c₀‖ ^ 2 := by positivity
      calc C * (2 * ε₂ / ‖P.s c₀‖ ^ 2) = ε₂ * (2 * C / ‖P.s c₀‖ ^ 2) := by ring
        _ ≤ (η * ‖P.s c₀‖ ^ 2 / (4 * C)) * (2 * C / ‖P.s c₀‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hε₂η h3.le
        _ = η / 2 := by field_simp; ring
    calc ‖z' - P.m c‖ * ‖1 / P.s c - 1 / P.s c₀‖
        ≤ C * (2 * ε₂ / ‖P.s c₀‖ ^ 2) :=
          mul_le_mul hz'm hinv (norm_nonneg _) hCpos.le
      _ ≤ η / 2 := hstep
  -- assemble
  have hnorm : ‖Work.PARIMPL.chartZeta P c z' - Work.PARIMPL.chartZeta P c₀ z‖ ≤
      ‖(z' - z) / P.s c₀‖ + ‖(d.z₁ - P.m c) / P.s c₀‖ +
        ‖(z' - P.m c) * (1 / P.s c - 1 / P.s c₀)‖ := by
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  linarith

end Work.PARIMPL2.Lavaurs
