import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

section OseAux

open scoped Topology
open Filter

/-- The `ε`-`δ` content of `HasDerivAt` in the shifted variable `a = x' - x`. -/
private lemma hasDerivAt_shift {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ a in 𝓝 (0 : ℝ), ‖f (x + a) - f x - f' * a‖ ≤ c * |a| := by
  have hlit : ∀ᶠ y in 𝓝 x, ‖f y - f x - (y - x) • f'‖ ≤ c * ‖y - x‖ := (h.isLittleO).bound hc
  have htend : Filter.Tendsto (fun a : ℝ => x + a) (𝓝 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 x)).add
      (tendsto_id : Filter.Tendsto (fun a : ℝ => a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)))
  filter_upwards [htend.eventually hlit] with a ha
  have h1 : x + a - x = a := by ring
  have h2 : a * f' = f' * a := mul_comm _ _
  rw [h1] at ha
  simpa only [smul_eq_mul, Real.norm_eq_abs, h2] using ha

/-- For `0 ≤ N` there are arbitrarily small positive `δ` with `N · δ ^ α ≤ c` (`c > 0`,
`α > 0`). -/
private lemma exists_rpow_small {N α : ℝ} (hN : 0 ≤ N) (hα : 0 < α) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, N * δ ^ α ≤ c := by
  have hN1 : (0 : ℝ) < N + 1 := by linarith
  refine ⟨(c / (N + 1)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  rw [← Real.rpow_mul (le_of_lt (by positivity : (0 : ℝ) < c / (N + 1))), one_div,
    inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
  rw [← mul_div_assoc, div_le_iff₀ hN1]
  nlinarith

/-- The `τ`-slices of a `Jet` are continuous on `[0,1]`. -/
private lemma jet_slice_continuousOn {h : ℝ → ℝ → ℝ → ℝ} {α N : ℝ}
    (H : Work.FTS.Regularity.Jet α 1 N h) (hα : 0 < α) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ContinuousOn (fun s => h z θ s) (Set.Icc 0 1) := by
  have hN : 0 ≤ N := H.1
  intro s₀ hs₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨t, htpos, htle⟩ := exists_rpow_small hN hα (c := ε / 2) (by linarith)
  refine ⟨t, htpos, ?_⟩
  intro s' hs' hd
  have hb := H.2.2 z z θ θ s' s₀ hz hz hθ hθ hs' hs₀
  simp only [sub_self, abs_zero, zero_add] at hb
  have hds : dist s' s₀ = |s' - s₀| := Real.dist_eq _ _
  rw [hds] at hd
  have h1 : |s' - s₀| ^ α ≤ t ^ α := Real.rpow_le_rpow (abs_nonneg _) hd.le hα.le
  have h2 : dist (h z θ s') (h z θ s₀) = |h z θ s' - h z θ s₀| := Real.dist_eq _ _
  rw [h2]
  calc |h z θ s' - h z θ s₀| ≤ N * |s' - s₀| ^ α := hb
    _ ≤ N * t ^ α := mul_le_mul_of_nonneg_left h1 hN
    _ ≤ ε / 2 := htle
    _ < ε := by linarith

end OseAux

namespace Work.FTS_RegExport.RXR1

theorem oneSided_expansion {g R : ℝ → ℝ → ℝ → ℝ} {θ Nc α z : ℝ} (hα : 0 < α) (hNc : 0 ≤ Nc)
    (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z)
    (hFTC : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ k ∈ Set.Icc (0:ℝ) 1,
      g z' θ k - g z' θ 0 = ∫ s in (0:ℝ)..k, R z' θ s)
    (hjet : Work.FTS.Regularity.Jet α 1 Nc (fun z θ τ => R z θ τ))
    (hder0 : HasDerivAt (fun z' => g z' θ 0) (deriv (fun z' => g z' θ 0) z) z) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ × ℝ, ‖y - (z, (0:ℝ))‖ < δ → 0 ≤ y.2 →
      ‖g y.1 θ y.2 - g z θ 0 - deriv (fun z' => g z' θ 0) z * (y.1 - z) - R z θ 0 * y.2‖
        ≤ ε * ‖y - (z, (0:ℝ))‖ := by
  intro ε hε
  set D : ℝ := deriv (fun z' => g z' θ 0) z with hD
  have hε2 : 0 < ε / 2 := by linarith
  -- (1) the one-dimensional differentiability in `z`
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      ‖g (z + a) θ 0 - g z θ 0 - D * a‖ ≤ (ε / 2) * |a| := by
    have h := hasDerivAt_shift hder0 hε2
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hδ'⟩ := h
    exact ⟨δ, hδ, fun a ha => hδ' (by simpa [Real.dist_eq] using ha)⟩
  -- (2) the smallness threshold for the `τ`-integral
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ > 0, ∀ r : ℝ, 0 ≤ r → r < δ → Nc * (2 * r) ^ α ≤ ε / 2 := by
    obtain ⟨t, htpos, htle⟩ := exists_rpow_small hNc hα hε2
    refine ⟨t / 2, by linarith, fun r hr hrt => ?_⟩
    have h2r : 2 * r < t := by linarith
    have hle : (2 * r) ^ α ≤ t ^ α := Real.rpow_le_rpow (by linarith) h2r.le hα.le
    calc Nc * (2 * r) ^ α ≤ Nc * t ^ α := mul_le_mul_of_nonneg_left hle hNc
      _ ≤ ε / 2 := htle
  have hδz : 0 < min δ₁ (min δ₂ (min (z / 2) (1 / 2))) :=
    lt_min hδ₁pos (lt_min hδ₂pos (lt_min (by linarith) (by norm_num)))
  refine ⟨min δ₁ (min δ₂ (min (z / 2) (1 / 2))), hδz, ?_⟩
  rintro ⟨y1, y2⟩ hy hy2
  -- the distance is the sup-distance
  have hdist : ‖(y1, y2) - (z, (0 : ℝ))‖ = max |y1 - z| |y2| := by
    rw [← dist_eq_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
  have hδ₁' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ δ₁ := min_le_left _ _
  have hδ₂' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ δ₂ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδz' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ z / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδu' : min δ₁ (min δ₂ (min (z / 2) (1 / 2))) ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have habs1 : |y1 - z| ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    rw [hdist]; exact le_max_left _ _
  have habs2 : |y2| ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    rw [hdist]; exact le_max_right _ _
  have hy1z : |y1 - z| < δ₁ := lt_of_lt_of_le (lt_of_le_of_lt habs1 hy) hδ₁'
  have hr₂ : ‖(y1, y2) - (z, (0 : ℝ))‖ < δ₂ := lt_of_lt_of_le hy hδ₂'
  have hy1pos : 0 < y1 := by
    have h : |y1 - z| < z :=
      lt_of_lt_of_le (lt_of_le_of_lt habs1 hy) (by linarith [hδz'])
    have h' : -z < y1 - z := (abs_lt.mp h).1
    linarith
  have hy1nn : 0 ≤ y1 := hy1pos.le
  have hy2le1 : y2 ≤ 1 := by
    have h : |y2| < 1 := lt_of_lt_of_le (lt_of_le_of_lt habs2 hy) (by linarith [hδu'])
    exact le_of_lt (lt_of_le_of_lt (le_abs_self y2) h)
  -- the `z`-part
  have hzA : ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖
      ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    have h := hδ₁ (y1 - z) hy1z
    have h2 : z + (y1 - z) = y1 := by ring
    rw [h2] at h
    calc ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖ ≤ (ε / 2) * |y1 - z| := h
      _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_left habs1 (by linarith)
  -- the `τ`-part
  have hkB : ‖g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2‖
      ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
    have hFTC' := hFTC y1 hy1pos y2 ⟨hy2, hy2le1⟩
    have hcont : ContinuousOn (fun s => R y1 θ s) (Set.Icc 0 1) :=
      jet_slice_continuousOn hjet hα hy1nn hθ
    have hInt : IntervalIntegrable (fun s => R y1 θ s) MeasureTheory.volume 0 y2 :=
      ContinuousOn.intervalIntegrable_of_Icc (u := fun s => R y1 θ s) hy2
        (hcont.mono (Set.Icc_subset_Icc le_rfl hy2le1))
    have hid : (∫ s in (0 : ℝ)..y2, R y1 θ s) - R z θ 0 * y2
        = ∫ s in (0 : ℝ)..y2, (R y1 θ s - R z θ 0) := by
      rw [intervalIntegral.integral_sub hInt intervalIntegrable_const,
        intervalIntegral.integral_const]
      rw [sub_zero, smul_eq_mul]
      ring
    rw [hFTC', hid]
    have hC : ∀ s ∈ Set.uIoc (0 : ℝ) y2,
        ‖R y1 θ s - R z θ 0‖ ≤ Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α := by
      intro s hs
      rw [Set.uIoc_of_le hy2] at hs
      have hs1 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, le_trans hs.2 hy2le1⟩
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
      have hb := hjet.2.2 y1 z θ θ s 0 hy1nn hz.le hθ hθ hs1 h0
      simp only [sub_self, abs_zero, add_zero, sub_zero, abs_of_pos hs.1] at hb
      have hle : |y1 - z| + s ≤ 2 * ‖(y1, y2) - (z, (0 : ℝ))‖ := by
        have hs : s ≤ ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          le_trans hs.2 (le_trans (le_abs_self y2) habs2)
        linarith [habs1]
      have hrpow : (|y1 - z| + s) ^ α ≤ (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α :=
        Real.rpow_le_rpow (by linarith [abs_nonneg (y1 - z), hs.1]) hle hα.le
      calc ‖R y1 θ s - R z θ 0‖ = |R y1 θ s - R z θ 0| := Real.norm_eq_abs _
        _ ≤ Nc * (|y1 - z| + s) ^ α := hb
        _ ≤ Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α :=
            mul_le_mul_of_nonneg_left hrpow hNc
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hC
    calc ‖∫ s in (0 : ℝ)..y2, (R y1 θ s - R z θ 0)‖
        ≤ (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * |y2 - 0| := hnorm
      _ = (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * y2 := by
          rw [sub_zero, abs_of_nonneg hy2]
      _ ≤ (Nc * (2 * ‖(y1, y2) - (z, (0 : ℝ))‖) ^ α) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self y2) habs2) (by positivity)
      _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
          mul_le_mul_of_nonneg_right (hδ₂ _ (norm_nonneg _) hr₂) (norm_nonneg _)
  have hdec : g y1 θ y2 - g z θ 0 - D * (y1 - z) - R z θ 0 * y2
      = (g y1 θ 0 - g z θ 0 - D * (y1 - z)) + (g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2) := by
    ring
  calc ‖g y1 θ y2 - g z θ 0 - D * (y1 - z) - R z θ 0 * y2‖
      = ‖(g y1 θ 0 - g z θ 0 - D * (y1 - z))
          + (g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2)‖ := by rw [hdec]
    _ ≤ ‖g y1 θ 0 - g z θ 0 - D * (y1 - z)‖
        + ‖g y1 θ y2 - g y1 θ 0 - R z θ 0 * y2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ + (ε / 2) * ‖(y1, y2) - (z, (0 : ℝ))‖ :=
        add_le_add hzA hkB
    _ = ε * ‖(y1, y2) - (z, (0 : ℝ))‖ := by ring

end Work.FTS_RegExport.RXR1
