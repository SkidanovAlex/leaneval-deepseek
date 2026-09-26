import Mathlib
import Submission.Work.Analysis.RemovableSingularity.logPowGrowthRemovable
import Submission.Work.CKFinal.deriv_zero_of_ray
import Submission.Work.CKFinal.differentiableAt_inv_mul

open Filter Topology

namespace Work.CKFinal

/-- The ray `y ↦ -exp(-2πy)` of the punctured unit disc, viewed in `ℂ`. -/
noncomputable def cuspRay (y : ℝ) : ℂ := -(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ)

lemma norm_cuspRay (y : ℝ) : ‖cuspRay y‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [cuspRay, Complex.ofReal_exp, norm_neg, Complex.norm_exp_ofReal]

lemma cuspRay_ne_zero (y : ℝ) : cuspRay y ≠ 0 := by
  rw [cuspRay]; simp

/-- The ray tends to the origin of `ℂ`, inside the punctured neighbourhood. -/
theorem cuspRay_tendsto :
    Filter.Tendsto cuspRay Filter.atTop (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) := by
  have hray : Filter.Tendsto (fun y : ℝ => -(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))
      Filter.atTop (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) := by
    rw [nhdsWithin, Filter.tendsto_inf]
    refine ⟨?_, ?_⟩
    · have hlin : Tendsto (fun y : ℝ => 2 * Real.pi * y) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
      have h1 : Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      have h2 : Tendsto (fun y : ℝ => (((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))
          atTop (nhds ((0:ℝ):ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa using h2.neg
    · rw [Filter.tendsto_principal]
      filter_upwards with y
      simp
  exact hray

/-- Riemann's removable singularity theorem in the form used below: a function holomorphic on a
punctured disc that grows at most like a power of `|log ‖z‖|` extends holomorphically, and
`limUnder (𝓝[≠] 0) G` is the value of the extension at `0`. -/
theorem cusp_removable_update {G : ℂ → ℂ} {ρ C N : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hG : DifferentiableOn ℂ G (Metric.ball 0 ρ \ {0}))
    (hgr : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ‖G q‖ ≤ C * (1 + |Real.log ‖q‖|) ^ N) :
    Filter.Tendsto G (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) (nhds ((nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ).limUnder G)) ∧
      DifferentiableAt ℂ (Function.update G 0 ((nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ).limUnder G)) 0 := by
  obtain ⟨F, hFdiff, hFeq⟩ :=
    Work.Analysis.RemovableSingularity.logPowGrowthRemovable (G := G) (ρ := ρ) (C := C) (N := N)
      hρ hC hN hG hgr
  have hball : Metric.ball (0:ℂ) ρ ∈ nhds (0:ℂ) :=
    Metric.isOpen_ball.mem_nhds (by simpa using hρ)
  have hball' : Metric.ball (0:ℂ) ρ ∈ nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ :=
    nhdsWithin_le_nhds hball
  have hFd0 : DifferentiableAt ℂ F 0 := hFdiff.differentiableAt hball
  have hev : G =ᶠ[nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ] F := by
    filter_upwards [hball', self_mem_nhdsWithin] with z hz hz0
    have hzlt : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact (hFeq z (by simpa using hz0) hzlt).symm
  have hTend : Tendsto G (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) (nhds (F 0)) :=
    Filter.Tendsto.congr' hev.symm (hFd0.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim : (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ).limUnder G = F 0 := hTend.limUnder_eq
  refine ⟨?_, ?_⟩
  · rw [hlim]; exact hTend
  · rw [hlim]
    refine (Filter.EventuallyEq.differentiableAt_iff ?_).2 hFd0
    filter_upwards [hball] with z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hzlt : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [Function.update_of_ne hz0]
      exact (hFeq z hz0 hzlt).symm

set_option maxHeartbeats 1000000 in
/-- A holomorphic function on the punctured unit disc with at most logarithmic growth which decays
along the ray `q = -exp(-2πy)` extends holomorphically to `0` with value `0` and vanishing
derivative there. -/
theorem cusp_at_zero {F : ℂ → ℂ} {Ke A ℓ : ℝ} (hA : 0 ≤ A) (hℓ : 0 < ℓ)
    (hdiff : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ F q)
    (hgr : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ ℓ → ‖F q‖ ≤ Ke * (1 + |Real.log ‖q‖|) ^ A)
    (hray0 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      ‖F (- Real.exp (-(2 * Real.pi * y)))‖ ≤ ε)
    (hray1 : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      ‖F (- Real.exp (-(2 * Real.pi * y)))‖ ≤ ε * Real.exp (-(2 * Real.pi * y))) :
    DifferentiableAt ℂ (Function.update F 0 (Filter.limUnder (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) F)) 0 ∧
    Filter.limUnder (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) F = 0 ∧
    DifferentiableAt ℂ (Function.update (fun q : ℂ => q⁻¹ * F q) 0 0) 0 := by
  -- radius of the disc on which we apply the removable singularity theorem
  set ρ : ℝ := min ℓ 1 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min hℓ one_pos
  have hρℓ : ρ ≤ ℓ := by rw [hρdef]; exact min_le_left _ _
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact min_le_right _ _
  -- hypotheses of the removable singularity theorem
  have hG : DifferentiableOn ℂ F (Metric.ball 0 ρ \ {0}) := by
    intro q hq
    have hqlt : ‖q‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq.1
    have hqne : q ≠ 0 := by simpa using hq.2
    exact (hdiff q (norm_pos_iff.mpr hqne) (lt_of_lt_of_le hqlt hρ1)).differentiableWithinAt
  have hgr' : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ‖F q‖ ≤ max Ke 0 * (1 + |Real.log ‖q‖|) ^ A := by
    intro q hq0 hqρ
    refine le_trans (hgr q (norm_pos_iff.mpr hq0) (le_trans (le_of_lt hqρ) hρℓ)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left Ke 0) (Real.rpow_nonneg (by positivity) A)
  obtain ⟨hTend, hDiff0⟩ :=
    cusp_removable_update (G := F) (ρ := ρ) (C := max Ke 0) (N := A)
      hρ0 (le_max_right _ _) hA hG hgr'
  -- the two ray hypotheses, as filter limits along `atTop`
  have hray : Tendsto cuspRay atTop (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) := cuspRay_tendsto
  have hray0f : Tendsto (fun y : ℝ => F (cuspRay y)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Y, hY⟩ := hray0 (ε / 2) (by linarith)
    refine ⟨Y, fun y hy => ?_⟩
    rw [dist_eq_norm, sub_zero]
    have h := hY y hy
    simp only [cuspRay] at h ⊢
    linarith
  have hray1f : Tendsto (fun y : ℝ => (cuspRay y)⁻¹ * F (cuspRay y)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Y, hY⟩ := hray1 (ε / 2) (by linarith)
    refine ⟨Y, fun y hy => ?_⟩
    rw [dist_eq_norm, sub_zero]
    have h := hY y hy
    have hnorm : ‖(cuspRay y)⁻¹ * F (cuspRay y)‖
        = ‖F (cuspRay y)‖ / Real.exp (-(2 * Real.pi * y)) := by
      rw [norm_mul, norm_inv, norm_cuspRay, div_eq_mul_inv, mul_comm]
    rw [hnorm]
    have hle : ‖F (cuspRay y)‖ / Real.exp (-(2 * Real.pi * y)) ≤ ε / 2 := by
      simp only [cuspRay] at h ⊢
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith
    linarith
  -- the limiting value at the origin vanishes, by the decay along the ray
  have hlim0 : (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ).limUnder F = 0 :=
    tendsto_nhds_unique (hTend.comp hray) hray0f
  -- the holomorphic extension of `F` across the origin
  set c : ℂ := (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ).limUnder F with hcdef
  have hext0 : Function.update F 0 c 0 = 0 := by simp [hlim0]
  have hext_diff : DifferentiableAt ℂ (Function.update F 0 c) 0 := hDiff0
  have hray1ext : Tendsto (fun y : ℝ => (cuspRay y)⁻¹ * Function.update F 0 c (cuspRay y))
      atTop (nhds 0) := by
    have heq : (fun y : ℝ => (cuspRay y)⁻¹ * Function.update F 0 c (cuspRay y)) =
        fun y : ℝ => (cuspRay y)⁻¹ * F (cuspRay y) := by
      funext y
      rw [Function.update_of_ne (cuspRay_ne_zero y)]
    rw [heq]
    exact hray1f
  -- the decay along the ray forces the derivative of the extension at `0` to vanish, and
  -- `q ↦ q⁻¹ * F̃ q` to tend to `0`
  obtain ⟨hderiv0, hPsiTend⟩ := deriv_zero_of_ray hext0 hext_diff hray1ext
  -- the extension is holomorphic on a punctured neighbourhood of `0`
  have hd : ∀ᶠ q : ℂ in nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ, DifferentiableAt ℂ (Function.update F 0 c) q := by
    have hballmem : Metric.ball (0:ℂ) (min ρ 1) ∈ nhds (0:ℂ) :=
      Metric.isOpen_ball.mem_nhds (by simp [lt_min hρ0 one_pos])
    have hballmem' : Metric.ball (0:ℂ) (min ρ 1) ∈ nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ :=
      nhdsWithin_le_nhds hballmem
    filter_upwards [self_mem_nhdsWithin, hballmem'] with q hqne hq
    have hqlt : ‖q‖ < min ρ 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq
    have hqne' : q ≠ 0 := by simpa using hqne
    have hev : Function.update F 0 c =ᶠ[nhds q] F := by
      filter_upwards [isOpen_ne.mem_nhds hqne'] with z hz
      exact Function.update_of_ne hz c F
    exact (hev.differentiableAt_iff).2
      (hdiff q (norm_pos_iff.mpr hqne') (lt_of_lt_of_le hqlt (min_le_right _ _)))
  have hPsi : DifferentiableAt ℂ (fun q : ℂ => q⁻¹ * Function.update F 0 c q) 0 :=
    differentiableAt_inv_mul hd hPsiTend
  -- `q ↦ q⁻¹ * F q`, corrected at `0`, agrees with `q ↦ q⁻¹ * F̃ q` near `0`
  have hev2 : (fun q : ℂ => q⁻¹ * Function.update F 0 c q) =ᶠ[nhds 0]
      Function.update (fun q : ℂ => q⁻¹ * F q) 0 0 := by
    refine Filter.Eventually.of_forall fun q => ?_
    rcases eq_or_ne q 0 with rfl | hqne
    · simp
    · show q⁻¹ * Function.update F 0 c q = Function.update (fun q : ℂ => q⁻¹ * F q) 0 0 q
      rw [Function.update_of_ne hqne (0:ℂ) (fun q : ℂ => q⁻¹ * F q),
        Function.update_of_ne hqne c F]
  exact ⟨hDiff0, hlim0, (hev2.differentiableAt_iff).1 hPsi⟩

end Work.CKFinal
