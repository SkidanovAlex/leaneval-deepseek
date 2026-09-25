import Mathlib
import Submission.Work.NN.Core.fiberPot

set_option autoImplicit false

noncomputable section

open scoped NNReal ContDiff
open MeasureTheory Set Filter

namespace Work.NN.Core

/-! ## A smooth radial cutoff on `ℂ` -/

/-- The smooth radial cutoff `s ↦ σ(2 - 2‖s‖²/M²)`: `1` where `2‖s‖² ≤ M²`, `0` where `M ≤ ‖s‖`. -/
noncomputable def nnBumpC (M : ℝ) (s : ℂ) : ℂ :=
  (Real.smoothTransition (2 - 2 * ‖s‖ ^ 2 / M ^ 2) : ℂ)

@[simp] lemma nnBumpC_apply (M : ℝ) (s : ℂ) :
    nnBumpC M s = (Real.smoothTransition (2 - 2 * ‖s‖ ^ 2 / M ^ 2) : ℂ) := rfl

lemma contDiff_nnBumpC (M : ℝ) : ContDiff ℝ ∞ (nnBumpC M) := by
  unfold nnBumpC
  refine Complex.ofRealCLM.contDiff.comp ?_
  refine Real.smoothTransition.contDiff.comp ?_
  have h1 : ContDiff ℝ ∞ (fun s : ℂ => ‖s‖ ^ 2) := contDiff_norm_sq ℝ
  fun_prop

lemma nnBumpC_eq_one {M : ℝ} (hM : 0 < M) {s : ℂ} (h : 2 * ‖s‖ ^ 2 ≤ M ^ 2) :
    nnBumpC M s = 1 := by
  unfold nnBumpC
  rw [← Complex.ofReal_one, Complex.ofReal_inj, Real.smoothTransition.eq_one_iff_one_le]
  have h3 : 2 * ‖s‖ ^ 2 / M ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr h
  linarith

lemma nnBumpC_eq_zero {M : ℝ} (hM : 0 < M) {s : ℂ} (h : M ≤ ‖s‖) :
    nnBumpC M s = 0 := by
  have h2 : M ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s, hM]
  have h3 : (2 : ℝ) ≤ 2 * ‖s‖ ^ 2 / M ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  unfold nnBumpC
  rw [← Complex.ofReal_zero, Complex.ofReal_inj, Real.smoothTransition.zero_iff_nonpos]
  linarith

lemma nnBumpC_ne_zero {M : ℝ} (hM : 0 < M) {s : ℂ} (h : nnBumpC M s ≠ 0) :
    ‖s‖ < M := by
  have hpos : 0 < 2 - 2 * ‖s‖ ^ 2 / M ^ 2 := by
    by_contra hc
    exact h (by
      unfold nnBumpC
      rw [← Complex.ofReal_zero, Complex.ofReal_inj, Real.smoothTransition.zero_iff_nonpos]
      push Not at hc; exact hc)
  have hlt : 2 * ‖s‖ ^ 2 / M ^ 2 < 2 := by linarith
  have h2 : 2 * ‖s‖ ^ 2 < 2 * M ^ 2 := by
    rw [div_lt_iff₀ (by positivity)] at hlt; linarith
  nlinarith [norm_nonneg s, hM]

lemma nnBumpC_neg (M : ℝ) (s : ℂ) : nnBumpC M (-s) = nnBumpC M s := by
  unfold nnBumpC; rw [norm_neg]

lemma norm_nnBumpC_le_one (M : ℝ) (s : ℂ) : ‖nnBumpC M s‖ ≤ 1 := by
  rw [nnBumpC_apply]
  rw [show ‖((Real.smoothTransition (2 - 2 * ‖s‖ ^ 2 / M ^ 2)) : ℂ)‖
        = |Real.smoothTransition (2 - 2 * ‖s‖ ^ 2 / M ^ 2)| from by simp]
  rw [abs_le]
  exact ⟨by linarith [Real.smoothTransition.nonneg (2 - 2 * ‖s‖ ^ 2 / M ^ 2)],
         Real.smoothTransition.le_one _⟩

lemma integrable_div_nnBumpC {M : ℝ} (hM : 0 < M) :
    Integrable (fun a : ℂ => nnBumpC M a / a) (volume : Measure ℂ) := by
  have hbase : Integrable (fun a : ℂ => ‖a⁻¹‖)
      ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) M)) := by
    simpa only [sub_zero] using (integrableOn_sub_inv_ball M 0).norm
  have hg : Integrable (fun a : ℂ => (Metric.ball (0 : ℂ) M).indicator (fun a => ‖a⁻¹‖) a)
      (volume : Measure ℂ) :=
    (integrable_indicator_iff measurableSet_ball).mpr hbase
  refine hg.mono' ?_ ?_
  · exact ((contDiff_nnBumpC M).continuous.measurable.div measurable_id).aestronglyMeasurable
  · filter_upwards with a
    by_cases ha : a ∈ Metric.ball (0 : ℂ) M
    · rw [Set.indicator_of_mem ha, norm_div]
      calc ‖nnBumpC M a‖ / ‖a‖ ≤ 1 / ‖a‖ := by gcongr; exact norm_nnBumpC_le_one M a
        _ = ‖a⁻¹‖ := by rw [norm_inv, one_div]
    · rw [Set.indicator_of_notMem ha]
      have h0 : nnBumpC M a = 0 := by
        rw [Metric.mem_ball, dist_zero_right] at ha
        exact nnBumpC_eq_zero hM (not_lt.mp ha)
      rw [h0, zero_div, norm_zero]

/-! ## Quotient by the identity -/

/-- If a `C^∞`-function vanishes on a ball around `0` then its quotient by `s` is `C^∞`. -/
lemma contDiff_div_self_of_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) (h0 : ∀ s : ℂ, ‖s‖ ≤ ε → g s = 0) :
    ContDiff ℝ ∞ (fun s : ℂ => g s / s) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  by_cases hs : ‖s₀‖ ≤ ε / 2
  · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) ?_
    filter_upwards [Metric.ball_mem_nhds s₀ (by linarith : (0 : ℝ) < ε / 2)] with s hs
    have hd : dist s s₀ < ε / 2 := by rwa [Metric.mem_ball] at hs
    have hle : ‖s‖ ≤ ε := le_of_lt (by
      calc ‖s‖ = ‖(s - s₀) + s₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖s - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := by rw [dist_eq_norm] at hd; linarith
        _ = ε := by ring)
    rw [h0 s hle, zero_div]
  · push Not at hs
    have hs0 : s₀ ≠ 0 := by
      intro h; rw [h, norm_zero] at hs; linarith
    have h1 : ContDiffAt ℝ ∞ g s₀ := hg.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun s : ℂ => s⁻¹) s₀ := contDiffAt_inv ℝ hs0
    refine (h1.mul h2).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds s₀ (by linarith : (0 : ℝ) < ε / 2)] with s hs
    rw [div_eq_mul_inv]

/-! ## A convolution helper -/

/-- Smoothness of `z ↦ ∫ a, F a * G z (-a)` for `F` locally integrable and `G` a parametrised
family that is `C^n` jointly and uniformly compactly supported. -/
lemma contDiffOn_integral_conv {n m : ℕ} {F : ℂ → ℂ} (hF : LocallyIntegrable F (volume : Measure ℂ))
    {G : (Fin n → ℂ) → ℂ → ℂ} {s : Set (Fin n → ℂ)} (hs : IsOpen s) {k : Set ℂ} (hk : IsCompact k)
    (hGk : ∀ (z : Fin n → ℂ) (a : ℂ), z ∈ s → a ∉ k → G z a = 0)
    (hG : ContDiffOn ℝ (m : WithTop ℕ∞) (Function.uncurry G) (s ×ˢ (Set.univ : Set ℂ))) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun z => ∫ a : ℂ, F a * G z (-a)) s := by
  have h := MeasureTheory.contDiffOn_convolution_right_with_param
      (𝕜 := ℝ) (L := ContinuousLinearMap.mul ℝ ℂ) (f := F) (g := G)
      (μ := (volume : Measure ℂ)) (s := s) (k := k) hs hk hGk hF hG
  have h2 := h.comp ((contDiffOn_id (E := Fin n → ℂ)).prodMk (contDiffOn_const (c := (0 : ℂ))))
      (fun z hz => ⟨hz, trivial⟩)
  refine h2.congr (fun z _ => ?_)
  show ∫ a : ℂ, F a * G z (-a)
      = convolution F (G z) (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', zero_sub]

/-! ## Smoothness of the coordinate replacements -/

lemma contDiff_update_neg {n : ℕ} (j : Fin n) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j (-p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = j
  · subst hi
    have h : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 i (-p.2) i) = fun p => -p.2 := by
      funext p; rw [Function.update_self]
    rw [h]; fun_prop
  · have h : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j (-p.2) i) = fun p => p.1 i := by
      funext p; rw [Function.update_of_ne hi]
    rw [h]; fun_prop

lemma contDiff_update_sub {n : ℕ} (j : Fin n) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j (p.1 j - p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = j
  · subst hi
    have h : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 i (p.1 i - p.2) i)
        = fun p => p.1 i - p.2 := by
      funext p; rw [Function.update_self]
    rw [h]; fun_prop
  · have h : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j (p.1 j - p.2) i)
        = fun p => p.1 i := by
      funext p; rw [Function.update_of_ne hi]
    rw [h]; fun_prop

/-! ## The main theorem -/

/-- **The fixed-disc potential preserves smoothness on the region where the pole is interior.**

If `u : ℂⁿ → ℂ` is (globally) `C^m` then `fiberPot R j u` is `C^m` on the open set
`{z | ‖z j‖ < R}` (the region where the pole `z j` lies inside the disc of integration).  The
restriction to this region is necessary: for `u ≡ 1` one has `fiberPot = conj (z j)` for
`‖z j‖ < R` and `= R² / z j` for `‖z j‖ > R`, so the function is not `C¹` across `‖z j‖ = R`.

The transverse derivatives pass through the integral (`∂_{z k} fiberPot = fiberPot ∘ ∂_{z k}` for
`k ≠ j`), while each fibre derivative is a Calderón–Zygmund-type singular integral applied to a
lower derivative of `u` (the subtracted kernels `(u(w) - u(z))/(w - z)^k` are integrable because a
`C^m` function is Lipschitz near the pole), so all partial derivatives up to order `m` exist and are
continuous on `‖z j‖ < R`.

This is used to see that the explicit solution operators built from `fiberPot` map smooth data to
smooth data (item (c) of the `(0,2)` interior `∂̄`-Poincaré statement). -/
theorem contDiff_fiberPot {n : ℕ} (R : ℝ) (m : ℕ) (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ m u) :
    ContDiffOn ℝ m (Work.NN.Core.fiberPot R j u) {z : Fin n → ℂ | ‖z j‖ < R} := by
  rcases le_or_gt R 0 with hR | hR
  · have hempty : {z : Fin n → ℂ | ‖z j‖ < R} = ∅ := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hR (norm_nonneg _)
    rw [hempty]; exact contDiffOn_empty
  refine contDiffOn_of_locally_contDiffOn ?_
  intro z₀ hz₀
  have hz₀R : ‖z₀ j‖ < R := hz₀
  set δ : ℝ := (R - ‖z₀ j‖) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith [hz₀R]
  have hz₀δ : ‖z₀ j‖ < R - δ := by rw [hδdef]; linarith
  set s : Set (Fin n → ℂ) := Metric.ball z₀ 1 ∩ {z : Fin n → ℂ | ‖z j‖ < R - δ} with hsdef
  have hs_open : IsOpen s := by
    rw [hsdef]
    exact Metric.isOpen_ball.inter (isOpen_lt (continuous_apply j).norm continuous_const)
  have hz₀s : z₀ ∈ s := by
    rw [hsdef]
    exact ⟨by rw [Metric.mem_ball, dist_self]; norm_num, hz₀δ⟩
  refine ⟨s, hs_open, hz₀s, ?_⟩
  -- the cutoffs
  set χ : ℂ → ℂ := nnBumpC δ with hχdef
  have hχ_smooth : ContDiff ℝ ∞ χ := by rw [hχdef]; exact contDiff_nnBumpC δ
  set φ : ℂ → ℂ := fun t : ℂ => (1 - χ t) / t with hφdef
  have hφ_smooth : ContDiff ℝ ∞ φ := by
    rw [hφdef]
    refine contDiff_div_self_of_eq_zero (ε := δ / 2) (contDiff_const.sub hχ_smooth) (by linarith) ?_
    intro t ht
    rw [sub_eq_zero, hχdef]
    refine (nnBumpC_eq_one hδpos ?_).symm
    have h2 : ‖t‖ ^ 2 ≤ (δ / 2) ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg t) ht; nlinarith [this]
    nlinarith [h2, hδpos]
  set γ : ℂ → ℂ := nnBumpC (2 * R) with hγdef
  have hγ_smooth : ContDiff ℝ ∞ γ := by rw [hγdef]; exact contDiff_nnBumpC _
  set κ : ℂ → ℂ := nnBumpC (2 * δ) with hκdef
  have hκ_smooth : ContDiff ℝ ∞ κ := by rw [hκdef]; exact contDiff_nnBumpC _
  -- the two integrals
  set G₁ : (Fin n → ℂ) → ℂ → ℂ := fun z b =>
    -((Real.pi : ℂ))⁻¹ * (u (Function.update z j (-b)) * (φ (-b - z j) * γ b)) with hG₁def
  have hG₁_smooth : ContDiff ℝ (m : WithTop ℕ∞) (Function.uncurry G₁) := by
    have hfun : Function.uncurry G₁ = fun p : (Fin n → ℂ) × ℂ =>
        -((Real.pi : ℂ))⁻¹ * (u (Function.update p.1 j (-p.2)) * (φ (-p.2 - p.1 j) * γ p.2)) := by
      funext p; simp only [Function.uncurry, hG₁def]
    rw [hfun]
    have h1 : ContDiff ℝ (m : WithTop ℕ∞)
        (fun p : (Fin n → ℂ) × ℂ => u (Function.update p.1 j (-p.2))) :=
      hu.comp ((contDiff_update_neg j).of_le (by simp))
    have h2 : ContDiff ℝ (m : WithTop ℕ∞)
        (fun p : (Fin n → ℂ) × ℂ => φ (-p.2 - p.1 j)) :=
      (hφ_smooth.of_le (by simp)).comp (by fun_prop)
    have h3 : ContDiff ℝ (m : WithTop ℕ∞) (fun p : (Fin n → ℂ) × ℂ => γ p.2) :=
      (hγ_smooth.of_le (by simp)).comp contDiff_snd
    exact (contDiff_const (c := -((Real.pi : ℂ))⁻¹)).mul (h1.mul (h2.mul h3))
  set G₂ : (Fin n → ℂ) → ℂ → ℂ := fun z b =>
    u (Function.update z j (z j - b)) * κ b with hG₂def
  have hG₂_smooth : ContDiff ℝ (m : WithTop ℕ∞) (Function.uncurry G₂) := by
    have hfun : Function.uncurry G₂ = fun p : (Fin n → ℂ) × ℂ =>
        u (Function.update p.1 j (p.1 j - p.2)) * κ p.2 := by
      funext p; simp only [Function.uncurry, hG₂def]
    rw [hfun]
    have h1 : ContDiff ℝ (m : WithTop ℕ∞)
        (fun p : (Fin n → ℂ) × ℂ => u (Function.update p.1 j (p.1 j - p.2))) :=
      hu.comp ((contDiff_update_sub j).of_le (by simp))
    have h2 : ContDiff ℝ (m : WithTop ℕ∞) (fun p : (Fin n → ℂ) × ℂ => κ p.2) :=
      (hκ_smooth.of_le (by simp)).comp contDiff_snd
    exact h1.mul h2
  set T₁ : (Fin n → ℂ) → ℂ :=
    fun z => ∫ a : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun _ => (1 : ℂ)) a * G₁ z (-a)
    with hT₁def
  set T₂ : (Fin n → ℂ) → ℂ :=
    fun z => ∫ a : ℂ, (-((Real.pi : ℂ))⁻¹ * χ a / a) * G₂ z (-a) with hT₂def
  have hT₁ : ContDiffOn ℝ (m : WithTop ℕ∞) T₁ s := by
    rw [hT₁def]
    refine contDiffOn_integral_conv (F := (Metric.ball (0 : ℂ) R).indicator (fun _ => (1 : ℂ)))
      ((locallyIntegrable_const (1 : ℂ)).indicator measurableSet_ball) hs_open
      (isCompact_closedBall 0 (2 * R)) ?_ hG₁_smooth.contDiffOn
    intro z a hz ha
    have ha' : 2 * R ≤ ‖a‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at ha
      exact le_of_lt (not_le.mp ha)
    simp only [hG₁def, hγdef, nnBumpC_eq_zero (M := 2 * R) (by linarith) ha', mul_zero]
  have hF₂_int : Integrable (fun a : ℂ => χ a / a) (volume : Measure ℂ) := by
    rw [hχdef]; exact integrable_div_nnBumpC hδpos
  have hT₂ : ContDiffOn ℝ (m : WithTop ℕ∞) T₂ s := by
    rw [hT₂def]
    refine contDiffOn_integral_conv (F := fun a : ℂ => -((Real.pi : ℂ))⁻¹ * χ a / a)
      ?_ hs_open (isCompact_closedBall 0 (2 * δ)) ?_ hG₂_smooth.contDiffOn
    · have h1 : Integrable (fun a : ℂ => -((Real.pi : ℂ))⁻¹ * χ a / a) (volume : Measure ℂ) := by
        have h2 : Integrable (fun a : ℂ => -((Real.pi : ℂ))⁻¹ * (χ a / a)) (volume : Measure ℂ) :=
          hF₂_int.const_mul _
        simpa only [mul_div_assoc] using h2
      exact h1.locallyIntegrable
    · intro z a hz ha
      have ha' : 2 * δ ≤ ‖a‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at ha
        exact le_of_lt (not_le.mp ha)
      simp only [hG₂def, hκdef, nnBumpC_eq_zero (M := 2 * δ) (by linarith) ha', mul_zero]
  have hsum : ContDiffOn ℝ (m : WithTop ℕ∞) (fun z => T₁ z + T₂ z) s := hT₁.add hT₂
  -- the pointwise identity
  have hkey : ∀ z ∈ s, fiberPot R j u z = T₁ z + T₂ z := by
    intro z hz
    have hz1 : ‖z j‖ < R - δ := hz.2
    have hζR : ‖z j‖ < R := by linarith
    have hcont_u : Continuous fun t : ℂ => u (Function.update z j t) :=
      hu.continuous.comp (continuous_update z j)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hcont_u.continuousOn
    -- integrability of the pieces on the disc
    have hcont_f1 : Continuous fun t : ℂ => u (Function.update z j t) * φ (t - z j) :=
      hcont_u.mul (hφ_smooth.continuous.comp (continuous_id.sub continuous_const))
    have hInt1 : IntegrableOn (fun t : ℂ => u (Function.update z j t) * φ (t - z j))
        (Metric.ball (0 : ℂ) R) :=
      (hcont_f1.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)).mono_set
        Metric.ball_subset_closedBall
    have hInt2 : IntegrableOn
        (fun t : ℂ => u (Function.update z j t) * (χ (t - z j) / (t - z j)))
        (Metric.ball (0 : ℂ) R) := by
      have hg : Integrable (fun t : ℂ => M * ‖(t - z j)⁻¹‖)
          ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) R)) :=
        (integrableOn_sub_inv_ball R (z j)).norm.const_mul M
      refine hg.mono' ?_ ?_
      · have hm : Measurable (fun t : ℂ => χ (t - z j) / (t - z j)) :=
          (hχ_smooth.continuous.measurable.comp (measurable_id.sub measurable_const)).div
            (measurable_id.sub measurable_const)
        exact (hcont_u.measurable.mul hm).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_ball] with t ht
        have htR : ‖t‖ ≤ R := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at ht)
        have hb : ‖u (Function.update z j t)‖ ≤ M := hM t (Metric.ball_subset_closedBall ht)
        have hχ1 : ‖χ (t - z j)‖ ≤ 1 := by rw [hχdef]; exact norm_nnBumpC_le_one δ _
        calc ‖u (Function.update z j t) * (χ (t - z j) / (t - z j))‖
            = ‖u (Function.update z j t)‖ * (‖χ (t - z j)‖ * ‖(t - z j)⁻¹‖) := by
              rw [norm_mul, norm_div, norm_inv, div_eq_mul_inv]
          _ ≤ M * (1 * ‖(t - z j)⁻¹‖) := by
              have hXM : 0 ≤ M := le_trans (norm_nonneg _) hb
              have hX : ‖χ (t - z j)‖ * ‖(t - z j)⁻¹‖ ≤ 1 * ‖(t - z j)⁻¹‖ :=
                mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _)
              exact mul_le_mul hb hX (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hXM
          _ = M * ‖(t - z j)⁻¹‖ := by ring
    -- splitting the integral
    have hφχ : ∀ t : ℂ, φ (t - z j) + χ (t - z j) / (t - z j) = (t - z j)⁻¹ := by
      intro t
      rw [hφdef, ← add_div]
      simp only [sub_add_cancel, one_div]
    have hsplit : ∫ t in Metric.ball (0 : ℂ) R, u (Function.update z j t) / (t - z j)
        = (∫ t in Metric.ball (0 : ℂ) R, u (Function.update z j t) * φ (t - z j))
          + (∫ t in Metric.ball (0 : ℂ) R,
              u (Function.update z j t) * (χ (t - z j) / (t - z j))) := by
      rw [← MeasureTheory.integral_add (μ := (volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) R))
        hInt1 hInt2]
      refine setIntegral_congr_fun measurableSet_ball (fun t _ => ?_)
      rw [← mul_add, hφχ t, div_eq_mul_inv]
    -- the first integral is `T₁`
    have hT₁eq : T₁ z
        = -((Real.pi : ℂ))⁻¹ * ∫ t in Metric.ball (0 : ℂ) R,
            u (Function.update z j t) * φ (t - z j) := by
      simp only [hT₁def]
      have h1 : (∫ a : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun _ => (1 : ℂ)) a * G₁ z (-a))
          = ∫ a : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun a => G₁ z (-a)) a := by
        refine integral_congr_ae ?_
        filter_upwards with a
        by_cases ha : a ∈ Metric.ball (0 : ℂ) R
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, one_mul]
        · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]
      rw [h1, MeasureTheory.integral_indicator measurableSet_ball]
      have e2 : ∀ a ∈ Metric.ball (0 : ℂ) R,
          G₁ z (-a) = -((Real.pi : ℂ))⁻¹ * (u (Function.update z j a) * φ (a - z j)) := by
        intro a ha
        simp only [hG₁def, neg_neg]
        have hγ : γ (-a) = 1 := by
          rw [hγdef, nnBumpC_neg]
          refine nnBumpC_eq_one (by linarith) ?_
          have haR : ‖a‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at ha
          nlinarith [norm_nonneg a, haR, hR]
        rw [hγ, mul_one]
      rw [setIntegral_congr_fun measurableSet_ball e2, MeasureTheory.integral_const_mul]
    -- the second integral is `T₂`
    have hT₂eq : T₂ z
        = -((Real.pi : ℂ))⁻¹ * ∫ t in Metric.ball (0 : ℂ) R,
            u (Function.update z j t) * (χ (t - z j) / (t - z j)) := by
      simp only [hT₂def]
      have h1 : (∫ a : ℂ, (-((Real.pi : ℂ))⁻¹ * χ a / a) * G₂ z (-a))
          = ∫ a : ℂ, -((Real.pi : ℂ))⁻¹ *
              (u (Function.update z j (z j + a)) * (χ a / a)) := by
        refine integral_congr_ae ?_
        filter_upwards with a
        simp only [hG₂def, sub_neg_eq_add]
        by_cases ha : χ a = 0
        · rw [ha]; ring
        · have hκ : κ (-a) = 1 := by
            rw [hκdef, nnBumpC_neg]
            refine nnBumpC_eq_one (by linarith) ?_
            have haδ : ‖a‖ < δ := by
              rw [hχdef] at ha; exact nnBumpC_ne_zero hδpos ha
            nlinarith [norm_nonneg a, haδ, hδpos]
          rw [hκ, mul_one]
          ring
      rw [h1, MeasureTheory.integral_const_mul]
      congr 1
      have hzero : ∀ t : ℂ, t ∉ Metric.ball (0 : ℂ) R →
          u (Function.update z j t) * (χ (t - z j) / (t - z j)) = 0 := by
        intro t ht
        rw [Metric.mem_ball, dist_zero_right] at ht
        have htR : R ≤ ‖t‖ := not_lt.mp ht
        have hδR : δ ≤ R - ‖z j‖ := by rw [hδdef]; linarith
        have hδt : δ ≤ ‖t - z j‖ := by
          calc δ ≤ R - ‖z j‖ := hδR
            _ ≤ ‖t‖ - ‖z j‖ := by linarith
            _ ≤ ‖t - z j‖ := norm_sub_norm_le t (z j)
        have hχ0 : χ (t - z j) = 0 := by rw [hχdef]; exact nnBumpC_eq_zero hδpos hδt
        rw [hχ0, zero_div, mul_zero]
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        ← MeasureTheory.integral_add_left_eq_self
          (fun t : ℂ => u (Function.update z j t) * (χ (t - z j) / (t - z j))) (z j)]
      refine integral_congr_ae ?_
      filter_upwards with a
      simp only [add_sub_cancel_left]
    rw [fiberPot_apply, hsplit, hT₁eq, hT₂eq]
    ring
  have hOnS : ContDiffOn ℝ (m : WithTop ℕ∞) (fiberPot R j u) s := hsum.congr hkey
  exact hOnS.mono Set.inter_subset_right

end Work.NN.Core
