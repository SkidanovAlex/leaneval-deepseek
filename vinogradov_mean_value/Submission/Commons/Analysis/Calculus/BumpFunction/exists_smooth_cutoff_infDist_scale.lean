import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Commons.Analysis.Calculus.BumpFunction.contDiff_eq_one_on_isCompact_tsupport_subset

namespace Commons.Analysis.Calculus.BumpFunction

open scoped ContDiff ENNReal Topology Convolution
open Set Metric MeasureTheory Filter

section ConvolutionInfrastructure

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [SFinite μ] [μ.IsAddLeftInvariant]

/-- The `j`-th iterated derivative of a convolution (with respect to scalar multiplication)
with a smooth compactly supported function is the convolution with the `j`-th iterated
derivative of the kernel. -/
theorem iteratedFDeriv_convolution_lsmul
    {f g : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) g) (hcg : HasCompactSupport g) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) y)
      = fun x => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
                    (fun y => iteratedFDeriv ℝ j g y)) x := by
  induction j with
  | zero =>
    funext x
    apply (continuousMultilinearCurryFin0 ℝ X ℝ).injective
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
    rw [convolution_lsmul, convolution_lsmul]
    refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans
      (LinearIsometry.integral_comp_comm (continuousMultilinearCurryFin0 ℝ X ℝ).toLinearIsometry
        (fun t => f t • (continuousMultilinearCurryFin0 ℝ X ℝ).symm (g (x - t))))
    show f t • g (x - t)
        = (continuousMultilinearCurryFin0 ℝ X ℝ)
            (f t • (continuousMultilinearCurryFin0 ℝ X ℝ).symm (g (x - t)))
    rw [map_smul, LinearIsometryEquiv.apply_symm_apply]
  | succ j ih =>
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
    set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => X) ℝ with he
    set Gj : X → (X [×j]→L[ℝ] ℝ) := fun y => iteratedFDeriv ℝ j g y with hGj
    set Gs : X → (X [×j+1]→L[ℝ] ℝ) := fun y => iteratedFDeriv ℝ (j + 1) g y with hGs
    have hcs : HasCompactSupport Gj := by
      rw [hGj]; exact hcg.iteratedFDeriv (𝕜 := ℝ) j
    have hc1 : ContDiff ℝ 1 Gj := by
      rw [hGj]
      exact hg.iteratedFDeriv_right (m := (1 : ℕ∞ω)) (i := j)
        (by exact_mod_cast (show (1 : ℕ∞) + j ≤ ⊤ from le_top))
    have hfdG : fderiv ℝ Gj = ⇑e ∘ Gs := by
      rw [hGj, hGs, he]
      exact fderiv_iteratedFDeriv
    have hfd := (hcs.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hc1 x).fderiv
    rw [hfd, hfdG]
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    conv_lhs => rw [convolution_def]
    conv_rhs => rw [convolution_lsmul]
    have hpull : (∫ t, e (f t • Gs (x - t)) ∂μ) = e (∫ t, f t • Gs (x - t) ∂μ) :=
      @LinearIsometry.integral_comp_comm X (X [×j+1]→L[ℝ] ℝ) (X →L[ℝ] (X [×j]→L[ℝ] ℝ)) _ μ ℝ
        _ _ _ _ _ _ _ _ _ e.toLinearIsometry (fun t => f t • Gs (x - t))
    refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans hpull
    rw [Function.comp_apply]
    ext z w
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply,
      smul_apply, map_smul]

end ConvolutionInfrastructure

section ConvolutionNormBound

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

/-- If `‖f‖ ≤ 1` pointwise and `g` is integrable, the convolution with respect to scalar
multiplication is bounded by `∫ y, ‖g y‖`. -/
theorem norm_convolution_lsmul_le_integral {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [CompleteSpace M] {f : X → ℝ} {g : X → M} (hf : ∀ t, ‖f t‖ ≤ 1) (hg : Integrable g μ)
    (x : X) :
    ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x‖ ≤ ∫ y, ‖g y‖ ∂μ := by
  rw [convolution_lsmul]
  calc ‖∫ t, f t • g (x - t) ∂μ‖
      ≤ ∫ t, ‖f t • g (x - t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖g (x - t)‖ ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          ((hg.comp_sub_left x).norm) (Eventually.of_forall fun t => ?_)
        show ‖f t • g (x - t)‖ ≤ ‖g (x - t)‖
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hf t)
    _ = ∫ t, ‖g t‖ ∂μ := integral_sub_left_eq_self (fun t => ‖g t‖) μ x

end ConvolutionNormBound

section ScalingBound

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  [FiniteDimensional ℝ X] {μ : Measure X} [μ.IsAddHaarMeasure]

/-- Scaling of the `L¹` norm of the `j`-th iterated derivative of `x ↦ Φ (s⁻¹ • x)`. -/
theorem integral_norm_iteratedFDeriv_comp_inv_smul (Φ : X → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ) (j : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ y, ‖iteratedFDeriv ℝ j (fun x => Φ (s⁻¹ • x)) y‖ ∂μ
      = s ^ Module.finrank ℝ X * (s⁻¹) ^ j * ∫ y, ‖iteratedFDeriv ℝ j Φ y‖ ∂μ := by
  have hsj : (0:ℝ) ≤ (s⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr hs.le) j
  have hpoint : ∀ y, ‖iteratedFDeriv ℝ j (fun x => Φ (s⁻¹ • x)) y‖
      = (s⁻¹) ^ j * ‖iteratedFDeriv ℝ j Φ (s⁻¹ • y)‖ := by
    intro y
    rw [iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := Φ) (i := j) s⁻¹
      (hΦ.of_le (by exact_mod_cast le_top))]
    rw [norm_smul, Real.norm_of_nonneg hsj]
  have hmain : (∫ a : X, ‖iteratedFDeriv ℝ j Φ (s⁻¹ • a)‖ ∂μ)
      = s ^ Module.finrank ℝ X * ∫ y, ‖iteratedFDeriv ℝ j Φ y‖ ∂μ := by
    have := Measure.integral_comp_inv_smul_of_nonneg (μ := μ)
      (f := fun y : X => ‖iteratedFDeriv ℝ j Φ y‖) (R := s) hs.le
    simpa using this
  simp only [hpoint]
  rw [MeasureTheory.integral_const_mul, hmain]
  ring

end ScalingBound

section MainTheorem

open scoped ContDiff ENNReal Topology in
theorem exists_smooth_cutoff_infDist_scale {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (K : Set X) :
    ∃ θ : ℝ → X → ℝ,
      (∀ r : ℝ, 0 < r → ContDiff ℝ (⊤ : ℕ∞) (θ r)) ∧
      (∀ r : ℝ, 0 < r → ∀ x, 0 ≤ θ r x ∧ θ r x ≤ 1) ∧
      (∀ r : ℝ, 0 < r → ∀ x, Metric.infDist x Kᶜ ≤ r → θ r x = 0) ∧
      (∀ r : ℝ, 0 < r → ∀ x, 3 * r < Metric.infDist x Kᶜ → θ r x = 1) ∧
      (∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ x,
        ‖iteratedFDeriv ℝ j (θ r) x‖ ≤ A / r ^ j) := by
  classical
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  haveI : ProperSpace X := FiniteDimensional.proper ℝ X
  haveI : LocallyCompactSpace X := inferInstance
  let μ : Measure X := Measure.addHaar
  haveI hμ : μ.IsAddHaarMeasure := inferInstance
  haveI : μ.IsAddLeftInvariant := inferInstance
  haveI : μ.IsNegInvariant := inferInstance
  haveI : SigmaFinite μ := inferInstance
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasureOnCompacts μ := inferInstance
  -- the fixed profile function
  let b : ContDiffBump (0 : X) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let Ψ : X → ℝ := b.normed μ
  have hΨcd : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) Ψ := b.contDiff_normed
  have hΨcs : HasCompactSupport Ψ := b.hasCompactSupport_normed
  have hΨint : ∫ z, Ψ z ∂μ = 1 := b.integral_normed
  have hΨnn : ∀ z, 0 ≤ Ψ z := fun z => b.nonneg_normed z
  have hΨz : ∀ z, (1 / 2 : ℝ) ≤ ‖z‖ → Ψ z = 0 := by
    intro z hz
    simp only [Ψ, ContDiffBump.normed_def]
    rw [div_eq_zero_iff]
    exact Or.inl (b.zero_of_le_dist (by simpa [b, dist_eq_norm] using hz))
  -- the distance function and the auxiliary data
  let d : X → ℝ := fun x => Metric.infDist x Kᶜ
  have hdcont : Continuous d := Metric.continuous_infDist_pt Kᶜ
  let h : ℝ → X → ℝ := fun r x => max 0 (min 1 ((d x - 3 * r / 2) / r))
  let s : ℝ → ℝ := fun r => r / 4
  let κ : ℝ → X → ℝ := fun r x => (s r ^ Module.finrank ℝ X)⁻¹ * Ψ ((s r)⁻¹ • x)
  let θ : ℝ → X → ℝ := fun r => h r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] κ r
  have hs_pos : ∀ r : ℝ, 0 < r → 0 < s r := fun r hr => by
    show 0 < r / 4
    linarith
  have hh_bdd : ∀ r x, 0 ≤ h r x ∧ h r x ≤ 1 := by
    intro r x
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hh_zero : ∀ r x, 0 < r → d x ≤ 3 * r / 2 → h r x = 0 := by
    intro r x _ hx
    have hle : (d x - 3 * r / 2) / r ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    show max 0 (min 1 ((d x - 3 * r / 2) / r)) = 0
    rw [min_eq_right (hle.trans zero_le_one), max_eq_left hle]
  have hh_one : ∀ r x, 0 < r → 5 * r / 2 ≤ d x → h r x = 1 := by
    intro r x hr hx
    have hge : 1 ≤ (d x - 3 * r / 2) / r := by
      rw [le_div_iff₀ hr]; linarith
    show max 0 (min 1 ((d x - 3 * r / 2) / r)) = 1
    rw [min_eq_left hge, max_eq_right zero_le_one]
  have hh_cont : ∀ r, Continuous (h r) := by
    intro r
    show Continuous fun x : X => max 0 (min 1 ((d x - 3 * r / 2) / r))
    exact continuous_const.max
      (continuous_const.min ((hdcont.sub continuous_const).div_const r))
  have hκz : ∀ r, 0 < r → ∀ z, (1 / 2) * s r ≤ ‖z‖ → κ r z = 0 := by
    intro r hr z hz
    have hs : 0 < s r := hs_pos r hr
    have h1 : (1 / 2 : ℝ) ≤ ‖(s r)⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
      calc (1 / 2 : ℝ) = (s r)⁻¹ * ((1 / 2) * s r) := by field_simp
        _ ≤ (s r)⁻¹ * ‖z‖ := by
            exact mul_le_mul_of_nonneg_left hz (le_of_lt (inv_pos.mpr hs))
    show (s r ^ Module.finrank ℝ X)⁻¹ * Ψ ((s r)⁻¹ • z) = 0
    rw [hΨz _ h1, mul_zero]
  have hκnn : ∀ r, 0 < r → ∀ z, 0 ≤ κ r z := by
    intro r hr z
    have hs : 0 < s r := hs_pos r hr
    show 0 ≤ (s r ^ Module.finrank ℝ X)⁻¹ * Ψ ((s r)⁻¹ • z)
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _)) (hΨnn _)
  have hκcd : ∀ r, 0 < r → ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (κ r) := by
    intro r hr
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun x : X => Ψ ((s r)⁻¹ • x)) :=
      hΨcd.comp (contDiff_id.const_smul (s r)⁻¹)
    have h2 := h1.const_smul ((s r ^ Module.finrank ℝ X)⁻¹)
    simpa only [κ, smul_eq_mul] using h2
  have hκcs : ∀ r, 0 < r → HasCompactSupport (κ r) := by
    intro r hr
    have hs : 0 < s r := hs_pos r hr
    have h0 : HasCompactSupport (fun x : X => Ψ ((s r)⁻¹ • x)) :=
      hΨcs.comp_smul (c := (s r)⁻¹) (ne_of_gt (inv_pos.mpr hs))
    have h1 := h0.comp_left (g := fun y : ℝ => (s r ^ Module.finrank ℝ X)⁻¹ * y) (by ring)
    simpa only [κ, Function.comp_def] using h1
  have hκint : ∀ r, 0 < r → ∫ z, κ r z ∂μ = 1 := by
    intro r hr
    have hs : 0 < s r := hs_pos r hr
    have h1 : (∫ z, κ r z ∂μ)
        = (s r ^ Module.finrank ℝ X)⁻¹ * ∫ z, Ψ ((s r)⁻¹ • z) ∂μ := by
      simp only [κ, integral_const_mul]
    rw [h1]
    have h2 : (∫ z, Ψ ((s r)⁻¹ • z) ∂μ) = s r ^ Module.finrank ℝ X * ∫ z, Ψ z ∂μ := by
      have hh := Measure.integral_comp_inv_smul_of_nonneg (μ := μ) (f := Ψ) (R := s r) hs.le
      simpa using hh
    rw [h2, hΨint, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hs.ne')]
  have hκintabs : ∀ r, 0 < r → Integrable (κ r) μ := fun r hr =>
    ((hκcd r hr).continuous).integrable_of_hasCompactSupport (hκcs r hr)
  refine ⟨θ, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (hκcs r hr).contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((hh_cont r).locallyIntegrable) (hκcd r hr)
  · intro r hr x
    constructor
    · show 0 ≤ (h r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] κ r) x
      rw [convolution_lsmul]
      exact integral_nonneg fun t => mul_nonneg (hh_bdd r t).1 (hκnn r hr (x - t))
    · have hb := norm_convolution_lsmul_le_integral (μ := μ) (f := h r) (g := κ r)
        (fun t => by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hh_bdd r t).1], (hh_bdd r t).2⟩) (hκintabs r hr) x
      have h2 : ∫ y, ‖κ r y‖ ∂μ = 1 := by
        rw [funext fun y => Real.norm_of_nonneg (hκnn r hr y), hκint r hr]
      refine le_trans (le_abs_self (θ r x)) ?_
      rw [Real.norm_eq_abs] at hb
      rwa [← h2]
  · intro r hr x hx
    have hzero : θ r x = ∫ t, h r t * κ r (x - t) ∂μ := by
      show (h r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] κ r) x = _
      rw [convolution_lsmul]
      simp only [smul_eq_mul]
    rw [hzero]
    have hzero' : (∫ t, h r t * κ r (x - t) ∂μ) = ∫ t, (0 : ℝ) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show h r t * κ r (x - t) = (0 : ℝ)
      by_cases hκ : κ r (x - t) = 0
      · rw [hκ, mul_zero]
      · have hlt : ‖x - t‖ < (1 / 2) * s r := by
          by_contra hcon
          exact hκ (hκz r hr (x - t) (not_lt.mp hcon))
        have hdt : d t < 3 * r / 2 := by
          have h3 : d t ≤ d x + dist x t := by
            simpa [d, dist_comm] using
              (Metric.infDist_le_infDist_add_dist (x := t) (y := x) (s := Kᶜ))
          rw [dist_eq_norm] at h3
          rw [show s r = r / 4 from rfl] at hlt
          linarith
        rw [hh_zero r t hr hdt.le, zero_mul]
    rw [hzero', integral_zero]
  · intro r hr x hx
    have hone : θ r x = ∫ t, h r t * κ r (x - t) ∂μ := by
      show (h r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] κ r) x = _
      rw [convolution_lsmul]
      simp only [smul_eq_mul]
    rw [hone]
    have hone' : (∫ t, h r t * κ r (x - t) ∂μ) = ∫ t, κ r (x - t) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show h r t * κ r (x - t) = κ r (x - t)
      by_cases hκ : κ r (x - t) = 0
      · rw [hκ, mul_zero]
      · have hlt : ‖x - t‖ < (1 / 2) * s r := by
          by_contra hcon
          exact hκ (hκz r hr (x - t) (not_lt.mp hcon))
        have hdt : 5 * r / 2 ≤ d t := by
          have h3 : d x ≤ d t + dist x t := by
            simpa [d] using
              (Metric.infDist_le_infDist_add_dist (x := x) (y := t) (s := Kᶜ))
          rw [dist_eq_norm] at h3
          rw [show s r = r / 4 from rfl] at hlt
          linarith
        rw [hh_one r t hr hdt, one_mul]
    rw [hone', integral_sub_left_eq_self (κ r) μ x, hκint r hr]
  · intro j
    refine ⟨max (4 ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ) 1, lt_max_of_lt_right one_pos, ?_⟩
    intro r hr x
    have hs : 0 < s r := hs_pos r hr
    have hκd : ∫ y, ‖iteratedFDeriv ℝ j (κ r) y‖ ∂μ
        = ((s r)⁻¹) ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ := by
      have hstep : ∀ y, ‖iteratedFDeriv ℝ j (κ r) y‖
          = (s r ^ Module.finrank ℝ X)⁻¹
            * ‖iteratedFDeriv ℝ j (fun x : X => Ψ ((s r)⁻¹ • x)) y‖ := by
        intro y
        have hcd : ContDiffAt ℝ (↑j) (fun x : X => Ψ ((s r)⁻¹ • x)) y :=
          ((hΨcd.comp (contDiff_id.const_smul (s r)⁻¹)).of_le
            (by exact_mod_cast le_top)).contDiffAt
        rw [show κ r = (s r ^ Module.finrank ℝ X)⁻¹
              • (fun x : X => Ψ ((s r)⁻¹ • x)) from rfl]
        rw [iteratedFDeriv_const_smul_apply hcd]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))]
      simp only [hstep]
      rw [MeasureTheory.integral_const_mul,
        integral_norm_iteratedFDeriv_comp_inv_smul (μ := μ) Ψ hΨcd j hs]
      have hsn : s r ^ Module.finrank ℝ X ≠ 0 := pow_ne_zero _ hs.ne'
      field_simp
    have hint : Integrable (fun y => iteratedFDeriv ℝ j (κ r) y) μ :=
      ((hκcd r hr).continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
        ((hκcs r hr).iteratedFDeriv (𝕜 := ℝ) j)
    have hb := norm_convolution_lsmul_le_integral (μ := μ) (f := h r)
      (g := fun y => iteratedFDeriv ℝ j (κ r) y)
      (fun t => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [(hh_bdd r t).1], (hh_bdd r t).2⟩) hint x
    have hid := congrArg (fun z => ‖z‖) (congrFun (iteratedFDeriv_convolution_lsmul (μ := μ)
      (f := h r) (g := κ r) ((hh_cont r).locallyIntegrable) (hκcd r hr) (hκcs r hr) j) x)
    calc ‖iteratedFDeriv ℝ j (θ r) x‖
        = ‖(h r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
            (fun y => iteratedFDeriv ℝ j (κ r) y)) x‖ := hid
      _ ≤ ∫ y, ‖iteratedFDeriv ℝ j (κ r) y‖ ∂μ := hb
      _ = ((s r)⁻¹) ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ := hκd
      _ = (4 / r) ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ := by
          rw [show s r = r / 4 from rfl, inv_div]
      _ = (4 ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ) / r ^ j := by
          rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ max (4 ^ j * ∫ y, ‖iteratedFDeriv ℝ j Ψ y‖ ∂μ) 1 / r ^ j := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end MainTheorem

end Commons.Analysis.Calculus.BumpFunction