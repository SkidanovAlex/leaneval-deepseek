import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.dW_limits
import Submission.Work.Beltrami.contDiff_cauchyT
import Submission.Work.Beltrami.dW_cauchyT_eq_beurling_radial
import Submission.Work.Beltrami.dbarW_cauchyT
import Submission.Work.Beltrami.beurling_schauder_uniform
import Submission.Work.Beltrami.cauchyT_decay
import Submission.Work.Beltrami.mollification_holder_approx
import Submission.Work.Beltrami.tendsto_beurling_of_tendsto
import Submission.Work.Beltrami.memLp_of_bounded_supported

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff Topology
open Work.Beltrami

noncomputable section

/-! ## Elementary algebra of the `∂`-coefficients -/

/-- The difference of the squared norms of the `∂`- and `∂̄`-coefficients of a real-linear map is
the Jacobian determinant of that map. -/
lemma normSq_dzCoeff_sub_dzbarCoeff (L : ℂ →L[ℝ] ℂ) :
    ‖dzCoeff L‖ ^ 2 - ‖dzbarCoeff L‖ ^ 2
      = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  have h1 : (dzCoeff L).re = ((L 1).re + (L Complex.I).im) / 2 := by
    simp only [dzCoeff]
    rw [Complex.div_re]
    norm_num [Complex.normSq, Complex.I_mul_I]
    ring
  have h2 : (dzCoeff L).im = ((L 1).im - (L Complex.I).re) / 2 := by
    simp only [dzCoeff]
    rw [Complex.div_im]
    norm_num [Complex.normSq, Complex.I_mul_I]
    ring
  have h3 : (dzbarCoeff L).re = ((L 1).re - (L Complex.I).im) / 2 := by
    simp only [dzbarCoeff]
    rw [Complex.div_re]
    norm_num [Complex.normSq, Complex.I_mul_I]
    ring
  have h4 : (dzbarCoeff L).im = ((L 1).im + (L Complex.I).re) / 2 := by
    simp only [dzbarCoeff]
    rw [Complex.div_im]
    norm_num [Complex.normSq, Complex.I_mul_I]
    ring
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, h1, h2, h3, h4]
  ring

/-- The `∂`-coefficient is bounded by the operator norm. -/
lemma norm_dzCoeff_le (L : ℂ →L[ℝ] ℂ) : ‖dzCoeff L‖ ≤ ‖L‖ := by
  rw [dzCoeff, div_eq_mul_inv]
  calc ‖(L 1 - Complex.I * L Complex.I) * (2:ℂ)⁻¹‖
      = ‖L 1 - Complex.I * L Complex.I‖ * ‖(2:ℂ)⁻¹‖ := norm_mul _ _
    _ ≤ (‖L 1‖ + ‖Complex.I * L Complex.I‖) * ‖(2:ℂ)⁻¹‖ := by
        refine mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (‖L‖ + ‖L‖) * (2:ℝ)⁻¹ := by
        have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using ContinuousLinearMap.le_opNorm L 1
        have h2 : ‖Complex.I * L Complex.I‖ ≤ ‖L‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
          calc ‖L Complex.I‖ ≤ ‖L‖ * ‖Complex.I‖ := ContinuousLinearMap.le_opNorm L Complex.I
            _ = ‖L‖ := by rw [Complex.norm_I, mul_one]
        have h3 : ‖((2:ℂ)⁻¹)‖ = (2:ℝ)⁻¹ := by
          rw [norm_inv]; norm_num
        rw [h3]
        gcongr
    _ = ‖L‖ := by ring

/-- The `∂̄`-coefficient is bounded by the operator norm. -/
lemma norm_dzbarCoeff_le (L : ℂ →L[ℝ] ℂ) : ‖dzbarCoeff L‖ ≤ ‖L‖ := by
  rw [dzbarCoeff, div_eq_mul_inv]
  calc ‖(L 1 + Complex.I * L Complex.I) * (2:ℂ)⁻¹‖
      = ‖L 1 + Complex.I * L Complex.I‖ * ‖(2:ℂ)⁻¹‖ := norm_mul _ _
    _ ≤ (‖L 1‖ + ‖Complex.I * L Complex.I‖) * ‖(2:ℂ)⁻¹‖ := by
        refine mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ ≤ (‖L‖ + ‖L‖) * (2:ℝ)⁻¹ := by
        have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using ContinuousLinearMap.le_opNorm L 1
        have h2 : ‖Complex.I * L Complex.I‖ ≤ ‖L‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
          calc ‖L Complex.I‖ ≤ ‖L‖ * ‖Complex.I‖ := ContinuousLinearMap.le_opNorm L Complex.I
            _ = ‖L‖ := by rw [Complex.norm_I, mul_one]
        have h3 : ‖((2:ℂ)⁻¹)‖ = (2:ℝ)⁻¹ := by
          rw [norm_inv]; norm_num
        rw [h3]
        gcongr
    _ = ‖L‖ := by ring

/-! ## The `∂`- and `∂̄`-derivatives of the real and imaginary parts -/

lemma fderiv_re_apply (h : ℂ → ℂ) (z : ℂ) (hd : DifferentiableAt ℝ h z) (w : ℂ) :
    fderiv ℝ (fun y => (h y).re) z w = (fderiv ℝ h z w).re := by
  have hcomp : HasFDerivAt (fun y => (h y).re)
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ h z)) z :=
    Complex.reCLM.hasFDerivAt.comp z hd.hasFDerivAt
  rw [hcomp.fderiv]
  rfl

lemma fderiv_im_apply (h : ℂ → ℂ) (z : ℂ) (hd : DifferentiableAt ℝ h z) (w : ℂ) :
    fderiv ℝ (fun y => (h y).im) z w = (fderiv ℝ h z w).im := by
  have hcomp : HasFDerivAt (fun y => (h y).im)
      ((Complex.imCLM : ℂ →L[ℝ] ℝ).comp (fderiv ℝ h z)) z :=
    Complex.imCLM.hasFDerivAt.comp z hd.hasFDerivAt
  rw [hcomp.fderiv]
  rfl

/-- Symmetry of the mixed second derivative in the two directions `1` and `i`. -/
lemma clairaut_mixed (v : ℂ → ℝ) (z : ℂ) (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ (fun w => fderiv ℝ v w Complex.I) z 1
      = fderiv ℝ (fun w => fderiv ℝ v w 1) z Complex.I := by
  have hsym : IsSymmSndFDerivAt ℝ v z := hv.isSymmSndFDerivAt (by norm_num)
  have hdc : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun w => fderiv ℝ v w Complex.I) z
      = (fderiv ℝ (fderiv ℝ v) z).flip Complex.I := by
    simpa using fderiv_clm_apply (𝕜 := ℝ) hdc (differentiableAt_const (c := (Complex.I : ℂ)))
  have h2 : fderiv ℝ (fun w => fderiv ℝ v w (1:ℂ)) z
      = (fderiv ℝ (fderiv ℝ v) z).flip (1:ℂ) := by
    simpa using fderiv_clm_apply (𝕜 := ℝ) hdc (differentiableAt_const (c := (1:ℂ)))
  rw [h1, h2, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact hsym.eq 1 Complex.I

/-- The pointwise divergence identity: the difference `u_x v_y - u_y v_x` is the divergence of the
field `(u v_y, -u v_x)`. -/
lemma key_pointwise (u v : ℂ → ℝ) (z : ℂ) (hu : ContDiffAt ℝ 1 u z) (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ u z 1 * fderiv ℝ v z Complex.I - fderiv ℝ u z Complex.I * fderiv ℝ v z 1
      = fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1
        - fderiv ℝ (fun z => u z * fderiv ℝ v z 1) z Complex.I := by
  have hu' : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
  have hv2 : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv1 : DifferentiableAt ℝ (fun w => fderiv ℝ v w Complex.I) z :=
    hv2.clm_apply (differentiableAt_const _)
  have hv3 : DifferentiableAt ℝ (fun w => fderiv ℝ v w (1:ℂ)) z :=
    hv2.clm_apply (differentiableAt_const _)
  rw [fderiv_fun_mul hu' hv1, fderiv_fun_mul hu' hv3]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [clairaut_mixed v z hv]
  ring

/-! ## The `L¹`-vanishing of a compactly supported directional derivative -/

/-- For a compactly supported `C¹` function `A : ℂ → ℝ` and any direction `v`, the integral of the
directional derivative `z ↦ fderiv ℝ A z v` over `ℂ` vanishes. -/
theorem integral_fderiv_eq_zero {A : ℂ → ℝ} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    (v : ℂ) : ∫ z, fderiv ℝ A z v ∂volume = 0 := by
  obtain ⟨R, hR, hA0⟩ := hc.exists_pos_le_norm
  obtain ⟨M₀, hM₀⟩ := Continuous.bounded_above_of_compact_support
    (hA.continuous_fderiv (by simp)) (hc.fderiv (𝕜 := ℝ))
  set M : ℝ := max M₀ 0 * max ‖v‖ 1 with hMdef
  have hM : ∀ w : ℂ, ‖fderiv ℝ A w v‖ ≤ M := by
    intro w
    have h1 : ‖fderiv ℝ A w v‖ ≤ ‖fderiv ℝ A w‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖fderiv ℝ A w‖ ≤ max M₀ 0 := le_trans (hM₀ w) (le_max_left M₀ 0)
    have h3 : (0:ℝ) ≤ max M₀ 0 := le_max_right M₀ 0
    have h4 : ‖v‖ ≤ max ‖v‖ 1 := le_max_left ‖v‖ 1
    rw [hMdef]
    exact le_trans h1 (mul_le_mul h2 h4 (norm_nonneg v) h3)
  have htsupp : tsupport A ⊆ Metric.closedBall (0:ℂ) R := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hx (hA0 x (le_of_lt (not_le.mp h)))
  have hfd0 : ∀ w : ℂ, R < ‖w‖ → fderiv ℝ A w = 0 := by
    intro w hw
    refine fderiv_of_notMem_tsupport ℝ ?_
    intro hmem
    have h2 := htsupp hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  set S : Set ℝ := Set.Ioc (-1:ℝ) 1 with hSdef
  have hSmeas : MeasurableSet S := measurableSet_Ioc
  set F : ℂ × ℝ → ℝ := fun p => fderiv ℝ A (p.1 + p.2 • v) v with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    exact ((hA.continuous_fderiv (by simp)).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  set G : ℂ × ℝ → ℝ := fun p => (S.indicator (fun _ => (1:ℝ)) p.2) * F p with hGdef
  have hGmeas : AEStronglyMeasurable G (volume.prod volume) := by
    have h1 : Measurable (fun p : ℂ × ℝ => S.indicator (fun _ => (1:ℝ)) p.2) :=
      (measurable_const.indicator hSmeas).comp measurable_snd
    rw [hGdef]
    exact (h1.mul hFcont.measurable).aestronglyMeasurable
  have hFsupp : ∀ p : ℂ × ℝ, p.2 ∈ S → p.1 ∉ Metric.ball (0:ℂ) (R + 1 + ‖v‖) → F p = 0 := by
    intro p hs hz
    have hle1 : ‖p.2‖ ≤ 1 := by
      rw [hSdef, Set.mem_Ioc] at hs
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hs.1], hs.2⟩
    have hzn : R + 1 + ‖v‖ ≤ ‖p.1‖ := by
      rw [Metric.mem_ball, not_lt, dist_zero_right] at hz; exact hz
    have hfar : R < ‖p.1 + p.2 • v‖ := by
      have h1 : ‖p.1‖ ≤ ‖p.1 + p.2 • v‖ + ‖p.2 • v‖ := by
        have := norm_sub_le (p.1 + p.2 • v) (p.2 • v)
        simpa using this
      have h2 : ‖p.2 • v‖ ≤ ‖v‖ := by
        rw [norm_smul]
        calc ‖p.2‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg v)
          _ = ‖v‖ := one_mul _
      linarith
    rw [hFdef]
    simp only
    rw [hfd0 _ hfar]
    simp
  have hGbound : ∀ p : ℂ × ℝ, ‖G p‖ ≤
      (M * (Metric.ball (0:ℂ) (R + 1 + ‖v‖)).indicator (fun _ => (1:ℝ)) p.1)
        * (S.indicator (fun _ => (1:ℝ)) p.2) := by
    intro p
    by_cases hs : p.2 ∈ S
    · have hGval : G p = F p := by
        rw [hGdef]; simp only [Set.indicator_of_mem hs, one_mul]
      by_cases hz : p.1 ∈ Metric.ball (0:ℂ) (R + 1 + ‖v‖)
      · rw [hGval, Set.indicator_of_mem hz, Set.indicator_of_mem hs, mul_one, mul_one]
        exact hM (p.1 + p.2 • v)
      · rw [hGval, hFsupp p hs hz, norm_zero, Set.indicator_of_notMem hz]
        simp
    · have hG0 : G p = 0 := by
        rw [hGdef]; simp only [Set.indicator_of_notMem hs, zero_mul]
      rw [hG0, norm_zero, Set.indicator_of_notMem hs, mul_zero]
  have hdom : Integrable (fun p : ℂ × ℝ =>
      (M * (Metric.ball (0:ℂ) (R + 1 + ‖v‖)).indicator (fun _ => (1:ℝ)) p.1)
        * (S.indicator (fun _ => (1:ℝ)) p.2)) (volume.prod volume) := by
    have hball : Integrable (fun z : ℂ =>
        M * (Metric.ball (0:ℂ) (R + 1 + ‖v‖)).indicator (fun _ => (1:ℝ)) z) volume :=
      ((integrable_indicator_iff measurableSet_ball).mpr
        (integrableOn_const (C := (1:ℝ)))).const_mul M
    have hSfin : volume S ≠ ⊤ := by
      rw [hSdef, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top.ne
    have hSint : Integrable (fun s : ℝ => S.indicator (fun _ => (1:ℝ)) s) volume :=
      (integrable_indicator_iff hSmeas).mpr (integrableOn_const (hs := hSfin) (C := (1:ℝ)))
    exact Integrable.mul_prod hball hSint
  have hGint : Integrable G (volume.prod volume) :=
    Integrable.mono' hdom hGmeas (Filter.Eventually.of_forall hGbound)
  have hinner : ∀ z : ℂ, ∫ s, G (z, s) = A (z + v) - A (z - v) := by
    intro z
    have hGs : ∀ s : ℝ, G (z, s) = S.indicator (fun s => F (z, s)) s := by
      intro s
      rw [hGdef]
      simp only
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs, one_mul, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, zero_mul, Set.indicator_of_notMem hs]
    simp only [hGs]
    rw [integral_indicator hSmeas]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    have hderiv : ∀ s ∈ Set.uIcc (-1:ℝ) 1,
        HasDerivAt (fun t : ℝ => A (z + t • v)) (F (z, s)) s := by
      intro s _
      have h1 : HasDerivAt (fun t : ℝ => z + t • v) v s := by
        have h := (hasDerivAt_id s).smul_const v
        simpa using h.const_add z
      have h2 : HasFDerivAt A (fderiv ℝ A (z + s • v)) (z + s • v) :=
        ((hA.differentiable (by simp)) (z + s • v)).hasFDerivAt
      have h3 := h2.comp_hasDerivAt s h1
      rw [hFdef]
      exact h3
    have hint : IntervalIntegrable (fun s : ℝ => F (z, s)) volume (-1) 1 :=
      (hFcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [sub_eq_add_neg]
  have step1 : ∫ z, (∫ s, G (z, s)) = 0 := by
    simp_rw [hinner]
    have hsup1 : HasCompactSupport (fun z : ℂ => A (z + v)) := by
      simpa [Function.comp_def, add_comm] using hc.comp_homeomorph (Homeomorph.addLeft v)
    have hsup2 : HasCompactSupport (fun z : ℂ => A (z - v)) := by
      simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
        hc.comp_homeomorph (Homeomorph.addLeft (-v))
    have h1 : Integrable (fun z : ℂ => A (z + v)) volume :=
      (hA.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        hsup1
    have h2 : Integrable (fun z : ℂ => A (z - v)) volume :=
      (hA.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
        hsup2
    rw [integral_sub h1 h2]
    have e1 : ∫ z, A (z + v) = ∫ z, A z := integral_add_right_eq_self A v
    have e2 : ∫ z, A (z - v) = ∫ z, A z := integral_sub_right_eq_self A v
    rw [e1, e2, sub_self]
  have step2 : ∫ p, G p = ∫ z, ∫ s, G (z, s) := integral_prod G hGint
  have step3 : ∫ p, G p = ∫ s, ∫ z, G (z, s) := integral_prod_symm G hGint
  have step4 : ∫ s, ∫ z, G (z, s) = (2:ℝ) • (∫ z, fderiv ℝ A z v) := by
    have hC : ∀ s : ℝ, ∫ z, G (z, s)
        = (S.indicator (fun _ => (1:ℝ)) s) * (∫ z, fderiv ℝ A z v) := by
      intro s
      have h1 : (fun z : ℂ => G (z, s))
          = fun z => (S.indicator (fun _ => (1:ℝ)) s) * F (z, s) := by
        funext z; rw [hGdef]
      rw [h1, integral_const_mul]
      congr 1
      rw [hFdef]
      simpa using integral_add_right_eq_self (fun w : ℂ => fderiv ℝ A w v) (s • v)
    have h2 : (fun s : ℝ => (S.indicator (fun _ => (1:ℝ)) s) * (∫ z, fderiv ℝ A z v))
        = (fun s : ℝ => S.indicator (fun _ => (∫ z, fderiv ℝ A z v)) s) := by
      funext s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, one_mul]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
    simp only [hC, h2]
    rw [integral_indicator hSmeas, setIntegral_const]
    congr 1
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hzero : (2:ℝ) • (∫ z, fderiv ℝ A z v) = 0 := by
    rw [← step4, ← step3, step2, step1]
  have hadd : (∫ z, fderiv ℝ A z v) + (∫ z, fderiv ℝ A z v) = 0 := by
    rw [← two_smul ℝ (∫ z, fderiv ℝ A z v)]
    exact hzero
  exact add_self_eq_zero.mp hadd

/-! ## The isometry `∫ ‖∂h‖² = ∫ ‖∂̄h‖²` for compactly supported smooth `h` -/

/-- `dbarW` is continuous for a `C¹` function. -/
lemma continuous_dbarW {H : ℂ → ℂ} (hH : ContDiff ℝ 1 H) : Continuous (dbarW H) := by
  have hd : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have h1 : Continuous (fun u : ℂ => (fderiv ℝ H u) 1) := hd.clm_apply continuous_const
  have hI : Continuous (fun u : ℂ => (fderiv ℝ H u) Complex.I) := hd.clm_apply continuous_const
  unfold dbarW dzbarCoeff
  exact (h1.add (continuous_const.mul hI)).div_const 2

/-- `dbarW` has compact support for a compactly supported function. -/
lemma hasCompactSupport_dbarW {H : ℂ → ℂ} (hc : HasCompactSupport H) :
    HasCompactSupport (dbarW H) := by
  have h := (hc.fderiv ℝ).comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I)/2) (by simp)
  unfold dbarW dzbarCoeff
  exact h

/-- **The `L²` isometry for the `∂` and `∂̄` derivatives of a compactly supported smooth
function**: `∫ ‖dW h‖² = ∫ ‖dbarW h‖²`.  Both sides are the integral of the Jacobian determinant
`∫ det(Dh)`, which vanishes for a compactly supported map. -/
theorem integral_normSq_dW_eq_dbarW (h : ℂ → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) :
    ∫ z, ‖dW h z‖ ^ 2 ∂volume = ∫ z, ‖dbarW h z‖ ^ 2 ∂volume := by
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by norm_num)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hd : ∀ z : ℂ, DifferentiableAt ℝ h z := fun z => (hh1.differentiable (by simp)) z
  set u : ℂ → ℝ := fun z => (h z).re with hudef
  set v : ℂ → ℝ := fun z => (h z).im with hvdef
  have hu2 : ContDiff ℝ 2 u := by rw [hudef]; exact Complex.reCLM.contDiff.comp hh2
  have hv2 : ContDiff ℝ 2 v := by rw [hvdef]; exact Complex.imCLM.contDiff.comp hh2
  have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
  have huc : HasCompactSupport u := by
    rw [hudef]; exact hc.comp_left (g := Complex.reCLM) (by simp)
  have hvc : HasCompactSupport v := by
    rw [hvdef]; exact hc.comp_left (g := Complex.imCLM) (by simp)
  have hpoint : ∀ z : ℂ, ‖dW h z‖ ^ 2 - ‖dbarW h z‖ ^ 2
      = fderiv ℝ u z 1 * fderiv ℝ v z Complex.I
        - fderiv ℝ u z Complex.I * fderiv ℝ v z 1 := by
    intro z
    have h1 := normSq_dzCoeff_sub_dzbarCoeff (fderiv ℝ h z)
    simp only [dW, dbarW]
    rw [h1, fderiv_re_apply h z (hd z) 1, fderiv_im_apply h z (hd z) Complex.I,
      fderiv_re_apply h z (hd z) Complex.I, fderiv_im_apply h z (hd z) 1]
  have hkey : ∀ z : ℂ,
      fderiv ℝ u z 1 * fderiv ℝ v z Complex.I - fderiv ℝ u z Complex.I * fderiv ℝ v z 1
        = fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1
          - fderiv ℝ (fun z => u z * fderiv ℝ v z 1) z Complex.I :=
    fun z => key_pointwise u v z (hu1.contDiffAt) (hv2.contDiffAt)
  have hvy : ContDiff ℝ 1 (fun z => fderiv ℝ v z Complex.I) :=
    (hv2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hvx : ContDiff ℝ 1 (fun z => fderiv ℝ v z (1:ℂ)) :=
    (hv2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hAc : ContDiff ℝ 1 (fun z => u z * fderiv ℝ v z Complex.I) := hu1.mul hvy
  have hBc : ContDiff ℝ 1 (fun z => u z * fderiv ℝ v z (1:ℂ)) := hu1.mul hvx
  have hAsupp : HasCompactSupport (fun z => u z * fderiv ℝ v z Complex.I) := huc.mul_right
  have hBsupp : HasCompactSupport (fun z => u z * fderiv ℝ v z (1:ℂ)) := huc.mul_right
  have hAint : ∫ z, fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1 ∂volume = 0 :=
    integral_fderiv_eq_zero hAc hAsupp 1
  have hBint : ∫ z, fderiv ℝ (fun z => u z * fderiv ℝ v z (1:ℂ)) z Complex.I ∂volume = 0 :=
    integral_fderiv_eq_zero hBc hBsupp Complex.I
  have hcontA : Continuous (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1) :=
    (hAc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsuppA : HasCompactSupport (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1) :=
    (hAsupp.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L 1) (by simp)
  have hcontB : Continuous (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z (1:ℂ)) z Complex.I) :=
    (hBc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsuppB : HasCompactSupport (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z (1:ℂ)) z Complex.I) :=
    (hBsupp.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L Complex.I) (by simp)
  have hintA : Integrable (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1) volume :=
    hcontA.integrable_of_hasCompactSupport hsuppA
  have hintB : Integrable
      (fun z => fderiv ℝ (fun z => u z * fderiv ℝ v z (1:ℂ)) z Complex.I) volume :=
    hcontB.integrable_of_hasCompactSupport hsuppB
  have hsupp_dW : HasCompactSupport (fun z => ‖dW h z‖ ^ 2) :=
    (hasCompactSupport_dW hc).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hsupp_dbarW : HasCompactSupport (fun z => ‖dbarW h z‖ ^ 2) :=
    (hasCompactSupport_dbarW hc).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hint_dW : Integrable (fun z => ‖dW h z‖ ^ 2) volume :=
    ((continuous_dW hh1).norm.pow 2).integrable_of_hasCompactSupport hsupp_dW
  have hint_dbarW : Integrable (fun z => ‖dbarW h z‖ ^ 2) volume :=
    ((continuous_dbarW hh1).norm.pow 2).integrable_of_hasCompactSupport hsupp_dbarW
  have hdiff : ∫ z, (‖dW h z‖ ^ 2 - ‖dbarW h z‖ ^ 2) ∂volume = 0 := by
    have e1 : ∫ z, (‖dW h z‖ ^ 2 - ‖dbarW h z‖ ^ 2) ∂volume
        = ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z Complex.I
            - fderiv ℝ u z Complex.I * fderiv ℝ v z 1) ∂volume := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    have e2 : ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z Complex.I
            - fderiv ℝ u z Complex.I * fderiv ℝ v z 1) ∂volume
        = ∫ z, (fderiv ℝ (fun z => u z * fderiv ℝ v z Complex.I) z 1
            - fderiv ℝ (fun z => u z * fderiv ℝ v z (1:ℂ)) z Complex.I) ∂volume := by
      apply integral_congr_ae
      filter_upwards with z
      exact hkey z
    rw [e1, e2, integral_sub hintA hintB, hAint, hBint, sub_zero]
  rw [← sub_eq_zero]
  rw [← integral_sub hint_dW hint_dbarW]
  exact hdiff


/-! ## The cutoff family `χ_m z = bumpC ((m+1)⁻¹ z)` -/

/-- A bound for the derivative of the bump function `bumpC`. -/
noncomputable def Cbump : ℝ :=
  max (Classical.choose (Continuous.bounded_above_of_compact_support
    (bumpC_contDiffC.continuous_fderiv (by simp)) (bumpC_hasCompactSupport.fderiv ℝ))) 0

lemma Cbump_nonneg : 0 ≤ Cbump := le_max_right _ _

lemma norm_fderiv_bumpC_le (w : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => (bumpC z : ℂ)) w‖ ≤ Cbump :=
  le_trans (Classical.choose_spec (Continuous.bounded_above_of_compact_support
    (bumpC_contDiffC.continuous_fderiv (by simp)) (bumpC_hasCompactSupport.fderiv ℝ)) w)
    (le_max_left _ _)

/-- The cutoff `χ_m z = bumpC ((m+1)⁻¹ z)`: it equals `1` on the ball of radius `(m+1)/2` and
vanishes outside the ball of radius `m+1`. -/
noncomputable def chiC (m : ℕ) : ℂ → ℂ := fun z => (bumpC ((((m:ℝ)+1)⁻¹) • z) : ℂ)

lemma chiC_eq_comp (m : ℕ) :
    chiC m = (fun w : ℂ => (bumpC w : ℂ)) ∘ (fun z : ℂ => (((m:ℝ)+1)⁻¹) • z) := by
  funext z; rfl

lemma chiC_contDiff (m : ℕ) : ContDiff ℝ ∞ (chiC m) := by
  have h1 : (fun z : ℂ => (((m:ℝ)+1)⁻¹) • z) = ⇑(((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) := by
    funext w; simp
  rw [chiC_eq_comp, h1]
  exact bumpC_contDiffC.comp (ContinuousLinearMap.contDiff _)

lemma chiC_norm_le_one (m : ℕ) (z : ℂ) : ‖chiC m z‖ ≤ 1 := by
  have h : ‖chiC m z‖ = |bumpC ((((m:ℝ)+1)⁻¹) • z)| := by
    delta chiC
    simp
  rw [h, abs_of_nonneg (bumpC_nonneg _)]
  exact bumpC_le_one _

lemma chiC_eq_one (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ ((m:ℝ)+1)/2) : chiC m z = 1 := by
  have h3 : ‖((((m:ℝ)+1)⁻¹) • z)‖ = ‖z‖ * ((m:ℝ)+1)⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
  have h2 : (((m:ℝ)+1)/2) * ((m:ℝ)+1)⁻¹ = 1/2 := by field_simp
  delta chiC
  rw [Complex.ofReal_eq_one]
  refine bumpC_eq_one ?_
  rw [h3]
  calc ‖z‖ * ((m:ℝ)+1)⁻¹ ≤ (((m:ℝ)+1)/2) * ((m:ℝ)+1)⁻¹ :=
        mul_le_mul_of_nonneg_right hz (by positivity)
    _ = 1/2 := h2

lemma chiC_eq_zero (m : ℕ) {z : ℂ} (hz : (m:ℝ)+1 ≤ ‖z‖) : chiC m z = 0 := by
  have h3 : ‖((((m:ℝ)+1)⁻¹) • z)‖ = ‖z‖ * ((m:ℝ)+1)⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
  delta chiC
  rw [Complex.ofReal_eq_zero]
  refine bumpC_eq_zero ?_
  rw [h3]
  calc (1:ℝ) = ((m:ℝ)+1) * ((m:ℝ)+1)⁻¹ := by
        rw [mul_inv_cancel₀ (by positivity)]
    _ ≤ ‖z‖ * ((m:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right hz (by positivity)

lemma chiC_hasCompactSupport (m : ℕ) : HasCompactSupport (chiC m) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℂ) ((m:ℝ)+1)) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (chiC_eq_zero m (le_of_lt (not_le.mp h)))

lemma fderiv_chiC_eq_zero_of_lt (m : ℕ) {z : ℂ} (hz : ‖z‖ < ((m:ℝ)+1)/2) :
    fderiv ℝ (chiC m) z = 0 := by
  have hpos : 0 < ((m:ℝ)+1)/2 - ‖z‖ := by linarith
  have h : chiC m =ᶠ[𝓝 z] (fun _ => (1:ℂ)) := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z hpos) ?_
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine chiC_eq_one m (le_of_lt ?_)
    have h2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have h3 := norm_add_le z (w - z)
      simpa using h3
    linarith
  rw [h.fderiv_eq]
  simp

lemma fderiv_chiC_eq_zero_of_gt (m : ℕ) {z : ℂ} (hz : (m:ℝ)+1 < ‖z‖) :
    fderiv ℝ (chiC m) z = 0 := by
  have hpos : 0 < (‖z‖ - ((m:ℝ)+1))/2 := by linarith
  have h : chiC m =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z hpos) ?_
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine chiC_eq_zero m ?_
    have h2 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have h3 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        have h4 := norm_add_le (z - w) w
        simpa using h4
      rw [norm_sub_rev z w] at h3
      linarith
    linarith
  rw [h.fderiv_eq]
  simp

lemma norm_fderiv_chiC_le (m : ℕ) (z : ℂ) :
    ‖fderiv ℝ (chiC m) z‖ ≤ Cbump / ((m:ℝ)+1) := by
  have hcpos : (0:ℝ) ≤ ((m:ℝ)+1)⁻¹ := by positivity
  have hdiff_scale : DifferentiableAt ℝ (fun z : ℂ => (((m:ℝ)+1)⁻¹) • z) z :=
    (ContinuousLinearMap.hasFDerivAt (((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ))).differentiableAt
  have hdiff_bump : DifferentiableAt ℝ (fun w : ℂ => (bumpC w : ℂ))
      ((((m:ℝ)+1)⁻¹) • z) := (bumpC_contDiffC.differentiable (by simp) _)
  have hscale : fderiv ℝ (fun z : ℂ => (((m:ℝ)+1)⁻¹) • z) z
      = ((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ) := by
    have h1 : (fun z : ℂ => (((m:ℝ)+1)⁻¹) • z) = ⇑(((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) := by
      funext w; simp
    rw [h1]
    exact (ContinuousLinearMap.hasFDerivAt _).fderiv
  rw [chiC_eq_comp, fderiv_comp z hdiff_bump hdiff_scale, hscale]
  calc ‖(fderiv ℝ (fun w : ℂ => (bumpC w : ℂ)) ((((m:ℝ)+1)⁻¹) • z)).comp
        (((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ))‖
      ≤ ‖fderiv ℝ (fun w : ℂ => (bumpC w : ℂ)) ((((m:ℝ)+1)⁻¹) • z)‖ *
          ‖((m:ℝ)+1)⁻¹ • (1 : ℂ →L[ℝ] ℂ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Cbump * ((m:ℝ)+1)⁻¹ := by
        refine mul_le_mul (norm_fderiv_bumpC_le _) ?_ (norm_nonneg _) Cbump_nonneg
        rw [norm_smul, Real.norm_of_nonneg hcpos, norm_one, mul_one]
    _ = Cbump / ((m:ℝ)+1) := by rw [div_eq_mul_inv]

lemma norm_dW_chiC_le (m : ℕ) (z : ℂ) :
    ‖dW (chiC m) z‖ ≤ Cbump / ((m:ℝ)+1) :=
  le_trans (norm_dzCoeff_le _) (norm_fderiv_chiC_le m z)

lemma norm_dbarW_chiC_le (m : ℕ) (z : ℂ) :
    ‖dbarW (chiC m) z‖ ≤ Cbump / ((m:ℝ)+1) :=
  le_trans (norm_dzbarCoeff_le _) (norm_fderiv_chiC_le m z)

lemma dW_chiC_eq_zero_of_notMem_annulus (m : ℕ) {z : ℂ}
    (hz : ‖z‖ < ((m:ℝ)+1)/2 ∨ (m:ℝ)+1 < ‖z‖) : dW (chiC m) z = 0 := by
  unfold dW
  rcases hz with hz | hz
  · rw [fderiv_chiC_eq_zero_of_lt m hz]; simp [dzCoeff]
  · rw [fderiv_chiC_eq_zero_of_gt m hz]; simp [dzCoeff]

lemma dbarW_chiC_eq_zero_of_notMem_annulus (m : ℕ) {z : ℂ}
    (hz : ‖z‖ < ((m:ℝ)+1)/2 ∨ (m:ℝ)+1 < ‖z‖) : dbarW (chiC m) z = 0 := by
  unfold dbarW
  rcases hz with hz | hz
  · rw [fderiv_chiC_eq_zero_of_lt m hz]; simp [dzbarCoeff]
  · rw [fderiv_chiC_eq_zero_of_gt m hz]; simp [dzbarCoeff]

/-- A basic decay estimate: for `r ≥ (m+1)/2` and `C ≥ 0`, `C/(1+r) ≤ 2C/(m+1)`. -/
lemma div_le_two_mul_div {C r : ℝ} (hC : 0 ≤ C) {m : ℕ} (hr : ((m:ℝ)+1)/2 ≤ r) :
    C / (1 + r) ≤ 2 * C / ((m:ℝ)+1) := by
  have hpos : (0:ℝ) < (m:ℝ)+1 := by positivity
  have h1 : C / (1 + r) ≤ C / (1 + ((m:ℝ)+1)/2) :=
    div_le_div_of_nonneg_left hC (by linarith) (by linarith)
  have h2 : 1 + ((m:ℝ)+1)/2 = ((m:ℝ)+3)/2 := by ring
  have h3 : C / (((m:ℝ)+3)/2) = 2 * C / ((m:ℝ)+3) := by
    field_simp
  have h4 : 2 * C / ((m:ℝ)+3) ≤ 2 * C / ((m:ℝ)+1) :=
    div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 2 * C) hpos (by linarith)
  calc C / (1 + r) ≤ C / (1 + ((m:ℝ)+1)/2) := h1
    _ = C / (((m:ℝ)+3)/2) := by rw [h2]
    _ = 2 * C / ((m:ℝ)+3) := h3
    _ ≤ 2 * C / ((m:ℝ)+1) := h4

/-! ## The decay estimates -/

lemma real_volume_closedBall {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure ℂ).real (Metric.closedBall (0:ℂ) r) = r^2 * Real.pi := by
  rw [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp

lemma volume_closedBall_ne_top (r : ℝ) : volume (Metric.closedBall (0:ℂ) r) ≠ ⊤ := by
  rw [Complex.volume_closedBall]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top

lemma integrable_indicator_closedBall (r : ℝ) :
    Integrable (fun z : ℂ => (Metric.closedBall (0:ℂ) r).indicator (fun _ => (1:ℝ)) z) volume := by
  refine (integrable_indicator_iff measurableSet_closedBall).mpr
    (integrableOn_const (hs := volume_closedBall_ne_top r) (C := (1:ℝ)))

/-- The integral of a constant times the indicator of a closed ball. -/
lemma integral_const_mul_indicator_closedBall {r K : ℝ} (hr : 0 ≤ r) :
    ∫ z, K * (Metric.closedBall (0:ℂ) r).indicator (fun _ => (1:ℝ)) z ∂volume
      = K * (r^2 * Real.pi) := by
  rw [integral_const_mul, integral_indicator_const (1:ℝ) measurableSet_closedBall,
    smul_eq_mul, mul_one]
  congr 1
  exact real_volume_closedBall hr

/-- Estimate of `∫ ‖g‖²‖F‖²` when `F` is supported in the annulus `(m+1)/2 ≤ ‖z‖ ≤ m+1`. -/
lemma integral_sq_mul_sq_le {g F : ℂ → ℂ} {m : ℕ} {C Cb : ℝ} (hC : 0 ≤ C)
    (hgc : Continuous g) (hFc : Continuous F)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C / (1 + ‖z‖)) (hF : ∀ z : ℂ, ‖F z‖ ≤ Cb / ((m:ℝ)+1))
    (hFsupp : ∀ z : ℂ, F z ≠ 0 → ((m:ℝ)+1)/2 ≤ ‖z‖ ∧ ‖z‖ ≤ (m:ℝ)+1) :
    ∫ z, ‖g z‖ ^ 2 * ‖F z‖ ^ 2 ≤ 4 * Real.pi * C ^ 2 * Cb ^ 2 / ((m:ℝ)+1) ^ 2 := by
  have hpos : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hK : (0:ℝ) ≤ 4 * C ^ 2 * Cb ^ 2 / ((m:ℝ)+1)^4 :=
    div_nonneg (by positivity) (by positivity)
  have hpt : ∀ z : ℂ, ‖g z‖ ^ 2 * ‖F z‖ ^ 2 ≤
      (4 * C ^ 2 * Cb ^ 2 / ((m:ℝ)+1)^4) *
        (Metric.closedBall (0:ℂ) ((m:ℝ)+1)).indicator (fun _ => (1:ℝ)) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0:ℂ) ((m:ℝ)+1)
    · rw [Set.indicator_of_mem hz, mul_one]
      by_cases hF0 : F z = 0
      · rw [hF0]
        have hzero : ‖g z‖ ^ 2 * ‖(0:ℂ)‖ ^ 2 = 0 := by simp
        rw [hzero]
        exact hK
      · obtain ⟨hz1, hz2⟩ := hFsupp z hF0
        have hb1 : ‖g z‖ ≤ 2 * C / ((m:ℝ)+1) := le_trans (hg z) (div_le_two_mul_div hC hz1)
        have hb2 : ‖F z‖ ≤ Cb / ((m:ℝ)+1) := hF z
        have h1 : ‖g z‖ ^ 2 ≤ (2 * C / ((m:ℝ)+1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb1 2
        have h2 : ‖F z‖ ^ 2 ≤ (Cb / ((m:ℝ)+1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb2 2
        calc ‖g z‖ ^ 2 * ‖F z‖ ^ 2 ≤ (2 * C / ((m:ℝ)+1)) ^ 2 * (Cb / ((m:ℝ)+1)) ^ 2 :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 4 * C ^ 2 * Cb ^ 2 / ((m:ℝ)+1)^4 := by field_simp; ring
    · rw [Set.indicator_of_notMem hz, mul_zero]
      have hF0 : F z = 0 := by
        by_contra h
        exact hz (Metric.mem_closedBall.mpr (by
          rw [dist_zero_right]; exact (hFsupp z h).2))
      rw [hF0]
      have hzero : ‖g z‖ ^ 2 * ‖(0:ℂ)‖ ^ 2 = 0 := by simp
      rw [hzero]
  have hInt : Integrable (fun z : ℂ => (4 * C ^ 2 * Cb ^ 2 / ((m:ℝ)+1)^4) *
      (Metric.closedBall (0:ℂ) ((m:ℝ)+1)).indicator (fun _ => (1:ℝ)) z) volume :=
    (integrable_indicator_closedBall ((m:ℝ)+1)).const_mul _
  have hIntL : Integrable (fun z : ℂ => ‖g z‖ ^ 2 * ‖F z‖ ^ 2) volume :=
    hInt.mono' ((hgc.norm.pow 2).mul (hFc.norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hpt z))
  have hmono := integral_mono_ae hIntL hInt (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul_indicator_closedBall (by positivity)] at hmono
  refine le_trans hmono (le_of_eq ?_)
  field_simp

/-- Estimate of `∫ ‖G‖‖g‖‖F‖` when `F` is supported in the annulus. -/
lemma integral_norm_mul_le {g F G : ℂ → ℂ} {m : ℕ} {C Cb : ℝ} (hC : 0 ≤ C) (hCb : 0 ≤ Cb)
    (hgc : Continuous g) (hFc : Continuous F) (hGc : Continuous G)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C / (1 + ‖z‖)) (hG : ∀ z : ℂ, ‖G z‖ ≤ C / (1 + ‖z‖))
    (hF : ∀ z : ℂ, ‖F z‖ ≤ Cb / ((m:ℝ)+1))
    (hFsupp : ∀ z : ℂ, F z ≠ 0 → ((m:ℝ)+1)/2 ≤ ‖z‖ ∧ ‖z‖ ≤ (m:ℝ)+1) :
    ∫ z, ‖G z‖ * ‖g z‖ * ‖F z‖ ≤ 4 * Real.pi * C ^ 2 * Cb / ((m:ℝ)+1) := by
  have hpos : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hK : (0:ℝ) ≤ 4 * C ^ 2 * Cb / ((m:ℝ)+1)^3 :=
    div_nonneg (by positivity) (by positivity)
  have hpt : ∀ z : ℂ, ‖G z‖ * ‖g z‖ * ‖F z‖ ≤
      (4 * C ^ 2 * Cb / ((m:ℝ)+1)^3) *
        (Metric.closedBall (0:ℂ) ((m:ℝ)+1)).indicator (fun _ => (1:ℝ)) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0:ℂ) ((m:ℝ)+1)
    · rw [Set.indicator_of_mem hz, mul_one]
      by_cases hF0 : F z = 0
      · rw [hF0]
        have hzero : ‖G z‖ * ‖g z‖ * ‖(0:ℂ)‖ = 0 := by simp
        rw [hzero]
        exact hK
      · obtain ⟨hz1, hz2⟩ := hFsupp z hF0
        have hb1 : ‖g z‖ ≤ 2 * C / ((m:ℝ)+1) := le_trans (hg z) (div_le_two_mul_div hC hz1)
        have hb1' : ‖G z‖ ≤ 2 * C / ((m:ℝ)+1) := le_trans (hG z) (div_le_two_mul_div hC hz1)
        have hb2 : ‖F z‖ ≤ Cb / ((m:ℝ)+1) := hF z
        calc ‖G z‖ * ‖g z‖ * ‖F z‖ ≤
              (2 * C / ((m:ℝ)+1)) * (2 * C / ((m:ℝ)+1)) * (Cb / ((m:ℝ)+1)) := by
              refine mul_le_mul (mul_le_mul hb1' hb1 (norm_nonneg _) (by positivity)) hb2
                (norm_nonneg _) (by positivity)
          _ = 4 * C ^ 2 * Cb / ((m:ℝ)+1)^3 := by field_simp; ring
    · rw [Set.indicator_of_notMem hz, mul_zero]
      have hF0 : F z = 0 := by
        by_contra h
        exact hz (Metric.mem_closedBall.mpr (by
          rw [dist_zero_right]; exact (hFsupp z h).2))
      rw [hF0]
      have hzero : ‖G z‖ * ‖g z‖ * ‖(0:ℂ)‖ = 0 := by simp
      rw [hzero]
  have hInt : Integrable (fun z : ℂ => (4 * C ^ 2 * Cb / ((m:ℝ)+1)^3) *
      (Metric.closedBall (0:ℂ) ((m:ℝ)+1)).indicator (fun _ => (1:ℝ)) z) volume :=
    (integrable_indicator_closedBall ((m:ℝ)+1)).const_mul _
  have hIntL : Integrable (fun z : ℂ => ‖G z‖ * ‖g z‖ * ‖F z‖) volume :=
    hInt.mono' ((hGc.norm.mul hgc.norm).mul hFc.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hpt z))
  have hmono := integral_mono_ae hIntL hInt (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul_indicator_closedBall (by positivity)] at hmono
  refine le_trans hmono (le_of_eq ?_)
  field_simp

/-! ## The cutoff family is monotone -/

lemma chiC_mono (m : ℕ) (z : ℂ) : ‖chiC m z‖ ≤ ‖chiC (m+1) z‖ := by
  have hval : ∀ k : ℕ, ‖chiC k z‖ = Real.smoothTransition (2 - 2 * ‖((((k:ℝ)+1)⁻¹) • z)‖) := by
    intro k
    have h1 : ‖chiC k z‖ = |bumpC ((((k:ℝ)+1)⁻¹) • z)| := by delta chiC; simp
    rw [h1, abs_of_nonneg (bumpC_nonneg _), bumpC]
  rw [hval m, hval (m+1)]
  apply Real.smoothTransition.monotone
  have h4 : ‖((((↑(m+1) + 1 : ℝ))⁻¹) • z)‖ ≤ ‖((((↑m + 1 : ℝ))⁻¹) • z)‖ := by
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    apply inv_anti₀ (by positivity)
    push_cast
    linarith
  linarith [h4]


/-! ## Auxiliary lemmas for the limit argument -/

lemma abs_normSq_add_sub_normSq_le (a b : ℂ) :
    |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have h := norm_sub_le (a + b) b
    rwa [add_sub_cancel_right] at h
  have h3 : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h4 : (0:ℝ) ≤ ‖a + b‖ + ‖a‖ := by positivity
  have h5 : ‖a + b‖ + ‖a‖ ≤ 2 * ‖a‖ + ‖b‖ := by linarith
  have hsq : ‖a + b‖ ^ 2 - ‖a‖ ^ 2 = (‖a + b‖ - ‖a‖) * (‖a + b‖ + ‖a‖) := by ring
  calc |‖a + b‖ ^ 2 - ‖a‖ ^ 2| = |(‖a + b‖ - ‖a‖) * (‖a + b‖ + ‖a‖)| := by rw [hsq]
    _ = |‖a + b‖ - ‖a‖| * (‖a + b‖ + ‖a‖) := by rw [abs_mul, abs_of_nonneg h4]
    _ ≤ ‖b‖ * (2 * ‖a‖ + ‖b‖) := mul_le_mul h3 h5 h4 (norm_nonneg b)
    _ = 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring

lemma integrable_normSq_of_hasCompactSupport {W : ℂ → ℂ} (hWc : Continuous W)
    (hWs : HasCompactSupport W) : Integrable (fun z : ℂ => ‖W z‖ ^ 2) volume := by
  refine ((hWc.norm.pow 2)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hWs ?_
  intro z hz
  rw [Function.mem_support] at hz
  refine subset_tsupport W ?_
  rw [Function.mem_support]
  intro h
  exact hz (by show ‖W z‖ ^ 2 = 0; rw [h]; simp)

lemma integrable_sq_mul_sq {F G : ℂ → ℂ} (hFc : Continuous F) (hGc : Continuous G)
    (hFs : HasCompactSupport F) : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * ‖G z‖ ^ 2) volume := by
  refine (((hFc.norm.pow 2).mul (hGc.norm.pow 2))).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hFs ?_
  intro z hz
  rw [Function.mem_support] at hz
  refine subset_tsupport F ?_
  rw [Function.mem_support]
  intro hFz
  exact hz (by show ‖F z‖ ^ 2 * ‖G z‖ ^ 2 = 0; rw [hFz]; simp)

lemma integrable_norm_mul_norm {F G H : ℂ → ℂ} (hFc : Continuous F) (hGc : Continuous G)
    (hHc : Continuous H) (hFs : HasCompactSupport F) :
    Integrable (fun z : ℂ => ‖F z‖ * ‖G z‖ * ‖H z‖) volume := by
  refine (((hFc.norm.mul hGc.norm).mul hHc.norm)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hFs ?_
  intro z hz
  rw [Function.mem_support] at hz
  refine subset_tsupport F ?_
  rw [Function.mem_support]
  intro hFz
  exact hz (by show ‖F z‖ * ‖G z‖ * ‖H z‖ = 0; rw [hFz]; simp)

lemma chiC_mono_of_le {m k : ℕ} (hmk : m ≤ k) (z : ℂ) : ‖chiC m z‖ ≤ ‖chiC k z‖ := by
  induction hmk with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (chiC_mono _ z)

/-- The sup over the cutoffs of `‖χ_m z‖` is `1`. -/
lemma iSup_norm_chiC (z : ℂ) : (⨆ m : ℕ, ENNReal.ofReal (‖chiC m z‖ ^ 2)) = 1 := by
  refine le_antisymm (iSup_le fun m => ?_) ?_
  · rw [ENNReal.ofReal_le_one]
    exact pow_le_one₀ (norm_nonneg _) (chiC_norm_le_one m z)
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, ‖z‖ ≤ ((M:ℝ)+1)/2 :=
      ⟨⌈2 * ‖z‖⌉₊, by
        have h2 : (2 * ‖z‖ : ℝ) ≤ ⌈2 * ‖z‖⌉₊ := Nat.le_ceil _
        push_cast
        linarith⟩
    have h1 : ENNReal.ofReal (‖chiC M z‖ ^ 2) = 1 := by
      rw [chiC_eq_one M hM, norm_one, one_pow, ENNReal.ofReal_one]
    rw [← h1]
    exact le_iSup (fun m : ℕ => ENNReal.ofReal (‖chiC m z‖ ^ 2)) M


/-- `‖z‖ₑ ^ (2 : ℝ) = ofReal (‖z‖ ^ 2)` for a complex number. -/
lemma enorm_rpow_two_ofReal (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm z]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

/-! ## The pointwise supremum over the cutoff family -/

/-- The pointwise supremum over the cutoffs: `⨆ m, ofReal ‖χ_m z · h z‖² = ofReal ‖h z‖²`. -/
lemma iSup_ofReal_normSq_chiC_mul (h : ℂ → ℂ) (z : ℂ) :
    (⨆ m : ℕ, ENNReal.ofReal (‖chiC m z * h z‖ ^ 2)) = ENNReal.ofReal (‖h z‖ ^ 2) := by
  refine le_antisymm (iSup_le fun m => ?_) ?_
  · rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
    calc ‖chiC m z * h z‖ ^ 2 = ‖chiC m z‖ ^ 2 * ‖h z‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ 1 ^ 2 * ‖h z‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ (norm_nonneg _) (chiC_norm_le_one m z) 2
      _ = ‖h z‖ ^ 2 := by ring
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, ‖z‖ ≤ ((M:ℝ)+1)/2 :=
      ⟨⌈2 * ‖z‖⌉₊, by
        have h2 : (2 * ‖z‖ : ℝ) ≤ ⌈2 * ‖z‖⌉₊ := Nat.le_ceil _
        push_cast
        linarith⟩
    have h1 : ENNReal.ofReal (‖chiC M z * h z‖ ^ 2) = ENNReal.ofReal (‖h z‖ ^ 2) := by
      rw [chiC_eq_one M hM, one_mul]
    rw [← h1]
    exact le_iSup (fun m : ℕ => ENNReal.ofReal (‖chiC m z * h z‖ ^ 2)) M

/-- The family `m ↦ ofReal ‖χ_m z · h z‖²` is monotone, for every `h`. -/
lemma monotone_ofReal_normSq_chiC_mul (h : ℂ → ℂ) :
    Monotone (fun m : ℕ => fun z : ℂ => ENNReal.ofReal (‖chiC m z * h z‖ ^ 2)) := by
  intro m m' hmm' z
  show ENNReal.ofReal (‖chiC m z * h z‖ ^ 2) ≤ ENNReal.ofReal (‖chiC m' z * h z‖ ^ 2)
  rw [norm_mul, norm_mul, mul_pow, mul_pow]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ‖chiC m z‖ ≤ ‖chiC m' z‖ := chiC_mono_of_le hmm' z
  have h2 : ‖chiC m z‖ ^ 2 ≤ ‖chiC m' z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- Measurability of the cutoff family. -/
lemma measurable_ofReal_normSq_chiC_mul (h : ℂ → ℂ) (hm : Measurable h) (m : ℕ) :
    Measurable (fun z : ℂ => ENNReal.ofReal (‖chiC m z * h z‖ ^ 2)) := by
  have hc : Measurable (fun z : ℂ => chiC m z) := (chiC_contDiff m).continuous.measurable
  have h1 : Measurable (fun z : ℂ => ‖chiC m z * h z‖) := (hc.mul hm).norm
  exact (h1.pow_const 2).ennreal_ofReal

/-- Monotone convergence for the cutoff family: for measurable `h`,
`⨆ m ∫⁻ ofReal ‖χ_m z · h z‖² = ∫⁻ ofReal ‖h z‖²`. -/
lemma iSup_lintegral_normSq_chiC_mul (h : ℂ → ℂ) (hm : Measurable h) :
    (⨆ m : ℕ, ∫⁻ z, ENNReal.ofReal (‖chiC m z * h z‖ ^ 2))
      = ∫⁻ z, ENNReal.ofReal (‖h z‖ ^ 2) := by
  rw [← lintegral_iSup (measurable_ofReal_normSq_chiC_mul h hm)
    (monotone_ofReal_normSq_chiC_mul h)]
  exact lintegral_congr (fun z => iSup_ofReal_normSq_chiC_mul h z)

/-- For `X ≥ 0` and `d ≥ 1`, `X/d² ≤ X/d`. -/
lemma div_sq_le_div_self {X : ℝ} (hX : 0 ≤ X) {d : ℝ} (hd : 1 ≤ d) : X / d ^ 2 ≤ X / d := by
  have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  rw [div_le_div_iff₀ (pow_pos hd0 2) hd0]
  have h1 : X * 1 ≤ X * d := mul_le_mul_of_nonneg_left hd hX
  nlinarith [h1, hd0]

/-- **The key limit step.**  For a smooth `g` whose `∂̄`-derivative is compactly supported and
which satisfies `‖g z‖, ‖∇g z‖ ≤ C/(1+‖z‖)`, the `L²` norms of `∂g` and `∂̄g` satisfy
`∫⁻ ‖∂g‖² ≤ ∫⁻ ‖∂̄g‖²`.

The proof applies the isometry `integral_normSq_dW_eq_dbarW` to the truncations `h_m = χ_m · g`,
controls the boundary terms by the decay of `g` and `∇g`, and lets `m → ∞`
(monotone convergence). -/
theorem lintegral_normSq_dW_le (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport (dbarW g)) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, ‖g z‖ ≤ C / (1 + ‖z‖) ∧ ‖fderiv ℝ g z‖ ≤ C / (1 + ‖z‖)) :
    ∫⁻ z, ENNReal.ofReal (‖dW g z‖ ^ 2) ≤ ∫⁻ z, ENNReal.ofReal (‖dbarW g z‖ ^ 2) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hdWg : ∀ z : ℂ, ‖dW g z‖ ≤ C / (1 + ‖z‖) :=
    fun z => le_trans (norm_dzCoeff_le _) (hdec z).2
  obtain ⟨R, hR, hR0⟩ := hfc.exists_pos_le_norm
  set K : ℝ := 16 * Real.pi * C ^ 2 * Cbump + 8 * Real.pi * C ^ 2 * Cbump ^ 2 + 1 with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : (0:ℝ) ≤ 16 * Real.pi * C ^ 2 * Cbump := by
      have := Cbump_nonneg; have := Real.pi_pos; positivity
    have h2 : (0:ℝ) ≤ 8 * Real.pi * C ^ 2 * Cbump ^ 2 := by
      have := Cbump_nonneg; have := Real.pi_pos; positivity
    linarith
  have hint1 : ∀ m : ℕ, Integrable (fun z : ℂ => ‖chiC m z * dW g z‖ ^ 2) volume := fun m =>
    integrable_normSq_of_hasCompactSupport
      (((chiC_contDiff m).continuous).mul (continuous_dW hg1))
      ((chiC_hasCompactSupport m).mul_right (f' := dW g))
  have hint2 : ∀ m : ℕ, Integrable (fun z : ℂ => ‖chiC m z * dbarW g z‖ ^ 2) volume := fun m =>
    integrable_normSq_of_hasCompactSupport
      (((chiC_contDiff m).continuous).mul (continuous_dbarW hg1))
      ((chiC_hasCompactSupport m).mul_right (f' := dbarW g))
  have hstep : ∀ m : ℕ, 2 * R < (m:ℝ)+1 →
      ∫ z, ‖chiC m z * dW g z‖ ^ 2 ≤
        (∫ z, ‖chiC m z * dbarW g z‖ ^ 2) + K / ((m:ℝ)+1) := by
    intro m hmR
    have hmpos : (0:ℝ) < (m:ℝ)+1 := by positivity
    have hcm : ContDiff ℝ 1 (chiC m) := (chiC_contDiff m).of_le (by norm_num)
    have hchi : HasCompactSupport (chiC m) := chiC_hasCompactSupport m
    have hF1supp : ∀ z : ℂ, dW (chiC m) z ≠ 0 →
        ((m:ℝ)+1)/2 ≤ ‖z‖ ∧ ‖z‖ ≤ (m:ℝ)+1 := by
      intro z hz
      constructor
      · by_contra h; push_neg at h
        exact hz (dW_chiC_eq_zero_of_notMem_annulus m (Or.inl h))
      · by_contra h; push_neg at h
        exact hz (dW_chiC_eq_zero_of_notMem_annulus m (Or.inr h))
    have hF2supp : ∀ z : ℂ, dbarW (chiC m) z ≠ 0 →
        ((m:ℝ)+1)/2 ≤ ‖z‖ ∧ ‖z‖ ≤ (m:ℝ)+1 := by
      intro z hz
      constructor
      · by_contra h; push_neg at h
        exact hz (dbarW_chiC_eq_zero_of_notMem_annulus m (Or.inl h))
      · by_contra h; push_neg at h
        exact hz (dbarW_chiC_eq_zero_of_notMem_annulus m (Or.inr h))
    set P : ℂ → ℝ := fun z => ‖chiC m z * dW g z‖ ^ 2 with hPdef
    set Q : ℂ → ℝ := fun z => ‖g z‖ ^ 2 * ‖dW (chiC m) z‖ ^ 2 with hQdef
    set PQ : ℂ → ℝ := fun z => ‖chiC m z * dW g z‖ * ‖g z‖ * ‖dW (chiC m) z‖ with hPQdef
    set P2 : ℂ → ℝ := fun z => ‖chiC m z * dbarW g z‖ ^ 2 with hP2def
    set Q2 : ℂ → ℝ := fun z => ‖g z‖ ^ 2 * ‖dbarW (chiC m) z‖ ^ 2 with hQ2def
    set PQ2 : ℂ → ℝ := fun z => ‖chiC m z * dbarW g z‖ * ‖g z‖ * ‖dbarW (chiC m) z‖ with hPQ2def
    have hPi : Integrable P volume := by
      rw [hPdef]
      exact integrable_normSq_of_hasCompactSupport
        (((chiC_contDiff m).continuous).mul (continuous_dW hg1))
        (hchi.mul_right (f' := dW g))
    have hQi : Integrable Q volume := by
      have hQeq : Q = fun z : ℂ => ‖dW (chiC m) z‖ ^ 2 * ‖g z‖ ^ 2 := by
        funext z
        show ‖g z‖ ^ 2 * ‖dW (chiC m) z‖ ^ 2 = ‖dW (chiC m) z‖ ^ 2 * ‖g z‖ ^ 2
        ring
      rw [hQeq]
      exact integrable_sq_mul_sq (F := dW (chiC m)) (G := g) (continuous_dW hcm) hg1.continuous
        (hasCompactSupport_dW hchi)
    have hPQi : Integrable PQ volume := by
      rw [hPQdef]
      exact integrable_norm_mul_norm (F := fun z => chiC m z * dW g z) (G := g) (H := dW (chiC m))
        (((chiC_contDiff m).continuous).mul (continuous_dW hg1)) hg1.continuous (continuous_dW hcm)
        (hchi.mul_right (f' := dW g))
    have hP2i : Integrable P2 volume := by
      rw [hP2def]
      exact integrable_normSq_of_hasCompactSupport
        (((chiC_contDiff m).continuous).mul (continuous_dbarW hg1))
        (hchi.mul_right (f' := dbarW g))
    have hQ2i : Integrable Q2 volume := by
      have hQ2eq : Q2 = fun z : ℂ => ‖dbarW (chiC m) z‖ ^ 2 * ‖g z‖ ^ 2 := by
        funext z
        show ‖g z‖ ^ 2 * ‖dbarW (chiC m) z‖ ^ 2 = ‖dbarW (chiC m) z‖ ^ 2 * ‖g z‖ ^ 2
        ring
      rw [hQ2eq]
      exact integrable_sq_mul_sq (F := dbarW (chiC m)) (G := g) (continuous_dbarW hcm) hg1.continuous
        (hasCompactSupport_dbarW hchi)
    have hPQ2i : Integrable PQ2 volume := by
      rw [hPQ2def]
      exact integrable_norm_mul_norm (F := fun z => chiC m z * dbarW g z) (G := g)
        (H := dbarW (chiC m))
        (((chiC_contDiff m).continuous).mul (continuous_dbarW hg1)) hg1.continuous
        (continuous_dbarW hcm) (hchi.mul_right (f' := dbarW g))
    have hpr : ∀ z : ℂ, dW (fun y => chiC m y * g y) z
        = chiC m z * dW g z + g z * dW (chiC m) z := by
      intro z
      rw [dW_mul (hcm.differentiable (by norm_num) z) (hg1.differentiable (by norm_num) z)]
      ring
    have hpr2 : ∀ z : ℂ, dbarW (fun y => chiC m y * g y) z
        = chiC m z * dbarW g z + g z * dbarW (chiC m) z := by
      intro z
      rw [dbarW_mul (hcm.differentiable (by norm_num) z) (hg1.differentiable (by norm_num) z)]
      ring
    have hFcont : ContDiff ℝ 1 (fun y => chiC m y * g y) :=
      ((chiC_contDiff m).mul hg).of_le (by norm_num)
    have hhi : Integrable (fun z : ℂ => ‖dW (fun y => chiC m y * g y) z‖ ^ 2) volume :=
      integrable_normSq_of_hasCompactSupport (continuous_dW hFcont)
        (hasCompactSupport_dW (hchi.mul_right (f' := g)))
    have hhi2 : Integrable (fun z : ℂ => ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2) volume :=
      integrable_normSq_of_hasCompactSupport (continuous_dbarW hFcont)
        (hasCompactSupport_dbarW (hchi.mul_right (f' := g)))
    -- pointwise bounds
    have hpt1 : ∀ z : ℂ, P z ≤ ‖dW (fun y => chiC m y * g y) z‖ ^ 2 + (2 * PQ z + Q z) := by
      intro z
      have h := abs_normSq_add_sub_normSq_le (chiC m z * dW g z) (g z * dW (chiC m) z)
      simp only [norm_mul] at h
      have h2 : P z - ‖dW (fun y => chiC m y * g y) z‖ ^ 2 ≤ 2 * PQ z + Q z := by
        rw [hpr z, hPdef, hPQdef, hQdef]
        simp only [Pi.add_apply, norm_mul]
        have hle := (abs_le.mp h).1
        linarith
      linarith
    have hpt2 : ∀ z : ℂ, ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2 ≤ P2 z + (2 * PQ2 z + Q2 z) := by
      intro z
      have h := abs_normSq_add_sub_normSq_le (chiC m z * dbarW g z) (g z * dbarW (chiC m) z)
      simp only [norm_mul] at h
      have h2 : ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2 - P2 z ≤ 2 * PQ2 z + Q2 z := by
        rw [hpr2 z, hP2def, hPQ2def, hQ2def]
        simp only [Pi.add_apply, norm_mul]
        have hle := le_of_abs_le h
        nlinarith [hle]
      linarith
    -- integrating the pointwise bounds
    have hsplit1 : ∫ z, (‖dW (fun y => chiC m y * g y) z‖ ^ 2 + (2 * PQ z + Q z))
        = (∫ z, ‖dW (fun y => chiC m y * g y) z‖ ^ 2) + (2 * (∫ z, PQ z) + ∫ z, Q z) := by
      have h1 : ∫ z, (‖dW (fun y => chiC m y * g y) z‖ ^ 2 + (2 * PQ z + Q z))
          = (∫ z, ‖dW (fun y => chiC m y * g y) z‖ ^ 2) + ∫ z, (2 * PQ z + Q z) :=
        integral_add hhi ((hPQi.const_mul 2).add hQi)
      have h2 : ∫ z, (2 * PQ z + Q z) = (∫ z, (2 * PQ z)) + ∫ z, Q z :=
        integral_add (hPQi.const_mul 2) hQi
      have h3 : ∫ z, (2 * PQ z) = 2 * ∫ z, PQ z := by
        simpa [smul_eq_mul] using integral_const_mul (2:ℝ) PQ
      rw [h2, h3] at h1
      exact h1
    have hsplit2 : ∫ z, (P2 z + (2 * PQ2 z + Q2 z)) = (∫ z, P2 z) + (2 * (∫ z, PQ2 z) + ∫ z, Q2 z) := by
      have h1 : ∫ z, (P2 z + (2 * PQ2 z + Q2 z)) = (∫ z, P2 z) + ∫ z, (2 * PQ2 z + Q2 z) :=
        integral_add hP2i ((hPQ2i.const_mul 2).add hQ2i)
      have h2 : ∫ z, (2 * PQ2 z + Q2 z) = (∫ z, (2 * PQ2 z)) + ∫ z, Q2 z :=
        integral_add (hPQ2i.const_mul 2) hQ2i
      have h3 : ∫ z, (2 * PQ2 z) = 2 * ∫ z, PQ2 z := by
        simpa [smul_eq_mul] using integral_const_mul (2:ℝ) PQ2
      rw [h2, h3] at h1
      exact h1
    have hm1 : ∫ z, P z ≤ (∫ z, ‖dW (fun y => chiC m y * g y) z‖ ^ 2)
        + (2 * (∫ z, PQ z) + ∫ z, Q z) := by
      have h0 : ∫ z, P z ≤ ∫ z, (‖dW (fun y => chiC m y * g y) z‖ ^ 2 + (2 * PQ z + Q z)) :=
        integral_mono_ae hPi (hhi.add ((hPQi.const_mul 2).add hQi))
          (Filter.Eventually.of_forall hpt1)
      linarith [h0, hsplit1]
    have hm2 : ∫ z, ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2
        ≤ (∫ z, P2 z) + (2 * (∫ z, PQ2 z) + ∫ z, Q2 z) := by
      have h0 : ∫ z, ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2 ≤ ∫ z, (P2 z + (2 * PQ2 z + Q2 z)) :=
        integral_mono_ae hhi2 (hP2i.add ((hPQ2i.const_mul 2).add hQ2i))
          (Filter.Eventually.of_forall hpt2)
      linarith [h0, hsplit2]
    have hIBeq : ∫ z, ‖dW (fun y => chiC m y * g y) z‖ ^ 2
        = ∫ z, ‖dbarW (fun y => chiC m y * g y) z‖ ^ 2 :=
      integral_normSq_dW_eq_dbarW (fun y => chiC m y * g y) ((chiC_contDiff m).mul hg)
        (hchi.mul_right (f' := g))
    -- the error estimates
    have hQb : ∫ z, Q z ≤ 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) ^ 2 := by
      rw [hQdef]
      exact integral_sq_mul_sq_le (g := g) (F := dW (chiC m)) (C := C) (Cb := Cbump) (m := m)
        hC hg1.continuous (continuous_dW hcm) (fun z => (hdec z).1) (norm_dW_chiC_le m) hF1supp
    have hQ2b : ∫ z, Q2 z ≤ 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) ^ 2 := by
      rw [hQ2def]
      exact integral_sq_mul_sq_le (g := g) (F := dbarW (chiC m)) (C := C) (Cb := Cbump) (m := m)
        hC hg1.continuous (continuous_dbarW hcm) (fun z => (hdec z).1) (norm_dbarW_chiC_le m) hF2supp
    have hQbu : ∫ z, Q z ≤ 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) :=
      le_trans hQb (div_sq_le_div_self (X := 4 * Real.pi * C ^ 2 * Cbump ^ 2)
        (by have := Cbump_nonneg; have := Real.pi_pos; positivity)
        (by have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; linarith))
    have hQ2bu : ∫ z, Q2 z ≤ 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) :=
      le_trans hQ2b (div_sq_le_div_self (X := 4 * Real.pi * C ^ 2 * Cbump ^ 2)
        (by have := Cbump_nonneg; have := Real.pi_pos; positivity)
        (by have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m; linarith))
    have hI1 : ∫ z, PQ z ≤ 4 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1) := by
      rw [hPQdef]
      refine integral_norm_mul_le (g := g) (G := fun z => chiC m z * dW g z) (F := dW (chiC m))
        (C := C) (Cb := Cbump) (m := m) hC Cbump_nonneg hg1.continuous (continuous_dW hcm)
        (((chiC_contDiff m).continuous).mul (continuous_dW hg1)) (fun z => (hdec z).1) ?_
        (norm_dW_chiC_le m) hF1supp
      intro z
      rw [norm_mul]
      calc ‖chiC m z‖ * ‖dW g z‖ ≤ 1 * (C / (1 + ‖z‖)) :=
            mul_le_mul (chiC_norm_le_one m z) (hdWg z) (norm_nonneg _) (by positivity)
        _ = C / (1 + ‖z‖) := one_mul _
    have hPQu : 2 * (∫ z, PQ z) ≤ 8 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1) := by
      have h2 : (2:ℝ) * (∫ z, PQ z)
          ≤ 2 * (4 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hI1 (by norm_num)
      rw [show 2 * (4 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1))
          = 8 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1) from by ring] at h2
      exact h2
    have hIz : ∫ z, PQ2 z = 0 := by
      have hzero : ∀ z : ℂ, PQ2 z = 0 := by
        intro z
        rw [hPQ2def]
        show ‖chiC m z * dbarW g z‖ * ‖g z‖ * ‖dbarW (chiC m) z‖ = 0
        by_cases hz : dbarW (chiC m) z = 0
        · simp [hz]
        · have h1 : R < ‖z‖ := by
            have h2 := (hF2supp z hz).1
            linarith
          rw [hR0 z h1.le]
          simp
      rw [show (∫ z, PQ2 z) = ∫ z, (0:ℝ) from by
        apply integral_congr_ae
        filter_upwards with z
        exact hzero z]
      simp
    have hQQ : (∫ z, Q z) + (∫ z, Q2 z) ≤ 8 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) :=
      calc (∫ z, Q z) + (∫ z, Q2 z)
          ≤ 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1)
              + 4 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) := add_le_add hQbu hQ2bu
        _ = 8 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) := by ring
    have hfin : 8 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1)
        + 8 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1) ≤ K / ((m:ℝ)+1) := by
      have hL : 8 * Real.pi * C ^ 2 * Cbump / ((m:ℝ)+1)
            + 8 * Real.pi * C ^ 2 * Cbump ^ 2 / ((m:ℝ)+1)
          = (8 * Real.pi * C ^ 2 * Cbump + 8 * Real.pi * C ^ 2 * Cbump ^ 2) / ((m:ℝ)+1) :=
        (add_div _ _ _).symm
      have hA : (0:ℝ) ≤ Real.pi * C ^ 2 * Cbump := by
        have := Cbump_nonneg; have := Real.pi_pos; positivity
      rw [hL, hKdef]
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    have hcomb : ∫ z, P z ≤ (∫ z, P2 z)
        + ((2 * (∫ z, PQ2 z) + ∫ z, Q2 z) + (2 * (∫ z, PQ z) + ∫ z, Q z)) := by
      linarith [hm1, hm2, hIBeq]
    have htot : ∫ z, P z ≤ (∫ z, P2 z) + K / ((m:ℝ)+1) := by
      linarith [hcomb, hPQu, hQQ, hIz, hfin]
    simpa only [hPdef, hP2def] using htot
  have hAi := iSup_lintegral_normSq_chiC_mul (dW g) ((continuous_dW hg1).measurable)
  have hBi := iSup_lintegral_normSq_chiC_mul (dbarW g) ((continuous_dbarW hg1).measurable)
  by_cases hBtop : (∫⁻ z, ENNReal.ofReal (‖dbarW g z‖ ^ 2)) = ⊤
  · rw [hBtop]
    exact le_top
  · refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have hεpos : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    set N : ℕ := max (⌈K / (ε:ℝ)⌉₊) (⌈2 * R⌉₊) + 1 with hNdef
    have hNK : K ≤ (ε:ℝ) * ((N:ℝ) + 1) := by
      have h1 : K / (ε:ℝ) ≤ ((⌈K / (ε:ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈K / (ε:ℝ)⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) := by
        have h3 : (⌈K / (ε:ℝ)⌉₊ : ℕ) ≤ N := by
          rw [hNdef]
          exact le_trans (le_max_left _ _) (Nat.le_succ _)
        exact_mod_cast h3
      have h4 : K / (ε:ℝ) ≤ (N:ℝ) + 1 := by linarith
      rw [div_le_iff₀ hεpos] at h4
      linarith
    have hNR : 2 * R < (N:ℝ) + 1 := by
      have h3 : (⌈2 * R⌉₊ : ℕ) ≤ N := by
        rw [hNdef]
        exact le_trans (le_max_right _ _) (Nat.le_succ _)
      have h4 : ((⌈2 * R⌉₊ : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h3
      have h5 : (2 * R : ℝ) ≤ ((⌈2 * R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    rw [← hAi]
    apply iSup_le
    intro m
    set m' : ℕ := max m N with hm'def
    have hNm' : (N:ℝ) ≤ (m':ℝ) := by
      have h3 : N ≤ m' := by
        rw [hm'def]
        exact le_max_right _ _
      exact_mod_cast h3
    have hm'R : 2 * R < (m':ℝ) + 1 := by linarith
    have hst := hstep m' hm'R
    have hm'm : (∫⁻ z, ENNReal.ofReal (‖chiC m z * dW g z‖ ^ 2))
        ≤ ∫⁻ z, ENNReal.ofReal (‖chiC m' z * dW g z‖ ^ 2) :=
      lintegral_mono (fun z => (monotone_ofReal_normSq_chiC_mul (dW g)) (le_max_left m N) z)
    have hAeq : (∫⁻ z, ENNReal.ofReal (‖chiC m' z * dW g z‖ ^ 2))
        = ENNReal.ofReal (∫ z, ‖chiC m' z * dW g z‖ ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal (hint1 m')
        (Filter.Eventually.of_forall (fun z => by positivity))).symm
    have hBeq : (∫⁻ z, ENNReal.ofReal (‖chiC m' z * dbarW g z‖ ^ 2))
        = ENNReal.ofReal (∫ z, ‖chiC m' z * dbarW g z‖ ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal (hint2 m')
        (Filter.Eventually.of_forall (fun z => by positivity))).symm
    have hBmle : (∫⁻ z, ENNReal.ofReal (‖chiC m' z * dbarW g z‖ ^ 2))
        ≤ (∫⁻ z, ENNReal.ofReal (‖dbarW g z‖ ^ 2)) := by
      rw [← hBi]
      exact le_iSup (fun m : ℕ => ∫⁻ z, ENNReal.ofReal (‖chiC m z * dbarW g z‖ ^ 2)) m'
    have hm'pos : (0:ℝ) < (m':ℝ) + 1 := by positivity
    have hKm'ε : K / ((m':ℝ)+1) ≤ (ε:ℝ) := by
      have hd : (0:ℝ) < (m':ℝ)+1 := hm'pos
      have h1 : K / ((m':ℝ)+1) ≤ ((ε:ℝ) * ((N:ℝ)+1)) / ((m':ℝ)+1) :=
        div_le_div_of_nonneg_right hNK (le_of_lt hd)
      have h2 : ((ε:ℝ) * ((N:ℝ)+1)) / ((m':ℝ)+1) ≤ ((ε:ℝ) * ((m':ℝ)+1)) / ((m':ℝ)+1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : (N:ℝ)+1 ≤ (m':ℝ)+1) hεpos.le) (le_of_lt hd)
      have h3 : ((ε:ℝ) * ((m':ℝ)+1)) / ((m':ℝ)+1) = (ε:ℝ) := by
        rw [mul_div_assoc, div_self (ne_of_gt hd), mul_one]
      linarith
    calc (∫⁻ z, ENNReal.ofReal (‖chiC m z * dW g z‖ ^ 2))
        ≤ (∫⁻ z, ENNReal.ofReal (‖chiC m' z * dW g z‖ ^ 2)) := hm'm
      _ = ENNReal.ofReal (∫ z, ‖chiC m' z * dW g z‖ ^ 2) := hAeq
      _ ≤ ENNReal.ofReal ((∫ z, ‖chiC m' z * dbarW g z‖ ^ 2) + K / ((m':ℝ)+1)) :=
            ENNReal.ofReal_le_ofReal hst
      _ = ENNReal.ofReal (∫ z, ‖chiC m' z * dbarW g z‖ ^ 2) + ENNReal.ofReal (K / ((m':ℝ)+1)) :=
            ENNReal.ofReal_add (p := ∫ z, ‖chiC m' z * dbarW g z‖ ^ 2)
              (q := K / ((m':ℝ)+1)) (by positivity) (div_nonneg hKnn (le_of_lt hm'pos))
      _ ≤ (∫⁻ z, ENNReal.ofReal (‖dbarW g z‖ ^ 2)) + (ε : ENNReal) := by
            refine add_le_add ?_ ?_
            · rw [← hBeq]
              exact hBmle
            · rw [← ENNReal.ofReal_coe_nnreal (p := ε)]
              exact ENNReal.ofReal_le_ofReal hKm'ε

/-! ## The Beurling transform is an `L²` contraction -/

/-- The `L²` isometry of the Beurling transform on smooth compactly supported functions:
`‖beurling f‖_{L²} ≤ ‖f‖_{L²}`.  Indeed `beurling f = dW (cauchyT f)`
(`Work.Beltrami.dW_cauchyT_eq_beurling_radial`) and `dbarW (cauchyT f) = f`
(`Work.Beltrami.dbarW_cauchyT`), while `∫⁻ ‖dW h‖² ≤ ∫⁻ ‖dbarW h‖²` for a smooth `h` with
compactly supported `dbarW h` and decay `O(1/‖z‖)` for `h` and `∇h`
(`Work.Beltrami.lintegral_normSq_dW_le`), which `cauchyT f` satisfies
(`Work.Beltrami.cauchyT_decay`). -/
theorem beurling_eLpNorm_le_of_smooth (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    eLpNorm (beurling f) 2 volume ≤ eLpNorm f 2 volume := by
  obtain ⟨C, hC, hdec⟩ := cauchyT_decay f hf hc
  have hg : ContDiff ℝ ∞ (cauchyT f) := contDiff_cauchyT f hf hc
  have hdbar : dbarW (cauchyT f) = f := funext (dbarW_cauchyT f hf hc)
  have hdW : ∀ z : ℂ, dW (cauchyT f) z = beurling f z := dW_cauchyT_eq_beurling_radial f hf hc
  have hfc : HasCompactSupport (dbarW (cauchyT f)) := by rw [hdbar]; exact hc
  have hmain : (∫⁻ z, ENNReal.ofReal (‖dW (cauchyT f) z‖ ^ 2))
      ≤ ∫⁻ z, ENNReal.ofReal (‖dbarW (cauchyT f) z‖ ^ 2) :=
    lintegral_normSq_dW_le (cauchyT f) hg hfc hC.le hdec
  have hg1 : ContDiff ℝ 1 (cauchyT f) := hg.of_le (by norm_num)
  have hmn : (∫⁻ z, ‖dW (cauchyT f) z‖ₑ ^ (2:ℝ))
      ≤ (∫⁻ z, ‖dbarW (cauchyT f) z‖ₑ ^ (2:ℝ)) := by
    have e1 : (∫⁻ z, ‖dW (cauchyT f) z‖ₑ ^ (2:ℝ))
        = ∫⁻ z, ENNReal.ofReal (‖dW (cauchyT f) z‖ ^ 2) :=
      lintegral_congr (fun z => enorm_rpow_two_ofReal _)
    have e2 : (∫⁻ z, ‖dbarW (cauchyT f) z‖ₑ ^ (2:ℝ))
        = ∫⁻ z, ENNReal.ofReal (‖dbarW (cauchyT f) z‖ ^ 2) :=
      lintegral_congr (fun z => enorm_rpow_two_ofReal _)
    rw [e1, e2]
    exact hmain
  have hR2 : eLpNorm (dW (cauchyT f)) 2 volume ≤ eLpNorm (dbarW (cauchyT f)) 2 volume := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
          (continuous_dW hg1).aestronglyMeasurable,
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
          (continuous_dbarW hg1).aestronglyMeasurable]
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    simpa using hmn
  have hbeur : eLpNorm (dW (cauchyT f)) 2 volume = eLpNorm (beurling f) 2 volume :=
    eLpNorm_congr_ae (Filter.Eventually.of_forall hdW)
  have hfdeq : eLpNorm (dbarW (cauchyT f)) 2 volume = eLpNorm f 2 volume := by rw [hdbar]
  rw [hbeur, hfdeq] at hR2
  exact hR2

/-- From the smooth case to continuous bounded `α`-Hölder compactly supported functions, by
mollification (`Work.Beltrami.mollification_holder_approx`) and Fatou.

If `beurling` is an `L²` contraction on `C_c^∞`, then for every continuous `f` bounded by `M`,
`α`-Hölder with constant `K` (`0 < α < 1`) and supported in the ball of radius `R`, `beurling f`
is in `L²` with `‖beurling f‖_{L²} ≤ ‖f‖_{L²}`: approximate `f` by smooth compactly supported
`u n` which are still bounded by `M`, `α`-Hölder with constant `K`, supported in the ball of
radius `R + 1`, with `‖u n‖_{L²} ≤ ‖f‖_{L²}`; `beurling (u n) → beurling f` pointwise
(`Work.Beltrami.tendsto_beurling_of_tendsto`) and Fatou
(`MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`) gives the claim. -/
theorem beurling_eLpNorm_le_of_holder
    (Hsmooth : ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      eLpNorm (beurling f) 2 volume ≤ eLpNorm f 2 volume)
    {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) {f : ℂ → ℂ}
    (hf : Continuous f) (hM : ∀ z, ‖f z‖ ≤ M)
    (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    MemLp (beurling f) 2 volume ∧
      eLpNorm (beurling f) 2 volume ≤ eLpNorm f 2 volume := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  have hK0 : 0 ≤ K := by
    have h := hK 0 1
    have h1 : ‖(0 : ℂ) - 1‖ ^ α = 1 := by
      rw [show (0 : ℂ) - 1 = -(1 : ℂ) by ring, norm_neg, norm_one, Real.one_rpow]
    rw [h1, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hfL2 : MemLp f 2 volume := memLp_of_bounded_supported hf hM hsupp
  obtain ⟨u, hu_smooth, hu_cs, hu_L2, hu_conv, hu_bound, hu_holder, hu_supp⟩ :=
    mollification_holder_approx hf hM hK hsupp hfL2
  have hbdd : ∀ᶠ n in Filter.atTop, eLpNorm (beurling (u n)) 2 volume ≤ eLpNorm f 2 volume :=
    Filter.Eventually.of_forall fun n => le_trans (Hsmooth (u n) (hu_smooth n) (hu_cs n)) (hu_L2 n)
  have hf_asm : ∀ n, AEStronglyMeasurable (beurling (u n)) volume := fun n =>
    aestronglyMeasurable_of_eLpNorm_ne_top
      ((le_trans (Hsmooth (u n) (hu_smooth n) (hu_cs n)) (hu_L2 n)).trans_lt hfL2.eLpNorm_lt_top).ne
  have hconv : ∀ z, Filter.Tendsto (fun n => beurling (u n) z) Filter.atTop
      (nhds (beurling f z)) :=
    tendsto_beurling_of_tendsto hα hM0 hK0 hu_bound hu_holder hu_supp hu_conv
  have hconv_ae : ∀ᵐ z ∂volume,
      Filter.Tendsto (fun n => beurling (u n) z) Filter.atTop (nhds (beurling f z)) :=
    Filter.Eventually.of_forall hconv
  have hg_asm : AEStronglyMeasurable (beurling f) volume :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hf_asm hconv_ae
  have hineq : eLpNorm (beurling f) 2 volume ≤ eLpNorm f 2 volume :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hbdd hf_asm hg_asm hconv_ae
  exact ⟨lt_of_le_of_lt hineq hfL2.eLpNorm_lt_top, hineq⟩

/-- **The Beurling transform `beurling` is bounded on `L²` with a constant independent of the
function.**  For every continuous `α`-Hölder (`0 < α < 1`) function `f` that is bounded by `M` and
supported in the ball of radius `R`, `beurling f` is square integrable with
`‖beurling f‖_{L²} ≤ C ‖f‖_{L²}`, where `C` depends on nothing (neither `f` nor `α, M, K, R`).
(Actually the sharp constant is `1`.) -/
theorem beurling_isometry_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) {f : ℂ → ℂ}
      (hf : Continuous f) (hM : ∀ z, ‖f z‖ ≤ M)
      (hK : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) (hsupp : ∀ z, R < ‖z‖ → f z = 0),
      MemLp (beurling f) 2 volume ∧
        eLpNorm (beurling f) 2 volume ≤ ENNReal.ofReal C * eLpNorm f 2 volume := by
  refine ⟨1, one_pos, ?_⟩
  intro α M K R hα hα1 hR f hf hM hK hsupp
  obtain ⟨hmem, hineq⟩ := beurling_eLpNorm_le_of_holder
    (fun g hg hc => beurling_eLpNorm_le_of_smooth g hg hc) hα hα1 hf hM hK hsupp
  exact ⟨hmem, by simpa using hineq⟩

end

end Work.Beltrami
