import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.integral_comp_normSq
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.cauchyPompeiu
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.PlanarCauchy

/-!
# The Cauchy--Pompeiu representation formula on `ℂ`

For `φ : ℂ → ℂ` of class `C¹` with compact support and every `z : ℂ`,

  `∫ ζ, (∂̄φ)(ζ)/(ζ - z) dA(ζ) = -2π φ(z)`,

where `dbar = ∂_x + i ∂_y = 2 ∂_z̄` is the *unscaled* `∂̄` of `Defs.lean`; equivalently
`φ(z) = -(1/2π) ∫ ζ, (∂̄φ)(ζ)/(ζ - z) dA(ζ)`, the classical Cauchy–Pompeiu formula.  (With the
kernel `1/(ζ-z)` and the scaled operator `∂_z̄` the constant would be `-π`; the factor `2` is
exactly the normalisation of `dbar`.)

This is the representation that makes the *duality* proof of the Runge approximation property work:
it turns `∫_K f dμ` into `-(1/2π) ∫ (∂̄(χf))(ζ) G(ζ) dA(ζ)` with `G(ζ) = ∫_K dμ(x)/(ζ - x)`
(Fubini), and `G` is holomorphic off `K`.  Together with `dbar_solvable` (∂̄-solvability for
compactly supported `C^∞` data) it is the analytic heart of the Behnke–Stein / Cousin chapter.

## Proof

The proof regularises the singularity at `η = 0` with the radial cutoffs of `cauchyPompeiu.lean`:

* `G_δ η := cutChi δ η * φ η / η` is `C¹` with compact support (`cutChi δ` vanishes near `0`),
  so `∫ ∂̄G_δ = 0` (`integral_dbar_eq_zero`), which expands (product rule, `∂̄(1/·) = 0`) into
  `∫ cutChi δ η * (∂̄φ η)/η + ∫ 2 (deriv (cutProf δ))(‖η‖²) φ η = 0`;
* as `δ → 0⁺` the first integral tends to `∫ (∂̄φ η)/η` (dominated convergence, the kernel `1/η`
  being locally integrable in dimension two, `PlanarCauchy`), while the second tends to `2π φ 0`:
  its radial part is computed by `integral_comp_normSq` and the fundamental theorem of calculus
  (`∫_0^∞ deriv (cutProf δ) = cutProf δ ∞ - cutProf δ 0 = 1`), and the remainder is `O(δ)` because
  `φ` is Lipschitz and `‖η‖ ≤ δ` on the support of `deriv (cutProf δ)(‖·‖²)`;
* translation invariance of Lebesgue measure (`integral_add_right_eq_self`) and
  `fderiv_comp_add_right` give the general `z` from the case `z = 0`.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-! ### The cutoff profiles -/

theorem cutProf_nonneg (δ σ : ℝ) : 0 ≤ cutProf δ σ := Real.smoothTransition.nonneg _

theorem cutProf_le_one (δ σ : ℝ) : cutProf δ σ ≤ 1 := Real.smoothTransition.le_one _

theorem cutProf_mono {δ : ℝ} (hδ : 0 < δ) : Monotone (cutProf δ) := by
  intro a b hab
  simp only [cutProf]
  refine Real.smoothTransition.monotone ?_
  have : 2 * a / δ ^ 2 ≤ 2 * b / δ ^ 2 := by gcongr
  linarith

theorem contDiff_cutProf (δ : ℝ) (n : ℕ∞) : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (cutProf δ) := by
  have h1 : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => 2 * σ / δ ^ 2 - 1) := by
    have h : (fun σ : ℝ => 2 * σ / δ ^ 2 - 1) = fun σ : ℝ => (2 / δ ^ 2) * σ - 1 := by
      funext σ; ring
    rw [h]
    exact ContDiff.sub (((contDiff_id (𝕜 := ℝ)).const_smul (2 / δ ^ 2)) :
      ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) fun σ : ℝ => (2 / δ ^ 2) * σ) contDiff_const
  exact (Real.smoothTransition.contDiff (n := n)).comp h1

theorem deriv_cutProf_eq_zero_of_lt {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : σ < δ ^ 2 / 2) :
    deriv (cutProf δ) σ = 0 := by
  have hev : cutProf δ =ᶠ[𝓝 σ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_id continuous_const |>.mem_nhds hσ] with σ' hσ'
    exact cutProf_eq_zero hδ (le_of_lt hσ')
  rw [hev.deriv_eq, deriv_const]

theorem deriv_cutProf_eq_zero_of_gt {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : δ ^ 2 < σ) :
    deriv (cutProf δ) σ = 0 := by
  have hev : cutProf δ =ᶠ[𝓝 σ] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_const continuous_id |>.mem_nhds hσ] with σ' hσ'
    exact cutProf_eq_one hδ (le_of_lt hσ')
  rw [hev.deriv_eq, deriv_const]

theorem support_deriv_cutProf_subset {δ : ℝ} (hδ : 0 < δ) :
    Function.support (deriv (cutProf δ)) ⊆ Set.Icc (δ ^ 2 / 2) (δ ^ 2) := by
  intro σ hσ
  rw [Function.mem_support] at hσ
  exact ⟨by by_contra h; exact hσ (deriv_cutProf_eq_zero_of_lt hδ (lt_of_not_ge h)),
    by by_contra h; exact hσ (deriv_cutProf_eq_zero_of_gt hδ (lt_of_not_ge h))⟩

theorem deriv_cutProf_nonneg {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) : 0 ≤ deriv (cutProf δ) σ :=
  Monotone.deriv_nonneg (cutProf_mono hδ)

theorem integral_deriv_cutProf {δ : ℝ} (hδ : 0 < δ) :
    ∫ σ in Set.Ioi (0 : ℝ), deriv (cutProf δ) σ = 1 := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hcont : Continuous fun σ : ℝ => deriv (cutProf δ) σ :=
    (contDiff_cutProf δ 2).continuous_deriv (by norm_num)
  have hdiff : ∀ σ ∈ Set.uIcc (0 : ℝ) (δ ^ 2), DifferentiableAt ℝ (cutProf δ) σ :=
    fun σ _ => ((contDiff_cutProf δ 1).differentiable (by norm_num)).differentiableAt
  have e1 : ∫ σ in Set.Ioi (0 : ℝ), deriv (cutProf δ) σ
      = ∫ σ : ℝ, deriv (cutProf δ) σ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun σ hσ => by
      rw [Set.mem_Ioi, not_lt] at hσ
      exact deriv_cutProf_eq_zero_of_lt hδ (by linarith))
  have e2 : ∫ σ in Set.Icc (δ ^ 2 / 2) (δ ^ 2), deriv (cutProf δ) σ
      = ∫ σ : ℝ, deriv (cutProf δ) σ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun σ hσ => by
      by_contra h
      exact hσ (support_deriv_cutProf_subset hδ (Function.mem_support.mpr h)))
  have e3 : ∫ σ in Set.Icc (δ ^ 2 / 2) (δ ^ 2), deriv (cutProf δ) σ
      = ∫ σ in (δ ^ 2 / 2)..δ ^ 2, deriv (cutProf δ) σ := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have e4 : ∫ σ in (δ ^ 2 / 2)..δ ^ 2, deriv (cutProf δ) σ = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub (f := cutProf δ)
      (fun σ _ => ((contDiff_cutProf δ 1).differentiable (by norm_num)).differentiableAt)
      (hcont.intervalIntegrable _ _)]
    rw [cutProf_eq_one hδ (by linarith [hδ2]), cutProf_eq_zero hδ (by linarith [hδ2])]
    ring
  rw [e1, ← e2, e3, e4]

/-! ### The cutoff `cutChi` -/

theorem cutChi_eq_zero_of_le {δ : ℝ} (hδ : 0 < δ) {η : ℂ} (h : ‖η‖ ^ 2 ≤ δ ^ 2 / 2) :
    cutChi δ η = 0 := by
  simp [cutChi, cutProf_eq_zero hδ h]

theorem cutChi_eq_one_of_le {δ : ℝ} (hδ : 0 < δ) {η : ℂ} (h : δ ^ 2 ≤ ‖η‖ ^ 2) :
    cutChi δ η = 1 := by
  simp [cutChi, cutProf_eq_one hδ h]

theorem norm_cutChi_le_one (δ : ℝ) (η : ℂ) : ‖cutChi δ η‖ ≤ 1 := by
  have h : ‖cutChi δ η‖ = |cutProf δ (‖η‖ ^ 2)| := by simp [cutChi]
  rw [h, abs_of_nonneg (cutProf_nonneg δ (‖η‖ ^ 2))]
  exact cutProf_le_one δ (‖η‖ ^ 2)

/-- `∂̄` of the cutoff `cutChi δ` has compact support (it is supported in the annulus
`δ²/2 ≤ ‖η‖² ≤ δ²`). -/
theorem hasCompactSupport_dbar_cutChi {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun η : ℂ => dbar (cutChi δ) η) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) δ) ?_
  intro η hη
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hle
  push_neg at hle
  have hev : cutChi δ =ᶠ[𝓝 η] (fun _ : ℂ => (1 : ℂ)) := by
    have hmem : {η' : ℂ | (δ + ‖η‖) / 2 < ‖η'‖} ∈ 𝓝 η := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) ?_
      simp only [Set.mem_ofPred_eq]; linarith
    filter_upwards [hmem] with η' hη'
    refine cutChi_eq_one_of_le hδ ?_
    have h2 : δ < ‖η'‖ := by linarith
    nlinarith [norm_nonneg η', hle]
  have hval : dbar (cutChi δ) η = 0 := by rw [dbar_congr hev, dbar_const]
  exact (Function.mem_support.mp hη) hval

/-- Pointwise form of the product rule for `∂̄ (cutChi δ · φ/·)` on `η ≠ 0`. -/
theorem dbar_cutChi_mul_div (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) {δ : ℝ} (hδ : 0 < δ)
    {η : ℂ} (hη : η ≠ 0) :
    dbar (fun w : ℂ => cutChi δ w * φ w / w) η
      = 2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) * φ η
        + cutChi δ η * (dbar φ η / η) := by
  have h1 : (fun w : ℂ => cutChi δ w * φ w / w)
      = fun w : ℂ => cutChi δ w * (φ w / w) := by funext w; ring
  rw [h1]
  have hd1 : DifferentiableAt ℝ (cutChi δ) η :=
    ((contDiff_cutChi δ 1).differentiable (by norm_num)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun w : ℂ => φ w / w) η := by
    have hmul : DifferentiableAt ℝ (fun w : ℂ => φ w * w⁻¹) η :=
      ((hφ.differentiable one_ne_zero).differentiableAt).mul
        (differentiableAt_inv (𝕜 := ℝ) (x := η) hη)
    simpa [div_eq_mul_inv] using hmul
  rw [dbar_mul _ _ _ hd1 hd2]
  have h3 : dbar (fun w : ℂ => φ w / w) η = dbar φ η / η := by
    have h4 : (fun w : ℂ => φ w / w) = fun w : ℂ => φ w * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [h4, dbar_mul _ _ _ ((hφ.differentiable one_ne_zero).differentiableAt)
      (differentiableAt_inv (𝕜 := ℝ) (x := η) hη), dbar_inv η hη, mul_zero, add_zero]
    rw [div_eq_mul_inv]
  have h5 : dbar (cutChi δ) η * (φ η / η)
      = 2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) * φ η := by
    rw [← dbar_cutChi_div δ hδ hη]
    field_simp
  rw [h3, h5]

theorem ae_ne_zero : ∀ᵐ η ∂(volume : Measure ℂ), η ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {η : ℂ | ¬η ≠ 0} = {(0 : ℂ)} := by ext η; simp
  rw [h]
  exact measure_singleton 0

/-- A compactly supported `C¹` function on `ℂ` is Lipschitz. -/
theorem exists_lipschitz_const (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∃ L : ℝ, ∀ a b : ℂ, ‖φ a - φ b‖ ≤ L * ‖a - b‖ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  have hzero : ∀ z : ℂ, R < ‖z‖ → fderiv ℝ φ z = 0 := by
    intro z hz
    have hopen : IsOpen {z' : ℂ | R < ‖z'‖} := isOpen_lt continuous_const continuous_norm
    have hev : φ =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen.mem_nhds hz] with z' hz'
      exact image_eq_zero_of_notMem_tsupport fun hmem => by
        have h := hR hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact absurd h (not_le_of_gt hz')
    rw [hev.fderiv_eq]; simp
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hφ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max C 1, fun a b => ?_⟩
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun x _ => (hφ.differentiable one_ne_zero).differentiableAt) (fun x _ => ?_) convex_univ
    (Set.mem_univ a) (Set.mem_univ b)
  by_cases hx : ‖x‖ ≤ R
  · exact le_trans (hC x (by rwa [Metric.mem_closedBall, dist_zero_right])) (le_max_left _ _)
  · rw [hzero x (lt_of_not_ge hx)]
    simp only [norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

theorem continuous_dbar (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) :
    Continuous fun η : ℂ => dbar φ η := by
  have hder : Continuous fun η : ℂ => fderiv ℝ φ η := hφ.continuous_fderiv one_ne_zero
  rw [show (fun η : ℂ => dbar φ η)
      = fun η : ℂ => fderiv ℝ φ η 1 + Complex.I * fderiv ℝ φ η Complex.I from rfl]
  exact (hder.clm_apply continuous_const).add
    (continuous_const.mul (hder.clm_apply continuous_const))

theorem hasCompactSupport_dbar (φ : ℂ → ℂ) (hc : HasCompactSupport φ) :
    HasCompactSupport fun η : ℂ => dbar φ η := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hzt
  push_neg at hzt
  have hzts : z ∉ tsupport φ := fun hmem => by
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact not_le_of_gt hzt this
  have hev : φ =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hzts] with w hw
    exact image_eq_zero_of_notMem_tsupport (by simpa using hw)
  exact hz (by rw [dbar_congr hev]; exact dbar_zero z)

theorem integrable_dbar_div (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable fun η : ℂ => dbar φ η / η := by
  have := Work.Analysis.RiemannSurface.integrable_div_sub (continuous_dbar φ hφ)
    (hasCompactSupport_dbar φ hc) 0
  simpa using this

/-! ### The key algebraic step -/

theorem integral_cutChi_mul_dbar_div (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ η : ℂ, cutChi δ η * (dbar φ η / η)
      = -∫ η : ℂ, (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η := by
  have hnear : {η' : ℂ | ‖η'‖ ^ 2 < δ ^ 2 / 2} ∈ 𝓝 (0 : ℂ) :=
    IsOpen.mem_nhds (isOpen_lt (continuous_norm.pow 2) continuous_const) (by simp [hδ])
  have hGcd : ContDiff ℝ 1 (fun w : ℂ => cutChi δ w * φ w / w) := by
    rw [contDiff_iff_contDiffAt]
    intro η
    rcases eq_or_ne η 0 with rfl | hη
    · have hev : (fun w : ℂ => cutChi δ w * φ w / w) =ᶠ[𝓝 (0 : ℂ)] (fun _ : ℂ => (0 : ℂ)) := by
        filter_upwards [hnear] with η' hη'
        rw [cutChi_eq_zero_of_le hδ (le_of_lt hη')]
        ring
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hcut : ContDiffAt ℝ 1 (cutChi δ) η := (contDiff_cutChi δ 1).contDiffAt
      have hinv : ContDiffAt ℝ 1 (fun w : ℂ => w⁻¹) η :=
        (contDiffAt_id (𝕜 := ℝ) (x := η)).inv hη
      have hmain : ContDiffAt ℝ 1 (fun w : ℂ => cutChi δ w * φ w * w⁻¹) η :=
        (hcut.mul hφ.contDiffAt).mul hinv
      simpa [div_eq_mul_inv, mul_assoc] using hmain
  have hGcs : HasCompactSupport (fun w : ℂ => cutChi δ w * φ w / w) :=
    HasCompactSupport.mono' hc fun z hz => subset_tsupport φ (by
      rw [Function.mem_support] at hz ⊢
      intro hzφ
      exact hz (by rw [hzφ]; ring))
  have hzero : ∫ η : ℂ, dbar (fun w : ℂ => cutChi δ w * φ w / w) η = 0 :=
    integral_dbar_eq_zero _ hGcd hGcs
  have hae : (fun η : ℂ => dbar (fun w : ℂ => cutChi δ w * φ w / w) η)
      =ᵐ[volume] (fun η : ℂ => (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η
        + cutChi δ η * (dbar φ η / η)) := by
    filter_upwards [ae_ne_zero] with η hη
    exact dbar_cutChi_mul_div φ hφ hδ hη
  have hint1 : Integrable
      (fun η : ℂ => (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · refine Continuous.mul (Continuous.mul continuous_const ?_) hφ.continuous
      exact Complex.continuous_ofReal.comp
        (((contDiff_cutProf δ 2).continuous_deriv (by norm_num)).comp
          (continuous_norm.pow 2))
    · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) δ) ?_
      intro η hη
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hle
      push_neg at hle
      rw [Function.mem_support] at hη
      refine hη ?_
      have hd : deriv (cutProf δ) (‖η‖ ^ 2) = 0 :=
        deriv_cutProf_eq_zero_of_gt hδ (by nlinarith [hle, norm_nonneg η])
      rw [hd]; simp
  have hcont2 : Continuous (fun η : ℂ => cutChi δ η * (dbar φ η / η)) := by
    rw [continuous_iff_continuousAt]
    intro η
    rcases eq_or_ne η 0 with rfl | hη
    · have hev : (fun η : ℂ => cutChi δ η * (dbar φ η / η))
          =ᶠ[𝓝 (0 : ℂ)] (fun _ => (0 : ℂ)) := by
        filter_upwards [hnear] with η' hη'
        rw [cutChi_eq_zero_of_le hδ (le_of_lt hη')]; ring
      exact (continuousAt_const).congr_of_eventuallyEq hev
    · exact ((contDiff_cutChi δ 1).continuous.continuousAt).mul
        ((continuous_dbar φ hφ).continuousAt.div continuousAt_id hη)
  have hint2 : Integrable (fun η : ℂ => cutChi δ η * (dbar φ η / η)) := by
    refine Integrable.mono' (integrable_dbar_div φ hφ hc).norm
      hcont2.aestronglyMeasurable ?_
    filter_upwards with η
    rw [norm_mul]
    calc ‖cutChi δ η‖ * ‖dbar φ η / η‖ ≤ 1 * ‖dbar φ η / η‖ :=
          mul_le_mul_of_nonneg_right (norm_cutChi_le_one δ η) (norm_nonneg _)
      _ = ‖dbar φ η / η‖ := one_mul _
  rw [integral_congr_ae hae, integral_add hint1 hint2] at hzero
  linear_combination hzero

/-! ### The two limits -/

theorem continuous_cutChi_mul_dbar_div (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun η : ℂ => cutChi δ η * (dbar φ η / η) := by
  rw [continuous_iff_continuousAt]
  intro η
  rcases eq_or_ne η 0 with rfl | hη
  · have hnear : {η' : ℂ | ‖η'‖ ^ 2 < δ ^ 2 / 2} ∈ 𝓝 (0 : ℂ) :=
      IsOpen.mem_nhds (isOpen_lt (continuous_norm.pow 2) continuous_const) (by simp [hδ])
    have hev : (fun η : ℂ => cutChi δ η * (dbar φ η / η)) =ᶠ[𝓝 (0 : ℂ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnear] with η' hη'
      rw [cutChi_eq_zero_of_le hδ (le_of_lt hη')]; ring
    exact (continuousAt_const).congr_of_eventuallyEq hev
  · exact ((contDiff_cutChi δ 1).continuous.continuousAt).mul
      ((continuous_dbar φ hφ).continuousAt.div continuousAt_id hη)

theorem tendsto_integral_cutChi_mul_dbar_div (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    Filter.Tendsto (fun n : ℕ => ∫ η : ℂ, cutChi (1 / ((n : ℝ) + 1)) η * (dbar φ η / η))
      Filter.atTop (𝓝 (∫ η : ℂ, dbar φ η / η)) := by
  refine tendsto_integral_of_dominated_convergence (fun η : ℂ => ‖dbar φ η / η‖) ?_ ?_ ?_ ?_
  · intro n
    exact (continuous_cutChi_mul_dbar_div φ hφ (by positivity)).aestronglyMeasurable
  · exact (integrable_dbar_div φ hφ hc).norm
  · intro n
    filter_upwards with η
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_cutChi_le_one _ _)
  · filter_upwards [ae_ne_zero] with η hη
    have htend : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev : ∀ᶠ n : ℕ in Filter.atTop, cutChi (1 / ((n : ℝ) + 1)) η = 1 := by
      filter_upwards [htend.eventually (eventually_lt_nhds (norm_pos_iff.mpr hη))] with n hn
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine cutChi_eq_one_of_le hpos ?_
      nlinarith [norm_nonneg η, hn, hpos]
    have h1 : Filter.Tendsto (fun n : ℕ => cutChi (1 / ((n : ℝ) + 1)) η) Filter.atTop (𝓝 1) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
    simpa using h1.mul tendsto_const_nhds

theorem integrable_deriv_cutProf_mul (ψ : ℂ → ℂ) (hψ : Continuous ψ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun η : ℂ => (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * ψ η) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact Continuous.mul (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp (((contDiff_cutProf δ 2).continuous_deriv (by norm_num)).comp
        (continuous_norm.pow 2)))) hψ
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) δ) ?_
    intro η hη
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hle
    push_neg at hle
    rw [Function.mem_support] at hη
    refine hη ?_
    have hd : deriv (cutProf δ) (‖η‖ ^ 2) = 0 :=
      deriv_cutProf_eq_zero_of_gt hδ (by nlinarith [hle, norm_nonneg η])
    rw [hd]; simp

theorem integral_two_deriv_cutProf {δ : ℝ} (hδ : 0 < δ) :
    ∫ η : ℂ, (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
  have h1 : ∫ η : ℂ, (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ))
      = 2 * ∫ η : ℂ, ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) := integral_const_mul 2 _
  have h2 : ∫ η : ℂ, ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)
      = ((∫ η : ℂ, deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) := integral_ofReal
  have h3 : ∫ η : ℂ, deriv (cutProf δ) (‖η‖ ^ 2) = Real.pi := by
    rw [integral_comp_normSq (deriv (cutProf δ)), integral_deriv_cutProf hδ, mul_one]
  rw [h1, h2, h3]
  push_cast
  ring

theorem integral_deriv_cutProf_mul_const {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    ∫ η : ℂ, (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * c
      = ((2 * Real.pi : ℝ) : ℂ) * c := by
  rw [integral_mul_const, integral_two_deriv_cutProf hδ]

theorem integral_abs_deriv_cutProf {δ : ℝ} (hδ : 0 < δ) :
    ∫ η : ℂ, |deriv (cutProf δ) (‖η‖ ^ 2)| = Real.pi := by
  rw [integral_comp_normSq (fun σ : ℝ => |deriv (cutProf δ) σ|)]
  have h : ∫ σ in Set.Ioi (0 : ℝ), |deriv (cutProf δ) σ|
      = ∫ σ in Set.Ioi (0 : ℝ), deriv (cutProf δ) σ :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun σ _ => abs_of_nonneg (deriv_cutProf_nonneg hδ σ))
  rw [h, integral_deriv_cutProf hδ, mul_one]

theorem integrable_abs_deriv_cutProf {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun η : ℂ => |deriv (cutProf δ) (‖η‖ ^ 2)|) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · have hcd : Continuous fun η : ℂ => deriv (cutProf δ) (‖η‖ ^ 2) :=
      ((contDiff_cutProf δ 2).continuous_deriv (by norm_num)).comp (continuous_norm.pow 2)
    exact hcd.abs
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) δ) ?_
    intro η hη
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hle
    push_neg at hle
    rw [Function.mem_support] at hη
    refine hη ?_
    rw [deriv_cutProf_eq_zero_of_gt hδ (by nlinarith [hle, norm_nonneg η])]
    simp

theorem norm_integral_deriv_cutProf_mul_sub_le (φ : ℂ → ℂ) (hφc : Continuous φ) {δ L : ℝ}
    (hδ : 0 < δ) (hL0 : 0 ≤ L) (hL : ∀ a b : ℂ, ‖φ a - φ b‖ ≤ L * ‖a - b‖) :
    ‖∫ η : ℂ, (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * (φ η - φ 0)‖
      ≤ 2 * L * Real.pi * δ := by
  have hpt : ∀ η : ℂ, ‖(2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ)) * (φ η - φ 0)‖
      ≤ (2 * L * δ) * |deriv (cutProf δ) (‖η‖ ^ 2)| := by
    intro η
    by_cases hd : deriv (cutProf δ) (‖η‖ ^ 2) = 0
    · rw [hd]; simp
    · have hmem := support_deriv_cutProf_subset hδ (Function.mem_support.mpr hd)
      have hnorm : ‖η‖ ≤ δ := by nlinarith [norm_nonneg η, hδ, hmem.2]
      have hnorm2 : ‖(2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ))‖
          = 2 * |deriv (cutProf δ) (‖η‖ ^ 2)| := by
        rw [show (2 * ((deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ))
            = (((2 : ℝ) * deriv (cutProf δ) (‖η‖ ^ 2) : ℝ) : ℂ) from by push_cast; ring]
        simp
      rw [norm_mul, hnorm2]
      have h3 : ‖φ η - φ 0‖ ≤ L * ‖η‖ := by simpa using hL η 0
      have h4 : ‖φ η - φ 0‖ ≤ L * δ := le_trans h3 (mul_le_mul_of_nonneg_left hnorm hL0)
      have h5 : 2 * |deriv (cutProf δ) (‖η‖ ^ 2)| * ‖φ η - φ 0‖
          ≤ 2 * |deriv (cutProf δ) (‖η‖ ^ 2)| * (L * δ) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      calc 2 * |deriv (cutProf δ) (‖η‖ ^ 2)| * ‖φ η - φ 0‖
          ≤ 2 * |deriv (cutProf δ) (‖η‖ ^ 2)| * (L * δ) := h5
        _ = (2 * L * δ) * |deriv (cutProf δ) (‖η‖ ^ 2)| := by ring
  have hcont : Continuous fun η : ℂ => φ η - φ 0 := hφc.sub continuous_const
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => norm_nonneg _)
    ((integrable_abs_deriv_cutProf hδ).const_mul (2 * L * δ))
    (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul, integral_abs_deriv_cutProf hδ]
  exact le_of_eq (by ring)

theorem tendsto_integral_deriv_cutProf_mul (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    Filter.Tendsto (fun n : ℕ => ∫ η : ℂ,
        (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η)
      Filter.atTop (𝓝 (((2 * Real.pi : ℝ) : ℂ) * φ 0)) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_const φ hφ hc
  have hL0 : (0 : ℝ) ≤ max L 0 := le_max_right _ _
  have hL' : ∀ a b : ℂ, ‖φ a - φ b‖ ≤ max L 0 * ‖a - b‖ := fun a b =>
    le_trans (hL a b) (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hdiff : ∀ n : ℕ,
      (∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η)
        - ((2 * Real.pi : ℝ) : ℂ) * φ 0
      = ∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ))
          * (φ η - φ 0) := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsplit : (∫ η : ℂ,
          (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η)
        = (∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ))
            * (φ η - φ 0))
          + (∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ))
            * φ 0) := by
      rw [← integral_add
        (integrable_deriv_cutProf_mul (fun η => φ η - φ 0) (hφ.continuous.sub continuous_const) hδ)
        (integrable_deriv_cutProf_mul (fun _ => φ 0) continuous_const hδ)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      ring
    rw [hsplit, integral_deriv_cutProf_mul_const hδ (φ 0)]
    ring
  have hbound : ∀ n : ℕ,
      ‖(∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η)
        - ((2 * Real.pi : ℝ) : ℂ) * φ 0‖
      ≤ 2 * max L 0 * Real.pi * (1 / ((n : ℝ) + 1)) := by
    intro n
    rw [hdiff n]
    exact norm_integral_deriv_cutProf_mul_sub_le φ hφ.continuous (by positivity) hL0 hL'
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * max L 0 * Real.pi * (1 / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * max L 0 * Real.pi)
    simpa [mul_assoc] using this
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖(∫ η : ℂ,
          (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η)
        - ((2 * Real.pi : ℝ) : ℂ) * φ 0‖) Filter.atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall hbound) hlim
  let c : ℂ := (((2 * Real.pi : ℝ)) : ℂ) * φ 0
  have h2 : Filter.Tendsto (fun n : ℕ => (∫ η : ℂ,
        (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η) - c)
      Filter.atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [c] using hnorm)
  have hconst : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (𝓝 c) := tendsto_const_nhds
  have h3 := h2.add hconst
  simpa [c, sub_add_cancel] using h3

theorem integral_dbar_div_self (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∫ η : ℂ, dbar φ η / η = -(((2 * Real.pi : ℝ)) : ℂ) * φ 0 := by
  have hA : ∀ n : ℕ, (∫ η : ℂ, cutChi (1 / ((n : ℝ) + 1)) η * (dbar φ η / η))
      = -(∫ η : ℂ, (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η) :=
    fun n => integral_cutChi_mul_dbar_div φ hφ hc (δ := 1 / ((n : ℝ) + 1)) (by positivity)
  have hlimA := tendsto_integral_cutChi_mul_dbar_div φ hφ hc
  have hlimB := tendsto_integral_deriv_cutProf_mul φ hφ hc
  have h1 : Filter.Tendsto (fun n : ℕ => ∫ η : ℂ, cutChi (1 / ((n : ℝ) + 1)) η * (dbar φ η / η))
      Filter.atTop (𝓝 (-(((2 * Real.pi : ℝ)) : ℂ) * φ 0)) := by
    have hneg := hlimB.neg
    have : (fun n : ℕ => ∫ η : ℂ, cutChi (1 / ((n : ℝ) + 1)) η * (dbar φ η / η))
        = fun (n : ℕ) => -(∫ η : ℂ,
            (2 * ((deriv (cutProf (1 / ((n : ℝ) + 1))) (‖η‖ ^ 2) : ℝ) : ℂ)) * φ η) := by
      funext n; rw [hA n]
    rw [this]
    simpa [neg_mul] using hneg
  exact tendsto_nhds_unique hlimA h1

theorem dbar_representation (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (z : ℂ) :
    ∫ ζ : ℂ, dbar φ ζ / (ζ - z) = -(((2 * Real.pi : ℝ)) : ℂ) * φ z := by
  have hψcd : ContDiff ℝ 1 (fun w : ℂ => φ (w + z)) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have hψcs : HasCompactSupport (fun w : ℂ => φ (w + z)) := by
    obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) (R + ‖z‖)) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hle
    push_neg at hle
    rw [Function.mem_support] at hw
    refine hw ?_
    have hz : R < ‖w + z‖ := by
      have h1 : ‖w‖ ≤ ‖w + z‖ + ‖z‖ := by
        have := norm_sub_le (w + z) z
        simpa using this
      linarith
    exact image_eq_zero_of_notMem_tsupport fun hmem => by
      have h2 := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      linarith
  have hψ := integral_dbar_div_self (fun w : ℂ => φ (w + z)) hψcd hψcs
  have htrans : (∫ η : ℂ, dbar (fun w : ℂ => φ (w + z)) η / η)
      = ∫ ζ : ℂ, dbar φ ζ / (ζ - z) := by
    have h1 : (∫ η : ℂ, dbar (fun w : ℂ => φ (w + z)) η / η)
        = ∫ η : ℂ, dbar φ (η + z) / η := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      have hshift : dbar (fun w : ℂ => φ (w + z)) η = dbar φ (η + z) := by
        simp only [dbar, fderiv_comp_add_right]
      simp only [hshift]
    have h2 : (∫ η : ℂ, dbar φ (η + z) / η) = ∫ ζ : ℂ, dbar φ ζ / (ζ - z) := by
      have := integral_add_right_eq_self (μ := volume) (fun ζ : ℂ => dbar φ ζ / (ζ - z)) z
      simpa using this
    rw [h1, h2]
  rw [← htrans]
  simpa using hψ

end Work.Analysis.Complex.DbarCauchy
