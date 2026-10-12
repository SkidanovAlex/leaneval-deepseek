import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_uncurry_bsWin_deriv_sq
import Submission.Work.BSKinetic.kinFT_energy_sum
import Submission.Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `FamilyBound_of_le` — the FS cutoff is antitone in the family bound

`Work.BSKinetic.FamilyBound ℓ c` says that the moving-box family form at the FS cutoff
coefficient `fsKinCoeff c = [· − c]₊²` is dominated by the full-space Dirichlet word `dSpace`:

    `bsFamilyForm ℓ (fsKinCoeff c) ψ ≤ dSpace ψ`   for every `ψ ∈ C_c^∞(ℝ³)`.

Since `c ↦ fsKinCoeff c r` is *decreasing* on `c ≥ 0`, the family form is decreasing in `c`
(its `p`-integrand is `fsKinCoeff c ‖p‖` times a nonnegative weight), so the uncut (`c = 0`)
bound implies the bound at every `c ≥ 0`.

The only analytic content is that the two Bochner integrals involved are *not* junk:

* the inner `p`-weight `‖kinFT (χ_u·Q_uψ)‖²` is `L¹` with the `‖p‖²` weight
  (`integrable_bsKinWeight_zero`, from the Schwartz-space Plancherel lemma
  `Work.SmallBoxTBWord.integrable_kinFT_energy_cspt`);
* the outer `u`-integrand `u ↦ bsOneBody ℓ (fsKinCoeff 0) u ψ` is `Integrable`
  (`integrable_bsOneBody_fsKinCoeff_zero`): it is the marginal of the *joint* integrand
  `(x,u) ↦ Σ_k (∂_k(χ_u·Q_uψ)(x))²`, which is `L¹` on the product measure
  (`integrable_uncurry_bsQ_deriv_sq`), the Dirichlet identity
  `bsOneBody ℓ (·)² u ψ = ∫_x Σ_k (∂_k(χ_u·Q_uψ)(x))²` (`bsOneBody_eq_dirichlet_of_ne`, from
  `kinFT_energy_sum`) identifying it with the marginal.

The degenerate case `ℓ = 0` is handled separately: then the window is the constant `χ(0)`, the
box mean vanishes, the `u`-integrand is constant, and the whole family form is `0`
(`bsFamilyForm_zero_eq_zero`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 1. The coefficient is antitone in the cutoff -/

lemma fsKinCoeff_zero_of_nonneg {r : ℝ} (hr : 0 ≤ r) : fsKinCoeff 0 r = r ^ 2 := by
  rw [fsKinCoeff, sub_zero, max_eq_left hr]

lemma fsKinCoeff_zero_le {c : ℝ} (hc : 0 ≤ c) (r : ℝ) :
    fsKinCoeff c r ≤ fsKinCoeff 0 r := by
  rw [fsKinCoeff, fsKinCoeff, sub_zero]
  have hle : max (r - c) 0 ≤ max r 0 :=
    max_le (le_trans (sub_le_self r hc) (le_max_left r 0)) (le_max_right r 0)
  exact pow_le_pow_left₀ (le_max_right _ _) hle 2

/-! ## 2. The `u`-integrand is nonnegative, and monotone in the coefficient -/

lemma bsOneBody_nonneg {ℓ : ℝ} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    0 ≤ bsOneBody ℓ F u ψ := by
  rw [bsOneBody]
  refine mul_nonneg (by positivity) (integral_nonneg ?_)
  intro p
  exact mul_nonneg (hF _) (sq_nonneg _)

lemma bsOneBody_mono_coeff {ℓ : ℝ} {u : ℝ³} {ψ : ℝ³ → ℝ} {F G : ℝ → ℝ}
    (hF : ∀ r, 0 ≤ F r) (hFG : ∀ r, F r ≤ G r)
    (hint : Integrable (fun p : ℝ³ =>
      G ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2)) :
    bsOneBody ℓ F u ψ ≤ bsOneBody ℓ G u ψ := by
  rw [bsOneBody, bsOneBody]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono_of_nonneg (f := fun p : ℝ³ =>
      F ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2)
    (g := fun p : ℝ³ =>
      G ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2)
    (Eventually.of_forall fun p => mul_nonneg (hF _) (sq_nonneg _)) hint
    (Eventually.of_forall fun p => mul_le_mul_of_nonneg_right (hFG _) (sq_nonneg _))

/-! ## 3. The degenerate `ℓ = 0` family form vanishes -/

lemma bsMean_zero (u : ℝ³) (ψ : ℝ³ → ℝ) : bsMean 0 u ψ = 0 := by
  rw [bsMean]
  simp

lemma bsQ_zero (u : ℝ³) (ψ : ℝ³ → ℝ) : bsQ 0 u ψ = ψ := by
  funext x
  simp [bsQ, bsMean_zero]

lemma bsWin_zero (u : ℝ³) : bsWin 0 u = fun x : ℝ³ => chi 0 := by
  funext x
  rw [bsWin, chiScale]
  simp

lemma bsOneBody_zero_eq (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) :
    bsOneBody 0 F u ψ = bsOneBody 0 F 0 ψ := by
  have hfun : (fun z : ℝ³ => (bsWin 0 u z : ℂ) * (bsQ 0 u ψ z : ℂ))
      = fun z : ℝ³ => (bsWin 0 0 z : ℂ) * (bsQ 0 0 ψ z : ℂ) := by
    funext z
    simp only [bsWin_zero u, bsWin_zero 0, bsQ_zero u ψ, bsQ_zero 0 ψ]
  rw [bsOneBody, bsOneBody, hfun]

lemma bsFamilyForm_zero_eq_zero (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) : bsFamilyForm 0 F ψ = 0 := by
  rw [bsFamilyForm]
  rw [show (fun u : ℝ³ => bsOneBody 0 F u ψ)
      = fun _ : ℝ³ => bsOneBody 0 F 0 ψ from funext (bsOneBody_zero_eq F ψ)]
  rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
    MeasureTheory.measure_univ_of_isAddLeftInvariant]
  simp

lemma dSpace_nonneg (ψ : ℝ³ → ℝ) : 0 ≤ dSpace ψ := by
  rw [dSpace]
  exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _

/-! ## 4. The moving window and the box mean: vanishing, smoothness, support -/

/-- `chiScale ℓ` vanishes outside the ball of radius `|ℓ|/2` (any sign of `ℓ ≠ 0`). -/
lemma chiScale_eq_zero_of_norm_gt_abs {ℓ : ℝ} (hℓ : ℓ ≠ 0) {y : ℝ³}
    (h : |ℓ| / 2 < ‖y‖) : chiScale ℓ y = 0 := by
  rw [chiScale]
  apply chi_eq_zero_of_norm_gt
  have hpos : 0 < |ℓ| := abs_pos.mpr hℓ
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have h2 : |ℓ|⁻¹ * (|ℓ| / 2) = 1 / 2 := by
    field_simp
  rw [← h2]
  exact mul_lt_mul_of_pos_left h (inv_pos.mpr hpos)

/-- The derivative of `chiScale ℓ` vanishes outside the ball of radius `|ℓ|/2`. -/
lemma fderiv_chiScale_eq_zero_of_norm_gt_abs {ℓ : ℝ} (hℓ : ℓ ≠ 0) {y v : ℝ³}
    (h : |ℓ| / 2 < ‖y‖) : fderiv ℝ (chiScale ℓ) y v = 0 := by
  have hev : chiScale ℓ =ᶠ[𝓝 y] (fun _ : ℝ³ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds h] with z hz
    exact chiScale_eq_zero_of_norm_gt_abs hℓ hz
  rw [hev.fderiv_eq]
  simp

/-- The centred cube is empty for negative `ℓ`. -/
lemma acube_eq_empty_of_neg {ℓ : ℝ} (hℓ : ℓ < 0) : acube ℓ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_acube_iff] at hy
  have h := hy 0
  simp only [Set.mem_Icc] at h
  linarith [h.1, h.2]

/-- `ψ` vanishing outside a ball has vanishing derivative outside that ball. -/
lemma fderiv_eq_zero_of_far {R : ℝ} {ψ : ℝ³ → ℝ} (h : ∀ x : ℝ³, R ≤ ‖x‖ → ψ x = 0)
    {x : ℝ³} (hx : R < ‖x‖) : fderiv ℝ ψ x = 0 := by
  have hopen : IsOpen {y : ℝ³ | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hev : ψ =ᶠ[𝓝 x] (fun _ : ℝ³ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact h y (le_of_lt hy)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

/-- A compactly supported function vanishes beyond an explicit radius. -/
private lemma exists_radius_eq_zero_of_hasCompactSupport {ψ : ℝ³ → ℝ} (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ³, R ≤ ‖x‖ → ψ x = 0 := by
  obtain ⟨C, hC⟩ := (hcs.isCompact.isBounded).exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hne
  have hxsupp : x ∈ Function.support ψ := by simpa [Function.mem_support] using hne
  have hle : ‖x‖ ≤ C := hC x (subset_tsupport ψ hxsupp)
  have : C < ‖x‖ := by
    have h1 : C ≤ max C 0 := le_max_left C 0
    linarith
  linarith

/-- The box mean is continuous as a function of the box position, for every `ℓ ≠ 0`. -/
lemma continuous_bsMean_of_ne {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun u : ℝ³ => bsMean ℓ u ψ) := by
  rcases lt_trichotomy ℓ 0 with hneg | hzero | hpos
  · have hempty := acube_eq_empty_of_neg hneg
    have hzero' : (fun u : ℝ³ => bsMean ℓ u ψ) = fun _ => 0 := by
      funext u
      rw [bsMean, hempty, MeasureTheory.setIntegral_empty, mul_zero]
    rw [hzero']
    exact continuous_const
  · exact absurd hzero hℓ
  · obtain ⟨R, _hR0, hψzero⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ³) R).exists_bound_of_continuousOn
      hψ.continuous.continuousOn
    have hC' : ∀ x : ℝ³, ‖ψ x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ closedBall (0 : ℝ³) R
      · exact le_trans (hC x hx) (le_max_left _ _)
      · rw [mem_closedBall, dist_zero_right] at hx
        have hx' : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
        rw [hψzero x hx', norm_zero]
        exact le_max_right _ _
    have hmain : Continuous (fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z)) := by
      refine continuous_of_dominated (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (F := fun u z => ψ (ℓ • u + z)) (bound := fun _ => max C 0) ?_ ?_ ?_ ?_
      · intro u
        exact (hψ.continuous.comp (by fun_prop)).aestronglyMeasurable
      · intro u
        filter_upwards with z
        exact hC' _
      · rw [integrable_const_iff]
        right
        rw [isFiniteMeasure_restrict]
        exact ne_of_lt (acube_lt_top ℓ hpos.le)
      · filter_upwards with z
        exact hψ.continuous.comp (by fun_prop)
    simpa only [bsMean] using hmain.const_mul ((ℓ ^ 3)⁻¹)

/-- The box mean is bounded uniformly in the box position. -/
private lemma exists_abs_bsMean_le {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ M : ℝ, ∀ u : ℝ³, |bsMean ℓ u ψ| ≤ M := by
  obtain ⟨Mψ, hMψ⟩ := hcs.exists_bound_of_continuous hψ
  have hcomp : IsCompact (acube ℓ) := Work.UBBInputs9.B.acube_isCompact ℓ
  have hvol : (volume : Measure ℝ³) (acube ℓ) < ⊤ := hcomp.measure_lt_top
  refine ⟨|(ℓ ^ 3)⁻¹| * (Mψ * (volume : Measure ℝ³).real (acube ℓ)), fun u => ?_⟩
  have h1 : |∫ z in acube ℓ, ψ (ℓ • u + z)| ≤ Mψ * (volume : Measure ℝ³).real (acube ℓ) := by
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hvol (fun z _ => hMψ _)
  rw [bsMean, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- The box mean vanishes once the moving box has left the support of the state. -/
lemma exists_bsMean_eq_zero_of_far {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, ∀ u : ℝ³, R ≤ ‖u‖ → bsMean ℓ u ψ = 0 := by
  rcases lt_trichotomy ℓ 0 with hneg | hzero | hpos
  · refine ⟨0, fun u _ => ?_⟩
    rw [bsMean, acube_eq_empty_of_neg hneg, MeasureTheory.setIntegral_empty, mul_zero]
  · exact absurd hzero hℓ
  · obtain ⟨C₀, hC₀⟩ := hcs.isCompact.exists_bound_of_continuousOn continuous_norm.continuousOn
    have hKb : ∀ y ∈ tsupport ψ, ‖y‖ ≤ C₀ := fun y hy => by
      have h := hC₀ y hy
      rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] at h
    obtain ⟨B, hB⟩ := (acube_isBounded ℓ hpos.le).exists_norm_le
    refine ⟨(C₀ + B + 1) / ℓ, fun u hu => ?_⟩
    have hfar : ∀ z ∈ acube ℓ, C₀ < ‖ℓ • u + z‖ := by
      intro z hz
      have hzb : ‖z‖ ≤ B := hB z hz
      have h2 : ‖ℓ • u‖ - ‖z‖ ≤ ‖ℓ • u + z‖ := by
        have h := norm_sub_norm_le (ℓ • u) (-z)
        simpa using h
      have h3 : ℓ * ‖u‖ ≤ ‖ℓ • u‖ := by
        rw [norm_smul, Real.norm_of_nonneg hpos.le]
      have h4 : C₀ + B + 1 ≤ ℓ * ‖u‖ := by
        have h5 := mul_le_mul_of_nonneg_left hu hpos.le
        rwa [mul_div_cancel₀ _ hℓ] at h5
      linarith
    have hzero' : ∀ z ∈ acube ℓ, ψ (ℓ • u + z) = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport
        (fun hmem => absurd (hKb _ hmem) (not_le.mpr (hfar z hz)))
    rw [bsMean, MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) hzero']
    simp

/-! ## 5. Smoothness and compact support of the windowed mean-free state -/

lemma contDiff_bsWin (ℓ : ℝ) (u : ℝ³) : ContDiff ℝ (⊤ : ENat) (bsWin ℓ u) := by
  have h : bsWin ℓ u = fun x : ℝ³ => chiScale ℓ (x - ℓ • u) := rfl
  rw [h]
  exact (Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).comp (by fun_prop)

lemma contDiff_bsQ {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
  have h : bsQ ℓ u ψ = fun y : ℝ³ => ψ y - bsMean ℓ u ψ := rfl
  rw [h]
  exact hψ.sub contDiff_const

lemma hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) :
    HasCompactSupport (bsWin ℓ u) := by
  refine HasCompactSupport.intro' (K := closedBall (ℓ • u) (|ℓ| / 2))
    (isCompact_closedBall _ _) Metric.isClosed_closedBall ?_
  intro x hx
  rw [bsWin]
  refine chiScale_eq_zero_of_norm_gt_abs hℓ ?_
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  exact lt_of_not_ge hx

lemma hasCompactSupport_bsWin_mul_bsQ {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hcs : HasCompactSupport ψ) :
    HasCompactSupport (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hw : bsWin 0 u = fun _ : ℝ³ => chi 0 := bsWin_zero u
    have hq : bsQ 0 u ψ = ψ := bsQ_zero u ψ
    rw [hw, hq]
    refine HasCompactSupport.of_support_subset_isCompact hcs.isCompact ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport ψ (Function.mem_support.mpr (fun h => hx (by rw [h, mul_zero])))
  · exact (hasCompactSupport_bsWin hℓ u).mul_right

lemma hasCompactSupport_bsWin_mul_bsQ_of_ne {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    HasCompactSupport (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
  (hasCompactSupport_bsWin hℓ u).mul_right

lemma contDiff_bsWin_mul_bsQ {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
  (contDiff_bsWin ℓ u).mul (contDiff_bsQ u hψ)

/-! ## 6. The Leibniz form of the projected derivative, and the Dirichlet identity -/

/-- **The Leibniz form** of the directional derivative of the windowed mean-free state:
`∂_k(χ_u·Q_uψ)(x) = Q_uψ(x)·∂_kχ_u(x) + χ_u(x)·∂_kψ(x)`, jointly in `(x,u)`. -/
noncomputable def bsLeibniz (ℓ : ℝ) (ψ : ℝ³ → ℝ) (k : Fin 3) : ℝ³ × ℝ³ → ℝ :=
  fun p => (ψ p.1 - bsMean ℓ p.2 ψ) * fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)
    + chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)

lemma fderiv_bsWin_bsQ_eq {ℓ : ℝ} (hχ : Differentiable ℝ (chiScale ℓ)) {ψ : ℝ³ → ℝ}
    (hψ : Differentiable ℝ ψ) (p : ℝ³ × ℝ³) (k : Fin 3) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * bsQ ℓ p.2 ψ y) p.1 (kcStdBasis k)
      = bsLeibniz ℓ ψ k p := by
  have hQeq : bsQ ℓ p.2 ψ = fun y : ℝ³ => ψ y - bsMean ℓ p.2 ψ := rfl
  rw [hQeq, fderiv_bsWin_mul_eq p.2 k hχ ((hψ p.1).sub_const _), fderiv_sub_const]
  rfl

/-- **The Dirichlet identity** for the one-body big-box form at the coefficient `(·)²`. -/
theorem bsOneBody_eq_dirichlet_of_ne {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    bsOneBody ℓ (fun r => r ^ 2) u ψ
      = ∫ x : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2 := by
  have hsm : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
    contDiff_bsWin_mul_bsQ u hψ
  have hcsc : HasCompactSupport (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
    hasCompactSupport_bsWin_mul_bsQ_of_ne hℓ u ψ
  have hint : ∀ k : Fin 3, Integrable (fun x : ℝ³ =>
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2) := by
    intro k
    have hfd : HasCompactSupport (fun x : ℝ³ =>
        fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) :=
      hcsc.fderiv_apply ℝ (kcStdBasis k)
    have hcpt : HasCompactSupport (fun x : ℝ³ =>
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2) := by
      refine HasCompactSupport.of_support_subset_isCompact hfd.isCompact ?_
      intro x hx
      exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hx (by simp [h0]))
    have hcont : Continuous (fun x : ℝ³ =>
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2) :=
      ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
    exact hcont.integrable_of_hasCompactSupport hcpt
  have hkey := kinFT_energy_sum (u := fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) hsm hcsc
  have hswap : (∑ k : Fin 3, ∫ x : ℝ³,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2)
      = ∫ x : ℝ³, ∑ k : Fin 3,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2 :=
    (integral_finsetSum Finset.univ fun k _ => hint k).symm
  have hcongr : bsOneBody ℓ (fun r => r ^ 2) u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
          ‖kinFT (fun z : ℝ³ => ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2 := by
    rw [bsOneBody]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have hf_eq : (fun z : ℝ³ => ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ))
        = fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ) := by
      funext z
      push_cast
      ring
    rw [← hf_eq]
  rw [hcongr, hkey, hswap]

/-! ## 7. Integrability of the `p`-weight at the uncut coefficient -/

theorem integrable_bsKinWeight_zero {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun p : ℝ³ => fsKinCoeff 0 ‖p‖ *
        ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2) := by
  have hsm : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
    contDiff_bsWin_mul_bsQ u hψ
  have hcsu : HasCompactSupport (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) :=
    hasCompactSupport_bsWin_mul_bsQ u hcs
  have hkey := Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
    (u := fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) hsm hcsu
  refine hkey.congr (Eventually.of_forall fun p => ?_)
  show ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2
      = fsKinCoeff 0 ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2
  rw [fsKinCoeff_zero_of_nonneg (norm_nonneg p)]
  have hf_eq : (fun z : ℝ³ => ((bsWin ℓ u z * bsQ ℓ u ψ z : ℝ) : ℂ))
      = fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ) := by
    funext z
    push_cast
    ring
  rw [hf_eq]

/-! ## 8. The joint integrand of the projected derivative is `L¹` -/

lemma norm_le_norm_sub_add (a b : ℝ³) : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  have h := norm_add_le (a - b) b
  rwa [sub_add_cancel] at h

theorem integrable_uncurry_bsQ_deriv_sq {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    Integrable (fun p : ℝ³ × ℝ³ =>
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * bsQ ℓ p.2 ψ y) p.1 (kcStdBasis k)) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  classical
  have hχdiff : Differentiable ℝ (chiScale ℓ) :=
    (Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).differentiable (by norm_num)
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hpt : ∀ p : ℝ³ × ℝ³,
      fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * bsQ ℓ p.2 ψ y) p.1 (kcStdBasis k)
        = bsLeibniz ℓ ψ k p := fun p => fderiv_bsWin_bsQ_eq hχdiff hψdiff p k
  obtain ⟨Rψ, hRψ0, hψzero⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  obtain ⟨Mψ, hMψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨Mm, hMm⟩ := exists_abs_bsMean_le hℓ hψ.continuous hcs
  obtain ⟨Rm, hRm⟩ := exists_bsMean_eq_zero_of_far hℓ hψ hcs
  set Rψ' : ℝ := Rψ + 1 with hRψ'def
  have hψzero' : ∀ x : ℝ³, Rψ' ≤ ‖x‖ → ψ x = 0 := by
    intro x hx
    refine hψzero x ?_
    rw [hRψ'def] at hx
    linarith
  -- constants bounding the Leibniz form
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0)
  have hMm0 : 0 ≤ Mm := le_trans (abs_nonneg _) (hMm 0)
  have hdψcont : Continuous (fun x : ℝ³ => fderiv ℝ ψ x (kcStdBasis k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨Mdψ, hMdψ⟩ := (hcs.fderiv_apply ℝ (kcStdBasis k)).exists_bound_of_continuous hdψcont
  have hdχcont : Continuous (fun y : ℝ³ => fderiv ℝ (chiScale ℓ) y (kcStdBasis k)) :=
    ((Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).continuous_fderiv (by simp)).clm_apply
      continuous_const
  obtain ⟨Mdχ, hMdχ⟩ := ((chiScale_hasCompactSupport hℓ).fderiv_apply ℝ (kcStdBasis k))
    |>.exists_bound_of_continuous hdχcont
  have hχsup : ∀ y : ℝ³, ‖chiScale ℓ y‖ ≤ chiSup := fun y => by
    rw [Real.norm_eq_abs]
    exact abs_chiScale_le_chiSup ℓ y
  have hKbdd : ∀ p : ℝ³ × ℝ³, ‖bsLeibniz ℓ ψ k p‖ ≤ (Mψ + Mm) * Mdχ + chiSup * Mdψ := by
    intro p
    have h1 : ‖ψ p.1 - bsMean ℓ p.2 ψ‖ ≤ Mψ + Mm := by
      have hab := norm_sub_le (ψ p.1) (bsMean ℓ p.2 ψ)
      have hb : ‖bsMean ℓ p.2 ψ‖ ≤ Mm := by
        rw [Real.norm_eq_abs]
        exact hMm p.2
      linarith [hMψ p.1, hab, hb]
    have h2 : ‖fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)‖ ≤ Mdχ := hMdχ _
    have h3 : ‖chiScale ℓ (p.1 - ℓ • p.2)‖ ≤ chiSup := hχsup _
    have h4 : ‖fderiv ℝ ψ p.1 (kcStdBasis k)‖ ≤ Mdψ := hMdψ _
    have hAa : ‖(ψ p.1 - bsMean ℓ p.2 ψ) *
          fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)‖ ≤ (Mψ + Mm) * Mdχ := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    have hBb : ‖chiScale ℓ (p.1 - ℓ • p.2) * fderiv ℝ ψ p.1 (kcStdBasis k)‖
        ≤ chiSup * Mdψ := by
      rw [norm_mul]
      exact mul_le_mul h3 h4 (norm_nonneg _) chiSup_pos.le
    rw [bsLeibniz]
    exact le_trans (norm_add_le _ _) (add_le_add hAa hBb)
  -- the bounded set carrying the support
  set ρ : ℝ := |ℓ| / 2 with hρdef
  have hℓpos : 0 < |ℓ| := abs_pos.mpr hℓ
  set R₁ : ℝ := max Rψ' (ρ + |ℓ| * Rm) with hR₁def
  set R₂ : ℝ := max ((Rψ' + ρ) / |ℓ|) Rm with hR₂def
  set S : Set (ℝ³ × ℝ³) := closedBall (0 : ℝ³) R₁ ×ˢ closedBall (0 : ℝ³) R₂ with hSdef
  have hvan : ∀ p : ℝ³ × ℝ³, p ∉ S → bsLeibniz ℓ ψ k p = 0 := by
    intro p hp
    simp only [bsLeibniz]
    by_contra hnz
    apply hp
    have hwin : ‖p.1 - ℓ • p.2‖ ≤ ρ := by
      by_contra hcon
      have hcon' : ρ < ‖p.1 - ℓ • p.2‖ := lt_of_not_ge hcon
      exact hnz (by rw [chiScale_eq_zero_of_norm_gt_abs hℓ hcon',
        fderiv_chiScale_eq_zero_of_norm_gt_abs hℓ hcon']; ring)
    have hcase : ψ p.1 ≠ 0 ∨ bsMean ℓ p.2 ψ ≠ 0 ∨ fderiv ℝ ψ p.1 (kcStdBasis k) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnz (by rw [hcon.1, hcon.2.1, hcon.2.2]; ring)
    rw [hSdef, Set.mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right,
      dist_zero_right]
    rcases hcase with h1 | h2 | h3
    · have hlt : ‖p.1‖ < Rψ' := lt_of_not_ge fun hge => h1 (hψzero' p.1 hge)
      refine ⟨le_trans (le_of_lt hlt) (le_max_left _ _), le_max_of_le_left ?_⟩
      rw [le_div_iff₀ hℓpos]
      have h2' : ‖ℓ • p.2‖ ≤ Rψ' + ρ := by
        have h := norm_le_norm_sub_add (ℓ • p.2) p.1
        rw [norm_sub_rev] at h
        linarith
      calc ‖p.2‖ * |ℓ| = |ℓ| * ‖p.2‖ := by ring
        _ = ‖ℓ • p.2‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ Rψ' + ρ := h2'
    · have hlt : ‖p.2‖ < Rm := lt_of_not_ge fun hge => h2 (hRm p.2 hge)
      refine ⟨?_, le_trans (le_of_lt hlt) (le_max_right _ _)⟩
      have h3' : ‖p.1‖ ≤ ρ + |ℓ| * Rm := by
        have h := norm_le_norm_sub_add p.1 (ℓ • p.2)
        have h4 : ‖ℓ • p.2‖ ≤ |ℓ| * Rm := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (le_of_lt hlt) (abs_nonneg ℓ)
        linarith
      exact le_trans h3' (le_max_right _ _)
    · have hle : ‖p.1‖ ≤ Rψ' := by
        by_contra hcon
        have h0 : fderiv ℝ ψ p.1 = 0 := fderiv_eq_zero_of_far hψzero' (lt_of_not_ge hcon)
        exact h3 (by rw [h0]; simp)
      refine ⟨le_trans hle (le_max_left _ _), le_max_of_le_left ?_⟩
      rw [le_div_iff₀ hℓpos]
      have h5 : ‖ℓ • p.2‖ ≤ Rψ' + ρ := by
        have h := norm_le_norm_sub_add (ℓ • p.2) p.1
        rw [norm_sub_rev] at h
        linarith
      calc ‖p.2‖ * |ℓ| = |ℓ| * ‖p.2‖ := by ring
        _ = ‖ℓ • p.2‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ Rψ' + ρ := h5
  -- continuity of the Leibniz form
  have hcontφ : Continuous (fun p : ℝ³ × ℝ³ => ψ p.1 - bsMean ℓ p.2 ψ) :=
    (hψ.continuous.comp continuous_fst).sub
      ((continuous_bsMean_of_ne hℓ hψ hcs).comp continuous_snd)
  have hcontDχ : Continuous (fun p : ℝ³ × ℝ³ =>
      fderiv ℝ (chiScale ℓ) (p.1 - ℓ • p.2) (kcStdBasis k)) :=
    hdχcont.comp (continuous_fst.sub (continuous_snd.const_smul ℓ))
  have hcontχ : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ (p.1 - ℓ • p.2)) :=
    ((Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).continuous).comp
      (continuous_fst.sub (continuous_snd.const_smul ℓ))
  have hcontDψ : Continuous (fun p : ℝ³ × ℝ³ => fderiv ℝ ψ p.1 (kcStdBasis k)) :=
    hdψcont.comp continuous_fst
  have hcontL : Continuous (bsLeibniz ℓ ψ k) :=
    (hcontφ.mul hcontDχ).add (hcontχ.mul hcontDψ)
  have hmeasL : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => (bsLeibniz ℓ ψ k p) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hcontL.pow 2).aestronglyMeasurable
  have hSfin : ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) S ≠ ⊤ := by
    rw [hSdef, Measure.prod_prod]
    exact ENNReal.mul_ne_top (isCompact_closedBall (0 : ℝ³) R₁).measure_lt_top.ne
      (isCompact_closedBall (0 : ℝ³) R₂).measure_lt_top.ne
  have hIntOn : IntegrableOn (fun p : ℝ³ × ℝ³ => (bsLeibniz ℓ ψ k p) ^ 2) S
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    Measure.integrableOn_of_bounded hSfin hmeasL (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg (bsLeibniz ℓ ψ k p))]
      have h := pow_le_pow_left₀ (norm_nonneg (bsLeibniz ℓ ψ k p)) (hKbdd p) 2
      simpa only [Real.norm_eq_abs, sq_abs] using h)
  have hIntL : Integrable (fun p : ℝ³ × ℝ³ => (bsLeibniz ℓ ψ k p) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hIntOn.integrable_of_forall_notMem_eq_zero (fun p hp => by rw [hvan p hp]; ring)
  refine hIntL.congr (Eventually.of_forall fun p => ?_)
  show (bsLeibniz ℓ ψ k p) ^ 2
      = (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * bsQ ℓ p.2 ψ y) p.1 (kcStdBasis k)) ^ 2
  rw [hpt p]

/-! ## 9. Integrability of the `u`-integrand at the uncut coefficient -/

lemma bsOneBody_fsKinCoeff_zero {ℓ : ℝ} (u : ℝ³) (ψ : ℝ³ → ℝ) :
    bsOneBody ℓ (fsKinCoeff 0) u ψ = bsOneBody ℓ (fun r => r ^ 2) u ψ := by
  rw [bsOneBody, bsOneBody]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show fsKinCoeff 0 ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2
      = (fun r => r ^ 2) ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2
  rw [fsKinCoeff_zero_of_nonneg (norm_nonneg p)]

theorem integrable_bsOneBody_fsKinCoeff_zero {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff 0) u ψ) := by
  have hjoint : Integrable (fun p : ℝ³ × ℝ³ => ∑ k : Fin 3,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ p.2 y * bsQ ℓ p.2 ψ y) p.1 (kcStdBasis k)) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    integrable_finsetSum Finset.univ fun k _ => integrable_uncurry_bsQ_deriv_sq hℓ hψ hcs k
  have hmarg : Integrable (fun u : ℝ³ => ∫ x : ℝ³, ∑ k : Fin 3,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2) :=
    Integrable.integral_prod_right hjoint
  refine hmarg.congr (Eventually.of_forall fun u => ?_)
  show (∫ x : ℝ³, ∑ k : Fin 3,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) x (kcStdBasis k)) ^ 2)
    = bsOneBody ℓ (fsKinCoeff 0) u ψ
  rw [bsOneBody_fsKinCoeff_zero, bsOneBody_eq_dirichlet_of_ne hℓ u ψ hψ]

/-! ## 10. Monotonicity of the family form in the cutoff, and the main theorem -/

theorem bsFamilyForm_fsKinCoeff_le {ℓ : ℝ} (hℓ : ℓ ≠ 0) {c : ℝ} (hc : 0 ≤ c) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    bsFamilyForm ℓ (fsKinCoeff c) ψ ≤ bsFamilyForm ℓ (fsKinCoeff 0) ψ := by
  have hInt0 : Integrable (fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff 0) u ψ) :=
    integrable_bsOneBody_fsKinCoeff_zero hℓ hψ hcs
  rw [bsFamilyForm, bsFamilyForm]
  refine integral_mono_of_nonneg (f := fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff c) u ψ)
    (g := fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff 0) u ψ) ?_ hInt0 ?_
  · filter_upwards with u
    exact bsOneBody_nonneg (fun r => fsKinCoeff_nonneg c r) u ψ
  · filter_upwards with u
    exact bsOneBody_mono_coeff (fun r => fsKinCoeff_nonneg c r)
      (fun r => fsKinCoeff_zero_le hc r) (integrable_bsKinWeight_zero u hψ hcs)

theorem FamilyBound_of_le {ℓ c : ℝ} (hc : 0 ≤ c)
    (h : Work.BSKinetic.FamilyBound ℓ 0) : Work.BSKinetic.FamilyBound ℓ c := by
  intro ψ hψ hcs
  by_cases hℓ : ℓ = 0
  · subst hℓ
    rw [bsFamilyForm_zero_eq_zero]
    exact dSpace_nonneg ψ
  · exact le_trans (bsFamilyForm_fsKinCoeff_le hℓ hc hψ hcs) (h ψ hψ hcs)

end Work.BSKinetic
