import Submission.Gauss
import Submission.GeodesicSpeed
import Submission.ChartBounds
import Submission.EDist
import Submission.GeodesicSpeed

/-!
# Local minimality of geodesics

This file proves that for small `v` the Riemannian distance from `x₀` to `expMap cov x₀ v` is
exactly `√(chartGram x₀ x₀ v v)`, i.e. the geodesic ray `s ↦ expMap cov x₀ (s • v)` is minimising
for `s ∈ [0,1]`.

## Method

* Gauss's lemma (`Submission.Gauss.gauss_lemma_fderiv`) says that at a point `σ` of the ball where
  `exp` is a local diffeomorphism the differential of `exp` preserves the scalar product with the
  radial direction `σ`; combined with Cauchy–Schwarz in the fibre this gives the *pointwise*
  inequality `g_{x₀}(σ,σ')² ≤ g_{x₀}(σ,σ) ‖(d exp)_σ σ'‖²`, i.e. `|d r| ≤ 1` for the radial
  function `r = √(g_{x₀}(σ,σ))`.
* Integrating along a `C¹` path gives `pathELength γ ≥ |r(γ 1) - r(γ 0)|`.
* If the path leaves the ball, it has already accumulated at least the radius of the ball, which is
  larger than `√(chartGram x₀ x₀ v v)` for the small `v` under consideration.

## Main results

* `gauss_ineq`: the pointwise Gauss inequality;
* `hasDerivAt_chartGram_self_comp`, `hasDerivAt_sqrt_chartGram_self_comp`: derivatives of the base
  point metric along a curve;
* `pathELength_ge_radial`: the length lower bound for a path staying in the normal ball;
* `pathELength_ge_radial'`: the same without the staying hypothesis (handling the exit of the ball);
* `riemannianEDist_expMap_eq`: **local minimality of geodesics**;
* `riemannianEDist_expMap_eq_of_mem`: the same for `expMap cov x₀ v` with `v` in the ball.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric MeasureTheory
open Submission.Geodesic
open Submission.Length
open Submission.ChartConnection
open Submission.Variation
open Submission.ChartBounds
open Submission.Gauss
open Submission.GeodesicSpeed

namespace Submission.Minimal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable [I.Boundaryless]

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The pointwise Gauss inequality.**  At a point `σ` of the ball where Gauss's lemma holds, the
differential of the exponential map satisfies
`g_{x₀}(σ,σ')² ≤ g_{x₀}(σ,σ) ‖(d exp_{x₀})_σ σ'‖²`.
This is the infinitesimal form of the statement that the radial function in normal coordinates has
gradient of norm at most one. -/
lemma chartGram_self_nonneg (x₀ p : M) (a : E) :
    0 ≤ chartGram (I := I) x₀ p a a := by
  rw [chartGram_apply]
  exact inner_self_nonneg (𝕜 := ℝ) (x := frameVector (I := I) x₀ p a)

theorem gauss_ineq {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (x₀ : M) {ρ : ℝ}
    (hgauss : ∀ u : E, ‖u‖ < ρ → ∀ X : E,
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) u u)
        (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) u X)
      = chartGram (I := I) x₀ x₀ u X)
    {σ : E} (hσ : ‖σ‖ < ρ) (σ' : E) :
    (chartGram (I := I) x₀ x₀ σ σ') ^ 2 ≤
      chartGram (I := I) x₀ x₀ σ σ *
        ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ'‖ ^ 2 := by
  have h1 : inner ℝ ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ)
      ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ)
      = chartGram (I := I) x₀ x₀ σ σ := hgauss σ hσ σ
  have h2 : inner ℝ ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ)
      ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ')
      = chartGram (I := I) x₀ x₀ σ σ' := hgauss σ hσ σ'
  have hcs := real_inner_mul_inner_self_le
    ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ)
    ((mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) σ) σ')
  rw [h1, h2, real_inner_self_eq_norm_sq, pow_two] at hcs
  linarith [hcs]
lemma hasDerivAt_chartGram_self_comp (x₀ : M) {σ σ' : ℝ → E} {t : ℝ}
    (h : HasDerivAt σ (σ' t) t) :
    HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ x₀ (σ s) (σ s))
      (2 * chartGram (I := I) x₀ x₀ (σ t) (σ' t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => frameVector (I := I) x₀ x₀ (σ s))
      (frameVector (I := I) x₀ x₀ (σ' t)) t := by
    have hl : HasFDerivAt (fun v : E => frameVector (I := I) x₀ x₀ v)
        (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x₀) (σ t) :=
      ContinuousLinearMap.hasFDerivAt (x := σ t)
        (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x₀)
    have hb := HasFDerivAt.comp_hasDerivAt (l := fun v : E => frameVector (I := I) x₀ x₀ v)
      (f := σ) (x := t) (f' := σ' t) hl h
    simpa [Function.comp_def, frameVector] using hb
  have hinner := HasDerivAt.inner ℝ hlin hlin
  have hval : Inner.inner ℝ (frameVector (I := I) x₀ x₀ (σ t)) (frameVector (I := I) x₀ x₀ (σ' t))
      + Inner.inner ℝ (frameVector (I := I) x₀ x₀ (σ' t)) (frameVector (I := I) x₀ x₀ (σ t))
      = 2 * chartGram (I := I) x₀ x₀ (σ t) (σ' t) := by
    rw [chartGram_apply]
    rw [real_inner_comm (frameVector (I := I) x₀ x₀ (σ' t))
      (frameVector (I := I) x₀ x₀ (σ t))]
    ring
  rw [hval] at hinner
  exact hinner

lemma hasDerivAt_sqrt_chartGram_add_sq (x₀ : M) {σ σ' : ℝ → E} {t δ : ℝ} (hδ : 0 < δ)
    (h : HasDerivAt σ (σ' t) t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (chartGram (I := I) x₀ x₀ (σ s) (σ s) + δ ^ 2))
      (chartGram (I := I) x₀ x₀ (σ t) (σ' t)
        / Real.sqrt (chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2)) t := by
  have hA := hasDerivAt_chartGram_self_comp (I := I) x₀ h
  have hA' : HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ x₀ (σ s) (σ s) + δ ^ 2)
      (2 * chartGram (I := I) x₀ x₀ (σ t) (σ' t)) t := by
    simpa using hA.add_const (δ ^ 2)
  have hnn := chartGram_self_nonneg (I := I) x₀ x₀ (σ t)
  have hpos : chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2 ≠ 0 := by
    have h2 : (0:ℝ) < δ^2 := by positivity
    linarith
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt x)
      (1 / (2 * Real.sqrt (chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2)))
      (chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2) := Real.hasDerivAt_sqrt hpos
  have hcomp := HasDerivAt.comp t hs hA'
  have hv : (1 / (2 * Real.sqrt (chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2)))
      * (2 * chartGram (I := I) x₀ x₀ (σ t) (σ' t))
      = chartGram (I := I) x₀ x₀ (σ t) (σ' t)
        / Real.sqrt (chartGram (I := I) x₀ x₀ (σ t) (σ t) + δ ^ 2) := by
    rw [div_eq_mul_inv]; ring
  rw [hv] at hcomp
  simpa [Function.comp_def] using hcomp

lemma enorm_eq_ofReal_norm {F : Type*} [SeminormedAddCommGroup F] (x : F) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
  simp

lemma enorm_eq_ofReal_of_nonneg {x : ℝ} (h : 0 ≤ x) : ‖x‖ₑ = ENNReal.ofReal x := by
  rw [enorm_eq_ofReal_norm, Real.norm_of_nonneg h]

lemma enorm_eq_ofReal_abs (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal |x| := by
  rw [enorm_eq_ofReal_norm, Real.norm_eq_abs]

lemma chartGram_add_snd (x₀ p : M) (a b c : E) :
    chartGram (I := I) x₀ p a (b + c) = chartGram (I := I) x₀ p a b + chartGram (I := I) x₀ p a c := by
  rw [chartGram_apply, chartGram_apply, chartGram_apply, frameVector_add, inner_add_right]



/-- **The chain rule for the exponential map along a chart curve.**  If `γ` agrees with
`expMap cov x₀ ∘ σ` near `t`, then the velocity of `γ` is the image of the velocity of `σ` under
the differential of `expMap`. -/
lemma mfderiv_eq_exp_comp (x₀ : M) {σ : ℝ → E} {γ : ℝ → M} {t : ℝ}
    (hσ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) σ t)
    (hsm : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t))
    (hev : γ =ᶠ[𝓝 t] (fun r => expMap cov x₀ (σ r))) :
    mfderiv 𝓘(ℝ) I γ t
      = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t)).comp
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) := by
  rw [hev.mfderiv_eq]
  exact mfderiv_comp t hsm hσ

/-- **The velocity identity.**  Under the hypotheses of `mfderiv_eq_exp_comp`, applied to the
derivative `σ'` of `σ`, the velocity of `γ` is `(d exp)_{σ t} σ'(t)`. -/
lemma curveVelocity_eq_exp_deriv (x₀ : M) {σ σ' : ℝ → E} {γ : ℝ → M} {t : ℝ}
    (hσ : HasDerivAt σ (σ' t) t)
    (hsm : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t))
    (hev : γ =ᶠ[𝓝 t] (fun r => expMap cov x₀ (σ r))) :
    curveVelocity (I := I) γ t
      = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t)) (σ' t) := by
  have h1 : mfderiv 𝓘(ℝ) I γ t
      = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t)).comp
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) :=
    mfderiv_eq_exp_comp (cov := cov) x₀
      (mdifferentiableAt_iff_differentiableAt.mpr hσ.differentiableAt) hsm hev
  change (mfderiv 𝓘(ℝ) I γ t) (1 : ℝ) = _
  rw [h1]
  change (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ t))
      ((mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) (1 : ℝ)) = _
  rw [show (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) σ t) (1 : ℝ) = deriv σ t from by
    rw [mfderiv_eq_fderiv]; rfl, hσ.deriv]

/-- **The length lower bound for a path staying in the normal ball.** -/
theorem pathELength_ge_radial_of_stays (x₀ : M)
    {σ σ' : ℝ → E} {R ρg : ℝ}
    (hRg : R ≤ ρg)
    (hgauss : ∀ u : E, ‖u‖ < ρg → ∀ X : E,
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) u u)
        (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) u X)
      = chartGram (I := I) x₀ x₀ u X)
    {γ : ℝ → M} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hσd : ∀ s ∈ Icc (0:ℝ) t, HasDerivAt σ (σ' s) s)
    (hσC1 : ContDiffOn ℝ 1 σ (Icc (0:ℝ) t))
    (hσnorm : ∀ s ∈ Icc (0:ℝ) t, ‖σ s‖ < R)
    (hσ0 : σ 0 = 0)
    (hvelnorm : ∀ s ∈ Ioo (0:ℝ) t,
      ‖curveVelocity (I := I) γ s‖ₑ
        = ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ) :
    ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t) (σ t)))
      ≤ Manifold.pathELength I γ 0 t := by
  by_cases ht0 : t ≤ 0
  · have ht_eq : t = 0 := le_antisymm ht0 ht.1
    subst ht_eq
    rw [Manifold.pathELength_self, hσ0, chartGram_zero, Real.sqrt_zero, ENNReal.ofReal_zero]
  have h0t : (0:ℝ) ≤ t := lt_of_not_ge ht0 |>.le
  set A : ℝ → ℝ := fun s => chartGram (I := I) x₀ x₀ (σ s) (σ s) with hAdef
  set B : ℝ → ℝ := fun s => chartGram (I := I) x₀ x₀ (σ s) (σ' s) with hBdef
  -- `A` is `C¹`
  have hAcont : ContDiffOn ℝ 1 A (Icc (0:ℝ) t) := by
    have hLs : ContDiffOn ℝ 1 (fun s : ℝ => frameVector (I := I) x₀ x₀ (σ s)) (Icc (0:ℝ) t) := by
      have hL : ContDiff ℝ 1 (fun v : E => frameVector (I := I) x₀ x₀ v) := by
        have h := ContinuousLinearMap.contDiff (n := (1 : ℕ∞ω))
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀)
        simpa only [frameVector] using h
      exact (hL.contDiffOn).comp hσC1 (mapsTo_univ _ _)
    have hinner := ContDiffOn.inner ℝ hLs hLs
    simpa only [hAdef, chartGram_apply] using hinner
  -- the key inequality for every `δ > 0`
  have key : ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (Real.sqrt (A t + δ ^ 2) - δ)
        ≤ Manifold.pathELength I γ 0 t := by
    intro δ hδ
    set Rδ : ℝ → ℝ := fun s => Real.sqrt (A s + δ ^ 2) with hRδdef
    have hRδC1 : ContDiffOn ℝ 1 Rδ (Icc (0:ℝ) t) := by
      have h1 : ContDiffOn ℝ 1 (fun s : ℝ => A s + δ ^ 2) (Icc (0:ℝ) t) :=
        hAcont.add contDiffOn_const
      have h2 := h1.sqrt (fun x hx => by
        have h3 := chartGram_self_nonneg (I := I) x₀ x₀ (σ x)
        have h4 : (0:ℝ) < δ ^ 2 := by positivity
        simp only [hAdef] at h3 ⊢
        linarith)
      simpa only [hRδdef] using h2
    have hftc := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hRδC1 h0t
    -- pointwise bound
    have hpt : ∀ s ∈ Ioo (0:ℝ) t,
        ‖deriv Rδ s‖ₑ
          ≤ ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
      intro s hs
      have hsIcc : s ∈ Icc (0:ℝ) t := Ioo_subset_Icc_self hs
      have hAd : HasDerivAt A (2 * B s) s := by
        have h := hasDerivAt_chartGram_self_comp (I := I) x₀ (σ := σ) (σ' := σ')
          (hσd s hsIcc)
        simpa only [hAdef, hBdef] using h
      have hRδd : HasDerivAt Rδ (B s / Real.sqrt (A s + δ ^ 2)) s := by
        have h := hasDerivAt_sqrt_chartGram_add_sq (I := I) x₀ (σ := σ) (σ' := σ') hδ (hσd s hsIcc)
        simpa only [hAdef, hBdef, hRδdef] using h
      have hdv : ‖deriv Rδ s‖ₑ = ‖B s / Real.sqrt (A s + δ ^ 2)‖ₑ := by
        rw [hRδd.deriv]
      -- Gauss bound
      have hgi := gauss_ineq (cov := cov) x₀ hgauss
        (σ := σ s) (lt_of_lt_of_le (hσnorm s hsIcc) hRg) (σ' := σ' s)
      have hAs : A s = chartGram (I := I) x₀ x₀ (σ s) (σ s) := by simp only [hAdef]
      have hBs : B s = chartGram (I := I) x₀ x₀ (σ s) (σ' s) := by simp only [hBdef]
      rw [← hAs, ← hBs] at hgi
      have hAnn : 0 ≤ A s := by simp only [hAdef]; exact chartGram_self_nonneg (I := I) x₀ x₀ (σ s)
      have hd2 : 0 ≤ δ ^ 2 := sq_nonneg δ
      set V : ℝ := ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ with hVdef
      have hsq : (B s) ^ 2 ≤ (A s + δ ^ 2) * V ^ 2 := by
        have hN : 0 ≤ V ^ 2 := sq_nonneg _
        have h1 : A s * V ^ 2 ≤ (A s + δ ^ 2) * V ^ 2 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd2) hN
        exact hgi.trans h1
      have hden : 0 < A s + δ ^ 2 := by
        have h2 : (0:ℝ) < δ ^ 2 := sq_pos_of_pos hδ
        linarith
      have hsqrtpos : 0 < Real.sqrt (A s + δ ^ 2) := Real.sqrt_pos.mpr hden
      have hbound : |B s / Real.sqrt (A s + δ ^ 2)| ≤ V := by
        have h1 : |B s / Real.sqrt (A s + δ ^ 2)|
            = |B s| / Real.sqrt (A s + δ ^ 2) := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
        rw [h1, div_le_iff₀ hsqrtpos]
        have h2 : (|B s| : ℝ) ^ 2 ≤ (V * Real.sqrt (A s + δ ^ 2)) ^ 2 := by
          rw [sq_abs, mul_pow, Real.sq_sqrt hden.le]
          nlinarith [hsq]
        have h3 := sq_le_sq.mp h2
        rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))] at h3
        rw [abs_abs, ← hVdef] at h3
        exact h3
      have hnn : (0:ℝ) ≤ V := by rw [hVdef]; exact norm_nonneg _
      calc ‖deriv Rδ s‖ₑ = ‖B s / Real.sqrt (A s + δ ^ 2)‖ₑ := hdv
        _ = ENNReal.ofReal |B s / Real.sqrt (A s + δ ^ 2)| := enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal V := ENNReal.ofReal_le_ofReal hbound
        _ = ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
            rw [hVdef]
            exact (enorm_eq_ofReal_norm _).symm
    -- integral comparison
    have hmono : ∫⁻ s in Icc (0:ℝ) t, ‖deriv Rδ s‖ₑ
        ≤ ∫⁻ s in Icc (0:ℝ) t,
            ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
      rw [← restrict_Ioo_eq_restrict_Icc (μ := volume) (a := (0:ℝ)) (b := t)]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact hpt s hs
    have hconv : ∫⁻ s in Icc (0:ℝ) t,
          ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ
        = ∫⁻ s in Icc (0:ℝ) t, ‖curveVelocity (I := I) γ s‖ₑ := by
      rw [← restrict_Ioo_eq_restrict_Icc (μ := volume) (a := (0:ℝ)) (b := t)]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact (hvelnorm s hs).symm
    have hpath : Manifold.pathELength I γ 0 t
        = ∫⁻ s in Icc (0:ℝ) t, ‖curveVelocity (I := I) γ s‖ₑ :=
      Manifold.pathELength_eq_lintegral_mfderiv_Icc
    have hRδ0 : Rδ 0 = δ := by
      have h0 : A 0 = 0 := by simp only [hAdef, hσ0, chartGram_zero_fst]
      have h1 : Rδ 0 = Real.sqrt (A 0 + δ ^ 2) := by simp only [hRδdef]
      rw [h1, h0, zero_add, Real.sqrt_sq hδ.le]
    have h0A : A 0 = 0 := by simp only [hAdef, hσ0, chartGram_zero_fst]
    have hsub : Rδ t - Rδ 0 = Real.sqrt (A t + δ ^ 2) - δ := by
      simp only [hRδdef, h0A, zero_add, Real.sqrt_sq hδ.le]
    have hnonneg : 0 ≤ Rδ t - Rδ 0 := by
      rw [hsub]
      have h1 : Real.sqrt ((0:ℝ) + δ ^ 2) ≤ Real.sqrt (A t + δ ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h2 : 0 ≤ A t := by simp only [hAdef]; exact chartGram_self_nonneg (I := I) x₀ x₀ (σ t)
        linarith
      rw [zero_add, Real.sqrt_sq hδ.le] at h1
      linarith
    have hfinal : ENNReal.ofReal (Real.sqrt (A t + δ ^ 2) - δ)
        ≤ ∫⁻ s in Icc (0:ℝ) t, ‖deriv Rδ s‖ₑ := by
      rw [← hsub]
      calc ENNReal.ofReal (Rδ t - Rδ 0) = ‖Rδ t - Rδ 0‖ₑ :=
            (enorm_eq_ofReal_of_nonneg hnonneg).symm
        _ ≤ _ := hftc
    calc ENNReal.ofReal (Real.sqrt (A t + δ ^ 2) - δ)
        ≤ ∫⁻ s in Icc (0:ℝ) t, ‖deriv Rδ s‖ₑ := hfinal
      _ ≤ ∫⁻ s in Icc (0:ℝ) t,
            ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := hmono
      _ = ∫⁻ s in Icc (0:ℝ) t, ‖curveVelocity (I := I) γ s‖ₑ := hconv
      _ = Manifold.pathELength I γ 0 t := hpath.symm
  -- pass to the limit `δ → 0`
  have hAt : A t = chartGram (I := I) x₀ x₀ (σ t) (σ t) := by simp only [hAdef]
  have hAnn : 0 ≤ A t := by simp only [hAdef]; exact chartGram_self_nonneg (I := I) x₀ x₀ (σ t)
  rw [← hAt]
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  have hδ : (0:ℝ) < (ε:ℝ)/2 := by linarith
  have hk := key ((ε:ℝ)/2) hδ
  have hs1nn : 0 ≤ Real.sqrt (A t + ((ε:ℝ)/2)^2) - (ε:ℝ)/2 := by
    have h1 : Real.sqrt (((ε:ℝ)/2)^2) ≤ Real.sqrt (A t + ((ε:ℝ)/2)^2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hAnn, sq_nonneg ((ε:ℝ)/2)]
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (ε:ℝ)/2)] at h1
    linarith
  have hstep : Real.sqrt (A t)
      ≤ (Real.sqrt (A t + ((ε:ℝ)/2)^2) - (ε:ℝ)/2) + (ε:ℝ)/2 := by
    have h1 : Real.sqrt (A t) ≤ Real.sqrt (A t + ((ε:ℝ)/2)^2) := by
      apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg ((ε:ℝ)/2)]
    linarith
  have hε2 : ENNReal.ofReal ((ε:ℝ)/2) ≤ (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (by linarith : (ε:ℝ)/2 ≤ (ε:ℝ))
  calc ENNReal.ofReal (Real.sqrt (A t))
      ≤ ENNReal.ofReal ((Real.sqrt (A t + ((ε:ℝ)/2)^2) - (ε:ℝ)/2) + (ε:ℝ)/2) :=
        ENNReal.ofReal_le_ofReal hstep
    _ ≤ ENNReal.ofReal (Real.sqrt (A t + ((ε:ℝ)/2)^2) - (ε:ℝ)/2)
          + ENNReal.ofReal ((ε:ℝ)/2) := ENNReal.ofReal_add_le
    _ ≤ Manifold.pathELength I γ 0 t + (ε : ℝ≥0∞) := add_le_add hk hε2



/-- **Local minimality of geodesics.**  For small `v`, the Riemannian distance from `x₀` to
`expMap cov x₀ v` is exactly `√(chartGram x₀ x₀ v v)`, i.e. the geodesic ray from `x₀` in the
direction `v` is minimising. -/
theorem riemannianEDist_expMap_eq [Nontrivial E]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ →
      Manifold.riemannianEDist I x₀ (expMap cov x₀ v)
        = ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  classical
  obtain ⟨ρg, hρg, hgauss⟩ := gauss_lemma_fderiv (cov := cov) hmet htor x₀
  obtain ⟨ρs, hρs, hsm₀⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  obtain ⟨ρc, hρc, hgeo⟩ := exists_pos_hasChartGeodesic (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x₀
    (K := {x₀}) isCompact_singleton ⟨x₀, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H x₀)
  have hf := isLocalDiffeomorphAt_expMap_zero (cov := cov) x₀
  obtain ⟨ε, hε, hεball⟩ : ∃ ε > 0, Metric.ball (0 : E) ε ⊆ (Classical.choose hf).source := by
    rcases Metric.isOpen_iff.mp (Classical.choose hf).open_source 0 hf.localInverse_mem_target
      with ⟨ε, hε, hsub⟩
    exact ⟨ε, hε, hsub⟩
  -- the radii
  obtain ⟨R, hRpos, hRε, hRg, hRs, hRc⟩ : ∃ R > 0, R ≤ ε/3 ∧ R ≤ ρg ∧ R ≤ ρs ∧ R ≤ ρc := by
    refine ⟨min (min (ε/3) ρg) (min ρs ρc) / 2, by positivity, ?_, ?_, ?_, ?_⟩
    · have : min (min (ε/3) ρg) (min ρs ρc) ≤ ε/3 := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    · have : min (min (ε/3) ρg) (min ρs ρc) ≤ ρg := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · have : min (min (ε/3) ρg) (min ρs ρc) ≤ ρs := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : min (min (ε/3) ρg) (min ρs ρc) ≤ ρc := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  set φ := hf.localInverse with hφdef
  have hφopen : IsOpen φ.source := hf.localInverse_open_source
  have hφmd : CMDiff[φ.source] ∞ φ := hf.contmdiffOn_localInverse
  have hφright : ∀ y ∈ φ.source, expMap cov x₀ (φ y) = y := fun y hy =>
    hf.localInverse_right_inv hy
  have hclos : closure (Metric.ball (0 : E) (R / 2)) ⊆ (Classical.choose hf).source := by
    intro w hw
    rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)] at hw
    have hw' : ‖w‖ ≤ R / 2 := by
      have := Metric.mem_closedBall.mp hw
      rwa [dist_zero_right] at this
    have hlt : ‖w‖ < ε := by linarith
    exact hεball (by rw [Metric.mem_ball, dist_zero_right]; exact hlt)
  -- the local inverse on the small closed ball
  have hφball : ∀ w : E, ‖w‖ ≤ R / 2 →
      expMap cov x₀ w ∈ φ.source ∧ φ (expMap cov x₀ w) = w := by
    intro w hw
    have hwcl : w ∈ closure (Metric.ball (0 : E) (R / 2)) := by
      rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)]
      exact Metric.mem_closedBall.mpr (by rwa [dist_zero_right])
    have hwsrc : w ∈ (Classical.choose hf).source := hclos hwcl
    have hmaps : (Classical.choose hf) w ∈ (Classical.choose hf).target :=
      (Classical.choose hf).map_source hwsrc
    have heq : expMap cov x₀ w = (Classical.choose hf) w := (hf.choose_spec.2 hwsrc)
    refine ⟨?_, ?_⟩
    · rw [hφdef]; rw [heq]; exact hmaps
    · rw [hφdef]; exact hf.localInverse_left_inv hwsrc
  -- the small radius for the statement
  have hsqpos : 0 < Real.sqrt (lam / Lam) := Real.sqrt_pos.mpr (div_pos hlam hLam)
  refine ⟨min (R / 8) (R / 4 * Real.sqrt (lam / Lam)), by positivity, ?_⟩
  intro v hv
  have hvR : ‖v‖ < R / 8 := lt_of_lt_of_le hv (min_le_left _ _)
  have hvsqrt : ‖v‖ < R / 4 * Real.sqrt (lam / Lam) := lt_of_lt_of_le hv (min_le_right _ _)
  have hvR4 : ‖v‖ < R / 4 := by linarith
  have hvR' : ‖v‖ < R := by linarith
  have hvc : ‖v‖ ≤ ρc := le_of_lt (lt_of_lt_of_le hvR' hRc)
  set ℓ : ℝ := Real.sqrt (chartGram (I := I) x₀ x₀ v v) with hℓdef
  rcases eq_or_ne v 0 with rfl | hvne
  · rw [expMap_zero, Manifold.riemannianEDist_self, hℓdef, chartGram_zero, Real.sqrt_zero,
      ENNReal.ofReal_zero]
  refine le_antisymm ?_ ?_
  · -- upper bound: the geodesic ray
    obtain ⟨u, w, huw⟩ := hgeo v hvc
    exact riemannianEDist_expMap_le (cov := cov) hmet x₀ huw
  · -- lower bound
    by_contra hcon
    have hlt : Manifold.riemannianEDist I x₀ (expMap cov x₀ v) < ENNReal.ofReal ℓ :=
      lt_of_not_ge hcon
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen, -, -⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I) hlt zero_lt_one
    set σ : ℝ → E := fun s => φ (γ s) with hσdef
    set σ' : ℝ → E := fun s => (mfderiv I 𝓘(ℝ, E) φ (γ s)) ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ))
      with hσ'def
    set u : Set M := Set.image (fun w : E => expMap cov x₀ w)
      (closure (Metric.ball (0 : E) (R / 2))) with hudef
    set sset : Set ℝ := {t | γ t ∈ u} with hsdef
    have hσapp : ∀ s : ℝ, σ s = φ (γ s) := fun s => by simp only [hσdef]
    have hσ'app : ∀ s : ℝ, σ' s
        = (mfderiv I 𝓘(ℝ, E) φ (γ s)) ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ)) :=
      fun s => by simp only [hσ'def]
    -- `u` is closed
    have hcompact : IsCompact (closure (Metric.ball (0 : E) (R / 2))) := by
      rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)]
      exact isCompact_closedBall 0 (R / 2)
    have hcont_exp : ContinuousOn (fun w : E => expMap cov x₀ w)
        (closure (Metric.ball (0 : E) (R / 2))) := by
      intro w hw
      rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)] at hw
      have hw' : ‖w‖ ≤ R / 2 := by
        have := Metric.mem_closedBall.mp hw
        rwa [dist_zero_right] at this
      exact (hsm₀ w (lt_of_le_of_lt hw' (by linarith))).continuousAt.continuousWithinAt
    have hu_closed : IsClosed u := (hcompact.image_of_continuousOn hcont_exp).isClosed
    -- membership in `u` gives the ball description
    have hu_mem : ∀ t : ℝ, γ t ∈ u → ∃ w : E, ‖w‖ ≤ R / 2 ∧ γ t = expMap cov x₀ w := by
      intro t ht
      rw [hudef] at ht
      obtain ⟨w, hw, hwt⟩ := ht
      rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)] at hw
      refine ⟨w, ?_, hwt.symm⟩
      have := Metric.mem_closedBall.mp hw
      rwa [dist_zero_right] at this
    -- the induction
    have hbase : (0 : ℝ) ∈ sset := by
      rw [hsdef]
      change γ 0 ∈ u
      rw [hγ0, hudef]
      refine ⟨0, ?_, ?_⟩
      · rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)]
        exact Metric.mem_closedBall.mpr (by rw [dist_zero_right, norm_zero]; linarith)
      · exact expMap_zero (cov := cov) x₀
    have hstep : ∀ t₁ ∈ Ico (0 : ℝ) 1, Icc (0 : ℝ) t₁ ⊆ sset → sset ∈ 𝓝[>] t₁ := by
      intro t₁ ht₁ hsub
      have ht₁Icc : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, le_of_lt ht₁.2⟩
      -- facts on `[0,t₁]`
      have hu_t : ∀ s ∈ Icc (0:ℝ) t₁, ∃ w : E, ‖w‖ ≤ R / 2 ∧ γ s = expMap cov x₀ w :=
        fun s hs => hu_mem s (hsub hs)
      have hσsrc : ∀ s ∈ Icc (0:ℝ) t₁, γ s ∈ φ.source := by
        intro s hs
        obtain ⟨w, hw, hws⟩ := hu_t s hs
        rw [hws]
        exact (hφball w hw).1
      have hσnorm : ∀ s ∈ Icc (0:ℝ) t₁, ‖σ s‖ < R := by
        intro s hs
        obtain ⟨w, hw, hws⟩ := hu_t s hs
        have h1 : σ s = w := by rw [hσapp s, hws]; exact (hφball w hw).2
        rw [h1]; linarith
      have hσinv : ∀ s ∈ Icc (0:ℝ) t₁, γ s = expMap cov x₀ (σ s) := by
        intro s hs
        rw [hσapp s]
        exact (hφright (γ s) (hσsrc s hs)).symm
      have hmapsTo : MapsTo γ (Icc (0:ℝ) t₁) φ.source := fun s hs => hσsrc s hs
      have hσC1 : ContDiffOn ℝ 1 σ (Icc (0:ℝ) t₁) := by
        have h1 : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0:ℝ) t₁) := hγC1.contMDiffOn
        have h2 : ContMDiffOn I 𝓘(ℝ, E) 1 φ φ.source := hφmd.of_le (WithTop.coe_le_coe.mpr le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
        have h3 := h2.comp h1 hmapsTo
        exact contMDiffOn_iff_contDiffOn.mp h3
      have hσd : ∀ s ∈ Icc (0:ℝ) t₁, HasDerivAt σ (σ' s) s := by
        intro s hs
        have hγmd : MDifferentiableAt 𝓘(ℝ) I γ s := hγC1.mdifferentiableAt one_ne_zero
        have hφmdAt : MDifferentiableAt I 𝓘(ℝ, E) φ (γ s) :=
          (hφmd.mdifferentiableOn (by norm_num) (γ s) (hσsrc s hs)).mdifferentiableAt
            (hφopen.mem_nhds (hσsrc s hs))
        have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (φ ∘ γ) s := hφmdAt.comp s hγmd
        have hdiff : DifferentiableAt ℝ σ s := mdifferentiableAt_iff_differentiableAt.mp hcomp
        have hderiv : deriv σ s
            = (mfderiv I 𝓘(ℝ, E) φ (γ s)) ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ)) :=
          (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (g := φ) (γ := γ) hφmdAt hγmd).symm
        rw [hσ'def]
        exact hdiff.hasDerivAt.congr_deriv hderiv
      have hvelnorm : ∀ s ∈ Ioo (0:ℝ) t₁,
          ‖curveVelocity (I := I) γ s‖ₑ
            = ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
        intro s hs
        have hsIcc : s ∈ Icc (0:ℝ) t₁ := Ioo_subset_Icc_self hs
        have hev : γ =ᶠ[𝓝 s] (fun r => expMap cov x₀ (σ r)) := by
          filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
          exact hσinv r (Ioo_subset_Icc_self hr)
        have hsm' : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s) :=
          (hsm₀ (σ s) (lt_of_lt_of_le (hσnorm s hsIcc) hRs)).mdifferentiableAt (by norm_num)
        have hvec : curveVelocity (I := I) γ s
            = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s) :=
          curveVelocity_eq_exp_deriv (cov := cov) x₀ (hσd s hsIcc) hsm' hev
        rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, hvec, hev.eq_of_nhds]
      -- apply the staying lemma
      have hσ0' : σ 0 = 0 := by
        rw [hσapp 0, hγ0, ← expMap_zero (cov := cov) x₀, hφdef]
        exact hf.localInverse_left_inv hf.localInverse_mem_target
      have hstay_lem := pathELength_ge_radial_of_stays (cov := cov) x₀ (σ := σ) (σ' := σ')
        (R := R) (ρg := ρg) hRg hgauss ht₁Icc hσd hσC1 hσnorm hσ0' hvelnorm
      -- the length is < ofReal ℓ
      have hlen_t : Manifold.pathELength I γ 0 t₁ < ENNReal.ofReal ℓ :=
        lt_of_le_of_lt (Manifold.pathELength_mono le_rfl ht₁.2.le) hγlen
      have hRad_lt : Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)) < ℓ := by
        have h1 : ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)))
            < ENNReal.ofReal ℓ := lt_of_le_of_lt hstay_lem hlen_t
        rwa [ENNReal.ofReal_lt_ofReal_iff (by rw [hℓdef]; exact Real.sqrt_pos.mpr (chartGram_self_pos (mem_chart_source H x₀) hvne))] at h1
      -- σ t₁ is strictly inside the ball
      have hσt_small : ‖σ t₁‖ < R / 4 := by
        have h1 : lam * ‖σ t₁‖ ^ 2 ≤ chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁) := (hbnd x₀ (Set.mem_singleton x₀) (σ t₁)).1
        have h2 : chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁)
            = (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁))) ^ 2 :=
          (Real.sq_sqrt (chartGram_self_nonneg (I := I) x₀ x₀ (σ t₁))).symm
        have h3 : (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁))) ^ 2 < ℓ ^ 2 := by
          nlinarith [hRad_lt, Real.sqrt_nonneg (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁))]
        have h4 : ℓ ^ 2 < lam * (R / 4) ^ 2 := by
          have h5 : chartGram (I := I) x₀ x₀ v v ≤ Lam * ‖v‖ ^ 2 := (hbnd x₀ (Set.mem_singleton x₀) v).2
          have h6 : ℓ ^ 2 = chartGram (I := I) x₀ x₀ v v :=
            Real.sq_sqrt (chartGram_self_nonneg (I := I) x₀ x₀ v)
          have hs2 : Real.sqrt (lam / Lam) ^ 2 = lam / Lam :=
            Real.sq_sqrt (le_of_lt (div_pos hlam hLam))
          have h7 : ‖v‖ ^ 2 < (R / 4) ^ 2 * (lam / Lam) := by
            nlinarith [hvsqrt, norm_nonneg v, hRpos, hsqpos, hs2]
          have h10 : Lam * ((R / 4) ^ 2 * (lam / Lam)) = lam * (R / 4) ^ 2 := by
            field_simp
          have h9 : Lam * ‖v‖ ^ 2 < lam * (R / 4) ^ 2 := by
            calc Lam * ‖v‖ ^ 2 < Lam * ((R / 4) ^ 2 * (lam / Lam)) :=
                  mul_lt_mul_of_pos_left h7 hLam
              _ = lam * (R / 4) ^ 2 := h10
          rw [h6]
          exact lt_of_le_of_lt h5 h9
        have h11 : lam * ‖σ t₁‖ ^ 2 < lam * (R / 4) ^ 2 := by
          calc lam * ‖σ t₁‖ ^ 2 ≤ chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁) := h1
            _ = (Real.sqrt (chartGram (I := I) x₀ x₀ (σ t₁) (σ t₁))) ^ 2 := h2
            _ < ℓ ^ 2 := h3
            _ < lam * (R / 4) ^ 2 := h4
        have h12 : ‖σ t₁‖ ^ 2 < (R / 4) ^ 2 :=
          lt_of_mul_lt_mul_left h11 (le_of_lt hlam)
        have h13 : (0:ℝ) ≤ ‖σ t₁‖ := norm_nonneg _
        nlinarith [h12, h13, hRpos]
      -- neighbourhood of `t₁` staying in `u`
      have hW : {t : ℝ | γ t ∈ φ.source ∧ ‖φ (γ t)‖ < R / 4} ∈ 𝓝 t₁ := by
        have ht₁self : t₁ ∈ Icc (0:ℝ) t₁ := ⟨ht₁.1, le_rfl⟩
        have hγt_src : γ t₁ ∈ φ.source := hσsrc t₁ ht₁self
        have hcont_φ : ContinuousAt φ (γ t₁) :=
          hφmd.continuousOn.continuousAt (hφopen.mem_nhds hγt_src)
        have hcont : ContinuousAt (fun t => φ (γ t)) t₁ := hcont_φ.comp hγC1.continuous.continuousAt
        have hmem : {t : ℝ | φ (γ t) ∈ Metric.ball (0 : E) (R / 4)} ∈ 𝓝 t₁ :=
          hcont.preimage_mem_nhds
            (Metric.isOpen_ball.mem_nhds (by
              rw [Metric.mem_ball, dist_zero_right, ← hσapp t₁]
              exact hσt_small))
        have hmem2 : {t : ℝ | γ t ∈ φ.source} ∈ 𝓝 t₁ :=
          hγC1.continuous.continuousAt.preimage_mem_nhds (hφopen.mem_nhds hγt_src)
        filter_upwards [hmem, hmem2] with t ht ht2
        exact ⟨ht2, by rwa [Metric.mem_ball, dist_zero_right] at ht⟩
      show sset ∈ 𝓝 t₁ ⊓ Filter.principal (Ioi t₁)
      rw [Filter.mem_inf_principal]
      refine Filter.mem_of_superset hW ?_
      rintro t ⟨htφ, htφ4⟩ htIoi
      rw [hsdef, hudef]
      refine ⟨φ (γ t), ?_, ?_⟩
      · rw [closure_ball (0 : E) (by linarith : (R / 2) ≠ 0)]
        exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
      · exact hφright (γ t) htφ
    -- conclude that the path stays in `u`
    have hIcc : Icc (0:ℝ) 1 ⊆ sset :=
      ((hu_closed.preimage hγC1.continuous).inter isClosed_Icc)
        |>.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hbase hstep
    have hγ1u : γ 1 ∈ u := hIcc ⟨zero_le_one, le_rfl⟩
    -- γ 1 = expMap v and v is the radial coordinate
    obtain ⟨w, hw, hw1⟩ := hu_mem 1 hγ1u
    have hφ1 : σ 1 = v := by
      rw [hσapp 1, hγ1, hφdef]
      exact hf.localInverse_left_inv (by
        have hvε : v ∈ Metric.ball (0:E) ε := by
          rw [Metric.mem_ball, dist_zero_right]; linarith
        exact hεball hvε)
    -- apply the staying lemma on the whole interval
    have hstay_full : ∀ s ∈ Icc (0:ℝ) 1, γ s ∈ φ.source ∧ ‖σ s‖ < R := by
      intro s hs
      obtain ⟨w, hw, hws⟩ := hu_mem s (hIcc hs)
      have hσs : σ s = w := by rw [hσapp s, hws]; exact (hφball w hw).2
      exact ⟨by rw [hws]; exact (hφball w hw).1, by rw [hσs]; linarith⟩
    have hσC1_full : ContDiffOn ℝ 1 σ (Icc (0:ℝ) 1) := by
      have h1 : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0:ℝ) 1) := hγC1.contMDiffOn
      have h2 : ContMDiffOn I 𝓘(ℝ, E) 1 φ φ.source := hφmd.of_le (WithTop.coe_le_coe.mpr le_top : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
      exact contMDiffOn_iff_contDiffOn.mp
        (h2.comp h1 (fun s hs => (hstay_full s hs).1))
    have hσd_full : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt σ (σ' s) s := by
      intro s hs
      have hγmd : MDifferentiableAt 𝓘(ℝ) I γ s := hγC1.mdifferentiableAt one_ne_zero
      have hφmdAt : MDifferentiableAt I 𝓘(ℝ, E) φ (γ s) :=
        (hφmd.mdifferentiableOn (by norm_num) (γ s) (hstay_full s hs).1).mdifferentiableAt
          (hφopen.mem_nhds (hstay_full s hs).1)
      have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (φ ∘ γ) s := hφmdAt.comp s hγmd
      have hdiff : DifferentiableAt ℝ σ s := mdifferentiableAt_iff_differentiableAt.mp hcomp
      have hderiv : deriv σ s
          = (mfderiv I 𝓘(ℝ, E) φ (γ s)) ((mfderiv 𝓘(ℝ) I γ s) (1 : ℝ)) :=
        (Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (g := φ) (γ := γ) hφmdAt hγmd).symm
      rw [hσ'def]
      exact hdiff.hasDerivAt.congr_deriv hderiv
    have hvelnorm_full : ∀ s ∈ Ioo (0:ℝ) 1,
        ‖curveVelocity (I := I) γ s‖ₑ
          = ‖(mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s)‖ₑ := by
      intro s hs
      have hsIcc : s ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hs
      have hev : γ =ᶠ[𝓝 s] (fun r => expMap cov x₀ (σ r)) := by
        filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
        have hrIcc : r ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hr
        exact (hφright (γ r) (hstay_full r hrIcc).1).symm
      have hsm' : MDifferentiableAt 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s) :=
        (hsm₀ (σ s) (lt_of_lt_of_le (hstay_full s hsIcc).2 hRs)).mdifferentiableAt (by norm_num)
      have hvec : curveVelocity (I := I) γ s
          = (mfderiv 𝓘(ℝ, E) I (fun v : E => expMap cov x₀ v) (σ s)) (σ' s) :=
        curveVelocity_eq_exp_deriv (cov := cov) x₀ (hσd_full s hsIcc) hsm' hev
      rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, hvec, hev.eq_of_nhds]
    have hσ0'' : σ 0 = 0 := by
      rw [hσapp 0, hγ0, ← expMap_zero (cov := cov) x₀, hφdef]
      exact hf.localInverse_left_inv hf.localInverse_mem_target
    have hfull := pathELength_ge_radial_of_stays (cov := cov) x₀ (σ := σ) (σ' := σ')
      (R := R) (ρg := ρg) hRg hgauss ⟨zero_le_one, le_rfl⟩ hσd_full hσC1_full
      (fun s hs => (hstay_full s hs).2) hσ0'' hvelnorm_full
    rw [hφ1] at hfull
    exact absurd (lt_of_le_of_lt hfull hγlen) (lt_irrefl _)


end
end Submission.Minimal
