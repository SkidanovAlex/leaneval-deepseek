import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SqrtKin.heatK_mass
import Submission.Work.BoseBoxFock.SqrtKin.heatK_t_rpow_lintegral
import Submission.Work.BoseBoxFock.SqrtKin.riesz_pair_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heatK_t_rpow_swap`

The `t`-integration of the heat-regularised difference form against `t^{-3/2}`:

`∫_0^∞ t^{-3/2} · diffHeat g t dt = (2/π^{3/2}) · diffKernel g`,

for `g` smooth and compactly supported, where

* `diffHeat g t = ∬ heatK t (x-y)‖g x - g y‖²` with `heatK t z = (4πt)^{-3/2}e^{-‖z‖²/4t}`,
* `diffKernel g = ∬ ‖x-y‖^{-4}‖g x - g y‖²`.

**Proof.** All integrands are nonnegative, so everything is done in `ℝ≥0∞` (Tonelli, no
integrability needed a priori) and converted back at the end:

1. for each `(x,y)` the pointwise `t`-integral is the Riesz kernel,
   `∫_0^∞ t^{-3/2}heatK t (x-y)dt = 2π^{-3/2}‖x-y‖^{-4}` (`heatK_rpow_integral`, proved in the
   corpus) — this is `heatK_t_rpow_lintegral`;
2. Tonelli over `(t, x, y)`;
3. the `(x,y)`-double integral of the Riesz kernel is finite (`riesz_pair_integrable`);
4. the resulting real integral is finite, which yields the integrability of
   `t ↦ t^{-3/2}diffHeat g t` and hence the `ofReal`-conversion back to reals.

The elementary analytic inputs `integrable_norm_sq_g`, `heatK_mul_integrable` and
`heatK_pair_integrable` are small variations of lemmas proved in
`Submission/Work/BoseBoxFock/sqrtKin_diffForm.lean` (namespace `Work.BoseBoxFock`); they are
re-proved here so that this module rests only on completed (warning-free) imports.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 0. Elementary integrability inputs -/

/-- The heat kernel of `ℝ³` is integrable at each positive time. -/
lemma integrable_heatK_local {t : ℝ} (ht : 0 < t) : Integrable (fun z : ℝ³ => heatK t z) := by
  have hne : (∫ y : ℝ³, heatK t y) ≠ 0 := by
    have h1 : (∫ y : ℝ³, heatK t y) = ∫ y : ℝ³, heatK t (0 - y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [zero_sub, heatK_even]
    rw [h1, heatK_mass ht 0]
    norm_num
  by_contra hcon
  exact hne (MeasureTheory.integral_undef hcon)

/-- `‖g‖²` is integrable for smooth compactly supported `g`. -/
lemma integrable_norm_sq_g {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : Integrable (fun x : ℝ³ => ‖g x‖ ^ 2) := by
  obtain ⟨C, _hC0, hC⟩ := bounded_g hg hgc
  have h1 : Integrable g := integrable_g_of hg hgc
  refine Integrable.mono' (h1.norm.const_mul C) ?_ ?_
  · exact (h1.1.norm).pow 2
  · filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (g x), hC x]

/-- Mixed integrability of the heat kernel against an `L¹` weight (second factor). -/
lemma heatK_mul_integrable {h : ℝ³ → ℝ} (hh : Integrable h) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * h q.2) (volume.prod volume) := by
  have h := Integrable.convolution_integrand (μ := volume) (ν := volume)
    (L := ContinuousLinearMap.mul ℝ ℝ) (f := h) (g := fun z : ℝ³ => heatK t z)
    hh (integrable_heatK_local ht)
  simpa [ContinuousLinearMap.mul_apply, Function.uncurry, mul_comm] using h

/-- Mixed integrability of the heat kernel against an `L¹` weight (first factor). -/
lemma heatK_mul_integrable' {h : ℝ³ → ℝ} (hh : Integrable h) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * h q.1) (volume.prod volume) := by
  have h := (heatK_mul_integrable hh ht).swap
  refine h.congr (Eventually.of_forall fun q => ?_)
  obtain ⟨x, y⟩ := q
  simp only [Function.comp_apply, Prod.swap_prod_mk]
  rw [show heatK t (y - x) = heatK t (x - y) by
    rw [show y - x = -(x - y) by abel, heatK_even]]

/-- The heat-regularised difference integrand is jointly integrable on `ℝ³ × ℝ³`. -/
lemma heatK_pair_integrable {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)
      (volume.prod volume) := by
  have hg2 : Integrable (fun x : ℝ³ => ‖g x‖ ^ 2) := integrable_norm_sq_g hg hgc
  have hF2 := heatK_mul_integrable hg2 ht
  have hF1 := heatK_mul_integrable' hg2 ht
  refine Integrable.mono' ((hF1.const_mul 2).add (hF2.const_mul 2)) ?_ ?_
  · have hcont : Continuous (fun q : ℝ³ × ℝ³ =>
        heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2) := by
      refine Continuous.mul ((heatK_continuous ht).comp (continuous_fst.sub continuous_snd)) ?_
      exact ((hg.continuous.comp continuous_fst).sub
        (hg.continuous.comp continuous_snd)).norm.pow 2
    exact hcont.aestronglyMeasurable
  · filter_upwards with q
    obtain ⟨x, y⟩ := q
    rw [Real.norm_of_nonneg (mul_nonneg (heatK_nonneg ht.le _) (by positivity))]
    have h1 : ‖g x - g y‖ ^ 2 ≤ 2 * ‖g x‖ ^ 2 + 2 * ‖g y‖ ^ 2 := by
      have h2 : ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := by
        calc ‖g x - g y‖ = ‖g x + (-g y)‖ := by rw [sub_eq_add_neg]
          _ ≤ ‖g x‖ + ‖-g y‖ := norm_add_le _ _
          _ = ‖g x‖ + ‖g y‖ := by rw [norm_neg]
      have h4 : ‖g x - g y‖ ^ 2 ≤ (‖g x‖ + ‖g y‖) ^ 2 := by
        rw [sq, sq]
        exact mul_le_mul h2 h2 (norm_nonneg _) (by positivity)
      have h5 : (‖g x‖ + ‖g y‖) ^ 2 ≤ 2 * ‖g x‖ ^ 2 + 2 * ‖g y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖g x‖ - ‖g y‖)]
      linarith
    calc heatK t (x - y) * ‖g x - g y‖ ^ 2
        ≤ heatK t (x - y) * (2 * ‖g x‖ ^ 2 + 2 * ‖g y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (heatK_nonneg ht.le _)
      _ = 2 * (heatK t (x - y) * ‖g x‖ ^ 2) + 2 * (heatK t (x - y) * ‖g y‖ ^ 2) := by ring

/-- The iterated integral defining `diffHeat` is the integral over the product measure. -/
lemma diffHeat_eq_integral_prod {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    diffHeat g t = ∫ q : ℝ³ × ℝ³, heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2 := by
  have hInt : Integrable
      (Function.uncurry (fun x y : ℝ³ => heatK t (x - y) * ‖g x - g y‖ ^ 2))
      (volume.prod volume) := heatK_pair_integrable hg hgc ht
  rw [diffHeat]
  exact integral_integral hInt

/-- **The heat pairing in `ofReal`/`∫⁻` form**: for `t > 0` the double integral defining
`diffHeat g t` is the `∫⁻`-integral of the `ofReal` of the joint integrand. -/
lemma ofReal_diffHeat_eq {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (diffHeat g t)
      = ∫⁻ q : ℝ³ × ℝ³,
          ENNReal.ofReal (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2) := by
  rw [diffHeat_eq_integral_prod hg hgc ht]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (heatK_pair_integrable hg hgc ht)
    (Eventually.of_forall fun q => mul_nonneg (heatK_nonneg ht.le _) (by positivity))

theorem heatK_t_rpow_swap {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * diffHeat g t)
      = (2 / Real.pi ^ (3 / 2 : ℝ)) * diffKernel g := by
  set c₀ : ℝ := 2 / Real.pi ^ (3 / 2 : ℝ) with hc₀def
  have hc₀ : 0 ≤ c₀ := by rw [hc₀def]; positivity
  -- ## the Riesz pair integrand
  have hriesz : Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2) (volume.prod volume) :=
    riesz_pair_integrable hg hgc
  have hriesz' : Integrable (Function.uncurry (fun x y : ℝ³ =>
      ‖x - y‖ ^ (-(4 : ℝ)) * ‖g x - g y‖ ^ 2)) (volume.prod volume) := hriesz
  have hriesz_nn : ∀ q : ℝ³ × ℝ³,
      0 ≤ ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2 :=
    fun q => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hdK : diffKernel g
      = ∫ q : ℝ³ × ℝ³, ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2 := by
    rw [diffKernel]
    exact integral_integral hriesz'
  have hdKnn : 0 ≤ c₀ * diffKernel g :=
    mul_nonneg hc₀ (by rw [hdK]; exact integral_nonneg_of_ae (Eventually.of_forall hriesz_nn))
  have hdKlin : ENNReal.ofReal (diffKernel g)
      = ∫⁻ q : ℝ³ × ℝ³,
          ENNReal.ofReal (‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2) := by
    rw [hdK]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hriesz
      (Eventually.of_forall hriesz_nn)
  -- ## the per-`(x,y)` computation of the `t`-integral
  have hperq : ∀ q : ℝ³ × ℝ³,
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
          (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)))
        = ENNReal.ofReal (c₀ * (‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2)) := by
    intro q
    by_cases hq : q.1 = q.2
    · rw [hq]
      simp [Real.zero_rpow (by norm_num : (-(4 : ℝ)) ≠ 0)]
    · exact heatK_t_rpow_lintegral (sub_ne_zero.mpr hq) (by positivity)
  -- ## joint measurability for Tonelli
  have hgm : Measurable g := hg.continuous.measurable
  have hm1 : Measurable (fun p : ℝ × (ℝ³ × ℝ³) => heatK p.1 (p.2.1 - p.2.2)) := by
    unfold heatK
    fun_prop
  have hm2 : Measurable (fun p : ℝ × (ℝ³ × ℝ³) => ‖g p.2.1 - g p.2.2‖ ^ 2) := by
    have h : Measurable (fun p : ℝ × (ℝ³ × ℝ³) => g p.2.1 - g p.2.2) :=
      (hgm.comp (by fun_prop)).sub (hgm.comp (by fun_prop))
    exact h.norm.pow_const 2
  have hΦmeas : AEMeasurable (Function.uncurry (fun t (q : ℝ³ × ℝ³) =>
      ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
        (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2))))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
    have h3 : Measurable (fun p : ℝ × (ℝ³ × ℝ³) => p.1 ^ (-(3 : ℝ) / 2)) := by fun_prop
    have h4 : Measurable (fun p : ℝ × (ℝ³ × ℝ³) =>
        ENNReal.ofReal (p.1 ^ (-(3 : ℝ) / 2) *
          (heatK p.1 (p.2.1 - p.2.2) * ‖g p.2.1 - g p.2.2‖ ^ 2))) :=
      ENNReal.measurable_ofReal.comp (h3.mul (hm1.mul hm2))
    exact h4.aemeasurable
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := volume.restrict (Set.Ioi 0)) (ν := volume.prod volume) hΦmeas
  -- ## the inner `q`-integral at fixed `t`
  have hbmeas : ∀ t : ℝ, Measurable (fun q : ℝ³ × ℝ³ =>
      ENNReal.ofReal (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)) := by
    intro t
    refine ENNReal.measurable_ofReal.comp ?_
    have h5 : Measurable (fun q : ℝ³ × ℝ³ => heatK t (q.1 - q.2)) := by
      unfold heatK; fun_prop
    have h6 : Measurable (fun q : ℝ³ × ℝ³ => ‖g q.1 - g q.2‖ ^ 2) := by
      have h : Measurable (fun q : ℝ³ × ℝ³ => g q.1 - g q.2) :=
        (hgm.comp measurable_fst).sub (hgm.comp measurable_snd)
      exact h.norm.pow_const 2
    exact h5.mul h6
  have hinner : Set.EqOn (fun t : ℝ => ∫⁻ q : ℝ³ × ℝ³,
        ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
          (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)))
      (fun t : ℝ => ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * diffHeat g t)) (Set.Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    show (∫⁻ q : ℝ³ × ℝ³, ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
          (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)))
        = ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * diffHeat g t)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _),
      ofReal_diffHeat_eq hg hgc ht0,
      ← MeasureTheory.lintegral_const_mul (ENNReal.ofReal (t ^ (-(3 : ℝ) / 2)))
        (hbmeas t)]
    exact MeasureTheory.lintegral_congr
      (fun q => ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _))
  -- ## the outer `t`-integral at fixed `(x,y)`
  have hRiesz_meas : Measurable (fun q : ℝ³ × ℝ³ =>
      ENNReal.ofReal (‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h7 : Measurable (fun q : ℝ³ × ℝ³ => ‖q.1 - q.2‖ ^ (-(4 : ℝ))) := by fun_prop
    have h6 : Measurable (fun q : ℝ³ × ℝ³ => ‖g q.1 - g q.2‖ ^ 2) := by
      have h : Measurable (fun q : ℝ³ × ℝ³ => g q.1 - g q.2) :=
        (hgm.comp measurable_fst).sub (hgm.comp measurable_snd)
      exact h.norm.pow_const 2
    exact h7.mul h6
  have houter : (∫⁻ q : ℝ³ × ℝ³, ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) *
          (heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)))
      = ENNReal.ofReal (c₀ * diffKernel g) := by
    rw [MeasureTheory.lintegral_congr hperq,
      MeasureTheory.lintegral_congr (fun q => ENNReal.ofReal_mul hc₀),
      MeasureTheory.lintegral_const_mul (ENNReal.ofReal c₀) hRiesz_meas, ← hdKlin,
      ← ENNReal.ofReal_mul hc₀]
  -- ## the `ℝ≥0∞` identity
  have hmain : (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-(3 : ℝ) / 2) * diffHeat g t))
      = ENNReal.ofReal (c₀ * diffKernel g) := by
    rw [← MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi hinner]
    exact hswap.trans houter
  -- ## measurability and integrability of the real integrand
  have hAESM0 : AEStronglyMeasurable (fun t : ℝ => ∫ q : ℝ³ × ℝ³,
      heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2) (volume.restrict (Set.Ioi 0)) := by
    have h1 : Measurable (fun p : ℝ × (ℝ³ × ℝ³) => heatK p.1 (p.2.1 - p.2.2) *
        ‖g p.2.1 - g p.2.2‖ ^ 2) := hm1.mul hm2
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume.prod volume)
      (f := fun t (q : ℝ³ × ℝ³) => heatK t (q.1 - q.2) * ‖g q.1 - g q.2‖ ^ 2)
      h1.stronglyMeasurable).aestronglyMeasurable
  have hAESM : AEStronglyMeasurable (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * diffHeat g t)
      (volume.restrict (Set.Ioi 0)) := by
    have h3 : Measurable (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) := by fun_prop
    refine (h3.aestronglyMeasurable.mul hAESM0).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Pi.mul_apply]
    rw [diffHeat_eq_integral_prod hg hgc ht]
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * diffHeat g t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    refine mul_nonneg (Real.rpow_nonneg ht.le _) ?_
    rw [diffHeat]
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    refine integral_nonneg_of_ae ?_
    filter_upwards with y
    exact mul_nonneg (heatK_nonneg ht.le _) (by positivity)
  have hfin : HasFiniteIntegral (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * diffHeat g t)
      (volume.restrict (Set.Ioi 0)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn, hmain]
    exact ENNReal.ofReal_lt_top
  have hInt : Integrable (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * diffHeat g t)
      (volume.restrict (Set.Ioi 0)) := ⟨hAESM, hfin⟩
  have h9 : ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * diffHeat g t)
      = ENNReal.ofReal (c₀ * diffKernel g) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, hmain]
  have hLHSnn : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * diffHeat g t :=
    integral_nonneg_of_ae hnn
  have hkey := (ENNReal.ofReal_eq_ofReal_iff hLHSnn hdKnn).mp h9
  simpa [hc₀def] using hkey

end Work.BoseBoxFock.SqrtKin
