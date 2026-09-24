import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.uniform_of_exp
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.basic_cNu
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.ode_solve
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.gamma_log_limit
import Submission.Work.NumberTheory.Chen.ApSumTenth.eulerMascheroni_eq_integral

/-!
# `∫ (1+z)⁻¹ d(cNu) = e^{-γ}`

`cNu` is the law of the reference sum `cY = Σ_{k ≥ 1} e^{-S_k}` (`S_k` the partial sums of
iid standard exponentials), i.e. the extremal "infinitely fine" configuration of the
linear sieve.  Its Laplace transform `phi L = ∫ e^{-Lz} d(cNu)` satisfies, by the
self-similarity `cNu = law of U·(1+Y)`,

  `phi L = ∫_0^1 e^{-Lu} phi (Lu) du`,   hence   `L · phi L = ∫_0^L e^{-s} phi s ds`,

and `ode_solve` then gives `phi L = exp (-∫_0^L (1-e^{-s})/s ds)`.  Evaluating at `L → ∞`
via the integral representation of `γ`, and comparing with the limit
`L · phi L → ∫ (1+z)⁻¹ d(cNu)` (dominated convergence on the product measure), gives the
value `e^{-γ}` of the total mass functional of `cNu`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-! ### The product-measure integral defining `phi` -/

lemma phi_map_prod (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (L : ℝ) :
    phi L = ∫ p : ℝ × ℝ, Real.exp (-(L * (p.1 * (1 + p.2)))) ∂(cUnif.prod cNu) := by
  have hf : Measurable (fun p : ℝ × ℝ => p.1 * (1 + p.2)) := by fun_prop
  have hg : AEStronglyMeasurable (fun z : ℝ => Real.exp (-(L * z)))
      ((cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2))) :=
    (by fun_prop : Measurable fun z : ℝ => Real.exp (-(L * z))).aestronglyMeasurable
  have hkey : phi L = ∫ z : ℝ, Real.exp (-(L * z))
      ∂((cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2))) := by
    rw [← hself]
    rfl
  rw [hkey]
  exact integral_map hf.aemeasurable hg

/-- Integration against `cUnif` is integration over the interval `(0,1)`. -/
lemma integral_cUnif_eq_interval
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) (g : ℝ → ℝ) :
    (∫ u, g u ∂cUnif) = ∫ u in (0:ℝ)..1, g u := by
  rw [hcUnif, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 1))]

/-- The pushforward form: `phi L = ∫_0^1 e^{-Lu} phi (Lu) du`. -/
lemma phi_eq_integral_cUnif
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    (L : ℝ) (hL : 0 ≤ L) :
    phi L = ∫ u : ℝ, Real.exp (-(L * u)) * phi (L * u) ∂cUnif := by
  have hprod := integral_prod (μ := cUnif) (ν := cNu)
    (f := fun p : ℝ × ℝ => Real.exp (-(L * (p.1 * (1 + p.2)))))
    (integrable_exp_neg_mul_prod L hL)
  rw [phi_map_prod hself L, hprod]
  refine integral_congr_ae ?_
  filter_upwards with u
  have h : (fun z : ℝ => Real.exp (-(L * (u * (1 + z)))))
      = fun z : ℝ => Real.exp (-(L * u)) * Real.exp (-((L * u) * z)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h, integral_const_mul]
  rfl

/-- The ODE `L φ L = ∫_0^L e^{-s} φ s ds` for the Laplace transform of `cNu`. -/
lemma laplace_ode
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) :
    ∀ L : ℝ, 0 ≤ L → L * phi L = ∫ s in (0:ℝ)..L, Real.exp (-s) * phi s := by
  intro L hL
  rcases eq_or_lt_of_le hL with h | h
  · rw [← h, zero_mul, intervalIntegral.integral_same]
  · have hpush := phi_eq_integral_cUnif hself hcUnif L hL
    have h1 : (∫ u : ℝ, Real.exp (-(L * u)) * phi (L * u) ∂cUnif)
        = ∫ u in (0:ℝ)..1, Real.exp (-(L * u)) * phi (L * u) :=
      integral_cUnif_eq_interval hcUnif _
    have hsub : (∫ u in (0:ℝ)..1, Real.exp (-(L * u)) * phi (L * u))
        = L⁻¹ * ∫ s in (0:ℝ)..L, Real.exp (-s) * phi s := by
      have hcc := intervalIntegral.integral_comp_mul_left
        (f := fun s : ℝ => Real.exp (-s) * phi s) (a := (0:ℝ)) (b := (1:ℝ)) h.ne'
      simpa using hcc
    rw [hpush, h1, hsub, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]

/-! ### Evaluation of the inner integral over `cUnif` -/

lemma integral_exp_neg_mul_interval (a : ℝ) (ha : a ≠ 0) :
    (∫ u in (0:ℝ)..1, Real.exp (-(a * u))) = (1 - Real.exp (-a)) / a := by
  have h1 : (∫ u in (0:ℝ)..1, Real.exp (-(a * u)))
      = a⁻¹ * ∫ s in (0:ℝ)..a, Real.exp (-s) := by
    have hcc := intervalIntegral.integral_comp_mul_left
      (f := fun s : ℝ => Real.exp (-s)) (a := (0:ℝ)) (b := (1:ℝ)) ha
    simpa using hcc
  have h2 : (∫ s in (0:ℝ)..a, Real.exp (-s)) = 1 - Real.exp (-a) := by
    have hcc := intervalIntegral.integral_comp_neg (f := fun s : ℝ => Real.exp s)
      (a := (0:ℝ)) (b := a)
    rw [hcc, integral_exp]
    simp
  rw [h1, h2, div_eq_inv_mul]

/-- The "swap" form: `phi L = ∫ (1 - e^{-L(1+z)})/(L(1+z)) d(cNu)`, for `L > 0`. -/
lemma phi_eq_integral_cNu_div
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    (L : ℝ) (hL : 0 < L) :
    phi L = ∫ z : ℝ, (1 - Real.exp (-(L * (1 + z)))) / (L * (1 + z)) ∂cNu := by
  have hswap := integral_prod_symm (μ := cUnif) (ν := cNu)
    (f := fun p : ℝ × ℝ => Real.exp (-(L * (p.1 * (1 + p.2)))))
    (integrable_exp_neg_mul_prod L hL.le)
  rw [phi_map_prod hself L, hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_cNu_nonneg] with z hz
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have ha : L * (1 + z) ≠ 0 := ne_of_gt (mul_pos hL hz1)
  rw [integral_cUnif_eq_interval hcUnif]
  have hrewrite : (∫ u in (0:ℝ)..1, Real.exp (-(L * (u * (1 + z)))))
      = ∫ u in (0:ℝ)..1, Real.exp (-((L * (1 + z)) * u)) := by
    apply intervalIntegral.integral_congr
    intro u _
    change Real.exp (-(L * (u * (1 + z)))) = Real.exp (-((L * (1 + z)) * u))
    rw [show L * (u * (1 + z)) = (L * (1 + z)) * u from by ring]
  rw [hrewrite, integral_exp_neg_mul_interval (L * (1 + z)) ha]

/-- The limit form of the ODE: `L phi L = ∫ (1 - e^{-L(1+z)})/(1+z) d(cNu)`, for `L > 0`. -/
lemma laplace_J
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    (L : ℝ) (hL : 0 < L) :
    L * phi L = ∫ z : ℝ, (1 - Real.exp (-(L * (1 + z)))) / (1 + z) ∂cNu := by
  rw [phi_eq_integral_cNu_div hself hcUnif L hL, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_cNu_nonneg] with z hz
  have hz1 : (1:ℝ) + z ≠ 0 := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp

/-! ### Integrability of the "safe" representatives -/

lemma integrable_safe_inv :
    Integrable (fun z : ℝ => if 0 ≤ z then (1 + z)⁻¹ else 0) cNu := by
  refine Integrable.of_bound ?_ 1 ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  · filter_upwards with z
    by_cases hz : 0 ≤ z
    · rw [if_pos hz, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith)
    · rw [if_neg hz, norm_zero]
      norm_num

lemma integrable_safe_div (L : ℝ) (hL : 0 ≤ L) :
    Integrable (fun z : ℝ => if 0 ≤ z then (1 - Real.exp (-(L * (1 + z)))) / (1 + z) else 0)
      cNu := by
  refine Integrable.of_bound ?_ 1 ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  · filter_upwards with z
    by_cases hz : 0 ≤ z
    · rw [if_pos hz, Real.norm_eq_abs, abs_of_nonneg (by
        apply div_nonneg _ (by linarith)
        have ha : (0:ℝ) ≤ L * (1 + z) := by nlinarith
        linarith [Real.exp_le_one_iff.mpr (by linarith : -(L * (1 + z)) ≤ 0)])]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
      have he : (0:ℝ) < Real.exp (-(L * (1 + z))) := Real.exp_pos _
      nlinarith
    · rw [if_neg hz, norm_zero]
      norm_num

/-! ### The limit `L · phi L → ∫ (1+z)⁻¹ d(cNu)` -/

lemma tendsto_mul_phi
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) :
    Tendsto (fun L : ℝ => L * phi L) atTop (nhds (∫ z : ℝ, (1+z)⁻¹ ∂cNu)) := by
  set A : ℝ := ∫ z : ℝ, (1+z)⁻¹ ∂cNu with hA
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun L : ℝ => Real.exp (-L)) ?_ ?_
    Real.tendsto_exp_neg_atTop_nhds_zero
  · filter_upwards with L using norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hJ := laplace_J hself hcUnif L hL
    have hA' : A = ∫ z : ℝ, (if 0 ≤ z then (1 + z)⁻¹ else 0) ∂cNu := by
      rw [hA]
      refine integral_congr_ae ?_
      filter_upwards [ae_cNu_nonneg] with z hz
      rw [if_pos hz]
    have hJ' : L * phi L
        = ∫ z : ℝ, (if 0 ≤ z then (1 - Real.exp (-(L * (1 + z)))) / (1 + z) else 0) ∂cNu := by
      rw [hJ]
      refine integral_congr_ae ?_
      filter_upwards [ae_cNu_nonneg] with z hz
      rw [if_pos hz]
    have hdiff : L * phi L - A
        = ∫ z : ℝ, (if 0 ≤ z then -(Real.exp (-(L * (1 + z))) / (1 + z)) else 0) ∂cNu := by
      rw [hJ', hA', ← integral_sub (integrable_safe_div L hL.le) (integrable_safe_inv)]
      refine integral_congr_ae ?_
      filter_upwards with z
      by_cases hz : 0 ≤ z
      · rw [if_pos hz, if_pos hz, if_pos hz]
        have hz1 : (1:ℝ) + z ≠ 0 := by linarith
        field_simp
        ring
      · rw [if_neg hz, if_neg hz, if_neg hz, sub_zero]
    rw [hdiff]
    refine le_trans (MeasureTheory.norm_integral_le_of_norm_le_const (C := Real.exp (-L)) ?_) ?_
    · filter_upwards with z
      by_cases hz : 0 ≤ z
      · rw [if_pos hz, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
        calc Real.exp (-(L * (1 + z))) = Real.exp (-L) * Real.exp (-(L * z)) := by
              rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (-L) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
              rw [Real.exp_le_one_iff]
              nlinarith
          _ = Real.exp (-L) := mul_one _
          _ ≤ Real.exp (-L) * (1 + z) := by
              have h1 : (1:ℝ) ≤ 1 + z := by linarith
              nlinarith [Real.exp_pos (-L)]
      · rw [if_neg hz, norm_zero]
        exact Real.exp_nonneg _
    · rw [Measure.real_def, measure_univ]
      simp

/-! ### The main theorem -/

theorem inv_eq_exp_neg_gamma
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)) :
    (∫ z : ℝ, (1+z)⁻¹ ∂cNu) = Real.exp (- Real.eulerMascheroniConstant) := by
  have hsol := ode_solve phi phi_continuousOn phi_zero (laplace_ode hself hcUnif)
  set H : ℝ → ℝ := fun L => ∫ s in (0:ℝ)..L, (1 - Real.exp (-s))/s with hH
  have hlim : Tendsto (fun L : ℝ => L * phi L) atTop
      (nhds (Real.exp (- Real.eulerMascheroniConstant))) := by
    have hgl : Tendsto (fun L : ℝ => Real.log L - H L) atTop
        (nhds (- Real.eulerMascheroniConstant)) := by
      have hgl' := gamma_log_limit
      have hfun : (fun L : ℝ => Real.log L - H L)
          = fun L : ℝ => Real.log L - ∫ s in (0:ℝ)..L, (1 - Real.exp (-s))/s := by
        funext L; rw [congrFun hH L]
      rw [hfun]
      exact hgl'
    have hcomp : Tendsto (fun L : ℝ => Real.exp (Real.log L - H L)) atTop
        (nhds (Real.exp (- Real.eulerMascheroniConstant))) :=
      Real.continuous_exp.continuousAt.tendsto.comp hgl
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [hsol L hL.le, ← congrFun hH L, Real.exp_sub, Real.exp_log hL, Real.exp_neg,
      div_eq_mul_inv]
  exact tendsto_nhds_unique (tendsto_mul_phi hself hcUnif) hlim

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
