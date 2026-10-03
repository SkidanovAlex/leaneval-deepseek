import Mathlib

/-!
# Building blocks for the separating function of *FI* Lemma 26.1

This file develops the analytic vocabulary used in `Work.FIArea7.exists_separating_function`:

* `sepRho` — a `C^∞` flat-topped probability density supported on `[-1,1]` with `∫|ρ'| = 16/15`;
* `sepPsi` — its primitive, a smooth odd sigmoid with `Ψ = -1/2` on `(-∞,-1]` and `Ψ = 1/2` on
  `[1,∞)`;
* `sepK` — the smooth trapezoid `x ↦ Ψ((x+λ)/ε) - Ψ((x-λ)/ε)`, equal to `1` on `[-λ+ε, λ-ε]`
  and to `0` off `[-λ-ε, λ+ε]`, with `∫K = 2λ`, `∫|K'| = 2` and `∫|K''| ≤ 32/(15ε)`.
-/

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology

noncomputable section

/-! ## 1. The transition function `Real.smoothTransition` -/

/-- Symmetry of Mathlib's smooth transition: `τ u + τ (1 - u) = 1`. -/
lemma smoothTransition_add_sub (u : ℝ) :
    Real.smoothTransition u + Real.smoothTransition (1 - u) = 1 := by
  have h := Real.smoothTransition.pos_denom u
  have h2 : expNegInvGlue (1 - u) + expNegInvGlue u ≠ 0 := ne_of_gt (by linarith)
  unfold Real.smoothTransition
  rw [show (1:ℝ) - (1 - u) = u by ring]
  rw [div_add_div _ _ (ne_of_gt h) h2]
  rw [div_eq_one_iff_eq (by positivity)]
  ring

/-- `∫_0^1 τ = 1/2`. -/
lemma integral_smoothTransition_zero_one : ∫ u in (0:ℝ)..1, Real.smoothTransition u = 1/2 := by
  have hsym : ∫ u in (0:ℝ)..1, Real.smoothTransition (1 - u)
      = ∫ u in (0:ℝ)..1, Real.smoothTransition u := by
    rw [integral_comp_sub_left]; norm_num
  have hsub : ∫ u in (0:ℝ)..1, Real.smoothTransition (1 - u)
      = ∫ u in (0:ℝ)..1, (1 - Real.smoothTransition u) := by
    apply integral_congr; intro u _
    have := smoothTransition_add_sub u; linarith
  have hone : ∫ u in (0:ℝ)..1, (1 - Real.smoothTransition u)
      = 1 - ∫ u in (0:ℝ)..1, Real.smoothTransition u := by
    rw [intervalIntegral.integral_sub]
    · norm_num [intervalIntegral.integral_const]
    · exact intervalIntegrable_const
    · exact (Real.smoothTransition.continuous.intervalIntegrable 0 1)
  linarith

/-- `∫_0^c τ u τ (c-u) du = c - 1` for `c ≥ 2`. -/
lemma integral_smoothTransition_mul (c : ℝ) (hc : 2 ≤ c) :
    ∫ u in (0:ℝ)..c, Real.smoothTransition u * Real.smoothTransition (c - u) = c - 1 := by
  have hcont : Continuous fun u : ℝ => Real.smoothTransition u * Real.smoothTransition (c - u) :=
    Real.smoothTransition.continuous.mul
      (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))
  have h1 : ∫ u in (0:ℝ)..1, Real.smoothTransition u * Real.smoothTransition (c - u)
      = ∫ u in (0:ℝ)..1, Real.smoothTransition u := by
    apply integral_congr; intro u hu
    show Real.smoothTransition u * Real.smoothTransition (c - u) = Real.smoothTransition u
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    have : Real.smoothTransition (c - u) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      have := hu.2; linarith
    rw [this, mul_one]
  have h2 : ∫ u in (1:ℝ)..(c-1), Real.smoothTransition u * Real.smoothTransition (c - u)
      = c - 2 := by
    have hconst : ∫ u in (1:ℝ)..(c-1), Real.smoothTransition u * Real.smoothTransition (c - u)
        = ∫ u in (1:ℝ)..(c-1), (1:ℝ) := by
      apply integral_congr; intro u hu
      show Real.smoothTransition u * Real.smoothTransition (c - u) = (1:ℝ)
      rw [Set.uIcc_of_le (by linarith : (1:ℝ) ≤ c-1)] at hu
      have hA : Real.smoothTransition u = 1 := Real.smoothTransition.one_of_one_le hu.1
      have hB : Real.smoothTransition (c - u) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith [hu.2])
      rw [hA, hB, mul_one]
    rw [hconst, intervalIntegral.integral_const]
    simp
    ring
  have h3 : ∫ u in (c-1)..c, Real.smoothTransition u * Real.smoothTransition (c - u) = 1/2 := by
    have hconst : ∫ u in (c-1)..c, Real.smoothTransition u * Real.smoothTransition (c - u)
        = ∫ u in (c-1)..c, Real.smoothTransition (c - u) := by
      apply integral_congr; intro u hu
      show Real.smoothTransition u * Real.smoothTransition (c - u) = Real.smoothTransition (c - u)
      rw [Set.uIcc_of_le (by linarith : c-1 ≤ c)] at hu
      have hA : Real.smoothTransition u = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith [hu.1])
      rw [hA, one_mul]
    rw [hconst, integral_comp_sub_left]
    norm_num
    exact integral_smoothTransition_zero_one
  have h01 : (∫ u in (0:ℝ)..1, Real.smoothTransition u * Real.smoothTransition (c - u))
      + (∫ u in (1:ℝ)..(c-1), Real.smoothTransition u * Real.smoothTransition (c - u))
      = ∫ u in (0:ℝ)..(c-1), Real.smoothTransition u * Real.smoothTransition (c - u) :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 (c-1))
  have h02 : (∫ u in (0:ℝ)..(c-1), Real.smoothTransition u * Real.smoothTransition (c - u))
      + (∫ u in (c-1)..c, Real.smoothTransition u * Real.smoothTransition (c - u))
      = ∫ u in (0:ℝ)..c, Real.smoothTransition u * Real.smoothTransition (c - u) :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 (c-1)) (hcont.intervalIntegrable (c-1) c)
  have key : ∫ u in (0:ℝ)..c, Real.smoothTransition u * Real.smoothTransition (c - u) = c - 1 := by
    rw [← h02, ← h01, h1, h2, h3]
    rw [show (∫ u in (0:ℝ)..1, Real.smoothTransition u) = 1/2 from integral_smoothTransition_zero_one]
    ring
  exact key

/-! ### Derivatives of `τ` -/

lemma deriv_smoothTransition_continuous : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).continuous_deriv_one

lemma deriv_smoothTransition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_smoothTransition_eq_zero_of_lt_neg {u : ℝ} (h : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_one_lt {u : ℝ} (h : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [hev.deriv_eq, deriv_const]

lemma deriv_smoothTransition_eq_zero_of_nonpos {u : ℝ} (h : u ≤ 0) :
    deriv Real.smoothTransition u = 0 := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_lt_neg h
  · have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ))
        (𝓝 (deriv Real.smoothTransition 0)) :=
      (deriv_smoothTransition_continuous.continuousAt.tendsto).mono_left inf_le_left
    have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0:ℝ)) (𝓝 0) := by
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact deriv_smoothTransition_eq_zero_of_lt_neg hu
    exact tendsto_nhds_unique h1 h2

lemma deriv_smoothTransition_eq_zero_of_one_le {u : ℝ} (h : 1 ≤ u) :
    deriv Real.smoothTransition u = 0 := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact deriv_smoothTransition_eq_zero_of_one_lt h
  · have h1 : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1:ℝ))
        (𝓝 (deriv Real.smoothTransition 1)) :=
      (deriv_smoothTransition_continuous.continuousAt.tendsto).mono_left inf_le_left
    have h2 : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1:ℝ)) (𝓝 0) := by
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact deriv_smoothTransition_eq_zero_of_one_lt hu
    exact tendsto_nhds_unique h1 h2

lemma intervalIntegrable_deriv_smoothTransition :
    IntervalIntegrable (deriv Real.smoothTransition) volume 0 1 :=
  deriv_smoothTransition_continuous.intervalIntegrable _ _

lemma integral_deriv_smoothTransition_zero_one :
    ∫ u in (0:ℝ)..1, deriv Real.smoothTransition u = 1 := by
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) 1, DifferentiableAt ℝ Real.smoothTransition x := fun x _ =>
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt
  rw [intervalIntegral.integral_deriv_eq_sub hdiff intervalIntegrable_deriv_smoothTransition]
  rw [Real.smoothTransition.one, Real.smoothTransition.zero]
  norm_num

lemma integral_deriv_smoothTransition : ∫ u : ℝ, deriv Real.smoothTransition u = 1 := by
  have hzero : ∀ u ∉ Set.Ioc (0:ℝ) 1, deriv Real.smoothTransition u = 0 := by
    intro u hu
    rw [Set.mem_Ioc, not_and_or, not_lt] at hu
    rcases hu with h | h
    · exact deriv_smoothTransition_eq_zero_of_nonpos h
    · exact deriv_smoothTransition_eq_zero_of_one_le (by linarith)
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact integral_deriv_smoothTransition_zero_one

lemma integral_deriv_smoothTransition_comp (b : ℝ) :
    ∫ y : ℝ, deriv Real.smoothTransition (8 * y + b) = 1/8 := by
  have h1 : ∫ y : ℝ, deriv Real.smoothTransition (8 * y + b)
      = ∫ u : ℝ, deriv Real.smoothTransition (8 * u) := by
    rw [show (∫ y : ℝ, deriv Real.smoothTransition (8 * y + b))
        = ∫ x : ℝ, (fun u : ℝ => deriv Real.smoothTransition (8*u)) (x + b/8) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      show deriv Real.smoothTransition (8*y+b) = deriv Real.smoothTransition (8*(y + b/8))
      ring_nf]
    exact integral_add_right_eq_self (fun u : ℝ => deriv Real.smoothTransition (8*u)) (b/8)
  rw [h1, Measure.integral_comp_mul_left (deriv Real.smoothTransition) 8,
    integral_deriv_smoothTransition]
  norm_num

lemma integrable_deriv_smoothTransition_comp (b : ℝ) :
    Integrable (fun y : ℝ => deriv Real.smoothTransition (8 * y + b)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact deriv_smoothTransition_continuous.comp (by fun_prop)
  · refine HasCompactSupport.intro (K := Set.Icc (-b/8) ((1-b)/8)) isCompact_Icc ?_
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · exact deriv_smoothTransition_eq_zero_of_nonpos (by linarith)
    · exact deriv_smoothTransition_eq_zero_of_one_le (by linarith)

/-! ## 2. The flat-topped density `sepRho` and its primitive `sepPsi` -/

/-- A `C^∞` flat-topped density: `= 1` on `[-7/8, 7/8]`, `C^∞`, positive, supported in `[-1,1]`. -/
noncomputable def sepRho (y : ℝ) : ℝ :=
  (8/15) * (Real.smoothTransition (8 * (y + 1)) * Real.smoothTransition (8 * (1 - y)))

/-- The primitive of the density `sepRho`, normalised to vanish at `0`.  It is an odd smooth
sigmoid with `Ψ z = -1/2` for `z ≤ -1` and `Ψ z = 1/2` for `z ≥ 1`. -/
noncomputable def sepPsi (z : ℝ) : ℝ := ∫ x in (0:ℝ)..z, sepRho x

lemma sepRho_continuous : Continuous sepRho := by
  unfold sepRho
  fun_prop

lemma sepRho_nonneg (y : ℝ) : 0 ≤ sepRho y := by
  unfold sepRho
  have h1 := Real.smoothTransition.nonneg (8 * (y + 1))
  have h2 := Real.smoothTransition.nonneg (8 * (1 - y))
  positivity

lemma sepRho_le (y : ℝ) : sepRho y ≤ 8/15 := by
  unfold sepRho
  have h1 := Real.smoothTransition.le_one (8 * (y + 1))
  have h2 := Real.smoothTransition.le_one (8 * (1 - y))
  have h3 := Real.smoothTransition.nonneg (8 * (y + 1))
  have h4 := Real.smoothTransition.nonneg (8 * (1 - y))
  nlinarith

lemma sepRho_eq_zero_of_le {y : ℝ} (h : y ≤ -1) : sepRho y = 0 := by
  unfold sepRho
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 8 * (y + 1) ≤ 0)]
  ring

lemma sepRho_eq_zero_of_one_le {y : ℝ} (h : 1 ≤ y) : sepRho y = 0 := by
  unfold sepRho
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 8 * (1 - y) ≤ 0)]
  ring

lemma sepRho_even (y : ℝ) : sepRho (-y) = sepRho y := by
  unfold sepRho
  rw [show 8 * (-y + 1) = 8 * (1 - y) by ring, show 8 * (1 - -y) = 8 * (y + 1) by ring]
  ring

lemma sepRho_eq_const {y : ℝ} (h1 : -7/8 ≤ y) (h2 : y ≤ 7/8) : sepRho y = 8/15 := by
  unfold sepRho
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8 * (y + 1)),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8 * (1 - y))]
  norm_num

lemma sepRho_hasDerivAt (y : ℝ) : HasDerivAt sepRho
    ((8/15) * ((deriv Real.smoothTransition (8*(y+1)) * 8) * Real.smoothTransition (8*(1-y)))
      + (8/15) * (Real.smoothTransition (8*(y+1)) * (deriv Real.smoothTransition (8*(1-y)) * (-8)))) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.smoothTransition (8 * (y + 1)))
      (deriv Real.smoothTransition (8*(y+1)) * 8) y := by
    have hg : HasDerivAt (fun y : ℝ => 8 * (y + 1)) 8 y := by
      simpa using (((hasDerivAt_id y : HasDerivAt (fun x : ℝ => x) 1 y)).add_const 1).const_mul (8:ℝ)
    have hf : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (8*(y+1))) (8*(y+1)) :=
      (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt).hasDerivAt
    exact hf.comp y hg
  have h2 : HasDerivAt (fun y : ℝ => Real.smoothTransition (8 * (1 - y)))
      (deriv Real.smoothTransition (8*(1-y)) * (-8)) y := by
    have hg : HasDerivAt (fun y : ℝ => 8 * (1 - y)) (-8) y := by
      simpa using (((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)).const_mul (8:ℝ))
    have hf : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (8*(1-y))) (8*(1-y)) :=
      (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt).hasDerivAt
    exact hf.comp y hg
  have h3 := (h1.mul h2).const_mul (8/15)
  unfold sepRho
  simpa only [Pi.mul_apply, mul_add] using h3

lemma integral_sepRho : ∫ x in (-1:ℝ)..1, sepRho x = 1 := by
  have hcongr : ∫ y in (-1:ℝ)..1, sepRho y
      = ∫ y in (-1:ℝ)..1,
          (8/15) * (fun u : ℝ => Real.smoothTransition u * Real.smoothTransition (16 - u)) (8*y+8) := by
    apply integral_congr; intro y _
    show sepRho y = (8/15) * (Real.smoothTransition (8*y+8) * Real.smoothTransition (16 - (8*y+8)))
    unfold sepRho
    rw [show 8*(y+1) = 8*y+8 by ring, show 8*(1-y) = 16-(8*y+8) by ring]
  rw [hcongr, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_add
    (f := fun u : ℝ => Real.smoothTransition u * Real.smoothTransition (16-u))
    (by norm_num : (8:ℝ) ≠ 0) 8]
  simp only [smul_eq_mul]
  norm_num
  rw [integral_smoothTransition_mul 16 (by norm_num)]
  norm_num

lemma integral_deriv_smoothTransition_comp8_neg (b : ℝ) :
    ∫ y : ℝ, deriv Real.smoothTransition (b - 8 * y) = 1/8 := by
  have h1 : ∫ y : ℝ, deriv Real.smoothTransition (b - 8*y)
      = ∫ w : ℝ, deriv Real.smoothTransition (-8*w) := by
    rw [show (∫ y : ℝ, deriv Real.smoothTransition (b - 8*y))
        = ∫ w : ℝ, (fun u : ℝ => deriv Real.smoothTransition (-8*u)) (w + (-(b/8))) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      show deriv Real.smoothTransition (b - 8*y)
        = deriv Real.smoothTransition (-8*(y + -(b/8)))
      ring_nf]
    exact integral_add_right_eq_self (fun u : ℝ => deriv Real.smoothTransition (-8*u)) (-(b/8))
  rw [h1, Measure.integral_comp_mul_left (deriv Real.smoothTransition) (-8),
    integral_deriv_smoothTransition]
  norm_num

lemma integrable_deriv_smoothTransition_comp8_neg (b : ℝ) :
    Integrable (fun y : ℝ => deriv Real.smoothTransition (b - 8 * y)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact deriv_smoothTransition_continuous.comp (by fun_prop)
  · refine HasCompactSupport.intro (K := Set.Icc ((b-1)/8) (b/8)) isCompact_Icc ?_
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · exact deriv_smoothTransition_eq_zero_of_one_lt (by linarith)
    · exact deriv_smoothTransition_eq_zero_of_nonpos (by linarith)

/-! ## 2b. The primitive `sepPsi` -/

lemma sepPsi_hasDerivAt (z : ℝ) : HasDerivAt sepPsi (sepRho z) z := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hG : HasDerivAt (fun u : ℝ => ∫ x in u..0, sepRho x) (-(sepRho z)) z :=
      intervalIntegral.integral_hasDerivAt_left (sepRho_continuous.intervalIntegrable z 0)
        (sepRho_continuous.stronglyMeasurable.stronglyMeasurableAtFilter)
        sepRho_continuous.continuousAt
    have h2 : (fun u : ℝ => ∫ x in (0:ℝ)..u, sepRho x) = fun u => - ∫ x in u..0, sepRho x := by
      funext u
      exact intervalIntegral.integral_symm u 0
    have hgoal : HasDerivAt (fun u : ℝ => - ∫ x in u..0, sepRho x) (sepRho z) z := by
      have h := hG.neg
      rw [neg_neg] at h
      exact h
    rwa [show sepPsi = fun u => ∫ x in (0:ℝ)..u, sepRho x from rfl, h2]
  · exact intervalIntegral.integral_hasDerivAt_right (sepRho_continuous.intervalIntegrable 0 0)
      (sepRho_continuous.stronglyMeasurable.stronglyMeasurableAtFilter)
      sepRho_continuous.continuousAt
  · exact intervalIntegral.integral_hasDerivAt_right (sepRho_continuous.intervalIntegrable 0 z)
      (sepRho_continuous.stronglyMeasurable.stronglyMeasurableAtFilter)
      sepRho_continuous.continuousAt

lemma deriv_sepPsi : deriv sepPsi = sepRho := funext fun z => (sepPsi_hasDerivAt z).deriv

lemma sepPsi_continuous : Continuous sepPsi := by
  rw [show sepPsi = fun u => ∫ x in (0:ℝ)..u, sepRho x from rfl]
  exact intervalIntegral.continuous_primitive (fun a b => sepRho_continuous.intervalIntegrable a b) 0

lemma sepPsi_monotone : Monotone sepPsi := by
  intro a b hab
  have hsplit : (∫ x in a..b, sepRho x)
      = (∫ x in (0:ℝ)..b, sepRho x) - (∫ x in (0:ℝ)..a, sepRho x) := by
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (sepRho_continuous.intervalIntegrable 0 a) (sepRho_continuous.intervalIntegrable a b)
    linarith [this]
  have hnonneg : 0 ≤ ∫ x in a..b, sepRho x :=
    intervalIntegral.integral_nonneg hab (fun x _ => sepRho_nonneg x)
  have hmain : sepPsi b - sepPsi a = ∫ x in a..b, sepRho x := by
    rw [sepPsi, sepPsi, hsplit]
  linarith [hmain ▸ hnonneg]

lemma integral_sepRho_zero_one : ∫ x in (0:ℝ)..1, sepRho x = 1/2 := by
  have hsym : (∫ x in (-1:ℝ)..0, sepRho x) = ∫ x in (0:ℝ)..1, sepRho x := by
    have h := intervalIntegral.integral_comp_neg (f := sepRho) (a := (-1:ℝ)) (b := (0:ℝ))
    simp only [neg_zero, neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro y _
    exact (sepRho_even y).symm
  have hadd : (∫ x in (-1:ℝ)..0, sepRho x) + (∫ x in (0:ℝ)..1, sepRho x)
      = ∫ x in (-1:ℝ)..1, sepRho x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (sepRho_continuous.intervalIntegrable (-1) 0) (sepRho_continuous.intervalIntegrable 0 1)
  rw [show (∫ x in (-1:ℝ)..1, sepRho x) = 1 from integral_sepRho] at hadd
  linarith

lemma sepPsi_eq_half {z : ℝ} (h : 1 ≤ z) : sepPsi z = 1/2 := by
  have hsplit : sepPsi z = (∫ x in (0:ℝ)..1, sepRho x) + (∫ x in (1:ℝ)..z, sepRho x) := by
    rw [sepPsi, ← intervalIntegral.integral_add_adjacent_intervals
      (sepRho_continuous.intervalIntegrable 0 1) (sepRho_continuous.intervalIntegrable 1 z)]
  have hz : (∫ x in (1:ℝ)..z, sepRho x) = 0 := by
    rw [← intervalIntegral.integral_zero (a := (1:ℝ)) (b := z)]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le h] at hy
    exact sepRho_eq_zero_of_one_le hy.1
  rw [hsplit, integral_sepRho_zero_one, hz, add_zero]

lemma sepPsi_eq_neg_half {z : ℝ} (h : z ≤ -1) : sepPsi z = -1/2 := by
  have hsym : (∫ x in (-1:ℝ)..0, sepRho x) = 1/2 := by
    have hadd : (∫ x in (-1:ℝ)..0, sepRho x) + (∫ x in (0:ℝ)..1, sepRho x)
        = ∫ x in (-1:ℝ)..1, sepRho x :=
      intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (sepRho_continuous.intervalIntegrable (-1) 0) (sepRho_continuous.intervalIntegrable 0 1)
    rw [show (∫ x in (-1:ℝ)..1, sepRho x) = 1 from integral_sepRho] at hadd
    linarith [integral_sepRho_zero_one]
  have hz : (∫ x in z..(-1), sepRho x) = 0 := by
    rw [← intervalIntegral.integral_zero (a := z) (b := (-1:ℝ))]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le h] at hy
    exact sepRho_eq_zero_of_le hy.2
  have hsplit : (∫ x in z..(-1), sepRho x) + (∫ x in (-1:ℝ)..0, sepRho x)
      = ∫ x in z..0, sepRho x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (sepRho_continuous.intervalIntegrable z (-1)) (sepRho_continuous.intervalIntegrable (-1) 0)
  have hmain : sepPsi z = - ∫ x in z..0, sepRho x := by
    have h := intervalIntegral.integral_symm (μ := volume) (a := z) (b := (0:ℝ)) (f := sepRho)
    rw [sepPsi]
    exact h
  rw [hmain, ← hsplit, hz, zero_add, hsym]
  norm_num

lemma sepPsi_neg (z : ℝ) : sepPsi (-z) = -sepPsi z := by
  have h2 : (∫ x in (-z)..0, sepRho x) = ∫ x in (0:ℝ)..z, sepRho x := by
    have h := intervalIntegral.integral_comp_neg (f := sepRho) (a := -z) (b := (0:ℝ))
    simp only [neg_zero, neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro y _
    exact (sepRho_even y).symm
  have h1 : sepPsi (-z) = - ∫ x in (-z)..0, sepRho x := by
    have h := intervalIntegral.integral_symm (μ := volume) (a := -z) (b := (0:ℝ)) (f := sepRho)
    rw [sepPsi]
    exact h
  rw [h1, h2, sepPsi]

lemma sepPsi_le_half (z : ℝ) : sepPsi z ≤ 1/2 := by
  rcases le_or_gt 1 z with h | h
  · rw [sepPsi_eq_half h]
  · have := sepPsi_monotone h.le
    rw [sepPsi_eq_half le_rfl] at this
    exact this

lemma neg_half_le_sepPsi (z : ℝ) : -1/2 ≤ sepPsi z := by
  rcases le_or_gt z (-1) with h | h
  · rw [sepPsi_eq_neg_half h]
  · have := sepPsi_monotone h.le
    rw [sepPsi_eq_neg_half le_rfl] at this
    exact this

lemma sepPsi_abs_le (z : ℝ) : |sepPsi z| ≤ 1/2 := by
  have h1 := neg_half_le_sepPsi z
  have h2 := sepPsi_le_half z
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## 2c. The `L¹` norm of `ρ'` -/

lemma deriv_sepRho_eq (y : ℝ) : deriv sepRho y =
    (8/15) * ((deriv Real.smoothTransition (8*(y+1)) * 8) * Real.smoothTransition (8*(1-y)))
      + (8/15) * (Real.smoothTransition (8*(y+1)) * (deriv Real.smoothTransition (8*(1-y)) * (-8))) :=
  (sepRho_hasDerivAt y).deriv

lemma abs_deriv_sepRho_le (y : ℝ) :
    |deriv sepRho y| ≤ (64/15) * (deriv Real.smoothTransition (8*y+8)
      + deriv Real.smoothTransition (8-8*y)) := by
  have key : deriv sepRho y =
      (8/15) * ((deriv Real.smoothTransition (8*y+8) * 8) * Real.smoothTransition (8-8*y))
        + (8/15) * (Real.smoothTransition (8*y+8)
          * (deriv Real.smoothTransition (8-8*y) * (-8))) := by
    have h := deriv_sepRho_eq y
    rw [show (8:ℝ)*(y+1) = 8*y+8 by ring, show (8:ℝ)*(1-y) = 8-8*y by ring] at h
    exact h
  rw [key]
  have h1 : 0 ≤ deriv Real.smoothTransition (8*y+8) := deriv_smoothTransition_nonneg _
  have h2 : 0 ≤ deriv Real.smoothTransition (8-8*y) := deriv_smoothTransition_nonneg _
  have h3 : Real.smoothTransition (8*y+8) ≤ 1 := Real.smoothTransition.le_one _
  have h4 : Real.smoothTransition (8-8*y) ≤ 1 := Real.smoothTransition.le_one _
  have h5 : 0 ≤ Real.smoothTransition (8*y+8) := Real.smoothTransition.nonneg _
  have h6 : 0 ≤ Real.smoothTransition (8-8*y) := Real.smoothTransition.nonneg _
  rw [abs_le]
  constructor <;> nlinarith [h1, h2, h3, h4, h5, h6]

lemma integral_abs_deriv_sepRho_le : ∫ y : ℝ, |deriv sepRho y| ≤ 16/15 := by
  have hint : Integrable (fun y : ℝ => (64/15) * (deriv Real.smoothTransition (8*y+8)
      + deriv Real.smoothTransition (8-8*y))) :=
    ((integrable_deriv_smoothTransition_comp 8).add
      (integrable_deriv_smoothTransition_comp8_neg 8)).const_mul _
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun y : ℝ => |deriv sepRho y|)
    (g := fun y : ℝ => (64/15) * (deriv Real.smoothTransition (8*y+8)
      + deriv Real.smoothTransition (8-8*y)))
    (by filter_upwards with y; exact abs_nonneg _) hint
    (by filter_upwards with y; exact abs_deriv_sepRho_le y)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add (integrable_deriv_smoothTransition_comp 8)
      (integrable_deriv_smoothTransition_comp8_neg 8),
    integral_deriv_smoothTransition_comp 8, integral_deriv_smoothTransition_comp8_neg 8]
  norm_num


end

end Work.FIArea7
