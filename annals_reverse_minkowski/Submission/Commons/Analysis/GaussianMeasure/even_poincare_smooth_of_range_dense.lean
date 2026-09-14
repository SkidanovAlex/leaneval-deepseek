import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.weighted_ibp_grad_inner
import Submission.Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex
import Submission.Commons.Analysis.GaussianMeasure.convex_sub_quadratic_lower_bound
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
import Submission.Commons.Analysis.InnerProductSpace.weighted_cauchy_schwarz

open MeasureTheory Real Filter
open scoped Real Topology

namespace Commons.Analysis.GaussianMeasure

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Helper lemmas (private) -/

/-- For an even convex function, the origin is a global minimum. -/
private lemma epr_even_convex_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hconv : ConvexOn ℝ Set.univ g) (he : ∀ x, g (-x) = g x) (x : E) :
    g 0 ≤ g x := by
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ (-x)) (by norm_num) (by norm_num)
    (by norm_num : ((1:ℝ)/2) + 1/2 = 1)
  have hx : ((1:ℝ)/2) • x + ((1:ℝ)/2) • (-x) = 0 := by module
  rw [hx, he x] at h
  simp only [smul_eq_mul] at h
  linarith

/-- `f - π‖·‖²` is convex and even, hence `π‖x‖² + f 0 ≤ f x`. -/
private lemma epr_pi_mul_norm_sq_add_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E → ℝ) (he : ∀ x, f (-x) = f x)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (x : E) :
    Real.pi * ‖x‖ ^ 2 + f 0 ≤ f x := by
  have hge : ∀ y : E, (fun y => f y - Real.pi * ‖y‖ ^ 2) (-y)
      = (fun y => f y - Real.pi * ‖y‖ ^ 2) y := by
    intro y; simp only [he y, norm_neg]
  have hmin := epr_even_convex_min hconv hge x
  simp only [norm_zero, pow_two, mul_zero, sub_zero] at hmin
  linarith

/-- From a pointwise bound on a linear functional, bound the operator norm. -/
private lemma epr_norm_fderiv_le_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (h : ∀ x v : E, |fderiv ℝ φ x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) (x : E) :
    ‖fderiv ℝ φ x‖ ≤ C * (1 + ‖x‖) ^ N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [Real.norm_eq_abs]
  exact h x v

/-- `2⟪a,b⟫ ≤ 4π‖a‖² + (1/(4π))‖b‖²`. -/
private lemma epr_two_mul_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) :
    2 * inner ℝ a b ≤ 4 * Real.pi * ‖a‖ ^ 2 + (1 / (4 * Real.pi)) * ‖b‖ ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hXY : 2 * (2 * Real.sqrt Real.pi * ‖a‖) * (‖b‖ / (2 * Real.sqrt Real.pi))
      = 2 * (‖a‖ * ‖b‖) := by
    field_simp
  have hX2 : (2 * Real.sqrt Real.pi * ‖a‖) ^ 2 = 4 * Real.pi * ‖a‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]; ring
  have hY2 : (‖b‖ / (2 * Real.sqrt Real.pi)) ^ 2 = (1 / (4 * Real.pi)) * ‖b‖ ^ 2 := by
    rw [div_pow, mul_pow, hs]
    field_simp
    ring
  have hmain := two_mul_le_add_sq (2 * Real.sqrt Real.pi * ‖a‖) (‖b‖ / (2 * Real.sqrt Real.pi))
  rw [hXY, hX2, hY2] at hmain
  have h1 : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
  linarith

/-- Polynomial growth of a real-valued function on a normed group. -/
private def PolyGrowth {E : Type*} [NormedAddCommGroup E] (Φ : E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : E, |Φ x| ≤ C * (1 + ‖x‖) ^ N

private lemma polyGrowth_const {E : Type*} [NormedAddCommGroup E] (c : ℝ) :
    PolyGrowth (fun _ : E => c) := by
  refine ⟨|c|, abs_nonneg c, 0, fun x => ?_⟩
  simp

private lemma polyGrowth_mul {E : Type*} [NormedAddCommGroup E] {Φ Ψ : E → ℝ}
    (hΦ : PolyGrowth Φ) (hΨ : PolyGrowth Ψ) :
    PolyGrowth (fun x => Φ x * Ψ x) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := hΦ
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := hΨ
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, N₁ + N₂, fun x => ?_⟩
  rw [abs_mul]
  calc |Φ x| * |Ψ x| ≤ (C₁ * (1 + ‖x‖) ^ N₁) * (C₂ * (1 + ‖x‖) ^ N₂) :=
        mul_le_mul (h₁ x) (h₂ x) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * (1 + ‖x‖) ^ (N₁ + N₂) := by rw [pow_add]; ring

private lemma polyGrowth_add {E : Type*} [NormedAddCommGroup E] {Φ Ψ : E → ℝ}
    (hΦ : PolyGrowth Φ) (hΨ : PolyGrowth Ψ) :
    PolyGrowth (fun x => Φ x + Ψ x) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := hΦ
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := hΨ
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max N₁ N₂, fun x => ?_⟩
  have hpow : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have hle1 : (1 + ‖x‖) ^ N₁ ≤ (1 + ‖x‖) ^ max N₁ N₂ :=
    pow_le_pow_right₀ hpow (le_max_left _ _)
  have hle2 : (1 + ‖x‖) ^ N₂ ≤ (1 + ‖x‖) ^ max N₁ N₂ :=
    pow_le_pow_right₀ hpow (le_max_right _ _)
  calc |Φ x + Ψ x| ≤ |Φ x| + |Ψ x| := abs_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ N₁ + C₂ * (1 + ‖x‖) ^ N₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ C₁ * (1 + ‖x‖) ^ max N₁ N₂ + C₂ * (1 + ‖x‖) ^ max N₁ N₂ :=
        add_le_add (mul_le_mul_of_nonneg_left hle1 hC₁) (mul_le_mul_of_nonneg_left hle2 hC₂)
    _ = (C₁ + C₂) * (1 + ‖x‖) ^ max N₁ N₂ := by ring

private lemma polyGrowth_neg {E : Type*} [NormedAddCommGroup E] {Φ : E → ℝ}
    (hΦ : PolyGrowth Φ) : PolyGrowth (fun x => -Φ x) := by
  obtain ⟨C, hC, N, h⟩ := hΦ
  exact ⟨C, hC, N, fun x => by rw [abs_neg]; exact h x⟩

private lemma polyGrowth_sub {E : Type*} [NormedAddCommGroup E] {Φ Ψ : E → ℝ}
    (hΦ : PolyGrowth Φ) (hΨ : PolyGrowth Ψ) :
    PolyGrowth (fun x => Φ x - Ψ x) := by
  have := polyGrowth_add hΦ (polyGrowth_neg hΨ)
  simpa [sub_eq_add_neg] using this

private lemma polyGrowth_sq {E : Type*} [NormedAddCommGroup E] {Φ : E → ℝ}
    (hΦ : PolyGrowth Φ) : PolyGrowth (fun x => Φ x ^ 2) := by
  have := polyGrowth_mul hΦ hΦ
  simpa [pow_two] using this

private lemma polyGrowth_norm_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v : E, |fderiv ℝ φ x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) :
    PolyGrowth (fun x : E => ‖fderiv ℝ φ x‖) :=
  ⟨C, hC, N, fun x => by
    have hx := epr_norm_fderiv_le_of_bound φ hC N h x
    simpa only [abs_of_nonneg (norm_nonneg (fderiv ℝ φ x))] using hx⟩

/-- Integrability of `Φ * exp (-f)` when `Φ` has polynomial growth. -/
private lemma epr_integrable_of_polyGrowth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f Φ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hΦc : Continuous Φ) (hΦ : PolyGrowth Φ) :
    Integrable (fun x : E => Φ x * Real.exp (-(f x))) := by
  obtain ⟨C, hC, N, hN⟩ := hΦ
  exact integrable_mul_exp_neg_stronglyConvex f Φ hf hconv hΦc C hC N hN

/-- Boundedness of a continuous compactly supported function. -/
private lemma epr_exists_normBound_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (hcs : HasCompactSupport φ) (hc : Continuous φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hcs.isCompact_range hc).exists_bound_of_continuousOn
    (continuousOn_id : ContinuousOn (fun y : F => y) (Set.range φ))
  exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC (φ x) ⟨x, rfl⟩) (le_max_left _ _)⟩

/-- A `C²` function with compact support has bounded value, gradient and second derivative. -/
private lemma epr_exists_polyGrad_bound_of_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x v w : E,
      |u x| ≤ C ∧ |fderiv ℝ u x v| ≤ C * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * ‖v‖ * ‖w‖ := by
  have hb0' := epr_exists_normBound_of_hasCompactSupport u hcs hu.continuous
  obtain ⟨C₀, hC₀, hb₀⟩ := hb0'
  have hb1' := epr_exists_normBound_of_hasCompactSupport (fderiv ℝ u) (hcs.fderiv ℝ)
    (hu.continuous_fderiv (by norm_num))
  obtain ⟨C₁, hC₁, hb₁⟩ := hb1'
  have hb2' := epr_exists_normBound_of_hasCompactSupport (fderiv ℝ (fderiv ℝ u))
    ((hcs.fderiv ℝ).fderiv ℝ)
    ((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp))
  obtain ⟨C₂, hC₂, hb₂⟩ := hb2'
  refine ⟨max (max C₀ C₁) C₂, by positivity, fun x v w => ⟨?_, ?_, ?_⟩⟩
  · have := hb₀ x
    have h1 : C₀ ≤ max (max C₀ C₁) C₂ := le_trans (le_max_left _ _) (le_max_left _ _)
    calc |u x| = ‖u x‖ := Real.norm_eq_abs _
      _ ≤ C₀ := this
      _ ≤ max (max C₀ C₁) C₂ := h1
  · have h1 : C₁ ≤ max (max C₀ C₁) C₂ := le_trans (le_max_right _ _) (le_max_left _ _)
    calc |fderiv ℝ u x v| = ‖fderiv ℝ u x v‖ := Real.norm_eq_abs _
      _ ≤ ‖fderiv ℝ u x‖ * ‖v‖ := (fderiv ℝ u x).le_opNorm v
      _ ≤ C₁ * ‖v‖ := mul_le_mul_of_nonneg_right (hb₁ x) (norm_nonneg v)
      _ ≤ max (max C₀ C₁) C₂ * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
  · have h1 : C₂ ≤ max (max C₀ C₁) C₂ := le_max_right _ _
    calc |fderiv ℝ (fderiv ℝ u) x v w| = ‖fderiv ℝ (fderiv ℝ u) x v w‖ := Real.norm_eq_abs _
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) x v‖ * ‖w‖ := (fderiv ℝ (fderiv ℝ u) x v).le_opNorm w
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) x‖ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) x).le_opNorm v) (norm_nonneg w)
      _ ≤ (C₂ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb₂ x) (norm_nonneg v))
              (norm_nonneg w)
      _ ≤ (max (max C₀ C₁) C₂ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg v))
              (norm_nonneg w)

/-- The doubled AM-GM inequality integrated against the weight `exp (-f)`. -/
private lemma epr_integral_amgm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} {a b : E → E}
    (hai : Integrable (fun x => ‖a x‖ ^ 2 * Real.exp (-(f x))))
    (hbi : Integrable (fun x => ‖b x‖ ^ 2 * Real.exp (-(f x))))
    (habi : Integrable (fun x => inner ℝ (a x) (b x) * Real.exp (-(f x)))) :
    2 * (∫ x, inner ℝ (a x) (b x) * Real.exp (-(f x)))
      ≤ 4 * Real.pi * (∫ x, ‖a x‖ ^ 2 * Real.exp (-(f x)))
        + (1 / (4 * Real.pi)) * (∫ x, ‖b x‖ ^ 2 * Real.exp (-(f x))) := by
  have hpt : ∀ x : E, 2 * inner ℝ (a x) (b x) * Real.exp (-(f x))
      ≤ (4 * Real.pi * ‖a x‖ ^ 2 + (1 / (4 * Real.pi)) * ‖b x‖ ^ 2) * Real.exp (-(f x)) :=
    fun x => mul_le_mul_of_nonneg_right (epr_two_mul_inner_le (a x) (b x)) (Real.exp_pos _).le
  have hL : Integrable (fun x : E => 2 * inner ℝ (a x) (b x) * Real.exp (-(f x))) :=
    habi.const_mul 2 |>.congr (Eventually.of_forall fun x => by ring)
  have hR : Integrable (fun x : E =>
      (4 * Real.pi * ‖a x‖ ^ 2 + (1 / (4 * Real.pi)) * ‖b x‖ ^ 2) * Real.exp (-(f x))) :=
    ((hai.const_mul (4 * Real.pi)).add (hbi.const_mul (1 / (4 * Real.pi)))).congr
      (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have hmono := integral_mono hL hR hpt
  have e1 : (∫ x, 2 * inner ℝ (a x) (b x) * Real.exp (-(f x)))
      = 2 * (∫ x, inner ℝ (a x) (b x) * Real.exp (-(f x))) := by
    rw [show (fun x : E => 2 * inner ℝ (a x) (b x) * Real.exp (-(f x)))
        = fun x => 2 * (inner ℝ (a x) (b x) * Real.exp (-(f x))) from by funext x; ring]
    rw [integral_const_mul]
  have e2 : (∫ x, (4 * Real.pi * ‖a x‖ ^ 2 + (1 / (4 * Real.pi)) * ‖b x‖ ^ 2) * Real.exp (-(f x)))
      = 4 * Real.pi * (∫ x, ‖a x‖ ^ 2 * Real.exp (-(f x)))
        + (1 / (4 * Real.pi)) * (∫ x, ‖b x‖ ^ 2 * Real.exp (-(f x))) := by
    rw [show (fun x : E =>
        (4 * Real.pi * ‖a x‖ ^ 2 + (1 / (4 * Real.pi)) * ‖b x‖ ^ 2) * Real.exp (-(f x)))
        = fun x => 4 * Real.pi * (‖a x‖ ^ 2 * Real.exp (-(f x)))
            + (1 / (4 * Real.pi)) * (‖b x‖ ^ 2 * Real.exp (-(f x))) from by funext x; ring]
    rw [integral_add (hai.const_mul _) (hbi.const_mul _), integral_const_mul, integral_const_mul]
  rw [e1, e2] at hmono
  exact hmono

/-- Expansion of the weighted second moment of `g - h`. -/
private lemma epr_integral_sq_sub_decomp {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (g h w : E → ℝ)
    (hgi : Integrable (fun x => g x ^ 2 * w x) μ)
    (hhi : Integrable (fun x => h x ^ 2 * w x) μ)
    (hghi : Integrable (fun x => g x * h x * w x) μ) :
    (∫ x, (g x - h x) ^ 2 * w x ∂μ)
      = (∫ x, g x ^ 2 * w x ∂μ) - 2 * (∫ x, g x * h x * w x ∂μ)
        + (∫ x, h x ^ 2 * w x ∂μ) := by
  have hI1 : Integrable (fun x => g x ^ 2 * w x - 2 * (g x * h x * w x)) μ :=
    hgi.sub (hghi.const_mul 2)
  rw [show (fun x => (g x - h x) ^ 2 * w x)
      = fun x => (g x ^ 2 * w x - 2 * (g x * h x * w x)) + h x ^ 2 * w x from by
        funext x; ring]
  rw [integral_add hI1 hhi, integral_sub hgi (hghi.const_mul 2), integral_const_mul]

/-- The Laplacian is the sum of the diagonal second derivatives along an orthonormal basis. -/
private lemma epr_laplacian_eq_sum_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) :
    Laplacian.laplacian u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (b i) (b i) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b u x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- **Even Poincaré inequality for a whole-space strongly log-concave even measure, from
range density and the creation energy bound.** -/
theorem even_poincare_smooth_of_range_dense {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] (f h : E → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (heven : ∀ x : E, f (-x) = f x)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hh : ContDiff ℝ 1 h) (hheven : ∀ x : E, h (-x) = h x)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖)
    (hrange : ∀ ε : ℝ, 0 < ε → ∃ u : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∫ x, ((- Laplacian.laplacian u x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) - h x) ^ 2
          * Real.exp (-(f x))) ≤ ε)
    (henergy : ∀ u : E → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) →
      (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
        |u x| ≤ C * (1 + ‖x‖) ^ N ∧
        |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
        |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) →
      4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        ≤ (∫ x, (- Laplacian.laplacian u x
              + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2
            * Real.exp (-(f x)))) :
    (∫ x, h x ^ 2 * Real.exp (-(f x)))
        - (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x)))
      ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hhf_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hh_cont : Continuous h := hh.continuous
  have hhd_cont : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  obtain ⟨Cf, hCf, Nf, hgfN⟩ := hgf
  have hghCopy := hgh
  obtain ⟨Ch0, hCh0, Nh0, hghN⟩ := hghCopy
  have hgf1 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ :=
    ⟨Cf, hCf, Nf, fun x v => (hgfN x v).1⟩
  have hdec : ∃ c : ℝ, ∀ x : E, c + Real.pi * ‖x‖ ^ 2 ≤ f x :=
    ⟨f 0, fun x => by
      have := epr_pi_mul_norm_sq_add_le f heven hconv x
      linarith⟩
  have hh_poly : PolyGrowth (fun x : E => h x) := ⟨Ch0, hCh0, Nh0, fun x => (hghN x 0).1⟩
  have hf_norm_poly : PolyGrowth (fun x : E => ‖fderiv ℝ f x‖) :=
    polyGrowth_norm_fderiv hCf (fun x v => (hgfN x v).1)
  have hh_norm_poly : PolyGrowth (fun x : E => ‖fderiv ℝ h x‖) :=
    polyGrowth_norm_fderiv hCh0 (fun x v => (hghN x v).2)
  have hh2_int : Integrable (fun x : E => h x ^ 2 * Real.exp (-(f x))) :=
    epr_integrable_of_polyGrowth f (fun x => h x ^ 2) hf hconv (hh_cont.pow 2)
      (polyGrowth_sq hh_poly)
  have hCh_int : Integrable (fun x : E => ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) :=
    epr_integrable_of_polyGrowth f (fun x => ‖fderiv ℝ h x‖ ^ 2) hf hconv
      ((hhd_cont.norm).pow 2) (polyGrowth_sq hh_norm_poly)
  have hAC : (∫ x, h x ^ 2 * Real.exp (-(f x)))
      ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨u, hu_top, hucs, hueven, hru⟩ := hrange ε hε
    have hu2 : ContDiff ℝ 2 u := hu_top.of_le (WithTop.coe_le_coe.mpr le_top)
    have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
    have hud_cont : Continuous (fderiv ℝ u) := hu1.continuous_fderiv (by norm_num)
    have hud2_cont : Continuous (fderiv ℝ (fderiv ℝ u)) :=
      (hu2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)
    set g : E → ℝ := fun x => - Laplacian.laplacian u x
        + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) with hgdef
    have hu_bnd' := epr_exists_polyGrad_bound_of_hasCompactSupport u hu2 hucs
    obtain ⟨Cu, hCu, hu_bnd⟩ := hu_bnd'
    have hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w : E,
        |u x| ≤ C * (1 + ‖x‖) ^ N ∧
        |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
        |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ := by
      refine ⟨Cu, hCu, 0, fun x v w => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hu_bnd x v w
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
    have hgu_hen : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
        |u x| ≤ C * (1 + ‖x‖) ^ N ∧
        |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
        |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
      obtain ⟨C, hC, N, hN⟩ := hgu
      refine ⟨C, hC, N, fun x v => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hN x v v
      exact ⟨h1, h2, by simpa [pow_two, mul_assoc] using h3⟩
    have hu_norm_poly : PolyGrowth (fun x : E => ‖fderiv ℝ u x‖) :=
      polyGrowth_norm_fderiv (N := 0) hCu (fun x v => by
        simpa using (hu_bnd x v v).2.1)
    have hBu_int : Integrable (fun x : E => ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) :=
      epr_integrable_of_polyGrowth f (fun x => ‖fderiv ℝ u x‖ ^ 2) hf hconv
        ((hud_cont.norm).pow 2) (polyGrowth_sq hu_norm_poly)
    have htoDualu_cont : Continuous (fun x : E =>
        (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp hud_cont
    have htoDualf_cont : Continuous (fun x : E =>
        (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp hhf_cont
    have htoDualh_cont : Continuous (fun x : E =>
        (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp hhd_cont
    have hinner1_cont : Continuous (fun x : E =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) :=
      htoDualf_cont.inner htoDualu_cont
    have hinner2_cont : Continuous (fun x : E =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))) :=
      htoDualu_cont.inner htoDualh_cont
    set b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hbdef
    have hΔcont : Continuous (fun x : E => Laplacian.laplacian u x) := by
      have hkey : (fun x : E => Laplacian.laplacian u x)
          = fun x => ∑ i : Fin (Module.finrank ℝ E), fderiv ℝ (fderiv ℝ u) x (b i) (b i) :=
        funext fun x => epr_laplacian_eq_sum_fderiv b u x
      rw [hkey]
      refine continuous_finsetSum _ fun i _ => ?_
      exact (hud2_cont.clm_apply continuous_const).clm_apply continuous_const
    have hg_cont : Continuous g := by
      rw [hgdef]
      exact hΔcont.neg.add hinner1_cont
    have hΔpoly : PolyGrowth (fun x : E => Laplacian.laplacian u x) := by
      refine ⟨(Module.finrank ℝ E : ℝ) * Cu, by positivity, 0, fun x => ?_⟩
      change |Laplacian.laplacian u x| ≤ ((Module.finrank ℝ E : ℝ) * Cu) * (1 + ‖x‖) ^ 0
      rw [epr_laplacian_eq_sum_fderiv b u x]
      calc |∑ i : Fin (Module.finrank ℝ E), fderiv ℝ (fderiv ℝ u) x (b i) (b i)|
          ≤ ∑ i : Fin (Module.finrank ℝ E), |fderiv ℝ (fderiv ℝ u) x (b i) (b i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (Module.finrank ℝ E), Cu := Finset.sum_le_sum fun i _ => by
              have h := (hu_bnd x (b i) (b i)).2.2
              rw [b.norm_eq_one i, mul_one, mul_one] at h
              exact h
        _ = (Module.finrank ℝ E : ℝ) * Cu := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ((Module.finrank ℝ E : ℝ) * Cu) * (1 + ‖x‖) ^ 0 := by ring
    have hinner1_poly : PolyGrowth (fun x : E =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) := by
      obtain ⟨C, hC, N, hN⟩ := polyGrowth_mul hf_norm_poly hu_norm_poly
      refine ⟨C, hC, N, fun x => ?_⟩
      have habs : |inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))|
          ≤ ‖fderiv ℝ f x‖ * ‖fderiv ℝ u x‖ := by
        have h := abs_real_inner_le_norm ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
        simpa only [LinearIsometryEquiv.norm_map] using h
      calc |inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))|
            ≤ ‖fderiv ℝ f x‖ * ‖fderiv ℝ u x‖ := habs
        _ = |‖fderiv ℝ f x‖ * ‖fderiv ℝ u x‖| :=
              (abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).symm
        _ ≤ C * (1 + ‖x‖) ^ N := hN x
    have hinner2_poly : PolyGrowth (fun x : E =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))) := by
      obtain ⟨C, hC, N, hN⟩ := polyGrowth_mul hu_norm_poly hh_norm_poly
      refine ⟨C, hC, N, fun x => ?_⟩
      have habs : |inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))|
          ≤ ‖fderiv ℝ u x‖ * ‖fderiv ℝ h x‖ := by
        have h := abs_real_inner_le_norm ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))
        simpa only [LinearIsometryEquiv.norm_map] using h
      calc |inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))|
            ≤ ‖fderiv ℝ u x‖ * ‖fderiv ℝ h x‖ := habs
        _ = |‖fderiv ℝ u x‖ * ‖fderiv ℝ h x‖| :=
              (abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).symm
        _ ≤ C * (1 + ‖x‖) ^ N := hN x
    have hg_poly : PolyGrowth g := by
      rw [hgdef]
      exact polyGrowth_add (polyGrowth_neg hΔpoly) hinner1_poly
    have hAg_int : Integrable (fun x : E => g x ^ 2 * Real.exp (-(f x))) :=
      epr_integrable_of_polyGrowth f (fun x => g x ^ 2) hf hconv (hg_cont.pow 2)
        (polyGrowth_sq hg_poly)
    have hgh_int : Integrable (fun x : E => g x * h x * Real.exp (-(f x))) :=
      epr_integrable_of_polyGrowth f (fun x => g x * h x) hf hconv (hg_cont.mul hh_cont)
        (polyGrowth_mul hg_poly hh_poly)
    have hinner2_int : Integrable (fun x : E =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) * Real.exp (-(f x))) :=
      epr_integrable_of_polyGrowth f (fun x =>
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))) hf hconv hinner2_cont hinner2_poly
    have hstep0 : 2 * (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) * Real.exp (-(f x)))
        ≤ 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
          + (1 / (4 * Real.pi)) * (∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
      have hai : Integrable (fun x : E =>
          ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)‖ ^ 2 * Real.exp (-(f x))) :=
        hBu_int.congr (Eventually.of_forall fun x => by
          simp only [LinearIsometryEquiv.norm_map])
      have hbi : Integrable (fun x : E =>
          ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)‖ ^ 2 * Real.exp (-(f x))) :=
        hCh_int.congr (Eventually.of_forall fun x => by
          simp only [LinearIsometryEquiv.norm_map])
      have h0 := epr_integral_amgm_le (f := f)
        (a := fun x : E => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
        (b := fun x : E => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x))
        hai hbi hinner2_int
      rwa [show (∫ x, ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)‖ ^ 2 * Real.exp (-(f x)))
            = ∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)) from
          integral_congr_ae (Eventually.of_forall fun x => by
            simp only [LinearIsometryEquiv.norm_map]),
        show (∫ x, ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)‖ ^ 2 * Real.exp (-(f x)))
            = ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) from
          integral_congr_ae (Eventually.of_forall fun x => by
            simp only [LinearIsometryEquiv.norm_map])] at h0
    have hstep : 2 * (∫ x, g x * h x * Real.exp (-(f x)))
        ≤ (∫ x, g x ^ 2 * Real.exp (-(f x)))
          + (1 / (4 * Real.pi)) * (∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) := by
      have hen : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
          ≤ ∫ x, g x ^ 2 * Real.exp (-(f x)) := by
        have h0 := henergy u hu2 hueven hgu_hen
        simpa only [hgdef] using h0
      have hIBP' : (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x)) * Real.exp (-(f x)))
          = ∫ x, g x * h x * Real.exp (-(f x)) := by
        have h0 := weighted_ibp_grad_inner f u h hf1 hu2 hh hdec hgf1 hgu hgh
        simpa only [hgdef] using h0
      rw [hIBP'] at hstep0
      linarith [hstep0, hen]
    have herr : ∫ x, (g x - h x) ^ 2 * Real.exp (-(f x)) ≤ ε := by
      simpa only [hgdef] using hru
    have hdecomp : ∫ x, (g x - h x) ^ 2 * Real.exp (-(f x))
        = (∫ x, g x ^ 2 * Real.exp (-(f x)))
          - 2 * (∫ x, g x * h x * Real.exp (-(f x)))
          + (∫ x, h x ^ 2 * Real.exp (-(f x))) :=
      epr_integral_sq_sub_decomp volume g h (fun x => Real.exp (-(f x))) hAg_int hh2_int hgh_int
    have hkey : (∫ x, h x ^ 2 * Real.exp (-(f x)))
        ≤ (1 / (4 * Real.pi)) * (∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))) + ε := by
      have h1 : (∫ x, h x ^ 2 * Real.exp (-(f x)))
          = (∫ x, (g x - h x) ^ 2 * Real.exp (-(f x)))
            - (∫ x, g x ^ 2 * Real.exp (-(f x)))
            + 2 * (∫ x, g x * h x * Real.exp (-(f x))) := by
        linarith [hdecomp]
      rw [h1]
      linarith [herr, hstep]
    exact hkey
  have hZnn : 0 ≤ ∫ x : E, Real.exp (-(f x)) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have hsqnn : 0 ≤ (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x))) :=
    div_nonneg (sq_nonneg _) hZnn
  calc (∫ x, h x ^ 2 * Real.exp (-(f x)))
        - (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x)))
      ≤ ∫ x, h x ^ 2 * Real.exp (-(f x)) := sub_le_self _ hsqnn
    _ ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := hAC

end

end Commons.Analysis.GaussianMeasure
