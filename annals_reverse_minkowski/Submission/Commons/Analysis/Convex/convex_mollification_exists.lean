import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv

open MeasureTheory Filter Set
open scoped Topology ContDiff Convolution

namespace Commons.Analysis.Convex

noncomputable section

/-- The bump functions used for the mollification; their outer radii tend to `0`. -/
def ccBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1),
    by positivity,
    by
      have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff_of_pos_right h]; norm_num⟩

lemma ccBump_rOut_tendsto : Tendsto (fun n => (ccBump n).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have := h.const_div_atTop 2
  simpa [ccBump] using this

/-- Integrability of `t ↦ ρ t * f (g t)` for `ρ` continuous with compact support and `f`, `g`
continuous. -/
lemma integrable_bump_comp (ρ : ℝ → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (f : ℝ → ℝ) (hf : Continuous f) (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun t => ρ t * f (g t)) volume := by
  have hcont : Continuous fun t : ℝ => ρ t * f (g t) := hρc.mul (hf.comp hg)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine hρs.of_isClosed_subset (isClosed_tsupport (fun t => ρ t * f (g t))) (closure_mono ?_)
  intro t ht
  simp only [Function.mem_support] at ht ⊢
  intro h0
  exact ht (by rw [h0, zero_mul])

/-- For an even weight `ρ`, `∫ t, ρ t * f (c - t) = ∫ t, ρ t * f (c + t)`. -/
lemma integral_even_shift (ρ : ℝ → ℝ) (heven : ∀ t, ρ (-t) = ρ t) (f : ℝ → ℝ) (c : ℝ) :
    ∫ t, ρ t * f (c - t) = ∫ t, ρ t * f (c + t) := by
  have h := integral_neg_eq_self (fun t : ℝ => ρ t * f (c - t)) volume
  simp only [sub_neg_eq_add] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with t
  rw [heven]

/-- The weighted average `y ↦ ∫ t, ρ t * f (y - t)` of a convex function is convex. -/
lemma convexOn_integral_shift (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) (hfc : Continuous f)
    (ρ : ℝ → ℝ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) :
    ConvexOn ℝ univ (fun y => ∫ t, ρ t * f (y - t)) := by
  have hint : ∀ c : ℝ, Integrable (fun t => ρ t * f (c - t)) volume := fun c =>
    integrable_bump_comp ρ hρc hρs f hfc (fun t => c - t) (continuous_const.sub continuous_id)
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hix := hint x
  have hiy := hint y
  have hixy := hint (a * x + b * y)
  have heq : ∫ t, (a * (ρ t * f (x - t)) + b * (ρ t * f (y - t)))
      = a * (∫ t, ρ t * f (x - t)) + b * (∫ t, ρ t * f (y - t)) := by
    rw [integral_add (hix.const_mul a) (hiy.const_mul b), integral_const_mul, integral_const_mul]
  have hle : ∀ t, ρ t * f (a * x + b * y - t) ≤ a * (ρ t * f (x - t)) + b * (ρ t * f (y - t)) := by
    intro t
    have hconv : f (a * x + b * y - t) ≤ a * f (x - t) + b * f (y - t) := by
      have h := hf.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
      simp only [smul_eq_mul] at h
      have harith : a * (x - t) + b * (y - t) = a * x + b * y - t := by
        linear_combination (-t) * hab
      rwa [harith] at h
    calc ρ t * f (a * x + b * y - t)
        ≤ ρ t * (a * f (x - t) + b * f (y - t)) := mul_le_mul_of_nonneg_left hconv (hρ0 t)
      _ = a * (ρ t * f (x - t)) + b * (ρ t * f (y - t)) := by ring
  calc ∫ t, ρ t * f (a * x + b * y - t)
      ≤ ∫ t, (a * (ρ t * f (x - t)) + b * (ρ t * f (y - t))) :=
        integral_mono hixy (hix.const_mul a |>.add (hiy.const_mul b)) hle
    _ = a * (∫ t, ρ t * f (x - t)) + b * (∫ t, ρ t * f (y - t)) := heq

/-- Jensen-type inequality for a symmetric normalized mollifier applied to a convex function. -/
lemma le_integral_shift (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) (hfc : Continuous f)
    (ρ : ℝ → ℝ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (heven : ∀ t, ρ (-t) = ρ t) (hint : ∫ t, ρ t = 1) (x : ℝ) :
    f x ≤ ∫ t, ρ t * f (x - t) := by
  have h1 : Integrable (fun t => ρ t * f (x - t)) volume :=
    integrable_bump_comp ρ hρc hρs f hfc (fun t => x - t) (continuous_const.sub continuous_id)
  have h2 : Integrable (fun t => ρ t * f (x + t)) volume :=
    integrable_bump_comp ρ hρc hρs f hfc (fun t => x + t) (continuous_const.add continuous_id)
  have hL : Integrable (fun t => ρ t * f x) volume :=
    (integrable_bump_comp ρ hρc hρs (fun _ => f x) continuous_const (fun _ => (0:ℝ)) continuous_const)
  have hR : Integrable (fun t => ρ t * ((f (x - t) + f (x + t)) / 2)) volume := by
    have h := (h1.const_mul (1/2)).add (h2.const_mul (1/2))
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  have hshift : ∫ t, ρ t * f (x - t) = ∫ t, ρ t * f (x + t) :=
    integral_even_shift ρ heven f x
  have hle : ∀ t, ρ t * f x ≤ ρ t * ((f (x - t) + f (x + t)) / 2) := by
    intro t
    refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
    have h := hf.2 (mem_univ (x - t)) (mem_univ (x + t))
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at h
    have harith : (1/2) * (x - t) + (1/2) * (x + t) = x := by ring
    rw [harith] at h
    linarith
  have hmono := integral_mono hL hR hle
  have hLeq : ∫ t, ρ t * f x = f x := by
    rw [show (fun t => ρ t * f x) = fun t => f x * ρ t by funext t; ring, integral_const_mul,
      hint, mul_one]
  have hReq : ∫ t, ρ t * ((f (x - t) + f (x + t)) / 2) = ∫ t, ρ t * f (x - t) := by
    rw [show (fun t => ρ t * ((f (x - t) + f (x + t)) / 2))
        = fun t => (1/2) * (ρ t * f (x - t)) + (1/2) * (ρ t * f (x + t)) by
      funext t; ring]
    rw [integral_add (h1.const_mul (1/2)) (h2.const_mul (1/2)), integral_const_mul,
      integral_const_mul, ← hshift]
    ring
  rw [hLeq, hReq] at hmono
  exact hmono

/-- The potential `U = V - π x²`. -/
def ccU (V : ℝ → ℝ) : ℝ → ℝ := fun x => V x - Real.pi * x ^ 2

/-- The mollification of `f` by the `n`-th bump, written as an integral. -/
def ccMoll (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun y => ∫ t, (ccBump n).normed volume t * f (y - t)

lemma ccMoll_eq_convolution (f : ℝ → ℝ) (n : ℕ) :
    ccMoll f n = ((ccBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext y
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, ccMoll]

lemma ccMoll_contDiff (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ ∞ (ccMoll f n) := by
  rw [ccMoll_eq_convolution]
  have hc := (ccBump n).hasCompactSupport_normed (μ := volume)
  have hd := (ccBump n).contDiff_normed (μ := volume) (n := ⊤)
  exact hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hd hf

lemma ccMoll_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) (hfc : Continuous f) (n : ℕ) :
    ConvexOn ℝ univ (ccMoll f n) :=
  convexOn_integral_shift f hf hfc (fun t => (ccBump n).normed volume t)
    (fun t => (ccBump n).nonneg_normed t) (ccBump n).continuous_normed
    (ccBump n).hasCompactSupport_normed

lemma ccMoll_ge (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) (hfc : Continuous f) (n : ℕ) (x : ℝ) :
    f x ≤ ccMoll f n x :=
  le_integral_shift f hf hfc (fun t => (ccBump n).normed volume t)
    (fun t => (ccBump n).nonneg_normed t) (ccBump n).continuous_normed
    (ccBump n).hasCompactSupport_normed (fun t => (ccBump n).normed_neg t)
    (ccBump n).integral_normed x

lemma ccMoll_tendsto (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    Tendsto (fun n => ccMoll f n x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) ccBump_rOut_tendsto hf x
  simpa only [ccMoll_eq_convolution] using h

/-- **Mollification of a strongly convex potential.**
For a convex `V : ℝ → ℝ` with `x ↦ V x - π x²` also convex, there is a sequence of smooth
convex potentials `Vε n` which dominate `V` from above, whose second derivatives are at least
`2π`, and which converge to `V` pointwise. -/
theorem convex_mollification_exists (V : ℝ → ℝ) (hV : ConvexOn ℝ Set.univ V)
    (hV2 : ConvexOn ℝ Set.univ (fun x => V x - Real.pi * x ^ 2)) :
    ∃ (Vε : ℕ → ℝ → ℝ) (Vε' Vε'' : ℕ → ℝ → ℝ),
      (∀ n x, HasDerivAt (Vε n) (Vε' n x) x) ∧
      (∀ n x, HasDerivAt (Vε' n) (Vε'' n x) x) ∧
      (∀ n, ContinuousOn (Vε'' n) Set.univ) ∧
      (∀ n x, 2 * Real.pi ≤ Vε'' n x) ∧
      (∀ n, ConvexOn ℝ Set.univ (Vε n)) ∧
      (∀ n x, V x ≤ Vε n x) ∧
      (∀ x, Filter.Tendsto (fun n => Vε n x) Filter.atTop (nhds (V x))) := by
  have hUconv : ConvexOn ℝ univ (ccU V) := hV2
  have hUcont : Continuous (ccU V) :=
    continuousOn_univ.mp (hUconv.continuousOn isOpen_univ)
  have hUli : LocallyIntegrable (ccU V) volume := hUcont.locallyIntegrable
  have hCd : ∀ n, ContDiff ℝ ∞ (ccMoll (ccU V) n) := fun n => ccMoll_contDiff (ccU V) hUli n
  have hdiff : ∀ n x, DifferentiableAt ℝ (ccMoll (ccU V) n) x := fun n x =>
    (hCd n).differentiable (by simp) |>.differentiableAt
  have hdiff' : ∀ n x, DifferentiableAt ℝ (deriv (ccMoll (ccU V) n)) x := by
    intro n x
    have hd : Differentiable ℝ (iteratedDeriv 1 (ccMoll (ccU V) n)) :=
      (hCd n).differentiable_iteratedDeriv 1 (WithTop.coe_lt_coe.mpr (by norm_num))
    rw [iteratedDeriv_one] at hd
    exact hd.differentiableAt
  refine ⟨fun n => (fun x => ccMoll (ccU V) n x + Real.pi * x ^ 2),
      (fun n => (fun x => deriv (ccMoll (ccU V) n) x + 2 * Real.pi * x)),
      (fun n => (fun x => deriv (deriv (ccMoll (ccU V) n)) x + 2 * Real.pi)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    have h1 : HasDerivAt (ccMoll (ccU V) n) (deriv (ccMoll (ccU V) n) x) x :=
      (hdiff n x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2) (2 * Real.pi * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul Real.pi
      convert h using 1 <;> first | rfl | (norm_num; ring)
    have h3 := h1.add h2
    convert h3 using 1 <;> rfl
  · intro n x
    have h1 : HasDerivAt (deriv (ccMoll (ccU V) n)) (deriv (deriv (ccMoll (ccU V) n)) x) x :=
      (hdiff' n x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
      have h := (hasDerivAt_id x).const_mul (2 * Real.pi)
      convert h using 1 <;> first | rfl | ring
    have h3 := h1.add h2
    convert h3 using 1 <;> rfl
  · intro n
    have hcont : Continuous (iteratedDeriv 2 (ccMoll (ccU V) n)) :=
      (hCd n).continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)
    have h2 : iteratedDeriv 2 (ccMoll (ccU V) n) = deriv (deriv (ccMoll (ccU V) n)) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2] at hcont
    have h3 : Continuous (fun x => deriv (deriv (ccMoll (ccU V) n)) x + 2 * Real.pi) :=
      hcont.add continuous_const
    exact h3.continuousOn
  · intro n x
    have hconv : ConvexOn ℝ univ (ccMoll (ccU V) n) := ccMoll_convex (ccU V) hUconv hUcont n
    have hmono : Monotone (deriv (ccMoll (ccU V) n)) :=
      fun a b hab => (hconv.monotoneOn_deriv (fun x _ => hdiff n x)) (mem_univ a) (mem_univ b) hab
    have hnn : 0 ≤ deriv (deriv (ccMoll (ccU V) n)) x := hmono.deriv_nonneg (x := x)
    simp only
    linarith
  · intro n
    have hconv : ConvexOn ℝ univ (ccMoll (ccU V) n) := ccMoll_convex (ccU V) hUconv hUcont n
    have hsq : ConvexOn ℝ univ (fun x : ℝ => Real.pi * x ^ 2) := by
      have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul (Real.pi_pos.le)
      simpa only [smul_eq_mul] using h
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    have h1 := hconv.2 (mem_univ x) (mem_univ y) ha hb hab
    have h2 := hsq.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h1 h2
    nlinarith [h1, h2]
  · intro n x
    have hJ := ccMoll_ge (ccU V) hUconv hUcont n x
    simp only [ccU] at hJ
    simp only
    linarith
  · intro x
    have htend := ccMoll_tendsto (ccU V) hUcont x
    have h2 := htend.add_const (Real.pi * x ^ 2)
    have hval : ccU V x + Real.pi * x ^ 2 = V x := by simp only [ccU]; ring
    rw [hval] at h2
    simpa only [Pi.add_apply] using h2

end

end Commons.Analysis.Convex