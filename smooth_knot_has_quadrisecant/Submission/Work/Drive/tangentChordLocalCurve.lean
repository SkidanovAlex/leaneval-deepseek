import Mathlib
import ChallengeDeps
import Submission.CollinearityMap
import Submission.Work.Drive.tangentChordLocalInterface
import Submission.Work.Drive.genericFullDefs
import Submission.Commons.Analysis.CrossProduct.inner_cross3_self_left
import Submission.Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top
import Submission.Commons.Analysis.Normed.isInvertible_of_det_columns
import Submission.Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent
import Submission.Commons.LinearAlgebra.Span.span_top_of_three_independent
import Submission.Commons.Analysis.CrossProduct.cross3_contDiff
import Submission.Commons.Analysis.CrossProduct.hasDerivAt_cross3
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open MeasureTheory Filter
open scoped Topology

noncomputable section

/-! ## 1. The average velocity and its strict derivative at the diagonal -/

/-- The affine parameter of the point at time `t` on the segment from `q.1` to `q.2`. -/
def seg (q : ℝ × ℝ) (t : ℝ) : ℝ := q.1 + t * (q.2 - q.1)

/-- The average velocity of `r` over the segment from `x` to `m`. -/
def avgVel (r : ℝ → Space) (x m : ℝ) : Space :=
  ∫ t in (0 : ℝ)..1, deriv r (x + t * (m - x))

/-- The average velocity as a function of the pair of parameters. -/
def avgVelP (r : ℝ → Space) (q : ℝ × ℝ) : Space :=
  ∫ t in (0 : ℝ)..1, deriv r (seg q t)

/-- The representative of the strict derivative of `avgVelP` at a diagonal point. -/
def avgVelLin (cc : Space) : (ℝ × ℝ) →L[ℝ] Space :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight cc

lemma avgVelLin_apply (cc : Space) (q : ℝ × ℝ) :
    avgVelLin cc q = ((q.1 + q.2) / 2) • cc := by
  have h2 : (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) q = q.1 + q.2 := by
    simp only [ContinuousLinearMap.add_apply]
    rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) q = q.1 from rfl,
      show (ContinuousLinearMap.snd ℝ ℝ ℝ) q = q.2 from rfl]
  rw [avgVelLin, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, h2,
    smul_smul]
  congr 1
  ring

lemma avgVelP_apply (r : ℝ → Space) (q : ℝ × ℝ) :
    avgVelP r q = ∫ t in (0 : ℝ)..1, deriv r (seg q t) := rfl

lemma continuous_seg (q : ℝ × ℝ) : Continuous (seg q) := by
  unfold seg; fun_prop

/-- `∫₀¹ (x + t(m-x)) dt = (x+m)/2`. -/
lemma integral_affine (x m : ℝ) :
    (∫ t in (0 : ℝ)..1, (x + t * (m - x))) = (x + m) / 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => x * s + (m - x) * s ^ 2 / 2) (x + t * (m - x)) t := by
    intro t ht
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun s : ℝ => (m - x) * s ^ 2 / 2) ((m - x) * (2 * t) / 2) t :=
      (hsq.const_mul (m - x)).div_const 2
    have h1 : HasDerivAt (fun s : ℝ => x * s) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have hsum := h1.add h2
    have hval : x + (m - x) * (2 * t) / 2 = x + t * (m - x) := by ring
    rw [hval] at hsum
    exact hsum
  have hint : IntervalIntegrable (fun t : ℝ => x + t * (m - x)) volume 0 1 :=
    (continuous_const.add (continuous_id.mul continuous_const)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  ring

/-- The integral of the affine parameter `seg`. -/
lemma integral_seg (q : ℝ × ℝ) :
    (∫ t in (0 : ℝ)..1, seg q t) = (q.1 + q.2) / 2 := by
  simpa [seg] using integral_affine q.1 q.2

/-- The integral of the difference of the two affine parameters. -/
lemma integral_seg_sub (q₁ q₂ : ℝ × ℝ) :
    (∫ t in (0 : ℝ)..1, (seg q₁ t - seg q₂ t)) = ((q₁ - q₂).1 + (q₁ - q₂).2) / 2 := by
  have h1 : IntervalIntegrable (seg q₁) volume (0 : ℝ) 1 :=
    (continuous_seg q₁).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (seg q₂) volume (0 : ℝ) 1 :=
    (continuous_seg q₂).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub h1 h2, integral_seg, integral_seg]
  rw [show (q₁ - q₂).1 = q₁.1 - q₂.1 from rfl, show (q₁ - q₂).2 = q₁.2 - q₂.2 from rfl]
  ring

/-- Uniform two-point estimate for a `C¹` function: the derivative at `a` controls all pairs
of points near `a`. -/
lemma exists_strict_bound {v : ℝ → Space} (hv : ContDiff ℝ 1 v) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y y' : ℝ, |y - a| < δ → |y' - a| < δ →
      ‖v y - v y' - (fderiv ℝ v a) (y - y')‖ ≤ c * ‖y - y'‖ := by
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hcAt : ContinuousAt (fderiv ℝ v) a := hcont.continuousAt
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := (Metric.continuousAt_iff.mp hcAt) c hc
  refine ⟨δ₀, hδ₀, fun y y' hy hy' => ?_⟩
  have hbound : ∀ z ∈ Metric.ball a δ₀, ‖fderiv ℝ v z - fderiv ℝ v a‖ ≤ c := by
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have h := hδ₀' (x := z) hz
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hyb : y ∈ Metric.ball a δ₀ := by rw [Metric.mem_ball, Real.dist_eq]; exact hy
  have hyb' : y' ∈ Metric.ball a δ₀ := by rw [Metric.mem_ball, Real.dist_eq]; exact hy'
  exact Convex.norm_image_sub_le_of_norm_fderiv_le' (f := v) (s := Metric.ball a δ₀)
    (φ := fderiv ℝ v a) (C := c)
    (fun z _ => (hv.differentiable (by norm_num)) z) hbound (convex_ball a δ₀) hyb' hyb

/-- **The average velocity is strictly differentiable at the diagonal.**  The strict derivative
of `(x,m) ↦ ∫₀¹ r'(x + t(m-x)) dt` at `(a,a)` is
`(dx,dm) ↦ ((dx+dm)/2) • r''(a)`. -/
lemma avgVelP_hasStrictFDerivAt {r : ℝ → Space} (hr : ContDiff ℝ 2 r) (a : ℝ) :
    HasStrictFDerivAt (avgVelP r) (avgVelLin (deriv (deriv r) a)) (a, a) := by
  have hvcd : ContDiff ℝ 1 (deriv r) := hr.deriv'
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hbdd⟩ := exists_strict_bound hvcd a (half_pos hc)
  let W : Set ℝ := {z : ℝ | |z - a| < δ / 2}
  have hWne : W ∈ 𝓝 a := by
    rw [Metric.mem_nhds_iff]
    exact ⟨δ / 2, half_pos hδ, fun z hz => by
      show |z - a| < δ / 2
      rw [Metric.mem_ball, Real.dist_eq] at hz
      exact hz⟩
  have hUne : (W ×ˢ W) ×ˢ (W ×ˢ W) ∈ 𝓝 ((a, a), (a, a)) := by
    have h₁ : W ×ˢ W ∈ 𝓝 (a, a) := by
      rw [nhds_prod_eq]; exact Filter.prod_mem_prod hWne hWne
    have h₂ : (W ×ˢ W) ×ˢ (W ×ˢ W) ∈ 𝓝 (a, a) ×ˢ 𝓝 (a, a) :=
      Filter.prod_mem_prod h₁ h₁
    rwa [← nhds_prod_eq] at h₂
  filter_upwards [hUne] with p hp
  rcases p with ⟨q₁, q₂⟩
  have h11 : |q₁.1 - a| < δ / 2 := hp.1.1
  have h12 : |q₁.2 - a| < δ / 2 := hp.1.2
  have h21 : |q₂.1 - a| < δ / 2 := hp.2.1
  have h22 : |q₂.2 - a| < δ / 2 := hp.2.2
  set cc : Space := deriv (deriv r) a with hccdef
  have hseg₁ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, |seg q₁ t - a| < δ := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have heq : seg q₁ t - a = (1 - t) * (q₁.1 - a) + t * (q₁.2 - a) := by
      rw [seg]; ring
    rw [heq]
    have hle : |(1 - t) * (q₁.1 - a) + t * (q₁.2 - a)|
        ≤ (1 - t) * |q₁.1 - a| + t * |q₁.2 - a| := by
      calc |(1 - t) * (q₁.1 - a) + t * (q₁.2 - a)|
          ≤ |(1 - t) * (q₁.1 - a)| + |t * (q₁.2 - a)| := abs_add_le _ _
        _ = (1 - t) * |q₁.1 - a| + t * |q₁.2 - a| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    have hfin : (1 - t) * |q₁.1 - a| + t * |q₁.2 - a| ≤ δ / 2 := by
      have hA : |q₁.1 - a| ≤ δ / 2 := le_of_lt h11
      have hB : |q₁.2 - a| ≤ δ / 2 := le_of_lt h12
      nlinarith [hA, hB, ht0, ht1]
    linarith
  have hseg₂ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, |seg q₂ t - a| < δ := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have heq : seg q₂ t - a = (1 - t) * (q₂.1 - a) + t * (q₂.2 - a) := by
      rw [seg]; ring
    rw [heq]
    have hle : |(1 - t) * (q₂.1 - a) + t * (q₂.2 - a)|
        ≤ (1 - t) * |q₂.1 - a| + t * |q₂.2 - a| := by
      calc |(1 - t) * (q₂.1 - a) + t * (q₂.2 - a)|
          ≤ |(1 - t) * (q₂.1 - a)| + |t * (q₂.2 - a)| := abs_add_le _ _
        _ = (1 - t) * |q₂.1 - a| + t * |q₂.2 - a| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    have hfin : (1 - t) * |q₂.1 - a| + t * |q₂.2 - a| ≤ δ / 2 := by
      have hA : |q₂.1 - a| ≤ δ / 2 := le_of_lt h21
      have hB : |q₂.2 - a| ≤ δ / 2 := le_of_lt h22
      nlinarith [hA, hB, ht0, ht1]
    linarith
  have hphi : (fderiv ℝ (deriv r) a) 1 = cc := by
    rw [hccdef, fderiv_apply_one_eq_deriv]
  have hphi_apply : ∀ z : ℝ, (fderiv ℝ (deriv r) a) z = z • cc := by
    intro z
    have hz : (fderiv ℝ (deriv r) a) z = (fderiv ℝ (deriv r) a) (z • (1 : ℝ)) := by
      rw [smul_eq_mul, mul_one]
    rw [hz, map_smul, hphi]
  have hI₁ : IntervalIntegrable (fun t : ℝ => deriv r (seg q₁ t)) volume 0 1 :=
    ((hvcd.continuous.comp (continuous_seg q₁))).intervalIntegrable 0 1
  have hI₂ : IntervalIntegrable (fun t : ℝ => deriv r (seg q₂ t)) volume 0 1 :=
    ((hvcd.continuous.comp (continuous_seg q₂))).intervalIntegrable 0 1
  have hI₁₂ : IntervalIntegrable
      (fun t : ℝ => deriv r (seg q₁ t) - deriv r (seg q₂ t)) volume 0 1 :=
    (((hvcd.continuous.comp (continuous_seg q₁)).sub
      (hvcd.continuous.comp (continuous_seg q₂)))).intervalIntegrable 0 1
  have hI₃ : IntervalIntegrable (fun t : ℝ => (seg q₁ t - seg q₂ t) • cc) volume 0 1 :=
    (((continuous_seg q₁).sub (continuous_seg q₂)).smul continuous_const).intervalIntegrable 0 1
  have hId : avgVelP r q₁ - avgVelP r q₂ - avgVelLin cc (q₁ - q₂)
      = ∫ t in (0 : ℝ)..1,
          (deriv r (seg q₁ t) - deriv r (seg q₂ t) - (seg q₁ t - seg q₂ t) • cc) := by
    have e1 : (∫ t in (0 : ℝ)..1, deriv r (seg q₁ t))
        - (∫ t in (0 : ℝ)..1, deriv r (seg q₂ t))
        = ∫ t in (0 : ℝ)..1, (deriv r (seg q₁ t) - deriv r (seg q₂ t)) :=
      (intervalIntegral.integral_sub hI₁ hI₂).symm
    have e3 : avgVelLin cc (q₁ - q₂) = ∫ t in (0 : ℝ)..1, (seg q₁ t - seg q₂ t) • cc := by
      rw [avgVelLin_apply, intervalIntegral.integral_smul_const, integral_seg_sub]
    rw [avgVelP_apply, avgVelP_apply, e1, e3,
      ← intervalIntegral.integral_sub hI₁₂ hI₃]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖deriv r (seg q₁ t) - deriv r (seg q₂ t) - (seg q₁ t - seg q₂ t) • cc‖
        ≤ (c / 2) * (|q₁.1 - q₂.1| + |q₁.2 - q₂.2|) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc ht
    have hb := hbdd (seg q₁ t) (seg q₂ t) (hseg₁ t ht') (hseg₂ t ht')
    rw [hphi_apply ((seg q₁ t) - (seg q₂ t))] at hb
    refine le_trans hb ?_
    rw [Real.norm_eq_abs]
    have ht0 : 0 ≤ t := le_of_lt htIoc.1
    have ht1 : t ≤ 1 := htIoc.2
    have hyt : seg q₁ t - seg q₂ t = (1 - t) * (q₁.1 - q₂.1) + t * (q₁.2 - q₂.2) := by
      rw [seg, seg]; ring
    rw [hyt]
    have h1 : |(1 - t) * (q₁.1 - q₂.1) + t * (q₁.2 - q₂.2)|
        ≤ (1 - t) * |q₁.1 - q₂.1| + t * |q₁.2 - q₂.2| := by
      calc |(1 - t) * (q₁.1 - q₂.1) + t * (q₁.2 - q₂.2)|
          ≤ |(1 - t) * (q₁.1 - q₂.1)| + |t * (q₁.2 - q₂.2)| := abs_add_le _ _
        _ = (1 - t) * |q₁.1 - q₂.1| + t * |q₁.2 - q₂.2| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    have h2 : (1 - t) * |q₁.1 - q₂.1| + t * |q₁.2 - q₂.2|
        ≤ |q₁.1 - q₂.1| + |q₁.2 - q₂.2| := by
      nlinarith [abs_nonneg (q₁.1 - q₂.1), abs_nonneg (q₁.2 - q₂.2)]
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (le_of_lt (half_pos hc))
  have hdx : |q₁.1 - q₂.1| ≤ ‖q₁ - q₂‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le (q₁ - q₂)
  have hdm : |q₁.2 - q₂.2| ≤ ‖q₁ - q₂‖ := by
    simpa [Real.norm_eq_abs] using norm_snd_le (q₁ - q₂)
  calc ‖avgVelP r q₁ - avgVelP r q₂ - avgVelLin cc (q₁ - q₂)‖
      = ‖∫ t in (0 : ℝ)..1,
          (deriv r (seg q₁ t) - deriv r (seg q₂ t) - (seg q₁ t - seg q₂ t) • cc)‖ := by
        rw [hId]
    _ ≤ ((c / 2) * (|q₁.1 - q₂.1| + |q₁.2 - q₂.2|)) * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = (c / 2) * (|q₁.1 - q₂.1| + |q₁.2 - q₂.2|) := by ring
    _ ≤ c * ‖q₁ - q₂‖ := by nlinarith [hdx, hdm, hc]



/-! ## 2. Auxiliary linear algebra -/

/-- The cyclic identity for the scalar triple product. -/
lemma inner_cross3_swap (u v w : Space) :
    inner ℝ (cross3 u v) w = inner ℝ u (cross3 v w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [cross3, WithLp.ofLp_toLp, star_trivial]
  rw [dotProduct_comm (crossProduct (WithLp.ofLp v) (WithLp.ofLp w)) (WithLp.ofLp u)]
  exact triple_product_permutation (WithLp.ofLp w) (WithLp.ofLp u) (WithLp.ofLp v)

/-- The cross product is orthogonal to its second argument. -/
lemma inner_cross3_self_right (u v : Space) : inner ℝ (cross3 u v) v = 0 := by
  have h : inner ℝ (cross3 v u) v = 0 :=
    Commons.Analysis.CrossProduct.inner_cross3_self_left (u := v) (v := u)
  rw [cross3_anticomm] at h
  simpa using h

lemma finrank_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

/-- The cube extraction from a neighbourhood of a point of `ℝ × (ℝ × ℝ)`. -/
lemma exists_cube_subset {u : ℝ × (ℝ × ℝ)} {s : Set (ℝ × (ℝ × ℝ))} (hs : s ∈ 𝓝 u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x m σ : ℝ, |x - u.1| < δ → |m - u.2.1| < δ → |σ - u.2.2| < δ →
      (x, (m, σ)) ∈ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε, hε, fun x m σ hx hm hσ => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm,
    show (x, (m, σ)) - u = (x - u.1, (m - u.2.1, σ - u.2.2)) from rfl,
    Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_lt hx (max_lt hm hσ)

/-! ## 3. The reduced collinearity map -/

/-- The reduced collinearity map `(r σ - r x) ⨯ (average velocity)`. -/
def secPsi (r : ℝ → Space) (q : ℝ × (ℝ × ℝ)) : Space :=
  cross3 (r q.2.2 - r q.1) (avgVelP r (q.1, q.2.1))

/-- The two-scalar reduction of the reduced collinearity map. -/
private def red (r : ℝ → Space) (P Q : Space) (q : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (inner ℝ (secPsi r q) P, inner ℝ (secPsi r q) Q)

lemma avgVelP_self (r : ℝ → Space) (x : ℝ) : avgVelP r (x, x) = velocity r x := by
  rw [avgVelP_apply]
  have h : (fun t : ℝ => deriv r (seg (x, x) t)) = fun _ : ℝ => deriv r x := by
    funext t; simp [seg]
  rw [h, intervalIntegral.integral_const]
  simp [velocity]

lemma avgVelP_secant {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (x m : ℝ) :
    r m - r x = (m - x) • avgVelP r (x, m) := by
  have hsc : ∀ t : ℝ, HasDerivAt (fun s : ℝ => r (x + s * (m - x)))
      ((m - x) • deriv r (x + t * (m - x))) t := by
    intro t
    have hg : HasDerivAt (fun s : ℝ => x + s * (m - x)) (m - x) t := by
      have h1 : HasDerivAt (fun s : ℝ => s * (m - x)) (1 * (m - x)) t :=
        (hasDerivAt_id t).mul_const (m - x)
      simpa using h1.const_add x
    have hr' : HasDerivAt r (deriv r (x + t * (m - x))) (x + t * (m - x)) :=
      ((hr.differentiable (by norm_num)) (x + t * (m - x))).hasDerivAt
    exact HasDerivAt.scomp t hr' hg
  have hcont : Continuous (fun t : ℝ => (m - x) • deriv r (x + t * (m - x))) := by
    have hv : Continuous (deriv r) := ContDiff.continuous_deriv (f := r) hr (by norm_num)
    exact (hv.comp (by continuity)).const_smul (m - x)
  have hint : IntervalIntegrable (fun t : ℝ => (m - x) • deriv r (x + t * (m - x)))
      volume 0 1 := hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hsc t) hint
  have h1 : (∫ t in (0 : ℝ)..1, (m - x) • deriv r (x + t * (m - x))) = r m - r x := by
    simpa using hftc
  rw [← h1, intervalIntegral.integral_smul, avgVelP_apply]
  congr 1

/-- The collinearity identity. -/
lemma collinearity_eq_smul_secPsi {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (x m σ : ℝ) :
    cross3 (r σ - r x) (r m - r x) = (m - x) • secPsi r (x, (m, σ)) := by
  rw [secPsi, avgVelP_secant hr x m, cross3_smul_right]

/-- If the reduced map vanishes and the triple `{P, Q, w}` spans, then `secPsi` vanishes. -/
lemma secPsi_eq_zero_of_red_eq_zero {r : ℝ → Space} {P Q : Space} {q : ℝ × (ℝ × ℝ)}
    (hspan : Submodule.span ℝ ({P, Q, avgVelP r (q.1, q.2.1)} : Set Space) = ⊤)
    (h : red r P Q q = (0, 0)) : secPsi r q = 0 := by
  have h1 : inner ℝ (secPsi r q) P = 0 := by
    have := congrArg Prod.fst h
    simpa [red] using this
  have h2 : inner ℝ (secPsi r q) Q = 0 := by
    have := congrArg Prod.snd h
    simpa [red] using this
  have h3 : inner ℝ (secPsi r q) (avgVelP r (q.1, q.2.1)) = 0 := by
    rw [secPsi]
    exact inner_cross3_self_right _ _
  refine Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top
    (secPsi r q) {P, Q, avgVelP r (q.1, q.2.1)} ?_ hspan
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- The reduced map is strictly differentiable at the base point. -/
lemma red_hasStrictFDerivAt {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (a b : ℝ) (P Q : Space) :
    HasStrictFDerivAt (red r P Q) (fderiv ℝ (red r P Q) (a, (a, b))) (a, (a, b)) := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le le_top
  have hA : HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1) (a, (a, b))) (a, (a, b)) :=
    ((by fun_prop : ContDiff ℝ ⊤ (fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1)).contDiffAt).hasStrictFDerivAt
      (by norm_num)
  have hproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1))
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (a, (a, b))) (a, (a, b)) :=
    ((by fun_prop : ContDiff ℝ ⊤ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1))).contDiffAt).hasStrictFDerivAt
      (by norm_num)
  have hB : HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => avgVelP r (q.1, q.2.1))
      ((avgVelLin (deriv (deriv r) a)) ∘L
        (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (a, (a, b)))) (a, (a, b)) :=
    (avgVelP_hasStrictFDerivAt hr2 a).comp (a, (a, b)) hproj
  have hCross : HasStrictFDerivAt (fun p : Space × Space => cross3 p.1 p.2)
      (fderiv ℝ (fun p : Space × Space => cross3 p.1 p.2) (r b - r a, avgVelP r (a, a)))
      (r b - r a, avgVelP r (a, a)) :=
    ((Commons.Analysis.CrossProduct.cross3_contDiff).contDiffAt).hasStrictFDerivAt (by norm_num)
  have hpair : HasStrictFDerivAt
      (fun q : ℝ × (ℝ × ℝ) => ((fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1) q,
        (fun q : ℝ × (ℝ × ℝ) => avgVelP r (q.1, q.2.1)) q))
      ((fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1) (a, (a, b))).prod
        ((avgVelLin (deriv (deriv r) a)) ∘L
          (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (a, (a, b))))) (a, (a, b)) :=
    hA.prodMk hB
  have hsecC := hCross.comp (a, (a, b)) hpair
  have hsec : HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => secPsi r q)
      ((fderiv ℝ (fun p : Space × Space => cross3 p.1 p.2) (r b - r a, avgVelP r (a, a))) ∘L
        ((fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => r q.2.2 - r q.1) (a, (a, b))).prod
          ((avgVelLin (deriv (deriv r) a)) ∘L
            (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (a, (a, b))))))
      (a, (a, b)) :=
    hsecC.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => rfl))
  have hL2 : HasStrictFDerivAt
      (⇑(((innerSLFlip ℝ P : Space →L[ℝ] ℝ)).prod (innerSLFlip ℝ Q : Space →L[ℝ] ℝ)))
      (fderiv ℝ (⇑(((innerSLFlip ℝ P : Space →L[ℝ] ℝ)).prod (innerSLFlip ℝ Q : Space →L[ℝ] ℝ)))
        (secPsi r (a, (a, b)))) (secPsi r (a, (a, b))) := by
    have h := ContinuousLinearMap.hasStrictFDerivAt
      (((innerSLFlip ℝ P : Space →L[ℝ] ℝ)).prod (innerSLFlip ℝ Q : Space →L[ℝ] ℝ))
      (x := secPsi r (a, (a, b)))
    rw [h.hasFDerivAt.fderiv]
    exact h
  have hcomp := hL2.comp (a, (a, b)) hsec
  have heq : (fun x : ℝ × (ℝ × ℝ) =>
        ⇑(((innerSLFlip ℝ P : Space →L[ℝ] ℝ)).prod (innerSLFlip ℝ Q : Space →L[ℝ] ℝ)) (secPsi r x))
      =ᶠ[𝓝 (a, (a, b))] red r P Q :=
    Filter.Eventually.of_forall (fun q => by
      simp only [ContinuousLinearMap.prod_apply, innerSLFlip_apply_apply, red]
      rfl)
  have hfin : HasStrictFDerivAt (red r P Q) (fderiv ℝ (red r P Q) (a, (a, b))) (a, (a, b)) := by
    have hc : HasStrictFDerivAt (red r P Q) _ (a, (a, b)) :=
      hcomp.congr_of_eventuallyEq heq
    rw [hc.hasFDerivAt.fderiv]
    exact hc
  exact hfin

lemma avgVelP_continuousAt {r : ℝ → Space} (hr : ContDiff ℝ 2 r) (a b : ℝ) :
    ContinuousAt (fun v : ℝ × (ℝ × ℝ) => avgVelP r (v.1, v.2.1)) (a, (a, b)) := by
  have hproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1))
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (a, (a, b))) (a, (a, b)) :=
    ((by fun_prop : ContDiff ℝ ⊤ (fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1))).contDiffAt).hasStrictFDerivAt
      (by norm_num)
  have hB := (avgVelP_hasStrictFDerivAt hr a).comp (a, (a, b)) hproj
  have hcont : ContinuousAt
      (fun x => avgVelP r ((fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) x)) (a, (a, b)) :=
    hB.hasFDerivAt.continuousAt
  simpa using hcont

/-! ## 4. The value of the derivative on the three axes -/

/-- The Leibniz rule for the cross product, stated with `cross3`. -/
lemma hasDerivAt_cross3' (u v : ℝ → Space) {du dv : Space} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun x => cross3 (u x) (v x)) (cross3 du (v t) + cross3 (u t) dv) t :=
  Commons.Analysis.CrossProduct.hasDerivAt_cross3 u v hu hv

lemma fderiv_cross3_apply (u₀ v₀ du dv : Space) :
    (fderiv ℝ (fun p : Space × Space => cross3 p.1 p.2) (u₀, v₀)) (du, dv)
      = cross3 du v₀ + cross3 u₀ dv := by
  have hF : DifferentiableAt ℝ (fun p : Space × Space => cross3 p.1 p.2) (u₀, v₀) :=
    ((Commons.Analysis.CrossProduct.cross3_contDiff).differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun p : Space × Space => cross3 p.1 p.2) (p := (u₀, v₀)) (e := (du, dv)) hF
  have h2 : HasDerivAt (fun s : ℝ => cross3 (u₀ + s • du) (v₀ + s • dv))
      (cross3 du v₀ + cross3 u₀ dv) 0 := by
    have hu : HasDerivAt (fun s : ℝ => u₀ + s • du) du 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const du |>.const_add u₀
    have hv : HasDerivAt (fun s : ℝ => v₀ + s • dv) dv 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const dv |>.const_add v₀
    have h := hasDerivAt_cross3' _ _ hu hv
    simpa using h
  have hfun : (fun s : ℝ => (fun p : Space × Space => cross3 p.1 p.2) ((u₀, v₀) + s • (du, dv)))
      = fun s : ℝ => cross3 (u₀ + s • du) (v₀ + s • dv) := by
    funext s; simp [Prod.mk_add_mk, Prod.smul_mk]
  rw [hfun] at h1
  exact HasDerivAt.unique h1 h2

lemma red_value_σ {r : ℝ → Space} (hr : ContDiff ℝ 1 r) (a b : ℝ) (P Q : Space) :
    HasDerivAt (fun s : ℝ => red r P Q (a, (a, b + s)))
      (inner ℝ (cross3 (velocity r b) (velocity r a)) P,
       inner ℝ (cross3 (velocity r b) (velocity r a)) Q) 0 := by
  have h1 : HasDerivAt r (velocity r b) b := ((hr.differentiable (by norm_num)) b).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => b + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add b
  have h1' : HasDerivAt r (velocity r b) (b + 0) := by simpa using h1
  have hrb : HasDerivAt (fun s : ℝ => r (b + s)) (velocity r b) 0 :=
    HasDerivAt.comp_const_add b (0 : ℝ) h1'
  have hX : HasDerivAt (fun s : ℝ => r (b + s) - r a) (velocity r b) 0 := by
    simpa using hrb.sub_const (r a)
  have hY : HasDerivAt (fun _ : ℝ => avgVelP r (a, a)) 0 0 := hasDerivAt_const 0 _
  have hcr := hasDerivAt_cross3' (fun s : ℝ => r (b + s) - r a)
    (fun _ : ℝ => avgVelP r (a, a)) hX hY
  have hval : cross3 (velocity r b) (avgVelP r (a, a)) + cross3 (r (b + 0) - r a) (0 : Space)
      = cross3 (velocity r b) (velocity r a) := by
    rw [cross3_zero_right, add_zero, avgVelP_self]
  rw [hval] at hcr
  have hp : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r (b + s) - r a) (avgVelP r (a, a))) P)
      (inner ℝ (cross3 (velocity r b) (velocity r a)) P) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 P)).congr_deriv (by simp)
  have hq : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r (b + s) - r a) (avgVelP r (a, a))) Q)
      (inner ℝ (cross3 (velocity r b) (velocity r a)) Q) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 Q)).congr_deriv (by simp)
  simpa [red, secPsi] using hp.prodMk hq

lemma red_value_m {r : ℝ → Space} (hr : ContDiff ℝ 2 r) (a b : ℝ) (P Q : Space) :
    HasDerivAt (fun s : ℝ => red r P Q (a, (a + s, b)))
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
       inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 := by
  have hst := avgVelP_hasStrictFDerivAt hr a
  have hdiff : DifferentiableAt ℝ (avgVelP r) (a, a) := hst.hasFDerivAt.differentiableAt
  have hdir := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := avgVelP r) (p := (a, a)) (e := ((0 : ℝ), (1 : ℝ))) hdiff
  rw [hst.hasFDerivAt.fderiv, avgVelLin_apply] at hdir
  have hY : HasDerivAt (fun s : ℝ => avgVelP r (a, a + s))
      ((1 / 2 : ℝ) • deriv (deriv r) a) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => avgVelP r ((a, a) + s • ((0 : ℝ), (1 : ℝ))))
        ((1 / 2 : ℝ) • deriv (deriv r) a) 0 :=
      hdir.congr_deriv (by rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num])
    have hfun : (fun s : ℝ => avgVelP r ((a, a) + s • ((0 : ℝ), (1 : ℝ))))
        = fun s : ℝ => avgVelP r (a, a + s) := by
      funext s; simp [Prod.mk_add_mk, Prod.smul_mk]
    rwa [hfun] at h3
  have hX : HasDerivAt (fun _ : ℝ => r b - r a) 0 0 := hasDerivAt_const 0 _
  have hcr := hasDerivAt_cross3' (fun _ : ℝ => r b - r a) (fun s : ℝ => avgVelP r (a, a + s)) hX hY
  have hval : cross3 0 (avgVelP r (a, a + 0)) + cross3 (r b - r a) ((1 / 2 : ℝ) • deriv (deriv r) a)
      = (1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a) := by
    rw [cross3_zero_left, zero_add, cross3_smul_right]
  rw [hval] at hcr
  have hp : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r b - r a) (avgVelP r (a, a + s))) P)
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 P)).congr_deriv (by simp)
  have hq : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r b - r a) (avgVelP r (a, a + s))) Q)
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 Q)).congr_deriv (by simp)
  simpa [red, secPsi] using hp.prodMk hq

lemma red_value_x {r : ℝ → Space} (hr : ContDiff ℝ 2 r) (a b : ℝ) (P Q : Space) :
    HasDerivAt (fun s : ℝ => red r P Q (a + s, (a, b)))
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
       inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 := by
  have h1 : HasDerivAt r (velocity r a) a := ((hr.differentiable (by norm_num)) a).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => a + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add a
  have h1' : HasDerivAt r (velocity r a) (a + 0) := by simpa using h1
  have hra : HasDerivAt (fun s : ℝ => r (a + s)) (velocity r a) 0 :=
    HasDerivAt.comp_const_add a (0 : ℝ) h1'
  have hX : HasDerivAt (fun s : ℝ => r b - r (a + s)) (-velocity r a) 0 := by
    simpa using hra.const_sub (r b)
  have hst := avgVelP_hasStrictFDerivAt hr a
  have hdiff : DifferentiableAt ℝ (avgVelP r) (a, a) := hst.hasFDerivAt.differentiableAt
  have hdir := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := avgVelP r) (p := (a, a)) (e := ((1 : ℝ), (0 : ℝ))) hdiff
  rw [hst.hasFDerivAt.fderiv, avgVelLin_apply] at hdir
  have hY : HasDerivAt (fun s : ℝ => avgVelP r (a + s, a))
      ((1 / 2 : ℝ) • deriv (deriv r) a) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => avgVelP r ((a, a) + s • ((1 : ℝ), (0 : ℝ))))
        ((1 / 2 : ℝ) • deriv (deriv r) a) 0 :=
      hdir.congr_deriv (by rw [show ((1 : ℝ) + 0) / 2 = 1 / 2 by norm_num])
    have hfun : (fun s : ℝ => avgVelP r ((a, a) + s • ((1 : ℝ), (0 : ℝ))))
        = fun s : ℝ => avgVelP r (a + s, a) := by
      funext s; simp [Prod.mk_add_mk, Prod.smul_mk]
    rwa [hfun] at h3
  have hcr := hasDerivAt_cross3' (fun s : ℝ => r b - r (a + s)) (fun s : ℝ => avgVelP r (a + s, a)) hX hY
  have hval : cross3 (-velocity r a) (avgVelP r (a + 0, a)) + cross3 (r b - r (a + 0)) ((1 / 2 : ℝ) • deriv (deriv r) a)
      = (1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a) := by
    simp only [add_zero, avgVelP_self, cross3_neg_left, cross3_self, neg_zero, zero_add,
      cross3_smul_right]
  rw [hval] at hcr
  have hp : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r b - r (a + s)) (avgVelP r (a + s, a))) P)
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 P)).congr_deriv (by simp)
  have hq : HasDerivAt (fun s : ℝ => inner ℝ (cross3 (r b - r (a + s)) (avgVelP r (a + s, a))) Q)
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 :=
    (HasDerivAt.inner ℝ hcr (hasDerivAt_const 0 Q)).congr_deriv (by simp)
  simpa [red, secPsi] using hp.prodMk hq

/-! ## 5. The derivative of `red` at the base point on the three axes -/

lemma fderiv_red_x {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (a b : ℝ) (P Q : Space) :
    (fderiv ℝ (red r P Q) (a, (a, b))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
      = (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
         inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le le_top
  have hD : DifferentiableAt ℝ (red r P Q) (a, (a, b)) :=
    (red_hasStrictFDerivAt hr a b P Q).hasFDerivAt.differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := red r P Q) (p := (a, (a, b))) (e := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) hD
  have h2 : HasDerivAt (fun s : ℝ => red r P Q ((a, (a, b)) + s • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
       inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 :=
    (red_value_x hr2 a b P Q).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by
        simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, add_zero]))
  exact (HasDerivAt.unique h2 h1).symm

lemma fderiv_red_m {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (a b : ℝ) (P Q : Space) :
    (fderiv ℝ (red r P Q) (a, (a, b))) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
      = (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
         inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le le_top
  have hD : DifferentiableAt ℝ (red r P Q) (a, (a, b)) :=
    (red_hasStrictFDerivAt hr a b P Q).hasFDerivAt.differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := red r P Q) (p := (a, (a, b))) (e := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) hD
  have h2 : HasDerivAt (fun s : ℝ => red r P Q ((a, (a, b)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
      (inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) P,
       inner ℝ ((1 / 2 : ℝ) • cross3 (r b - r a) (deriv (deriv r) a)) Q) 0 :=
    (red_value_m hr2 a b P Q).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by
        simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, add_zero]))
  exact (HasDerivAt.unique h2 h1).symm

lemma fderiv_red_σ {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (a b : ℝ) (P Q : Space) :
    (fderiv ℝ (red r P Q) (a, (a, b))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      = (inner ℝ (cross3 (velocity r b) (velocity r a)) P,
         inner ℝ (cross3 (velocity r b) (velocity r a)) Q) := by
  have hD : DifferentiableAt ℝ (red r P Q) (a, (a, b)) :=
    (red_hasStrictFDerivAt hr a b P Q).hasFDerivAt.differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := red r P Q) (p := (a, (a, b))) (e := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) hD
  have h2 : HasDerivAt (fun s : ℝ => red r P Q ((a, (a, b)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
      (inner ℝ (cross3 (velocity r b) (velocity r a)) P,
       inner ℝ (cross3 (velocity r b) (velocity r a)) Q) 0 :=
    (red_value_σ (hr.of_le le_top) a b P Q).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by
        simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, add_zero]))
  exact (HasDerivAt.unique h2 h1).symm

/-! ## 6. The main theorem -/

open LeanEval.KnotTheory.Quadrisecant in
/-- **The free-end (tangent-chord) local structure.**  If the chord `{r a, r b}` (`0 < b - a < period`) is tangent to the knot at `a`, then for a knot without inflections (`hinfl`) in tangent-chord general position (`htc`), the collinearity zero set near the tangent chord is the diagonal together with exactly one branch, encoded by `Work.Drive.TangentChordLocalCurve r a b`. -/
theorem tangentChordLocalCurve {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) {a b : ℝ} (hab : r b - r a ≠ 0)
    (hbd : 0 < b - a) (hlt : b - a < period)
    (htan : cross3 (r b - r a) (velocity r a) = 0) :
    Work.Drive.TangentChordLocalCurve r a b := by
  obtain ⟨hnotb, hin⟩ := (htc a b hbd hlt).1 htan
  have hrc : ContDiff ℝ ⊤ r := hr.smooth
  have hr2 : ContDiff ℝ 2 r := hrc.of_le le_top
  have hva : velocity r a ≠ 0 := hr.regular a
  set cc : Space := deriv (deriv r) a with hccdef
  set Pv : Space := (1 / 2 : ℝ) • cross3 (r b - r a) cc with hPvdef
  set Qv : Space := cross3 (velocity r b) (velocity r a) with hQvdef
  -- the chord is parallel to the tangent at `a`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, velocity r a = t • (r b - r a) := by
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul (r b - r a)
      (velocity r a)).mp htan with h | h
    · exact absurd h hab
    · exact h
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht
    exact hva ht
  have hrb : r b - r a = t⁻¹ • velocity r a := by
    rw [ht, smul_smul, inv_mul_cancel₀ htne, one_smul]
  have hvc : LinearIndependent ℝ ![velocity r a, cc] := hinfl a
  have hcross_vacc : cross3 (velocity r a) cc ≠ 0 :=
    (Commons.Analysis.CrossProduct.cross3_ne_zero_iff_linearIndependent _ _).mpr hvc
  have hPveq : Pv = ((1 / 2 : ℝ) * t⁻¹) • cross3 (velocity r a) cc := by
    rw [hPvdef, hrb, cross3_smul_left, smul_smul]
  have hPvne : Pv ≠ 0 := by
    rw [hPveq]
    exact smul_ne_zero (mul_ne_zero (by norm_num) (inv_ne_zero htne)) hcross_vacc
  have hPvcc : inner ℝ Pv cc = 0 := by
    rw [hPveq, inner_smul_left, inner_cross3_self_right]
    simp
  have hQvcc : inner ℝ Qv cc ≠ 0 := by
    rw [hQvdef, inner_cross3_swap, real_inner_comm]
    exact hin
  have hPvva : inner ℝ Pv (velocity r a) = 0 := by
    have h0 : inner ℝ (cross3 (velocity r a) cc) (velocity r a) = 0 :=
      Commons.Analysis.CrossProduct.inner_cross3_self_left _ _
    rw [hPveq, inner_smul_left, h0]
    simp
  have hQvva : inner ℝ Qv (velocity r a) = 0 := by
    rw [hQvdef]
    exact inner_cross3_self_right _ _
  -- independence
  have hPQ : ∀ x y : ℝ, x • Pv + y • Qv = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have key : y * inner ℝ Qv cc = 0 := by
      have h := congrArg (fun z : Space => inner ℝ z cc) hxy
      have h' : x * inner ℝ Pv cc + y * inner ℝ Qv cc = 0 := by
        simpa [inner_add_left, inner_smul_left, RCLike.conj_to_real, smul_eq_mul] using h
      rw [hPvcc, mul_zero, zero_add] at h'
      exact h'
    have hy : y = 0 := (mul_eq_zero.mp key).resolve_right hQvcc
    have hx : x = 0 := by
      have h2 : x • Pv = 0 := by
        rw [hy, zero_smul, add_zero] at hxy
        exact hxy
      exact (smul_eq_zero.mp h2).resolve_right hPvne
    exact ⟨hx, hy⟩
  have hPQlin : LinearIndependent ℝ ![Pv, Qv] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 • Pv + g 1 • Qv = 0 := by simpa [Fin.sum_univ_two] using hg
    obtain ⟨h0', h1'⟩ := hPQ (g 0) (g 1) h0
    intro i
    fin_cases i
    · exact h0'
    · exact h1'
  have hLI3 : ∀ {w : Space}, inner ℝ w (velocity r a) ≠ 0 → LinearIndependent ℝ ![Pv, Qv, w] := by
    intro w hw
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g 0 • Pv + g 1 • Qv + g 2 • w = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have h1 : inner ℝ (g 0 • Pv + g 1 • Qv + g 2 • w) (velocity r a) = 0 := by
      rw [h0, inner_zero_left]
    have h1' : g 2 * inner ℝ w (velocity r a) = 0 := by
      simpa [inner_add_left, inner_smul_left, RCLike.conj_to_real, smul_eq_mul, hPvva,
        hQvva] using h1
    have hg2 : g 2 = 0 := (mul_eq_zero.mp h1').resolve_right hw
    have h3 : g 0 • Pv + g 1 • Qv = 0 := by
      have hh := h0
      rw [hg2, zero_smul, add_zero] at hh
      exact hh
    obtain ⟨hg0, hg1⟩ := hPQ (g 0) (g 1) h3
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  -- the spanning neighbourhood
  have hwperp : ∀ᶠ v in 𝓝 (a, (a, b)),
      inner ℝ (avgVelP r (v.1, v.2.1)) (velocity r a) ≠ 0 := by
    have hcont : ContinuousAt (fun v : ℝ × (ℝ × ℝ) =>
        inner ℝ (avgVelP r (v.1, v.2.1)) (velocity r a)) (a, (a, b)) :=
      ContinuousAt.inner (avgVelP_continuousAt hr2 a b) continuousAt_const
    have hbase : inner ℝ (avgVelP r (a, a)) (velocity r a) ≠ 0 := by
      rw [avgVelP_self, real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hva)
    exact hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simpa using hbase))
  have hspan_ev : ∀ᶠ v in 𝓝 (a, (a, b)),
      Submodule.span ℝ ({Pv, Qv, avgVelP r (v.1, v.2.1)} : Set Space) = ⊤ := by
    filter_upwards [hwperp] with v hv
    exact Commons.LinearAlgebra.Span.span_top_of_three_independent (E := Space) finrank_space
      (hLI3 (w := avgVelP r (v.1, v.2.1)) hv)
  -- the reduced map
  have hsec0 : secPsi r (a, (a, b)) = 0 := by
    rw [secPsi, avgVelP_self]
    exact htan
  have hred0 : red r Pv Qv (a, (a, b)) = (0, 0) := by
    simp [red, hsec0]
  have hred := red_hasStrictFDerivAt hrc a b Pv Qv
  set F : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) := fderiv ℝ (red r Pv Qv) (a, (a, b)) with hFdef
  set T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := F ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) with hTdef
  have hFm : F ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) = (inner ℝ Pv Pv, inner ℝ Pv Qv) := by
    rw [hFdef]
    exact fderiv_red_m hrc a b Pv Qv
  have hFx : F ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = (inner ℝ Pv Pv, inner ℝ Pv Qv) := by
    rw [hFdef]
    exact fderiv_red_x hrc a b Pv Qv
  have hT1 : T ((1 : ℝ), (0 : ℝ)) = (inner ℝ Pv Pv, inner ℝ Pv Qv) := by
    rw [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact hFm
  have hT0 : T ((0 : ℝ), (1 : ℝ)) = (inner ℝ Qv Pv, inner ℝ Qv Qv) := by
    rw [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hFdef]
    exact fderiv_red_σ hrc a b Pv Qv
  have hTinv : T.IsInvertible := by
    refine Commons.Analysis.Normed.isInvertible_of_det_columns (c₁₁ := inner ℝ Pv Pv)
      (c₁₂ := inner ℝ Pv Qv) (c₂₁ := inner ℝ Qv Pv) (c₂₂ := inner ℝ Qv Qv) hT1 hT0 ?_
    have hGdet : (Matrix.det !![inner ℝ Pv Pv, inner ℝ Pv Qv; inner ℝ Qv Pv,
        inner ℝ Qv Qv]) ≠ 0 :=
      Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent
        (x := Pv) (y := Qv) hPQlin
    have hEq : (Matrix.det !![inner ℝ Pv Pv, inner ℝ Pv Qv; inner ℝ Qv Pv,
        inner ℝ Qv Qv]) = (inner ℝ Pv Pv) * (inner ℝ Qv Qv) - (inner ℝ Pv Qv) * (inner ℝ Qv Pv) := by
      rw [Matrix.det_fin_two_of]
    rw [← hEq]
    exact hGdet
  set ψ : ℝ → ℝ × ℝ := hred.implicitFunctionOfProdDomain hTinv with hψdef
  have hψ_iff : ∀ᶠ v in 𝓝 (a, (a, b)),
      red r Pv Qv v = red r Pv Qv (a, (a, b)) ↔ ψ v.1 = v.2 :=
    hred.eventually_apply_eq_iff_implicitFunctionOfProdDomain hTinv
  have hψ_tend : Tendsto ψ (𝓝 a) (𝓝 (a, b)) :=
    hred.tendsto_implicitFunctionOfProdDomain hTinv
  have hψ_strict : HasStrictFDerivAt ψ
      (-(T.inverse) ∘L (F ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) a := by
    have h := hred.hasStrictFDerivAt_implicitFunctionOfProdDomain hTinv
    simpa [hψdef, hTdef] using h
  have hψ_eq : ψ a = (a, b) := (hψ_iff.self_of_nhds).mp rfl
  have hψ_deriv : HasDerivAt ψ (-1, 0) a := by
    have h1 : HasDerivAt ψ ((-(T.inverse) ∘L (F ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1) a :=
      hψ_strict.hasFDerivAt.hasDerivAt
    have h2 : ((-(T.inverse) ∘L (F ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1) = (-1, 0) := by
      apply hTinv.injective
      have e1 : T ((-(T.inverse) ∘L (F ∘L ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ))) 1)
          = -F ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.inl_apply, map_neg, hTinv.self_apply_inverse]
        rfl
      have e2 : T ((-1 : ℝ), (0 : ℝ)) = -F ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
        have hneg : ((-1 : ℝ), (0 : ℝ)) = -((1 : ℝ), (0 : ℝ)) := by ext <;> simp
        rw [hneg]
        simp only [map_neg, hT1, hFx]
      rw [e1, e2]
    rw [← h2]
    exact h1
  -- neighbourhood bookkeeping
  obtain ⟨S₁, hS₁, hS₁'⟩ := hψ_iff.exists_mem
  obtain ⟨S₂, hS₂, hS₂'⟩ := hspan_ev.exists_mem
  obtain ⟨δ, hδ, hcube⟩ := exists_cube_subset (Filter.inter_mem hS₁ hS₂)
  have hgraph_ev : ∀ᶠ x in 𝓝 a, |(ψ x).1 - a| < δ ∧ |(ψ x).2 - b| < δ := by
    have hs : {z : ℝ × ℝ | |z.1 - a| < δ ∧ |z.2 - b| < δ} ∈ 𝓝 (a, b) := by
      have h1 : {z : ℝ | |z - a| < δ} ∈ 𝓝 a := by
        rw [Metric.mem_nhds_iff]
        exact ⟨δ, hδ, fun z hz => by rw [Metric.mem_ball, Real.dist_eq] at hz; exact hz⟩
      have h2 : {z : ℝ | |z - b| < δ} ∈ 𝓝 b := by
        rw [Metric.mem_nhds_iff]
        exact ⟨δ, hδ, fun z hz => by rw [Metric.mem_ball, Real.dist_eq] at hz; exact hz⟩
      have hh := Filter.prod_mem_prod h1 h2
      rwa [← nhds_prod_eq] at hh
    exact hψ_tend.eventually hs
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp hgraph_ev
  refine ⟨min δ₁ δ, lt_min hδ₁ hδ, ψ, hψ_eq, hψ_deriv, ?_, ?_⟩
  · intro x hx
    have hx₁ : |x - a| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hxδ : |x - a| < δ := lt_of_lt_of_le hx (min_le_right _ _)
    obtain ⟨hg1, hg2⟩ := hδ₁' (y := x) hx₁
    have hmem : (x, ψ x) ∈ S₁ ∩ S₂ := hcube x (ψ x).1 (ψ x).2 hxδ hg1 hg2
    have hredv : red r Pv Qv (x, ψ x) = red r Pv Qv (a, (a, b)) :=
      (hS₁' (x, ψ x) hmem.1).mpr rfl
    have hsec : secPsi r (x, ψ x) = 0 :=
      secPsi_eq_zero_of_red_eq_zero (hS₂' (x, ψ x) hmem.2) (by rw [hredv, hred0])
    rw [collinearity_eq_smul_secPsi hrc x (ψ x).1 (ψ x).2, hsec, smul_zero]
  · intro x m σ hx hm hσ hcol
    have hxδ : |x - a| < δ := lt_of_lt_of_le hx (min_le_right _ _)
    have hmδ : |m - a| < δ := lt_of_lt_of_le hm (min_le_right _ _)
    have hσδ : |σ - b| < δ := lt_of_lt_of_le hσ (min_le_right _ _)
    have hmem : (x, (m, σ)) ∈ S₁ ∩ S₂ := hcube x m σ hxδ hmδ hσδ
    by_cases hmx : m = x
    · exact Or.inl hmx
    · refine Or.inr ?_
      have hsec : secPsi r (x, (m, σ)) = 0 := by
        have h := collinearity_eq_smul_secPsi hrc x m σ
        rw [hcol] at h
        rcases smul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' (sub_ne_zero.mpr hmx)
        · exact h'
      have hredv : red r Pv Qv (x, (m, σ)) = red r Pv Qv (a, (a, b)) := by
        rw [hred0]
        simp [red, hsec]
      have := (hS₁' (x, (m, σ)) hmem.1).mp hredv
      exact this.symm
