import Mathlib

/-!
# Auxiliary calculus lemmas for `farRegionGlueBounds`

This module collects the "junk-value aware" calculus lemmas used by
`Work.OddVolterra.Free.farRegionGlueBounds` and its helpers:

* `deriv_eq_zero_of_even` : an even function has derivative `0` at `0`;
* `not_differentiableAt_comp_cos` : if `f` is not differentiable at `cos y` and `sin y ≠ 0`,
  then `f ∘ cos` is not differentiable at `y`;
* `deriv_cos_comp` : the pointwise chain rule `deriv (f ∘ cos) y = deriv f (cos y) * (-sin y)`,
  valid for *every* `f`, with the junk value `0` taken into account;
* `abs_deriv_le_of_eventually_lipschitz` : a local Lipschitz bound bounds the derivative;
* `deriv_eq_zero_of_frequently_zero` : if `g` vanishes on a set accumulating at `u` and `g` is
  differentiable at `u`, then `g u = 0` and `deriv g u = 0`;
* the quotient-rule formulas for `v ↦ 2 * R v / v ^ 2` and `v ↦ 2 * R v / v`, together with the
  fact that these are not differentiable at the points where `R` is not.
-/

namespace Work.OddVolterra.Free

open Filter
open scoped Topology

/-- An even function has vanishing derivative at `0`. -/
theorem deriv_eq_zero_of_even {g : ℝ → ℝ} (h : ∀ t, g (-t) = g t) : deriv g 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ g 0
  · have hneg : HasDerivAt (fun x : ℝ => -x) (-1) 0 := hasDerivAt_neg' 0
    have hg : HasDerivAt g (deriv g 0) ((fun x : ℝ => -x) 0) := by simpa using hd.hasDerivAt
    have hcomp : HasDerivAt (g ∘ fun x : ℝ => -x) (deriv g 0 * (-1)) 0 := hg.comp 0 hneg
    have hgl : (g ∘ fun x : ℝ => -x) = g := by funext t; exact h t
    rw [hgl] at hcomp
    have huniq := HasDerivAt.unique hcomp hd.hasDerivAt
    linarith
  · exact deriv_zero_of_not_differentiableAt hd

/-- If `f` is not differentiable at `cos y` and `sin y ≠ 0`, then `f ∘ cos` is not differentiable
at `y` (the derivative of `cos` at `y` is nonzero, so `cos` is a local diffeomorphism there). -/
theorem not_differentiableAt_comp_cos {f : ℝ → ℝ} {y : ℝ} (hsin : Real.sin y ≠ 0)
    (hf : ¬ DifferentiableAt ℝ f (Real.cos y)) :
    ¬ DifferentiableAt ℝ (fun y : ℝ => f (Real.cos y)) y := by
  intro hG
  have hc := Real.hasStrictDerivAt_cos y
  have hc' : (-Real.sin y) ≠ 0 := by simpa using hsin
  have hright := hc.eventually_right_inverse hc'
  have hleft := hc.eventually_left_inverse hc'
  have hψ : hc.localInverse Real.cos (-Real.sin y) y hc' (Real.cos y) = y := by
    simpa using hleft.self_of_nhds
  have hdiff : DifferentiableAt ℝ (hc.localInverse Real.cos (-Real.sin y) y hc') (Real.cos y) :=
    (hc.hasStrictFDerivAt_equiv hc').to_localInverse.differentiableAt
  have hev : f =ᶠ[𝓝 (Real.cos y)]
      (fun v => f (Real.cos (hc.localInverse Real.cos (-Real.sin y) y hc' v))) := by
    filter_upwards [hright] with v hv
    rw [hv]
  have hcomp : DifferentiableAt ℝ
      (fun v => f (Real.cos (hc.localInverse Real.cos (-Real.sin y) y hc' v))) (Real.cos y) := by
    have h2 : DifferentiableAt ℝ (fun v => f (Real.cos v))
        (hc.localInverse Real.cos (-Real.sin y) y hc' (Real.cos y)) := by
      rw [hψ]; exact hG
    exact h2.comp (Real.cos y) hdiff
  exact hf (hev.differentiableAt_iff.mpr hcomp)

/-- The pointwise chain rule for `cos`, valid for every `f` (junk values included):
`deriv (f ∘ cos) y = deriv f (cos y) * (-sin y)`. -/
theorem deriv_cos_comp (f : ℝ → ℝ) (y : ℝ) :
    deriv (fun y : ℝ => f (Real.cos y)) y = deriv f (Real.cos y) * (-Real.sin y) := by
  by_cases hd : DifferentiableAt ℝ f (Real.cos y)
  · have hc : deriv (fun y : ℝ => f (Real.cos y)) y = deriv f (Real.cos y) * deriv Real.cos y :=
      deriv_comp (h₂ := f) (h := Real.cos) (x := y) hd Real.differentiableAt_cos
    rw [hc, Real.deriv_cos]
  · rw [deriv_zero_of_not_differentiableAt hd, zero_mul]
    by_cases hsin : Real.sin y = 0
    · by_cases hGy : DifferentiableAt ℝ (fun y : ℝ => f (Real.cos y)) y
      · have heven : ∀ t : ℝ,
            (fun s : ℝ => f (Real.cos (y + s))) (-t) = (fun s : ℝ => f (Real.cos (y + s))) t := by
          intro t
          simp only
          congr 1
          rw [Real.cos_add, Real.cos_add, hsin]
          ring_nf
          rw [Real.cos_neg]
        have h0 := deriv_eq_zero_of_even (g := fun s : ℝ => f (Real.cos (y + s))) heven
        have htrans : deriv (fun s : ℝ => f (Real.cos (y + s))) 0
            = deriv (fun y : ℝ => f (Real.cos y)) y := by
          have hc := deriv_comp (h₂ := fun y : ℝ => f (Real.cos y)) (h := fun s : ℝ => y + s)
            (x := 0) (by simpa using hGy) (by fun_prop)
          simpa [Function.comp_def, deriv_const_add_id] using hc
        rw [← htrans]; exact h0
      · exact deriv_zero_of_not_differentiableAt hGy
    · exact deriv_zero_of_not_differentiableAt (not_differentiableAt_comp_cos hsin hd)

/-- A local Lipschitz bound bounds the derivative. -/
theorem abs_deriv_le_of_eventually_lipschitz {g : ℝ → ℝ} {x L : ℝ} (hL : 0 ≤ L)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ → |g (x + h) - g x| ≤ L * |h|) :
    |deriv g x| ≤ L := by
  by_cases hd : DifferentiableAt ℝ g x
  · obtain ⟨δ, hδ, hb⟩ := h
    have hslope : Tendsto (slope g x) (𝓝[≠] x) (𝓝 (deriv g x)) := hd.hasDerivAt.tendsto_slope
    have hbd : ∀ᶠ y in 𝓝[≠] x, |slope g x y| ≤ L := by
      have h1 : ∀ᶠ y in 𝓝[≠] x, |y - x| < δ := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy _
        simpa [Real.dist_eq] using hy
      filter_upwards [h1, self_mem_nhdsWithin] with y hy hyne
      have hyne' : y ≠ x := hyne
      have h2 : |g (x + (y - x)) - g x| ≤ L * |y - x| :=
        hb (y - x) (by simpa [abs_pos] using sub_ne_zero.mpr hyne') (by simpa using hy)
      rw [show x + (y - x) = y from by ring] at h2
      rw [slope_def_field, abs_div, div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hyne'))]
      exact h2
    rw [abs_le]
    exact ⟨ge_of_tendsto hslope (by filter_upwards [hbd] with y hy using (abs_le.mp hy).1),
           le_of_tendsto hslope (by filter_upwards [hbd] with y hy using (abs_le.mp hy).2)⟩
  · rw [deriv_zero_of_not_differentiableAt hd]; simpa using hL

/-- If `g` vanishes at points accumulating at `u` and is differentiable at `u`, then `g u = 0`
and `deriv g u = 0`. -/
theorem deriv_eq_zero_of_frequently_zero {g : ℝ → ℝ} {u : ℝ} (hd : DifferentiableAt ℝ g u)
    (h : ∀ δ : ℝ, 0 < δ → ∃ v : ℝ, |v - u| < δ ∧ v ≠ u ∧ g v = 0) :
    g u = 0 ∧ deriv g u = 0 := by
  choose v hv using fun n : ℕ => h (1 / (n + 1)) (by positivity)
  have hv1 : ∀ n : ℕ, |v n - u| < 1 / (n + 1) := fun n => (hv n).1
  have hvne : ∀ n : ℕ, v n ≠ u := fun n => (hv n).2.1
  have hvz : ∀ n : ℕ, g (v n) = 0 := fun n => (hv n).2.2
  have hvu : Tendsto v atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using le_of_lt (hv1 n)
  have hgu : g u = 0 := by
    have h1 : Tendsto (fun n => g (v n)) atTop (𝓝 (g u)) := hd.continuousAt.tendsto.comp hvu
    have h2 : Tendsto (fun n => g (v n)) atTop (𝓝 0) := by
      simp only [hvz]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  refine ⟨hgu, ?_⟩
  have hslope : Tendsto (slope g u) (𝓝[≠] u) (𝓝 (deriv g u)) := hd.hasDerivAt.tendsto_slope
  have hmem : Tendsto v atTop (𝓝[≠] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hvu, eventually_atTop.mpr ⟨0, fun n _ => hvne n⟩⟩
  have h1 : Tendsto (fun n => slope g u (v n)) atTop (𝓝 (deriv g u)) := hslope.comp hmem
  have h2 : Tendsto (fun n => slope g u (v n)) atTop (𝓝 0) := by
    have hzero : ∀ n : ℕ, slope g u (v n) = 0 := by
      intro n
      rw [slope_def_field, hvz n, hgu, sub_zero, zero_div]
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- The derivative of `v ↦ 2 * R v / v ^ 2` at a point where `R` is differentiable. -/
theorem hasDerivAt_two_mul_div_sq (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : DifferentiableAt ℝ R v) :
    HasDerivAt (fun v : ℝ => 2 * R v / v ^ 2) (2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3) v := by
  have h2 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * v) v := by simpa using hasDerivAt_pow 2 v
  have hnum : HasDerivAt (fun v : ℝ => 2 * R v) (2 * deriv R v) v := hd.hasDerivAt.const_mul 2
  have h := hnum.div h2 (by simpa using hv)
  have hval : (2 * deriv R v * v ^ 2 - 2 * R v * (2 * v)) / (v ^ 2) ^ 2
      = 2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3 := by
    field_simp
    ring
  rw [hval] at h
  have hfun : ((fun v : ℝ => 2 * R v) / fun v : ℝ => v ^ 2) = fun v : ℝ => 2 * R v / v ^ 2 := by
    funext y; rfl
  rwa [hfun] at h

/-- `v ↦ 2 * R v / v ^ 2` is differentiable where `R` is. -/
theorem differentiableAt_two_mul_div_sq (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : DifferentiableAt ℝ R v) :
    DifferentiableAt ℝ (fun v : ℝ => 2 * R v / v ^ 2) v :=
  (hasDerivAt_two_mul_div_sq R hv hd).differentiableAt

/-- Quotient rule for `v ↦ 2 * R v / v ^ 2` at a point where `R` is differentiable. -/
theorem deriv_two_mul_div_sq (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ R v) :
    deriv (fun v : ℝ => 2 * R v / v ^ 2) v = 2 * deriv R v / v ^ 2 - 4 * R v / v ^ 3 :=
  (hasDerivAt_two_mul_div_sq R hv hd).deriv

/-- The derivative of `v ↦ 2 * R v / v` at a point where `R` is differentiable. -/
theorem hasDerivAt_two_mul_div (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : DifferentiableAt ℝ R v) :
    HasDerivAt (fun v : ℝ => 2 * R v / v) (2 * deriv R v / v - 2 * R v / v ^ 2) v := by
  have h2 : HasDerivAt (fun v : ℝ => v) 1 v := hasDerivAt_id v
  have hnum : HasDerivAt (fun v : ℝ => 2 * R v) (2 * deriv R v) v := hd.hasDerivAt.const_mul 2
  have h := hnum.div h2 (by simpa using hv)
  have hval : (2 * deriv R v * v - 2 * R v * 1) / v ^ 2 = 2 * deriv R v / v - 2 * R v / v ^ 2 := by
    field_simp
  rw [hval] at h
  have hfun : ((fun v : ℝ => 2 * R v) / fun v : ℝ => v) = fun v : ℝ => 2 * R v / v := by
    funext y; rfl
  rwa [hfun] at h

/-- `v ↦ 2 * R v / v` is differentiable where `R` is. -/
theorem differentiableAt_two_mul_div (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : DifferentiableAt ℝ R v) :
    DifferentiableAt ℝ (fun v : ℝ => 2 * R v / v) v :=
  (hasDerivAt_two_mul_div R hv hd).differentiableAt

/-- Quotient rule for `v ↦ 2 * R v / v` at a point where `R` is differentiable. -/
theorem deriv_two_mul_div (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ R v) :
    deriv (fun v : ℝ => 2 * R v / v) v = 2 * deriv R v / v - 2 * R v / v ^ 2 :=
  (hasDerivAt_two_mul_div R hv hd).deriv

/-- `v ↦ 2 * R v / v ^ 2` is not differentiable where `R` is not. -/
theorem not_differentiableAt_two_mul_div_sq (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : ¬ DifferentiableAt ℝ R v) :
    ¬ DifferentiableAt ℝ (fun v : ℝ => 2 * R v / v ^ 2) v := by
  intro hF
  refine hd ?_
  have heq : R =ᶠ[𝓝 v] (fun v : ℝ => (v ^ 2 / 2) * (2 * R v / v ^ 2)) := by
    filter_upwards [eventually_ne_nhds hv] with y hy
    field_simp
  exact heq.differentiableAt_iff.mpr
    ((by fun_prop : DifferentiableAt ℝ (fun v : ℝ => v ^ 2 / 2) v).mul hF)

/-- `v ↦ 2 * R v / v` is not differentiable where `R` is not. -/
theorem not_differentiableAt_two_mul_div (R : ℝ → ℝ) {v : ℝ} (hv : v ≠ 0)
    (hd : ¬ DifferentiableAt ℝ R v) :
    ¬ DifferentiableAt ℝ (fun v : ℝ => 2 * R v / v) v := by
  intro hF
  refine hd ?_
  have heq : R =ᶠ[𝓝 v] (fun v : ℝ => (v / 2) * (2 * R v / v)) := by
    filter_upwards [eventually_ne_nhds hv] with y hy
    field_simp
  exact heq.differentiableAt_iff.mpr
    ((by fun_prop : DifferentiableAt ℝ (fun v : ℝ => v / 2) v).mul hF)

/-- An affine Lipschitz bound (with a linear-in-`h` extra term) bounds the derivative. -/
theorem abs_deriv_le_of_eventually_lipschitz_affine {g : ℝ → ℝ} {x L E : ℝ} (hL : 0 ≤ L)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      |g (x + h) - g x| ≤ (L + E * |h|) * |h|) :
    |deriv g x| ≤ L := by
  by_cases hd : DifferentiableAt ℝ g x
  · obtain ⟨δ, hδ, hb⟩ := h
    have hslope : Tendsto (slope g x) (𝓝[≠] x) (𝓝 (deriv g x)) := hd.hasDerivAt.tendsto_slope
    have hbd : ∀ᶠ y in 𝓝[≠] x, |slope g x y| ≤ L + E * |y - x| := by
      have h1 : ∀ᶠ y in 𝓝[≠] x, |y - x| < δ := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy _
        simpa [Real.dist_eq] using hy
      filter_upwards [h1, self_mem_nhdsWithin] with y hy hyne
      have hyne' : y ≠ x := hyne
      have h2 : |g (x + (y - x)) - g x| ≤ (L + E * |y - x|) * |y - x| :=
        hb (y - x) (by simpa [abs_pos] using sub_ne_zero.mpr hyne') (by simpa using hy)
      rw [show x + (y - x) = y from by ring] at h2
      rw [slope_def_field, abs_div, div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hyne'))]
      exact h2
    have htend : Tendsto (fun y : ℝ => L + E * |y - x|) (𝓝[≠] x) (𝓝 L) := by
      have h0 : Tendsto (fun y : ℝ => y - x) (𝓝[≠] x) (𝓝 0) := by
        have hbase : Tendsto (fun y : ℝ => y - x) (𝓝 x) (𝓝 ((x:ℝ) - x)) :=
          tendsto_id.sub tendsto_const_nhds
        rw [sub_self] at hbase
        exact hbase.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun y : ℝ => |y - x|) (𝓝[≠] x) (𝓝 0) := by simpa using h0.abs
      simpa using ((tendsto_const_nhds (x := L)).add (h1.const_mul E))
    exact le_of_tendsto_of_tendsto hslope.abs htend hbd
  · rw [deriv_zero_of_not_differentiableAt hd]
    simpa using hL

/-- From `HasDerivAt f f' x` one gets a two-sided linear bound on the increment. -/
theorem exists_bound_of_hasDerivAt {f : ℝ → ℝ} {x f' : ℝ} (h : HasDerivAt f f' x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → |f (x + t) - f x| ≤ (|f'| + 1) * |t| := by
  have hslope : Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') := h.tendsto_slope
  have h1 : ∀ᶠ y in 𝓝[≠] x, dist (slope f x y) f' < 1 :=
    hslope.eventually (Metric.ball_mem_nhds f' (by norm_num : (0:ℝ) < 1))
  rw [eventually_nhdsWithin_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
  refine ⟨δ, hδ, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    simp
  have ht' : dist (x + t) x < δ := by
    rw [Real.dist_eq]; simpa using ht
  have hne : x + t ≠ x := by
    intro hc
    exact ht0 (by linarith)
  have h2 : dist (slope f x (x + t)) f' < 1 := hδ' ht' hne
  rw [Real.dist_eq] at h2
  have h3 : |slope f x (x + t)| ≤ |f'| + 1 := by
    have h4 := abs_sub_lt_iff.mp h2
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le f', h4.2], by linarith [le_abs_self f', h4.1]⟩
  have hslopeval : slope f x (x + t) = (f (x + t) - f x) / t := by
    rw [slope_def_field, show x + t - x = t from by ring]
  rw [hslopeval, abs_div, div_le_iff₀ (abs_pos.mpr ht0)] at h3
  exact h3

/-- `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rw [abs_neg] at h
  calc |a - b| = |a + -b| := by ring_nf
    _ ≤ |a| + |b| := h

end Work.OddVolterra.Free
