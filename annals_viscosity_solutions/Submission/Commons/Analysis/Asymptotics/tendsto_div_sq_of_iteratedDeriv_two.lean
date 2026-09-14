import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Asymptotics

open Filter MeasureTheory
open scoped Topology Interval

set_option autoImplicit false

private lemma tendsto_sub_div_sq (a : ℝ) :
    Tendsto (fun t : ℝ => (t - a) / t ^ 2) atTop (𝓝 0) := by
  have h : (fun t : ℝ => (t - a) / t ^ 2) =ᶠ[atTop]
      fun t : ℝ => (1 - a * t⁻¹) * t⁻¹ := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  refine Tendsto.congr' h.symm ?_
  have h1 : Tendsto (fun t : ℝ => 1 - a * t⁻¹) atTop (𝓝 1) := by
    have h2 : Tendsto (fun t : ℝ => a * t⁻¹) atTop (𝓝 (a * 0)) :=
      tendsto_inv_atTop_zero.const_mul a
    simpa using (tendsto_const_nhds.sub h2)
  simpa using h1.mul tendsto_inv_atTop_zero

private lemma tendsto_sub_sq_div_sq (a : ℝ) :
    Tendsto (fun t : ℝ => (t - a) ^ 2 / t ^ 2) atTop (𝓝 1) := by
  have h : (fun t : ℝ => (t - a) ^ 2 / t ^ 2) =ᶠ[atTop]
      fun t : ℝ => (1 - a * t⁻¹) ^ 2 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp
  refine Tendsto.congr' h.symm ?_
  have h1 : Tendsto (fun t : ℝ => 1 - a * t⁻¹) atTop (𝓝 1) := by
    have h2 : Tendsto (fun t : ℝ => a * t⁻¹) atTop (𝓝 (a * 0)) :=
      tendsto_inv_atTop_zero.const_mul a
    simpa using (tendsto_const_nhds.sub h2)
  have h3 : Tendsto (fun t : ℝ => (1 - a * t⁻¹) ^ 2) atTop (𝓝 (1 ^ 2)) := h1.pow 2
  simpa using h3

private lemma tendsto_inv_sq :
    Tendsto (fun t : ℝ => (t ^ 2)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h2 := h.pow 2
  simpa [inv_pow] using h2

private lemma abs_weighted_integral_le {a A t ε : ℝ} {g : ℝ → ℝ}
    (haA : a ≤ A) (hAt : A ≤ t) (hcont : ContinuousOn g (Set.Ici a)) (_hε : 0 ≤ ε)
    (hbound : ∀ s ∈ Set.Icc A t, |g s| ≤ ε) :
    |∫ s in a..t, (t - s) * g s| ≤ (t - a) * (∫ s in a..A, |g s|) + ε * (t - A) ^ 2 := by
  have hat : a ≤ t := le_trans haA hAt
  have hcontA : ContinuousOn (fun s : ℝ => (t - s) * |g s|) (Set.uIcc a A) := by
    rw [Set.uIcc_of_le haA]
    exact (continuousOn_const.sub continuousOn_id).mul
      ((hcont.mono (fun x hx => hx.1)).abs)
  have hcontAt : ContinuousOn (fun s : ℝ => (t - s) * |g s|) (Set.uIcc A t) := by
    rw [Set.uIcc_of_le hAt]
    exact (continuousOn_const.sub continuousOn_id).mul
      ((hcont.mono (fun x hx => le_trans haA hx.1)).abs)
  have hintA : IntervalIntegrable (fun s : ℝ => (t - s) * |g s|) volume a A :=
    hcontA.intervalIntegrable
  have hintAt : IntervalIntegrable (fun s : ℝ => (t - s) * |g s|) volume A t :=
    hcontAt.intervalIntegrable
  have hnorm0 := intervalIntegral.norm_integral_le_integral_norm
    (a := a) (b := t) (f := fun s : ℝ => (t - s) * g s) (μ := volume) hat
  have hnorm : |∫ s in a..t, (t - s) * g s| ≤ ∫ s in a..t, (t - s) * |g s| := by
    rw [Real.norm_eq_abs] at hnorm0
    refine hnorm0.trans (le_of_eq ?_)
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hat] at hs
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  have hsplit : (∫ s in a..t, (t - s) * |g s|)
      = (∫ s in a..A, (t - s) * |g s|) + ∫ s in A..t, (t - s) * |g s| :=
    (intervalIntegral.integral_add_adjacent_intervals hintA hintAt).symm
  have hA1 : (∫ s in a..A, (t - s) * |g s|) ≤ (t - a) * (∫ s in a..A, |g s|) := by
    have hint2 : IntervalIntegrable (fun s : ℝ => (t - a) * |g s|) volume a A := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le haA]
      exact continuousOn_const.mul ((hcont.mono (fun x hx => hx.1)).abs)
    have hmono := intervalIntegral.integral_mono_on haA hintA hint2 (fun s hs => by
      exact mul_le_mul_of_nonneg_right (by linarith [hs.1]) (abs_nonneg _))
    rwa [intervalIntegral.integral_const_mul] at hmono
  have hA2 : (∫ s in A..t, (t - s) * |g s|) ≤ ε * (t - A) ^ 2 := by
    have hint3 : IntervalIntegrable (fun _ : ℝ => (t - A) * ε) volume A t :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hAt hintAt hint3 (fun s hs => by
      have h2 : |g s| ≤ ε := hbound s hs
      have h3 : 0 ≤ t - A := by linarith
      exact mul_le_mul (by linarith [hs.1]) h2 (abs_nonneg _) h3)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    have heq : (t - A) * ((t - A) * ε) = ε * (t - A) ^ 2 := by ring
    rwa [heq] at hmono
  calc |∫ s in a..t, (t - s) * g s|
      ≤ ∫ s in a..t, (t - s) * |g s| := hnorm
    _ = (∫ s in a..A, (t - s) * |g s|) + ∫ s in A..t, (t - s) * |g s| := hsplit
    _ ≤ (t - a) * (∫ s in a..A, |g s|) + ε * (t - A) ^ 2 := add_le_add hA1 hA2

private lemma tendsto_div_sq_weighted_integral_aux {a : ℝ} {g : ℝ → ℝ}
    (hgc : ContinuousOn g (Set.Ici a)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => (∫ s in a..t, (t - s) * g s) / t ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, ∀ s ≥ A₀, |g s| < ε / 8 := by
    have h := (Metric.tendsto_nhds.mp hg) (ε / 8) hε8
    rw [eventually_atTop] at h
    obtain ⟨A₀, hA₀⟩ := h
    exact ⟨A₀, fun s hs => by simpa [Real.dist_eq] using hA₀ s hs⟩
  set A := max A₀ a with hAdef
  have haA : a ≤ A := le_max_right _ _
  have hA₀A : A₀ ≤ A := le_max_left _ _
  have hbdA : ∀ s ≥ A, |g s| < ε / 8 := fun s hs => hA₀ s (le_trans hA₀A hs)
  have hlim1 : Tendsto (fun t : ℝ => (∫ s in a..A, |g s|) * (t - a) / t ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_sub_div_sq a).const_mul (∫ s in a..A, |g s|)
    simpa [mul_div_assoc] using h
  have hlim2 : Tendsto (fun t : ℝ => (t - A) ^ 2 / t ^ 2) atTop (𝓝 1) :=
    tendsto_sub_sq_div_sq A
  have hev1 : ∀ᶠ t in atTop, (∫ s in a..A, |g s|) * (t - a) / t ^ 2 ≤ ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hlim1) (ε / 4) (by positivity)
    filter_upwards [h] with t ht
    rw [Real.dist_eq, sub_zero] at ht
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) ht)
  have hev2 : ∀ᶠ t in atTop, (t - A) ^ 2 / t ^ 2 ≤ 2 := by
    have h := (Metric.tendsto_nhds.mp hlim2) 1 one_pos
    filter_upwards [h] with t ht
    rw [Real.dist_eq] at ht
    linarith [(abs_lt.mp ht).2]
  filter_upwards [hev1, hev2, eventually_ge_atTop A, eventually_gt_atTop (0 : ℝ)]
    with t h1 h2 htA ht0
  have hb := abs_weighted_integral_le (g := g) haA htA hgc (show (0 : ℝ) ≤ ε / 8 by positivity)
    (fun s hs => le_of_lt (hbdA s hs.1))
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have hstep : ε / 8 * ((t - A) ^ 2 / t ^ 2) ≤ ε / 8 * 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc dist ((∫ s in a..t, (t - s) * g s) / t ^ 2) 0
      = |(∫ s in a..t, (t - s) * g s) / t ^ 2| := by rw [Real.dist_eq, sub_zero]
    _ = |∫ s in a..t, (t - s) * g s| / t ^ 2 := by rw [abs_div, abs_of_pos ht2]
    _ ≤ ((t - a) * (∫ s in a..A, |g s|) + ε / 8 * (t - A) ^ 2) / t ^ 2 :=
        div_le_div_of_nonneg_right hb (le_of_lt ht2)
    _ = (∫ s in a..A, |g s|) * (t - a) / t ^ 2 + ε / 8 * ((t - A) ^ 2 / t ^ 2) := by
        field_simp
    _ ≤ ε / 4 + ε / 8 * 2 := add_le_add h1 hstep
    _ = ε / 2 := by ring
    _ < ε := by linarith

private lemma sub_deriv_mul_eq_weighted_integral_aux {f : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hcont : ContinuousOn (fun s : ℝ => deriv (deriv f) s) (Set.Icc a t))
    (hf : ∀ x ∈ Set.Icc a t, ContDiffAt ℝ 2 f x) :
    f t - f a - deriv f a * (t - a) = ∫ s in a..t, (t - s) * deriv (deriv f) s := by
  have hderiv : ∀ s ∈ Set.uIcc a t,
      HasDerivAt (fun s : ℝ => f s + (t - s) * deriv f s) ((t - s) * deriv (deriv f) s) s := by
    intro s hs
    rw [Set.uIcc_of_le hat] at hs
    have hcd : ContDiffAt ℝ 2 f s := hf s hs
    have h1 : HasDerivAt f (deriv f s) s := (hcd.differentiableAt (by norm_num)).hasDerivAt
    have h1' : ContDiffAt ℝ 1 (deriv f) s := hcd.derivWithin (m := 1) (by norm_num)
    have h2 : HasDerivAt (deriv f) (deriv (deriv f) s) s :=
      (h1'.differentiableAt (by norm_num)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h4 : HasDerivAt (fun s : ℝ => (t - s) * deriv f s)
        ((-1) * deriv f s + (t - s) * deriv (deriv f) s) s := h3.mul h2
    have h5 := h1.add h4
    refine h5.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun s : ℝ => (t - s) * deriv (deriv f) s) volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hat]
    exact (continuousOn_const.sub continuousOn_id).mul hcont
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  ring

lemma tendsto_div_sq_of_iteratedDeriv_two {f : ℝ → ℝ} {M T : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ici T))
    (hM : Tendsto (fun t : ℝ => iteratedDeriv 2 f t) atTop (𝓝 M)) :
    Tendsto (fun t : ℝ => f t / t ^ 2) atTop (𝓝 (M / 2)) := by
  have hfun : (fun t : ℝ => iteratedDeriv 2 f t) = fun t => deriv (deriv f) t := by
    funext t
    simp [iteratedDeriv_succ]
  rw [hfun] at hM
  set a : ℝ := T + 1 with hadef
  have haT : T < a := by simp [hadef]
  have hcont : ContinuousOn (fun s : ℝ => deriv (deriv f) s) (Set.Ici a) := by
    intro x hx
    have hxT : T < x := lt_of_lt_of_le haT hx
    have hcd : ContDiffAt ℝ 2 f x := hf.contDiffAt (Ici_mem_nhds hxT)
    have h2 : ContDiffAt ℝ 0 (deriv (deriv f)) x :=
      (hcd.derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)
    exact h2.continuousAt.continuousWithinAt
  have hcontIcc : ∀ t, a ≤ t → ContinuousOn (fun s : ℝ => deriv (deriv f) s) (Set.Icc a t) :=
    fun t _ => hcont.mono (fun x hx => hx.1)
  have hcdIcc : ∀ t, a ≤ t → ∀ x ∈ Set.Icc a t, ContDiffAt ℝ 2 f x := by
    intro t _ x hx
    have hxT : T < x := lt_of_lt_of_le haT hx.1
    exact hf.contDiffAt (Ici_mem_nhds hxT)
  -- the `g` whose weighted integral converges to zero
  set g : ℝ → ℝ := fun s => deriv (deriv f) s - M with hgdef
  have hgc : ContinuousOn g (Set.Ici a) := hcont.sub continuousOn_const
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => M) atTop (𝓝 M) := tendsto_const_nhds
    have h := hM.sub hc
    simpa [g] using h
  -- identity: f t - (f a + f' a (t-a) + M (t-a)^2/2) = ∫ (t-s) (f'' s - M)
  have hintOf : ∀ t, a ≤ t →
      IntervalIntegrable (fun s : ℝ => (t - s) * deriv (deriv f) s) volume a t := by
    intro t hat
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hat]
    exact (continuousOn_const.sub continuousOn_id).mul (hcontIcc t hat)
  have hintM : ∀ t : ℝ, IntervalIntegrable (fun s : ℝ => (t - s) * M) volume a t := by
    intro t
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.sub continuousOn_id).mul continuousOn_const
  have h_int_M : ∀ t : ℝ, ∫ s in a..t, (t - s) * M = M * (t - a) ^ 2 / 2 := by
    intro t
    rw [intervalIntegral.integral_mul_const]
    have hderiv : ∀ s ∈ Set.uIcc a t,
        HasDerivAt (fun s : ℝ => t * s - s ^ 2 / 2) (t - s) s := by
      intro s hs
      have h1 : HasDerivAt (fun s : ℝ => t * s) t s := by
        simpa using (hasDerivAt_id s).const_mul t
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        have hh := ((hasDerivAt_id s).pow 2).div_const 2
        simpa using hh
      have h3 := h1.sub h2
      exact h3.congr_deriv rfl
    have hint : IntervalIntegrable (fun s : ℝ => t - s) volume a t := by
      apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.sub continuousOn_id
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [h]
    ring
  have heq : ∀ t, a ≤ t →
      f t - (f a + deriv f a * (t - a) + M * (t - a) ^ 2 / 2)
        = ∫ s in a..t, (t - s) * g s := by
    intro t hat
    have h1 := sub_deriv_mul_eq_weighted_integral_aux hat (hcontIcc t hat) (hcdIcc t hat)
    have h2 : ∫ s in a..t, (t - s) * g s
        = ∫ s in a..t, ((t - s) * deriv (deriv f) s - (t - s) * M) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [g]
      ring
    rw [h2, intervalIntegral.integral_sub (hintOf t hat) (hintM t), h_int_M t, ← h1]
    ring
  -- the error tends to zero
  have hE : Tendsto (fun t : ℝ =>
      (f t - (f a + deriv f a * (t - a) + M * (t - a) ^ 2 / 2)) / t ^ 2) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_div_sq_weighted_integral_aux hgc hg0)
    filter_upwards [eventually_ge_atTop a] with t ht
    rw [heq t ht]
  -- the main term tends to `M / 2`
  have h1a : Tendsto (fun t : ℝ => f a / t ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_sq.const_mul (f a)
  have h1b : Tendsto (fun t : ℝ => deriv f a * (t - a) / t ^ 2) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using (tendsto_sub_div_sq a).const_mul (deriv f a)
  have hP1 : Tendsto (fun t : ℝ => (f a + deriv f a * (t - a)) / t ^ 2) atTop (𝓝 0) := by
    have hsplit : (fun t : ℝ => (f a + deriv f a * (t - a)) / t ^ 2)
        = fun t : ℝ => f a / t ^ 2 + deriv f a * (t - a) / t ^ 2 := by
      funext t
      rw [add_div]
    rw [hsplit]
    simpa using h1a.add h1b
  have hP2 : Tendsto (fun t : ℝ => M / 2 * (t - a) ^ 2 / t ^ 2) atTop (𝓝 (M / 2)) := by
    have h := (tendsto_sub_sq_div_sq a).const_mul (M / 2)
    simpa [mul_div_assoc] using h
  have hP : Tendsto (fun t : ℝ =>
      (f a + deriv f a * (t - a)) / t ^ 2 + M / 2 * (t - a) ^ 2 / t ^ 2)
      atTop (𝓝 (M / 2)) := by
    simpa using hP1.add hP2
  have hsum := hP.add hE
  have hev : (fun t : ℝ => f t / t ^ 2) =ᶠ[atTop] fun t : ℝ =>
      (f a + deriv f a * (t - a)) / t ^ 2 + M / 2 * (t - a) ^ 2 / t ^ 2
        + (f t - (f a + deriv f a * (t - a) + M * (t - a) ^ 2 / 2)) / t ^ 2 := by
    filter_upwards with t
    rw [← add_div, ← add_div]
    congr 1
    ring
  simpa using hsum.congr' hev.symm

end Commons.Analysis.Asymptotics