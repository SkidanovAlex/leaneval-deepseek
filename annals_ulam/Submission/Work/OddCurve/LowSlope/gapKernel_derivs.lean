import Mathlib

namespace Work.OddCurve.LowSlope

open scoped Interval Topology
open Set Filter MeasureTheory

noncomputable section

/-!
# Derivatives of the "gap kernel" integrals

This file differentiates, three times in a row, the family of integrals

`v ↦ ∫ c in m..M', c * Φ c * ((v^2 - c^2) ^ p)`

(with `p = -1/2, -3/2, -5/2`) under the integral sign.  Since `0 ≤ m ≤ M' < 79/100 < u`,
the whole integration range lies strictly below `u` and `v^2 - c^2` is bounded away from `0`
on a neighbourhood of `u`; everything is therefore a routine dominated–convergence argument
with the chain of scalar kernels

* `f₁ = (v²-c²)^{-1/2}`,       `∂_v f₁ = -v (v²-c²)^{-3/2} =: f₂`
* `f₂ = -v (v²-c²)^{-3/2}`,    `∂_v f₂ = (2v²+c²) (v²-c²)^{-5/2} =: f₃`
* `f₃ = (2v²+c²) (v²-c²)^{-5/2}`, `∂_v f₃ = (-6v³-9vc²) (v²-c²)^{-7/2} =: f₄`.
-/

/-! ## Scalar kernels: derivatives in the first variable -/

/-- `d/dx (x²-t²)^p = p (x²-t²)^{p-1} · 2x` away from `x² = t²`. -/
lemma gapKernel_hasDerivAt_sq_sub_rpow {t p x : ℝ} (h : x^2 - t^2 ≠ 0) :
    HasDerivAt (fun y : ℝ => (y^2 - t^2)^p) (p * (x^2 - t^2)^(p-1) * (2*x)) x := by
  have ha : HasDerivAt (fun y : ℝ => y^2 - t^2) (2*x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const (t^2) using 1
    all_goals try rfl
    all_goals (simp only [id_eq]; ring)
  have hpow := (Real.hasDerivAt_rpow_const (x := x^2 - t^2) (p := p) (Or.inl h)).comp x ha
  convert hpow using 1
  all_goals try rfl

/-- `(x²-t²)^{-3/2} = (x²-t²)·(x²-t²)^{-5/2}`. -/
lemma gapKernel_rpow3 {t x : ℝ} (h : 0 < x^2 - t^2) :
    (x^2 - t^2)^(-(3/2:ℝ)) = (x^2 - t^2) * (x^2 - t^2)^(-(5/2:ℝ)) := by
  rw [show (-(3/2:ℝ)) = 1 + (-(5/2:ℝ)) by norm_num, Real.rpow_add h, Real.rpow_one]

/-- `(x²-t²)^{-5/2} = (x²-t²)·(x²-t²)^{-7/2}`. -/
lemma gapKernel_rpow5 {t x : ℝ} (h : 0 < x^2 - t^2) :
    (x^2 - t^2)^(-(5/2:ℝ)) = (x^2 - t^2) * (x^2 - t^2)^(-(7/2:ℝ)) := by
  rw [show (-(5/2:ℝ)) = 1 + (-(7/2:ℝ)) by norm_num, Real.rpow_add h, Real.rpow_one]

/-- Derivative of the first kernel. -/
lemma gapKernel_d1 {t x : ℝ} (h : 0 < x^2 - t^2) :
    HasDerivAt (fun y : ℝ => (y^2 - t^2)^(-(1/2:ℝ))) (-x * (x^2-t^2)^(-(3/2:ℝ))) x := by
  have hd := gapKernel_hasDerivAt_sq_sub_rpow (t := t) (p := -(1/2:ℝ)) (x := x) (ne_of_gt h)
  have hv : (-(1/2:ℝ)) * (x^2 - t^2)^((-(1/2:ℝ)) - 1) * (2*x)
      = -x * (x^2-t^2)^(-(3/2:ℝ)) := by
    rw [show (-(1/2:ℝ) - 1 : ℝ) = -(3/2) by norm_num]; ring
  exact hd.congr_deriv hv

/-- Derivative of the second kernel. -/
lemma gapKernel_d2 {t x : ℝ} (h : 0 < x^2 - t^2) :
    HasDerivAt (fun y : ℝ => -y * (y^2 - t^2)^(-(3/2:ℝ)))
      ((2*x^2 + t^2) * (x^2-t^2)^(-(5/2:ℝ))) x := by
  have hm : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    convert (hasDerivAt_id x).neg using 1
    all_goals try rfl
  have hp := gapKernel_hasDerivAt_sq_sub_rpow (t := t) (p := -(3/2:ℝ)) (x := x) (ne_of_gt h)
  have hmul := hm.mul hp
  have hv : (-1) * (x^2 - t^2)^(-(3/2:ℝ))
        + (-x) * ((-(3/2:ℝ)) * (x^2 - t^2)^((-(3/2:ℝ)) - 1) * (2*x))
      = (2*x^2 + t^2) * (x^2-t^2)^(-(5/2:ℝ)) := by
    rw [show (-(3/2:ℝ) - 1 : ℝ) = -(5/2) by norm_num]
    rw [gapKernel_rpow3 h]
    ring
  convert hmul.congr_deriv hv using 1
  all_goals try rfl

/-- Derivative of the third kernel. -/
lemma gapKernel_d3 {t x : ℝ} (h : 0 < x^2 - t^2) :
    HasDerivAt (fun y : ℝ => (2*y^2 + t^2) * (y^2 - t^2)^(-(5/2:ℝ)))
      ((-(6*x^3) - 9*x*t^2) * (x^2-t^2)^(-(7/2:ℝ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2*y^2 + t^2) (2*(2*x)) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul 2).add_const (t^2)) using 1
    all_goals try rfl
    all_goals (simp only [id_eq]; ring)
  have hp := gapKernel_hasDerivAt_sq_sub_rpow (t := t) (p := -(5/2:ℝ)) (x := x) (ne_of_gt h)
  have hmul := h1.mul hp
  have hv : (2*(2*x)) * (x^2 - t^2)^(-(5/2:ℝ))
        + (2*x^2 + t^2) * ((-(5/2:ℝ)) * (x^2 - t^2)^((-(5/2:ℝ)) - 1) * (2*x))
      = (-(6*x^3) - 9*x*t^2) * (x^2-t^2)^(-(7/2:ℝ)) := by
    rw [show (-(5/2:ℝ) - 1 : ℝ) = -(7/2) by norm_num]
    rw [gapKernel_rpow5 h]
    ring
  convert hmul.congr_deriv hv using 1
  all_goals try rfl

/-! ## Differentiation under the integral sign -/

/-- Differentiation under the integral sign for a family of kernels `F x t` with `x`-derivative
`F' x t` uniformly bounded on a neighbourhood of the point. -/
lemma gapKernel_integral_hasDerivAt {m M' u δ C : ℝ} (hmM' : m ≤ M') (hδ : 0 < δ)
    {F F' : ℝ → ℝ → ℝ}
    (hF_cont : ∀ x ∈ Metric.ball u δ, ContinuousOn (F x) (Set.Icc m M'))
    (hF'_cont : ContinuousOn (F' u) (Set.Icc m M'))
    (hbound : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M', |F' x t| ≤ C)
    (hdiff : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
      HasDerivAt (fun y => F y t) (F' x t) x) :
    HasDerivAt (fun x => ∫ t in m..M', F x t) (∫ t in m..M', F' u t) u := by
  have hu_mem : u ∈ Metric.ball u δ := Metric.mem_ball_self hδ
  have hdt : ∀ t, t ∈ Set.uIoc m M' → t ∈ Set.Icc m M' := by
    intro t ht
    rw [Set.uIoc_of_le hmM'] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hF_meas : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc m M')) := by
    filter_upwards [Metric.ball_mem_nhds u hδ] with x hx
    exact ((hF_cont x hx).mono (fun t ht => hdt t ht)).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (F u) volume m M' := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hmM']
    exact hF_cont u hu_mem
  have hF'_meas : AEStronglyMeasurable (F' u) (volume.restrict (Set.uIoc m M')) :=
    (hF'_cont.mono (fun t ht => hdt t ht)).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc m M' →
      ∀ x ∈ Metric.ball u δ, ‖F' x t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards with t ht x hx
    rw [Real.norm_eq_abs]
    exact hbound x hx t (hdt t ht)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc m M' → ∀ x ∈ Metric.ball u δ,
      HasDerivAt (fun y => F y t) (F' x t) x := by
    filter_upwards with t ht x hx
    exact hdiff x hx t (hdt t ht)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ) (a := m) (b := M') (bound := fun _ : ℝ => C)
    (F := F) (F' := F') (x₀ := u) (s := Metric.ball u δ)
    (Metric.ball_mem_nhds u hδ) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const h_diff).2

/-! ## Continuity of the kernels -/

/-- Continuity of `t ↦ t Φ t (P t (q²-t²)^p)` on `[m,M']` when `M' < q` and `m ≥ 0`. -/
lemma gapKernel_cont_gen {m M' q : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M') (hq : M' < q)
    {Φ P : ℝ → ℝ} (hΦc : ContinuousOn Φ (Set.Icc m M')) (hP : ContinuousOn P (Set.Icc m M'))
    (p : ℝ) :
    ContinuousOn (fun t : ℝ => t * Φ t * (P t * (q^2 - t^2)^p)) (Set.Icc m M') := by
  have h1 : ContinuousOn (fun t : ℝ => t * Φ t) (Set.Icc m M') :=
    continuousOn_id.mul hΦc
  have h2 : ContinuousOn (fun t : ℝ => (q^2 - t^2)^p) (Set.Icc m M') := by
    apply ContinuousOn.rpow_const
    · exact (continuous_const.sub (continuous_id.pow 2)).continuousOn
    · intro t ht
      refine Or.inl ?_
      have ht0 : 0 ≤ t := le_trans hm0 ht.1
      have htM : t ≤ M' := ht.2
      nlinarith [hq, ht0, htM]
  exact h1.mul (hP.mul h2)

/-! ## Uniform bounds for the derivative kernels -/

/-- Bound for `|g t|` from `|Φ| ≤ B` on `[m,M']`. -/
lemma gapKernel_gbound {m M' B : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M') {Φ : ℝ → ℝ}
    (hΦb : ∀ c ∈ Set.Icc m M', |Φ c| ≤ B) {t : ℝ} (ht : t ∈ Set.Icc m M') :
    |t * Φ t| ≤ M' * B := by
  have hM'0 : 0 ≤ M' := le_trans hm0 hmM'
  have ht0 : 0 ≤ t := le_trans hm0 ht.1
  rw [abs_mul, abs_of_nonneg ht0]
  exact mul_le_mul ht.2 (hΦb t ht) (abs_nonneg _) hM'0

/-- Bound for the kernel `f₂ = -x (x²-t²)^{-3/2}`. -/
lemma gapKernel_bound_d2 {m M' u δ x t : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M')
    (huδ : M' < u - δ) (hx : x ∈ Set.Icc (u - δ) (u + δ)) (ht : t ∈ Set.Icc m M') :
    |(-x) * (x^2 - t^2)^(-(3/2:ℝ))| ≤ (u + δ) * ((u-δ)^2 - M'^2)^(-(3/2:ℝ)) := by
  have hM'0 : 0 ≤ M' := le_trans hm0 hmM'
  have huδ0 : 0 < u - δ := lt_of_le_of_lt hM'0 huδ
  have hx0 : 0 ≤ x := le_trans huδ0.le hx.1
  have ht0 : 0 ≤ t := le_trans hm0 ht.1
  have hρpos : 0 < (u-δ)^2 - M'^2 := by nlinarith [huδ, hM'0, huδ0]
  have hρle : (u-δ)^2 - M'^2 ≤ x^2 - t^2 := by nlinarith [hx.1, hx0, huδ0.le, ht0, ht.2]
  have hpos : 0 < x^2 - t^2 := lt_of_lt_of_le hρpos hρle
  have hrpow : (x^2 - t^2)^(-(3/2:ℝ)) ≤ ((u-δ)^2 - M'^2)^(-(3/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hρpos hρle (by norm_num)
  have hrpow0 : 0 ≤ (x^2 - t^2)^(-(3/2:ℝ)) := Real.rpow_nonneg hpos.le _
  rw [abs_mul, abs_neg, abs_of_nonneg hx0, abs_of_nonneg hrpow0]
  exact mul_le_mul hx.2 hrpow hrpow0 (le_trans hx0 hx.2)

/-- Bound for the kernel `f₃ = (2x²+t²)(x²-t²)^{-5/2}`. -/
lemma gapKernel_bound_d3 {m M' u δ x t : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M')
    (huδ : M' < u - δ) (hx : x ∈ Set.Icc (u - δ) (u + δ)) (ht : t ∈ Set.Icc m M') :
    |(2*x^2 + t^2) * (x^2 - t^2)^(-(5/2:ℝ))| ≤
      (2*(u + δ)^2 + M'^2) * ((u-δ)^2 - M'^2)^(-(5/2:ℝ)) := by
  have hM'0 : 0 ≤ M' := le_trans hm0 hmM'
  have huδ0 : 0 < u - δ := lt_of_le_of_lt hM'0 huδ
  have hx0 : 0 ≤ x := le_trans huδ0.le hx.1
  have ht0 : 0 ≤ t := le_trans hm0 ht.1
  have hρpos : 0 < (u-δ)^2 - M'^2 := by nlinarith [huδ, hM'0, huδ0]
  have hρle : (u-δ)^2 - M'^2 ≤ x^2 - t^2 := by nlinarith [hx.1, hx0, huδ0.le, ht0, ht.2]
  have hpos : 0 < x^2 - t^2 := lt_of_lt_of_le hρpos hρle
  have hrpow : (x^2 - t^2)^(-(5/2:ℝ)) ≤ ((u-δ)^2 - M'^2)^(-(5/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hρpos hρle (by norm_num)
  have hrpow0 : 0 ≤ (x^2 - t^2)^(-(5/2:ℝ)) := Real.rpow_nonneg hpos.le _
  have hpoly0 : 0 ≤ 2*x^2 + t^2 := by positivity
  have hpoly : 2*x^2 + t^2 ≤ 2*(u + δ)^2 + M'^2 := by
    nlinarith [hx.1, hx.2, hx0, ht0, ht.2, huδ0.le]
  rw [abs_mul, abs_of_nonneg hpoly0, abs_of_nonneg hrpow0]
  exact mul_le_mul hpoly hrpow hrpow0 (by positivity)

/-- Bound for the kernel `f₄ = (-6x³-9xt²)(x²-t²)^{-7/2}`. -/
lemma gapKernel_bound_d4 {m M' u δ x t : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M')
    (huδ : M' < u - δ) (hx : x ∈ Set.Icc (u - δ) (u + δ)) (ht : t ∈ Set.Icc m M') :
    |(-(6*x^3) - 9*x*t^2) * (x^2 - t^2)^(-(7/2:ℝ))| ≤
      (6*(u + δ)^3 + 9*(u + δ)*M'^2) * ((u-δ)^2 - M'^2)^(-(7/2:ℝ)) := by
  have hM'0 : 0 ≤ M' := le_trans hm0 hmM'
  have huδ0 : 0 < u - δ := lt_of_le_of_lt hM'0 huδ
  have hx0 : 0 ≤ x := le_trans huδ0.le hx.1
  have ht0 : 0 ≤ t := le_trans hm0 ht.1
  have hX0 : 0 ≤ u + δ := le_trans hx0 hx.2
  have hρpos : 0 < (u-δ)^2 - M'^2 := by nlinarith [huδ, hM'0, huδ0]
  have hρle : (u-δ)^2 - M'^2 ≤ x^2 - t^2 := by nlinarith [hx.1, hx0, huδ0.le, ht0, ht.2]
  have hpos : 0 < x^2 - t^2 := lt_of_lt_of_le hρpos hρle
  have hrpow : (x^2 - t^2)^(-(7/2:ℝ)) ≤ ((u-δ)^2 - M'^2)^(-(7/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hρpos hρle (by norm_num)
  have hrpow0 : 0 ≤ (x^2 - t^2)^(-(7/2:ℝ)) := Real.rpow_nonneg hpos.le _
  have hpoly0 : 0 ≤ 6*x^3 + 9*x*t^2 := by positivity
  have hpoly : 6*x^3 + 9*x*t^2 ≤ 6*(u + δ)^3 + 9*(u + δ)*M'^2 := by
    have hx2 : x^2 ≤ (u + δ)^2 := by nlinarith [hx.2, hx0, huδ0.le, hX0]
    have hx3 : x^3 ≤ (u + δ)^3 := by nlinarith [hx.2, hx0, hX0, hx2]
    have ht2 : t^2 ≤ M'^2 := by nlinarith [ht0, ht.2, hM'0]
    nlinarith [hx3, ht2, hx.2, ht.2, hx0, ht0, hX0, hM'0]
  have hkey : -(6*x^3) - 9*x*t^2 = -(6*x^3 + 9*x*t^2) := by ring
  rw [hkey, abs_mul, abs_neg, abs_of_nonneg hpoly0, abs_of_nonneg hrpow0]
  exact mul_le_mul hpoly hrpow hrpow0 (by positivity)

/-! ## The main statement -/

theorem gapKernel_derivs {m M' B : ℝ} (hm0 : 0 ≤ m) (hmM' : m ≤ M') (hM' : M' < (79/100 : ℝ)) {Φ : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Set.Icc m M')) (hΦb : ∀ c ∈ Set.Icc m M', |Φ c| ≤ B) :
    ∀ u ∈ Set.Ioo (79/100 : ℝ) (11/10),
      HasDerivAt (fun v : ℝ => ∫ c in m..M', c * Φ c * ((v:ℝ)^2 - c^2)^(-(1/2 : ℝ)))
        (∫ c in m..M', c * Φ c * (-u * ((u:ℝ)^2 - c^2)^(-(3/2 : ℝ)))) u ∧
      HasDerivAt (fun v : ℝ => ∫ c in m..M', c * Φ c * (-v * ((v:ℝ)^2 - c^2)^(-(3/2 : ℝ))))
        (∫ c in m..M', c * Φ c * ((2*(u:ℝ)^2 + c^2) * ((u:ℝ)^2 - c^2)^(-(5/2 : ℝ)))) u ∧
      HasDerivAt (fun v : ℝ => ∫ c in m..M', c * Φ c * ((2*(v:ℝ)^2 + c^2) * ((v:ℝ)^2 - c^2)^(-(5/2 : ℝ))))
        (∫ c in m..M', c * Φ c * ((-(6*(u:ℝ)^3) - 9*u*c^2) * ((u:ℝ)^2 - c^2)^(-(7/2 : ℝ)))) u := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  have hM'0 : 0 ≤ M' := le_trans hm0 hmM'
  have hM'u : M' < u := lt_trans hM' hu1
  set δ : ℝ := (u - M') / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have huδ : M' < u - δ := by rw [hδ]; linarith
  have hxIcc : ∀ x ∈ Metric.ball u δ, x ∈ Set.Icc (u - δ) (u + δ) := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    exact ⟨by linarith, by linarith⟩
  have hreg : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M', 0 < x^2 - t^2 := by
    intro x hx t ht
    have hxI := hxIcc x hx
    have huδ0 : 0 < u - δ := lt_of_le_of_lt hM'0 huδ
    have hx0 : 0 ≤ x := le_trans huδ0.le hxI.1
    have ht0 : 0 ≤ t := le_trans hm0 ht.1
    have hlt : t < x := lt_of_le_of_lt ht.2 (lt_of_lt_of_le huδ hxI.1)
    have h1 : 0 < x - t := sub_pos.mpr hlt
    have h2 : 0 < x + t := by linarith
    have h3 := mul_pos h1 h2
    nlinarith [h3]
  have hMB0 : 0 ≤ M' * B := mul_nonneg hM'0 (le_trans (abs_nonneg _) (hΦb m ⟨le_rfl, hmM'⟩))
  refine ⟨?_, ?_, ?_⟩
  · -- first derivative
    have hc1 : ∀ x ∈ Metric.ball u δ,
        ContinuousOn (fun t : ℝ => t * Φ t * ((x:ℝ)^2 - t^2)^(-(1/2:ℝ))) (Set.Icc m M') := by
      intro x hx
      have hxlt : M' < x := lt_of_lt_of_le huδ (hxIcc x hx).1
      have h := gapKernel_cont_gen (q := x) hm0 hmM' hxlt hΦc
        (P := fun _ : ℝ => (1:ℝ)) continuousOn_const (-(1/2:ℝ))
      simpa using h
    have hc1' : ContinuousOn (fun t : ℝ => t * Φ t * (-u * ((u:ℝ)^2 - t^2)^(-(3/2:ℝ))))
        (Set.Icc m M') := by
      have h := gapKernel_cont_gen (q := u) hm0 hmM' hM'u hΦc
        (P := fun _ : ℝ => -u) continuousOn_const (-(3/2:ℝ))
      simpa using h
    have hb1 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        |t * Φ t * (-x * ((x:ℝ)^2 - t^2)^(-(3/2:ℝ)))| ≤
          M' * B * ((u + δ) * ((u-δ)^2 - M'^2)^(-(3/2:ℝ))) := by
      intro x hx t ht
      have hxI := hxIcc x hx
      rw [abs_mul]
      exact mul_le_mul (gapKernel_gbound hm0 hmM' hΦb ht)
        (gapKernel_bound_d2 hm0 hmM' huδ hxI ht) (abs_nonneg _) hMB0
    have hd1 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        HasDerivAt (fun y : ℝ => t * Φ t * ((y:ℝ)^2 - t^2)^(-(1/2:ℝ)))
          (t * Φ t * (-x * ((x:ℝ)^2 - t^2)^(-(3/2:ℝ)))) x := by
      intro x hx t ht
      exact (gapKernel_d1 (hreg x hx t ht)).const_mul (t * Φ t)
    exact gapKernel_integral_hasDerivAt (m := m) (M' := M') (u := u) (δ := δ) hmM' hδpos hc1 hc1' hb1 hd1
  · -- second derivative
    have hc2 : ∀ x ∈ Metric.ball u δ,
        ContinuousOn (fun t : ℝ => t * Φ t * (-x * ((x:ℝ)^2 - t^2)^(-(3/2:ℝ)))) (Set.Icc m M') := by
      intro x hx
      have hxlt : M' < x := lt_of_lt_of_le huδ (hxIcc x hx).1
      have h := gapKernel_cont_gen (q := x) hm0 hmM' hxlt hΦc
        (P := fun _ : ℝ => -x) continuousOn_const (-(3/2:ℝ))
      simpa using h
    have hc2' : ContinuousOn (fun t : ℝ => t * Φ t * ((2*(u:ℝ)^2 + t^2) * ((u:ℝ)^2 - t^2)^(-(5/2:ℝ))))
        (Set.Icc m M') := by
      have h := gapKernel_cont_gen (q := u) hm0 hmM' hM'u hΦc
        (P := fun t : ℝ => 2*(u:ℝ)^2 + t^2)
        ((continuousOn_const).add (continuousOn_id.pow 2)) (-(5/2:ℝ))
      simpa using h
    have hb2 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        |t * Φ t * ((2*x^2 + t^2) * ((x:ℝ)^2 - t^2)^(-(5/2:ℝ)))| ≤
          M' * B * ((2*(u + δ)^2 + M'^2) * ((u-δ)^2 - M'^2)^(-(5/2:ℝ))) := by
      intro x hx t ht
      have hxI := hxIcc x hx
      rw [abs_mul]
      exact mul_le_mul (gapKernel_gbound hm0 hmM' hΦb ht)
        (gapKernel_bound_d3 hm0 hmM' huδ hxI ht) (abs_nonneg _) hMB0
    have hd2 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        HasDerivAt (fun y : ℝ => t * Φ t * (-y * ((y:ℝ)^2 - t^2)^(-(3/2:ℝ))))
          (t * Φ t * ((2*x^2 + t^2) * ((x:ℝ)^2 - t^2)^(-(5/2:ℝ)))) x := by
      intro x hx t ht
      exact (gapKernel_d2 (hreg x hx t ht)).const_mul (t * Φ t)
    have key := gapKernel_integral_hasDerivAt (m := m) (M' := M') (u := u) (δ := δ) (C := M' * B * ((2*(u + δ)^2 + M'^2) * ((u-δ)^2 - M'^2)^(-(5/2:ℝ)))) (F := fun (x : ℝ) (t : ℝ) => t * Φ t * (-x * ((x:ℝ)^2 - t^2)^(-(3/2:ℝ)))) (F' := fun (x : ℝ) (t : ℝ) => t * Φ t * ((2*x^2 + t^2) * ((x:ℝ)^2 - t^2)^(-(5/2:ℝ)))) hmM' hδpos hc2 hc2' hb2 hd2
    convert key using 1
  · -- third derivative
    have hc3 : ∀ x ∈ Metric.ball u δ,
        ContinuousOn (fun t : ℝ => t * Φ t * ((2*x^2 + t^2) * ((x:ℝ)^2 - t^2)^(-(5/2:ℝ))))
          (Set.Icc m M') := by
      intro x hx
      have hxlt : M' < x := lt_of_lt_of_le huδ (hxIcc x hx).1
      have h := gapKernel_cont_gen (q := x) hm0 hmM' hxlt hΦc
        (P := fun t : ℝ => 2*x^2 + t^2)
        ((continuousOn_const).add (continuousOn_id.pow 2)) (-(5/2:ℝ))
      simpa using h
    have hc3' : ContinuousOn
        (fun t : ℝ => t * Φ t * ((-(6*(u:ℝ)^3) - 9*u*t^2) * ((u:ℝ)^2 - t^2)^(-(7/2:ℝ))))
        (Set.Icc m M') := by
      have h := gapKernel_cont_gen (q := u) hm0 hmM' hM'u hΦc
        (P := fun t : ℝ => -(6*(u:ℝ)^3) - 9*u*t^2)
        ((continuousOn_const).sub ((continuousOn_const).mul (continuousOn_id.pow 2))) (-(7/2:ℝ))
      simpa using h
    have hb3 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        |t * Φ t * ((-(6*x^3) - 9*x*t^2) * ((x:ℝ)^2 - t^2)^(-(7/2:ℝ)))| ≤
          M' * B * ((6*(u + δ)^3 + 9*(u + δ)*M'^2) * ((u-δ)^2 - M'^2)^(-(7/2:ℝ))) := by
      intro x hx t ht
      have hxI := hxIcc x hx
      rw [abs_mul]
      exact mul_le_mul (gapKernel_gbound hm0 hmM' hΦb ht)
        (gapKernel_bound_d4 hm0 hmM' huδ hxI ht) (abs_nonneg _) hMB0
    have hd3 : ∀ x ∈ Metric.ball u δ, ∀ t ∈ Set.Icc m M',
        HasDerivAt (fun y : ℝ => t * Φ t * ((2*y^2 + t^2) * ((y:ℝ)^2 - t^2)^(-(5/2:ℝ))))
          (t * Φ t * ((-(6*x^3) - 9*x*t^2) * ((x:ℝ)^2 - t^2)^(-(7/2:ℝ)))) x := by
      intro x hx t ht
      exact (gapKernel_d3 (hreg x hx t ht)).const_mul (t * Φ t)
    have key := gapKernel_integral_hasDerivAt (m := m) (M' := M') (u := u) (δ := δ) (C := M' * B * ((6*(u + δ)^3 + 9*(u + δ)*M'^2) * ((u-δ)^2 - M'^2)^(-(7/2:ℝ)))) (F := fun (x : ℝ) (t : ℝ) => t * Φ t * ((2*x^2 + t^2) * ((x:ℝ)^2 - t^2)^(-(5/2:ℝ)))) (F' := fun (x : ℝ) (t : ℝ) => t * Φ t * ((-(6*x^3) - 9*x*t^2) * ((x:ℝ)^2 - t^2)^(-(7/2:ℝ)))) hmM' hδpos hc3 hc3' hb3 hd3
    convert key using 1

end

end Work.OddCurve.LowSlope
