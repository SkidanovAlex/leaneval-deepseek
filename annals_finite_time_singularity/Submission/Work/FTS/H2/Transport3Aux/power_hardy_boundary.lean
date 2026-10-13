import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Hardy inequality with a boundary term

For `a > -1`, `b > 0` and `f` of class `C¹` on `[0,b]`,

  `∫_0^b f(t)² t^a dt ≤ 4/(a+1)² ∫_0^b f'(t)² t^{a+2} dt + 2/(a+1) b^{a+1} f(b)²`.

This is the boundary-term version of the classical weighted Hardy inequality: writing
`φ(t) = f(t)² t^{a+1}`, one has `φ'(t) = 2 f f' t^{a+1} + (a+1) f² t^a` on `(0,b)` and
`φ → 0` at `0⁺` (since `a + 1 > 0`), so the fundamental theorem of calculus gives

  `(a+1) ∫_0^b f² t^a = f(b)² b^{a+1} - 2 ∫_0^b f f' t^{a+1}`.

Combining this with the weighted arithmetic--geometric mean inequality
`2 |f f'| t^{a+1} ≤ (a+1)/2 · f² t^a + 2/(a+1) · f'² t^{a+2}` (which is `2 X Y ≤ X² + Y²`
after rescaling) and `|∫ f f' t^{a+1}| ≤ ∫ |f f' t^{a+1}|` yields the claim with exactly the
stated constants.
-/

namespace Work.FTS.H2.Transport3Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- `t ↦ f t ^ 2 * t ^ (a + 1) → 0` as `t → 0⁺`, given that `f` is bounded near `0`. -/
private lemma phb_tendsto_zero {a b C : ℝ} (ha1 : 0 < a + 1) (hb : 0 < b) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hbf : ∀ t ∈ Set.Ioo 0 b, |f t| ≤ C) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
  have hmem : Set.Ioo 0 b ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Iio_mem_nhds hb] with t ht h0t
    exact ⟨h0t, ht⟩
  have hpoly : Tendsto (fun t : ℝ => t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (a + 1)) 0 :=
      Real.continuousAt_rpow_const 0 (a + 1) (Or.inr ha1.le)
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    rwa [Real.zero_rpow ha1.ne'] at h2
  have hg : Tendsto (fun t : ℝ => C ^ 2 * t ^ (a + 1)) (𝓝[>] 0) (𝓝 0) := by
    have h2 := (tendsto_const_nhds (x := C ^ 2) (f := 𝓝[>] (0 : ℝ))).mul hpoly
    simpa using h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hmem] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
  · filter_upwards [hmem] with t ht
    have h1 : f t ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hC]
      exact hbf t ht
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)

/-- `t ↦ f t ^ 2 * t ^ (a + 1) → f b ^ 2 * b ^ (a + 1)` as `t → b⁻`. -/
private lemma phb_tendsto_b {a b : ℝ} (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 b)) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (a + 1)) (𝓝[<] b) (𝓝 (f b ^ 2 * b ^ (a + 1))) := by
  have hle : 𝓝[<] b ≤ 𝓝[Set.Icc 0 b] b := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
    filter_upwards [Ioi_mem_nhds (show b / 2 < b by linarith)] with t ht hlt
    simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_Icc] at ht hlt ⊢
    exact ⟨by linarith, le_of_lt hlt⟩
  have hfb : Tendsto f (𝓝[<] b) (𝓝 (f b)) :=
    (hf.continuousOn.continuousWithinAt ⟨hb.le, le_refl b⟩).mono_left hle
  have hft : Tendsto (fun t : ℝ => f t ^ 2) (𝓝[<] b) (𝓝 (f b ^ 2)) := hfb.pow 2
  have hrp : Tendsto (fun t : ℝ => t ^ (a + 1)) (𝓝[<] b) (𝓝 (b ^ (a + 1))) :=
    (Real.continuousAt_rpow_const b (a + 1) (Or.inl hb.ne')).tendsto.mono_left
      (nhdsWithin_le_nhds (a := b) (s := Set.Iio b))
  exact hft.mul hrp

theorem power_hardy_boundary {a b : ℝ} (ha : -1 < a) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 b)) :
    ∫ t in (0 : ℝ)..b, f t ^ 2 * t ^ a
      ≤ 4 / (a + 1) ^ 2 * (∫ t in (0 : ℝ)..b, (deriv f t) ^ 2 * t ^ (a + 2))
        + 2 / (a + 1) * b ^ (a + 1) * (f b) ^ 2 := by
  have ha1 : 0 < a + 1 := by linarith
  -- ## Step 1: the two bounds on `f` and `deriv f` on `(0,b)`
  have hcontf : ContinuousOn f (Set.Icc 0 b) := hf.continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontf
  have hdcont : ContinuousOn (derivWithin f (Set.Icc 0 b)) (Set.Icc 0 b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hb) le_rfl
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hdcont
  have hC : 0 ≤ max C₁ C₂ := by
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_refl 0, hb.le⟩
    have h := hC₁ 0 h0mem
    simp only [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) (le_trans h (le_max_left _ _))
  have hbf : ∀ t ∈ Set.Ioo 0 b, |f t| ≤ max C₁ C₂ := by
    intro t ht
    have hmem : t ∈ Set.Icc 0 b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h := hC₁ t hmem
    simp only [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hbd : ∀ t ∈ Set.Ioo 0 b, |deriv f t| ≤ max C₁ C₂ := by
    intro t ht
    have hmem : t ∈ Set.Icc 0 b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hnhds : Set.Icc (0 : ℝ) b ∈ 𝓝 t :=
      mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
    have hdt : deriv f t = derivWithin f (Set.Icc 0 b) t :=
      (derivWithin_of_mem_nhds hnhds).symm
    rw [hdt]
    have h := hC₂ t hmem
    simp only [Real.norm_eq_abs] at h
    exact le_trans h (le_max_right _ _)
  obtain ⟨C, hC, hbfC, hbdC⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ (∀ t ∈ Set.Ioo 0 b, |f t| ≤ C) ∧
        (∀ t ∈ Set.Ioo 0 b, |deriv f t| ≤ C) := ⟨max C₁ C₂, hC, hbf, hbd⟩
  -- ## Step 2: integrability of the three integrands
  have hdercont : ContinuousOn (deriv f) (Set.Ioo 0 b) := by
    have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 b) t) (Set.Ioo 0 b) :=
      hdcont.mono Set.Ioo_subset_Icc_self
    refine h1.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hcont1 : ContinuousOn (fun t : ℝ => f t ^ 2 * t ^ a) (Set.Ioo 0 b) :=
    ((hcontf.mono Set.Ioo_subset_Icc_self).pow 2).mul
      (continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne'))
  have hcont2 : ContinuousOn (fun t : ℝ => (deriv f t) ^ 2 * t ^ (a + 2)) (Set.Ioo 0 b) :=
    (hdercont.pow 2).mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne'))
  have hcont3 : ContinuousOn (fun t : ℝ => f t * deriv f t * t ^ (a + 1)) (Set.Ioo 0 b) :=
    ((hcontf.mono Set.Ioo_subset_Icc_self).mul hdercont).mul
      (continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne'))
  have key : ∀ {G : ℝ → ℝ} {r C' : ℝ}, -1 < r → 0 ≤ C' →
      ContinuousOn G (Set.Ioo 0 b) → (∀ t ∈ Set.Ioo 0 b, |G t| ≤ C' * t ^ r) →
      IntervalIntegrable G volume 0 b := by
    intro G r C' hr hC' hcont hbound
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    have hg : IntegrableOn (fun t : ℝ => C' * t ^ r) (Set.Ioo 0 b) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1
        ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := b) hr).const_mul C')
    refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)]
      with t ht
    simpa only [Real.norm_eq_abs] using ht
  have hIp1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ a) volume 0 b :=
    key ha (sq_nonneg C) hcont1 (fun t ht => by
      have h1 : f t ^ 2 ≤ C ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hC]
        exact hbfC t ht
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f t)),
        abs_of_nonneg (Real.rpow_nonneg ht.1.le a)]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le a))
  have hIp2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (a + 2)) volume 0 b :=
    key (by linarith : -1 < a + 2) (sq_nonneg C) hcont2 (fun t ht => by
      have h1 : (deriv f t) ^ 2 ≤ C ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hC]
        exact hbdC t ht
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f t)),
        abs_of_nonneg (Real.rpow_nonneg ht.1.le (a + 2))]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le (a + 2)))
  have hIp3 : IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (a + 1)) volume 0 b :=
    key (by linarith : -1 < a + 1) (sq_nonneg C) hcont3 (fun t ht => by
      have h1 : |f t| * |deriv f t| ≤ C ^ 2 := by
        calc |f t| * |deriv f t| ≤ C * C :=
              mul_le_mul (hbfC t ht) (hbdC t ht) (abs_nonneg _) hC
          _ = C ^ 2 := by ring
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le (a + 1))]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le (a + 1)))
  -- ## Step 3: notation
  set A : ℝ := ∫ t in (0 : ℝ)..b, f t ^ 2 * t ^ a with hAdef
  set B : ℝ := ∫ t in (0 : ℝ)..b, (deriv f t) ^ 2 * t ^ (a + 2) with hBdef
  set S : ℝ := ∫ t in (0 : ℝ)..b, f t * deriv f t * t ^ (a + 1) with hSdef
  set L : ℝ := ∫ t in (0 : ℝ)..b, |f t * deriv f t * t ^ (a + 1)| with hLdef
  -- ## Step 4: the fundamental theorem of calculus for `φ t = f t ^ 2 * t ^ (a+1)`
  have hφderiv : ∀ x ∈ Set.Ioo 0 b, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (a + 1))
      (2 * (f x * deriv f x * x ^ (a + 1)) + (a + 1) * (f x ^ 2 * x ^ a)) x := by
    intro x hx
    have hnhds : Set.Icc (0 : ℝ) b ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    have hd : HasDerivAt f (deriv f x) x :=
      (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f x ^ 1 * deriv f x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (a + 1)) ((a + 1) * x ^ ((a + 1) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')
    have h3 := h1.mul h2
    rw [show (a + 1) - 1 = a by ring] at h3
    refine h3.congr_deriv ?_
    ring
  have hφint : IntervalIntegrable
      (fun t : ℝ => 2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a))
      volume 0 b :=
    (hIp3.const_mul 2).add (hIp1.const_mul (a + 1))
  have hFTC : ∫ t in (0 : ℝ)..b,
      (2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a))
      = f b ^ 2 * b ^ (a + 1) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb hφderiv hφint
      (phb_tendsto_zero ha1 hb hC hbfC) (phb_tendsto_b (a := a) hb hf)
    rwa [sub_zero] at h
  have hsplit : (∫ t in (0 : ℝ)..b,
      (2 * (f t * deriv f t * t ^ (a + 1)) + (a + 1) * (f t ^ 2 * t ^ a)))
      = 2 * S + (a + 1) * A := by
    rw [intervalIntegral.integral_add (hIp3.const_mul 2) (hIp1.const_mul (a + 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- ## Step 5: the identity `(a+1) A = f b ^ 2 * b ^ (a+1) - 2 S`
  have hAB : (a + 1) * A = f b ^ 2 * b ^ (a + 1) - 2 * S := by
    rw [hsplit] at hFTC
    linarith
  -- ## Step 6: the weighted arithmetic--geometric mean inequality
  have hpt : ∀ t ∈ Set.Ioo 0 b,
      2 * |f t * deriv f t * t ^ (a + 1)|
        ≤ (a + 1) / 2 * (f t ^ 2 * t ^ a)
          + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ (a + 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hta : 0 ≤ t ^ a := Real.rpow_nonneg ht0.le a
    have hpow1 : t ^ (a + 1) = t ^ a * t := by
      rw [Real.rpow_add ht0 a 1, Real.rpow_one]
    have hpow2 : t ^ (a + 2) = t ^ a * t ^ 2 := by
      rw [Real.rpow_add ht0 a 2, Real.rpow_two]
    have hL : |f t * deriv f t * (t ^ a * t)| = (|f t| * |deriv f t| * t) * t ^ a := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hta, abs_of_pos ht0]
      ring
    have hkey : 4 * (a + 1) * (|f t| * |deriv f t| * t)
        ≤ (a + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
      have htwo := two_mul_le_add_sq ((a + 1) * |f t|) (2 * |deriv f t| * t)
      have hfa : |f t| ^ 2 = f t ^ 2 := sq_abs (f t)
      have hga : |deriv f t| ^ 2 = (deriv f t) ^ 2 := sq_abs (deriv f t)
      nlinarith [htwo, hfa, hga]
    have hred : 2 * (|f t| * |deriv f t| * t)
        ≤ (a + 1) / 2 * f t ^ 2 + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ 2) := by
      have hc : (0 : ℝ) < 2 * (a + 1) := by linarith
      refine le_of_mul_le_mul_right ?_ hc
      have h1 : ((a + 1) / 2 * f t ^ 2 + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ 2))
          * (2 * (a + 1)) = (a + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
        field_simp
        ring
      have h2 : 2 * (|f t| * |deriv f t| * t) * (2 * (a + 1))
          = 4 * (a + 1) * (|f t| * |deriv f t| * t) := by ring
      rw [h1, h2]
      exact hkey
    rw [hpow1, hpow2, hL]
    have hmul := mul_le_mul_of_nonneg_right hred hta
    nlinarith [hmul]
  -- ## Step 7: integrate the pointwise bound
  have hIL : IntervalIntegrable (fun t : ℝ => 2 * |f t * deriv f t * t ^ (a + 1)|)
      volume 0 b := hIp3.abs.const_mul 2
  have hIR : IntervalIntegrable (fun t : ℝ =>
      (a + 1) / 2 * (f t ^ 2 * t ^ a) + 2 / (a + 1) * ((deriv f t) ^ 2 * t ^ (a + 2)))
      volume 0 b :=
    (hIp1.const_mul ((a + 1) / 2)).add (hIp2.const_mul (2 / (a + 1)))
  have hAMGM : 2 * L ≤ (a + 1) / 2 * A + 2 / (a + 1) * B := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hb.le hIL hIR hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hIp1.const_mul ((a + 1) / 2))
        (hIp2.const_mul (2 / (a + 1))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hSL : |S| ≤ L := by
    rw [hSdef, hLdef]
    exact intervalIntegral.abs_integral_le_integral_abs hb.le
  -- ## Step 8: finish
  have hstep : (a + 1) / 2 * A ≤ f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B := by
    have h1 : -2 * S ≤ 2 * L := by
      have h2 := neg_abs_le S
      linarith
    nlinarith [hAB, h1, hAMGM]
  have hfin : A ≤ 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B := by
    have hc : (0 : ℝ) < (a + 1) / 2 := by linarith
    have h1 : A * ((a + 1) / 2) ≤ f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B := by
      linarith
    have h2 := (le_div_iff₀ hc).2 h1
    have h3 : (f b ^ 2 * b ^ (a + 1) + 2 / (a + 1) * B) / ((a + 1) / 2)
        = 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B := by
      field_simp
      ring
    rw [h3] at h2
    exact h2
  have hgoal : 2 / (a + 1) * (f b ^ 2 * b ^ (a + 1)) + 4 / (a + 1) ^ 2 * B
      = 4 / (a + 1) ^ 2 * B + 2 / (a + 1) * b ^ (a + 1) * (f b) ^ 2 := by
    ring
  linarith [hfin, hgoal]

end Work.FTS.H2.Transport3Aux
