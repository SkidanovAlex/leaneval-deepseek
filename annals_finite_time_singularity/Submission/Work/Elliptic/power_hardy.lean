/-
Copyright: work module for the Elgindi finite-time singularity project.

# The sharp weighted Hardy inequality `power_hardy`

For `f : ℝ → ℝ` of class `C¹` on `[0,a]` (`a > 0`) with `f 0 = 0` and for `0 ≤ η < 1`,

  `∫_0^a f(t)² t^{-(2+η)} dt ≤ 4/(1+η)² ∫_0^a f'(t)² t^{-η} dt`.

This is the classical sharp weighted Hardy inequality (the exponent `a = -(2+η)` with `p = 2`),
the one-dimensional estimate used in the elliptic section of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

## Proof

Write `g(t) = f(t)² t^{-(1+η)}`.  On `(0,a)` one has

  `g'(t) = 2 f(t) f'(t) t^{-(1+η)} - (1+η) f(t)² t^{-(2+η)}`,

and the pointwise completion of the square
`0 ≤ (f'(t) - (1+η)/2 · f(t)/t)² t^{-η}` is equivalent to

  `(1+η)²/4 · f(t)² t^{-(2+η)} ≤ f'(t)² t^{-η} - (1+η)/2 · g'(t)`.

Integrating over `[0,a]` and applying the fundamental theorem of calculus to `g` (the boundary
term at `0` vanishes because `f(t) = O(t)` as `t → 0⁺`, and the boundary term at `a` has the
favourable sign) gives `(1+η)²/4 · ∫ f² t^{-(2+η)} ≤ ∫ f'² t^{-η}`, i.e. the claim.

The auxiliary estimates are:

* `Work.Elliptic.power_hardy_bounds` (proved elsewhere in the workspace): `f` and `deriv f` are
  bounded by a common constant `C ≥ 0` in the sense `|f t| ≤ C t`, `|deriv f t| ≤ C`.
* `power_hardy_tendsto_zero`, `power_hardy_tendsto_a`: the two endpoint limits of `g`.
* `power_hardy_hasDerivAt`: the derivative identity above.
* `power_hardy_integrable`: the three integrands are interval integrable, by comparison with
  the integrable power `t^{-η}` (here `η < 1` is used).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.power_hardy_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option maxHeartbeats 1000000

/-! ## Auxiliary estimates -/

/-- `t ↦ f t ^ 2 * t ^ (-(1 + η)) → 0` as `t → 0⁺`, given `|f t| ≤ C t`. -/
private lemma power_hardy_tendsto_zero {a η C : ℝ} (ha : 0 < a) (hη1 : η < 1) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hbf : ∀ t ∈ Set.Ioo 0 a, |f t| ≤ C * t) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (-(1 + η))) (𝓝[>] 0) (𝓝 0) := by
  have hmem : Set.Ioo 0 a ∈ 𝓝[>] 0 := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Iio_mem_nhds ha] with t ht h0t
    exact ⟨h0t, ht⟩
  have hpoly : Tendsto (fun t : ℝ => t ^ (1 - η)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (1 - η)) 0 :=
      Real.continuousAt_rpow_const 0 (1 - η) (Or.inr (by linarith))
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    rwa [Real.zero_rpow (by linarith : (1 - η) ≠ 0)] at h2
  have hg : Tendsto (fun t : ℝ => C ^ 2 * t ^ (1 - η)) (𝓝[>] 0) (𝓝 0) := by
    have h2 := (tendsto_const_nhds (x := C ^ 2) (f := 𝓝[>] (0 : ℝ))).mul hpoly
    simpa using h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hmem] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
  · filter_upwards [hmem] with t ht
    have h1 : f t ^ 2 ≤ (C * t) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC ht.1.le)]
      exact hbf t ht
    have hid : t ^ 2 * t ^ (-(1 + η)) = t ^ (1 - η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht.1]
      congr 1; ring
    calc f t ^ 2 * t ^ (-(1 + η)) ≤ (C * t) ^ 2 * t ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (1 - η) := by
          rw [mul_pow, ← hid]; ring

/-- `t ↦ f t ^ 2 * t ^ (-(1 + η)) → f a ^ 2 * a ^ (-(1 + η))` as `t → a⁻`. -/
private lemma power_hardy_tendsto_a {a η : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (-(1 + η))) (𝓝[<] a)
      (𝓝 (f a ^ 2 * a ^ (-(1 + η)))) := by
  have hle : 𝓝[<] a ≤ 𝓝[Set.Icc 0 a] a := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
    filter_upwards [Ioi_mem_nhds (show a / 2 < a by linarith)] with t ht hlt
    simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_Icc] at ht hlt ⊢
    exact ⟨by linarith, le_of_lt hlt⟩
  have hfa : Tendsto f (𝓝[<] a) (𝓝 (f a)) :=
    (hf.continuousOn.continuousWithinAt ⟨ha.le, le_refl a⟩).mono_left hle
  have hft : Tendsto (fun t : ℝ => f t ^ 2) (𝓝[<] a) (𝓝 (f a ^ 2)) := hfa.pow 2
  have hrp : Tendsto (fun t : ℝ => t ^ (-(1 + η))) (𝓝[<] a) (𝓝 (a ^ (-(1 + η)))) :=
    (Real.continuousAt_rpow_const a (-(1 + η)) (Or.inl ha.ne')).tendsto.mono_left
      (nhdsWithin_le_nhds (a := a) (s := Set.Iio a))
  exact hft.mul hrp

/-- Derivative of `t ↦ f t ^ 2 * t ^ (-(1 + η))` on the interior. -/
private lemma power_hardy_hasDerivAt {a η : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) {t : ℝ} (ht : t ∈ Set.Ioo 0 a) :
    HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (-(1 + η)))
      (2 * (f t * deriv f t * t ^ (-(1 + η))) - (1 + η) * (f t ^ 2 * t ^ (-(2 + η)))) t := by
  have hnhds : Set.Icc 0 a ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hd : HasDerivAt f (deriv f t) t :=
    (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f t ^ 1 * deriv f t) t := hd.pow 2
  have h2 : HasDerivAt (fun s : ℝ => s ^ (-(1 + η))) (-(1 + η) * t ^ (-(1 + η) - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.1.ne')
  have h3 := h1.mul h2
  rw [show -(1 + η) - 1 = -(2 + η) by ring] at h3
  refine h3.congr_deriv ?_
  ring

/-- Interval integrability of the three weighted integrands appearing in `power_hardy`. -/
private lemma power_hardy_integrable {a η C : ℝ} (ha : 0 < a) (hη1 : η < 1) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a))
    (hbf : ∀ t ∈ Set.Ioo 0 a, |f t| ≤ C * t)
    (hbd : ∀ t ∈ Set.Ioo 0 a, |deriv f t| ≤ C) :
    IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ (-(2 + η))) volume 0 a ∧
    IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) volume 0 a ∧
    IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (-(1 + η))) volume 0 a := by
  have hfcont : ContinuousOn f (Set.Ioo 0 a) := hf.continuousOn.mono Set.Ioo_subset_Icc_self
  have hdcont : ContinuousOn (deriv f) (Set.Ioo 0 a) := by
    have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 a) t) (Set.Ioo 0 a) :=
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hrpow2 : ContinuousOn (fun t : ℝ => t ^ (-(2 + η))) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hrpow1 : ContinuousOn (fun t : ℝ => t ^ (-(1 + η))) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hrpow0 : ContinuousOn (fun t : ℝ => t ^ (-η)) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hid1 : ∀ t ∈ Set.Ioo 0 a, t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
    intro t ht
    rw [← Real.rpow_two t, ← Real.rpow_add ht.1]; congr 1; ring
  have hid2 : ∀ t ∈ Set.Ioo 0 a, t * t ^ (-(1 + η)) = t ^ (-η) := by
    intro t ht
    have h := Real.rpow_add ht.1 (1 : ℝ) (-(1 + η))
    rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
    rw [Real.rpow_one] at h
    exact h.symm
  have key : ∀ {G : ℝ → ℝ}, ContinuousOn G (Set.Ioo 0 a) →
      (∀ t ∈ Set.Ioo 0 a, |G t| ≤ C ^ 2 * t ^ (-η)) → IntervalIntegrable G volume 0 a := by
    intro G hcont hbound
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    have hg : IntegrableOn (fun t => C ^ 2 * t ^ (-η)) (Set.Ioo 0 a) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
        ((intervalIntegral.intervalIntegrable_rpow' (show -1 < -η by linarith)).const_mul (C ^ 2))
    refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)]
      with t ht
    simpa only [Real.norm_eq_abs] using ht
  refine ⟨key (hfcont.pow 2 |>.mul hrpow2) ?_, key (hdcont.pow 2 |>.mul hrpow0) ?_,
    key ((hfcont.mul hdcont).mul hrpow1) ?_⟩
  · intro t ht
    have h1 : f t ^ 2 ≤ (C * t) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC ht.1.le)]; exact hbf t ht
    calc |f t ^ 2 * t ^ (-(2 + η))| = f t ^ 2 * t ^ (-(2 + η)) := by
          rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _))]
      _ ≤ (C * t) ^ 2 * t ^ (-(2 + η)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (-η) := by rw [mul_pow, ← hid1 t ht]; ring
  · intro t ht
    have h1 : (deriv f t) ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hC]; exact hbd t ht
    calc |(deriv f t) ^ 2 * t ^ (-η)| = (deriv f t) ^ 2 * t ^ (-η) := by
          rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _))]
      _ ≤ C ^ 2 * t ^ (-η) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
  · intro t ht
    have hab : |f t| * |deriv f t| ≤ C ^ 2 * t := by
      have hb1 := hbf t ht; have hb2 := hbd t ht
      calc |f t| * |deriv f t| ≤ (C * t) * C :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (mul_nonneg hC ht.1.le)
        _ = C ^ 2 * t := by ring
    calc |f t * deriv f t * t ^ (-(1 + η))|
        = |f t| * |deriv f t| * t ^ (-(1 + η)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      _ ≤ (C ^ 2 * t) * t ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (-η) := by rw [mul_assoc, hid2 t ht]

/-! ## The target theorem -/

theorem power_hardy {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) (h0 : f 0 = 0) :
    (∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
  obtain ⟨C, hC, hbf, hbd⟩ := power_hardy_bounds ha hf h0
  obtain ⟨hI1, hI2, hI3⟩ := power_hardy_integrable ha hη1 hC hf hbf hbd
  set φ : ℝ → ℝ :=
    fun t => 2 * (f t * deriv f t * t ^ (-(1 + η))) - (1 + η) * (f t ^ 2 * t ^ (-(2 + η)))
    with hφdef
  have hIφ : IntervalIntegrable φ volume 0 a := by
    simp only [hφdef]
    exact (hI3.const_mul 2).sub (hI1.const_mul (1 + η))
  have hderiv : ∀ x ∈ Set.Ioo 0 a, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (-(1 + η))) (φ x) x := by
    intro x hx
    simp only [hφdef]
    exact power_hardy_hasDerivAt hf hx
  have hFTC : ∫ t in (0 : ℝ)..a, φ t = f a ^ 2 * a ^ (-(1 + η)) - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha hderiv hIφ
      (power_hardy_tendsto_zero ha hη1 hC hbf) (power_hardy_tendsto_a ha hf)
  have hpt : ∀ t ∈ Set.Ioo 0 a, (1 + η) ^ 2 / 4 * (f t ^ 2 * t ^ (-(2 + η)))
      ≤ (deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t := by
    intro t ht
    simp only [hφdef]
    have hid1 : t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht.1]; congr 1; ring
    have hid2 : t * t ^ (-(1 + η)) = t ^ (-η) := by
      have h := Real.rpow_add ht.1 (1 : ℝ) (-(1 + η))
      rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
      rw [Real.rpow_one] at h
      exact h.symm
    have h2 : (f t / t) ^ 2 * t ^ 2 = f t ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 ht.1.ne')]
    have hx1 : f t ^ 2 * t ^ (-(2 + η)) = (f t / t) ^ 2 * t ^ (-η) := by
      calc f t ^ 2 * t ^ (-(2 + η)) = ((f t / t) ^ 2 * t ^ 2) * t ^ (-(2 + η)) := by rw [h2]
        _ = (f t / t) ^ 2 * (t ^ 2 * t ^ (-(2 + η))) := by ring
        _ = (f t / t) ^ 2 * t ^ (-η) := by rw [hid1]
    have hx2 : f t * deriv f t * t ^ (-(1 + η)) = (f t / t) * deriv f t * t ^ (-η) := by
      have h3 : (f t / t) * t = f t := div_mul_cancel₀ (f t) ht.1.ne'
      calc f t * deriv f t * t ^ (-(1 + η))
          = ((f t / t) * t) * deriv f t * t ^ (-(1 + η)) := by rw [h3]
        _ = (f t / t) * deriv f t * (t * t ^ (-(1 + η))) := by ring
        _ = (f t / t) * deriv f t * t ^ (-η) := by rw [hid2]
    rw [hx1, hx2]
    nlinarith [mul_nonneg (Real.rpow_nonneg ht.1.le (-η))
      (sq_nonneg (deriv f t - (1 + η) / 2 * (f t / t)))]
  have hmono : ∫ t in (0 : ℝ)..a, (1 + η) ^ 2 / 4 * (f t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in (0 : ℝ)..a, ((deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ha.le
      (hI1.const_mul _) (hI2.add (hIφ.const_mul _)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add hI2 (hIφ.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  rw [hFTC, sub_zero] at hmono
  have hle : (-(1 + η) / 2) * (f a ^ 2 * a ^ (-(1 + η))) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha.le _))
  have hkey : (1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
    linarith [hmono, hle]
  have hsq : (0 : ℝ) < (1 + η) ^ 2 := pow_pos (by linarith) 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith [hkey, hsq]

end Work.Elliptic
