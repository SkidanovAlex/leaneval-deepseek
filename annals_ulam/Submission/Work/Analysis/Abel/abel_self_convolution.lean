import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral
import Submission.Work.Analysis.Abel.integrableOn_invSqrt_triangle_right

/-!
# Abel's self-convolution, unconditionally for continuous profiles

`Commons.Analysis.Abel.integrableOn_invSqrt_triangle_right` (the right-edge half of the Abel
layer, proved in the sibling file) discharges the Tonelli hypothesis that
`abel_self_convolution_of_integrable` in
`Submission/Work/Geometry/Ulam/odd_noncentral_profile_data.lean` took as input.  The result is the
unconditional Abel self-convolution for a profile that is continuous on `[0,1]`:

  `∫_0^x (√(x-v))⁻¹ (∫_0^v (√(v-t))⁻¹ g t) = π ∫_0^x g`   for `0 < x ≤ 1`.

Together with the Abel inversion step this is the analytic core of the non-local construction in
the odd-dimensional case of Ulam's Problem 19.

The one-dimensional beta integral `∫_a^b (√(b-v))⁻¹(√(v-a))⁻¹ = π` (`integral_invSqrt_mul_invSqrt_sub`,
via `∫_0^1 (u(1-u))^{-1/2} = π`) is proved here as well: it is the value of the inner integral and is
currently only available in a Work file, so it is restated here for commons use.

Once the sibling file is adopted into the commons as
`Submission.Commons.Analysis.Abel.integrableOn_invSqrt_triangle_right`, the import above should be
switched to that commons module.
-/

open MeasureTheory Filter
open scoped Interval Topology
open Set

namespace Commons.Analysis.Abel

lemma integral_invSqrt_mul_one_sub :
    (∫ u in (0:ℝ)..1, (Real.sqrt (u * (1 - u)))⁻¹) = Real.pi := by
  have hderiv : ∀ u ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => 2 * Real.arcsin (Real.sqrt u)) ((Real.sqrt (u * (1 - u)))⁻¹) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hsqrt0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
    have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt (le_of_lt hu0)
    have hlt : Real.sqrt u < 1 := by
      have h := Real.sqrt_lt_sqrt (le_of_lt hu0) hu1
      simpa [Real.sqrt_one] using h
    have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u := Real.hasDerivAt_sqrt (ne_of_gt hu0)
    have h2 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (Real.sqrt u) ^ 2)) (Real.sqrt u) :=
      Real.hasDerivAt_arcsin (by intro h; nlinarith [hsqrt0]) (ne_of_lt hlt)
    have h3 : HasDerivAt (fun u : ℝ => Real.arcsin (Real.sqrt u))
        ((1 / Real.sqrt (1 - (Real.sqrt u) ^ 2)) * (1 / (2 * Real.sqrt u))) u := h2.comp u h1
    have h4 := h3.const_mul 2
    have hval : 2 * ((1 / Real.sqrt (1 - (Real.sqrt u) ^ 2)) * (1 / (2 * Real.sqrt u)))
        = (Real.sqrt (u * (1 - u)))⁻¹ := by
      rw [hsq, Real.sqrt_mul (le_of_lt hu0)]
      simp only [one_div, mul_inv]
      ring
    rw [hval] at h4
    exact h4
  have hcontAll : Continuous (fun u : ℝ => 2 * Real.arcsin (Real.sqrt u)) :=
    (Real.continuous_arcsin.comp Real.continuous_sqrt).const_mul 2
  have hcontIcc : ContinuousOn (fun u : ℝ => 2 * Real.arcsin (Real.sqrt u)) (Set.Icc (0:ℝ) 1) :=
    hcontAll.continuousOn
  have hcontU : ContinuousOn (fun u : ℝ => 2 * Real.arcsin (Real.sqrt u)) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hcontIcc
  have hderiv' : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun u : ℝ => 2 * Real.arcsin (Real.sqrt u)) ((Real.sqrt (x * (1 - x)))⁻¹) x := by
    intro x hx
    simp only [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hx
    exact hderiv x hx
  have hpos : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ (Real.sqrt (x * (1 - x)))⁻¹ :=
    fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hint : IntervalIntegrable (fun u : ℝ => (Real.sqrt (u * (1 - u)))⁻¹) volume (0:ℝ) 1 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg hcontU hderiv' hpos
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0:ℝ)) (b := 1)
    (by norm_num) hcontIcc hderiv hint
  rw [h]
  rw [Real.sqrt_one, Real.arcsin_one, Real.sqrt_zero, Real.arcsin_zero]
  ring

/-- The Abel kernel integrates to `π`: for `a < b`,
`∫_a^b (√(b-v))⁻¹ (√(v-a))⁻¹ dv = π`.  By the substitution `v = a + (b-a)s` this is
`∫_0^1 (s(1-s))^{-1/2} ds` (`integral_invSqrt_mul_one_sub`).  This is the inner integral of both
forms of Abel's inversion, hence of the spherical-Radon inversion used in the odd case. -/
lemma integral_invSqrt_mul_invSqrt_sub {a b : ℝ} (hab : a < b) :
    (∫ v in a..b, (Real.sqrt (b - v))⁻¹ * (Real.sqrt (v - a))⁻¹) = Real.pi := by
  set c : ℝ := b - a with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcomp := intervalIntegral.integral_comp_mul_add
    (f := fun v : ℝ => (Real.sqrt (b - v))⁻¹ * (Real.sqrt (v - a))⁻¹)
    (a := (0:ℝ)) (b := 1) hcne a
  simp only [mul_zero, mul_one, zero_add, smul_eq_mul] at hcomp
  have hsub : (∫ v in a..b, (Real.sqrt (b - v))⁻¹ * (Real.sqrt (v - a))⁻¹)
      = c * ∫ s in (0:ℝ)..1,
          (Real.sqrt (b - (c * s + a)))⁻¹ * (Real.sqrt (c * s + a - a))⁻¹ := by
    rw [hcomp]
    rw [show c + a = b by rw [hc]; ring]
    rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  rw [hsub]
  have hcongr : (∫ s in (0:ℝ)..1,
        (Real.sqrt (b - (c * s + a)))⁻¹ * (Real.sqrt (c * s + a - a))⁻¹)
      = ∫ s in (0:ℝ)..1, c⁻¹ * (Real.sqrt (s * (1 - s)))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have hs0 : 0 ≤ s := hs.1
    have h1 : b - (c * s + a) = c * (1 - s) := by rw [hc]; ring
    have h2 : c * s + a - a = c * s := by ring
    rw [h1, h2, Real.sqrt_mul (le_of_lt hcpos), Real.sqrt_mul (le_of_lt hcpos)]
    rw [Real.sqrt_mul hs0]
    have h3 : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = c⁻¹ := by
      rw [← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hcpos)]
    rw [mul_inv, mul_inv, ← h3]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_invSqrt_mul_one_sub]
  field_simp

/-- **Abel's self-convolution**, unconditionally for a profile continuous on `[0,1]`:
the triangle `(t,v) ↦ (√(v-t))⁻¹(√(x-v))⁻¹` is integrable by
`integrableOn_invSqrt_triangle_right` (with the continuous factor `g`), so the Fubini swap and the
inner beta integral give the identity. -/
lemma abel_self_convolution {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1))
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ v in (0:ℝ)..x, (Real.sqrt (x - v))⁻¹ *
        (∫ t in (0:ℝ)..v, (Real.sqrt (v - t))⁻¹ * g t))
      = Real.pi * ∫ t in (0:ℝ)..x, g t := by
  have hsub : Set.Icc (0:ℝ) x ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc_right hx1
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => g p.1)
      (Set.Icc (0:ℝ) x ×ˢ Set.Icc (0:ℝ) x) :=
    ContinuousOn.comp (hg.mono hsub) continuousOn_fst (fun p hp => hp.1)
  have hint_raw := integrableOn_invSqrt_triangle_right (a := (0:ℝ)) (b := x) hx
    (K := fun t v => g t) hK_cont
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * g p.1 else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
    simpa only [smul_eq_mul, mul_assoc] using hint_raw

  set F : ℝ → ℝ → ℝ := fun t v => (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹ * g t with hF
  have hleft : (∫ v in (0:ℝ)..x, (Real.sqrt (x - v))⁻¹ *
        (∫ t in (0:ℝ)..v, (Real.sqrt (v - t))⁻¹ * g t))
      = ∫ v in (0:ℝ)..x, ∫ t in (0:ℝ)..v, F t v := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    simp only [hF]
    ring
  have hint' : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then F p.1 p.2 else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by simpa [hF] using hint
  have hswap := Commons.Analysis.Abel.intervalIntegral_triangle_swap (a := (0:ℝ)) (b := x)
    (le_of_lt hx) (F := F) hint'
  have hinner : ∀ t ∈ Set.Ioo (0:ℝ) x, (∫ v in t..x, F t v) = g t * Real.pi := by
    intro t ht
    have hconst : (∫ v in t..x, F t v)
        = g t * ∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹ := by
      simp only [hF]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _
      ring
    rw [hconst]
    have hker : (∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹) = Real.pi := by
      rw [show (∫ v in t..x, (Real.sqrt (v - t))⁻¹ * (Real.sqrt (x - v))⁻¹)
          = ∫ v in t..x, (Real.sqrt (x - v))⁻¹ * (Real.sqrt (v - t))⁻¹ by
        apply intervalIntegral.integral_congr
        intro v _
        ring]
      exact integral_invSqrt_mul_invSqrt_sub (a := t) (b := x) ht.2
    rw [hker]
  have hae_neq : ∀ᵐ t : ℝ ∂volume, t ≠ x := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton x
  rw [hleft, hswap]
  have hfinal : (∫ t in (0:ℝ)..x, ∫ v in t..x, F t v) = Real.pi * ∫ t in (0:ℝ)..x, g t := by
    have hcongr : (∫ t in (0:ℝ)..x, ∫ v in t..x, F t v)
        = ∫ t in (0:ℝ)..x, g t * Real.pi := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hae_neq] with t htx ht
      rw [Set.uIoc_of_le (le_of_lt hx)] at ht
      exact hinner t ⟨ht.1, lt_of_le_of_ne ht.2 htx⟩
    rw [hcongr, intervalIntegral.integral_mul_const]
    ring
  exact hfinal


/-- **Abel's inversion**, unconditionally for a profile continuous on `[0,1]`: from
`B x = ∫_0^x g t / √(x-t)` one recovers `g = (1/π) d/dx ∫_0^{·} B v / √(·-v)` on `(0,1)`.
The Tonelli input of the Work-file version is supplied by `abel_self_convolution`. -/
lemma abel_inversion {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) {B : ℝ → ℝ}
    (hB : ∀ x ∈ Set.Icc (0:ℝ) 1, B x = ∫ t in (0:ℝ)..x, g t / Real.sqrt (x - t))
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    g x = (1/Real.pi) * deriv (fun w => ∫ v in (0:ℝ)..w, B v / Real.sqrt (w - v)) x := by

  have hE : ∀ w ∈ Set.Ioo (0:ℝ) 1, (∫ v in (0:ℝ)..w, (Real.sqrt (w - v))⁻¹ * B v)
      = Real.pi * ∫ t in (0:ℝ)..w, g t := by
    intro w hw
    have hsc := abel_self_convolution (g := g) hg hw.1 (le_of_lt hw.2)
    rw [← hsc]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (le_of_lt hw.1)] at hv
    have hvmem : v ∈ Set.Icc (0:ℝ) 1 :=
      ⟨hv.1, le_trans hv.2 (le_of_lt hw.2)⟩
    dsimp only
    rw [hB v hvmem]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [div_eq_mul_inv]
    ring
  have hev : (fun w : ℝ => ∫ v in (0:ℝ)..w, (Real.sqrt (w - v))⁻¹ * B v)
      =ᶠ[nhds x] fun w : ℝ => Real.pi * ∫ t in (0:ℝ)..w, g t := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with w hw
    exact hE w hw
  have hintg : IntervalIntegrable (fun t : ℝ => g t) volume (0:ℝ) x :=
    (hg.mono (Set.Icc_subset_Icc le_rfl (le_of_lt hx.2))).intervalIntegrable_of_Icc (le_of_lt hx.1)
  have hftc : HasDerivAt (fun w : ℝ => ∫ t in (0:ℝ)..w, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right hintg
      ((hg.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
      ((hg.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hx.1 hx.2))
  have hderiv : deriv (fun w : ℝ => ∫ v in (0:ℝ)..w, (Real.sqrt (w - v))⁻¹ * B v) x
      = Real.pi * g x := by
    rw [hev.deriv_eq]
    exact (hftc.const_mul Real.pi).deriv
  have hgoal : (fun w : ℝ => ∫ v in (0:ℝ)..w, B v / Real.sqrt (w - v))
      = fun w : ℝ => ∫ v in (0:ℝ)..w, (Real.sqrt (w - v))⁻¹ * B v := by
    funext w
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [div_eq_mul_inv]
    ring
  rw [hgoal, hderiv]
  field_simp



end Commons.Analysis.Abel
