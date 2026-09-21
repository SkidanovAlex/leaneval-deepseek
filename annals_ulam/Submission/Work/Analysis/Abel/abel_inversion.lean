import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral

open MeasureTheory
open scoped Interval Topology

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



/-- **Abel self-convolution (triangle Fubini step).**  Assuming the Abel kernel
`(p.1,p.2) ↦ 1/√((p.2-p.1)(x-p.2))` is integrable on the triangle `{0 ≤ p.1 ≤ p.2 ≤ x}` (with
the usual `Ioc`-indicator), swapping the order of integration and using
`integral_invSqrt_mul_invSqrt_sub` for the inner integral gives

`∫_{v=0}^{x} (√(x-v))⁻¹ (∫_{t=0}^{v} (√(v-t))⁻¹ g t) = π ∫_{0}^{x} g`.

The integrability hypothesis is a Tonelli computation (the kernel is the product
`(√(p.2-p.1))⁻¹(√(x-p.2))⁻¹`, whose double integral is finite) and is the only remaining input to
Abel's inversion `abel_inversion`. -/
 lemma abel_self_convolution_of_integrable {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * g p.1 else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x)) :
    (∫ v in (0:ℝ)..x, (Real.sqrt (x - v))⁻¹ *
        (∫ t in (0:ℝ)..v, (Real.sqrt (v - t))⁻¹ * g t))
      = Real.pi * ∫ t in (0:ℝ)..x, g t := by
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

/-- **Abel's inversion.**  If `B = A g` with `(A g)(x) = ∫_0^x g t / √(x-t) dt`, then
`g = (1/π) d/dx A B` on `(0,1)`.  The proof combines `abel_self_convolution_of_integrable`
(with `B` expanded by its definition) with the fundamental theorem of calculus; the hypothesis
`hint` is the integrability of the Abel kernel on the triangle, i.e. precisely the Tonelli step
that `abel_self_convolution_of_integrable` takes as input. -/
 lemma abel_inversion_of_integrable {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) {B : ℝ → ℝ}
    (hB : ∀ x ∈ Set.Icc (0:ℝ) 1, B x = ∫ t in (0:ℝ)..x, g t / Real.sqrt (x - t))
    (hint : ∀ w ∈ Set.Ioo (0:ℝ) 1, MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (w - p.2))⁻¹ * g p.1 else 0)
      (Set.uIoc 0 w ×ˢ Set.uIoc 0 w))
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    g x = (1/Real.pi) * deriv (fun w => ∫ v in (0:ℝ)..w, B v / Real.sqrt (w - v)) x := by
  have hE : ∀ w ∈ Set.Ioo (0:ℝ) 1, (∫ v in (0:ℝ)..w, (Real.sqrt (w - v))⁻¹ * B v)
      = Real.pi * ∫ t in (0:ℝ)..w, g t := by
    intro w hw
    have hsc := abel_self_convolution_of_integrable (g := g) hw.1 (hint w hw)
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



lemma integrableOn_abel_weight_triangle_open {x : ℝ} (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ else 0)
      (Set.uIoo 0 x ×ˢ Set.uIoo 0 x) := by
  rw [Set.uIoo_of_le hx.le]
  let S : Set ℝ := Set.Ioo 0 x
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (x - p.2, x - p.1)
  let T_equiv : ℝ × ℝ ≃ᵐ ℝ × ℝ := {
    toEquiv := {
      toFun := T
      invFun := T
      left_inv := by
        intro p
        cases p with
        | mk p1 p2 => simp [T]
      right_inv := by
        intro p
        cases p with
        | mk p1 p2 => simp [T] }
    measurable_toFun := by
      dsimp [T]
      fun_prop
    measurable_invFun := by
      dsimp [T]
      fun_prop }
  have hT_mp : MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.prod volume) (volume.prod volume) := by
      simpa using (MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume))
    have hneg : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
        (volume.prod volume) (volume.prod volume) :=
      MeasureTheory.MeasurePreserving.prod
        (MeasureTheory.Measure.measurePreserving_neg volume)
        (MeasureTheory.Measure.measurePreserving_neg volume)
    have hadd : MeasurePreserving (fun q : ℝ × ℝ => q + (x, x))
        (volume.prod volume) (volume.prod volume) :=
      MeasureTheory.measurePreserving_add_right (volume.prod volume) (x, x)
    have hcomp : MeasurePreserving
        (fun p : ℝ × ℝ => (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) (Prod.swap p))
        (volume.prod volume) (volume.prod volume) := hneg.comp hswap
    have hfinal : MeasurePreserving
        (fun p : ℝ × ℝ => ((Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) (Prod.swap p)) + (x, x))
        (volume.prod volume) (volume.prod volume) := hadd.comp hcomp
    convert hfinal using 1
    ext p <;> simp [T, Prod.map, Prod.swap] <;> ring
  have hT_pre : T ⁻¹' (S ×ˢ S) = S ×ˢ S := by
    ext p
    constructor
    · intro hp
      have hp1 : (T p).1 ∈ S := hp.1
      have hp2 : (T p).2 ∈ S := hp.2
      change x - p.2 ∈ S at hp1
      change x - p.1 ∈ S at hp2
      have hp1' : 0 < x - p.2 ∧ x - p.2 < x := by simpa [S] using hp1
      have hp2' : 0 < x - p.1 ∧ x - p.1 < x := by simpa [S] using hp2
      exact ⟨⟨by linarith [hp1'.1, hp1'.2], by linarith [hp1'.1, hp1'.2]⟩,
        ⟨by linarith [hp2'.1, hp2'.2], by linarith [hp2'.1, hp2'.2]⟩⟩
    · intro hp
      have hp1 : p.1 ∈ S := hp.1
      have hp2 : p.2 ∈ S := hp.2
      have hp1' : 0 < p.1 ∧ p.1 < x := by simpa [S] using hp1
      have hp2' : 0 < p.2 ∧ p.2 < x := by simpa [S] using hp2
      exact ⟨⟨by linarith [hp2'.1, hp2'.2], by linarith [hp2'.1, hp2'.2]⟩,
        ⟨by linarith [hp1'.1, hp1'.2], by linarith [hp1'.1, hp1'.2]⟩⟩
  let stdW : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.1 - 0))⁻¹ * (Real.sqrt (p.2 - p.1))⁻¹ else 0
  have hstd : MeasureTheory.IntegrableOn stdW (S ×ˢ S) := by
    have hstd_half : MeasureTheory.IntegrableOn stdW (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
      dsimp only [stdW]
      simpa using integrableOn_weight_triangle (a := 0) (b := x) hx
    rw [Set.uIoc_of_le hx.le] at hstd_half
    exact hstd_half.mono_set (by
      intro p hp
      exact ⟨⟨hp.1.1, le_of_lt hp.1.2⟩, ⟨hp.2.1, le_of_lt hp.2.2⟩⟩)
  have hcomp : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => stdW (T p)) (T ⁻¹' (S ×ˢ S)) :=
    (hT_mp.integrableOn_comp_preimage T_equiv.measurableEmbedding).2 hstd
  rw [hT_pre] at hcomp
  refine hcomp.congr_fun ?_ (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  dsimp [stdW, T]
  by_cases hle : p.1 ≤ p.2
  · have hle' : x - p.2 ≤ x - p.1 := by linarith
    rw [if_pos hle', if_pos hle]
    have h1 : x - p.2 - 0 = x - p.2 := by ring
    have h2 : x - p.1 - (x - p.2) = p.2 - p.1 := by ring
    rw [h1, h2]
    ring
  · have hle' : ¬ x - p.2 ≤ x - p.1 := by linarith
    rw [if_neg hle', if_neg hle]

lemma integrableOn_abel_weight_triangle {x : ℝ} (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
  have h_open := integrableOn_abel_weight_triangle_open hx
  rw [Set.uIoo_of_le hx.le] at h_open
  rw [Set.uIoc_of_le hx.le]
  have h_ae : (Set.Ioc 0 x ×ˢ Set.Ioc 0 x : Set (ℝ × ℝ)) =ᵐ[volume]
      (Set.Ioo 0 x ×ˢ Set.Ioo 0 x : Set (ℝ × ℝ)) :=
    MeasureTheory.Measure.set_prod_ae_eq Ioo_ae_eq_Ioc.symm Ioo_ae_eq_Ioc.symm
  exact h_open.congr_set_ae h_ae


lemma integrableOn_abel_kernel {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hg : ContinuousOn g (Set.Icc 0 x)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => if p.1 ≤ p.2 then
        (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * g p.1 else 0)
      (Set.uIoc 0 x ×ˢ Set.uIoc 0 x) := by
  rw [Set.uIoc_of_le hx.le]
  let S : Set (ℝ × ℝ) := Set.Ioc 0 x ×ˢ Set.Ioc 0 x
  let W : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ else 0
  let K : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then
    (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * g p.1 else 0
  have hW_int : IntegrableOn W S := by
    dsimp [W, S]
    simpa [Set.uIoc_of_le hx.le] using integrableOn_abel_weight_triangle hx
  have hg_bound : ∃ C, ∀ t ∈ Set.Icc 0 x, ‖g t‖ ≤ C := by
    have hcont_norm : ContinuousOn (fun t : ℝ => ‖g t‖) (Set.Icc 0 x) := hg.norm
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_norm
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  obtain ⟨C, hC⟩ := hg_bound
  have hCW_int : Integrable (fun p : ℝ × ℝ => C * W p) (volume.restrict S) := by
    have h := hW_int.const_mul C
    simpa [MeasureTheory.IntegrableOn, mul_comm] using h
  have hK_meas : AEStronglyMeasurable K (volume.restrict S) := by
    have hg_fst_cont : ContinuousOn (fun p : ℝ × ℝ => g p.1) S := by
      dsimp [S]
      apply hg.comp continuous_fst.continuousOn
      intro p hp
      exact ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hg_fst_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1) (volume.restrict S) :=
      hg_fst_cont.aestronglyMeasurable (measurableSet_Ioc.prod measurableSet_Ioc)
    have hW_meas : AEStronglyMeasurable W (volume.restrict S) := hW_int.aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => W p * g p.1) (volume.restrict S) :=
      hW_meas.mul hg_fst_meas
    refine hprod.congr ?_
    filter_upwards with p
    dsimp [K, W]
    by_cases hle : p.1 ≤ p.2
    · rw [if_pos hle, if_pos hle]
    · rw [if_neg hle, if_neg hle, zero_mul]

  have hK_bound : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict S), ‖K p‖ ≤ C * W p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hp1 : p.1 ∈ Set.Icc 0 x := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hgC : ‖g p.1‖ ≤ C := hC p.1 hp1
    dsimp [K, W]
    by_cases hle : p.1 ≤ p.2
    · have hw_nonneg : 0 ≤ (Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ :=
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      rw [if_pos hle, if_pos hle]
      calc
        ‖(Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹ * g p.1‖
            = ((Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹) * ‖g p.1‖ := by
              rw [norm_mul, Real.norm_of_nonneg hw_nonneg]
        _ ≤ ((Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹) * C :=
              mul_le_mul_of_nonneg_left hgC hw_nonneg
        _ = C * ((Real.sqrt (p.2 - p.1))⁻¹ * (Real.sqrt (x - p.2))⁻¹) := by ring
    · simp [W, hle, K, hle]
  have hK_int : Integrable K (volume.restrict S) :=
    Integrable.mono' hCW_int hK_meas hK_bound
  simpa [MeasureTheory.IntegrableOn, S] using hK_int



end Commons.Analysis.Abel
