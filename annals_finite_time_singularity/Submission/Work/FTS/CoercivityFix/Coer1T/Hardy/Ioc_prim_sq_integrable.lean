import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

open MeasureTheory Set Filter
open scoped Topology

/-- If `s ↦ (Ψ s)^2/s^2` is integrable on `(0,1]`, then so is `s ↦ (Ψ s)^2/s`
(note `1/s ≤ 1/s^2` on `(0,1]` and `s * ((Ψ s)^2/s^2) = (Ψ s)^2/s`). -/
theorem iocPrim_integrableOn_sq_div_self {Ψ : ℝ → ℝ}
    (hint : IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Ioc 0 1)) :
    IntegrableOn (fun s => (Ψ s) ^ 2 / s) (Ioc 0 1) := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ => s * ((Ψ s) ^ 2 / s ^ 2))
      (volume.restrict (Ioc 0 1)) :=
    continuous_id.aestronglyMeasurable.mul hint.1
  have hae : (fun s : ℝ => (Ψ s) ^ 2 / s)
      =ᵐ[volume.restrict (Ioc 0 1)] (fun s => s * ((Ψ s) ^ 2 / s ^ 2)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    field_simp
  refine hint.mono' (hmeas.congr hae.symm) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with s hs
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hs.1.le)]
  rw [div_le_div_iff₀ hs.1 (pow_pos hs.1 2)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (Ψ s)) hs.1.le) (sub_nonneg.mpr hs.2),
    sq_nonneg (Ψ s), hs.1, hs.2]

/-- A set integral of a function that is nonnegative on the set is nonnegative
(with Mathlib's convention that a non-integrable function has integral `0`). -/
theorem iocPrim_setIntegral_nonneg_of_nonnegOn {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, 0 ≤ f x) : 0 ≤ ∫ x in s, f x := by
  by_cases h : IntegrableOn f s
  · exact integral_nonneg_of_ae ((ae_restrict_iff' hs).mpr (Eventually.of_forall hf))
  · rw [integral_undef h]

/-- The elementary AM–GM inequality `2|a| ≤ t a²/s + s/t` for `s, t > 0`. -/
theorem iocPrim_two_mul_abs_le (t s a : ℝ) (hs : 0 < s) (ht : 0 < t) :
    2 * |a| ≤ t * (a ^ 2 / s) + s / t := by
  have hts : 0 < t * s := mul_pos ht hs
  have hiff : 0 ≤ t * (a ^ 2 / s) + s / t - 2 * |a| := by
    refine (mul_nonneg_iff_of_pos_right hts).mp ?_
    have heq : (t * (a ^ 2 / s) + s / t - 2 * |a|) * (t * s) = (t * |a| - s) ^ 2 := by
      rw [← sq_abs a]
      field_simp
      ring
    rw [heq]
    positivity
  linarith

/-- Optimisation step: if `c ≤ t φ + B/t` for all `t > 0` (with `c, φ, B ≥ 0`) then
`c² ≤ 4 φ B`. -/
theorem iocPrim_sq_le_four_mul_of_amgm {c φ B : ℝ} (hc : 0 ≤ c) (hφ : 0 ≤ φ) (hB : 0 ≤ B)
    (key : ∀ t : ℝ, 0 < t → c ≤ t * φ + B / t) : c ^ 2 ≤ 4 * (φ * B) := by
  by_cases hφ0 : φ = 0
  · have hkeys : ∀ t : ℝ, 0 < t → c ≤ B / t := fun t ht => by simpa [hφ0] using key t ht
    by_cases hc0 : c = 0
    · rw [hc0]
      have : (0 : ℝ) ≤ 4 * (φ * B) := mul_nonneg (by norm_num) (mul_nonneg hφ hB)
      simpa using this
    · exfalso
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      by_cases hB0 : B = 0
      · have hk := hkeys 1 one_pos
        rw [hB0, zero_div] at hk
        linarith
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
        have ht : 0 < B / c + 1 := by positivity
        have hk := hkeys (B / c + 1) ht
        have hlt : B / (B / c + 1) < c := by
          rw [div_lt_iff₀ ht]
          have hc1 : c * (B / c + 1) = B + c := by field_simp
          rw [hc1]; linarith
        linarith
  · have hφpos : 0 < φ := lt_of_le_of_ne hφ (Ne.symm hφ0)
    by_cases hc0 : c = 0
    · rw [hc0]
      have : (0 : ℝ) ≤ 4 * (φ * B) := mul_nonneg (by norm_num) (mul_nonneg hφ hB)
      simpa using this
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have ht : 0 < c / (2 * φ) := div_pos hcpos (by linarith)
      have hk := key (c / (2 * φ)) ht
      have h1 : (c / (2 * φ)) * φ = c / 2 := by field_simp
      have h2 : B / (c / (2 * φ)) = 2 * B * φ / c := by field_simp
      rw [h1, h2] at hk
      have hmul : c * c ≤ c * (c / 2 + 2 * B * φ / c) := mul_le_mul_of_nonneg_left hk hcpos.le
      have h3 : c * (c / 2 + 2 * B * φ / c) = c ^ 2 / 2 + 2 * B * φ := by field_simp
      rw [h3] at hmul
      nlinarith

/-- **Weighted Cauchy–Schwarz bound for the primitive.**  Under the hypothesis that
`s ↦ (Ψ s)^2/s^2` is integrable on `(0,1]` (which makes `s ↦ (Ψ s)^2/s` integrable there, so the
right-hand side is a genuine integral), for `0 < z ≤ 1`:
`(∫_0^z Ψ)^2 ≤ (z^2/2) * ∫_0^z (Ψ s)^2/s ds`.

The proof splits on whether `Ψ` is integrable on `(0,z]`; in the negative case the left-hand side
is `0` by `integral_undef`.  In the positive case we use the parameterised AM–GM inequality
`2|Ψ s| ≤ t (Ψ s)^2/s + s/t` for `t > 0`, integrate it, and then optimise `t`. -/
theorem prim_sq_le_weight {Ψ : ℝ → ℝ}
    (hint : IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Ioc 0 1))
    (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) :
    (∫ s in Ioc 0 z, Ψ s) ^ 2 ≤ (z ^ 2 / 2) * ∫ s in Ioc 0 z, (Ψ s) ^ 2 / s := by
  have hψ : IntegrableOn (fun s => (Ψ s) ^ 2 / s) (Ioc 0 z) :=
    (iocPrim_integrableOn_sq_div_self hint).mono_set fun s hs => ⟨hs.1, le_trans hs.2 hz1⟩
  have hφnn : 0 ≤ ∫ s in Ioc 0 z, (Ψ s) ^ 2 / s :=
    iocPrim_setIntegral_nonneg_of_nonnegOn measurableSet_Ioc fun s hs =>
      div_nonneg (sq_nonneg _) hs.1.le
  have hB : 0 ≤ z ^ 2 / 2 := by positivity
  have hIdint : ∫ s in Ioc 0 z, s = z ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hz.le]
    simp
  have hIdm : IntegrableOn (fun s : ℝ => s) (Ioc 0 z) :=
    (continuous_id.integrableOn_Icc (a := 0) (b := z)).mono_set Ioc_subset_Icc_self
  -- the integrated AM–GM inequality, for every `t > 0`
  have key : ∀ t : ℝ, 0 < t →
      2 * |∫ s in Ioc 0 z, Ψ s|
        ≤ t * (∫ s in Ioc 0 z, (Ψ s) ^ 2 / s) + (z ^ 2 / 2) / t := by
    intro t ht
    by_cases hΨ : IntegrableOn Ψ (Ioc 0 z)
    · have hΨabs : IntegrableOn (fun s => |Ψ s|) (Ioc 0 z) := by
        change Integrable (fun s => |Ψ s|) (volume.restrict (Ioc 0 z))
        simpa only [Real.norm_eq_abs] using hΨ.norm
      have hright : IntegrableOn (fun s => t * ((Ψ s) ^ 2 / s) + s / t) (Ioc 0 z) :=
        (hψ.const_mul t).add (hIdm.div_const t)
      have hmono : ∫ s in Ioc 0 z, 2 * |Ψ s|
          ≤ ∫ s in Ioc 0 z, (t * ((Ψ s) ^ 2 / s) + s / t) := by
        refine integral_mono_ae (hΨabs.const_mul 2) hright ?_
        exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun s hs => iocPrim_two_mul_abs_le t s (Ψ s) hs.1 ht)
      have hsplit : ∫ s in Ioc 0 z, (t * ((Ψ s) ^ 2 / s) + s / t)
          = t * (∫ s in Ioc 0 z, (Ψ s) ^ 2 / s) + (z ^ 2 / 2) / t := by
        rw [integral_add (hψ.const_mul t) (hIdm.div_const t), integral_const_mul, integral_div,
          hIdint]
      have hleabs : 2 * |∫ s in Ioc 0 z, Ψ s| ≤ ∫ s in Ioc 0 z, 2 * |Ψ s| := by
        have h := norm_integral_le_integral_norm (μ := volume.restrict (Ioc 0 z))
          (fun s => 2 * Ψ s)
        rw [integral_const_mul] at h
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
        simpa using h
      linarith
    · rw [integral_undef hΨ, abs_zero, mul_zero]
      have h1 : 0 ≤ t * (∫ s in Ioc 0 z, (Ψ s) ^ 2 / s) := mul_nonneg ht.le hφnn
      have h2 : 0 ≤ (z ^ 2 / 2) / t := div_nonneg hB ht.le
      linarith
  have hmain := iocPrim_sq_le_four_mul_of_amgm (mul_nonneg (by norm_num) (abs_nonneg (∫ s in Ioc 0 z, Ψ s)))
    hφnn hB key
  have hsq : (2 * |∫ s in Ioc 0 z, Ψ s|) ^ 2 = 4 * (∫ s in Ioc 0 z, Ψ s) ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num
  rw [hsq] at hmain
  nlinarith [hmain]

/-- Integration by parts identity behind the weighted Hardy bound: with
`φ z = ∫ t in 0..z, ψ t` and `q z = ψ z / z` (for `z > 0`),
`∫_ε^1 φ(z)/z² dz = ∫_ε^1 q(z) dz - φ 1 + φ ε/ε`. -/
theorem iocPrim_prim_ftc {ψ q : ℝ → ℝ} (hψ : IntervalIntegrable ψ volume 0 1)
    (hψq : ∀ z ∈ Ioc 0 1, ψ z / z = q z) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ z in ε..1, (∫ t in (0 : ℝ)..z, ψ t) / z ^ 2
      = (∫ z in ε..1, q z) - (∫ t in (0 : ℝ)..1, ψ t) + (∫ t in (0 : ℝ)..ε, ψ t) / ε := by
  have hφ_ac : AbsolutelyContinuousOnInterval (fun z => ∫ t in (0 : ℝ)..z, ψ t) ε 1 :=
    (hψ.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by
        rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)).mono (by
      rw [uIcc_of_le hε1, uIcc_of_le zero_le_one]
      exact fun x hx => ⟨hε.le.trans hx.1, hx.2⟩)
  have hne : ∀ x ∈ uIcc ε 1, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hε1] at hx
    exact ne_of_gt (lt_of_lt_of_le hε hx.1)
  have hg_ac : AbsolutelyContinuousOnInterval (fun z : ℝ => -(z⁻¹)) ε 1 :=
    ContDiffOn.absolutelyContinuousOnInterval ((contDiffOn_id.inv hne).neg)
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hφ_ac hg_ac
  have hderiv_g : ∀ x ∈ uIoc ε 1, deriv (fun z : ℝ => -(z⁻¹)) x = (x ^ 2)⁻¹ := by
    intro x hx
    rw [uIoc_of_le hε1] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hε hx.1)
    have hd := (hasDerivAt_inv hx0).neg
    have hd' : deriv (fun z : ℝ => -(z⁻¹)) x = -(-(x ^ 2)⁻¹) := hd.deriv
    rw [hd', neg_neg]
  have hderiv_φ : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ uIoc ε 1 → deriv (fun z => ∫ t in (0 : ℝ)..z, ψ t) x = ψ x := by
    filter_upwards [hψ.ae_hasDerivAt_integral] with x hx hxmem
    rw [uIoc_of_le hε1] at hxmem
    have hx01 : x ∈ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]
      exact ⟨le_of_lt (lt_trans hε hxmem.1), hxmem.2⟩
    exact ((hx hx01) 0 (by rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)).deriv
  have hL : ∫ x in ε..1, (∫ t in (0 : ℝ)..x, ψ t) * deriv (fun z : ℝ => -(z⁻¹)) x
      = ∫ x in ε..1, (∫ t in (0 : ℝ)..x, ψ t) / x ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Eventually.of_forall hderiv_g] with x hx hxmem
    rw [hx hxmem, div_eq_mul_inv]
  have hR : ∫ x in ε..1, deriv (fun z : ℝ => ∫ t in (0 : ℝ)..z, ψ t) x * (fun z : ℝ => -(z⁻¹)) x
      = -∫ x in ε..1, q x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv_φ] with x hx hxmem
    have hmem : x ∈ Ioc ε 1 := by
      have h := hxmem
      rwa [uIoc_of_le hε1] at h
    rw [hx hxmem, show ψ x * -x⁻¹ = -(ψ x / x) by ring,
      hψq x ⟨lt_trans hε hmem.1, hmem.2⟩]
  rw [hL, hR] at hIBP
  simp only [inv_one, sub_neg_eq_add] at hIBP
  have h3 : (∫ t in (0 : ℝ)..1, ψ t) * (-1) - (∫ t in (0 : ℝ)..ε, ψ t) * (-(ε⁻¹))
        + ∫ x in ε..1, q x
      = -(∫ t in (0 : ℝ)..1, ψ t) + (∫ t in (0 : ℝ)..ε, ψ t) / ε + ∫ x in ε..1, q x := by
    ring
  rw [h3] at hIBP
  linarith [hIBP]

/-- **Weighted Hardy bound for the primitive of `s ↦ (Ψ s)^2/s`.** -/
theorem hardy_prim_weight {Ψ : ℝ → ℝ}
    (hint : IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Ioc 0 1)) :
    IntegrableOn (fun z => (∫ s in Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2) (Ioc 0 1) ∧
      ∫ z in Ioc 0 1, (∫ s in Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2
        ≤ ∫ s in Ioc 0 1, (Ψ s) ^ 2 / s ^ 2 := by
  set ψ : ℝ → ℝ := fun s => (Ψ s) ^ 2 / s with hψ
  set q : ℝ → ℝ := fun s => (Ψ s) ^ 2 / s ^ 2 with hq
  have hqint : IntegrableOn q (Ioc 0 1) := by simpa [hq] using hint
  have hψint : IntegrableOn ψ (Ioc 0 1) := by simpa [hψ] using iocPrim_integrableOn_sq_div_self hint
  have hψI : IntervalIntegrable ψ volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hψint
  have hψq : ∀ z ∈ Ioc 0 1, ψ z / z = q z := by
    rintro z hz
    simp only [hψ, hq]
    field_simp
  -- `ψ` agrees with `t * q t` on `(0,1]`
  have hψmul : ∀ t ∈ Ioc 0 1, ψ t = t * q t := by
    intro t ht
    have h := hψq t ht
    rw [div_eq_iff (ne_of_gt ht.1)] at h
    rw [h]; ring
  -- the set-integral form and the interval-integral form of the primitive agree
  have hagree : ∀ z ∈ Ioc 0 1, (∫ s in Ioc 0 z, ψ s) = ∫ t in (0 : ℝ)..z, ψ t := by
    intro z hz
    exact (intervalIntegral.integral_of_le hz.1.le).symm
  have hφnn : ∀ z ∈ Ioc 0 1, 0 ≤ ∫ t in (0 : ℝ)..z, ψ t := by
    intro z hz
    rw [← hagree z hz]
    exact iocPrim_setIntegral_nonneg_of_nonnegOn measurableSet_Ioc fun s hs =>
      div_nonneg (sq_nonneg _) hs.1.le
  -- the bound on the truncated integrals
  have hbound : ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ z in Ioc ε 1, (∫ s in Ioc 0 z, ψ s) / z ^ 2 ≤ ∫ s in Ioc 0 1, q s := by
    intro ε hε hε1
    have hftc := iocPrim_prim_ftc hψI hψq hε hε1
    have hcongr : ∫ z in Ioc ε 1, (∫ s in Ioc 0 z, ψ s) / z ^ 2
        = ∫ z in Ioc ε 1, (∫ t in (0 : ℝ)..z, ψ t) / z ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
      rw [hagree z ⟨lt_trans hε hz.1, hz.2⟩]
    have hftc' : ∫ z in Ioc ε 1, (∫ t in (0 : ℝ)..z, ψ t) / z ^ 2
        = (∫ z in Ioc ε 1, q z) - (∫ t in (0 : ℝ)..1, ψ t)
          + (∫ t in (0 : ℝ)..ε, ψ t) / ε := by
      rw [← intervalIntegral.integral_of_le hε1, ← intervalIntegral.integral_of_le hε1]
      exact hftc
    -- the last term is bounded by `∫_{(0,ε]} q`
    have hφε : (∫ t in (0 : ℝ)..ε, ψ t) / ε ≤ ∫ s in Ioc 0 ε, q s := by
      have h1 : ∫ t in (0 : ℝ)..ε, ψ t ≤ (∫ s in Ioc 0 ε, q s) * ε := by
        rw [mul_comm]
        have hψε : IntegrableOn ψ (Ioc 0 ε) := hψint.mono_set fun s hs => ⟨hs.1, le_trans hs.2 hε1⟩
        have hqε : IntegrableOn (fun t => ε * q t) (Ioc 0 ε) :=
          (hqint.mono_set fun s hs => ⟨hs.1, le_trans hs.2 hε1⟩).const_mul ε
        have hmono : ∫ t in Ioc 0 ε, ψ t ≤ ∫ t in Ioc 0 ε, ε * q t := by
          refine integral_mono_ae hψε hqε ((ae_restrict_iff' measurableSet_Ioc).mpr ?_)
          refine Eventually.of_forall fun t ht => ?_
          rw [hψmul t ⟨ht.1, le_trans ht.2 hε1⟩]
          have hqt : 0 ≤ q t := by
            rw [hq]
            exact div_nonneg (sq_nonneg _) (sq_nonneg _)
          nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hqt]
        rw [integral_const_mul] at hmono
        rw [intervalIntegral.integral_of_le hε.le]
        exact hmono
      exact (div_le_iff₀ hε).mpr h1
    have hsum : (∫ s in Ioc 0 ε, q s) + (∫ s in Ioc ε 1, q s) = ∫ s in Ioc 0 1, q s := by
      rw [← intervalIntegral.integral_of_le hε.le, ← intervalIntegral.integral_of_le hε1,
        ← intervalIntegral.integral_of_le zero_le_one]
      have hq0ε : IntervalIntegrable q volume 0 ε :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).mpr
          (hqint.mono_set fun s hs => ⟨hs.1, le_trans hs.2 hε1⟩)
      have hqε1 : IntervalIntegrable q volume ε 1 :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).mpr
          (hqint.mono_set fun s hs => ⟨hε.trans_le hs.1.le, hs.2⟩)
      exact intervalIntegral.integral_add_adjacent_intervals hq0ε hqε1
    have hφ1nn : 0 ≤ ∫ t in (0 : ℝ)..1, ψ t := hφnn 1 ⟨zero_lt_one, le_rfl⟩
    rw [hcongr, hftc']
    linarith
  -- integrability of the truncated integrals and the cover
  have hcover : AECover (volume.restrict (Ioc (0 : ℝ) 1)) atTop
      (fun n : ℕ => Ioc (1 / ((n : ℝ) + 1)) 1) :=
    aecover_Ioc_of_Ioc (μ := (volume : Measure ℝ)) (A := (0 : ℝ)) (B := (1 : ℝ))
      tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
  set K' : ℝ → ℝ := fun z => (∫ t in (0 : ℝ)..z, ψ t) / z ^ 2 with hK'
  have hφc : ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, ψ t) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hψI
      (by rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)
  have hfi : ∀ n : ℕ,
      IntegrableOn K' (Ioc (1 / ((n : ℝ) + 1)) 1) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro n
    have hεn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsub : Ioc (1 / ((n : ℝ) + 1)) 1 ⊆ Ioc (0 : ℝ) 1 :=
      fun z hz => ⟨lt_of_lt_of_le hεn hz.1.le, hz.2⟩
    have hcont : ContinuousOn K' (Icc (1 / ((n : ℝ) + 1)) 1) := by
      have hmem : Icc (1 / ((n : ℝ) + 1)) 1 ⊆ uIcc (0 : ℝ) 1 := by
        rw [uIcc_of_le zero_le_one]
        exact fun z hz => ⟨(le_of_lt (lt_of_lt_of_le hεn hz.1)), hz.2⟩
      have h1 : ContinuousOn
          (fun z : ℝ => (∫ t in (0 : ℝ)..z, ψ t) * (z ^ 2)⁻¹) (Icc (1 / ((n : ℝ) + 1)) 1) :=
        (hφc.mono hmem).mul (ContinuousOn.inv₀ (continuous_pow 2).continuousOn
          fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hεn hz.1)))
      simpa only [hK', div_eq_mul_inv] using h1
    have hint : IntegrableOn K' (Ioc (1 / ((n : ℝ) + 1)) 1) volume :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    change Integrable K' ((volume.restrict (Ioc (0 : ℝ) 1)).restrict (Ioc (1 / ((n : ℝ) + 1)) 1))
    rw [Measure.restrict_restrict_of_subset hsub]
    exact hint
  have hnng : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] K' := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun z hz => ?_
    simp only [hK', Pi.zero_apply]
    exact div_nonneg (hφnn z hz) (by positivity)
  have hbounded : ∀ᶠ n : ℕ in atTop,
      (∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, K' x ∂(volume.restrict (Ioc (0 : ℝ) 1)))
        ≤ ∫ s in Ioc (0 : ℝ) 1, q s := by
    refine Eventually.of_forall fun n => ?_
    have hεn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hεn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsub : Ioc (1 / ((n : ℝ) + 1)) 1 ⊆ Ioc (0 : ℝ) 1 :=
      fun z hz => ⟨lt_of_lt_of_le hεn hz.1.le, hz.2⟩
    have h := hbound (1 / ((n : ℝ) + 1)) hεn hεn1
    have hμ : ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, K' x ∂(volume.restrict (Ioc (0 : ℝ) 1))
        = ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, ((∫ s in Ioc 0 x, ψ s) / x ^ 2)
            ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      simp only [hK']
      rw [hagree x ⟨lt_trans hεn hx.1, hx.2⟩]
    have hvol : ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, ((∫ s in Ioc 0 x, ψ s) / x ^ 2)
          ∂(volume.restrict (Ioc (0 : ℝ) 1))
        = ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, ((∫ s in Ioc 0 x, ψ s) / x ^ 2) := by
      rw [Measure.restrict_restrict_of_subset hsub]
    rw [hμ, hvol]
    exact h
  have hint' : Integrable K' (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae (∫ s in Ioc (0 : ℝ) 1, q s) hfi hnng
      hbounded
  have hle : ∫ x, K' x ∂(volume.restrict (Ioc (0 : ℝ) 1)) ≤ ∫ s in Ioc (0 : ℝ) 1, q s :=
    le_of_tendsto (hcover.integral_tendsto_of_countably_generated hint') hbounded
  have hae : K' =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun z => (∫ s in Ioc 0 z, ψ s) / z ^ 2) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun z hz => ?_
    simp only [hK']
    rw [hagree z hz]
  exact ⟨hint'.congr hae, by rw [← integral_congr_ae hae]; exact hle⟩

/-- **Measurability of the primitive.**  `z ↦ ∫ s in Ioc 0 z, Ψ s` is a.e. strongly measurable on
`(0,1]` as soon as `s ↦ (Ψ s)^2/s^2` is integrable there.  (No measurability of `Ψ` itself can be
derived from the hypothesis, so the proof proceeds by showing that the set of `z` for which `Ψ` is
integrable on `(0,z]` is an initial segment; on it the primitive is continuous, outside it the
integral vanishes by `integral_undef`.) -/
theorem aesm_prim_Ioc {Ψ : ℝ → ℝ}
    (_hint : IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Ioc 0 1)) :
    AEStronglyMeasurable (fun z => ∫ s in Ioc 0 z, Ψ s) (volume.restrict (Ioc 0 1)) := by
  set F : ℝ → ℝ := fun z => ∫ s in Ioc 0 z, Ψ s with hF
  change AEStronglyMeasurable F (volume.restrict (Ioc 0 1))
  -- the set of `z ∈ (0,1]` for which `Ψ` is integrable on `(0,z]`
  set A : Set ℝ := {z | 0 < z ∧ z ≤ 1 ∧ IntegrableOn Ψ (Ioc 0 z)} with hA
  set z₀ : ℝ := sSup (A ∪ {0}) with hz₀
  have hbdd : BddAbove (A ∪ {0}) := by
    refine ⟨1, ?_⟩
    rintro z (hz | hz)
    · exact hz.2.1
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  have hne : (A ∪ {0}).Nonempty := ⟨0, Or.inr rfl⟩
  have hz₀_le : z₀ ≤ 1 := by
    rw [hz₀]
    refine csSup_le hne ?_
    rintro a (ha | rfl)
    · exact ha.2.1
    · norm_num
  -- `A` is downward closed
  have hdown : ∀ z ∈ A, ∀ y, 0 < y → y ≤ z → y ∈ A := by
    rintro z ⟨hz1, hz2, hz3⟩ y hy hyz
    exact ⟨hy, le_trans hyz hz2, hz3.mono_set fun s hs => ⟨hs.1, le_trans hs.2 hyz⟩⟩
  -- below `z₀`, `Ψ` is integrable on `(0,z]`
  have hK1 : ∀ z, 0 < z → z < z₀ → IntegrableOn Ψ (Ioc 0 z) := by
    intro z hz hlt
    by_contra hcon
    have hle : sSup (A ∪ {0}) ≤ z := by
      refine csSup_le hne ?_
      rintro a (ha | rfl)
      · by_contra hgt
        push Not at hgt
        exact hcon (hdown a ha z hz hgt.le).2.2
      · exact hz.le
    rw [← hz₀] at hle
    linarith
  -- above `z₀`, `Ψ` is not integrable on `(0,z]`, hence the integral vanishes
  have hK2 : ∀ z, 0 < z → z ≤ 1 → z₀ < z → ¬ IntegrableOn Ψ (Ioc 0 z) := by
    intro z hz hz1 hlt hcon
    have hmem : z ∈ A ∪ {0} := Or.inl ⟨hz, hz1, hcon⟩
    have := le_csSup hbdd hmem
    rw [← hz₀] at this
    linarith
  have hF0 : ∀ z, 0 < z → z ≤ 1 → z₀ < z → F z = 0 := by
    intro z hz hz1 hlt
    have h := hK2 z hz hz1 hlt
    change (∫ s in Ioc 0 z, Ψ s) = 0
    exact integral_undef h
  -- `F` is continuous on `(0, z₀)`
  have hcont : ContinuousOn F (Ioo 0 z₀) := by
    intro x hx
    obtain ⟨a, hxa, haz⟩ : ∃ a, x < a ∧ a < z₀ :=
      ⟨(x + z₀) / 2, by linarith [hx.2], by linarith [hx.2]⟩
    have ha_gt0 : 0 < a := lt_trans hx.1 hxa
    have ha_mem : IntegrableOn Ψ (Ioc 0 a) := hK1 a ha_gt0 haz
    have hint : IntervalIntegrable Ψ volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha_gt0.le).mpr ha_mem
    have hcio : ContinuousOn (fun b => ∫ t in (0 : ℝ)..b, Ψ t) (uIcc 0 a) :=
      intervalIntegral.continuousOn_primitive_interval' hint
        (by rw [uIcc_of_le ha_gt0.le]; exact ⟨le_rfl, ha_gt0.le⟩)
    rw [uIcc_of_le ha_gt0.le] at hcio
    have hFcont : ContinuousOn F (Icc 0 a) := by
      refine hcio.congr fun b hb => ?_
      change (∫ s in Ioc 0 b, Ψ s) = ∫ t in (0 : ℝ)..b, Ψ t
      exact (intervalIntegral.integral_of_le hb.1).symm
    exact (hFcont.continuousAt (Icc_mem_nhds hx.1 hxa)).continuousWithinAt
  -- a.e. strongly measurable on `(0, z₀)` (continuity) ...
  have h1 : AEStronglyMeasurable F (volume.restrict (Ioo 0 z₀)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- ... and on `[z₀, 1] ∩ (0,1]` (where `F` vanishes a.e.)
  have h2 : AEStronglyMeasurable F (volume.restrict (Ici z₀ ∩ Ioc 0 1)) := by
    have hae : F =ᵐ[volume.restrict (Ici z₀ ∩ Ioc 0 1)] (fun _ : ℝ => 0) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ici.inter measurableSet_Ioc),
        MeasureTheory.ae_iff]
      refine measure_mono_null ?_ (measure_singleton z₀)
      intro z hz
      rw [Set.mem_singleton_iff]
      obtain ⟨hzle, hz0, hz1, hzF⟩ : z₀ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ ¬(F z = 0) := by
        simpa [not_imp] using hz
      rcases lt_or_eq_of_le hzle with hlt | heq
      · exact absurd (hF0 z hz0 hz1 hlt) hzF
      · exact heq.symm
    have h0 : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (volume.restrict (Ici z₀ ∩ Ioc 0 1)) := aestronglyMeasurable_const
    exact h0.congr hae.symm
  have hU : AEStronglyMeasurable F (volume.restrict (Ioo 0 z₀ ∪ (Ici z₀ ∩ Ioc 0 1))) :=
    aestronglyMeasurable_union_iff.mpr ⟨h1, h2⟩
  refine hU.mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro z hz
  rcases lt_or_ge z z₀ with hlt | hge
  · exact Or.inl ⟨hz.1, hlt⟩
  · exact Or.inr ⟨hge, hz⟩

/-- **Finite-time singularity, Coer1T/Hardy: the primitive squared is integrable and satisfies the
Hardy bound.**  If `s ↦ (Ψ s)^2/s^2` is integrable on `(0,1]`, then
`z ↦ (∫_0^z Ψ)^2/z^4` is integrable there and
`∫_0^1 (∫_0^z Ψ)^2/z^4 dz ≤ (1/2) ∫_0^1 Ψ(s)^2/s^2 ds`. -/
theorem Ioc_prim_sq_integrable (Ψ : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Set.Ioc 0 1)) :
    MeasureTheory.IntegrableOn (fun z => (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4) (Set.Ioc 0 1) ∧
      ∫ z in Set.Ioc 0 1, (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4
        ≤ (1 / 2) * ∫ s in Set.Ioc 0 1, (Ψ s) ^ 2 / s ^ 2 := by
  have hFasm := aesm_prim_Ioc hint
  have hhardy := hardy_prim_weight hint
  have hpt : ∀ z ∈ Set.Ioc 0 1,
      (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4
        ≤ (1 / 2) * ((∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2) := by
    intro z hz
    have h := prim_sq_le_weight hint z hz.1 hz.2
    have hz4 : 0 < z ^ 4 := pow_pos hz.1 4
    have h2 : ((z ^ 2 / 2) * (∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s)) / z ^ 4
        = (1 / 2) * ((∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2) := by
      field_simp
    calc (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4
        ≤ ((z ^ 2 / 2) * (∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s)) / z ^ 4 :=
          div_le_div_of_nonneg_right h hz4.le
      _ = (1 / 2) * ((∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2) := h2
  have hasm : AEStronglyMeasurable
      (fun z => (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4) (volume.restrict (Set.Ioc 0 1)) := by
    have h1 : AEStronglyMeasurable (fun z => (∫ s in Set.Ioc 0 z, Ψ s) ^ 2)
        (volume.restrict (Set.Ioc 0 1)) := hFasm.pow 2
    have h2 : AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹) (volume.restrict (Set.Ioc 0 1)) :=
      ((measurable_id.pow_const 4).inv).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        ((fun z => (∫ s in Set.Ioc 0 z, Ψ s) ^ 2) * fun z : ℝ => (z ^ 4)⁻¹)
        (volume.restrict (Set.Ioc 0 1)) := h1.mul h2
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Pi.mul_apply, div_eq_mul_inv]
  have hMint : IntegrableOn (fun z => (1 / 2) * ((∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2))
      (Set.Ioc 0 1) := hhardy.1.const_mul (1 / 2)
  have hfint : IntegrableOn (fun z => (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)
      (Set.Ioc 0 1) := by
    refine hMint.mono' hasm ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity : (0:ℝ) ≤ z ^ 4))]
      exact hpt z hz)
  refine ⟨hfint, ?_⟩
  have h1 : ∫ z in Set.Ioc 0 1, (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4
      ≤ ∫ z in Set.Ioc 0 1, (1 / 2) * ((∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 / s) / z ^ 2) := by
    refine integral_mono_ae hfint hMint ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
  rw [integral_const_mul] at h1
  linarith [hhardy.2]

end Work.FTS.CoercivityFix.Coer1T.Hardy
