import Mathlib
import Submission.Commons.Analysis.Integral.doubleIntegral_inv_one_sub_mul
import Submission.Commons.Analysis.Integral.integrableOn_l2_rpow_eighth_bound_zero_one

/-!
# `doubleIntegral_Bkernel_bound`

Bound for the iterated integral over the unit square of the *`B`-kernel*

    B(s,t)^n / (1 - s·t)^(n+1),   B(s,t) = (1 - s·t) - (1 - s²)(1 - t²).

The key observations are purely algebraic: on `[0,1]²`

    0 ≤ B(s,t) ≤ 1 - s·t .

The upper bound is immediate (`B = (1-st) - (1-s²)(1-t²)` and
`(1-s²)(1-t²) ≥ 0`), and the lower bound follows from
`B = (s-t)² + s·t·(1 - s·t)`.  Consequently, for `1 - s·t > 0`,

    B(s,t)^n / (1 - s·t)^(n+1) ≤ (1 - s·t)^n / (1 - s·t)^(n+1) = (1 - s·t)⁻¹ ,

and the integrand is nonnegative.  Integrating the resulting bound against
`doubleIntegral_inv_one_sub_mul` finishes the proof.
-/

namespace Commons.Analysis.Integral

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators

private abbrev unitIoc : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

/-! ## Pointwise algebra on the unit square -/

private lemma Bker_nonneg {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ (1 - s*t) - (1 - s^2)*(1 - t^2) := by
  have hst0 : 0 ≤ s*t := mul_nonneg hs.1 ht.1
  have hst1 : s*t ≤ 1 := by
    have h := mul_le_mul hs.2 ht.2 ht.1 (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have hprod : 0 ≤ s*t*(1 - s*t) := mul_nonneg hst0 (by linarith)
  have hkey : (1 - s*t) - (1 - s^2)*(1 - t^2) = (s-t)^2 + s*t*(1 - s*t) := by ring
  rw [hkey]
  exact add_nonneg (sq_nonneg (s-t)) hprod

private lemma Bker_le {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1 - s*t) - (1 - s^2)*(1 - t^2) ≤ 1 - s*t := by
  have h1 : 0 ≤ 1 - s^2 := by nlinarith [hs.1, hs.2]
  have h2 : 0 ≤ 1 - t^2 := by nlinarith [ht.1, ht.2]
  have h : 0 ≤ (1 - s^2)*(1 - t^2) := mul_nonneg h1 h2
  linarith

private lemma hst_lt_one {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    s*t < 1 := by
  have hle : s*t ≤ s*1 := mul_le_mul_of_nonneg_left (le_of_lt ht.2) (le_of_lt hs.1)
  rw [mul_one] at hle
  linarith [hs.2]

/-- The elementary analytic inequality `B^n / a^{n+1} ≤ a⁻¹` for `0 ≤ B ≤ a`, `a > 0`. -/
private lemma pow_div_pow_succ_le_inv {a B : ℝ} (hB0 : 0 ≤ B) (ha : 0 < a) (hBa : B ≤ a)
    (n : ℕ) : B^n / a^(n+1) ≤ a⁻¹ := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hpow : B^n ≤ a^n := pow_le_pow_left₀ hB0 hBa n
  calc B^n / a^(n+1) ≤ a^n / a^(n+1) := div_le_div_of_nonneg_right hpow (pow_nonneg ha0 _)
    _ = a⁻¹ := by
        rw [pow_succ]
        field_simp

/-! ## The two kernels -/

/-- `F(z) = B(z₁,z₂)^n / (1 - z₁z₂)^{n+1}`. -/
private def Fker (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  ((1 - z.1*z.2) - (1 - z.1^2)*(1 - z.2^2))^n / (1 - z.1*z.2)^(n+1)

/-- `G(z) = (1 - z₁z₂)⁻¹`. -/
private def Gker (z : ℝ × ℝ) : ℝ := (1 - z.1*z.2)⁻¹

private lemma Fker_nonneg {z : ℝ × ℝ} (hz1 : z.1 ∈ Set.Ioo (0:ℝ) 1)
    (hz2 : z.2 ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) : 0 ≤ Fker n z := by
  have hs : z.1 ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz1.1, le_of_lt hz1.2⟩
  have ht : z.2 ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz2.1, le_of_lt hz2.2⟩
  have hB0 : 0 ≤ (1 - z.1*z.2) - (1 - z.1^2)*(1 - z.2^2) := Bker_nonneg hs ht
  have ha : 0 < 1 - z.1*z.2 := by have := hst_lt_one hz1 hz2; linarith
  simp only [Fker]
  exact div_nonneg (pow_nonneg hB0 n) (pow_nonneg (le_of_lt ha) (n+1))

private lemma Fker_le_Gker {z : ℝ × ℝ} (hz1 : z.1 ∈ Set.Ioo (0:ℝ) 1)
    (hz2 : z.2 ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) : Fker n z ≤ Gker z := by
  have hs : z.1 ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz1.1, le_of_lt hz1.2⟩
  have ht : z.2 ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz2.1, le_of_lt hz2.2⟩
  have hB0 : 0 ≤ (1 - z.1*z.2) - (1 - z.1^2)*(1 - z.2^2) := Bker_nonneg hs ht
  have hBa : (1 - z.1*z.2) - (1 - z.1^2)*(1 - z.2^2) ≤ 1 - z.1*z.2 := Bker_le hs ht
  have ha : 0 < 1 - z.1*z.2 := by have := hst_lt_one hz1 hz2; linarith
  simp only [Fker, Gker]
  exact pow_div_pow_succ_le_inv hB0 ha hBa n

/-! ## Integrability on the unit square -/

private lemma inv_one_sub_mul_le_rpow {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1)
    (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    (1 - s*t)⁻¹ ≤ (1-s)^(-(1/2:ℝ)) * (1-t)^(-(1/2:ℝ)) := by
  have hs0 : 0 < s := hs.1
  have hs1 : s < 1 := hs.2
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  have h1st : 0 < 1 - s*t := by nlinarith [hst_lt_one hs ht]
  have hPpos : 0 < (1-s)*(1-t) := mul_pos h1s h1t
  have hmono : (1 - s)*(1 - t) ≤ (1 - s*t)^2 := by
    calc (1 - s)*(1 - t) ≤ (1 - s)*(1 - s*t) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt h1s)
            nlinarith [hs1, ht0]
      _ ≤ (1 - s*t)*(1 - s*t) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt h1st)
            nlinarith [hs0, ht1]
      _ = (1 - s*t)^2 := by ring
  have hsqrt : Real.sqrt ((1-s)*(1-t)) ≤ 1 - s*t := by
    calc Real.sqrt ((1-s)*(1-t)) ≤ Real.sqrt ((1 - s*t)^2) := Real.sqrt_le_sqrt hmono
      _ = 1 - s*t := Real.sqrt_sq (le_of_lt h1st)
  have hsqrpos : 0 < Real.sqrt ((1-s)*(1-t)) := Real.sqrt_pos.mpr hPpos
  calc (1 - s*t)⁻¹ ≤ (Real.sqrt ((1-s)*(1-t)))⁻¹ := inv_anti₀ hsqrpos hsqrt
    _ = (1-s)^(-(1/2:ℝ)) * (1-t)^(-(1/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hPpos),
          Real.mul_rpow (le_of_lt h1s) (le_of_lt h1t)]

private lemma integrable_one_sub_rpow_Ioc :
    Integrable (fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) unitIoc := by
  have hIoo : IntegrableOn (fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) (Set.Ioo (0:ℝ) 1) :=
    integrableOn_Ioo_one_sub_rpow _ (by norm_num)
  have hf1 : ‖(fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) 1‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_Ioc_iff_integrableOn_Ioo
    (f := fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) (a := 0) (b := 1) hf1).mpr hIoo

private lemma ae_mem_Ioo : ∀ᵐ x ∂unitIoc, x ∈ Set.Ioo (0:ℝ) 1 := by
  have h1 : ∀ᵐ x ∂unitIoc, x ∈ Set.Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have h2 : ∀ᵐ x ∂unitIoc, x ≠ 1 := Measure.ae_ne unitIoc 1
  filter_upwards [h1, h2] with x hx hne
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩

private lemma ae_prod_mem_Ioo :
    ∀ᵐ z ∂(unitIoc.prod unitIoc), z.1 ∈ Set.Ioo (0:ℝ) 1 ∧ z.2 ∈ Set.Ioo (0:ℝ) 1 := by
  have hz1 : ∀ᵐ z ∂(unitIoc.prod unitIoc), z.1 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun z : ℝ×ℝ => z.1 ∈ Set.Ioo (0:ℝ) 1)
      (by measurability)]
    filter_upwards [ae_mem_Ioo] with x hx
    exact Filter.Eventually.of_forall (fun y => by simpa using hx)
  have hz2 : ∀ᵐ z ∂(unitIoc.prod unitIoc), z.2 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun z : ℝ×ℝ => z.2 ∈ Set.Ioo (0:ℝ) 1)
      (by measurability)]
    filter_upwards [ae_mem_Ioo] with x hx
    filter_upwards [ae_mem_Ioo] with y hy
    simpa using hy
  filter_upwards [hz1, hz2] with z h1 h2
  exact ⟨h1, h2⟩

private lemma integrable_Gker : Integrable Gker (unitIoc.prod unitIoc) := by
  have hdom : Integrable (fun z : ℝ×ℝ => (1 - z.1)^(-(1/2:ℝ)) * (1 - z.2)^(-(1/2:ℝ)))
      (unitIoc.prod unitIoc) :=
    Integrable.mul_prod integrable_one_sub_rpow_Ioc integrable_one_sub_rpow_Ioc
  have hmeas : AEStronglyMeasurable Gker (unitIoc.prod unitIoc) :=
    (by unfold Gker; measurability : Measurable Gker).aestronglyMeasurable
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_prod_mem_Ioo] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hnon : 0 ≤ Gker z := by
    simp only [Gker]
    exact inv_nonneg.mpr (by have := hst_lt_one hz1 hz2; linarith)
  rw [Real.norm_of_nonneg hnon]
  simp only [Gker]
  exact inv_one_sub_mul_le_rpow hz1 hz2

private lemma integrable_Fker (n : ℕ) : Integrable (Fker n) (unitIoc.prod unitIoc) := by
  refine Integrable.mono' integrable_Gker
    ((by unfold Fker; measurability : Measurable (Fker n)).aestronglyMeasurable) ?_
  filter_upwards [ae_prod_mem_Ioo] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Real.norm_of_nonneg (Fker_nonneg hz1 hz2 n)]
  exact Fker_le_Gker hz1 hz2 n

/-! ## The main bound -/

theorem doubleIntegral_Bkernel_bound (n : ℕ) :
    |(∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1)))|
      ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
  have hFint : Integrable (Fker n) (unitIoc.prod unitIoc) := integrable_Fker n
  have hGint : Integrable Gker (unitIoc.prod unitIoc) := integrable_Gker
  have hFG : Fker n ≤ᵐ[unitIoc.prod unitIoc] Gker := by
    filter_upwards [ae_prod_mem_Ioo] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    exact Fker_le_Gker hz1 hz2 n
  have hFnn : 0 ≤ᵐ[unitIoc.prod unitIoc] Fker n := by
    filter_upwards [ae_prod_mem_Ioo] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    exact Fker_nonneg hz1 hz2 n
  have hFeq : (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Fker n (s, t))
      = ∫ z, Fker n z ∂(unitIoc.prod unitIoc) := by
    simpa only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
      using (integral_prod (Fker n) hFint).symm
  have hGval : (∫ z, Gker z ∂(unitIoc.prod unitIoc))
      = ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
    rw [integral_prod Gker hGint]
    simpa only [Gker, intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
      using doubleIntegral_inv_one_sub_mul
  have hFnonneg : 0 ≤ ∫ z, Fker n z ∂(unitIoc.prod unitIoc) := integral_nonneg_of_ae hFnn
  have hfinal : |(∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Fker n (s, t))|
      ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 :=
    calc |(∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Fker n (s, t))|
        = |∫ z, Fker n z ∂(unitIoc.prod unitIoc)| := by rw [hFeq]
      _ = ∫ z, Fker n z ∂(unitIoc.prod unitIoc) := abs_of_nonneg hFnonneg
      _ ≤ ∫ z, Gker z ∂(unitIoc.prod unitIoc) := integral_mono_ae hFint hGint hFG
      _ = ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := hGval
  simpa only [Fker] using hfinal

end

end Commons.Analysis.Integral
