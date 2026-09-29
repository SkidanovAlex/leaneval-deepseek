import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Integral.integrableOn_l2_rpow_eighth_bound_zero_one

/-!
# Binomial expansion of the `B`-kernel double integral

The `B`-kernel `((1-st) - (1-s²)(1-t²))^n / (1-st)^{n+1}` is expanded by the
binomial theorem as
`∑ₖ C(n,k)(-1)^k (1-s²)^k(1-t²)^k/(1-st)^{k+1}`, and the finite sum is pulled
out of the iterated integral over the unit square.  The interchange is
justified by working on the product measure `μ.prod μ`, `μ = volume.restrict (Ioc 0 1)`:
every summand is dominated on `(0,1)×(0,1)` by the integrable product function
`(1-s)^{-1/2}(1-t)^{-1/2}`.
-/

namespace Commons.Analysis.Integral

open MeasureTheory Set Finset
open scoped Interval BigOperators

noncomputable section

private abbrev unitIoc : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

private lemma binom_sub (x y : ℝ) (n : ℕ) :
    (x - y)^n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1)^k * x^(n-k) * y^k := by
  have h := add_pow x (-y) n
  rw [sub_eq_add_neg, h]
  rw [← Finset.sum_range_reflect (fun m => x^m * (-y)^(n-m) * (Nat.choose n m : ℝ)) (n+1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have e1 : (n+1) - 1 - k = n - k := by omega
  rw [e1]
  have e2 : n - (n - k) = k := by omega
  rw [e2]
  rw [Nat.choose_symm hkn]
  rw [neg_pow]
  ring

private lemma binom_div (x y : ℝ) (n : ℕ) :
    (x - y)^n / x^(n+1) = ∑ k ∈ Finset.range (n+1), (Nat.choose n k : ℝ) * (-1)^k * (y^k / x^(k+1)) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · rw [div_eq_iff_mul_eq (pow_ne_zero _ hx)]
    rw [Finset.sum_mul]
    rw [binom_sub x y n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    have hdiv : (x:ℝ)^(n+1) / x^(k+1) = x^(n-k) := by
      rw [div_eq_iff (pow_ne_zero _ hx)]
      rw [← pow_add]
      congr 1
      omega
    have hterm2 : (y^k / (x:ℝ)^(k+1)) * x^(n+1) = y^k * x^(n-k) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
    rw [mul_assoc, hterm2]
    ring

private lemma hs2_pos {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) : 0 < 1 - s^2 := by
  nlinarith [hs.1, hs.2, sq_nonneg s]

private lemma hst_lt_one {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Ioo (0:ℝ) 1) : s*t < 1 := by
  nlinarith [hs.1, hs.2, ht.1, ht.2, mul_pos hs.1 ht.1]

private lemma inv_one_sub_mul_le_rpow {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
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
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hPpos), Real.mul_rpow (le_of_lt h1s) (le_of_lt h1t)]

private lemma bound_ge_one {s t : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Ioo (0:ℝ) 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖(1 - s^2)^k * (1 - t^2)^k / (1 - s*t)^(k+1)‖ ≤ 1 := by
  have h1st : 0 < 1 - s*t := by nlinarith [hst_lt_one hs ht]
  have hA : (1 - s^2)*(1 - t^2) ≤ (1 - s*t)^2 := by nlinarith [sq_nonneg (s - t)]
  have hA0 : 0 ≤ (1 - s^2)*(1 - t^2) := by nlinarith [hs2_pos hs, hs2_pos ht]
  have hnum : 0 ≤ (1 - s^2)^k * (1 - t^2)^k :=
    mul_nonneg (pow_nonneg (le_of_lt (hs2_pos hs)) k) (pow_nonneg (le_of_lt (hs2_pos ht)) k)
  rw [Real.norm_of_nonneg (div_nonneg hnum (pow_nonneg (le_of_lt h1st) (k+1)))]
  rw [div_le_one (pow_pos h1st (k+1))]
  calc (1 - s^2)^k * (1 - t^2)^k = ((1 - s^2)*(1 - t^2))^k := by rw [mul_pow]
    _ ≤ ((1 - s*t)^2)^k := pow_le_pow_left₀ hA0 hA k
    _ = (1 - s*t)^(2*k) := by rw [← pow_mul]
    _ ≤ (1 - s*t)^(k+1) := by
        apply pow_le_pow_of_le_one (by linarith : (0:ℝ) ≤ 1 - s*t) (by nlinarith [hs.1, ht.1])
        omega

private lemma integrable_one_sub_rpow_Ioc :
    Integrable (fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) unitIoc := by
  have hIoo : IntegrableOn (fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) (Set.Ioo (0:ℝ) 1) :=
    Commons.Analysis.Integral.integrableOn_Ioo_one_sub_rpow _ (by norm_num)
  have hf1 : ‖(fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) 1‖ₑ ≠ ⊤ := by simp
  exact (integrableOn_Ioc_iff_integrableOn_Ioo
    (f := fun x : ℝ => (1 - x) ^ (-(1/2:ℝ))) (a := 0) (b := 1) hf1).mpr hIoo

private theorem integrable_kernel (k : ℕ) :
    Integrable (fun z : ℝ×ℝ => (1 - z.1^2)^k * (1 - z.2^2)^k / (1 - z.1*z.2)^(k+1))
      (unitIoc.prod unitIoc) := by
  have hae : ∀ᵐ x ∂unitIoc, x ∈ Set.Ioo (0:ℝ) 1 := by
    have h1 : ∀ᵐ x ∂unitIoc, x ∈ Set.Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    have h2 : ∀ᵐ x ∂unitIoc, x ≠ 1 := Measure.ae_ne unitIoc 1
    filter_upwards [h1, h2] with x hx hne
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  have hz1 : ∀ᵐ z ∂(unitIoc.prod unitIoc), z.1 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun z : ℝ×ℝ => z.1 ∈ Set.Ioo (0:ℝ) 1) (by measurability)]
    filter_upwards [hae] with x hx
    exact Filter.Eventually.of_forall (fun y => by simpa using hx)
  have hz2 : ∀ᵐ z ∂(unitIoc.prod unitIoc), z.2 ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun z : ℝ×ℝ => z.2 ∈ Set.Ioo (0:ℝ) 1) (by measurability)]
    filter_upwards [hae] with x hx
    filter_upwards [hae] with y hy
    simpa using hy
  have hmem : ∀ᵐ z ∂(unitIoc.prod unitIoc), z.1 ∈ Set.Ioo (0:ℝ) 1 ∧ z.2 ∈ Set.Ioo (0:ℝ) 1 := by
    filter_upwards [hz1, hz2] with z h1 h2; exact ⟨h1, h2⟩
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ×ℝ => (1 - z.1^2)^k * (1 - z.2^2)^k / (1 - z.1*z.2)^(k+1)) (unitIoc.prod unitIoc) :=
    (by measurability : Measurable _).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hdom : Integrable (fun z : ℝ×ℝ => (1 - z.1)^(-(1/2:ℝ)) * (1 - z.2)^(-(1/2:ℝ)))
        (unitIoc.prod unitIoc) :=
      Integrable.mul_prod integrable_one_sub_rpow_Ioc integrable_one_sub_rpow_Ioc
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [hmem] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1st : 0 < 1 - z.1*z.2 := by nlinarith [hst_lt_one hz1 hz2]
    simp only [pow_zero, mul_one, Nat.zero_add, pow_one]
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (le_of_lt h1st))]
    conv_lhs => rw [one_div]
    exact inv_one_sub_mul_le_rpow hz1 hz2
  · have hdom : Integrable (fun _ : ℝ×ℝ => (1:ℝ)) (unitIoc.prod unitIoc) := integrable_const 1
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [hmem] with z hz
    obtain ⟨hz1, hz2⟩ := hz
    exact bound_ge_one hz1 hz2 (by omega)

theorem doubleIntegral_Bkernel_binom (n : ℕ) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1)))
      = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
          (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
            (1 - s ^ 2) ^ k * (1 - t ^ 2) ^ k / (1 - s * t) ^ (k + 1)) := by
  have hpt : ∀ s t : ℝ,
      (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1))
      = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
          ((1 - s ^ 2) ^ k * (1 - t ^ 2) ^ k / (1 - s * t) ^ (k + 1)) := by
    intro s t
    rw [binom_div (1 - s * t) ((1 - s ^ 2) * (1 - t ^ 2)) n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_pow]
  have hInt : ∀ k : ℕ, Integrable (fun z : ℝ × ℝ =>
      (1 - z.1 ^ 2) ^ k * (1 - z.2 ^ 2) ^ k / (1 - z.1 * z.2) ^ (k + 1)) (unitIoc.prod unitIoc) :=
    fun k => integrable_kernel k
  have hIntSum : Integrable (fun z : ℝ × ℝ => ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (-1) ^ k *
        ((1 - z.1 ^ 2) ^ k * (1 - z.2 ^ 2) ^ k / (1 - z.1 * z.2) ^ (k + 1)))
      (unitIoc.prod unitIoc) :=
    integrable_finsetSum _ (fun k hk => (hInt k).const_mul _)
  simp only [intervalIntegral.integral_of_le zero_le_one]
  calc (∫ s in Set.Ioc (0:ℝ) 1, ∫ t in Set.Ioc (0:ℝ) 1,
        (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1)))
      = ∫ s in Set.Ioc (0:ℝ) 1, ∫ t in Set.Ioc (0:ℝ) 1, ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * (-1) ^ k *
            ((1 - s ^ 2) ^ k * (1 - t ^ 2) ^ k / (1 - s * t) ^ (k + 1)) := by
          apply integral_congr_ae; filter_upwards with s
          apply integral_congr_ae; filter_upwards with t
          exact hpt s t
    _ = ∫ z, (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
            ((1 - z.1 ^ 2) ^ k * (1 - z.2 ^ 2) ^ k / (1 - z.1 * z.2) ^ (k + 1)))
          ∂(unitIoc.prod unitIoc) := by
          exact (integral_prod _ hIntSum).symm
    _ = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
          (∫ z, (1 - z.1 ^ 2) ^ k * (1 - z.2 ^ 2) ^ k / (1 - z.1 * z.2) ^ (k + 1)
            ∂(unitIoc.prod unitIoc)) := by
          rw [integral_finsetSum _ (fun k hk => (hInt k).const_mul _)]
          apply Finset.sum_congr rfl; intro k hk
          rw [integral_const_mul]
    _ = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * (-1) ^ k *
          (∫ s in Set.Ioc (0:ℝ) 1, ∫ t in Set.Ioc (0:ℝ) 1,
            (1 - s ^ 2) ^ k * (1 - t ^ 2) ^ k / (1 - s * t) ^ (k + 1)) := by
          apply Finset.sum_congr rfl; intro k hk
          congr 1
          exact integral_prod _ (hInt k)

end

end Commons.Analysis.Integral