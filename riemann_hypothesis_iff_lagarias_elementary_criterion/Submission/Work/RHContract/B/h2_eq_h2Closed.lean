import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `h₂ = h₂Closed`: the closed form of the Landau integral (ROUTE_LEAD §3.3)

For `0 < Re s`,

`h₂(s) = ∫_2^∞ (ψ t − t) t^{−s−2} dt
       = [−ζ′(s+1)/ζ(s+1) − (s+1)/s]/(s+1) + (1 − 2^{−s})/s`.

Three ingredients:

* the corpus Mellin identity `Commons.NumberTheory.Zeta.logDeriv_zeta_eq_mellin_psi_sub_id`
  at `w = s+1`, which identifies `−ζ′(s+1)/ζ(s+1) − (s+1)/s` with `(s+1)` times the Mellin
  transform of `ψ − id`, i.e. with an integral over `(1, ∞)`;
* the elementary computation `∫_1^2 (−t) t^{−s−2} dt = (2^{−s} − 1)/s`: on `(1,2)` the Chebyshev
  function `ψ` vanishes (its only jump there would be at the prime `2`), so only the `−t` part
  contributes;
* additivity of the integral, splitting `(1, ∞) = (1, 2] ∪ (2, ∞)`.
-/

open MeasureTheory

namespace Work.RHContract.B

noncomputable section

/-- `(ψ t − t) t^{−s−2}` is integrable on `(1, ∞)` for `Re s > 0`: it is dominated by
`(log 4 + 5) · t^{−Re s − 1}`, using `ψ t ≤ (log 4 + 4) · t`. -/
private lemma integrable_psi_sub_id_cpow (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2))
      (Set.Ioi 1) := by
  have hC : IntegrableOn (fun t : ℝ => ((Real.log 4 + 4) + 1) * t ^ (-s.re - 1))
      (Set.Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) (c := 1) (by linarith) (by norm_num)).const_mul _
  refine hC.mono' ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp Chebyshev.psi_mono.measurable).sub
        (by fun_prop : Measurable fun t : ℝ => (t : ℂ))).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      exact (Complex.continuousAt_ofReal_cpow_const t (-s - 2)
        (Or.inr (ne_of_gt (lt_trans zero_lt_one ht)))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : 0 < t := by linarith
    have hnorm1 : ‖(Chebyshev.psi t : ℂ) - (t : ℂ)‖ = |Chebyshev.psi t - t| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hnorm2 : ‖(t : ℂ) ^ (-s - 2)‖ = t ^ (-s.re - 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
    rw [Complex.norm_mul, hnorm1, hnorm2]
    have hbound2 : |Chebyshev.psi t - t| ≤ Chebyshev.psi t + t := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith [Chebyshev.psi_nonneg t]⟩
    have hpsi : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht0.le
    have htmul : t ^ (1:ℝ) * t ^ (-s.re - 2) = t ^ (-s.re - 1) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [Real.rpow_one] at htmul
    calc |Chebyshev.psi t - t| * t ^ (-s.re - 2)
        ≤ (Chebyshev.psi t + t) * t ^ (-s.re - 2) :=
          mul_le_mul_of_nonneg_right hbound2 (Real.rpow_nonneg ht0.le _)
      _ ≤ ((Real.log 4 + 4) * t + t) * t ^ (-s.re - 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht0.le _)
      _ = ((Real.log 4 + 4) + 1) * t ^ (-s.re - 1) := by
          rw [add_mul, mul_assoc, htmul]
          ring

/-- The Mellin transform of the correlation function `ψ − id` (an integral over `(1, ∞)`,
thanks to the support condition `1 ≤ t`) written in the shape of the `h₂` integrand. -/
private lemma mellin_corr_eq_Ioi (s : ℂ) :
    mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-(s + 1))
      = ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s - 2) * ((Chebyshev.psi t : ℂ) - (t : ℂ)) := by
  have hpow : (-(s+1) : ℂ) - 1 = -s - 2 := by ring
  rw [mellin, hpow]
  have hfun : (fun t : ℝ =>
        (t : ℂ) ^ (-s - 2) • (if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0))
      = (Set.Ici (1:ℝ)).indicator
          (fun t : ℝ => (t : ℂ) ^ (-s - 2) * ((Chebyshev.psi t : ℂ) - (t : ℂ))) := by
    funext t
    by_cases h : 1 ≤ t <;> simp [Set.indicator, h, smul_eq_mul]
  rw [hfun, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioi (0:ℝ) ∩ Set.Ici (1:ℝ) = Set.Ici (1:ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    constructor <;> intro h
    · exact h.2
    · exact ⟨by linarith, h⟩
  rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- The Mellin transform of `ψ − id` at `-(s+1)` equals the `h₂`-integrand on `(1, ∞)`. -/
private lemma mellin_corr_eq_integral (s : ℂ) :
    mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-(s + 1))
      = ∫ t : ℝ in Set.Ioi 1, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2) := by
  rw [mellin_corr_eq_Ioi s]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => mul_comm _ _)

/-- The integral over the missing interval `(1, 2]`: since `ψ t = 0` on `(1,2)`,

`∫_1^2 (ψ t − t) t^{−s−2} dt = ∫_1^2 (−t) t^{−s−2} dt = (2^{−s} − 1)/s`. -/
private lemma integral_Ioc_one_two (s : ℂ) (hs : 0 < s.re) :
    ∫ t : ℝ in Set.Ioc 1 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2)
      = ((2 : ℂ) ^ (-s) - 1) / s := by
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hcongr : (∫ t : ℝ in Set.Ioo 1 2,
        ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2))
      = ∫ t : ℝ in Set.Ioo 1 2, -((t : ℂ) ^ (-s - 1)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change ((Chebyshev.psi t : ℂ) - (t:ℂ)) * (t:ℂ) ^ (-s-2) = -((t:ℂ) ^ (-s-1))
    have ht0 : (0:ℝ) < t := by have := ht.1; linarith
    have htne : (t:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
    rw [Chebyshev.psi_eq_zero_of_lt_two ht.2]
    have h1 : (t:ℂ) ^ (-s - 2) = (t:ℂ) ^ (-s-1) * (t:ℂ) ^ (-1 : ℂ) := by
      rw [← Complex.cpow_add (-s-1) (-1) htne]
      congr 1
      ring
    rw [h1, Complex.cpow_neg_one, Complex.ofReal_zero, zero_sub]
    field_simp
  rw [hcongr, MeasureTheory.integral_neg]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hval : ∫ t : ℝ in Set.Ioo 1 2, (t : ℂ) ^ (-s - 1) = (1 - (2:ℂ) ^ (-s)) / s := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (show (1:ℝ) ≤ 2 by norm_num)]
    have hne : (-s - 1 : ℂ) ≠ -1 := by
      intro h
      have h' : -s = 0 := by
        have h2 : -s - 1 + 1 = -1 + 1 := by rw [h]
        simpa using h2
      exact hs0 (by simpa using h')
    have hmem : (0:ℝ) ∉ Set.uIcc 1 2 := by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
      simp [Set.mem_Icc]
    rw [integral_cpow (Or.inr ⟨hne, hmem⟩)]
    rw [show (-s-1)+1 = -s by ring, Complex.ofReal_one, Complex.one_cpow]
    rw [div_neg, ← neg_div, neg_sub]
    norm_num
  rw [hval]
  rw [← neg_div, neg_sub]

/-- **The closed form of the Landau integral `h₂`.**  For `Re s > 0`,

`∫_2^∞ (ψ t − t) t^{−s−2} dt = [−ζ′(s+1)/ζ(s+1) − (s+1)/s]/(s+1) + (1 − 2^{−s})/s`. -/
theorem h2_eq_h2Closed (s : ℂ) (hs : 0 < s.re) :
    Work.RHContract.Landau.h2 s = Work.RHContract.Landau.h2Closed s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hs1 : 1 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hsp1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at this
    linarith
  -- the corpus Mellin identity at `w = s + 1`
  have hcorpus := Commons.NumberTheory.Zeta.logDeriv_zeta_eq_mellin_psi_sub_id (w := s + 1) hs1
  have hcorpus' : -(deriv riemannZeta (s + 1)) / riemannZeta (s + 1) - (s + 1) / s
      = (s + 1) * mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0)
          (-(s + 1)) := by
    simpa using hcorpus
  have hint := integrable_psi_sub_id_cpow s hs
  -- split `(1, ∞) = (1, 2] ∪ (2, ∞)`
  have hdisj : Disjoint (Set.Ioc (1:ℝ) 2) (Set.Ioi 2) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioc] at hx1
    simp only [Set.mem_Ioi] at hx2
    linarith [hx1.2, hx2]
  have hunion : Set.Ioc (1:ℝ) 2 ∪ Set.Ioi 2 = Set.Ioi 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h2) <;> linarith
    · intro h
      by_cases hx : x ≤ 2
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  have hsplit : (∫ t : ℝ in Set.Ioi 1, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2))
      = (∫ t : ℝ in Set.Ioc 1 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2))
        + (∫ t : ℝ in Set.Ioi 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2)) := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self)
      (hint.mono_set (Set.Ioi_subset_Ioi (by norm_num : (1:ℝ) ≤ 2)))
  have hlow := integral_Ioc_one_two s hs
  rw [mellin_corr_eq_integral s, hsplit] at hcorpus'
  -- solve for the `(2, ∞)` integral
  have hX : (∫ t : ℝ in Set.Ioi 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2))
      = (-(deriv riemannZeta (s + 1)) / riemannZeta (s + 1) - (s + 1) / s) / (s + 1)
        - ((2 : ℂ) ^ (-s) - 1) / s := by
    have hB : (s + 1) * (((2 : ℂ) ^ (-s) - 1) / s
        + (∫ t : ℝ in Set.Ioi 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2)))
        = -(deriv riemannZeta (s + 1)) / riemannZeta (s + 1) - (s + 1) / s := by
      rw [hcorpus', hlow]
    rw [eq_sub_iff_add_eq, eq_div_iff hsp1]
    linear_combination hB
  have h2val : Work.RHContract.Landau.h2 s
      = ∫ t : ℝ in Set.Ioi 2, ((Chebyshev.psi t : ℂ) - (t : ℂ)) * (t : ℂ) ^ (-s - 2) := by
    simp only [Work.RHContract.Landau.h2]
  rw [h2val, hX]
  simp only [Work.RHContract.Landau.h2Closed]
  have hterm : ((2 : ℂ) ^ (-s) - 1) / s = -((1 - (2 : ℂ) ^ (-s)) / s) := by
    rw [← neg_div, neg_sub]
  rw [hterm, sub_neg_eq_add]

end

end Work.RHContract.B
