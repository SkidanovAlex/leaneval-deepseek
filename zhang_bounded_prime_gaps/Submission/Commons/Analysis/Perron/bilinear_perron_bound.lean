import Mathlib
import Submission.Commons.Analysis.Complex.exists_perron_formula_bound
import Submission.Commons.Analysis.Normed.tailProduct_norm_sub_one_le

noncomputable section

open Complex MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

namespace Commons.Analysis.Perron

open Commons.Analysis.Complex

/-- Factor `x^s · m^{-s} · n^{-s}` as `exp (s · log (x/(mn)))` for positive reals. -/
lemma cpow_three_factor (x m n : ℝ) (hx : 0 < x) (hm : 0 < m) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ s * (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s)
      = Complex.exp (s * Complex.log (((x / (m * n)) : ℝ) : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hm0,
    Complex.cpow_def_of_ne_zero hn0]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hm.le, ← Complex.ofReal_log hn.le,
    ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ x / (m * n))]
  rw [Real.log_div hx.ne' (by positivity : (m*n) ≠ 0), Real.log_mul hm.ne' hn.ne']
  push_cast
  ring

/-- Cancellation of the `2π` normalization factor. -/
lemma two_pi_mul_inv_two_pi (X : ℂ) : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * X) = X := by
  field_simp

/-- The truncated Perron kernel integral is `2π` times `stepKern`. -/
lemma perron_kernel_integral (c T z : ℝ) :
    (∫ t in (-T)..T, Complex.exp ((((c : ℂ) + (t : ℂ) * Complex.I))
        * (Complex.log (z : ℂ))) / (((c : ℂ) + (t : ℂ) * Complex.I)))
      = (2 * Real.pi) * stepKern c T z := by
  rw [stepKern, two_pi_mul_inv_two_pi]

/-- Expansion of the bilinear Perron integral as a double sum of per-pair kernels. -/
lemma perron_bilinear_expansion (a b : ℕ → ℂ) (c x T : ℝ) (M N : ℕ)
    (hc : 0 < c) (hx : 0 < x) :
    (∫ t in (-T)..T,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
        * (∑ m ∈ Finset.Icc 1 M, a m * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
        * (∑ n ∈ Finset.Icc 1 N, b n * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))
    = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        a m * b n * ((2 * Real.pi) * stepKern c T (x / ((m : ℝ) * (n : ℝ)))) := by
  let Φ : ℕ → ℕ → ℝ → ℂ := fun m n t => a m * b n *
      (Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log ((x / ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ))
        / ((c : ℂ) + (t : ℂ) * Complex.I))
  have hpoint : ∀ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
        * (∑ m ∈ Finset.Icc 1 M, a m * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
        * (∑ n ∈ Finset.Icc 1 N, b n * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, Φ m n t := by
    intro t
    dsimp only [Φ]
    set s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hs
    rw [Finset.mul_sum (Finset.Icc 1 M) (fun m => a m * ((m : ℂ)) ^ (-s)) ((x : ℂ) ^ s / s)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
    have hmc : ((m : ℂ)) = (((m : ℝ) : ℂ)) := by push_cast; ring
    have hnc : ((n : ℂ)) = (((n : ℝ) : ℂ)) := by push_cast; ring
    rw [hmc, hnc]
    rw [show ((x : ℂ) ^ s / s * (a m * (((m : ℝ) : ℂ)) ^ (-s))) * (b n * (((n : ℝ) : ℂ)) ^ (-s))
        = a m * b n * ((x : ℂ) ^ s * (((m : ℝ) : ℂ)) ^ (-s) * (((n : ℝ) : ℂ)) ^ (-s) / s) by ring]
    rw [cpow_three_factor x (m : ℝ) (n : ℝ) hx hmpos hnpos s]
  have hΦcont : ∀ m n, Continuous (Φ m n) := by
    intro m n
    dsimp only [Φ]
    refine Continuous.mul continuous_const ?_
    apply Continuous.div
    · exact Complex.continuous_exp.comp (by fun_prop)
    · fun_prop
    · intro t; exact sline_ne_zero c hc t
  have hker : ∀ z : ℝ,
      (∫ t in (-T)..T, Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log (z : ℂ))
          / ((c : ℂ) + (t : ℂ) * Complex.I)) = (2 * Real.pi) * stepKern c T z :=
    fun z => perron_kernel_integral c T z
  have hΦint : ∀ m n, (∫ t in (-T)..T, Φ m n t)
      = a m * b n * ((2 * Real.pi) * stepKern c T (x / ((m : ℝ) * (n : ℝ)))) := by
    intro m n
    have hunf : Φ m n = fun t : ℝ => (a m * b n) *
        (Complex.exp (((c : ℂ) + (t : ℂ) * Complex.I) * Complex.log ((x / ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ))
          / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
      funext t; rfl
    rw [hunf, intervalIntegral.integral_const_mul, hker]
  have hcongr : (∫ t in (-T)..T,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
          * (∑ m ∈ Finset.Icc 1 M, a m * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
          * (∑ n ∈ Finset.Icc 1 N, b n * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))
      = ∫ t in (-T)..T, ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, Φ m n t :=
    intervalIntegral.integral_congr (fun t _ => hpoint t)
  rw [hcongr]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun n hn => hΦint m n)
    · intro n hn; exact (hΦcont m n).intervalIntegrable _ _
  · intro m hm
    exact (continuous_finsetSum _ (fun n hn => hΦcont m n)).intervalIntegrable _ _

theorem bilinear_perron_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℕ → ℂ) (c x T : ℝ) (M N : ℕ),
      0 < c → 1 < x → 0 < T → (∀ n : ℕ, (n : ℝ) ≠ x) →
      ‖(∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * a m * b n)
        - (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
            * (∑ m ∈ Finset.Icc 1 M, a m * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
            * (∑ n ∈ Finset.Icc 1 N, b n * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))‖
      ≤ C * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ c) *
              min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
  refine ⟨32 / (2 * Real.pi), by positivity, ?_⟩
  intro a b c x T M N hc hx1 hT hxnnat
  have hx : 0 < x := by linarith
  have hI : (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
            * (∑ m ∈ Finset.Icc 1 M, a m * ((m : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I)))
            * (∑ n ∈ Finset.Icc 1 N, b n * ((n : ℂ)) ^ (-((c : ℂ) + (t : ℂ) * Complex.I))))
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          a m * b n * stepKern c T (x / ((m : ℝ) * (n : ℝ))) := by
    rw [perron_bilinear_expansion a b c x T M N hc hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast Real.pi_ne_zero
    field_simp
  have hdiff : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) * a m * b n)
        - (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            a m * b n * stepKern c T (x / ((m : ℝ) * (n : ℝ))))
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          a m * b n * ((if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
            - stepKern c T (x / ((m : ℝ) * (n : ℝ)))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hI, hdiff]
  calc
    ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        a m * b n * ((if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
          - stepKern c T (x / ((m : ℝ) * (n : ℝ))))‖
        ≤ ∑ m ∈ Finset.Icc 1 M, ‖∑ n ∈ Finset.Icc 1 N,
            a m * b n * ((if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
              - stepKern c T (x / ((m : ℝ) * (n : ℝ))))‖ := by
          exact norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m * b n * ((if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
              - stepKern c T (x / ((m : ℝ) * (n : ℝ))))‖ := by
          exact Finset.sum_le_sum (fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * ((32 / (2 * Real.pi)) * (x / ((m : ℝ) * (n : ℝ))) ^ c
              * min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))) := by
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro n hn
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
          have hmnpos : 0 < (m : ℝ) * (n : ℝ) := mul_pos hmpos hnpos
          have hzpos : 0 < x / ((m : ℝ) * (n : ℝ)) := div_pos hx hmnpos
          have hz1 : x / ((m : ℝ) * (n : ℝ)) ≠ 1 := by
            intro h
            have hmncast : ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) := by push_cast; ring
            have hxb : x = (m : ℝ) * (n : ℝ) := (div_eq_one_iff_eq hmnpos.ne').mp h
            have hxval : ((m * n : ℕ) : ℝ) = x := by rw [hmncast]; exact hxb.symm
            exact hxnnat (m * n) hxval
          have hif : (1 < x / ((m : ℝ) * (n : ℝ))) ↔ ((m : ℝ) * (n : ℝ) < x) := by
            rw [lt_div_iff₀ hmnpos]; simp
          have hif' : (if 1 < x / ((m : ℝ) * (n : ℝ)) then (1 : ℂ) else 0)
              = (if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0) := by
            by_cases hlt : (m : ℝ) * (n : ℝ) < x
            · rw [if_pos (hif.mpr hlt), if_pos hlt]
            · rw [if_neg (fun hh => hlt (hif.mp hh)), if_neg hlt]
          have hstep : ‖(if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
                - stepKern c T (x / ((m : ℝ) * (n : ℝ)))‖
              ≤ (32 / (2 * Real.pi)) * (x / ((m : ℝ) * (n : ℝ))) ^ c
                * min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
            rw [norm_sub_rev, ← hif']
            exact perronStep_deviation_pos c T (x / ((m : ℝ) * (n : ℝ))) hc hT hzpos hz1
          calc
            ‖a m * b n * ((if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
                - stepKern c T (x / ((m : ℝ) * (n : ℝ))))‖
                = ‖a m‖ * ‖b n‖ * ‖(if (m : ℝ) * (n : ℝ) < x then (1 : ℂ) else 0)
                    - stepKern c T (x / ((m : ℝ) * (n : ℝ)))‖ := by rw [norm_mul, norm_mul]
              _ ≤ ‖a m‖ * ‖b n‖ * ((32 / (2 * Real.pi)) * (x / ((m : ℝ) * (n : ℝ))) ^ c
                    * min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))) :=
                    mul_le_mul_of_nonneg_left hstep (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (32 / (2 * Real.pi)) * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ c)
              * min 1 (1 / (T * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring

end Commons.Analysis.Perron
