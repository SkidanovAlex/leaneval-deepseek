import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Rpow.rpow_four_thirds_eq_sq_two_thirds

open Filter

namespace Commons.Analysis.Asymptotic

/-- Pointwise rewriting of the `t^{4/3}`-weighted expression, valid for `t > 0` and `f > 0`:
expressing everything in terms of the normalized quantities `f/t^{4/3}`, `g/t^{1/3}` and
`h*t^{2/3}`. -/
lemma phi_rpow_rewrite {t f g h : ℝ} (ht : 0 < t) (hf : 0 < f) :
    (h * t ^ ((2:ℝ)/3)) / (2 * Real.sqrt (f / t ^ ((4:ℝ)/3)))
      - (g / t ^ ((1:ℝ)/3)) ^ 2 / (4 * (Real.sqrt (f / t ^ ((4:ℝ)/3))) ^ 3)
    = t ^ ((4:ℝ)/3) * (h / (2 * Real.sqrt f) - g ^ 2 / (4 * (Real.sqrt f) ^ 3)) := by
  have ht0 : (0:ℝ) ≤ t := le_of_lt ht
  have hf0 : (0:ℝ) ≤ f := le_of_lt hf
  have hs4 : t ^ ((4:ℝ)/3) = (t ^ ((2:ℝ)/3)) ^ 2 :=
    Commons.Analysis.Rpow.rpow_four_thirds_eq_sq_two_thirds ht
  have hs_sqrt : Real.sqrt (t ^ ((4:ℝ)/3)) = t ^ ((2:ℝ)/3) := by
    rw [hs4, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)]
  have hR : Real.sqrt (f / t ^ ((4:ℝ)/3)) = Real.sqrt f / t ^ ((2:ℝ)/3) := by
    rw [Real.sqrt_div hf0, hs_sqrt]
  have hu2 : (t ^ ((1:ℝ)/3)) ^ 2 = t ^ ((2:ℝ)/3) := by
    have h23 : (2:ℝ)/3 = (1:ℝ)/3 + (1:ℝ)/3 := by norm_num
    rw [h23, Real.rpow_add ht]; ring
  have hsne : t ^ ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hrne : Real.sqrt f ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hf)
  rw [hR, hs4, div_pow, div_pow, hu2]
  field_simp

theorem rpow_phi_second_deriv {f g h : ℝ → ℝ} {κ a b : ℝ} (hκ : 0 < κ)
    (hfpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < f t)
    (hIn : Filter.Tendsto (fun t : ℝ => f t / t ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds κ))
    (hDer : Filter.Tendsto (fun t : ℝ => g t / t ^ ((1:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds a))
    (hSec : Filter.Tendsto (fun t : ℝ => h t * t ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds b)) :
    Filter.Tendsto
      (fun t : ℝ => t ^ ((4:ℝ)/3) * (h t / (2 * Real.sqrt (f t))
        - g t ^ 2 / (4 * (Real.sqrt (f t)) ^ 3)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (b / (2 * Real.sqrt κ) - a ^ 2 / (4 * (Real.sqrt κ) ^ 3))) := by
  have htpos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have hR : Filter.Tendsto (fun t : ℝ => Real.sqrt (f t / t ^ ((4:ℝ)/3)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt κ)) := hIn.sqrt
  have hκne : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hκ)
  have h1 : Filter.Tendsto
      (fun t : ℝ => (h t * t ^ ((2:ℝ)/3)) / (2 * Real.sqrt (f t / t ^ ((4:ℝ)/3))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (b / (2 * Real.sqrt κ))) := by
    have hden : Filter.Tendsto (fun t : ℝ => 2 * Real.sqrt (f t / t ^ ((4:ℝ)/3)))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (2 * Real.sqrt κ)) :=
      tendsto_const_nhds.mul hR
    exact hSec.div hden (mul_ne_zero two_ne_zero hκne)
  have h2 : Filter.Tendsto
      (fun t : ℝ => (g t / t ^ ((1:ℝ)/3)) ^ 2 /
        (4 * (Real.sqrt (f t / t ^ ((4:ℝ)/3))) ^ 3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (a ^ 2 / (4 * (Real.sqrt κ) ^ 3))) := by
    have hnum : Filter.Tendsto (fun t : ℝ => (g t / t ^ ((1:ℝ)/3)) ^ 2)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (a ^ 2)) := hDer.pow 2
    have hden : Filter.Tendsto (fun t : ℝ => 4 * (Real.sqrt (f t / t ^ ((4:ℝ)/3))) ^ 3)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (4 * (Real.sqrt κ) ^ 3)) :=
      tendsto_const_nhds.mul (hR.pow 3)
    exact hnum.div hden (mul_ne_zero (by norm_num) (pow_ne_zero 3 hκne))
  have hlim : Filter.Tendsto
      (fun t : ℝ => (h t * t ^ ((2:ℝ)/3)) / (2 * Real.sqrt (f t / t ^ ((4:ℝ)/3)))
        - (g t / t ^ ((1:ℝ)/3)) ^ 2 / (4 * (Real.sqrt (f t / t ^ ((4:ℝ)/3))) ^ 3))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (b / (2 * Real.sqrt κ) - a ^ 2 / (4 * (Real.sqrt κ) ^ 3))) := h1.sub h2
  have heq : (fun t : ℝ => (h t * t ^ ((2:ℝ)/3)) / (2 * Real.sqrt (f t / t ^ ((4:ℝ)/3)))
        - (g t / t ^ ((1:ℝ)/3)) ^ 2 / (4 * (Real.sqrt (f t / t ^ ((4:ℝ)/3))) ^ 3))
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun t : ℝ => t ^ ((4:ℝ)/3) * (h t / (2 * Real.sqrt (f t))
        - g t ^ 2 / (4 * (Real.sqrt (f t)) ^ 3))) := by
    filter_upwards [htpos, hfpos] with t ht hf
    exact phi_rpow_rewrite ht hf
  exact Filter.Tendsto.congr' heq hlim

end Commons.Analysis.Asymptotic