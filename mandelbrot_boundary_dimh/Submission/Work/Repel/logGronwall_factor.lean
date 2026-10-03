import Mathlib

namespace Work.Repel

open Set

/-- The Grönwall integrating factor `A t = 2 log (1 + t r) - 6 log (1 - t r)` for `0 ≤ r ≤ 1/2`:
it is continuous on `[0,1]`, has the explicit derivative `2 r ((4 + 2 t r)/(1 - (t r)^2))` on the
open interval, and `exp (-(A 1)) = ((1-r)^3/(1+r))^2`. -/
theorem logGronwall_factor (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    ContinuousOn (fun t : ℝ => 2 * Real.log (1 + t * r) - 6 * Real.log (1 - t * r)) (Set.Icc 0 1) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => 2 * Real.log (1 + t * r) - 6 * Real.log (1 - t * r))
          (2 * r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2))) t) ∧
    Real.exp (-((fun t : ℝ => 2 * Real.log (1 + t * r) - 6 * Real.log (1 - t * r)) 1))
      = ((1 - r) ^ 3 / (1 + r)) ^ 2 := by
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, t * r ≤ 1/2 := by
    intro t ht
    have h := mul_le_mul_of_nonneg_right ht.2 hr
    nlinarith
  have hne1 : ∀ t ∈ Set.Icc (0:ℝ) 1, 1 + t * r ≠ 0 := by
    intro t ht
    have : 0 ≤ t * r := mul_nonneg ht.1 hr
    positivity
  have hne2 : ∀ t ∈ Set.Icc (0:ℝ) 1, 1 - t * r ≠ 0 := by
    intro t ht
    have h := hbound t ht
    intro hc
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun t : ℝ => 1 + t * r) (Set.Icc 0 1) := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => 1 - t * r) (Set.Icc 0 1) := by fun_prop
    exact ((h1.log hne1).const_mul 2).sub ((h2.log hne2).const_mul 6)
  · intro t ht
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self ht
    have hne1t : 1 + t * r ≠ 0 := hne1 t htIcc
    have hne2t : 1 - t * r ≠ 0 := hne2 t htIcc
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (1 + y * r)) (r / (1 + t * r)) t := by
      have h : HasDerivAt (fun y : ℝ => 1 + y * r) (1 * r) t :=
        ((hasDerivAt_id t).mul_const r).const_add 1
      have hh := h.log hne1t
      simpa using hh
    have hd2 : HasDerivAt (fun y : ℝ => Real.log (1 - y * r)) (-r / (1 - t * r)) t := by
      have h : HasDerivAt (fun y : ℝ => 1 - y * r) (-(1 * r)) t :=
        ((hasDerivAt_id t).mul_const r).const_sub 1
      have hh := h.log hne2t
      simpa using hh
    have hcomb := (hd1.const_mul 2).sub (hd2.const_mul 6)
    have hA : 1 + r * t ≠ 0 := by rw [mul_comm r t]; exact hne1t
    have hB : 1 - r * t ≠ 0 := by rw [mul_comm r t]; exact hne2t
    have hC : 1 - r ^ 2 * t ^ 2 ≠ 0 := by
      have h4 : (1 - r * t) * (1 + r * t) = 1 - r ^ 2 * t ^ 2 := by ring
      rw [← h4]; exact mul_ne_zero hB hA
    have hderiv_eq : 2 * (r / (1 + t * r)) - 6 * (-r / (1 - t * r))
        = 2 * r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)) := by
      field_simp
      ring
    rwa [hderiv_eq] at hcomb
  · have ha : 0 < 1 + r := by linarith
    have hb : 0 < 1 - r := by linarith
    have hB : 0 < ((1 - r) ^ 3 / (1 + r)) ^ 2 := by positivity
    rw [← Real.exp_log hB]
    rw [Real.exp_eq_exp]
    rw [Real.log_pow]
    have hn : (1 - r) ^ 3 ≠ 0 := by positivity
    rw [Real.log_div hn (ne_of_gt ha)]
    rw [Real.log_pow]
    ring_nf

end Work.Repel
