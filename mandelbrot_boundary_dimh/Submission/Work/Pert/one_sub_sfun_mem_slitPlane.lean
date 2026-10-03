import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

open Complex

/-- If the imaginary part of `z` lies in `(-π, π)` then `exp z` avoids the closed negative
real axis: `exp` maps the open horizontal strip of width `2π` onto `slitPlane`.  (This is the
form in which the bound `‖log (1 - s)‖ < π` is used: it forces `1 - s` off `(-∞, 0]`.) -/
lemma exp_mem_slitPlane_of_abs_im_lt {z : ℂ} (h : |z.im| < Real.pi) :
    Complex.exp z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h0 : z.im = 0
  · left
    rw [Complex.exp_re, h0, Real.cos_zero, mul_one]
    exact Real.exp_pos _
  · right
    rw [Complex.exp_im]
    have hsin : Real.sin z.im ≠ 0 := by
      intro hs
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      have hn' : z.im = (n : ℝ) * Real.pi := hn.symm
      have h1 : |(n : ℝ)| * Real.pi < Real.pi := by
        have he : |(n:ℝ)| * Real.pi = |z.im| := by
          rw [hn', abs_mul, abs_of_pos Real.pi_pos]
        rw [he]; exact h
      have hlt : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
      have hlt' : (|n| : ℤ) < 1 := by exact_mod_cast hlt
      have hn0 : n = 0 := Int.abs_lt_one_iff.mp hlt'
      simp [hn0] at hn'
      exact h0 hn'
    exact mul_ne_zero (Real.exp_ne_zero _) hsin

/-- Shishikura (A.1.7)(ii) at the normalisation of the PERT gate: if the lift `F_f` satisfies
`F_f(w) = w + 1 + O(1/32)` and `‖α‖ ≤ 1/64`, then `1 - s_f(w) = exp (2πiα (F_f(w) - w))` lies
in the slit plane.  Indeed `F_f(w) - (w+1) = log(1-s)/(2πiα) - 1` bounds `log(1-s)` by
`(33/32)·2π‖α‖ ≤ 33π/1024 < π`, and `exp` maps `{|Im| < π}` into `slitPlane`. -/
theorem one_sub_sfun_mem_slitPlane {u : ℂ → ℂ} {σ α w : ℂ}
    (hα64 : ‖α‖ ≤ 1 / 64)
    (hNT : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    1 - Work.Pert.sfun u σ α w ∈ Complex.slitPlane := by
  set z : ℂ := 1 - Work.Pert.sfun u σ α w with hzdef
  set L : ℂ := Complex.log z with hLdef
  set c : ℂ := 1 / (2 * Real.pi * I * α) with hcdef
  -- `F_f(w) - (w+1) = c · log(1-s) - 1`
  have hrel : Work.Pert.liftF u σ α w - (w + 1) = c * L - 1 := by
    simp only [Work.Pert.liftF]
    rw [← hzdef, ← hLdef, ← hcdef]
    ring
  have h32 : ‖c * L - 1‖ ≤ 1 / 32 := by
    have h := hNT
    rwa [hrel] at h
  -- `c·L` is nonzero, hence so are `c` (i.e. `α`) and `L`
  have hne : c * L ≠ 0 := by
    intro h
    have hh := h32
    rw [h] at hh
    norm_num at hh
  have hc : c ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hL : L ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have h2pia : 2 * Real.pi * I * α ≠ 0 := by
    intro h
    exact hc (by rw [hcdef, h, div_zero])
  have hmul : (2 * Real.pi * I * α) * c = 1 := by
    rw [hcdef, mul_one_div_cancel h2pia]
  have hLeq : L = (2 * Real.pi * I * α) * (c * L) := by
    rw [← mul_assoc, hmul, one_mul]
  have hnormc : ‖(2 * Real.pi * I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [show (2 * Real.pi * I * α : ℂ) = ((2:ℂ) * (Real.pi:ℂ) * I) * α by ring]
    rw [norm_mul, norm_mul, norm_mul]
    simp
  have h3 : ‖c * L‖ ≤ 33 / 32 := by
    have h : c * L = (c * L - 1) + 1 := by ring
    calc ‖c * L‖ = ‖(c * L - 1) + 1‖ := congrArg norm h
      _ ≤ ‖c * L - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖c * L - 1‖ + 1 := by simp
      _ ≤ 1 / 32 + 1 := add_le_add h32 le_rfl
      _ = 33 / 32 := by norm_num
  have hLbound : ‖L‖ ≤ (Real.pi / 32) * (33 / 32) := by
    rw [hLeq]
    calc ‖(2 * Real.pi * I * α) * (c * L)‖
          = ‖(2 * Real.pi * I * α : ℂ)‖ * ‖c * L‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * (1 / 64)) * (33 / 32) := by
            apply mul_le_mul
            · rw [hnormc]; exact mul_le_mul_of_nonneg_left hα64 (by positivity)
            · exact h3
            · positivity
            · positivity
      _ = (Real.pi / 32) * (33 / 32) := by ring
  have hLpi : ‖L‖ < Real.pi := by
    have hlt : (Real.pi / 32) * (33 / 32) < Real.pi := by nlinarith [Real.pi_pos]
    linarith
  have him : |L.im| < Real.pi := lt_of_le_of_lt (Complex.abs_im_le_norm L) hLpi
  have hexp : Complex.exp L ∈ Complex.slitPlane := exp_mem_slitPlane_of_abs_im_lt him
  have hz0 : z ≠ 0 := by
    intro hz
    exact hL (by rw [hLdef, hz, Complex.log_zero])
  have hzL : Complex.exp L = z := by
    rw [hLdef]; exact Complex.exp_log hz0
  rw [← hzL]
  exact hexp

end Work.Pert
