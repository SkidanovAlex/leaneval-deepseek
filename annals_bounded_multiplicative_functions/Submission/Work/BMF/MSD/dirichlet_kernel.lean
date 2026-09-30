import Mathlib
import Submission.Work.BMF.MSD.basic
import Submission.Work.BMF.Defs
import Submission.Work.BMF.MSD.circDist_sin_pi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF
open Work.BMF.MSD

/-- `e(θ) = eC θ` has modulus one. -/
theorem norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  have harg : (2 : ℂ) * ↑Real.pi * Complex.I * ↑t = Complex.I * (↑(2 * Real.pi * t) : ℂ) := by
    push_cast
    ring
  rw [eC, harg]
  exact Complex.norm_exp_I_mul_ofReal _

/-- Multiplicativity of the additive character: `e(nθ) = e(θ)^n`. -/
theorem eC_nat_mul (n : ℕ) (θ : ℝ) : eC ((n : ℝ) * θ) = eC θ ^ n := by
  rw [eC, eC, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖e(θ) - 1‖ = 2|sin (πθ)|`: `eC θ = exp (I · 2πθ)` and
`Complex.norm_exp_I_mul_ofReal_sub_one`. -/
theorem eC_norm_sub_one (θ : ℝ) : ‖eC θ - 1‖ = 2 * |Real.sin (θ * Real.pi)| := by
  have h : eC θ = Complex.exp (Complex.I * (↑(2 * Real.pi * θ) : ℂ)) := by
    rw [eC]
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * θ) / 2 = θ * Real.pi by ring]
  simp

/-- Geometric-sum bounds for consecutive powers of a unit complex number: the sum over an
interval of `N` consecutive exponents is bounded by `N`, and multiplied by `‖z - 1‖` by `2`
(because `z^{a+N} - z^a = (∑ z^n)(z-1)` has modulus at most `2`). -/
theorem geom_sum_ico (z : ℂ) (a N : ℕ) (hz : ‖z‖ = 1) :
    ‖∑ n ∈ Finset.Ico a (a + N), z ^ n‖ ≤ (N : ℝ) ∧
      ‖∑ n ∈ Finset.Ico a (a + N), z ^ n‖ * ‖z - 1‖ ≤ 2 := by
  have h1 : ‖∑ n ∈ Finset.Ico a (a + N), z ^ n‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Ico a (a + N), z ^ n‖
        ≤ ∑ n ∈ Finset.Ico a (a + N), ‖z ^ n‖ := norm_sum_le _ _
      _ = (N : ℝ) := by simp [norm_pow, hz]
  refine ⟨h1, ?_⟩
  have h2 : (∑ n ∈ Finset.Ico a (a + N), z ^ n) * (z - 1) = z ^ (a + N) - z ^ a :=
    geom_sum_Ico_mul z (m := a) (n := a + N) (Nat.le_add_right a N)
  rw [← norm_mul, h2]
  calc ‖z ^ (a + N) - z ^ a‖ ≤ ‖z ^ (a + N)‖ + ‖z ^ a‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_pow, hz]; norm_num

/-- `4 · circDist θ ≤ ‖e(θ) - 1‖`: combining `‖e(θ) - 1‖ = 2|sin (πθ)|` with
Jordan's inequality `2 · circDist θ ≤ |sin (πθ)|`. -/
theorem four_mul_circDist_le_norm_eC_sub_one (θ : ℝ) : 4 * circDist θ ≤ ‖eC θ - 1‖ := by
  rw [eC_norm_sub_one θ]
  have := circDist_sin_pi θ
  linarith

/-- Dirichlet-kernel bound: for an interval of `N` consecutive integers and any real `θ`, the
exponential sum is bounded by `kern N θ` (`= N` for integral `θ`, and `min N (1/(2*circDist θ))`
otherwise), where `circDist θ = dist(θ, ℤ)`. -/
theorem dirichlet_kernel (a N : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Finset.Ico a (a + N), eC ((n : ℝ) * θ)‖ ≤ kern N θ := by
  have hsum : (∑ n ∈ Finset.Ico a (a + N), eC ((n : ℝ) * θ))
      = ∑ n ∈ Finset.Ico a (a + N), (eC θ) ^ n :=
    Finset.sum_congr rfl (fun n _ => eC_nat_mul n θ)
  rw [hsum]
  have hN : ‖∑ n ∈ Finset.Ico a (a + N), (eC θ) ^ n‖ ≤ (N : ℝ) :=
    (geom_sum_ico (eC θ) a N (norm_eC θ)).1
  rcases eq_or_ne (circDist θ) 0 with hδ | hδ
  · simpa [kern, hδ] using hN
  · rw [kern_eq_min hδ]
    refine le_min hN ?_
    have hδpos : 0 < circDist θ := lt_of_le_of_ne (circDist_nonneg θ) (Ne.symm hδ)
    have h4 : 4 * circDist θ ≤ ‖eC θ - 1‖ := four_mul_circDist_le_norm_eC_sub_one θ
    have hkey : ‖∑ n ∈ Finset.Ico a (a + N), (eC θ) ^ n‖ * (4 * circDist θ) ≤ 2 :=
      (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)).trans
        (geom_sum_ico (eC θ) a N (norm_eC θ)).2
    have hpos : 0 < 4 * circDist θ := by linarith
    have h1 : ‖∑ n ∈ Finset.Ico a (a + N), (eC θ) ^ n‖ ≤ 2 / (4 * circDist θ) :=
      (le_div_iff₀ hpos).mpr hkey
    have h2 : 2 / (4 * circDist θ) = 1 / (2 * circDist θ) := by
      rw [show (4 : ℝ) * circDist θ = 2 * (2 * circDist θ) by ring, div_mul_eq_div_div]
      norm_num
    calc ‖∑ n ∈ Finset.Ico a (a + N), (eC θ) ^ n‖ ≤ 2 / (4 * circDist θ) := h1
      _ = 1 / (2 * circDist θ) := h2

end Work.BMF.MSD
