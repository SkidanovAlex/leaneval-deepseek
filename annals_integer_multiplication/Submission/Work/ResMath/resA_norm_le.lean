import Mathlib
import Submission.Work.ResMath.defs
import Submission.Work.ResMath.gauss_lattice_le
import Submission.Work.ResMath.resS_rowsum_reindex
import Submission.Work.ResMath.norm_mulVec_le_of_row_sum

/-!
# The operator-norm bound `‖resA‖ ≤ 3/4` (paper Lemma 4.5)

`resA s t α = S/2` where `S` is the Gaussian resampling matrix of paper §4.1,

`(S u) k = α⁻¹ Σ_{j∈ℤ} e^{-π α⁻² s² (k/t - j/s)²} u_{j mod s}`.

Lemma 4.5 of Harvey–van der Hoeven proves `‖S‖ ≤ 1 + α⁻¹` (sup norm), whence
`‖resA‖ ≤ (1 + α⁻¹)/2 ≤ 3/4` for `α ≥ 2`.  The proof bounds the row sums of `S`:
for fixed `k`, the total weight `Σ_{j<s} Σ_{q∈ℤ} e^{-π α⁻² s² (k/t - j/s - q)²}`
is a theta sum `Σ_{n∈ℤ} e^{-π α⁻² (s·k/t - n)²}` over the lattice `(1/s)ℤ`, and the
classical Gaussian lattice bound `Σ_{n∈ℤ} e^{-π (z+n)²/α²} ≤ 1 + α` (integral
comparison against `∫ e^{-π x²/α²} = α`) gives the result.
-/

namespace Work.ResMath

open scoped BigOperators

/-- Unfolding of an entry of `resSmat` into the real theta sum it is defined by. -/
lemma resSmat_apply (s t α : ℕ) (k : Fin t) (j : Fin s) :
    HvdH.resSmat s t α k j
      = (((1 / (α : ℝ)) * ∑' q : ℤ,
          Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
            ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) : ℝ) : ℂ) := by
  simp only [HvdH.resSmat]
  have h : (∑' q : ℤ, Real.exp (-Real.pi * (s:ℝ)^2 / (α:ℝ)^2 *
        ((k:ℝ)/t - (j:ℝ)/s - (q:ℝ))^2))
      = (∑' q : ℤ, Real.exp (-(Real.pi * (s:ℝ)^2 / (α:ℝ)^2) *
            ((k:ℝ)/(t:ℝ) - (j:ℝ)/(s:ℝ) - (q:ℝ))^2)) := by
    apply tsum_congr; intro q; congr 1; ring
  rw [h]

/-- The total weight of row `k` of `resSmat` (before the factor `α⁻¹`) is a theta sum. -/
lemma theta_sum_le (s t α : ℕ) (hs : 0 < s) (hα : 0 < α) (k : Fin t) :
    ∑ j : Fin s, ∑' q : ℤ,
        Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
          ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) ≤ 1 + (α : ℝ) := by
  have hαR : (0:ℝ) < α := by exact_mod_cast hα
  rw [resS_rowsum_reindex s hs (α:ℝ) hαR ((k:ℝ)/(t:ℝ))]
  calc (∑' n : ℤ, Real.exp (-(Real.pi / (α:ℝ) ^ 2) *
          ((s:ℝ) * ((k:ℝ)/(t:ℝ)) - (n : ℝ)) ^ 2))
      = ∑' n : ℤ, Real.exp (-(Real.pi / (α:ℝ) ^ 2) *
          ((-(s:ℝ) * ((k:ℝ)/(t:ℝ))) + (n : ℝ)) ^ 2) := by
        apply tsum_congr; intro n; congr 1; ring
    _ ≤ 1 + (α:ℝ) := gauss_lattice_le (α:ℝ) hαR (-(s:ℝ)*((k:ℝ)/(t:ℝ)))

/-- Row sums of `resSmat` are at most `1 + α⁻¹` (paper Lemma 4.5). -/
lemma resS_rowsum_le (s t α : ℕ) (hs : 0 < s) (hα : 0 < α) (k : Fin t) :
    ∑ j : Fin s, ‖HvdH.resSmat s t α k j‖ ≤ 1 + 1 / (α : ℝ) := by
  have hαR : (0:ℝ) < α := by exact_mod_cast hα
  have hstep : ∀ j : Fin s, ‖HvdH.resSmat s t α k j‖
      = (1 / (α : ℝ)) * ∑' q : ℤ,
          Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
            ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) := by
    intro j
    rw [resSmat_apply]
    have hT : 0 ≤ ∑' q : ℤ, Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
            ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) :=
      tsum_nonneg fun q => Real.exp_nonneg _
    exact (RCLike.norm_ofReal _).trans (abs_of_nonneg (mul_nonneg (by positivity) hT))
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  rw [← Finset.mul_sum]
  have hle := theta_sum_le s t α hs hα k
  have hαne : (α:ℝ) ≠ 0 := ne_of_gt hαR
  calc (1 / (α : ℝ)) * ∑ j : Fin s, ∑' q : ℤ,
        Real.exp (-(Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2) *
          ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)
      ≤ (1/(α:ℝ)) * (1 + (α:ℝ)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 + 1/(α:ℝ) := by field_simp; ring

/-- Row sums of `resA = S/2` are at most `3/4`. -/
lemma resA_rowsum_le (s t α : ℕ) (hs : 0 < s) (hα : 2 ≤ α) (k : Fin t) :
    ∑ j : Fin s, ‖HvdH.resA s t α k j‖ ≤ 3 / 4 := by
  have hα0 : 0 < α := by omega
  have hαR : (0:ℝ) < α := by exact_mod_cast hα0
  have hstep : ∀ j : Fin s, ‖HvdH.resA s t α k j‖ = (1/2 : ℝ) * ‖HvdH.resSmat s t α k j‖ := by
    intro j
    simp only [HvdH.resA, Matrix.smul_apply, smul_eq_mul]
    rw [norm_mul]
    norm_num
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  rw [← Finset.mul_sum]
  have hS := resS_rowsum_le s t α hs hα0 k
  have h2 : (1:ℝ)/α ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < α)]
    linarith [show (2:ℝ) ≤ (α:ℝ) by exact_mod_cast hα]
  calc (1/2 : ℝ) * ∑ j : Fin s, ‖HvdH.resSmat s t α k j‖ ≤ (1/2) * (1 + 1/(α:ℝ)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ ≤ 3/4 := by linarith

theorem resA_norm_le (s t α : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
    (u : Fin s → ℂ) : ‖(HvdH.resA s t α).mulVec u‖ ≤ 3 / 4 * ‖u‖ := by
  have hs0 : 0 < s := by omega
  have _ := hst
  exact norm_mulVec_le_of_row_sum (HvdH.resA s t α) (by norm_num)
    (fun k => resA_rowsum_le s t α hs0 hα k) u

end Work.ResMath
