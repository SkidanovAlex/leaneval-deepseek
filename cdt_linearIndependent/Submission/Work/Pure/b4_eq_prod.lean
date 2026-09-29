import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.interfaces
import Submission.Work.Pure.b4_aux

/-!
# The product formula `B₄ = 4·y·Fser·fG`

Calegari--Dimitrov--Tang, arXiv:2408.15403, Section "Pure functions".  The pure function

`B₄ = 4 Σ_{n≥0} y^{n+1}/16ⁿ Σ_k C(2k,k)·C(2n-2k,n-k)/((2k-1)(2n-2k+1)²)`

(paper eq. `(defB)`, formalised as `Submission.CDTPlan.B4`) has a double-binomial
coefficient which is the `k`-convolution of the two auxiliary series

* `Fser = Σ_n C(2n,n) yⁿ/((2n-1)·16ⁿ) = -√(1-y/4)`   (`Work.Pure.Fser`),
* `fG   = Σ_n C(2n,n) yⁿ/((2n+1)²·16ⁿ)`               (`Work.Pure.fG`),

i.e. `B₄ = 4·y·Fser·fG` as (ordinary, Cauchy) products of power series.  This is
proved here coefficient by coefficient: for `m : ℕ` the coefficient of `y^{m+1}`
on the right is `4 Σ_{i+j=m} C(2i,i)C(2j,j)/((2i-1)(2j+1)²·16^{i+j})`, which is
exactly the inner sum defining the coefficient of `y^{m+1}` in `B₄`.

The definitions `Fser`, `fG` live in `Submission.Work.Pure.b4_aux`.
-/

namespace Work.Pure

open PowerSeries
open scoped BigOperators

noncomputable section

/-- The natural number `4` inside `ℚ⟦X⟧` is the image of the rational `4`. -/
lemma four_eq_C : (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) :=
  (map_natCast PowerSeries.C 4).symm

/-- `4·y·Fser·fG` regrouped as `C 4 · (y · (Fser · fG))`. -/
lemma fourXFserfG_eq (F G : PowerSeries ℚ) :
    (4 * PowerSeries.X * F * G : PowerSeries ℚ) =
      PowerSeries.C (4 : ℚ) * (PowerSeries.X * (F * G)) := by
  rw [← four_eq_C]
  ring

/-- Constant coefficient of `4·y·Fser·fG`. -/
lemma coeff_zero_fourXFserfG :
    PowerSeries.coeff 0 (4 * PowerSeries.X * Fser * fG : PowerSeries ℚ) = 0 := by
  rw [fourXFserfG_eq, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, mul_zero]

/-- The coefficient of `y^{m+1}` of `4·y·Fser·fG` is the convolution of the
coefficients of `Fser` and `fG`. -/
lemma coeff_succ_fourXFserfG (m : ℕ) :
    PowerSeries.coeff (m + 1) (4 * PowerSeries.X * Fser * fG : PowerSeries ℚ) =
      4 * ∑ i ∈ Finset.range (m + 1),
        PowerSeries.coeff i Fser * PowerSeries.coeff (m - i) fG := by
  rw [fourXFserfG_eq, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i Fser * PowerSeries.coeff j fG) m]

/-- The individual terms of the convolution: for `i ≤ m`,
`[y^i]Fser · [y^{m-i}]fG = 16^{-m} · C(2i,i)C(2(m-i),m-i)/((2i-1)(2(m-i)+1)²)`. -/
lemma conv_term (i m : ℕ) (him : i ≤ m) :
    (Nat.centralBinom i : ℚ) / ((2 * (i : ℚ) - 1) * 16 ^ i) *
      ((Nat.centralBinom (m - i) : ℚ) / ((2 * ((m - i : ℕ) : ℚ) + 1) ^ 2 * 16 ^ (m - i)))
    = (1 / 16 ^ m) * ((Nat.centralBinom i * Nat.centralBinom (m - i) : ℚ) /
        ((2 * (i : ℚ) - 1) * (2 * ((m - i : ℕ) : ℚ) + 1) ^ 2)) := by
  have h16 : (16 : ℚ) ^ i * 16 ^ (m - i) = 16 ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' him]
  have hd : (2 * (i : ℚ) - 1) ≠ 0 := by
    rcases i with _ | i
    · norm_num
    · have : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
      push_cast
      linarith
  have he : ((2 * ((m - i : ℕ) : ℚ) + 1) ^ 2 : ℚ) ≠ 0 := by
    have : (0 : ℚ) < 2 * ((m - i : ℕ) : ℚ) + 1 := by positivity
    positivity
  field_simp
  rw [← h16]
  ring

/-- The coefficient of `y^{m+1}` of the defining double sum of `B₄`, reindexed. -/
lemma coeff_succ_B4 (m : ℕ) :
    PowerSeries.coeff (m + 1) Submission.CDTPlan.B4 =
      4 / 16 ^ m * ∑ k ∈ Finset.range (m + 1),
        (Nat.centralBinom k * Nat.centralBinom (m - k) : ℚ) /
          ((2 * (k : ℚ) - 1) * (2 * ((m - k : ℕ) : ℚ) + 1) ^ 2) := by
  simp [Submission.CDTPlan.B4]

theorem b4_eq_prod : Submission.CDTPlan.B4 = 4 * PowerSeries.X * Work.Pure.Fser * Work.Pure.fG := by
  ext m
  rcases m with _ | m
  · rw [coeff_zero_fourXFserfG]
    simp [Submission.CDTPlan.B4]
  · rw [coeff_succ_fourXFserfG m, coeff_succ_B4 m]
    have hstep : ∀ i ∈ Finset.range (m + 1),
        PowerSeries.coeff i Fser * PowerSeries.coeff (m - i) fG
          = (1 / 16 ^ m) * ((Nat.centralBinom i * Nat.centralBinom (m - i) : ℚ) /
              ((2 * (i : ℚ) - 1) * (2 * ((m - i : ℕ) : ℚ) + 1) ^ 2)) := by
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [coeff_Fser, coeff_fG]
      exact conv_term i m him
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    ring

end

end Work.Pure
