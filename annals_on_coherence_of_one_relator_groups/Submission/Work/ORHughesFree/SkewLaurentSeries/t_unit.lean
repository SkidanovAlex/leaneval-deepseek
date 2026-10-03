import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.SkewLaurentSeries

section

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- The monomial `a·tᵐ` of `A((t;τ))`: the series whose only possibly nonzero coefficient is `a`,
at `m`. -/
private noncomputable def mono (m : ℤ) (a : A) : SkewLaurentSeries A :=
  ⟨fun n => if n = m then a else 0, ⟨m - 1, fun n hn => by
    simp only [show n ≠ m by omega, if_false]⟩⟩

private theorem mono_apply (m : ℤ) (a : A) (n : ℤ) :
    (mono m a).1 n = if n = m then a else 0 := rfl

/-- The product of two monomials is again a monomial: `(a·tᵐ)(b·tᵏ) = (a·(m•b))·tᵐ⁺ᵏ`, the
skew factor being the action `tᵐ b = (ofAdd m • b) tᵐ`. -/
private theorem mono_mul (m k : ℤ) (a b : A) :
    mono m a * mono k b = mono (m + k) (a * (Multiplicative.ofAdd m • b)) := by
  apply Subtype.ext
  funext n
  rw [mul_apply_of_bounds (mono m a) (mono k b) (m - 1) (k - 1)
    (fun i hi => by rw [mono_apply, if_neg (by omega : i ≠ m)])
    (fun i hi => by rw [mono_apply, if_neg (by omega : i ≠ k)]) n]
  rw [Finset.sum_eq_single m]
  · rw [mono_apply, mono_apply, mono_apply, if_pos rfl]
    rw [smul_ite, smul_zero, mul_ite, mul_zero]
    exact if_congr (by omega : n - m = k ↔ n = m + k) rfl rfl
  · intro i _ hi
    rw [mono_apply, if_neg hi, zero_mul]
  · intro hm
    rw [Finset.mem_Icc] at hm
    rw [mono_apply, if_pos rfl, mono_apply, if_neg (by omega : n - m ≠ k),
      smul_zero, mul_zero]

/-- The monomial `t⁻¹` of `A((t;τ))`: the series with the single nonzero coefficient `1` at `-1`.
It is the two-sided inverse of `t`. -/
private noncomputable def tInv : SkewLaurentSeries A := mono (-1) 1

private theorem t_eq_mono : (t : SkewLaurentSeries A) = mono 1 1 := Subtype.ext rfl

private theorem mono_zero_one : mono 0 (1 : A) = (1 : SkewLaurentSeries A) := Subtype.ext rfl

private theorem tInv_eq_mono : tInv = (mono (-1) (1 : A) : SkewLaurentSeries A) := rfl

private theorem t_mul_tInv : (t : SkewLaurentSeries A) * tInv = 1 := by
  rw [t_eq_mono, tInv_eq_mono, mono_mul, show (1 : ℤ) + -1 = 0 from by norm_num,
    MulSemiringAction.smul_one, mul_one]
  exact mono_zero_one

private theorem tInv_mul_t : tInv * (t : SkewLaurentSeries A) = 1 := by
  rw [t_eq_mono, tInv_eq_mono, mono_mul, show (-1 : ℤ) + 1 = 0 from by norm_num,
    MulSemiringAction.smul_one, mul_one]
  exact mono_zero_one

end

theorem t_unit {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    ∃ u : SkewLaurentSeries A, (t : SkewLaurentSeries A) * u = 1 ∧ u * t = 1 :=
  ⟨tInv, t_mul_tInv, tInv_mul_t⟩

end Work.ORHughesFree.SkewLaurentSeries
