import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries

/-!
# The `m`-th coefficient of `a · tᵏ` in `A((t;τ))`

The `m`-th coefficient of the series `a · tᵏ` (for `a : A` and `k : ℤ`) is `a` when `m = k` and
`0` otherwise.  The proof is a monomial computation: writing `mono k b` for the series whose only
possibly nonzero coefficient is `b` at `k`, one has
`mono m a * mono k b = mono (m+k) (a * ((ofAdd m) • b))`, and the integer powers of the unit `t`
are exactly the monomials `mono k 1`.  Since `coeff a = mono 0 a` and
`(coeff a * f).1 n = a * f.1 n` (`SkewLaurentSeries.coeff_mul_apply`), the coefficient is
`a * (mono k 1).1 m = a * (if m = k then 1 else 0)`.
-/

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

/-- The monomial `a·tᵐ` of `A((t;τ))`: the series whose only possibly nonzero coefficient is `a`,
at `m`. -/
private def mono {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (m : ℤ) (a : A) : SkewLaurentSeries A :=
  ⟨fun n => if n = m then a else 0, ⟨m - 1, fun n hn => by
    simp only [show n ≠ m by omega, if_false]⟩⟩

private theorem mono_apply {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (m : ℤ) (a : A) (n : ℤ) : (mono m a).1 n = if n = m then a else 0 := rfl

/-- The product of two monomials is a monomial: `(a·tᵐ)(b·tᵏ) = (a·(ofAdd m • b))·tᵐ⁺ᵏ`. -/
private theorem mono_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (m k : ℤ) (a b : A) :
    mono m a * mono k b = mono (m + k) (a * (Multiplicative.ofAdd m • b)) := by
  apply Subtype.ext
  funext n
  rw [SkewLaurentSeries.mul_apply_of_bounds (mono m a) (mono k b) (m - 1) (k - 1)
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

private theorem mono_zero_one {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    mono 0 (1 : A) = (1 : SkewLaurentSeries A) := Subtype.ext rfl

private theorem t_eq_mono {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    (SkewLaurentSeries.t : SkewLaurentSeries A) = mono 1 1 := Subtype.ext rfl

private theorem unit_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    mono 1 (1 : A) * mono (-1) 1 = 1 := by
  rw [mono_mul, show (1 : ℤ) + -1 = 0 from by norm_num, MulSemiringAction.smul_one, mul_one]
  exact mono_zero_one

private theorem unit_inv_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    mono (-1) (1 : A) * mono 1 1 = 1 := by
  rw [mono_mul, show (-1 : ℤ) + 1 = 0 from by norm_num, MulSemiringAction.smul_one, mul_one]
  exact mono_zero_one

/-- The unit `t = mono 1 1` of `A((t;τ))`, presented as an explicit unit with inverse
`mono (-1) 1`. -/
private def tUnit (A : Type) [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    (SkewLaurentSeries A)ˣ :=
  ⟨mono 1 1, mono (-1) 1, unit_mul, unit_inv_mul⟩

private theorem tUnit_eq {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    tUnit A = skewLaurentSeriesT A := Units.ext (t_eq_mono.symm)

private theorem tUnit_inv_coe {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    ↑((tUnit A)⁻¹) = mono (-1) (1 : A) := rfl

private theorem tUnit_coe {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] :
    ↑(tUnit A) = mono 1 (1 : A) := rfl

/-- The integer powers of `t` are the monomials `mono k 1`: `tᵏ = mono k 1` in `A((t;τ))`. -/
private theorem tUnit_zpow_coe {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (k : ℤ) : ↑((tUnit A) ^ k) = mono k (1 : A) := by
  refine Int.inductionOn' k 0 ?_ ?_ ?_
  · rw [zpow_zero, Units.val_one, mono_zero_one]
  · intro k hk ih
    rw [zpow_add_one, Units.val_mul, ih, tUnit_coe, mono_mul, MulSemiringAction.smul_one, mul_one]
  · intro k hk ih
    rw [zpow_sub_one, Units.val_mul, ih, tUnit_inv_coe, mono_mul, MulSemiringAction.smul_one,
      mul_one, show (k : ℤ) + -1 = k - 1 from by ring]

/-- The `m`-th coefficient of `a · tᵏ` is `a` if `m = k` and `0` otherwise. -/
theorem coeff_zpowT {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (a : A) (k m : ℤ) :
    ((Work.ORHughesFree.skewLaurentCoeff A a) *
        ↑((Work.ORHughesFree.skewLaurentSeriesT A) ^ k)).1 m = if m = k then a else 0 := by
  have hcoe : (skewLaurentCoeff A a : SkewLaurentSeries A) = SkewLaurentSeries.coeff a := rfl
  rw [hcoe, ← tUnit_eq, SkewLaurentSeries.coeff_mul_apply, tUnit_zpow_coe, mono_apply,
    mul_ite, mul_one, mul_zero]

end Work.ORHughesFree.Prop51
