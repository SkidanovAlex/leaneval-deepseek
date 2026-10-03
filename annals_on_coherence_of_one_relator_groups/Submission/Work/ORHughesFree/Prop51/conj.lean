/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The conjugation relation `tᵏ · a · t⁻ᵏ = τᵏ(a)` of [JZLA20, Proposition 5.1]

The embedding `D_{N,P}((t;τ)) →+* P` of [JZLA20, Proposition 5.1](iii) is a ring homomorphism
carrying the variable `t` of the skew Laurent series ring to `Φ(t)`.  Consequently the conjugated
coefficient `Φ(tᵏ) · Φ(a) · Φ(t⁻ᵏ)` of `[JZLA20, Proposition 5.1]` is nothing but `Φ` applied to
the conjugated series `tᵏ · coeff a · t⁻ᵏ`, and in `A((t;τ))` that conjugation is the `ℤ`-action
`τᵏ = (ofAdd k)•` on the coefficients, by the defining relation `t a = τ(a) t` of the ring.

That is the content of this file: the skew Laurent series ring identity

  `t^k * coeff a * t^(-k) = coeff ((ofAdd k) • a)`

(proved by two-sided induction on `k`, the descendants using `t a = τ(a) t` and its companion
`t⁻¹ a = τ⁻¹(a) t⁻¹`), transported to `P` along the ring homomorphism `laurentEmbed`, which is
the requested `conj`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.Prop51.ofGroup_t_pow
import Submission.Work.ORHughesFree.Prop51.base_case

namespace Work.ORHughesFree.Prop51

/-! ### The conjugation relation in the skew Laurent series ring `A((t;τ))` -/

/-- The companion `t⁻¹ a = τ⁻¹(a) t⁻¹` of the defining relation `t a = τ(a) t`
(`skewLaurentSeriesT_mul`) of the skew Laurent series ring: moving `a` past `t⁻¹` applies the
inverse `τ⁻¹ = ofAdd (-1)` of the automorphism `τ` to it.

The relation `t a = τ(a) t` applied to `τ⁻¹(a)` (so that `τ(τ⁻¹(a)) = a`) reads
`t · coeff (τ⁻¹ a) = coeff a · t`.  Multiplying this equality on the left by `t⁻¹` turns its left
hand side into `coeff (τ⁻¹ a)` (because `t⁻¹ t = 1`), and multiplying the resulting equality on the
right by `t⁻¹` turns `t⁻¹ · coeff a · t · t⁻¹` into `t⁻¹ · coeff a`. -/
theorem skewLaurentSeriesT_inv_mul_coeff {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (a : A) :
    (↑((skewLaurentSeriesT A)⁻¹) : SkewLaurentSeries A) * skewLaurentCoeff A a =
      skewLaurentCoeff A ((Multiplicative.ofAdd (-1 : ℤ)) • a) *
        ↑((skewLaurentSeriesT A)⁻¹) := by
  -- `τ⁻¹` is applied by `ofAdd (-1)`, and `τ (τ⁻¹ a) = a`.
  have hτ : (Multiplicative.ofAdd (1 : ℤ)) • ((Multiplicative.ofAdd (-1 : ℤ)) • a) = a := by
    rw [smul_smul, ← ofAdd_add, show (1 : ℤ) + (-1) = 0 from by norm_num, ofAdd_zero, one_smul]
  have h2 := skewLaurentSeriesT_mul A ((Multiplicative.ofAdd (-1 : ℤ)) • a)
  rw [hτ] at h2
  -- `coeff (τ⁻¹ a) = t⁻¹ · coeff a · t`, obtained from `h2 : t · coeff (τ⁻¹ a) = coeff a · t`
  -- by multiplying on the left by `t⁻¹`.
  have h3 : skewLaurentCoeff A ((Multiplicative.ofAdd (-1 : ℤ)) • a) =
      (↑((skewLaurentSeriesT A)⁻¹) : SkewLaurentSeries A) * skewLaurentCoeff A a *
        ↑(skewLaurentSeriesT A) := by
    rw [mul_assoc, ← h2, ← mul_assoc, Units.inv_mul, one_mul]
  -- Insert `t · t⁻¹ = 1` at the end and use `h3`.
  calc (↑((skewLaurentSeriesT A)⁻¹) : SkewLaurentSeries A) * skewLaurentCoeff A a
      = ↑((skewLaurentSeriesT A)⁻¹) * skewLaurentCoeff A a *
          (↑(skewLaurentSeriesT A) * ↑((skewLaurentSeriesT A)⁻¹)) := by
        rw [Units.mul_inv, mul_one]
    _ = (↑((skewLaurentSeriesT A)⁻¹) * skewLaurentCoeff A a * ↑(skewLaurentSeriesT A)) *
          ↑((skewLaurentSeriesT A)⁻¹) := by rw [← mul_assoc]
    _ = skewLaurentCoeff A ((Multiplicative.ofAdd (-1 : ℤ)) • a) *
          ↑((skewLaurentSeriesT A)⁻¹) := by rw [← h3]

/-- The commutation relation `tᵏ a = τᵏ(a) tᵏ` of the skew Laurent series ring, for every integer
power `k`: moving a coefficient `a` past `tᵏ` applies `τᵏ = ofAdd k` to it.

This is proved by two-sided induction on `k` (`Int.inductionOn'`): the successor step is the
defining relation `t a = τ(a) t` (`skewLaurentSeriesT_mul`), and the predecessor step is its
companion `t⁻¹ a = τ⁻¹(a) t⁻¹` (`skewLaurentSeriesT_inv_mul_coeff`), both followed by a
reassociation of the product inside the unit group. -/
theorem skewLaurentSeriesT_zpow_mul_coeff {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (k : ℤ) (a : A) :
    (↑((skewLaurentSeriesT A) ^ k) : SkewLaurentSeries A) * skewLaurentCoeff A a =
      skewLaurentCoeff A ((Multiplicative.ofAdd k) • a) * ↑((skewLaurentSeriesT A) ^ k) := by
  revert a
  refine Int.inductionOn' (motive := fun k => ∀ a : A,
      (↑((skewLaurentSeriesT A) ^ k) : SkewLaurentSeries A) * skewLaurentCoeff A a =
        skewLaurentCoeff A ((Multiplicative.ofAdd k) • a) * ↑((skewLaurentSeriesT A) ^ k))
    k 0 ?_ ?_ ?_
  · -- `k = 0`: `t⁰ = 1` and `ofAdd 0 = 1`.
    intro a
    rw [zpow_zero, Units.val_one, ofAdd_zero, one_smul, one_mul, mul_one]
  · -- `k ↦ k + 1`: `t^{k+1} a = tᵏ (t a) = tᵏ (τ(a) t) = (tᵏ τ(a)) t`.
    intro k _ ih a
    have hsa : (Multiplicative.ofAdd (k + 1)) • a =
        Multiplicative.ofAdd k • (Multiplicative.ofAdd (1 : ℤ) • a) := by
      rw [ofAdd_add, ← smul_smul]
    rw [hsa, zpow_add_one, Units.val_mul, mul_assoc, skewLaurentSeriesT_mul, ← mul_assoc,
      ih, mul_assoc]
  · -- `k ↦ k - 1`: `t^{k-1} a = tᵏ (t⁻¹ a) = tᵏ (τ⁻¹(a) t⁻¹) = (tᵏ τ⁻¹(a)) t⁻¹`.
    intro k _ ih a
    have hsa : (Multiplicative.ofAdd (k - 1)) • a =
        Multiplicative.ofAdd k • (Multiplicative.ofAdd (-1 : ℤ) • a) := by
      rw [show k - 1 = k + (-1) from by ring, ofAdd_add, ← smul_smul]
    rw [hsa, zpow_sub_one, Units.val_mul, mul_assoc, skewLaurentSeriesT_inv_mul_coeff,
      ← mul_assoc, ih, mul_assoc]

/-- The conjugation relation `tᵏ a t⁻ᵏ = τᵏ(a)` of the skew Laurent series ring `A((t;τ))`: the
inner automorphism of the ring induced by the unit `t` acts on the coefficients by the given
`ℤ`-action `τᵏ = ofAdd k`.

It is immediate from `tᵏ a = τᵏ(a) tᵏ` (`skewLaurentSeriesT_zpow_mul_coeff`) upon multiplying by
`t⁻ᵏ` on the right and using `tᵏ t⁻ᵏ = 1`. -/
theorem skewLaurentSeriesT_zpow_conj_coeff {A : Type} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (k : ℤ) (a : A) :
    (↑((skewLaurentSeriesT A) ^ k) : SkewLaurentSeries A) * skewLaurentCoeff A a *
        ↑((skewLaurentSeriesT A) ^ (-k)) =
      skewLaurentCoeff A ((Multiplicative.ofAdd k) • a) := by
  rw [skewLaurentSeriesT_zpow_mul_coeff k a, mul_assoc, ← Units.val_mul, ← zpow_add,
    add_neg_cancel, zpow_zero, Units.val_one, mul_one]

/-! ### The coefficient conjugation of [JZLA20, Proposition 5.1] -/

/-- The coefficient `k`-conjugated element of `D_{N,P}` maps to the conjugated coefficient in `P`:
`Φ(tᵏ) · a · Φ(t⁻ᵏ) = Φ` applied to `tᵏ · a · t⁻ᵏ = τᵏ(a)` in `D_{N,P}((t;τ))`.

`Φ(tᵏ) = laurentEmbed tᵏ` is `Φ_ofGroup_t_zpow`, `a = laurentEmbed (coeff a)` is
`laurentEmbed_coeff`, and `laurentEmbed` is a ring homomorphism, so it suffices to know the ring
identity `tᵏ · coeff a · t⁻ᵏ = coeff (τᵏ a)` of `skewLaurentSeriesT_zpow_conj_coeff`. -/
theorem conj {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (k : ℤ) (a : ↥DN) :
    d.coeffToP ((Multiplicative.ofAdd k) • a) =
      d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP a *
        d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ (-k))) := by
  calc d.coeffToP ((Multiplicative.ofAdd k) • a)
      = d.laurentEmbed (skewLaurentCoeff ↥DN ((Multiplicative.ofAdd k) • a)) :=
        (d.laurentEmbed_coeff _).symm
    _ = d.laurentEmbed ((↑((skewLaurentSeriesT ↥DN) ^ k) : SkewLaurentSeries ↥DN) *
          skewLaurentCoeff ↥DN a * ↑((skewLaurentSeriesT ↥DN) ^ (-k))) := by
        rw [skewLaurentSeriesT_zpow_conj_coeff]
    _ = d.laurentEmbed ↑((skewLaurentSeriesT ↥DN) ^ k) *
          d.laurentEmbed (skewLaurentCoeff ↥DN a) *
        d.laurentEmbed ↑((skewLaurentSeriesT ↥DN) ^ (-k)) := by rw [map_mul, map_mul]
    _ = d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP a *
        d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ (-k))) := by
        rw [ofGroup_t_pow d k, ofGroup_t_pow d (-k), d.laurentEmbed_coeff a]
        rfl

end Work.ORHughesFree.Prop51
