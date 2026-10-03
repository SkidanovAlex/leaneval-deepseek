import Mathlib
import Submission.Work.Analysis.Concentration.Bilinear
import Submission.Work.Analysis.Concentration.WeakType

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L² × L² → L^{2s}` bilinear average estimate from the fibre `L^s` bound

This file proves `bilinAverage_lq_fiber`: for the bilinear arithmetic average
`A(f,g)(x) = Q⁻¹ ∑_y f (x - y) g (x - P y)` on `ℤ/Qℤ` (the operator
`polyBilinearAverageZMod X P Q`, equation (avg-1) of §10 of Krause–Mirek–Tao),
the `L^s` concentration bound `‖h‖_{L^s} ≤ C` for the fibre counting function
`h(y) = #{x : P x = y}` of Appendix C implies the `L² × L² → L^{2s}` bound with
constant `C^{1/2}`.

The proof is the elementary one (no interpolation):

* pointwise Cauchy–Schwarz in the summation variable `y` gives
  `‖A(f,g)(x)‖² ≤ ‖f‖_{L²}² · (h ∗ |g|²)(x)`,
  where the second factor is the normalized convolution of the fibre count `h`
  with `|g|²` — this uses the reindexing `y ↦ x - y` and the identity
  `polyShiftAverageZMod P Q (|g|²) = h ∗ |g|²` (`shift_average_eq_conv`);
* Young's convolution inequality `L^s × L^1 → L^s` then bounds
  `‖h ∗ |g|²‖_{L^s} ≤ ‖h‖_{L^s} ‖ |g|² ‖_{L^1} ≤ C ‖g‖_{L²}²`.

Only `s ≥ 1` is used, matching the hypothesis `1 ≤ s`.
-/

namespace Work.Analysis.Paraproduct

open Polynomial Finset
open Work.Analysis.Concentration

/-- The normalized `L²` norm of a function on `ℤ/Qℤ`, squared, is the average of the squared
moduli: `‖u‖_{L²}² = Q⁻¹ ∑_x ‖u x‖²`. -/
lemma LpNormZMod_two_sq (Q : ℕ) [NeZero Q] (u : ZMod Q → ℂ) :
    (LpNormZMod Q 2 u) ^ 2 = (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖u x‖ ^ 2 := by
  rw [← Real.rpow_two, LpNormZMod_rpow Q (by norm_num) u]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => Real.rpow_two _)

/-- **Pointwise Cauchy–Schwarz for the bilinear average.**  For every `x`,

`‖A(f,g)(x)‖² ≤ ‖f‖_{L²}² · ‖ A_{P}(|g|²)(x) ‖`,

where `A_P(v)(x) = Q⁻¹ ∑_y v (x - P y)` is the linear polynomial average of `v = |g|²`.
The right-hand factor is the convolution of the fibre counting function with `|g|²`
(`shift_average_eq_conv`), which is why the fibre `L^s` bound controls the bilinear estimate. -/
lemma bilinAverage_pointwise_sq_le (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ)
    (x : ZMod Q) :
    ‖polyBilinearAverageZMod Polynomial.X P Q f g x‖ ^ 2
      ≤ (LpNormZMod Q 2 f) ^ 2 *
          ‖polyShiftAverageZMod P Q (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) x‖ := by
  have hnormQ : ‖((Q : ℂ))⁻¹‖ = (Q : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_def, Complex.normSq_natCast, Real.sqrt_mul_self (by positivity)]
  have hAx : polyBilinearAverageZMod Polynomial.X P Q f g x
      = (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y) := by
    simp only [polyBilinearAverageZMod, polyEvalZMod_X]
  have hreindex : (∑ y : ZMod Q, ‖f (x - y)‖ ^ 2) = ∑ z : ZMod Q, ‖f z‖ ^ 2 := by
    simpa using Equiv.sum_comp (Equiv.subLeft x) (fun z : ZMod Q => ‖f z‖ ^ 2)
  have hCS : ‖∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)‖ ^ 2
      ≤ (∑ z : ZMod Q, ‖f z‖ ^ 2) * (∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2) := by
    calc ‖∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)‖ ^ 2
        ≤ (∑ y : ZMod Q, ‖f (x - y) * g (x - polyEvalZMod P Q y)‖) ^ 2 := by
          simpa only [pow_two] using
            mul_self_le_mul_self (norm_nonneg _) (norm_sum_le _ _)
      _ = (∑ y : ZMod Q, ‖f (x - y)‖ * ‖g (x - polyEvalZMod P Q y)‖) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun y _ => norm_mul _ _)
      _ ≤ (∑ y : ZMod Q, ‖f (x - y)‖ ^ 2) *
            (∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ z : ZMod Q, ‖f z‖ ^ 2) * (∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2) := by
          rw [hreindex]
  have hSx : ‖polyShiftAverageZMod P Q (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) x‖
      = (Q : ℝ)⁻¹ * ∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2 := by
    rw [polyShiftAverageZMod, norm_mul, hnormQ,
      norm_sum_ofReal Q (fun y : ZMod Q => ‖g (x - polyEvalZMod P Q y)‖ ^ 2)
        (fun y => by positivity)]
  calc ‖polyBilinearAverageZMod Polynomial.X P Q f g x‖ ^ 2
      = ((Q : ℝ)⁻¹ * ‖∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)‖) ^ 2 := by
        rw [hAx, norm_mul, hnormQ]
    _ = (Q : ℝ)⁻¹ ^ 2 * ‖∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)‖ ^ 2 := by
        ring
    _ ≤ (Q : ℝ)⁻¹ ^ 2 *
          ((∑ z : ZMod Q, ‖f z‖ ^ 2) *
            (∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (LpNormZMod Q 2 f) ^ 2 *
          ((Q : ℝ)⁻¹ * ∑ y : ZMod Q, ‖g (x - polyEvalZMod P Q y)‖ ^ 2) := by
        rw [LpNormZMod_two_sq]
        ring
    _ = (LpNormZMod Q 2 f) ^ 2 *
          ‖polyShiftAverageZMod P Q (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) x‖ := by
        rw [hSx]

/-- **The bilinear arithmetic average maps `L² × L²` into `L^{2s}`** with constant `√C`, where
`C` bounds the `L^s` norm of the fibre counting function `h(y) = #{x : P x = y}`.

This is equation (avg-1) of §10 of Krause–Mirek–Tao in the sharp form in which it is used,
proved directly by Cauchy–Schwarz and Young's inequality (no bilinear interpolation). -/
theorem bilinAverage_lq_fiber (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {s C : ℝ} (hs : 1 ≤ s)
    (hC : Work.Analysis.Concentration.LpNormZMod Q s
      (fun m => (Work.Analysis.Concentration.polyFiberCard P Q m : ℂ)) ≤ C) :
    ∀ f g : ZMod Q → ℂ,
      Work.Analysis.Concentration.LpNormZMod Q (2 * s)
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ Real.sqrt C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
          Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  intro f g
  set A := polyBilinearAverageZMod Polynomial.X P Q f g with hA
  set GG : ZMod Q → ℂ := fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ) with hGG
  set S := polyShiftAverageZMod P Q GG with hS
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hs2 : (0 : ℝ) < 2 * s := by linarith
  have hC0 : 0 ≤ C :=
    le_trans (LpNormZMod_nonneg Q s (fun m => (polyFiberCard P Q m : ℂ))) hC
  have hYnn : (0 : ℝ) ≤ Real.sqrt C * LpNormZMod Q 2 f * LpNormZMod Q 2 g :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) (LpNormZMod_nonneg Q 2 f))
      (LpNormZMod_nonneg Q 2 g)
  have hpt : ∀ x : ZMod Q, ‖A x‖ ^ 2 ≤ (LpNormZMod Q 2 f) ^ 2 * ‖S x‖ :=
    fun x => bilinAverage_pointwise_sq_le P Q f g x
  have hYoung1 : LpNormZMod Q 1 GG = (LpNormZMod Q 2 g) ^ 2 := by
    rw [LpNormZMod_two_sq, LpNormZMod_one_eq]
    congr 1
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hGG]
    exact norm_ofReal_complex (by positivity)
  have hYoungS : LpNormZMod Q s S ≤ C * (LpNormZMod Q 2 g) ^ 2 := by
    have hconv : LpNormZMod Q s S = LpNormZMod Q s (convZMod Q (fiberFun P Q) GG) := by
      rw [hS, shift_average_eq_conv]
    rw [hconv]
    calc LpNormZMod Q s (convZMod Q (fiberFun P Q) GG)
        ≤ LpNormZMod Q s (fiberFun P Q) * LpNormZMod Q 1 GG :=
          young_zmod Q hs le_rfl hs (by rw [div_one]; ring) _ _
      _ ≤ C * (LpNormZMod Q 2 g) ^ 2 := by
          rw [hYoung1]
          exact mul_le_mul_of_nonneg_right
            (hC : LpNormZMod Q s (fiberFun P Q) ≤ C) (sq_nonneg _)
  have hsq2 : (Real.sqrt C * LpNormZMod Q 2 f * LpNormZMod Q 2 g) ^ (2 : ℝ)
      = (LpNormZMod Q 2 f) ^ 2 * (C * (LpNormZMod Q 2 g) ^ 2) := by
    rw [Real.rpow_two]
    have h2 : (Real.sqrt C * LpNormZMod Q 2 f * LpNormZMod Q 2 g) ^ 2
        = Real.sqrt C ^ 2 * (LpNormZMod Q 2 f) ^ 2 * (LpNormZMod Q 2 g) ^ 2 := by ring
    rw [h2, Real.sq_sqrt hC0]
    ring
  have hmain : (LpNormZMod Q (2 * s) A) ^ (2 * s)
      ≤ (Real.sqrt C * LpNormZMod Q 2 f * LpNormZMod Q 2 g) ^ (2 * s) := by
    rw [LpNormZMod_rpow Q hs2 A]
    calc (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖A x‖ ^ (2 * s)
        ≤ (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ((LpNormZMod Q 2 f) ^ 2 * ‖S x‖) ^ s := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => ?_)) (by positivity)
          rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
          exact Real.rpow_le_rpow (sq_nonneg _) (hpt x) hs0.le
      _ = ((LpNormZMod Q 2 f) ^ 2) ^ s * (LpNormZMod Q s S) ^ s := by
          have hterm : ∀ x : ZMod Q, ((LpNormZMod Q 2 f) ^ 2 * ‖S x‖) ^ s
              = ((LpNormZMod Q 2 f) ^ 2) ^ s * ‖S x‖ ^ s := fun x =>
            Real.mul_rpow (sq_nonneg (LpNormZMod Q 2 f)) (norm_nonneg (S x))
          simp only [hterm]
          rw [LpNormZMod_rpow Q hs0 S, ← Finset.mul_sum]
          ring
      _ ≤ ((LpNormZMod Q 2 f) ^ 2) ^ s * (C * (LpNormZMod Q 2 g) ^ 2) ^ s :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (LpNormZMod_nonneg Q s S) hYoungS hs0.le) (by positivity)
      _ = (Real.sqrt C * LpNormZMod Q 2 f * LpNormZMod Q 2 g) ^ (2 * s) := by
          rw [Real.rpow_mul hYnn, ← Real.mul_rpow (sq_nonneg (LpNormZMod Q 2 f))
                (mul_nonneg hC0 (sq_nonneg (LpNormZMod Q 2 g))), hsq2]
  rw [Real.rpow_le_rpow_iff (LpNormZMod_nonneg Q (2 * s) A) hYnn hs2] at hmain
  exact hmain

end Work.Analysis.Paraproduct
