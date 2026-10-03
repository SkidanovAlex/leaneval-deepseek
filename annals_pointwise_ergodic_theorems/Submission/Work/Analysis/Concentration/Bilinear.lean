/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.Improving

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bilinear arithmetic averaging estimates of Section 10

Section 10 of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, proves `L² × L² → L^q` bounds for the arithmetic bilinear average
`A_{ℤ/p^jℤ}(f,g)(x) = 𝔼_{y} f(x - y) g(x - P(y))` for `2 ≤ q < 2d/(d-1)` (equations (avg-1),
(avg-2)).  The proof reduces the claim by bilinear interpolation to the two endpoint estimates

* (avg-3) `‖A(f,g)‖_{L^∞} ≤ ‖f‖_{L¹}‖g‖_{L^∞}` (`bilinear_l1_linfty`), and
* (avg-4) `‖A(f,g)‖_{L^s} ≤ C‖f‖_{L^∞}‖g‖_{L¹}` for `1 ≤ s < d/(d-1)`
  (`bilinear_linfty_l1_ls`),

the second of which is a consequence of the Appendix C concentration estimate
(`FiberLpBound`).  Both endpoints are proved here.  The interpolation step itself is recorded as
the explicit predicate `BilinearInterpolationStep` — it is an instance of bilinear
Riesz–Thorin/Stein interpolation, which is not part of this library.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory
open scoped NNReal

noncomputable section

/-- `polyEvalZMod X Q` is the identity. -/
lemma polyEvalZMod_X (Q : ℕ) (x : ZMod Q) : polyEvalZMod Polynomial.X Q x = x := by
  rw [polyEvalZMod_def, polyMapZMod, Polynomial.map_X, Polynomial.eval_X]

/-- The supremum norm of a function on `ℤ/Qℤ` is bounded by any pointwise bound. -/
lemma pi_norm_le_of_forall_le {Q : ℕ} [NeZero Q] {f : ZMod Q → ℂ} {c : ℝ}
    (h : ∀ i, ‖f i‖ ≤ c) : ‖f‖ ≤ c := by
  have h0 : (0 : ℝ) ≤ c := le_trans (norm_nonneg (f 0)) (h 0)
  have hb : ∀ b, ‖f b‖₊ ≤ (Real.toNNReal c : ℝ≥0) := by
    intro b
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal c h0]
    exact h b
  rw [Pi.norm_def]
  calc ((Finset.univ.sup (fun b : ZMod Q => ‖f b‖₊) : ℝ≥0) : ℝ)
      ≤ ((Real.toNNReal c : ℝ≥0) : ℝ) := by exact_mod_cast Finset.sup_le (fun b _ => hb b)
    _ = c := Real.coe_toNNReal c h0

/-- The sum over `ℤ/Qℤ` of the complexification of a nonnegative real-valued function has norm
equal to the sum. -/
lemma norm_sum_ofReal (Q : ℕ) [NeZero Q] (v : ZMod Q → ℝ) (hv : ∀ y, 0 ≤ v y) :
    ‖∑ y : ZMod Q, ((v y : ℝ) : ℂ)‖ = ∑ y : ZMod Q, v y := by
  rw [← Complex.ofReal_sum, Complex.norm_def, Complex.normSq_ofReal,
    Real.sqrt_mul_self (Finset.sum_nonneg fun y _ => hv y)]

/-- The normalized `L^1` norm is the average of the pointwise norms. -/
lemma LpNormZMod_one_eq (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    LpNormZMod Q 1 f = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖f z‖ := by
  unfold LpNormZMod
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  congr 1
  exact Finset.sum_congr rfl (fun z _ => Real.rpow_one _)

/-- **(avg-3).**  The bilinear arithmetic average satisfies
`‖A(f,g)‖_{L^∞} ≤ ‖f‖_{L¹} ‖g‖_{L^∞}`. -/
theorem bilinear_l1_linfty {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] (f g : ZMod Q → ℂ)
    (x : ZMod Q) :
    ‖polyBilinearAverageZMod Polynomial.X P Q f g x‖ ≤ LpNormZMod Q 1 f * ‖g‖ := by
  have h1 : ‖∑ y : ZMod Q, f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖
      ≤ ‖g‖ * ∑ z : ZMod Q, ‖f z‖ := by
    calc ‖∑ y : ZMod Q, f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖
        ≤ ∑ y : ZMod Q,
            ‖f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖ :=
          norm_sum_le _ _
      _ = ∑ y : ZMod Q,
            ‖f (x - polyEvalZMod Polynomial.X Q y)‖ * ‖g (x - polyEvalZMod P Q y)‖ :=
          Finset.sum_congr rfl (fun y _ => norm_mul _ _)
      _ ≤ ∑ y : ZMod Q, ‖f (x - polyEvalZMod Polynomial.X Q y)‖ * ‖g‖ :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm g _)
            (norm_nonneg _))
      _ = (∑ y : ZMod Q, ‖f (x - polyEvalZMod Polynomial.X Q y)‖) * ‖g‖ := by
          rw [Finset.sum_mul]
      _ = (∑ z : ZMod Q, ‖f z‖) * ‖g‖ := by
          congr 1
          rw [← Equiv.sum_comp (Equiv.subLeft x) (fun z : ZMod Q => ‖f z‖)]
          exact Finset.sum_congr rfl (fun y _ => by rw [polyEvalZMod_X]; rfl)
      _ = ‖g‖ * ∑ z : ZMod Q, ‖f z‖ := by ring
  rw [polyBilinearAverageZMod, norm_mul]
  have hnorm : ‖((Q : ℂ))⁻¹‖ = (Q : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_def, Complex.normSq_natCast, Real.sqrt_mul_self (by positivity)]
  rw [hnorm]
  calc (Q : ℝ)⁻¹ * ‖∑ y : ZMod Q,
        f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖
      ≤ (Q : ℝ)⁻¹ * (‖g‖ * ∑ z : ZMod Q, ‖f z‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖f z‖) * ‖g‖ := by ring
    _ = LpNormZMod Q 1 f * ‖g‖ := by
        congr 1
        exact (LpNormZMod_one_eq Q f).symm

/-- **(avg-4).**  The bilinear arithmetic average satisfies
`‖A(f,g)‖_{L^s} ≤ C ‖f‖_{L^∞} ‖g‖_{L¹}` whenever `C` is a constant for the `L^s` concentration
bound `FiberLpBound P Q s C` of Appendix C. -/
theorem bilinear_linfty_l1_ls {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {s C : ℝ}
    (hs : 1 < s) (hC : 0 ≤ C) (h : FiberLpBound P Q s C) (f g : ZMod Q → ℂ) :
    LpNormZMod Q s (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ C * ‖f‖ * LpNormZMod Q 1 g := by
  have hpt : ∀ x : ZMod Q, ‖polyBilinearAverageZMod Polynomial.X P Q f g x‖
      ≤ ‖f‖ * ‖polyShiftAverageZMod P Q (fun z => ((‖g z‖ : ℝ) : ℂ)) x‖ := by
    intro x
    have hstep : ‖polyBilinearAverageZMod Polynomial.X P Q f g x‖
        ≤ (Q : ℝ)⁻¹ * ∑ y : ZMod Q, ‖f‖ * ‖g (x - polyEvalZMod P Q y)‖ := by
      rw [polyBilinearAverageZMod, norm_mul]
      have hnorm : ‖((Q : ℂ))⁻¹‖ = (Q : ℝ)⁻¹ := by
        rw [norm_inv, Complex.norm_def, Complex.normSq_natCast,
          Real.sqrt_mul_self (by positivity)]
      rw [hnorm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖∑ y : ZMod Q, f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖
          ≤ ∑ y : ZMod Q,
              ‖f (x - polyEvalZMod Polynomial.X Q y) * g (x - polyEvalZMod P Q y)‖ :=
            norm_sum_le _ _
        _ = ∑ y : ZMod Q,
              ‖f (x - polyEvalZMod Polynomial.X Q y)‖ * ‖g (x - polyEvalZMod P Q y)‖ :=
            Finset.sum_congr rfl (fun y _ => norm_mul _ _)
        _ ≤ ∑ y : ZMod Q, ‖f‖ * ‖g (x - polyEvalZMod P Q y)‖ :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (norm_le_pi_norm f _)
              (norm_nonneg _))
        _ = ∑ y : ZMod Q, ‖f‖ * ‖g (x - polyEvalZMod P Q y)‖ := rfl
    refine hstep.trans ?_
    rw [polyShiftAverageZMod, norm_mul]
    have hnorm : ‖((Q : ℂ))⁻¹‖ = (Q : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_def, Complex.normSq_natCast, Real.sqrt_mul_self (by positivity)]
    rw [hnorm, norm_sum_ofReal Q _ (fun y => norm_nonneg _)]
    rw [← Finset.mul_sum]
    exact le_of_eq (by ring)
  calc LpNormZMod Q s (polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ LpNormZMod Q s
          (fun x => ((‖f‖ : ℝ) : ℂ) * polyShiftAverageZMod P Q (fun z => ((‖g z‖ : ℝ) : ℂ)) x) := by
        apply LpNormZMod_mono (Q := Q) (s := s) (by linarith)
        intro x
        refine (hpt x).trans (le_of_eq ?_)
        rw [norm_mul, norm_ofReal_complex (norm_nonneg f)]
    _ = ‖f‖ * LpNormZMod Q s (polyShiftAverageZMod P Q (fun z => ((‖g z‖ : ℝ) : ℂ))) :=
        LpNormZMod_const_mul Q (by linarith) (norm_nonneg f) _
    _ ≤ ‖f‖ * (C * LpNormZMod Q 1 (fun z => ((‖g z‖ : ℝ) : ℂ))) :=
        mul_le_mul_of_nonneg_left
          (polyImproving_l1_ls hs hC h (fun z => ((‖g z‖ : ℝ) : ℂ))) (norm_nonneg _)
    _ = ‖f‖ * (C * LpNormZMod Q 1 g) := by
        congr 2
        rw [LpNormZMod_one_eq, LpNormZMod_one_eq]
        congr 1
        exact Finset.sum_congr rfl (fun z _ => norm_ofReal_complex (norm_nonneg _))
    _ = C * ‖f‖ * LpNormZMod Q 1 g := by ring

/-- **The bilinear interpolation step of Section 10.**  The two endpoint estimates
`L¹ × L^∞ → L^∞` and `L^∞ × L¹ → L^s` imply, by bilinear Riesz–Thorin/Stein interpolation, the
`L² × L² → L^{2s}` bound.  This predicate records the interpolation step explicitly; it is the
only ingredient of (avg-1) that is not formalised in this library. -/
def BilinearInterpolationStep (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (s C : ℝ) : Prop :=
  (∀ f g : ZMod Q → ℂ,
      LpNormZMod Q s (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ C * ‖f‖ * LpNormZMod Q 1 g) →
  (∀ f g : ZMod Q → ℂ,
      ‖polyBilinearAverageZMod Polynomial.X P Q f g‖ ≤ LpNormZMod Q 1 f * ‖g‖) →
  BilinearAverageLq P Q (2 * s) (C ^ (1 / 2))

/-- **(avg-1), reduced to the interpolation step.**  For `2 ≤ q < 2d/(d-1)`, i.e. `q = 2s` with
`s` in the range of the Appendix C concentration estimate, the bilinear arithmetic average maps
`L² × L²` into `L^q` with constant `C^{1/2}`. -/
theorem bilinearAverageLq_of_endpoints {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {s C : ℝ}
    (hint : BilinearInterpolationStep P Q s C) (hs : 1 < s) (hC : 0 ≤ C)
    (h : FiberLpBound P Q s C) :
    BilinearAverageLq P Q (2 * s) (C ^ (1 / 2)) :=
  hint (fun f g => bilinear_linfty_l1_ls hs hC h f g)
    (fun f g => pi_norm_le_of_forall_le (fun x => bilinear_l1_linfty (P := P) f g x))

end

end Work.Analysis.Concentration
