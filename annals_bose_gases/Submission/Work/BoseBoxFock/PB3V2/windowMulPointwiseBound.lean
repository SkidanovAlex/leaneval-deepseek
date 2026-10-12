import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.windowMulPointwiseBound`

The pointwise product-rule estimate for the windowed state `χ_ℓ · f`:

    `Σ_j ‖∂_j(χ_ℓ · f)(z)‖² ≤ 2 χ_ℓ(z)² Σ_j ‖∂_j f(z)‖² + 6 D² ‖f z‖²`

where `{e_j = kcStdBasis j}` is the standard orthonormal basis of `ℝ³` and `D` bounds the
gradient of `χ_ℓ` in the direction-free form `|dχ_ℓ(x) v| ≤ D ‖v‖`.

## Proof

The product rule (`fderiv_mul`, with `ℂ` as a `NormedAlgebra ℝ`) evaluated on `e_j` gives

    `∂_j(χ_ℓ·f)(z) = χ_ℓ(z)·∂_j f(z) + f(z)·∂_j χ_ℓ(z)`

(the scalar `χ_ℓ(z) ∈ ℝ` is pushed into `ℂ`; `hdchi` is the chain rule for `ℂ.ofReal ∘ χ_ℓ`,
whose differential is `Complex.ofRealCLM ∘ dχ_ℓ`).  Taking norms,

    `‖∂_j(χ_ℓ·f)(z)‖ ≤ χ_ℓ(z)·‖∂_j f(z)‖ + ‖f z‖·|∂_j χ_ℓ(z)|`

(`χ_ℓ ≥ 0`, `‖(r:ℂ)‖ = |r|`), and the elementary `(a+b)² ≤ 2a² + 2b²` turns this into a
square bound.  Summing over the three basis directions leaves only the gradient norm of the
window, which is estimated by the hypothesis: `|dχ_ℓ(z) e_j| ≤ D ‖e_j‖ = D`, so
`Σ_j |∂_j χ_ℓ(z)|² ≤ 3 D²`.  The result is `2χ_ℓ(z)² Σ‖∂_j f‖² + 6 D²‖f z‖²`.
-/

namespace Work.BoseBoxFock.PB3V2

theorem windowMulPointwiseBound {ℓ D : ℝ}
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
        |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v| ≤ D * ‖v‖)
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Differentiable ℝ f)
    (z : EuclideanSpace ℝ (Fin 3)) :
    ∑ j : Fin 3, ‖fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z
          (Submission.BoseGases.kcStdBasis j)‖ ^ 2
      ≤ 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            ∑ j : Fin 3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2
        + 6 * D ^ 2 * ‖f z‖ ^ 2 := by
  -- `χ_ℓ` is smooth (hence differentiable), so is its `ℂ`-valued version `y ↦ (χ_ℓ y : ℂ)`.
  have hχd : Differentiable ℝ (Submission.BoseGases.chiScale ℓ) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) := by
      unfold Submission.BoseGases.chiScale
      exact Submission.BoseGases.chi_contDiff.comp
        (ContinuousLinearMap.contDiff ((ℓ⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))))
    exact h1.differentiable (by norm_num)
  have hcd : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) :=
    Complex.differentiable_ofReal.comp hχd
  -- Chain rule: `d((χ_ℓ : ℂ))_z v = ((dχ_ℓ)_z v : ℂ)`.
  have hdchi : ∀ v : EuclideanSpace ℝ (Fin 3),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) z v
        = ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z v : ℝ) : ℂ) := by
    intro v
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) =>
          ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
        ((Complex.ofRealCLM).comp (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)) z :=
      (Complex.ofRealCLM.hasFDerivAt (x := Submission.BoseGases.chiScale ℓ z)).comp z
        (hχd z).hasFDerivAt
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- Product rule at `z`.
  have hmul : fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z
      = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) • fderiv ℝ f z
        + f z • fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) z := by
    show fderiv ℝ ((fun y : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) * f) z = _
    exact fderiv_mul hcd.differentiableAt (hf z)
  have hmul_v : ∀ v : EuclideanSpace ℝ (Fin 3),
      fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z v
        = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * (fderiv ℝ f z v)
          + f z * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z v : ℝ) : ℂ) := by
    intro v
    rw [hmul, add_apply, smul_apply, smul_apply, hdchi v, smul_eq_mul, smul_eq_mul]
  -- The triangle inequality for the two summands, in the exact shape the square bound needs.
  have hterm : ∀ j : Fin 3,
      ‖fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z
          (Submission.BoseGases.kcStdBasis j)‖
        ≤ Submission.BoseGases.chiScale ℓ z * ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖
          + ‖f z‖ * |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (Submission.BoseGases.kcStdBasis j)| := by
    intro j
    rw [hmul_v]
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ z)]
  -- `(a + b)² ≤ 2a² + 2b²`.
  have hsq : ∀ j : Fin 3,
      ‖fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z
          (Submission.BoseGases.kcStdBasis j)‖ ^ 2
        ≤ 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
            * ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2
          + 2 * ‖f z‖ ^ 2 * |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (Submission.BoseGases.kcStdBasis j)| ^ 2 := by
    intro j
    have h := hterm j
    have h2 := norm_nonneg (fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
    have h3 := abs_nonneg (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
      (Submission.BoseGases.kcStdBasis j))
    have h1 := norm_nonneg (fderiv ℝ (fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * f y) z
      (Submission.BoseGases.kcStdBasis j))
    have h4 := Submission.BoseGases.chiScale_nonneg ℓ z
    nlinarith [sq_nonneg (Submission.BoseGases.chiScale ℓ z
        * ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖
      - ‖f z‖ * |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (Submission.BoseGases.kcStdBasis j)|)]
  have hbasis_norm : ∀ j : Fin 3, ‖Submission.BoseGases.kcStdBasis j‖ = 1 := by
    intro j
    rw [Submission.BoseGases.kcStdBasis]
    simp
  have hBle : ∀ j : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (Submission.BoseGases.kcStdBasis j)| ≤ D := by
    intro j
    have h := hD z (Submission.BoseGases.kcStdBasis j)
    rwa [hbasis_norm j, mul_one] at h
  -- `Σ_j |∂_j χ_ℓ(z)|² ≤ 3 D²`.
  have hsumB : ∑ j : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (Submission.BoseGases.kcStdBasis j)| ^ 2
        ≤ 3 * D ^ 2 := by
    calc ∑ j : Fin 3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
            (Submission.BoseGases.kcStdBasis j)| ^ 2
        ≤ ∑ _j : Fin 3, D ^ 2 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact pow_le_pow_left₀ (abs_nonneg _) (hBle j) 2
      _ = 3 * D ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul, mul_comm]
  have hkey := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hsq j)
  -- Distribute the sums.
  have hAB : ∑ j : Fin 3, (2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
        * ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2
      + 2 * ‖f z‖ ^ 2 * |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (Submission.BoseGases.kcStdBasis j)| ^ 2)
      = 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
          * (∑ j : Fin 3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
        + 2 * ‖f z‖ ^ 2
          * (∑ j : Fin 3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (Submission.BoseGases.kcStdBasis j)| ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hAB] at hkey
  refine le_trans hkey ?_
  have hlast : 2 * ‖f z‖ ^ 2 * (∑ j : Fin 3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
        (Submission.BoseGases.kcStdBasis j)| ^ 2) ≤ 2 * ‖f z‖ ^ 2 * (3 * D ^ 2) :=
    mul_le_mul_of_nonneg_left hsumB (by positivity)
  nlinarith [hlast]

end Work.BoseBoxFock.PB3V2
