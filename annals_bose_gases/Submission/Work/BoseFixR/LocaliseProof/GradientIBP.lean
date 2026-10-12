import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LocaliseProof.C1DirFTC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integration by parts for the Laplacian on `ℝ³` (`C¹`/`C²` version)

For `f : ℝ³ → ℝ` of class `C¹` with compact support and `g : ℝ³ → ℝ` of class `C²`,

    ∫ f · Δg = - ∫ ⟨∇f, ∇g⟩ ,

Green's first identity on the whole space (the boundary term is absent because `f` has compact
support).  Everything is done direction by direction in the coordinate basis `kcStdBasis`:
for each `k` the product rule applied to `x ↦ f x * ∂_k g x` gives

    ∂_k (f · ∂_k g) = (∂_k f) (∂_k g) + f ∂_k ∂_k g ,

and the integral of the left-hand side vanishes by the `C¹` directional fundamental theorem of
calculus `integral_fderiv_kcStdBasis_eq_zero`.  Summing over `k` and using the orthonormal-basis
expansions of `Δg` (`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`) and of the
inner product (`OrthonormalBasis.sum_inner_mul_inner`) gives the claim.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases

namespace Work.BoseFixR.LocaliseProof

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The standard orthonormal basis of `EuclideanSpace ℝ (Fin 3)` is the coordinate basis
`kcStdBasis`. -/
lemma basisFun_eq_kcStdBasis (k : Fin 3) :
    EuclideanSpace.basisFun (Fin 3) ℝ k = kcStdBasis k := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- Parseval in the coordinate basis: `⟨x, y⟩ = ∑ k ⟨x, e_k⟩ ⟨y, e_k⟩`. -/
lemma inner_eq_sum_kcStdBasis (x y : ℝ³) :
    inner ℝ x y = ∑ k : Fin 3, inner ℝ x (kcStdBasis k) * inner ℝ y (kcStdBasis k) := by
  rw [← OrthonormalBasis.sum_inner_mul_inner (EuclideanSpace.basisFun (Fin 3) ℝ) x y]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [basisFun_eq_kcStdBasis k, real_inner_comm (kcStdBasis k) y]

/-- Currying of the second derivative: differentiating `y ↦ fderiv g y v` gives the flipped
second derivative at `v`. -/
lemma fderiv_fderiv_apply_const {g : ℝ³ → ℝ} (hg : ContDiff ℝ 2 g) (v x : ℝ³) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x = (fderiv ℝ (fderiv ℝ g) x).flip v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ (fun _ : ℝ³ => v) x := differentiableAt_const v
  rw [fderiv_clm_apply hc hu]
  simp

/-- The Laplacian as the sum of the second coordinate derivatives in `kcStdBasis`. -/
lemma laplacian_eq_sum_dir {g : ℝ³ → ℝ} (hg : ContDiff ℝ 2 g) (x : ℝ³) :
    Laplacian.laplacian g x
      = ∑ k : Fin 3, fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := g)
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [basisFun_eq_kcStdBasis k, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← ContinuousLinearMap.flip_apply, ← fderiv_fderiv_apply_const hg (kcStdBasis k) x]

/-- **Green's first identity / integration by parts for the Laplacian on `ℝ³`.** -/
theorem GradientIBP {f g : ℝ³ → ℝ} (hf : ContDiff ℝ 1 f) (hfcs : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) :
    ∫ x, f x * Laplacian.laplacian g x
      = -(∫ x, inner ℝ (gradient f x) (gradient g x)) := by
  -- the per-direction identity
  have hk : ∀ k : Fin 3,
      (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k))
        = -(∫ x, fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k)) := by
    intro k
    have hPcd : ContDiff ℝ 1 (fun y : ℝ³ => fderiv ℝ g y (kcStdBasis k)) :=
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hGcd : ContDiff ℝ 1 (fun x : ℝ³ => f x * fderiv ℝ g x (kcStdBasis k)) :=
      hf.mul hPcd
    have hGcs : HasCompactSupport (fun x : ℝ³ => f x * fderiv ℝ g x (kcStdBasis k)) :=
      hfcs.mul_right
    have hFTC : (∫ x, fderiv ℝ (fun x : ℝ³ => f x * fderiv ℝ g x (kcStdBasis k)) x
        (kcStdBasis k)) = 0 :=
      integral_fderiv_kcStdBasis_eq_zero hGcd hGcs k
    have hpt : ∀ x : ℝ³,
        fderiv ℝ (fun x : ℝ³ => f x * fderiv ℝ g x (kcStdBasis k)) x (kcStdBasis k)
          = fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k)
            + f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k) := by
      intro x
      have hfun : (fun x : ℝ³ => f x * fderiv ℝ g x (kcStdBasis k))
          = f * (fun y : ℝ³ => fderiv ℝ g y (kcStdBasis k)) := by funext y; rfl
      rw [hfun, fderiv_mul (hf.differentiable (by norm_num) x) (hPcd.differentiable (by norm_num) x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have hintA : Integrable (fun x : ℝ³ => fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k)) :=
      Continuous.integrable_of_hasCompactSupport
        (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hPcd.continuous)
        ((hfcs.fderiv_apply ℝ (kcStdBasis k)).mul_right)
    have hintB : Integrable (fun x : ℝ³ =>
        f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k)) :=
      Continuous.integrable_of_hasCompactSupport
        (hf.continuous.mul ((hPcd.continuous_fderiv (by norm_num)).clm_apply continuous_const))
        hfcs.mul_right
    have hsum0 : (∫ x, (fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k)
        + f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k))) = 0 := by
      rw [← hFTC]
      exact integral_congr_ae (Eventually.of_forall (fun x => (hpt x).symm))
    rw [integral_add hintA hintB] at hsum0
    linarith
  -- assemble
  have hLHS : (∫ x, f x * Laplacian.laplacian g x)
      = ∑ k : Fin 3,
          ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k) := by
    have hpt1 : (fun x : ℝ³ => f x * Laplacian.laplacian g x)
        = fun x => f x * (∑ k : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k)) := by
      funext x
      rw [laplacian_eq_sum_dir hg x]
    have hpt2 : (fun x : ℝ³ => f x * (∑ k : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k)))
        = fun x => ∑ k : Fin 3,
            f x * fderiv ℝ (fun y => fderiv ℝ g y (kcStdBasis k)) x (kcStdBasis k) := by
      funext x
      rw [Finset.mul_sum]
    rw [hpt1, hpt2, integral_finsetSum]
    intro k _
    have hPcd : ContDiff ℝ 1 (fun y : ℝ³ => fderiv ℝ g y (kcStdBasis k)) :=
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact Continuous.integrable_of_hasCompactSupport
      (hf.continuous.mul ((hPcd.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      hfcs.mul_right
  have hRHS : (∫ x, inner ℝ (gradient f x) (gradient g x))
      = ∑ k : Fin 3,
          ∫ x, fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k) := by
    have hpt : (fun x : ℝ³ => inner ℝ (gradient f x) (gradient g x))
        = fun x => ∑ k : Fin 3,
            fderiv ℝ f x (kcStdBasis k) * fderiv ℝ g x (kcStdBasis k) := by
      funext x
      rw [inner_eq_sum_kcStdBasis]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [inner_gradient_left, inner_gradient_left]
    rw [hpt, integral_finsetSum]
    intro k _
    exact Continuous.integrable_of_hasCompactSupport
      (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        (((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous))
      ((hfcs.fderiv_apply ℝ (kcStdBasis k)).mul_right)
  rw [hLHS, hRHS, Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_neg_distrib]

end Work.BoseFixR.LocaliseProof
