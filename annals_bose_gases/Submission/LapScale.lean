import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Laplacian commutes with multiplying the argument by a scalar (homothety) and with
multiplying the function by a constant.  Generic in the finite-dimensional real
inner product space `E`.

    Δ (x ↦ a * f (c • x)) = (x ↦ a * c² * (Δ f) (c • x))      (a c : ℝ)

Prove the two lemmas below; they are used for the kinetic-energy bound of the
one-particle trial state in `Submission.OneParticle`.

Suggested approach for `laplacian_comp_homothetic`:
- use `laplacian_eq_iteratedFDeriv_stdOrthonormalBasis` on `f ∘ S` where
  `S : E →L[ℝ] E` is `c • ContinuousLinearMap.id`, and on `f`;
- rewrite each term with `ContinuousLinearMap.iteratedFDeriv_comp_right`
  (`S.iteratedFDeriv_comp_right hf x (by norm_num : (2 : ℕ) ≤ 2)`);
- the second derivative evaluated at `(c • v, c • v)` is `c² • ...`, using
  `ContinuousMultilinearMap.map_smul_univ (fun _ : Fin 2 => c)` and
  `simp`/`ring` to collapse the product over `Fin 2`;
- factor `c²` out of the finite sum with `Finset.smul_sum`.
-/

open MeasureTheory
open scoped ContDiff Topology InnerProductSpace Laplacian

namespace Submission

set_option autoImplicit false

namespace LapScale

/-- The Laplacian commutes with multiplication by a real constant. -/
lemma laplacian_const_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a : ℝ) :
    Δ (fun x : E => a * f x) = fun x : E => a * (Δ f) x := by
  funext x
  rw [show (fun x : E => a * f x) = a • f by rfl]
  rw [InnerProductSpace.laplacian_smul a hf.contDiffAt]
  rfl

/-- Scaling the argument by `c` scales the Laplacian by `c²`. -/
lemma laplacian_comp_homothetic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) :
    Δ (fun x : E => f (c • x)) = fun x : E => c ^ 2 * (Δ f) (c • x) := by
  let S : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have hS : ∀ y : E, S y = c • y := by
    intro y
    simp [S]
  funext x
  have hfun : (fun x : E => f (c • x)) = f ∘ S := by
    funext y
    simp [Function.comp_apply, hS]
  rw [hfun]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (f ∘ S)]
  simp only
  have hcomp : iteratedFDeriv ℝ 2 (f ∘ S) x =
      (iteratedFDeriv ℝ 2 f (S x)).compContinuousLinearMap (fun _ : Fin 2 => S) := by
    exact ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) (g := S) hf x (by norm_num)
  rw [hcomp]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [← hS x]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  change (∑ i,
        (iteratedFDeriv ℝ 2 f (S x))
          (fun j => S (![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] j))) =
      c ^ 2 * (∑ i,
        (iteratedFDeriv ℝ 2 f (S x)) ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i])
  simp [hS, ContinuousMultilinearMap.map_smul_univ]
  rw [Finset.mul_sum]

end LapScale

end Submission
