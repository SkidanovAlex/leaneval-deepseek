import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Order.CompletePartialOrder

/-!
# Continuity of the Laplacian of a `C²` function on an open set

If `s` is open and `u : E → ℝ` is `C²` on `s` (in the sense of `ContDiffOn ℝ 2 u s`),
then the Laplacian `x ↦ Laplacian.laplacian u x` is continuous on `s`.

The proof writes the Laplacian in terms of the standard orthonormal basis,
`laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`, expressing every summand as
`fderiv ℝ (fderiv ℝ u) x a a` for a fixed vector `a`, which is continuous on `s`
by `ContDiffOn.continuousOn_fderiv_of_isOpen` composed with the continuous evaluation
map of continuous linear maps.
-/

open Laplacian

namespace Commons.Analysis.Calculus.Laplacian

theorem continuousOn_laplacian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) : ContinuousOn (fun x => Laplacian.laplacian u x) s := by
  -- `fderiv ℝ u` is `C¹` on the open set `s`
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ u) s := hu.fderiv_of_isOpen hs (by norm_num)
  -- hence its derivative `x ↦ fderiv ℝ (fderiv ℝ u) x` is continuous on `s`
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) s :=
    h1.continuousOn_fderiv_of_isOpen hs (by norm_num)
  -- each evaluation `L ↦ L a a` is continuous, so every summand below is continuous on `s`
  have h3 : ∀ i, ContinuousOn (fun x => fderiv ℝ (fderiv ℝ u) x
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) s := by
    intro i
    exact (show Continuous (fun L : E →L[ℝ] (E →L[ℝ] ℝ) =>
      L ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) by fun_prop).comp_continuousOn h2
  -- compute the Laplacian using the standard orthonormal basis
  have key : (fun x => Laplacian.laplacian u x) = fun x => ∑ i, fderiv ℝ (fderiv ℝ u) x
      ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i) := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_two_apply]
  rw [key]
  exact continuousOn_finsetSum _ (fun i _ => h3 i)

end Commons.Analysis.Calculus.Laplacian