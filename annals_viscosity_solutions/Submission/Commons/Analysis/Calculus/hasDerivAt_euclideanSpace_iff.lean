import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Calculus

open ContinuousLinearMap

/-- For a curve `f : ℝ → EuclideanSpace E (Fin N)` into a finite $L^2$ product of copies of a
normed space `E`, being differentiable at `t` with derivative `f'` is equivalent to each coordinate
being differentiable at `t` with the corresponding coordinate of `f'` as derivative. -/
lemma hasDerivAt_euclideanSpace_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    {f : ℝ → EuclideanSpace E (Fin N)} {f' : EuclideanSpace E (Fin N)} {t : ℝ} :
    HasDerivAt f f' t ↔ ∀ i : Fin N, HasDerivAt (fun s : ℝ => f s i) (f' i) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  simp_rw [hasDerivAt_iff_hasFDerivAt]
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  refine forall_congr' (fun i => ?_)
  rw [← hasFDerivWithinAt_univ]
  have key : (PiLp.proj 2 (fun _ : Fin N => E) i) ∘SL toSpanSingleton ℝ f'
      = toSpanSingleton ℝ (f' i) := by
    ext
    simp [PiLp.proj_apply]
  rw [key]

end Commons.Analysis.Calculus