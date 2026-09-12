import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- A function with a nonzero strict derivative at a point is injective on some
neighbourhood of that point. -/
theorem injOn_nhds_of_hasStrictDerivAt {f : ℂ → ℂ} {f' a : ℂ} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0) :
    ∃ D : Set ℂ, D ∈ nhds a ∧ Set.InjOn f D := by
  -- a local inverse to `f` near `a`, provided by the inverse function theorem
  let g : ℂ → ℂ := hf.localInverse f f' a hf'
  -- `g ∘ f` is the identity on a neighbourhood of `a`
  have h : ∀ᶠ x in 𝓝 a, g (f x) = x := hf.eventually_left_inverse hf'
  refine ⟨{x | g (f x) = x}, h, ?_⟩
  intro x hx y hy hxy
  have hg : g (f x) = g (f y) := by rw [hxy]
  rw [hx, hy] at hg
  exact hg

end Commons.Analysis.Calculus