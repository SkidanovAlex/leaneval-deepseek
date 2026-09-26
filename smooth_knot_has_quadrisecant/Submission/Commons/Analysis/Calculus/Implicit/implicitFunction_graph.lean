import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Basic

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus.Implicit

/-- The implicit function theorem in graph form: if `f : ℝ × E₂ → F` is `C¹` at `u`,
vanishes at `u`, and its partial derivative with respect to the second coordinate at `u` is
invertible, then locally the zero set of `f` is the graph of a `C¹` function
`ψ : ℝ → E₂` over the first coordinate, with `ψ u.1 = u.2`. -/
theorem implicitFunction_graph
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : ℝ × E₂} {f : ℝ × E₂ → F}
    (cdf : ContDiffAt ℝ 1 f u) (h0 : f u = 0)
    (if₂ : (fderiv ℝ f u ∘L .inr ℝ ℝ E₂).IsInvertible) :
    ∃ ψ : ℝ → E₂,
      ψ u.1 = u.2 ∧
      (∃ V : Set ℝ, V ∈ 𝓝 u.1 ∧ ContDiffOn ℝ 1 ψ V ∧ (∀ x ∈ V, f (x, ψ x) = 0)) ∧
      (∀ᶠ v in 𝓝 u, f v = 0 → ψ v.1 = v.2) := by
  -- The implicit function provided by Mathlib's ContDiff version of the theorem.
  let ψ : ℝ → E₂ := cdf.implicitFunction (by norm_num) if₂
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- ψ u.1 = u.2
    exact cdf.implicitFunction_apply_self (by norm_num) if₂
  · -- ψ is C¹ on a neighbourhood of u.1 and solves f (x, ψ x) = 0 there
    have hca : ContDiffAt ℝ 1 ψ u.1 := by
      simpa [ψ] using (cdf.contDiffAt_implicitFunction (by norm_num) if₂)
    rcases hca.contDiffOn (m := (1)) (n := (1)) le_rfl (by intro h; norm_num at h) with
      ⟨W, hW, hcW⟩
    have hz : ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = 0 := by
      filter_upwards [cdf.eventually_apply_implicitFunction (by norm_num) if₂] with x hx
      simpa [ψ, h0] using hx
    rcases eventually_iff_exists_mem.mp hz with ⟨Z, hZ, hZ'⟩
    refine ⟨W ∩ Z, Filter.inter_mem hW hZ, ?_, ?_⟩
    · exact hcW.mono (by intro x hx; exact hx.1)
    · intro x hx
      exact hZ' x hx.2
  · -- local uniqueness: near u the zero set is exactly the graph
    filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction (by norm_num) if₂] with v hv
    intro hfv
    exact (hv.mp (by simpa [h0] using hfv))

end Commons.Analysis.Calculus.Implicit