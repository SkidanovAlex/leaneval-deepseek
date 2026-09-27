import Mathlib
import Submission.Work.Routing.mfderivSelf

/-!
# Immersion is preserved by a reparametrisation with non-zero derivative

The reparametrised germ chain needs: if `γ` is an immersion and `θ : ℝ → ℝ` has non-zero derivative at
`t`, then `γ ∘ θ` is an immersion at `t`.  This is the chain rule (`mfderiv_comp`) with the manifold
immersion of `γ` supplying the outer factor and
`Work.Routing.injective_mfderiv_of_deriv_ne_zero` the inner one.
-/

namespace Work.Routing

open scoped Manifold ContDiff

/-- **Immersion transport through a reparametrisation with non-zero derivative.** -/
theorem injective_mfderiv_comp_of_deriv_ne_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {γ : ℝ → M} {θ : ℝ → ℝ} {t : ℝ}
    (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    (himm : ∀ s : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) γ s))
    (hθd : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal θ t)
    (hθ : HasStrictDerivAt θ (deriv θ t) t) (hθ' : deriv θ t ≠ 0) :
    Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (γ ∘ θ) t) := by
  have hne : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  have hchain := mfderiv_comp (I := Work.Noncompact.CompressionTube.MCreal)
    (I' := Work.Noncompact.CompressionTube.MCreal)
    (I'' := Work.Noncompact.CompressionTube.MC n) t (g := γ) (f := θ)
    (hγ.contMDiffAt.mdifferentiableAt hne) hθd
  rw [hchain]
  exact (himm (θ t)).comp (injective_mfderiv_of_deriv_ne_zero hθ hθ')

end Work.Routing
