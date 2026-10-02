import Mathlib
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.exists_smul_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `H⁰(X;ℚ)` of a path-connected space is one-dimensional

The rationalised cohomology of this workspace is `H^n(X;ℚ) := H^n(X;ℤ) ⊗[ℤ] ℚ`
(`Work.SignatureBordism.ratCohomology`).  For a path-connected space the integral degree-zero
cohomology is `ℤ` (`Work.Cohomology.singularCohomology_zero`), and base change along `ℤ → ℚ`
turns `ℤ` into `ℚ`; hence `H⁰(X;ℚ) = ℚ` and its `ℚ`-dimension (cardinal rank) is `1`.

This is the `j = 0` input of the degree-eight Borel computation: the rational cohomology
`H^j(G̃r_k(ℝ^{k+m});ℚ)` of the oriented Grassmannian is one-dimensional in degree `0`
(`Deg8.R`), the base of the induction on the rank of the tautological bundle.
-/

namespace Work.ThomBordism.Grassmann

open TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- **The degree-zero rational cohomology of a path-connected space has rank one.** -/
theorem deg8RankZero (X : Type) [TopologicalSpace X] [PathConnectedSpace X] : Module.rank ℚ (Work.SignatureBordism.ratCohomology 0 (TopCat.toSSet.obj (TopCat.of X))) = 1 := by
  -- `H⁰(X;ℤ) ≅ ℤ`
  obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero ℤ (TopCat.of X)
  have he : (Work.Cohomology.singularCohomology ℤ 0 (TopCat.of X)) ≃ₗ[ℤ] ℤ := e.toLinearEquiv
  -- `H⁰(X;ℚ) = H⁰(X;ℤ) ⊗[ℤ] ℚ` is the base change of `ℤ`
  have h1 : Module.rank ℚ (Work.SignatureBordism.ratCohomology 0 (TopCat.toSSet.obj (TopCat.of X)))
      = Module.rank ℚ (ℚ ⊗[ℤ] (Work.Cohomology.singularCohomology ℤ 0 (TopCat.of X))) := rfl
  have h2 : Module.rank ℚ (ℚ ⊗[ℤ] (Work.Cohomology.singularCohomology ℤ 0 (TopCat.of X)))
      = Module.rank ℚ (ℚ ⊗[ℤ] ℤ) := (he.baseChange ℤ ℚ _ _).rank_eq
  -- `ℚ ⊗[ℤ] ℤ ≅ ℚ`
  have h3 : Module.rank ℚ (ℚ ⊗[ℤ] ℤ) = 1 := by
    rw [(TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).rank_eq, Module.rank_self]
  rw [h1, h2, h3]

end Work.ThomBordism.Grassmann
