import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.simplexBoundary_homologyOne
import Submission.Work.HomologyExtra.SimplexCircleCover
import Submission.Work.HomologyExtra.circleUChain_boundary
import Submission.Work.HomologyExtra.circleVChain_boundary
import Submission.Work.HomologyExtra.circleMV_computation
import Submission.Work.HomologyExtra.circlePsi_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fundamental class of `∂Δ²` generates `H₁(∂Δ²; ℤ)`

The singular chain complex of `∂Δ² = circleU ∪ circleV` splits, along the open cover of
`Submission/Work/HomologyExtra/SimplexCircleCover.lean`, into a Mayer–Vietoris short exact
sequence whose connecting map sends the fundamental class to the class of the `0`-chain
`[v₂] - [v₁]` in `H₀(circleU ∩ circleV)`.  The two vertices `v₁`, `v₂` lie in *different* path
components of the intersection (they are separated by the point where `w 1 = w 2`), so the
functional `circlePsi` which reads off the coefficient of the component of `v₂` satisfies
`cycleClass x₁ ≫ circlePsi = 𝟙`.  Hence

`simplexBoundaryClass 1 ≫ (mvδX ≫ circlePsi) = 𝟙 ℤ`,

so `simplexBoundaryClass 1` is an epimorphism: the fundamental class of `∂Δ²` generates
`H₁(∂Δ²; ℤ) ≅ ℤ`.  (The passage from the displayed identity to epimorphy uses that a
`ℤ`-linear endomorphism of `ℤ` with a right inverse is an isomorphism, and that
`H₁(∂Δ²) ≅ ℤ`.)

The main theorem of this file is `Work.HomologyExtra.simplexBoundaryClass_one_epi`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-- **A morphism `ℤ ⟶ M` with a retraction and with `M ≅ ℤ` is an epimorphism.**  In
`ModuleCat ℤ`, the composite `f ≫ g = 𝟙` exhibits the composite `ℤ → M ≅ ℤ → ℤ` as having a right
inverse; an epimorphism `ℤ ⟶ ℤ` is an isomorphism (`epi_self_zmod_isIso`), and the retraction of
an isomorphism is an isomorphism again. -/
theorem epi_of_comp_eq_id_of_iso_zmod {M : ModuleCat ℤ} (e : M ≅ Work.Homology.ZMod)
    (f : Work.Homology.ZMod ⟶ M) (g : M ⟶ Work.Homology.ZMod)
    (h : f ≫ g = 𝟙 Work.Homology.ZMod) : CategoryTheory.Epi f := by
  have hfg : (f ≫ e.hom) ≫ (e.inv ≫ g) = 𝟙 Work.Homology.ZMod := by
    rw [← Category.assoc (f ≫ e.hom) e.inv g, Category.assoc f e.hom e.inv,
      Iso.hom_inv_id, Category.comp_id, h]
  haveI hsplit : CategoryTheory.IsSplitEpi (e.inv ≫ g) :=
    CategoryTheory.IsSplitEpi.mk' ⟨f ≫ e.hom, hfg⟩
  haveI : IsIso (e.inv ≫ g) :=
    epi_self_zmod_isIso _ (inferInstance : CategoryTheory.Epi (e.inv ≫ g))
  haveI : IsIso ((f ≫ e.hom) ≫ (e.inv ≫ g)) := by rw [hfg]; infer_instance
  haveI hk : IsIso (f ≫ e.hom) := IsIso.of_isIso_comp_right (f ≫ e.hom) (e.inv ≫ g)
  have hf : f = (f ≫ e.hom) ≫ e.inv := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hf]
  exact epi_comp _ _

/-- **The fundamental class of `∂Δ²` generates `H₁(∂Δ²; ℤ)`.** -/
theorem simplexBoundaryClass_one_epi :
    CategoryTheory.Epi (Work.HomologyExtra.simplexBoundaryClass 1) := by
  obtain ⟨e⟩ := simplexBoundary_homologyOne
  refine epi_of_comp_eq_id_of_iso_zmod e (simplexBoundaryClass 1)
    ((Work.Cohomology.mvδX circleU circleV isOpen_circleU isOpen_circleV
      circleU_union_circleV 0) ≫ circlePsi) ?_
  rw [← Category.assoc, circleMV_computation circleUChain_boundary circleVChain_boundary,
    circlePsi_apply]

end

end Work.HomologyExtra
