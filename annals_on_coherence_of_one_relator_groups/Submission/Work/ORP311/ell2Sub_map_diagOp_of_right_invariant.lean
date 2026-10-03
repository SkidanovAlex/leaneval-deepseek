import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.Ell2SubAux

namespace Work.ORP311

open Work.ORVonNeumann

/-- `diagOp n k` preserves `ell2Sub n Z` when `Z` is right-invariant under multiplication by
`k⁻¹`, i.e. `g ∈ Z → g * k⁻¹ ∈ Z`.

`diagOp n k` acts coordinatewise by the right regular operator `ρ_k`, and on basis vectors
`ρ_k (δ_g) = δ_{g * k⁻¹}`; the invariance hypothesis is exactly what makes the image of the
generators of `ell2Sub n Z` land back in `ell2Sub n Z`. -/
theorem ell2Sub_map_diagOp_of_right_invariant {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} {Z : Set G} {k : G} (hZ : ∀ g ∈ Z, g * k⁻¹ ∈ Z) : ∀ x ∈ Work.ORP311.ell2Sub (G := G) n Z, Work.ORVonNeumann.Rep.diagOp (G := G) n k x ∈ Work.ORP311.ell2Sub (G := G) n Z := by
  refine ell2Sub_map_subset_of_generators (G := G) n (Rep.diagOp (G := G) n k) Z
    (ell2Sub (G := G) n Z) ?_ ?_
  · unfold ell2Sub
    exact Submodule.isClosed_topologicalClosure _
  · intro g hg i
    have h1 : Rep.diagOp (G := G) n k (Rep.hinclude (G := G) n i (Rep.deltaG g))
        = Rep.hinclude (G := G) n i (Rep.deltaG (g * k⁻¹)) := by
      rw [← ContinuousLinearMap.comp_apply, Rep.diagOp_hinclude (G := G) n k i,
        ContinuousLinearMap.comp_apply, Rep.rightRegOp_deltaG (G := G) k g]
    rw [h1]
    unfold ell2Sub
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨g * k⁻¹, hZ g hg, i, rfl⟩)

end Work.ORP311
