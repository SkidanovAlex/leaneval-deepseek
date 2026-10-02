import Mathlib
import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.man8Finiteness

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Finiteness of the middle rational cohomology of the boundary `∂W`

`Work.ThomBordism.BoundaryFinite` (the first named input of `BoundaryDualityExplicit`, the finiteness
of `H⁴(∂W;ℚ)`) in the form in which the assembly uses it:
`Work.ThomBordism.bdryRatCohFinite`.

The proof is the one announced in `boundaryDualityExplicit.lean`: the homeomorphism
`W.bdry : ∂W ≃ₜ Σ i, (F i).pt` identifies the middle cohomology of `∂W` with that of the finite
disjoint union of the pieces (`finiteDimensional_ratCohomology_of_iso`, from the fact that a
homeomorphism induces an isomorphism on singular cohomology, hence a `ℤ`-linear equivalence of
cohomology groups and a `ℚ`-linear equivalence after tensoring with `ℚ`), and the middle cohomology
of a finite disjoint union of `Man8`s is finite dimensional
(`Work.ThomBordism.instFiniteDimensionalRatCohSigma`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **A homeomorphism induces an isomorphism of singular cohomology.**  For any `R`, `n` and an
isomorphism `e : X ≅ Y` of topological spaces, the induced map
`Hⁿ(Y;R) ⟶ Hⁿ(X;R)` is an isomorphism. -/
theorem isIso_singularCohomologyMap_of_iso {R : Type} [CommRing R] {X Y : TopCat} (e : X ≅ Y)
    (n : ℕ) : IsIso (Work.Cohomology.singularCohomologyMap R X Y e.hom n) := by
  refine IsIso.mk ⟨Work.Cohomology.singularCohomologyMap R Y X e.inv n, ?_, ?_⟩
  · rw [← Work.Cohomology.singularCohomologyMap_comp, e.inv_hom_id,
      Work.Cohomology.singularCohomologyMap_id]
  · rw [← Work.Cohomology.singularCohomologyMap_comp, e.hom_inv_id,
      Work.Cohomology.singularCohomologyMap_id]

/-- **Finiteness of the rational middle cohomology transfers along a homeomorphism**: an isomorphism
`e : X ≅ Y` of topological spaces induces the `ℤ`-linear equivalence `Hⁿ(Y;ℤ) ≃ₗ[ℤ] Hⁿ(X;ℤ)` on
cohomology groups, which becomes a `ℚ`-linear equivalence after tensoring with `ℚ`. -/
theorem finiteDimensional_ratCohomology_of_iso {n : ℕ} {X Y : TopCat} (e : X ≅ Y)
    (h : FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology n (TopCat.toSSet.obj Y))) :
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology n (TopCat.toSSet.obj X)) := by
  haveI : IsIso (Work.Cohomology.singularCohomologyMap ℤ X Y e.hom n) :=
    isIso_singularCohomologyMap_of_iso e n
  let ψ : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj Y)).homology n ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj X)).homology n :=
    (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap ℤ X Y e.hom n)).toLinearEquiv
  haveI := h
  exact Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ) ψ)

/-- **The middle rational cohomology of the boundary of a null-bordism is finite dimensional.**  The
boundary of `W` is homeomorphic to the disjoint union `Σ i, (F i).pt` of the pieces (`W.bdry`), and
each piece is a compact closed `8`-manifold, whose middle cohomology is finite dimensional
(`Work.ThomBordism.instFiniteDimensionalRatCoh`); finiteness passes to a finite coproduct
(`Work.ThomBordism.instFiniteDimensionalRatCohSigma`) and back along the homeomorphism
(`finiteDimensional_ratCohomology_of_iso`). -/
theorem bdryRatCohFinite {ι : Type} [Fintype ι] (F : ι → Work.ThomBordism.Man8)
    (W : Work.ThomBordism.NullBordismFamily ι F) :
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))) := by
  let Z : TopCat := TopCat.of (Σ i : ι, (F i).pt)
  let e : TopCat.of (Work.ThomBordism.bdrySet W.W) ≅ Z := TopCat.isoOfHomeo W.bdry
  haveI hZ : FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj Z)) :=
    Work.ThomBordism.instFiniteDimensionalRatCohSigma (fun i => (F i).pt)
  exact finiteDimensional_ratCohomology_of_iso e hZ

end

end Work.ThomBordism
