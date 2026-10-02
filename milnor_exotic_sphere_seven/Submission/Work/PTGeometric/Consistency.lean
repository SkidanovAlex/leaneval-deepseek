import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.ThomBordism.Transversality.Preimage.exists_preimage_structure

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: consistency of the local preimage theorem with the chapter's

The local preimage theorem (`LocalPreimageTheorem`, `Defs.lean`) generalises the chapter's
`Work.ThomBordism.Transversality.Preimage.exists_preimage_structure`: the chapter's theorem is the
special case in which the target `X₀` is a `CoreTarget`, i.e. carries **one global** defining function
`Φ : E → ℝ^k` of the core (equivalently: in which the normal bundle of the core is trivial).  This file
records that reduction, which shows both

* that the local statement is *implied by* a theorem that is already proved in the workspace whenever
  the global defining function exists — so it is not a vacuous weakening, and
* that the only new content of the local statement is precisely the impossibility of a global defining
  function (the non-triviality of the universal bundle `γ_k`, see `Defs.lean`).

## Main results

* `Work.PTGeometric.isCoreTransverse_ofCoreTarget_iff`
* `Work.PTGeometric.boundaryTransverse_of_coreTransverseOnBoundary`
* `Work.PTGeometric.exists_preimage_structure_of_coreTarget`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.Transversality

/-- **Transversality to the core of a `CoreTarget` *is* transversality to the core of the
corresponding `LocalCoreTarget`** (one index, the global `Φ`). -/
theorem isCoreTransverse_ofCoreTarget_iff {k : ℕ} (X₀ : CoreTarget ((8 + k) + 1) k)
    {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (F : M → X₀.E) :
    IsCoreTransverse (LocalCoreTarget.ofCoreTarget X₀) I F ↔ IsTransverse X₀ I F := by
  constructor
  · intro h x _ hx
    obtain ⟨i, -, hsub⟩ := h x hx
    exact hsub
  · intro h x hx
    refine ⟨PUnit.unit, mem_univ _, ?_⟩
    exact h x (mem_univ x) hx

/-- **Boundary transversality for the corresponding `LocalCoreTarget` gives the chapter's
`BoundaryTransverse`.** -/
theorem boundaryTransverse_of_coreTransverseOnBoundary {k : ℕ}
    (X₀ : CoreTarget ((8 + k) + 1) k) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X₀.E)
    (h : IsCoreTransverseOnBoundary (LocalCoreTarget.ofCoreTarget X₀) F) :
    BoundaryTransverse k X₀ F := by
  rw [boundaryTransverse_iff]
  intro x hx hcore
  obtain ⟨i, -, -, hsub⟩ := h x hx hcore
  exact hsub

/-- **The local preimage theorem for the chapter's `CoreTarget`s**: for a `CoreTarget` `X₀` (a
target with a global defining function of its core) the local preimage theorem holds — it is the
chapter's proved `Preimage.exists_preimage_structure`, with the two notions of transversality
identified (`isCoreTransverse_ofCoreTarget_iff`,
`boundaryTransverse_of_coreTransverseOnBoundary`).

Consequently `LocalPreimageTheorem` is a *bona fide* generalisation: its only new content over the
proved global theorem is the case in which no global defining function exists (the universal bundle
`γ_k`). -/
theorem exists_preimage_structure_of_coreTarget {k : ℕ} (X₀ : CoreTarget ((8 + k) + 1) k)
    (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] (F : M → X₀.E)
    (hF : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 ((8 + k) + 1)) ∞ F)
    (htr : IsCoreTransverse (LocalCoreTarget.ofCoreTarget X₀) (𝓡∂ ((8 + k) + 1)) F)
    (hbnd : IsCoreTransverseOnBoundary (LocalCoreTarget.ofCoreTarget X₀) F) :
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (EuclideanHalfSpace 9) W)
      (_ : IsManifold (𝓡∂ 9) ∞ W) (_ : CompactSpace W) (_ : T2Space W)
      (e : W ≃ₜ ↥(F ⁻¹' X₀.core)),
      (∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔
        (e w : M) ∈ endPreimage (𝓡∂ ((8 + k) + 1)) F) :=
  Preimage.exists_preimage_structure X₀ M F hF
    ((isCoreTransverse_ofCoreTarget_iff X₀ (𝓡∂ ((8 + k) + 1)) F).mp htr)
    (boundaryTransverse_iff.mp
      (boundaryTransverse_of_coreTransverseOnBoundary X₀ F hbnd))

end

end Work.PTGeometric
