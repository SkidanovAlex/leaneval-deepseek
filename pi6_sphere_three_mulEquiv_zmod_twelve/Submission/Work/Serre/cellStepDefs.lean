import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.RatHurewicz.AttachCells

/-!
# The pair map of a cell attachment, relative to the old space

For `Γ' = attachCells (D-2) Γ ι f` (a family of `D`-cells attached to `Γ`) and a continuous map
`q : X → Γ'`, this file defines the **map of pairs**

  `(X, q⁻¹(Γ)) ⟶ (Γ', Γ)`

induced by `q` on relative singular chains (where `Γ` sits inside `Γ'` as `Set.range attachIncl`).

This is the map whose being a quasi-isomorphism in the range `< D + f` (for a Serre fibration `q`
with homologically `f`-connected fibres) is the **cell step** of the cell-attachment argument for
the Serre exact sequence in the stable range: see the delegated lemma `Work.Serre.cellStep` and
`Submission/Work/Serre/STABLE_EXACT_PLAN.md`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The old part of the attached space, as a subset of it. -/
abbrev attachOld (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) : Set (Work.RatHurewicz.attachCells (D-2) Γ ι f) :=
  Set.range ((Work.RatHurewicz.attachIncl (D-2) Γ ι f : Γ → _))

/-- The restriction of `q` to the preimage of the old part, as a map of the relative parts. -/
def cellStepMapRel (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(q ⁻¹' attachOld D Γ ι f), ↥(attachOld D Γ ι f)) :=
  ⟨fun z => ⟨q z.1, z.2⟩, by
    exact Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun z => z.2)⟩

/-- **The map of pairs `(X, q⁻¹(Γ)) → (Γ', Γ)`** of a cell attachment. -/
noncomputable def cellStepAttachMap (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (X : Type) [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Cohomology.relChains (TopCat.of X) (q ⁻¹' attachOld D Γ ι f) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
        (attachOld D Γ ι f) :=
  Work.Cohomology.relChainsMapOf (TopCat.of X)
    (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (q ⁻¹' attachOld D Γ ι f) (attachOld D Γ ι f) (TopCat.ofHom q)
    (TopCat.ofHom (cellStepMapRel D Γ ι f X q))
    (by ext x; rfl)

end

end Work.Serre
