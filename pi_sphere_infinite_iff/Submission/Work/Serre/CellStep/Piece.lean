import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Model

set_option synthInstance.maxHeartbeats 400000


/-!
# The pieces of the cell cover and the per-cell map

The cover of `Γ' = attachCells n Γ ι f` used for the cell step is `{cellU f (3/4), cellV f 1}`: the
old part (the complement of the images of the closed balls of radius `3/4`) and the union of the
open cells.  The pieces of `cellV f 1` are the open cells `pieceSet α = cellInterior α`, with
relative part `pieceRelSet = cellShellImg f (3/4) 1` (the images of the shells
`{3/4 < ‖x‖ < 1}`).

`cellPieceMap` is the map of pairs `(X|_{P_α}, X|_{Q_α}) → (P_α, Q_α)` induced by a map
`q : X → Γ'`; the per-cell content of the cell step is that it is an isomorphism on homology in
degrees `< (n+2) + φ` when `q` is a Serre fibration with homologically `φ`-connected fibres.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

/-- The `α`-th piece of the cover `cellV f 1`: the open cell. -/
abbrev pieceSet (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) (α : ι) : Set (attachCells n Γ ι f) :=
  cellInterior n Γ ι f α

/-- The relative part of the pieces: the images of the shells `{3/4 < ‖x‖ < 1}`. -/
abbrev pieceRelSet (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) (α : ι) : Set (attachCells n Γ ι f) :=
  cellShellImg f (3/4) 1

/-- **The per-cell map of pairs** `(X|_{P_α}, X|_{Q_α}) → (P_α, Q_α)` induced by `q : X → Γ'`. -/
noncomputable def cellPieceMap (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(cellSphere n, Γ)) (α : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) :
    Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' pieceSet n Γ ι f α))
      {x : ↥(q ⁻¹' pieceSet n Γ ι f α) |
        (x : X) ∈ q ⁻¹' pieceRelSet n Γ ι f α} ⟶
    Work.Cohomology.relChains (TopCat.of ↥(pieceSet n Γ ι f α))
      {x : ↥(pieceSet n Γ ι f α) |
        (x : attachCells n Γ ι f) ∈ pieceRelSet n Γ ι f α} :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(q ⁻¹' pieceSet n Γ ι f α))
    (TopCat.of ↥(pieceSet n Γ ι f α))
    {x : ↥(q ⁻¹' pieceSet n Γ ι f α) | (x : X) ∈ q ⁻¹' pieceRelSet n Γ ι f α}
    {x : ↥(pieceSet n Γ ι f α) |
      (x : attachCells n Γ ι f) ∈ pieceRelSet n Γ ι f α}
    (TopCat.ofHom ⟨fun x => ⟨q x.1, x.2⟩, by
      exact Continuous.subtype_mk (q.continuous.comp continuous_subtype_val) (fun x => x.2)⟩)
    (TopCat.ofHom ⟨fun x => ⟨⟨q x.1.1, x.1.2⟩, x.2⟩, by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact q.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩)
    (by ext x; rfl)

end

end Work.Serre
