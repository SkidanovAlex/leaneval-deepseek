import Mathlib

/-!
# `H₀` of a set, and the components map

For a set `S` in a topological space, `H0 S` is the free abelian group on the connected components
of `S` (this is the degree-zero homology `H₀(S)`).  An inclusion `S ⊆ T` induces a map
`H0Map : H0 S →+ H0 T`, and for two sets `U, V` the **components map**

    `H0PairMap U V : H0 (U ∩ V) →+ H0 U × H0 V`

is the pair of the two restriction maps.

These are the definitions used by the Mayer–Vietoris input of the two-point Janiszewski theorem
(`Submission/Work/SphereJordan/mayerVietorisCover.lean`).
-/

namespace Work.SphereJordan

open Set

noncomputable section

/-- `H₀` of a set: the free abelian group on its connected components. -/
abbrev H0 {α : Type*} [TopologicalSpace α] (S : Set α) :=
  FreeAbelianGroup (ConnectedComponents ↥S)

/-- The induced map on connected components of an inclusion of sets. -/
def mapComponents {α : Type*} [TopologicalSpace α] {S T : Set α} (h : S ⊆ T) :
    ConnectedComponents ↥S → ConnectedComponents ↥T :=
  Quotient.lift (fun x => ConnectedComponents.mk ⟨x.1, h x.2⟩) (by
    intro a b hab
    rw [ConnectedComponents.coe_eq_coe']
    have hmem : a ∈ connectedComponent b := hab ▸ mem_connectedComponent
    have hcont : Continuous (fun x : ↥S => (⟨x.1, h x.2⟩ : ↥T)) := by fun_prop
    have himg : IsPreconnected ((fun x : ↥S => (⟨x.1, h x.2⟩ : ↥T)) '' connectedComponent b) :=
      isPreconnected_connectedComponent.image _ hcont.continuousOn
    exact himg.subset_connectedComponent ⟨b, mem_connectedComponent, rfl⟩ ⟨a, hmem, rfl⟩)

/-- The map `H₀(S) →+ H₀(T)` induced by an inclusion. -/
def H0Map {α : Type*} [TopologicalSpace α] {S T : Set α} (h : S ⊆ T) : H0 S →+ H0 T :=
  FreeAbelianGroup.lift (fun c => FreeAbelianGroup.of (mapComponents h c))

/-- The "components map" `H₀(U ∩ V) →+ H₀(U) × H₀(V)`. -/
def H0PairMap {α : Type*} [TopologicalSpace α] (U V : Set α) :
    H0 (U ∩ V) →+ H0 U × H0 V :=
  (H0Map inter_subset_left).prod (H0Map inter_subset_right)

/-- The class of a point of `S` as an element of `H₀(S)`. -/
def H0Class {α : Type*} [TopologicalSpace α] (S : Set α) (x : α) (hx : x ∈ S) : H0 S :=
  FreeAbelianGroup.of (ConnectedComponents.mk ⟨x, hx⟩)

end

end Work.SphereJordan
