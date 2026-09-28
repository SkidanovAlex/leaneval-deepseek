import Mathlib

/-!
# Paths lying in a contractible subset are homotopic

If `T ⊆ X` is a contractible subset (with the subspace topology) and two paths `p`, `q : Path x y`
of `X` have all their values in `T`, then `p` and `q` are homotopic relative to their endpoints.
-/

open scoped Topology

namespace Work.StemsB

/-- Two paths whose images lie in a common contractible subset are homotopic relative to endpoints.

Proof: a contractible space is simply connected, so inside `↥T` the two lifted paths are homotopic;
pushing the homotopy forward along the inclusion `↥T → X` gives the result. -/
theorem paths_homotopic_of_contractible {X : Type*} [TopologicalSpace X] {T : Set X}
    [ContractibleSpace ↥T] {x y : X} {p q : Path x y} (hp : ∀ t, p t ∈ T) (hq : ∀ t, q t ∈ T) :
    p.Homotopic q := by
  have hxT : x ∈ T := by rw [← p.source]; exact hp 0
  have hyT : y ∈ T := by rw [← p.target]; exact hp 1
  let x' : ↥T := ⟨x, hxT⟩
  let y' : ↥T := ⟨y, hyT⟩
  let p' : Path x' y' :=
    { toFun := fun t => ⟨p t, hp t⟩, source' := Subtype.ext p.source, target' := Subtype.ext p.target }
  let q' : Path x' y' :=
    { toFun := fun t => ⟨q t, hq t⟩, source' := Subtype.ext q.source, target' := Subtype.ext q.target }
  have h : p'.Homotopic q' := SimplyConnectedSpace.paths_homotopic p' q'
  have key := h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(↥T, X))
  have e₁ : p'.map continuous_subtype_val = p := by ext t; rfl
  have e₂ : q'.map continuous_subtype_val = q := by ext t; rfl
  rwa [e₁, e₂] at key

end Work.StemsB
