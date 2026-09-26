import Mathlib

/-!
# Descending a continuous map along a continuous surjection from a compact space

If `f : X → Y` is a continuous surjection with `X` compact and `Y` Hausdorff, then `f` is a
closed map, hence a quotient map (`IsClosedMap.isQuotientMap`).  Consequently any continuous
map `g : X → Z` which is constant on the fibres of `f` descends to a continuous map
`g' : Y → Z` with `g' ∘ f = g`; this is `Topology.IsQuotientMap.lift`.
-/

namespace Work.InnermostDisk

theorem descend_continuousMap {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (hsurj : Function.Surjective f) {g : X → Z} (hg : Continuous g)
    (hfib : ∀ x y, f x = f y → g x = g y) :
    ∃ g' : Y → Z, Continuous g' ∧ ∀ x, g' (f x) = g x := by
  -- A closed subset of a compact space is compact, its image under `f` is compact, and a
  -- compact subset of a Hausdorff space is closed: thus `f` is a closed map.
  have hcl : IsClosedMap f := fun s hs => (hs.isCompact.image hf).isClosed
  -- A continuous closed surjection is a quotient map.
  have hq : Topology.IsQuotientMap f := hcl.isQuotientMap hf hsurj
  let F : C(X, Y) := ⟨f, hf⟩
  have hq' : Topology.IsQuotientMap F := hq
  -- Descend `g` through the quotient map.
  let G : C(Y, Z) :=
    Topology.IsQuotientMap.lift (f := F) hq' ⟨g, hg⟩ fun a b hab => hfib a b hab
  refine ⟨fun y => G y, G.continuous, fun x => ?_⟩
  have hcomp := DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp (f := F) hq' ⟨g, hg⟩ fun a b hab => hfib a b hab) x
  simpa [F, ContinuousMap.comp_apply] using hcomp

end Work.InnermostDisk
