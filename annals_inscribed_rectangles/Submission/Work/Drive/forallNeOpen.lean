import Mathlib

/-!
# The set of parameters whose slice avoids a fixed compact set is open

A general topological brick used to turn the *single-point avoidance* of the transport `T6` (the cut
avoidance `Q 0 ∉ W '' unitBox 2`) into an *open* condition in the design's parameter `t`: if a family
`x ↦ f x` of maps of a compact parameter set `K` never meets the value `g x`, then the same holds in a
whole neighbourhood of `x`.  The content is that the projection `X × K → X` is a closed map for `K`
compact, so the *bad* set of parameters is closed.
-/

namespace Work.Drive

open Filter Set

/-- **The "no coincidence with `g` on the compact set `K`" condition is open.**  For a continuous
`f : X × K → Z` and a continuous `g : X → Z` into a Hausdorff space `Z`, with `K` compact, the set of
`x` such that `f x ·` avoids `g x` on `K` is open. -/
theorem isOpen_setOf_forall_ne_of_isCompact {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z] {K : Set Y} (hK : IsCompact K)
    {f : X → Y → Z} (hf : Continuous (Function.uncurry f)) {g : X → Z} (hg : Continuous g) :
    IsOpen {x : X | ∀ y ∈ K, f x y ≠ g x} := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {p : X × ↥K | f p.1 (p.2 : Y) = g p.1} :=
    isClosed_eq (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) (hg.comp continuous_fst)
  have hproper : IsProperMap (Prod.fst : X × ↥K → X) := isProperMap_fst_of_compactSpace
  have hproj : IsClosed (Prod.fst '' {p : X × ↥K | f p.1 (p.2 : Y) = g p.1}) :=
    hproper.isClosedMap _ hclosed
  have hset : {x : X | ∀ y ∈ K, f x y ≠ g x}
      = (Prod.fst '' {p : X × ↥K | f p.1 (p.2 : Y) = g p.1})ᶜ := by
    ext x
    constructor
    · rintro h ⟨p, hp, hpx⟩
      rw [← hpx] at h
      exact h (p.2 : Y) p.2.2 hp
    · intro h y hy heq
      exact h ⟨(x, ⟨y, hy⟩), heq, rfl⟩
  rw [hset]
  exact hproj.isOpen_compl

end Work.Drive

namespace Work.Drive

open Filter Set

/-- **The "no value of the slice lies in a fixed closed set on the compact `K`" condition is open.**
This is `Work.Drive.isOpen_setOf_forall_ne_of_isCompact` with the diagonal `{f = g}` replaced by an
arbitrary *closed* condition `C`: it is the shape needed to show that a *rank* condition (a closed
condition on the derivative, e.g. the general position `hgen` of
`Work.Drive.surjective_mfderiv_projMk`) holding at every point of a compact parameter box is an open
condition in an external parameter. -/
theorem isOpen_setOf_forall_notMem_of_isCompact {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {K : Set Y} (hK : IsCompact K)
    {f : X × Y → Z} (hf : Continuous f) {C : Set Z} (hC : IsClosed C) :
    IsOpen {x : X | ∀ y ∈ K, f (x, y) ∉ C} := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {p : X × ↥K | f (p.1, (p.2 : Y)) ∈ C} :=
    hC.preimage (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hproper : IsProperMap (Prod.fst : X × ↥K → X) := isProperMap_fst_of_compactSpace
  have hproj : IsClosed (Prod.fst '' {p : X × ↥K | f (p.1, (p.2 : Y)) ∈ C}) :=
    hproper.isClosedMap _ hclosed
  have hset : {x : X | ∀ y ∈ K, f (x, y) ∉ C}
      = (Prod.fst '' {p : X × ↥K | f (p.1, (p.2 : Y)) ∈ C})ᶜ := by
    ext x
    constructor
    · rintro h ⟨p, hp, hpx⟩
      rw [← hpx] at h
      exact h (p.2 : Y) p.2.2 hp
    · intro h y hy hyC
      exact h ⟨(x, ⟨y, hy⟩), hyC, rfl⟩
  rw [hset]
  exact hproj.isOpen_compl

end Work.Drive
