import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.exists_partialIso_toRationalMap_eq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-
# Finiteness of the exceptional set in codimension one

`exDiv φ = {x | coheight x = 1 ∧ ¬ IsIsoAt φ x}` (see `Submission/Work/Motivic/Defs.lean`), the
exceptional divisors of a birational map. This finiteness is essential because `excCount` uses
`Set.ncard`, which silently returns `0` on infinite sets.

## Proof

`Variety 𝕜 X` gives `LocallyOfFiniteType (X ↘ Spec 𝕜)` and `QuasiCompact (X ↘ Spec 𝕜)` (these
fields are *not* instances, so they have to be promoted by hand), whence `IsLocallyNoetherian X`,
`CompactSpace X`, so `IsNoetherian X` and finally `NoetherianSpace X`.

`F := {x | ¬ IsIsoAt φ x}` is closed, because `{x | IsIsoAt φ x}` is the union of the sources of
all partial isomorphisms representing `φ.hom`. `F` is proper: by
`Work.Motivic.exists_partialIso_toRationalMap_eq` the map `φ.hom` is represented by a partial
isomorphism `i`, whose source is dense, hence nonempty in the irreducible space `X`; a point of
`i.source` is a point at which `φ` is an isomorphism.

Finally `exDiv φ ⊆ {x ∈ F | coheight x = 1}`, and a closed proper subset of a Noetherian space
contains only finitely many points of coheight one
(`TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ`).
-/
theorem exDiv_finite_of_variety (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] (φ : X.BirationalMap Y) : (exDiv φ).Finite := by
  -- `X` is a Noetherian topological space.
  haveI : LocallyOfFiniteType (X ↘ Spec (.of 𝕜)) := Variety.locallyOfFiniteType
  haveI : QuasiCompact (X ↘ Spec (.of 𝕜)) := Variety.quasicompact
  haveI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of 𝕜))
  haveI : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  haveI : TopologicalSpace.NoetherianSpace X := IsNoetherian.noetherianSpace
  -- Some partial isomorphism represents `φ.hom`, and it is defined at some point of `X`.
  obtain ⟨i, hi⟩ := exists_partialIso_toRationalMap_eq φ
  obtain ⟨x₀, hx₀⟩ := i.dense_source.nonempty
  -- `{x | IsIsoAt φ x}` is open: it is a union of sources of representing partial isomorphisms.
  have hopen : IsOpen {x : X | IsIsoAt φ x} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨j, hy, hj⟩
    exact Filter.mem_of_superset (j.source.2.mem_nhds hy) fun z hz => ⟨j, hz, hj⟩
  -- `F := {x | ¬ IsIsoAt φ x}` is closed and proper.
  have hclosed : IsClosed {x : X | ¬ IsIsoAt φ x} := isClosed_compl_iff.mpr hopen
  have hproper : ({x : X | ¬ IsIsoAt φ x} : Set X) ≠ Set.univ := by
    intro h
    have hx : x₀ ∈ ({x : X | ¬ IsIsoAt φ x} : Set X) := by
      rw [h]
      exact Set.mem_univ x₀
    exact hx ⟨i, hx₀, hi⟩
  haveI : QuasiSober {x : X | ¬ IsIsoAt φ x} :=
    hclosed.isClosedEmbedding_subtypeVal.quasiSober
  haveI : TopologicalSpace.NoetherianSpace {x : X | ¬ IsIsoAt φ x} :=
    TopologicalSpace.NoetherianSpace.set _
  have hfin := TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    (X := X) (p := {x : X | ¬ IsIsoAt φ x}) (by rwa [hclosed.closure_eq])
  exact hfin.subset fun z hz => ⟨hz.2, hz.1⟩

end Work.Motivic
