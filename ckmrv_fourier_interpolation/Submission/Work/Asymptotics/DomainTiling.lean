/-
# The six translates of `𝓕` that tile the `Γ(2)`-fundamental domain `𝒟`

CKMRV (Prop. 3.2(1), proof) writes the `Γ(2)`-fundamental domain `𝒟` as the union of the six
`SL(2,ℤ)`-translates of the standard fundamental domain `𝓕` cut out by

  `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)`.

This file only contains the definitions; the geometric facts (`Mp_smul_mem_closure_DomainD`,
`closure_DomainD_subset_iUnion_Mp`, `exists_Mp_nbdh`, `exists_neighbour_nbdh`) are requested
separately.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The six elements `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` of `SL(2,ℤ)` whose translates of the
standard fundamental domain `𝓕` tile the `Γ(2)`-fundamental domain `𝒟` (CKMRV, proof of
Prop. 3.2(1)). -/
def Mp : Fin 6 → SL(2,ℤ) := ![1, ModularGroup.T⁻¹, ModularGroup.S * ModularGroup.T * ModularGroup.S,
  ModularGroup.S, ModularGroup.S * ModularGroup.T⁻¹, ModularGroup.T * ModularGroup.S]

/-- The neighbours of `𝓕`: the edge pairings `S, T, T⁻¹` together with the generators of the
stabilisers of the four vertices of `𝓕̄`, up to sign. -/
def Neighbors : Set SL(2,ℤ) :=
  {γ | γ ∈ ({ModularGroup.S, ModularGroup.S * ModularGroup.T,
      (ModularGroup.S * ModularGroup.T)⁻¹, ModularGroup.S * ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S, ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹}
        : Set SL(2,ℤ)) ∨
    -γ ∈ ({ModularGroup.S, ModularGroup.S * ModularGroup.T,
      (ModularGroup.S * ModularGroup.T)⁻¹, ModularGroup.S * ModularGroup.T⁻¹,
      ModularGroup.T * ModularGroup.S, ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹}
        : Set SL(2,ℤ))}

end Work.Asymptotics
