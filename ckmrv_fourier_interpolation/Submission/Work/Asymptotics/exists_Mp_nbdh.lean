/-
# An `Mp`-invariant(-enough) neighbourhood of `closure 𝓕` inside a given neighbourhood of `closure 𝒟`

This file proves the elementary topological statement used by `Work.Asymptotics.Propagate`:
every open neighbourhood `O` of `closure 𝒟` contains the union of the six `Mp`-translates of some
open neighbourhood `U` of `closure 𝓕`.

The construction is canonical.  Since (CKMRV, proof of Prop. 3.2(1), formalised in
`Mp_smul_mem_closure_DomainD`) each of the six translates `Mp i • closure 𝓕` lies in
`closure 𝒟 ⊆ O`, the set

  `U := ⋂ i : Fin 6, (fun τ => Mp i • τ) ⁻¹' O`

is an intersection of six opens, is therefore open, contains `closure 𝓕`, and by construction
every `Mp i • τ` with `τ ∈ U` lies in `O`.  No compactness is needed, and no hypothesis beyond
`closure 𝒟 ⊆ O` is used.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The `Mp i`-image of `closure 𝓕` lies in `closure 𝒟`, hence in any open `O` containing the
latter; consequently `U := ⋂ i, (Mp i)⁻¹'(O)` is an open neighbourhood of `closure 𝓕` whose six
`Mp`-translates all remain in `O`.

This is the source of the "thickening" of `𝓕̄` used to propagate bounds from `𝓕` to `𝒟`: because
each `Mp i` is inverted separately in the definition of `U`, no compactness argument (which would
fail here, `closure 𝓕` being unbounded in `ℍ`) is required. -/
theorem exists_Mp_nbdh {O : Set UpperHalfPlane} (hO : IsOpen O)
    (hOD : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainF ⊆ U ∧
      (⋃ i : Fin 6, (fun τ : UpperHalfPlane => (Work.Asymptotics.Mp i) • τ) '' U) ⊆ O := by
  haveI : ContinuousSMul SL(2, ℤ) ℍ :=
    MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
      continuous_of_discreteTopology
  have hUopen : IsOpen (⋂ i : Fin 6, (fun τ : UpperHalfPlane => (Mp i) • τ) ⁻¹' O) :=
    isOpen_iInter_of_finite fun i => hO.preimage (continuous_const_smul (Mp i))
  refine ⟨⋂ i : Fin 6, (fun τ : UpperHalfPlane => (Mp i) • τ) ⁻¹' O, hUopen, ?_, ?_⟩
  · intro τ hτ
    exact Set.mem_iInter.mpr fun i => hOD (Mp_smul_mem_closure_DomainD i hτ)
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, τ, hτ, hx⟩ := hx
    rw [← hx]
    exact Set.mem_iInter.mp hτ i

end Work.Asymptotics
