/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Neukirch–Uchida endgame at four independent universes

`Submission.neukirch_uchida` (`Challenge.lean`) is stated for `{K₁ K₂ K₁' K₂' : Type*}`, i.e. with
**four independent universe parameters**, whereas the single-universe capstone
`NK.EndgameRepair.challenge_of_repairedChapters` (the classical-input wall ⟹ the challenge) needs
all four fields in *one* universe `Type u`.  This module performs the assembly:

* lift the four fields to the common universe `w := max u₁ u₂ u₃ u₄` by `ULift`;
* transport the data `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` and the homeomorphism hypothesis to the
  lifted fields (`NK.UniverseUnify.transportGalEquiv`,
  `NK.UniverseUnify.isHomeomorph_transportGalEquiv`);
* apply the single-universe capstone to the **wall at the lifted types**
  `NK.EndgameRepair.ClassicalChaptersRepaired (ULift K₁) (ULift K₂) (ULift K₁') (ULift K₂')`;
* descend the `∃!` statement back along the conjugation bijection
  (`NK.UniverseUnify.existsUnique_ulift`).

The result `NK.UniverseUnify.neukirch_uchida_of_repairedChapters_lifted` has, verbatim, the
statement of `Challenge.lean`, with the four universes independent.

Nothing here says anything about the classical chapters themselves: they are the *hypothesis*, at
the lifted types.  See `README.md` for the universe audit of every field of the wall.
-/

import Submission.NK.UniverseUnify.Transport
import Submission.NK.EndgameRepair.All

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.UniverseUnify

open scoped Topology
open Submission.NeukirchUchida

universe u₁ u₂ u₃ u₄

section Main

variable {K₁ : Type u₁} [Field K₁] [NumberField K₁]
  {K₂ : Type u₂} [Field K₂] [NumberField K₂]
  {K₁' : Type u₃} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
  {K₂' : Type u₄} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']

/-- **The challenge, verbatim, from the repaired classical-input wall at the lifted types.**

This is the statement of `Challenge.lean` (equivalently, of `Submission.neukirch_uchida`) with four
independent universe parameters `u₁ u₂ u₃ u₄`; its conclusion is at the *original* universes.  Its
only hypothesis beyond the challenge's own data is the classical-input wall
`NK.EndgameRepair.ClassicalChaptersRepaired` evaluated at the four fields
`ULift.{max u₁ u₂ u₃ u₄} K₁`, …, all of which live in the single universe
`w := max u₁ (max u₂ (max u₃ u₄))` in which the single-universe capstone is stated. -/
theorem neukirch_uchida_of_repairedChapters_lifted
    (h : NK.EndgameRepair.ClassicalChaptersRepaired
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂'))
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have he' : IsHomeomorph (transportGalEquiv ϕ) := isHomeomorph_transportGalEquiv ϕ he
  have hc := NK.EndgameRepair.challenge_of_repairedChapters h (transportGalEquiv ϕ) he'
  exact (existsUnique_ulift_mp ϕ hc)

/-- The same, stated with `Submission.NeukirchUchida.MapsBase` (definitionally the range equality
used by the challenge). -/
theorem neukirch_uchida_of_repairedChapters_lifted_mapsBase
    (h : NK.EndgameRepair.ClassicalChaptersRepaired
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂'))
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_repairedChapters_lifted h ϕ he

/-- **The existence half** of the challenge at four independent universes, from the wall at the
lifted types. -/
theorem exists_sigma_of_repairedChapters_lifted
    (h : NK.EndgameRepair.ClassicalChaptersRepaired
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂'))
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, -⟩ := neukirch_uchida_of_repairedChapters_lifted h ϕ he
  exact ⟨σ, hσ⟩

/-- The `Submission`-level form of the assembly: the challenge of `Submission.lean` from the wall at
the lifted types. -/
theorem challenge_of_repairedChapters_lifted
    (h : NK.EndgameRepair.ClassicalChaptersRepaired
      (ULift.{max u₁ u₂ u₃ u₄, u₁} K₁) (ULift.{max u₁ u₂ u₃ u₄, u₂} K₂)
      (ULift.{max u₁ u₂ u₃ u₄, u₃} K₁') (ULift.{max u₁ u₂ u₃ u₄, u₄} K₂'))
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_repairedChapters_lifted h ϕ he

end Main

/-! ## The degenerate case: identical universes

When all four universes are equal, the lift is `ULift.{u,u}`, and the assembly still produces the
challenge at the original (single) universe.  This is the sanity check that the transport introduces
no loss: the hypothesis is the wall at a *different but isomorphic* pair of fields. -/

section Degenerate

universe u

variable {K₁ : Type u} [Field K₁] [NumberField K₁] {K₂ : Type u} [Field K₂] [NumberField K₂]
  {K₁' : Type u} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
  {K₂' : Type u} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']

/-- With a single universe for all four fields (`u₁ = u₂ = u₃ = u₄ = u`, so that
`max u u u u = u` and `ULift.{u,u} Kᵢ : Type u`), the assembly is the same statement with the wall
moved to the `ULift`-copies.  This is the sanity check that the transport loses nothing: the
hypothesis is the wall at a pair of fields isomorphic to the challenge's own, and the conclusion is
the challenge's conclusion. -/
theorem neukirch_uchida_of_repairedChapters_lifted_uniform
    (h : NK.EndgameRepair.ClassicalChaptersRepaired (ULift.{u,u} K₁) (ULift.{u,u} K₂)
      (ULift.{u,u} K₁') (ULift.{u,u} K₂'))
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_repairedChapters_lifted h ϕ he

end Degenerate

end NK.UniverseUnify
