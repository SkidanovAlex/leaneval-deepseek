/-
Copyright (c) 2025. All rights reserved.

# Embedding problems inside a fixed algebraic closure, and lifts of `G_ℚ`

An embedding problem `E : Submission.EmbeddingProblem ℚ` over `ℚ` has an *abstract* base field
`E.L` (finite Galois over `ℚ`).  Shafarevich's theorem, and the classical obstruction calculus
(`H²`-classes), are stated in the fixed algebraic closure: the base field is a *subfield* of `ℚ̄`
and a solution is a *larger* subfield.  This file provides the bridge.

* `Submission.EmbeddingProblem.ClosureModel E` — a *closure model* of `E`: an identification of
  `E.L` with an intermediate field `L ⊆ ℚ̄` (which is then automatically finite dimensional and
  Galois over `ℚ`).  Such a model always exists (`EmbeddingProblem.nonempty_closureModel`).

* `ClosureModel.HasSurjectiveLift M` — the *lifting* formulation of the embedding problem:
  a surjective `ψ : G_ℚ →* E.G` with open kernel whose composite with `E.π` agrees with the
  restriction map `G_ℚ →* Gal(M.L/ℚ)` under the identification `M.e`.

* `Work.AbsoluteGalois.HasSurjectiveLift E := ∃ M : E.ClosureModel, M.HasSurjectiveLift`.

The main theorem `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift` (in
`Submission/Work/AbsoluteGalois/Lift.lean`) says that a solution of the embedding problem and a
surjective lift of the projection are the same thing.  This is the form in which Shafarevich's
theorem ("every finite solvable group is a Galois group over `ℚ`") and the obstruction calculus
are classically stated: the obstruction to solving `E` is a class in `H²(Gal(E.L/ℚ), ker π)`
which vanishes if and only if `E.π` lifts to a *continuous* (equivalently, open-kernel) surjection
`G_ℚ →* E.G`.

## Main declarations

* `ClosureModel`, `ClosureModel.e`, `ClosureModel.finiteDimensional`, `ClosureModel.isGalois`;
* `ClosureModel.autCongr`, `ClosureModel.HasSurjectiveLift`,
  `ClosureModel.hasSurjectiveLift_iff_composite`;
* `EmbeddingProblem.nonempty_closureModel`;
* `Work.AbsoluteGalois.HasSurjectiveLift`, `hasSurjectiveLift_iff_hasSurjectiveLift_closure`.

## Implementation note

`HasSurjectiveLift` is phrased with `IsOpen ψ.ker` rather than with `Continuous ψ`, because
`E.G` carries no topology; the two are equivalent for the discrete topology
(`hasSurjectiveLift_iff_continuous`).
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.Realization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

namespace EmbeddingProblem

/-- A **closure model** of an embedding problem `E` over `ℚ`: an identification of the abstract
base field `E.L` with an intermediate field `L ⊆ ℚ̄ = AlgebraicClosure ℚ`.  The subfield `L` is
then automatically finite dimensional and Galois over `ℚ` (transported along `e` from `E.L`), and
those facts are recorded as instances. -/
structure ClosureModel (E : EmbeddingProblem ℚ) where
  /-- the image of the base field in `ℚ̄` -/
  L : IntermediateField ℚ (AlgebraicClosure ℚ)
  /-- `L` is finite over `ℚ` (transported from `E`) -/
  finiteDimensional : FiniteDimensional ℚ L
  /-- `L` is Galois over `ℚ` (transported from `E`) -/
  isGalois : IsGalois ℚ L
  /-- the identification of the base field with `L` -/
  e : E.L ≃ₐ[ℚ] L

attribute [instance] ClosureModel.finiteDimensional ClosureModel.isGalois

namespace ClosureModel

variable {E : EmbeddingProblem ℚ} (M : E.ClosureModel)

/-- The group isomorphism `Aut(E.L/ℚ) ≃* Aut(M.L/ℚ)` induced by the identification of the base
field with its image in `ℚ̄`.  It is `AlgEquiv.autCongr M.e`. -/
noncomputable def autCongr : (E.L ≃ₐ[ℚ] E.L) ≃* (↥M.L ≃ₐ[ℚ] ↥M.L) :=
  AlgEquiv.autCongr M.e

@[simp]
lemma autCongr_apply (u : E.L ≃ₐ[ℚ] E.L) :
    M.autCongr u = M.e.symm.trans (u.trans M.e) := rfl

/-- **The embedding problem as a lifting problem.**  `M.HasSurjectiveLift` holds if there is a
surjective homomorphism `ψ : G_ℚ →* E.G` with open kernel whose composite with the projection
`E.π : E.G →* Gal(E.L/ℚ)` is the restriction map `G_ℚ →* Gal(M.L/ℚ)`, transported along the
identification `M.e`:
`Aut(E.L/ℚ) ≅ Aut(M.L/ℚ)` identifies `E.π (ψ σ)` with `σ|_{M.L}`.

In classical language this says that `ψ` exhibits `G_ℚ` as an extension of
`Gal(E.L/ℚ) ≅ G_ℚ ⧸ ψ.ker` by `ker π`, compatibly with the given embedding problem, i.e. that
the *embedding problem* `E` has a solution which is a quotient of `G_ℚ`. -/
def HasSurjectiveLift : Prop :=
  ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
    IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ Function.Surjective ψ ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ,
        M.autCongr (E.π (ψ σ)) = Work.AbsoluteGalois.restrictHom M.L σ)

/-- The (equivalent) form of `HasSurjectiveLift` that literally says that the composite of `ψ` with
`E.π` is the restriction map. -/
theorem hasSurjectiveLift_iff_composite :
    M.HasSurjectiveLift ↔
      ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ Function.Surjective ψ ∧
          (∀ σ : Field.absoluteGaloisGroup ℚ,
            E.π (ψ σ) = M.autCongr.symm (Work.AbsoluteGalois.restrictHom M.L σ)) := by
  constructor
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact ⟨ψ, hopen, hsurj, fun σ => by
      have h := congrArg (fun u => M.autCongr.symm u) (hcomp σ)
      simpa only [MulEquiv.symm_apply_apply] using h⟩
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact ⟨ψ, hopen, hsurj, fun σ => by
      have h := congrArg (fun u => M.autCongr u) (hcomp σ)
      simpa only [MulEquiv.apply_symm_apply] using h⟩

end ClosureModel

/-- Every embedding problem over `ℚ` has a closure model: the base field `E.L` is algebraic over
`ℚ`, so it embeds into `ℚ̄` (`IsAlgClosed.lift`). -/
theorem nonempty_closureModel (E : EmbeddingProblem ℚ) : Nonempty E.ClosureModel := by
  haveI : FiniteDimensional ℚ E.L := E.finiteDimensional
  haveI : IsGalois ℚ E.L := E.isGalois
  obtain ⟨f, hf⟩ :
      ∃ f : E.L →ₐ[ℚ] AlgebraicClosure ℚ, True :=
    ⟨IsAlgClosed.lift (R := ℚ) (S := E.L) (M := AlgebraicClosure ℚ), trivial⟩
  haveI : FiniteDimensional ℚ ↥f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ ↥f.fieldRange := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField f)
  exact ⟨{ L := f.fieldRange
           finiteDimensional := inferInstance
           isGalois := inferInstance
           e := AlgEquiv.ofInjectiveField f }⟩

end EmbeddingProblem

end Submission

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-- `HasSurjectiveLift E` holds if the embedding problem `E` has a *surjective lift* in the
absolute Galois group: a surjection `ψ : G_ℚ →* E.G` with open kernel whose composite with `E.π`
is the restriction map to the base field (see `ClosureModel.HasSurjectiveLift`).

This is the classical "lifting formulation" of the embedding problem. -/
def HasSurjectiveLift (E : Submission.EmbeddingProblem ℚ) : Prop :=
  ∃ M : E.ClosureModel, M.HasSurjectiveLift

/-- `HasSurjectiveLift` holds as soon as it holds for one (hence any) closure model. -/
theorem hasSurjectiveLift_of_closureModel {E : Submission.EmbeddingProblem ℚ}
    (M : E.ClosureModel) (h : M.HasSurjectiveLift) : HasSurjectiveLift E :=
  ⟨M, h⟩

end

end Work.AbsoluteGalois
