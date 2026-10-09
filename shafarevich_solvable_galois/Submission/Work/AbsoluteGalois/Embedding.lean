/-
Copyright (c) 2025. All rights reserved.

# Embedding problems: closure models, continuity, and realizability

This file collects the interface of the closure-model formulation of embedding problems
(`Submission/Work/AbsoluteGalois/ClosureModel.lean`):

* `Submission.EmbeddingProblem.ClosureModel.toEmbeddingProblem` — a closure model makes the
  embedding problem into an `EmbeddingProblem` whose base field is an intermediate field of `ℚ̄`
  (the "closure variant" mentioned in the development notes; it is provided here as a bridge so
  that no separate variant structure is needed);
* `ClosureModel.hasSurjectiveLift_iff_continuous` — `HasSurjectiveLift` agrees with the
  literal "continuous surjective lift" formulation once `E.G` is discrete;
* `Work.AbsoluteGalois.RealizableOver.of_hasSurjectiveLift` — a surjective lift solves the
  embedding problem, hence realizes `E.G` over `ℚ` (via the absolute-Galois-group formulation of
  realizability).

## Main declarations

* `EmbeddingProblem.ClosureModel.toEmbeddingProblem`
* `ClosureModel.hasSurjectiveLift_iff_continuous`
* `Work.AbsoluteGalois.RealizableOver.of_hasSurjectiveLift`
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.Realization
import Submission.Work.AbsoluteGalois.ClosureModel
import Submission.Work.AbsoluteGalois.isOpen_ker_iff_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

namespace EmbeddingProblem

namespace ClosureModel

variable {E : EmbeddingProblem ℚ} (M : E.ClosureModel)

/-- A closure model of an embedding problem `E` presents `E` as an embedding problem whose base
field is an intermediate field `L ⊆ ℚ̄` (with projection `E.π` transported along
`M.autCongr : Aut(E.L/ℚ) ≃* Aut(M.L/ℚ)`).  This is the bridge between
`Submission.EmbeddingProblem` and the "closure variant" in which the base field is a subfield of
the fixed algebraic closure. -/
noncomputable def toEmbeddingProblem : EmbeddingProblem ℚ where
  L := ↥M.L
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := M.finiteDimensional
  isGalois := M.isGalois
  G := E.G
  group := E.group
  finite := E.finite
  π := M.autCongr.toMonoidHom.comp E.π
  surjective := M.autCongr.surjective.comp E.surjective

@[simp]
lemma toEmbeddingProblem_L : M.toEmbeddingProblem.L = ↥M.L := rfl

@[simp]
lemma toEmbeddingProblem_π :
    M.toEmbeddingProblem.π = M.autCongr.toMonoidHom.comp E.π := rfl

/-- **The lift formulation, in the literal `Continuous` language.**  If `E.G` is given the discrete
topology, then `HasSurjectiveLift` says exactly that there is a *continuous* surjective
`ψ : G_ℚ →* E.G` whose composite with `E.π` is the restriction map (up to `M.e`). -/
theorem hasSurjectiveLift_iff_continuous [TopologicalSpace E.G] [DiscreteTopology E.G] :
    M.HasSurjectiveLift ↔
      ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        Continuous ψ ∧ Function.Surjective ψ ∧
          (∀ σ : Field.absoluteGaloisGroup ℚ,
            M.autCongr (E.π (ψ σ)) = Work.AbsoluteGalois.restrictHom M.L σ) := by
  have key : ∀ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
      (IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) ↔ Continuous ψ) :=
    fun ψ => Work.AbsoluteGalois.isOpen_ker_iff_continuous ψ
  constructor
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact ⟨ψ, (key ψ).mp hopen, hsurj, hcomp⟩
  · rintro ⟨ψ, hcont, hsurj, hcomp⟩
    exact ⟨ψ, (key ψ).mpr hcont, hsurj, hcomp⟩

end ClosureModel

end EmbeddingProblem

end Submission

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-- A surjective open-kernel lift `G_ℚ ↠ E.G` of an embedding problem exhibits `E.G` as a
quotient of `G_ℚ` by an open subgroup. -/
theorem IsGaloisQuotient.of_hasSurjectiveLift (E : Submission.EmbeddingProblem ℚ)
    (h : HasSurjectiveLift E) : IsGaloisQuotient E.G := by
  obtain ⟨M, ψ, hopen, hsurj, -⟩ := h
  exact ⟨ψ, hopen, hsurj⟩

/-- A surjective open-kernel lift `G_ℚ ↠ E.G` of an embedding problem realizes `E.G` over `ℚ`.
(Compare `Submission.EmbeddingProblem.isSolvable_realizable`, which gives this from a
field-theoretic solution; here it is immediate from the `G_ℚ`-formulation.) -/
theorem RealizableOver.of_hasSurjectiveLift (E : Submission.EmbeddingProblem ℚ)
    (h : HasSurjectiveLift E) : Submission.RealizableOver ℚ E.G :=
  realizableOver_of_isGaloisQuotient E.G (IsGaloisQuotient.of_hasSurjectiveLift E h)

/-- A field-theoretic solution of an embedding problem realizes its group over `ℚ`, in the
language of continuous quotients of `G_ℚ`. -/
theorem IsGaloisQuotient.of_isSolvable (E : Submission.EmbeddingProblem ℚ) (h : E.IsSolvable) :
    IsGaloisQuotient E.G :=
  isGaloisQuotient_of_realizableOver E.G (E.isSolvable_realizable h)

end

end Work.AbsoluteGalois
