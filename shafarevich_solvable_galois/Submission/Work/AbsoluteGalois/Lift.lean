/-
Copyright (c) 2025. All rights reserved.

# The embedding problem as a lifting problem over `G_ℚ`

This is the main file of the `AbsoluteGalois` chapter: it proves that a field-theoretic solution of
an embedding problem `E : Submission.EmbeddingProblem ℚ` is the same thing as a *surjective lift*
of the projection `E.π : E.G ↠ Gal(E.L/ℚ)` to the absolute Galois group `G_ℚ`.

## Main declarations

* `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift` — **the main theorem**:
  `E.IsSolvable ↔ HasSurjectiveLift E`.
* `Work.AbsoluteGalois.hasSurjectiveLift_iff_closureModel` — `HasSurjectiveLift E` does not depend
  on the chosen `ClosureModel`.
* `Work.AbsoluteGalois.isSolvable_iff_closureModel_hasSurjectiveLift` — the same for any fixed
  closure model; the right form to use with a concrete subfield `L ⊆ ℚ̄`.
* `Work.AbsoluteGalois.isSolvable_iff_exists_continuous_surjective_lift` — the literal
  `Continuous` formulation of the main theorem (with `E.G` discrete).
* `Work.AbsoluteGalois.hasSurjectiveLift_of_injective` — sanity check: an embedding problem with
  injective projection (trivial kernel) has a lift.

## The classical form

This is the form in which Shafarevich's theorem is stated: given a finite Galois extension
`L/ℚ` with group `Gal(L/ℚ) ≅ G_ℚ/H` for an open normal subgroup `H`, and a finite group `E.G`
with a surjection `π : E.G ↠ Gal(L/ℚ)`, one asks whether `π` *lifts* across the continuous
surjection (the "restriction map") `G_ℚ ↠ Gal(L/ℚ)`:

```
        G_ℚ --ψ--> E.G
          \         |
   restrict \       | π
            \       v
             ---> Gal(L/ℚ)
```

The theorem says that such a lift exists (with open kernel, i.e. continuous) if and only if the
embedding problem `E` has a solution: a finite Galois `L'/ℚ` containing `L` with `L'/L` Galois
and `Gal(L'/ℚ) ≅ E.G` compatible with `π`.  In the obstruction calculus one writes the *extension
class* of `E` in `H²(Gal(L/ℚ), ker π)` (the kernel being a `Gal(L/ℚ)`-module by conjugation when
it is abelian) and the theorem says: `E` has a solution if and only if this class dies after
pullback along `G_ℚ ↠ Gal(L/ℚ)` — i.e. if and only if the class is in the kernel of the
restriction map `H²(Gal(L/ℚ), A) → H²(G_ℚ, A)`.  Choosing the solution field `L'` to be the fixed
field of `ψ.ker` makes `ψ` an isomorphism onto `Gal(L'/ℚ) ≅ G_ℚ/ψ.ker`, and Shafarevich's theorem
is proved by producing such `ψ` and then upgrading to a *surjection* `G_ℚ ↠ E.G` with the desired
fixed field.
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.Realization
import Submission.Work.AbsoluteGalois.ClosureModel
import Submission.Work.AbsoluteGalois.Embedding
import Submission.Work.AbsoluteGalois.isSolvable_of_hasSurjectiveLift
import Submission.Work.AbsoluteGalois.hasSurjectiveLift_of_isSolvable
import Submission.Work.AbsoluteGalois.closureModel_L_eq
import Submission.Work.AbsoluteGalois.hasSurjectiveLift_iff_of_L_eq
import Submission.Work.AbsoluteGalois.Obstruction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-- **Main theorem (the embedding problem as a lifting problem).**  For an embedding problem
`E` over `ℚ`, the following are equivalent:

* `E.IsSolvable`: there is a finite Galois `L'/ℚ` containing `E.L` with `L'/E.L` Galois and
  `E.G ≃* Gal(L'/ℚ)` compatible with `E.π`;
* `HasSurjectiveLift E`: there is a closure model `E.L ≅ L ⊆ ℚ̄` and a surjective
  `ψ : G_ℚ →* E.G` with open kernel whose composite with `E.π` is the restriction map
  `G_ℚ →* Gal(L/ℚ)`. -/
theorem isSolvable_iff_hasSurjectiveLift (E : Submission.EmbeddingProblem ℚ) :
    E.IsSolvable ↔ HasSurjectiveLift E :=
  ⟨hasSurjectiveLift_of_isSolvable E, isSolvable_of_hasSurjectiveLift E⟩

/-- `HasSurjectiveLift` does not depend on the closure model: if it holds for one model, it holds
for every model, and conversely. -/
theorem hasSurjectiveLift_iff_closureModel (E : Submission.EmbeddingProblem ℚ)
    (M : E.ClosureModel) : HasSurjectiveLift E ↔ M.HasSurjectiveLift := by
  constructor
  · rintro ⟨M', hM'⟩
    exact (hasSurjectiveLift_iff_of_L_eq E M' M (closureModel_L_eq E M' M)).mp hM'
  · exact fun h => ⟨M, h⟩

/-- The main theorem for a fixed closure model of `E`: solvability of `E` is equivalent to a
surjective open-kernel lift of `E.π` along the restriction map to the subfield `M.L ⊆ ℚ̄`. -/
theorem isSolvable_iff_closureModel_hasSurjectiveLift (E : Submission.EmbeddingProblem ℚ)
    (M : E.ClosureModel) : E.IsSolvable ↔ M.HasSurjectiveLift :=
  (isSolvable_iff_hasSurjectiveLift E).trans (hasSurjectiveLift_iff_closureModel E M)

/-- **The main theorem in the literal language of continuous lifts.**  If `E.G` carries the
discrete topology, then `E` is solvable if and only if the projection `E.π` lifts to a
*continuous* surjection `G_ℚ ↠ E.G` (with the fixed field of the kernel being the solution
field). -/
theorem isSolvable_iff_exists_continuous_surjective_lift (E : Submission.EmbeddingProblem ℚ)
    (M : E.ClosureModel) [TopologicalSpace E.G] [DiscreteTopology E.G] :
    E.IsSolvable ↔
      ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        Continuous ψ ∧ Function.Surjective ψ ∧
          (∀ σ : Field.absoluteGaloisGroup ℚ,
            M.autCongr (E.π (ψ σ)) = restrictHom M.L σ) :=
  (isSolvable_iff_closureModel_hasSurjectiveLift E M).trans
    M.hasSurjectiveLift_iff_continuous

/-- A surjective lift of `E.π` is in particular a *lift* along the restriction map to any closure
model: the fibre product `pullback E M` splits over `G_ℚ`. -/
theorem HasSurjectiveLift.exists_lift (E : Submission.EmbeddingProblem ℚ)
    (M : E.ClosureModel) (h : HasSurjectiveLift E) :
    ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
      M.pi.comp ψ = restrictHom M.L := by
  obtain ⟨ψ, -, -, hcomp⟩ := (hasSurjectiveLift_iff_closureModel E M).mp h
  exact ⟨ψ, MonoidHom.ext fun σ => by rw [MonoidHom.comp_apply, M.pi_apply]; exact hcomp σ⟩

/-- **Solvability implies the splitting of the fibre product.**  A solution of the embedding
problem gives a surjective lift, hence in particular a homomorphic section of the projection of
the fibre product `pullback E M` over `G_ℚ`.

The converse is *false* in general: if `E.π` itself splits, the extension class vanishes and a
plain lift (a section of the projection) exists, but the corresponding `ψ = σ ∘ ρ` is not
surjective when `ker E.π` is non-trivial; a *surjective* lift — i.e. a solution of `E` — need not
exist.  This is exactly why the classical obstruction calculus ("the pulled back class is
trivial") describes *plain* lifts, while solvability of `E` is the stronger requirement that
`E.G` be a quotient of `G_ℚ` fitting into the embedding problem. -/
theorem exists_pullback_section_of_isSolvable (E : Submission.EmbeddingProblem ℚ)
    (M : E.ClosureModel) (h : E.IsSolvable) :
    ∃ t : Field.absoluteGaloisGroup ℚ →* ↥M.pullback,
      M.pullbackFst.comp t = MonoidHom.id _ :=
  M.exists_lift_iff_exists_section.mp
    (HasSurjectiveLift.exists_lift E M ((isSolvable_iff_hasSurjectiveLift E).mp h))

/-- An embedding problem with injective projection (trivial kernel) has a surjective lift — the
sanity check that the lifting formulation is not too strong. -/
theorem hasSurjectiveLift_of_injective (E : Submission.EmbeddingProblem ℚ)
    (h : Function.Injective E.π) : HasSurjectiveLift E :=
  hasSurjectiveLift_of_isSolvable E (E.isSolvable_of_injective h)

end

end Work.AbsoluteGalois
