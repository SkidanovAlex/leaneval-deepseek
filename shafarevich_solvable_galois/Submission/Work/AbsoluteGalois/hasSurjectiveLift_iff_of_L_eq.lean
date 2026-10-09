/-
Copyright (c) 2025. All rights reserved.

# `HasSurjectiveLift` depends only on the subfield `L ⊆ ℚ̄` of the closure model

A `ClosureModel M` of an embedding problem `E : Submission.EmbeddingProblem ℚ` consists of an
intermediate field `M.L ⊆ ℚ̄` together with an identification `M.e : E.L ≃ₐ[ℚ] M.L`.  The
predicate `M.HasSurjectiveLift` asks for a surjective `ψ : G_ℚ →* E.G` with open kernel whose
composite with `E.π` is the restriction map to `M.L`, the latter being compared through
`M.autCongr : Gal(E.L/ℚ) ≃* Gal(M.L/ℚ)`, the conjugation by `M.e`.

Two closure models with the *same* subfield `M.L = M'.L ⊆ ℚ̄` therefore differ only in the choice
of the identification `e`, and any two such identifications differ by an automorphism of `E.L`.
The corresponding `autCongr`s differ by conjugation by an element `γ ∈ Gal(M.L/ℚ)`, and this does
not affect the existence of a lift: if `ψ` lifts `E.π` along `M.autCongr`, then the conjugate of
`ψ` by any preimage in `E.G` of `γ⁻¹` lifts `E.π` along `M'.autCongr` (and conversely).  The
result — the main theorem of this file — is that `HasSurjectiveLift` is insensitive to the choice
of the model once the subfield is fixed:

`Work.AbsoluteGalois.hasSurjectiveLift_iff_of_L_eq`.

It is the step that makes the closure-model formulation independent of the (arbitrary) choice of
identification of the base field with a subfield of `ℚ̄`
(`Work.AbsoluteGalois.hasSurjectiveLift_iff_closureModel`).

## Main declarations

* `Work.AbsoluteGalois.hasSurjectiveLift_iff_of_L_eq`.

## Implementation notes

The proof is a conjugation argument.  Writing `M.e` and `M'.e` for the two identifications of
`E.L` with the common subfield `L`, the two transport isomorphisms are related by
`AlgEquiv.autCongr M'.e u = γ * AlgEquiv.autCongr M.e u * γ⁻¹` for `γ = M.e.symm.trans M'.e`.
Since `E.π` is surjective, `γ⁻¹` has a preimage `g ∈ E.G`; conjugating any lift `ψ` of `E.π`
along `M.autCongr` by `g` produces a lift for `M'.autCongr` (and the same argument with the roles
of `e` and `e'` exchanged gives the converse).
-/
import Mathlib
import Submission.Work.AbsoluteGalois.ClosureModel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

set_option linter.style.haveILetI false

variable (E : Submission.EmbeddingProblem ℚ)

/-- **Transporting an automorphism of `A` along two isomorphisms to `B`.**

For `ℚ`-algebra isomorphisms `e e' : A ≃ₐ[ℚ] B`, the two identifications of `Aut(A)` with `Aut(B)`
obtained by conjugation differ by conjugation by `γ = e.symm.trans e' ∈ Aut(B)`:
`autCongr e' u = γ * autCongr e u * γ⁻¹`. -/
private lemma autCongr_conj {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e e' : A ≃ₐ[R] B) (u : A ≃ₐ[R] A) :
    AlgEquiv.autCongr e' u
      = (e.symm.trans e') * AlgEquiv.autCongr e u * (e.symm.trans e')⁻¹ := by
  ext x
  simp [AlgEquiv.autCongr_apply]

/-- **A lift can be transported from one identification of the base field to another.**

Let `L ⊆ ℚ̄` be an intermediate field with `e e' : E.L ≃ₐ[ℚ] L` two identifications of the base
field of `E`.  Given a surjective lift `ψ` of `E.π` with open kernel compatible with
`AlgEquiv.autCongr e`, the conjugate of `ψ` by a preimage in `E.G` of the element
`γ = e.symm.trans e'` is a surjective lift with open kernel compatible with
`AlgEquiv.autCongr e'`. -/
private theorem exists_lift_of_conj (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (fd : FiniteDimensional ℚ L) (gal : IsGalois ℚ L) (e e' : E.L ≃ₐ[ℚ] L)
    (ψ : Field.absoluteGaloisGroup ℚ →* E.G)
    (hopen : IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hsurj : Function.Surjective ψ)
    (hcomp : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ({ L := L, finiteDimensional := fd, isGalois := gal, e := e } : E.ClosureModel).autCongr
        (E.π (ψ σ)) = restrictHom L σ) :
    ∃ ψ' : Field.absoluteGaloisGroup ℚ →* E.G,
      IsOpen (ψ'.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ Function.Surjective ψ' ∧
        ∀ σ : Field.absoluteGaloisGroup ℚ,
          ({ L := L, finiteDimensional := fd, isGalois := gal, e := e' } : E.ClosureModel).autCongr
            (E.π (ψ' σ)) = restrictHom L σ := by
  haveI := fd
  haveI := gal
  -- the two transport isomorphisms differ by conjugation by `γ`
  let γ : L ≃ₐ[ℚ] L := e.symm.trans e'
  have hγ : ∀ u : E.L ≃ₐ[ℚ] E.L,
      ({ L := L, finiteDimensional := fd, isGalois := gal, e := e' } : E.ClosureModel).autCongr u
        = γ * ({ L := L, finiteDimensional := fd, isGalois := gal, e := e } :
            E.ClosureModel).autCongr u * γ⁻¹ :=
    fun u => autCongr_conj e e' u
  -- a preimage of `γ⁻¹` in `E.G` (possible since `E.π` is surjective)
  obtain ⟨g, hg⟩ := E.surjective
    (({ L := L, finiteDimensional := fd, isGalois := gal, e := e } :
      E.ClosureModel).autCongr.symm γ⁻¹)
  have hgval : ({ L := L, finiteDimensional := fd, isGalois := gal, e := e } :
      E.ClosureModel).autCongr (E.π g) = γ⁻¹ := by
    rw [hg, MulEquiv.apply_symm_apply]
  -- the conjugate lift
  refine ⟨(MulAut.conj g).toMonoidHom.comp ψ, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective ψ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective]
    exact hopen
  · exact (MulAut.conj g).surjective.comp hsurj
  · intro σ
    rw [MonoidHom.comp_apply]
    rw [show (MulAut.conj g).toMonoidHom (ψ σ) = g * ψ σ * g⁻¹ from
      MulAut.conj_apply g (ψ σ)]
    rw [hγ (E.π (g * ψ σ * g⁻¹))]
    rw [show E.π (g * ψ σ * g⁻¹) = E.π g * E.π (ψ σ) * (E.π g)⁻¹ by
      rw [map_mul, map_mul, map_inv]]
    rw [map_mul, map_mul, map_inv]
    rw [hgval, hcomp σ]
    group

/-- **`HasSurjectiveLift` is insensitive to the identification of the base field.**

For a fixed intermediate field `L ⊆ ℚ̄`, the property `HasSurjectiveLift` of the closure model
`(L, e)` does not depend on the choice of the identification `e : E.L ≃ₐ[ℚ] L`. -/
private theorem hasSurjectiveLift_congr (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (fd : FiniteDimensional ℚ L) (gal : IsGalois ℚ L) (e e' : E.L ≃ₐ[ℚ] L) :
    ({ L := L, finiteDimensional := fd, isGalois := gal, e := e } :
        E.ClosureModel).HasSurjectiveLift ↔
      ({ L := L, finiteDimensional := fd, isGalois := gal, e := e' } :
        E.ClosureModel).HasSurjectiveLift := by
  haveI := fd
  haveI := gal
  constructor
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact exists_lift_of_conj E L fd gal e e' ψ hopen hsurj hcomp
  · rintro ⟨ψ, hopen, hsurj, hcomp⟩
    exact exists_lift_of_conj E L fd gal e' e ψ hopen hsurj hcomp

/-- **`HasSurjectiveLift` only depends on the subfield `L ⊆ ℚ̄`.**

If two closure models `M`, `M'` of an embedding problem `E` over `ℚ` have the same underlying
subfield `M.L = M'.L` of `ℚ̄`, then `M.HasSurjectiveLift ↔ M'.HasSurjectiveLift`.  Indeed the two
models differ only by the identification of `E.L` with that subfield, and a lift for one
identification conjugates to a lift for the other. -/
theorem hasSurjectiveLift_iff_of_L_eq (E : Submission.EmbeddingProblem ℚ)
    (M M' : E.ClosureModel) (hL : M.L = M'.L) :
    M.HasSurjectiveLift ↔ M'.HasSurjectiveLift := by
  obtain ⟨L, fd, gal, e⟩ := M
  obtain ⟨L', fd', gal', e'⟩ := M'
  cases hL
  exact hasSurjectiveLift_congr E L fd gal e e'

end

end Work.AbsoluteGalois
