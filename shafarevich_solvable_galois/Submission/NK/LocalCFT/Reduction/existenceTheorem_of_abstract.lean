import Mathlib
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The existence theorem in concrete form, from its abstract form

`NK.LocalCFT.ExistenceTheoremAbstract F` is the existence theorem of local class field theory
(Lubin–Tate) stated for *abstract* extensions `L/F`: every finite-index subgroup `M ≤ Fˣ` contains
`N_{L/F} Lˣ` for some finite abelian Galois extension `L/F`.  The form used by the reciprocity
datum, `NK.LocalCFT.ExistenceTheorem F F'`, asks the same but with `L` a finite abelian level of
the maximal abelian subextension `F^{ab} ⊆ F'`, where `F'` is a separable closure of `F`.

The present file bridges the two.  Given `L/F` finite abelian Galois, the separable closure `F'`
receives an `F`-embedding `φ : L →ₐ[F] F'` (`IsSepClosed.lift`, using that `L/F` is separable and
`F'` is separably closed).  Its image `φ.fieldRange` is a finite normal subextension of `F'/F` with
commutative Galois group, hence lies in the maximal abelian subextension
(`NK.LocalReciprocity.le_maxAbelianSubext_of_commutative`); restricting `φ` to `F^{ab}` gives
`ψ : L →ₐ[F] F^{ab}`, whose image `L'' ≤ F^{ab}` is the desired finite abelian level.  Nothing is
lost: `L ≃ₐ[F] L''`, so `normGroup_eq_of_algEquiv` identifies the norm groups.

## Main result

* `NK.LocalCFT.Reduction.existenceTheorem_of_abstract`.
-/

open scoped Classical

-- the instances below are anonymous existential hypotheses, introduced with `letI`/`haveI`;
-- the style linter's `let`/`have` suggestion does not apply to instance binders
set_option linter.style.haveILetI false

namespace NK.LocalCFT.Reduction

universe u v

/-- **The existence theorem of local class field theory, from its abstract form.**  If every
finite-index subgroup of `Fˣ` contains the norm group of a finite abelian Galois extension of `F`,
then every finite-index subgroup of `Fˣ` contains the norm group of a finite abelian level of the
maximal abelian subextension `F^{ab}` of a separable closure `F'` of `F`. -/
theorem existenceTheorem_of_abstract {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsSepClosure F F'] (h : NK.LocalCFT.ExistenceTheoremAbstract F) :
    NK.LocalCFT.ExistenceTheorem F F' := by
  intro M hM
  -- the abstract existence theorem: a finite abelian Galois extension `L/F` with small norm group
  obtain ⟨L, hLfield, hLalg, hLfd, hLgal, hLcomm, hLnorm⟩ := h M hM
  letI : Field L := hLfield
  letI : Algebra F L := hLalg
  haveI : FiniteDimensional F L := hLfd
  haveI : IsGalois F L := hLgal
  -- `L` is separable over `F`, and the separable closure `F'` is separably closed
  haveI : Algebra.IsSeparable F L := IsGalois.to_isSeparable
  haveI : IsSepClosed F' := IsSepClosure.sep_closed F
  -- Step 1: embed `L` into the separable closure `F'`
  let φ : L →ₐ[F] F' := IsSepClosed.lift
  let L' : IntermediateField F F' := φ.fieldRange
  have eL : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F L' :=
    FiniteDimensional.of_surjective eL.toLinearMap eL.surjective
  haveI : Normal F L' := Normal.of_algEquiv eL
  -- the Galois group of the image is commutative, being isomorphic to `Gal(L/F)`
  have hcommL' : ∀ σ τ : L' ≃ₐ[F] L', σ * τ = τ * σ := by
    intro σ τ
    refine (AlgEquiv.autCongr eL).symm.injective ?_
    rw [map_mul, map_mul]
    exact hLcomm _ _
  -- Step 2: an abelian extension lies in the maximal abelian subextension `F^{ab}`
  have hsub : L' ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative L' hcommL'
  let A : IntermediateField F F' := NK.LocalReciprocity.maxAbelianSubext F F'
  -- `φ` corestricts to `F^{ab}`, and the image of the corestriction is the level we want
  let ψ : L →ₐ[F] ↥A := φ.codRestrict A.toSubalgebra
    (fun x => hsub (show φ x ∈ L' from ⟨x, rfl⟩))
  let L'' : IntermediateField F ↥A := ψ.fieldRange
  have e'' : L ≃ₐ[F] L'' := AlgEquiv.ofInjectiveField ψ
  haveI : FiniteDimensional F L'' :=
    FiniteDimensional.of_surjective e''.toLinearMap e''.surjective
  haveI : Normal F L'' := Normal.of_algEquiv e''
  have hcommL'' : ∀ σ τ : L'' ≃ₐ[F] L'', σ * τ = τ * σ := by
    intro σ τ
    refine (AlgEquiv.autCongr e'').symm.injective ?_
    rw [map_mul, map_mul]
    exact hLcomm _ _
  refine ⟨L'', inferInstance, inferInstance, hcommL'', ?_⟩
  -- the norm group is unchanged by the identification `L ≃ₐ[F] L''`
  rw [← NK.LocalReciprocity.normGroup_eq_of_algEquiv e'']
  exact hLnorm

end NK.LocalCFT.Reduction
