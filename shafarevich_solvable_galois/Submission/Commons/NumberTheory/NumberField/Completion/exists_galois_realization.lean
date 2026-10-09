import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Realization of finite Galois local extensions by global ones

Let `K` be a number field, `Q` a finite place of `K` and `E` a finite Galois extension of the
local field `K_Q = Q.adicCompletion K`.  Then `E` is the completion `L_q` of a *Galois* extension
`L / K` of number fields at a place `q | Q`.

This is the Galois form of the "local fields are completions of global fields" statement: it is
obtained from `exists_galois_adicCompletion_of_finiteDimensional` (Krasner's lemma + Chinese
remainder, where the global field is the splitting field of a small perturbation of the minimal
polynomial of a primitive element) by first shrinking the extension `E` -- which lives in an
arbitrary universe -- to the universe of `K`, using that `E` is a finite-dimensional vector space
over `K_Q` and hence bijective to the small type `Fin n → K_Q`.
-/

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

universe u

theorem exists_galois_realization {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      IsGalois K L ∧
      (letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
       Nonempty (E ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) := by
  classical
  -- ## Step 1: `E` is a finite-dimensional vector space over the local field `K_Q`, so as a type
  -- it is in bijection with the small type `Fin n → K_Q`.
  haveI hfree : Module.Free (Q.adicCompletion K) E := Module.Free.of_divisionRing _ _
  let basisE : Module.Basis (Fin (Module.finrank (Q.adicCompletion K) E))
      (Q.adicCompletion K) E := Module.finBasis (Q.adicCompletion K) E
  haveI hsmall : Small.{u} E :=
    ⟨(Fin (Module.finrank (Q.adicCompletion K) E) → Q.adicCompletion K),
      ⟨(Module.Basis.equivFun basisE).toEquiv⟩⟩
  -- ## Step 2: shrink `E` into the universe of `K`, transporting the field and algebra structure
  let E' : Type u := Shrink.{u} E
  letI fieldE' : Field E' := Shrink.instField
  letI algE' : Algebra (Q.adicCompletion K) E' :=
    Shrink.instAlgebra (R := Q.adicCompletion K) (α := E)
  haveI finE' : FiniteDimensional (Q.adicCompletion K) E' :=
    Module.Finite.equiv (Shrink.algEquiv (Q.adicCompletion K) E).symm.toLinearEquiv
  haveI galE' : IsGalois (Q.adicCompletion K) E' :=
    IsGalois.of_algEquiv (Shrink.algEquiv (Q.adicCompletion K) E).symm
  -- ## Step 3: realize `E'` as the completion of a Galois extension of `K`
  obtain ⟨L, hLf, hLnf, hLa, q, hq, hgalL, ⟨e'⟩⟩ :=
    @exists_galois_adicCompletion_of_finiteDimensional.{u} K _ _ Q E' fieldE' algE' finE' galE'
  -- ## Step 4: transport back along the (algebra) equivalence `E ≃ₐ[K_Q] E'`
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  refine ⟨L, hLf, hLnf, hLa, q, hq, hgalL, ⟨?_⟩⟩
  exact (Shrink.algEquiv (Q.adicCompletion K) E).symm.trans e'

end Commons.NumberTheory.NumberField.Completion
