import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.NUV2.ABHN.solvable_algEquiv_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.LC

set_option autoImplicit false

/-- **The local Galois group of an adic completion of a number field is solvable.**

Every finite Galois extension `E` of the local field `K_Q = Q.adicCompletion K` has solvable
Galois group.  By `exists_galois_realization` (Krasner's lemma) `E` is the completion `L_q` of a
finite Galois extension `L / K` of number fields at a place `q | Q`, and for those the solvability
of `Gal(L_q / K_Q)` is `NK.NUV2.ABHN.solvable_algEquiv_adicCompletion` (the ramification
filtration argument: the derived series refines the descending central filtration
`G ⊃ Gs 0 ⊃ Gs 1 ⊃ ⋯` with `⨅ₙ Gs n = ⊥`). -/
theorem isSolvable_algEquiv_local {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E] :
    Group.IsSolvable (E ≃ₐ[Q.adicCompletion K] E) := by
  classical
  -- `E` is realized as the completion of a finite Galois extension `L / K` of number fields.
  obtain ⟨L, hLf, hLnf, hLa, q, hq, hgalL, hne⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_realization (E := E) Q
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨e⟩ := hne
  -- the local Galois group of `L_q / K_Q` is solvable
  have hsol : Group.IsSolvable
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    NK.NUV2.ABHN.solvable_algEquiv_adicCompletion Q q hq
  haveI : Group.IsSolvable
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := hsol
  -- conjugation by `e` transports solvability to `Gal(E / K_Q)`
  let φ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →*
      (E ≃ₐ[Q.adicCompletion K] E) :=
    { toFun := fun τ => e.trans (τ.trans e.symm)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro σ τ
        ext x
        simp [AlgEquiv.mul_apply] }
  have hsurj : Function.Surjective φ := by
    intro σ
    refine ⟨e.symm.trans (σ.trans e), ?_⟩
    change e.trans ((e.symm.trans (σ.trans e)).trans e.symm) = σ
    ext x
    simp [AlgEquiv.trans_apply]
  exact Group.isSolvable_of_surjective (f := φ) hsurj

end NK.NUV2.LC
