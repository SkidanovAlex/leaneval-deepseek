import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_artinMap_of_abelian_local {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {E : Type} [Field E]
    [Algebra (Q.adicCompletion K) E] [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    ∃ Φ : (Q.adicCompletion K)ˣ →* (E ≃ₐ[Q.adicCompletion K] E),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = MonoidHom.range (Units.map
        (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K)) :=
  ArtinMap.exists_surjective_ker_norm_of_fundamental_class
    (fun {_} _ _ Q {_ _} _ _ _ _ _ _ _ _ _ _ =>
      ArtinMap.exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux (Q := Q))
    Q hcomm

end Commons.NumberTheory.NumberField.Completion
