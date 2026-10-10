import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- **The cyclic tower case of the local norm index theorem.**

Let `F = Q.adicCompletion K` be the completion of a number field at a finite place, let `M / F` be
a finite Galois extension and let `E / M` be a finite *cyclic* Galois extension.  Then the quotient
of the units of `M` by the norms from `E` has the cardinality of the Galois group `E ≃ₐ[M] E`.

The proof realizes `M` as the completion `q.adicCompletion L` of a number field `L` at a place
`q` lying over `Q` (commons lemma `exists_realization`), transports the `M`-algebra structure on
`E` along the resulting ring isomorphism, and invokes the cyclic theorem
`natCard_quotient_units_range_norm_eq_card_of_cyclic` for the resulting cyclic extension
`E / q.adicCompletion L`. -/
theorem natCard_quotient_units_range_norm_eq_card_of_cyclic_tower
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M E : Type*} [Field M] [Field E]
    [Algebra (Q.adicCompletion K) M] [Algebra M E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) M E]
    [FiniteDimensional (Q.adicCompletion K) M] [FiniteDimensional M E]
    [IsGalois (Q.adicCompletion K) M] [IsGalois M E]
    [IsCyclic (E ≃ₐ[M] E)] :
    Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) =
      Nat.card (E ≃ₐ[M] E) := by
  -- Realize `M` as the completion of a number field `L` at a place `q` over `Q`.
  obtain ⟨L, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ := exists_realization (Q := Q) (E := M)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- Transport the `M`-algebra structure on `E` along `e : M ≃ₐ[F] q.adicCompletion L`.
  letI : Algebra (q.adicCompletion L) E :=
    ((algebraMap M E).comp e.symm.toRingHom).toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) E).comp e.toRingHom = algebraMap M E := by
    ext x
    show algebraMap (q.adicCompletion L) E (e x) = algebraMap M E x
    rw [show algebraMap (q.adicCompletion L) E =
      (algebraMap M E).comp e.symm.toRingHom from rfl]
    simp [RingHom.comp_apply]
  haveI : FiniteDimensional (q.adicCompletion L) E :=
    finiteDimensional_transport e.toRingEquiv hhe
  haveI : IsGalois (q.adicCompletion L) E :=
    isGalois_transport e.toRingEquiv hhe
  haveI : IsCyclic (E ≃ₐ[q.adicCompletion L] E) :=
    (algEquiv_cast (E := E) hhe).isCyclic.mp inferInstance
  -- The cyclic theorem at `(L, q)`.
  have hcyclic :=
    natCard_quotient_units_range_norm_eq_card_of_cyclic (Q := q) (E := E)
  -- Transport the two sides back along `e`.
  have htransport : Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) =
      Nat.card ((q.adicCompletion L)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (q.adicCompletion L) : E →* q.adicCompletion L))) :=
    Nat.card_congr (quotEquiv_norm_of_cast (φ := e.toRingEquiv) hhe).toEquiv
  have hgal : Nat.card (E ≃ₐ[M] E) = Nat.card (E ≃ₐ[q.adicCompletion L] E) :=
    Nat.card_congr (algEquiv_cast (E := E) hhe).toEquiv
  rw [htransport, hcyclic, ← hgal]

end Commons.NumberTheory.NumberField.Completion
