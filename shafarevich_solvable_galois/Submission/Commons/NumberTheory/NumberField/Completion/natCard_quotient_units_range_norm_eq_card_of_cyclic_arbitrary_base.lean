import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- **The cyclic case of the local norm index theorem, for an arbitrary base field.**

Let `F = Q.adicCompletion K` be the completion of a number field at a finite place, let `B / F`
be an arbitrary finite extension field (not assumed Galois over `F`) and let `B₁ / B` be a finite
*cyclic* Galois extension.  Then the quotient of the units of `B` by the norms from `B₁` has the
cardinality of the Galois group `B₁ ≃ₐ[B] B₁`.

The proof realizes the (arbitrary) finite extension `B / F` as the completion `q.adicCompletion L`
of a number field `L` at a place `q` lying over `Q`
(`Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional`),
transports the `B`-algebra structure on `B₁` to a `q.adicCompletion L`-algebra structure along the
resulting `F`-algebra isomorphism, and then invokes the cyclic theorem
`natCard_quotient_units_range_norm_eq_card_of_cyclic` (whose base is a genuine completion of a
number field) for the resulting cyclic extension `B₁ / q.adicCompletion L`. -/
theorem natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
    {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B B₁ : Type u} [Field B] [Field B₁]
    [Algebra (Q.adicCompletion K) B] [Algebra (Q.adicCompletion K) B₁] [Algebra B B₁]
    [IsScalarTower (Q.adicCompletion K) B B₁]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B B₁]
    [IsGalois B B₁] [IsCyclic (B₁ ≃ₐ[B] B₁)] :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))) =
      Nat.card (B₁ ≃ₐ[B] B₁) := by
  -- Realize the arbitrary finite extension `B / F` as the completion of a number field.
  obtain ⟨L : Type u, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    exists_algEquiv_adicCompletion_of_finiteDimensional (Q := Q) (B := B)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- Transport the `B`-algebra structure on `B₁` along `e : B ≃ₐ[F] q.adicCompletion L`.
  letI : Algebra (q.adicCompletion L) B₁ :=
    ((algebraMap B B₁).comp e.symm.toRingHom).toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) B₁).comp e.toRingHom = algebraMap B B₁ := by
    ext x
    show algebraMap (q.adicCompletion L) B₁ (e x) = algebraMap B B₁ x
    rw [show algebraMap (q.adicCompletion L) B₁ =
      (algebraMap B B₁).comp e.symm.toRingHom from rfl]
    simp [RingHom.comp_apply]
  haveI : FiniteDimensional (q.adicCompletion L) B₁ :=
    finiteDimensional_transport e.toRingEquiv hhe
  haveI : IsGalois (q.adicCompletion L) B₁ :=
    isGalois_transport e.toRingEquiv hhe
  haveI : IsCyclic (B₁ ≃ₐ[q.adicCompletion L] B₁) :=
    (algEquiv_cast (E := B₁) hhe).isCyclic.mp inferInstance
  -- The cyclic norm index theorem at the realized base `q.adicCompletion L`.
  have hcyclic :=
    natCard_quotient_units_range_norm_eq_card_of_cyclic (Q := q) (E := B₁)
  -- Transport the two sides back along `e`.
  have htransport : Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))) =
      Nat.card ((q.adicCompletion L)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (q.adicCompletion L) : B₁ →* q.adicCompletion L))) :=
    Nat.card_congr (quotEquiv_norm_of_cast (φ := e.toRingEquiv) hhe).toEquiv
  have hgal : Nat.card (B₁ ≃ₐ[B] B₁) = Nat.card (B₁ ≃ₐ[q.adicCompletion L] B₁) :=
    Nat.card_congr (algEquiv_cast (E := B₁) hhe).toEquiv
  rw [htransport, hcyclic, ← hgal]

end Commons.NumberTheory.NumberField.Completion
