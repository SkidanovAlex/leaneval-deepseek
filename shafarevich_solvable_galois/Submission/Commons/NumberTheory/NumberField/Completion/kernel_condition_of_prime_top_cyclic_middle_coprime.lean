import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.FieldTheory.Galois.kernel_condition_of_cyclic_middle_coprime
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

universe uK uB uB1

open IsDedekindDomain.HeightOneSpectrum

/-- **The cyclic case of the local norm index theorem, for an arbitrary base field, with the
universes of the three fields kept independent.**

Let `F = Q.adicCompletion K` be the completion of a number field at a finite place, let `B / F`
be an arbitrary finite extension field (not assumed Galois over `F`) and let `B₁ / B` be a finite
*cyclic* Galois extension.  Then the quotient of the units of `B` by the norms from `B₁` has the
cardinality of the Galois group `B₁ ≃ₐ[B] B₁`.

This is the universe-flexible form of
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base`,
whose statement ties the base and the top to the universe of `K`; here `B`, `B₁` and `K` may live
in unrelated universes (all the transport lemmas used, `finiteDimensional_transport`,
`isGalois_transport`, `algEquiv_cast`, `quotEquiv_norm_of_cast`, are universe-flexible). -/
theorem natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base'
    {K : Type uK} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type uB} [Field B] {B₁ : Type uB1} [Field B₁]
    [Algebra (Q.adicCompletion K) B] [Algebra (Q.adicCompletion K) B₁] [Algebra B B₁]
    [IsScalarTower (Q.adicCompletion K) B B₁]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B B₁]
    [IsGalois B B₁] [IsCyclic (B₁ ≃ₐ[B] B₁)] :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : B₁ →* B))) =
      Nat.card (B₁ ≃ₐ[B] B₁) := by
  -- Realize the arbitrary finite extension `B / F` as the completion of a number field.
  obtain ⟨L, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{uK, uB, uB} (Q := Q) (B := B)
  letI : Field L := hLf
  letI : NumberField L := hLn
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

/-- **The kernel condition for a prime-degree top with cyclic middle.**  In the local tower
`B ⊆ B₁ ⊆ E` with `E/B` abelian Galois, `B₁/B` cyclic Galois and `[E : B₁]` prime, if
`#Gal(B₁/B)` is coprime to `[E:B₁] - 1`, then `ker N_{B₁/B} ≤ range N_{E/B₁}`.

Proof: `natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base'` at `(B₁, E)` (using
`IsCyclic (E ≃ₐ[B₁] E)`, which follows from the primality of `[E:B₁]`) identifies
`B₁ˣ ⧸ N_{E/B₁}Eˣ` with the prime `[E:B₁]`, and then
`Commons.FieldTheory.Galois.kernel_condition_of_cyclic_middle_coprime` applies. -/
theorem kernel_condition_of_prime_top_cyclic_middle_coprime
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra (Q.adicCompletion K) B₁]
    [Algebra (Q.adicCompletion K) E]
    [Algebra B B₁] [Algebra B E] [Algebra B₁ E]
    [IsScalarTower (Q.adicCompletion K) B B₁] [IsScalarTower (Q.adicCompletion K) B E]
    [IsScalarTower B B₁ E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional (Q.adicCompletion K) B₁]
    [FiniteDimensional B B₁] [FiniteDimensional B E] [FiniteDimensional B₁ E]
    [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois B B₁] [IsGalois B₁ E] [IsGalois B E]
    (hcyc : IsCyclic (B₁ ≃ₐ[B] B₁))
    (hprime : Nat.Prime (Module.finrank B₁ E))
    (hcop : (Nat.card (B₁ ≃ₐ[B] B₁)).Coprime (Module.finrank B₁ E - 1)) :
    MonoidHom.ker (Units.map (Algebra.norm B : B₁ →* B)) ≤
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) := by
  -- The three scalar towers combine to `F ⊆ B₁ ⊆ E`.
  haveI hSt : IsScalarTower (Q.adicCompletion K) B₁ E :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B B₁ x,
        ← IsScalarTower.algebraMap_apply B B₁ E]
      exact IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E x
  -- `E/B₁` has prime degree, hence cyclic Galois group.
  haveI : Fact (Nat.Prime (Module.finrank B₁ E)) := ⟨hprime⟩
  haveI : IsCyclic (E ≃ₐ[B₁] E) :=
    isCyclic_of_prime_card (α := E ≃ₐ[B₁] E) (p := Module.finrank B₁ E)
      (IsGalois.card_aut_eq_finrank B₁ E)
  -- The cyclic norm index theorem at the tower `B₁ ⊆ E`.
  have hN := natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base'
    (Q := Q) (B := B₁) (B₁ := E)
  refine Commons.FieldTheory.Galois.kernel_condition_of_cyclic_middle_coprime
    (B := B) (B₁ := B₁) (E := E) hcyc ?_ ?_
  · rw [hN, IsGalois.card_aut_eq_finrank B₁ E]
    exact hprime
  · rw [hN, IsGalois.card_aut_eq_finrank B₁ E]
    exact hcop

end Commons.NumberTheory.NumberField.Completion
