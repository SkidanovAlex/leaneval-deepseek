import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 16000000

universe uK uB uE

/-! ## The local norm index bound for an arbitrary local base

Let `K` be a number field with a finite place `Q`, put `F = Q.adicCompletion K`, and let `B` be a
finite field extension of `F`.  For a finite abelian Galois extension `E / B` the index
`#(Bˣ ⧸ N_{E/B}(Eˣ))` of the norm group is at most the order of the Galois group
`Gal(E/B) = E ≃ₐ[B] E`.

The mathematical input is the norm index theorem
`natCard_quotient_units_range_norm_le_finrank_of_abelian_local`, which is proved for a base which
*is* the completion `Q.adicCompletion K` of a number field at a place.  To reach an arbitrary
local base `B` we realise `B` as such a completion: by
`exists_algEquiv_adicCompletion_of_finiteDimensional` there are a number field `L`, a place `q | Q`
and an `F`-algebra isomorphism `φ : B ≃ₐ[F] q.adicCompletion L`.  The extension `E / B` is
transported along `φ` to an extension of the completion `q.adicCompletion L`
(`finiteDimensional_transport`, `isGalois_transport`, `commute_transport`), the norm index
theorem is applied there, and the conclusion is transported back.

The two sides of the inequality are transported differently:

* the Galois group via `algEquiv_cast` / `IsGalois.card_aut_eq_finrank`;
* the norm index via the invariance of `Subgroup.index` under a group isomorphism
  (`Subgroup.index_map_equiv`) applied to `range_norm_map_eq`.  Working with `Subgroup.index`
  rather than with `Nat.card` of the quotient `Bˣ ⧸ N(Eˣ)` keeps the statement in the light
  `Subgroup`-world and avoids the expensive instance search on the quotient type over the
  (transported, hence non-canonical) local field `q.adicCompletion L`. -/

/-- The result in named universes, so that the local base `B` can be realised in the *same*
universe (pinpointing the universe of the auxiliary number field `L` obtained from
`exists_algEquiv_adicCompletion_of_finiteDimensional_aux`). -/
private theorem base_aux
    {K : Type uK} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type uB} [Field B] [Algebra (Q.adicCompletion K) B]
    {E : Type uE} [Field E]
    [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) ≤
      Nat.card (E ≃ₐ[B] E) := by
  -- Realise `B` as the completion of a number field at a place over `Q`.
  obtain ⟨L, hLf, hLn, hLa, q, hq, hφ⟩ :=
    exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{uK, uB, uB} (Q := Q) (B := B)
  obtain ⟨φ⟩ := hφ
  obtain ⟨eφ, mulφ, addφ, commφ⟩ := φ
  -- The `F`-algebra isomorphism `B ≃ₐ[F] q.adicCompletion L` as a ring isomorphism.
  let rφ : B ≃+* (q.adicCompletion L) := RingEquiv.mk eφ mulφ addφ
  -- Transport the `B`-algebra structure on `E` to `q.adicCompletion L`.
  let f : (q.adicCompletion L) →+* E := (algebraMap B E).comp rφ.symm.toRingHom
  letI : Algebra (q.adicCompletion L) E := f.toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) E).comp rφ.toRingHom = algebraMap B E := by
    rw [RingHom.algebraMap_toAlgebra f]
    ext x
    show (algebraMap B E) (rφ.symm (rφ x)) = algebraMap B E x
    rw [rφ.symm_apply_apply]
  haveI : FiniteDimensional (q.adicCompletion L) E :=
    finiteDimensional_transport rφ hhe
  haveI : IsGalois (q.adicCompletion L) E := isGalois_transport rφ hhe
  have hcomm' : ∀ a b : E ≃ₐ[q.adicCompletion L] E, a * b = b * a :=
    commute_transport rφ hhe hcomm
  -- The norm index bound for the base `q.adicCompletion L`, a completion of a number field.
  have hmain := natCard_quotient_units_range_norm_le_finrank_of_abelian_local
    (K := L) (Q := q) (E := E) hcomm'
  have hmain' : (MonoidHom.range
        (Units.map (Algebra.norm (q.adicCompletion L) : E →* (q.adicCompletion L)))).index
      ≤ Module.finrank (q.adicCompletion L) E := hmain
  -- Transport of the norm index via `Subgroup.index`.
  have hmap := range_norm_map_eq (φ := rφ) hhe
  have hidx : (MonoidHom.range
        (Units.map (Algebra.norm (q.adicCompletion L) : E →* (q.adicCompletion L)))).index
      = (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).index := by
    rw [← hmap]
    exact Subgroup.index_map_equiv _ (Units.mapEquiv rφ.toMulEquiv)
  have hrank : Module.finrank (q.adicCompletion L) E = Module.finrank B E :=
    finrank_eq_of_algebraMap_eq rφ hhe
  calc Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
      = (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).index :=
        (Subgroup.index_eq_card _).symm
    _ = (MonoidHom.range
          (Units.map (Algebra.norm (q.adicCompletion L) : E →* (q.adicCompletion L)))).index :=
        hidx.symm
    _ ≤ Module.finrank (q.adicCompletion L) E := hmain'
    _ = Module.finrank B E := hrank
    _ = Nat.card (E ≃ₐ[B] E) := (IsGalois.card_aut_eq_finrank B E).symm

theorem natCard_quotient_units_range_norm_le_card_of_abelian_local_base
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) ≤
      Nat.card (E ≃ₐ[B] E) :=
  base_aux Q hcomm

end Commons.NumberTheory.NumberField.Completion
