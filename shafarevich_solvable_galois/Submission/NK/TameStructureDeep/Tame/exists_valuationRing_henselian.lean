import Mathlib
import Submission.NK.RamificationAdic.exists_valuationRingData
import Submission.NK.Ramification.exists_valuationSubring_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open IsDedekindDomain

namespace NK.TameStructureDeep.Tame

universe uK uB

/-- **Henselianity is transported along a ring isomorphism.**

If `e : A ≃+* B` is a ring isomorphism and `B` is a local Henselian ring, then the local ring `A`
is Henselian as well: a simple root in the residue field of `A` is carried by `e` to a simple
root in the residue field of `B`, which lifts to a root `b ∈ B`, and `e.symm b` lifts the
original root. -/
theorem henselianLocalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] (e : A ≃+* B) [HenselianLocalRing B] :
    HenselianLocalRing A where
  toIsLocalRing := ‹IsLocalRing A›
  is_henselian := by
    intro f hf a₀ h₁ h₂
    have hmemA : ∀ x : A, x ∈ IsLocalRing.maximalIdeal A ↔
        e x ∈ IsLocalRing.maximalIdeal B := by
      intro x
      rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, mem_nonunits_iff]
      exact not_congr ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
    have hf' : (f.map (e : A →+* B)).Monic := hf.map (e : A →+* B)
    have h₁' : (f.map (e : A →+* B)).eval ((e : A →+* B) a₀) ∈
        IsLocalRing.maximalIdeal B := by
      rw [Polynomial.eval_map]
      rw [show Polynomial.eval₂ (e : A →+* B) ((e : A →+* B) a₀) f = e (f.eval a₀) from
        Polynomial.eval₂_at_apply (e : A →+* B) a₀]
      exact (hmemA _).mp h₁
    have h₂' : IsUnit ((f.map (e : A →+* B)).derivative.eval ((e : A →+* B) a₀)) := by
      rw [Polynomial.derivative_map, Polynomial.eval_map]
      rw [show Polynomial.eval₂ (e : A →+* B) ((e : A →+* B) a₀) (Polynomial.derivative f) =
          e ((Polynomial.derivative f).eval a₀) from
        Polynomial.eval₂_at_apply (e : A →+* B) a₀]
      exact h₂.map e
    obtain ⟨b, hb, hbmem⟩ :=
      HenselianLocalRing.is_henselian (f.map (e : A →+* B)) hf' ((e : A →+* B) a₀) h₁' h₂'
    refine ⟨e.symm b, ?_, ?_⟩
    · have h1 : Polynomial.eval ((e : A →+* B) (e.symm b)) (Polynomial.map (e : A →+* B) f) =
          (e : A →+* B) (Polynomial.eval (e.symm b) f) := by
        rw [Polynomial.eval_map]
        exact Polynomial.eval₂_at_apply (e : A →+* B) (e.symm b)
      have h2 : (e : A →+* B) (e.symm b) = b := RingEquiv.apply_symm_apply e b
      have h3 : (e : A →+* B) (Polynomial.eval (e.symm b) f) = 0 := by
        rw [← h1, h2]
        exact hb
      exact e.injective (by simpa using h3)
    · refine (hmemA _).mpr ?_
      simpa using hbmem

/-- **The valuation ring of a finite extension of a `p`-adic field, Henselian, with finite
residue field of residue characteristic.**

Let `K` be a number field, `𝔭` a finite place and `B` a finite-dimensional field extension of
the `p`-adic completion `K_𝔭`.  Then `B` carries a valuation subring `A` which is a discrete
valuation ring, is Henselian, and whose residue field is a finite field of characteristic equal
to the residue characteristic `resCharAt 𝔭` of `𝔭`.

Indeed, by `exists_algEquiv_adicCompletion_of_finiteDimensional_aux` the field `B` is the
completion `L_q` of a number field `L` at a place `q | 𝔭`; transporting the integral closure
`q.adicCompletionIntegers L` of `L_q` across this isomorphism gives `A`.  Its residue field is
the finite field `𝓞 L ⧸ q` of characteristic `resCharAt 𝔭`; Henselianity is transported from
the Henselian ring `q.adicCompletionIntegers L` along the induced ring isomorphism. -/
theorem exists_valuationRing_henselian_aux {K : Type uK} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {B : Type uB}
    [Field B] [Algebra (𝔭.adicCompletion K) B] [FiniteDimensional (𝔭.adicCompletion K) B] :
    ∃ (A : ValuationSubring B), IsDiscreteValuationRing A ∧ HenselianLocalRing A ∧
      ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := by
  obtain ⟨L, hLf, hLn, hALK, q, hq, hne⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{uK, uB, uB}
      (Q := 𝔭) (B := B)
  letI := hLf
  letI := hLn
  letI := hALK
  letI : Algebra (𝔭.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 q hq)
  obtain ⟨e⟩ := hne
  let A₂ : ValuationSubring (q.adicCompletion L) := q.adicCompletionIntegers L
  let A : ValuationSubring B := A₂.comap e.toAlgHom.toRingHom
  have hA : ∀ x : B, x ∈ A ↔ e x ∈ A₂ := fun x => ValuationSubring.mem_comap
  -- the ring isomorphism `A ≃+* A₂` induced by `e`
  have eA : A ≃+* A₂ := NK.Ramification.ringEquivOfMap A A₂ e hA
  have hDVR : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (A := A₂) (B := A) eA.symm
  haveI : IsDiscreteValuationRing A := hDVR
  haveI : HenselianLocalRing A₂ :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing q
  have hHens : HenselianLocalRing A := henselianLocalRing_of_ringEquiv eA
  -- the residue field of `A` is that of `L_q`, i.e. `𝓞 L ⧸ q`
  have hres : IsLocalRing.ResidueField A ≃+*
      (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    (IsLocalRing.ResidueField.mapEquiv eA).trans
      (Classical.choice
        (Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := L) q))
  haveI : Finite (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient q.ne_bot
  haveI : Finite (IsLocalRing.ResidueField A) := Finite.of_equiv _ hres.symm.toEquiv
  haveI : PerfectField (IsLocalRing.ResidueField A) := PerfectField.ofFinite
  -- its characteristic is the residue characteristic of `𝔭`
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hcharK : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) :=
    NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  have hmemK : ((NK.TameStructureDeep.Tame.resCharAt 𝔭 : ℕ) :
      NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal :=
    NK.LocalInputs.ResidueChar.ratPrime_mem_asIdeal_of_charP 𝔭 hp hcharK
  have hmemL : ((NK.TameStructureDeep.Tame.resCharAt 𝔭 : ℕ) :
      NumberField.RingOfIntegers L) ∈ q.asIdeal := by
    have h2 : ((NK.TameStructureDeep.Tame.resCharAt 𝔭 : ℕ) :
        NumberField.RingOfIntegers K) ∈ q.asIdeal.under (NumberField.RingOfIntegers K) := by
      rw [show q.asIdeal.under (NumberField.RingOfIntegers K) = 𝔭.asIdeal from hq.over.symm]
      exact hmemK
    have h3 := (Ideal.mem_under (NumberField.RingOfIntegers K) q.asIdeal).mp h2
    rwa [map_natCast] at h3
  have hcharL : CharP (NumberField.RingOfIntegers L ⧸ q.asIdeal)
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmemL
  have hcharA : CharP (IsLocalRing.ResidueField A) (NK.TameStructureDeep.Tame.resCharAt 𝔭) :=
    NK.RamificationAdic.charP_of_ringEquiv hres.symm hp hcharL
  haveI : CharP (IsLocalRing.ResidueField A) (NK.TameStructureDeep.Tame.resCharAt 𝔭) := hcharA
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ :=
    FiniteField.card (IsLocalRing.ResidueField A) (NK.TameStructureDeep.Tame.resCharAt 𝔭)
  exact ⟨A, hDVR, hHens, n, by rw [Nat.card_eq_fintype_card, hn]⟩

/-- **A discrete valuation ring of a finite extension of a `p`-adic field, Henselian, with
finite residue field of residue characteristic.**  See `exists_valuationRing_henselian_aux`. -/
theorem exists_valuationRing_henselian {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {B : Type*}
    [Field B] [Algebra (𝔭.adicCompletion K) B] [FiniteDimensional (𝔭.adicCompletion K) B] :
    ∃ (A : ValuationSubring B), IsDiscreteValuationRing A ∧ HenselianLocalRing A ∧
      ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f :=
  exists_valuationRing_henselian_aux 𝔭

end NK.TameStructureDeep.Tame
