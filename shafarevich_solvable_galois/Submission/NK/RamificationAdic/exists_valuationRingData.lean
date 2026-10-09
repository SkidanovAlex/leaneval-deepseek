import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.Ramification.exists_valuationSubring_finiteDimensional
import Submission.NK.Ramification.ramificationSubgroup_map_conj
import Submission.NK.RamificationDeep.uniformizerData_of_isGalois
import Submission.NK.Ramification.exists_ramificationSubgroup_eq_bot
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
universe uK uB

set_option maxHeartbeats 800000

open scoped Pointwise

namespace NK.RamificationAdic

open IsDedekindDomain

/-- `CharP` is transported along a ring isomorphism.  (A local copy of the argument used in
`NK.IndecomposedDeep.localDegreeRigidity`, where it is `private`.) -/
theorem charP_of_ringEquiv {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [Nontrivial R] [Nontrivial S] (e : R ≃+* S) {p : ℕ} (hp : p.Prime) (h : CharP R p) :
    CharP S p := by
  rw [CharP.charP_iff_prime_eq_zero hp] at h ⊢
  rw [← map_natCast (e : R →+* S) p, h, map_zero]

/-- **A Galois-stable valuation ring of a finite extension of a `p`-adic field with the right
residue field.**

This is the reduction step used by `exists_valuationRingData`.  The finite extension `B` of the
`p`-adic field `K_𝔭` is the completion `L_q` of a number field `L` at a prime `q` lying over `𝔭`,
so the valuation ring `q.adicCompletionIntegers L` can be transported to a valuation subring `A`
of `B` whose residue field is that of `L_q`: the residue field of `L_q` is the residue field
`𝓞 L / q` of `q`, a finite field of characteristic `resCharAt 𝔭` (the residue characteristic of
`𝔭`).  Such an `A` is stable under the whole Galois group (`A.decompositionSubgroup K_𝔭 = ⊤`),
whence the decomposition subgroup is finite. -/
theorem exists_valuationSubring_residueData {K : Type uK} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type uB} [Field B] [Algebra (𝔭.adicCompletion K) B]
    [FiniteDimensional (𝔭.adicCompletion K) B] [IsGalois (𝔭.adicCompletion K) B] :
    ∃ (A : ValuationSubring B) (_ : IsDiscreteValuationRing A),
      A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤ ∧
      Finite ↥(A.decompositionSubgroup (𝔭.adicCompletion K)) ∧
      PerfectField (IsLocalRing.ResidueField A) ∧
      ∃ f : ℕ, Nat.card (IsLocalRing.ResidueField A) =
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := by
  obtain ⟨L, hLf, hLn, hALK, q, hq, hne⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{uK, uB, uB}
      (B := B) 𝔭
  letI := hLf
  letI := hLn
  letI := hALK
  letI : Algebra (𝔭.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 q hq)
  obtain ⟨e⟩ := hne
  let A₂ : ValuationSubring (q.adicCompletion L) := q.adicCompletionIntegers L
  let A : ValuationSubring B := A₂.comap e.toAlgHom.toRingHom
  have hA : ∀ x : B, x ∈ A ↔ e x ∈ A₂ := fun x => ValuationSubring.mem_comap
  have hDVR : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (A := A₂) (B := A) (NK.Ramification.ringEquivOfMap A A₂ e hA).symm
  haveI : IsDiscreteValuationRing A := hDVR
  have hA₂ : A₂.decompositionSubgroup (𝔭.adicCompletion K) = ⊤ :=
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_adicCompletionIntegers_eq_top
      𝔭 q hq
  have htop : A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro σ
    exact (NK.Ramification.conjugationMulEquiv_mem_decompositionSubgroup_iff A A₂ e hA σ).mp
      (by rw [hA₂]; exact Subgroup.mem_top _)
  haveI : Finite ↥(A.decompositionSubgroup (𝔭.adicCompletion K)) := by
    rw [htop]; infer_instance
  -- The residue field of `A` is the residue field `𝓞 L ⧸ q`, a finite field.
  have hres : IsLocalRing.ResidueField A ≃+* (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    (IsLocalRing.ResidueField.mapEquiv (NK.Ramification.ringEquivOfMap A A₂ e hA)).trans
      (Classical.choice
        (Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := L) q))
  haveI : Finite (NumberField.RingOfIntegers L ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient q.ne_bot
  haveI : Finite (IsLocalRing.ResidueField A) := Finite.of_equiv _ hres.symm.toEquiv
  haveI : PerfectField (IsLocalRing.ResidueField A) := PerfectField.ofFinite
  -- Its characteristic is the residue characteristic of `𝔭`.
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
    charP_of_ringEquiv hres.symm hp hcharL
  haveI : CharP (IsLocalRing.ResidueField A) (NK.TameStructureDeep.Tame.resCharAt 𝔭) := hcharA
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ :=
    FiniteField.card (IsLocalRing.ResidueField A) (NK.TameStructureDeep.Tame.resCharAt 𝔭)
  refine ⟨A, hDVR, htop, ?_, ?_, (n : ℕ), ?_⟩
  · rw [htop]; infer_instance
  · exact PerfectField.ofFinite
  · rw [Nat.card_eq_fintype_card, hn]

/-- **The required valuation-ring data for a finite Galois extension of a `p`-adic field.**

Everything is transported from the integral closure `q.adicCompletionIntegers L` of the completion
of a number field `L` at a prime `q | 𝔭`: its decomposition subgroup is everything (so finite),
its residue field is the finite field `𝓞 L ⧸ q` of characteristic `resCharAt 𝔭`, it carries the
data of the uniformizer criterion (`NK.RamificationDeep.UniformizerData`, with the inertia field
as `E`), and the higher ramification filtration eventually becomes trivial. -/
theorem exists_valuationRingData {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type*} [Field B] [Algebra (𝔭.adicCompletion K) B]
    [FiniteDimensional (𝔭.adicCompletion K) B] [IsGalois (𝔭.adicCompletion K) B] :
    ∃ (A : ValuationSubring B) (hA : IsDiscreteValuationRing A) (πA : A)
      (E : IntermediateField (𝔭.adicCompletion K) B) (f N : ℕ),
      A.decompositionSubgroup (𝔭.adicCompletion K) = ⊤ ∧
      Finite ↥(A.decompositionSubgroup (𝔭.adicCompletion K)) ∧
      PerfectField (IsLocalRing.ResidueField A) ∧
      Nat.card (IsLocalRing.ResidueField A) = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f ∧
      NK.RamificationDeep.UniformizerData (K := 𝔭.adicCompletion K) A πA E ∧
      NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A N = ⊥ := by
  obtain ⟨A, hDVR, htop, hFinite, hPerfect, hcard⟩ :=
    exists_valuationSubring_residueData (K := K) (B := B) 𝔭
  haveI : IsDiscreteValuationRing A := hDVR
  haveI : Finite ↥(A.decompositionSubgroup (𝔭.adicCompletion K)) := hFinite
  haveI : PerfectField (IsLocalRing.ResidueField A) := hPerfect
  obtain ⟨πA, E, hUD⟩ :=
    NK.RamificationDeep.uniformizerData_of_isGalois (K := 𝔭.adicCompletion K) A htop
  obtain ⟨N, hN⟩ := NK.Ramification.exists_ramificationSubgroup_eq_bot (K := 𝔭.adicCompletion K) A
  obtain ⟨f, hf⟩ := hcard
  exact ⟨A, hDVR, πA, E, f, N, htop, hFinite, hPerfect, hf, hUD, hN⟩

end NK.RamificationAdic
