import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.TameStructureDeep.Tame.WildInertiaAux
import Submission.NK.TameStructureDeep.Tame.wildInertia_le_tameClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace NK.TameStructureDeep.Tame

theorem tameClosure_inf_finrank_prime_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M] :
    ∃ k : ℕ, Module.finrank ↥(NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) ⊓ M) ↥M
      = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k := by
  classical
  -- the valuation-ring data of `M/κ` supplied by the global model
  obtain ⟨A, hA, πA, E, f, N, hdec, hfin, hperf, hq, hunif, hbot⟩ :=
    NK.RamificationAdic.exists_valuationRingData (K := K) 𝔭 (B := M)
  letI : IsDiscreteValuationRing A := hA
  haveI : Finite ↥(A.decompositionSubgroup (𝔭.adicCompletion K)) := hfin
  haveI : PerfectField (IsLocalRing.ResidueField A) := hperf
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hq' : Nat.card (↥A ⧸ IsLocalRing.maximalIdeal ↥A)
      = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ f := hq
  -- the filtration terminates
  have hbot1 : NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A (1 + N) = ⊥ :=
    le_bot_iff.mp
      ((NK.Ramification.ramificationSubgroup_antitone A (by omega : N ≤ 1 + N)).trans_eq hbot)
  -- `#G_1` is a power of `p`
  obtain ⟨j, hj⟩ := NK.RamificationDeep.exists_natCard_one_eq_prime_pow (K := 𝔭.adicCompletion K)
    (A := A) hunif hp hq' hbot1
  -- the wild inertia is tamely ramified
  have hle := NK.TameStructureDeep.Tame.wildInertia_le_tameClosure 𝔭 hπ M A hdec f hp hq
  let T : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  let X : IntermediateField (𝔭.adicCompletion K) ↥M :=
    IntermediateField.fixedField
      (Subgroup.map (A.decompositionSubgroup (𝔭.adicCompletion K)).subtype
        (NK.Ramification.ramificationSubgroup (K := 𝔭.adicCompletion K) A 1))
  have hXcard : Nat.card ↥X.fixingSubgroup = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ j := by
    rw [IntermediateField.fixingSubgroup_fixedField]
    rw [Subgroup.card_map_of_injective Subtype.coe_injective]
    exact hj
  have hXdeg : Module.finrank ↥X ↥M = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ j := by
    rw [← hXcard]
    conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup X]
    exact IntermediateField.finrank_fixedField_eq_card X.fixingSubgroup
  let Y : IntermediateField (𝔭.adicCompletion K) ↥M :=
    (T ⊓ M).restrict (inf_le_right : T ⊓ M ≤ M)
  have hY : (Y : IntermediateField (𝔭.adicCompletion K) ↥M) = IntermediateField.comap M.val T := by
    ext x
    rw [IntermediateField.mem_restrict]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hXY : X ≤ Y := by
    rw [hY]
    exact hle
  have hYdeg : Module.finrank ↥Y ↥M = Nat.card ↥Y.fixingSubgroup := by
    conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup Y]
    exact IntermediateField.finrank_fixedField_eq_card Y.fixingSubgroup
  have hdvd : Module.finrank ↥Y ↥M ∣ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ j := by
    rw [hYdeg, ← hXcard]
    exact Subgroup.card_dvd_of_le (IntermediateField.fixingSubgroup_le hXY)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  -- transport the degree from the subfield of `M` back to `T ⊓ M`
  have hbridge : Module.finrank ↥(T ⊓ M) ↥M = Module.finrank ↥Y ↥M := by
    refine Algebra.finrank_eq_of_equiv_equiv (IntermediateField.restrictAlgEquiv
      (inf_le_right : T ⊓ M ≤ M)).toRingEquiv (RingEquiv.refl ↥M) ?_
    ext x
    rfl
  exact ⟨k, by rw [hbridge, hk]⟩

end NK.TameStructureDeep.Tame
