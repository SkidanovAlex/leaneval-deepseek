import Mathlib
import Submission.NK.LocalInputs.Inputs
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

namespace NK.LocalInputs.PowerQuotient

noncomputable section

/-- The `p`-power quotient of the unit group `𝒪ˣ` of the valuation ring (a subgroup of `κˣ`)
has the same cardinality as the `p`-power quotient of the abstract unit group `𝒪ˣ`
(the two are identified by `ValuationSubring.unitGroupMulEquiv`). -/
private theorem natCard_unitGroup_quot_pow_eq {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) :
    Nat.card ((𝔭.adicCompletionIntegers K).unitGroup ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
          (𝔭.adicCompletionIntegers K).unitGroup).range) =
      Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
          (𝔭.adicCompletionIntegers K)ˣ).range) := by
  have he : ((powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
        (𝔭.adicCompletionIntegers K).unitGroup).range).map
        (ValuationSubring.unitGroupMulEquiv (𝔭.adicCompletionIntegers K)) =
      (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
        (𝔭.adicCompletionIntegers K)ˣ).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      rw [MonoidHom.mem_range] at hk ⊢
      obtain ⟨g, hg⟩ := hk
      refine ⟨ValuationSubring.unitGroupMulEquiv _ g, ?_⟩
      have hgk : g ^ p = k := by simpa only [powMonoidHom_apply] using hg
      rw [powMonoidHom_apply, ← map_pow, hgk]
      exact hkx
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨(ValuationSubring.unitGroupMulEquiv _).symm (k ^ p), ?_, ?_⟩
      · rw [MonoidHom.mem_range]
        exact ⟨(ValuationSubring.unitGroupMulEquiv _).symm k, by
          simp only [powMonoidHom_apply]
          rw [← map_pow]⟩
      · rw [← hk, powMonoidHom_apply]
        exact MulEquiv.apply_symm_apply _ _
  have hidx : ((powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
        (𝔭.adicCompletionIntegers K).unitGroup).range).index =
      ((powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
        (𝔭.adicCompletionIntegers K)ˣ).range).index := by
    rw [← he, Subgroup.index_map_equiv]
  exact hidx

theorem natCard_KummerGroup_eq_pow_of_principalUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime)
    (hres : Nat.card ((IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ ⧸
      (powMonoidHom p).range) = 1)
    (hU : Nat.card (NK.LocalInputs.principalUnits K 𝔭 ⧸ (powMonoidHom p).range) =
      p ^ (NK.LocalInputs.localDegree K 𝔭 + NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K))) :
    Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) =
      p ^ (NK.LocalInputs.localDegree K 𝔭 + 1 + NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- the residue field of the completion is finite
  haveI hfinRes : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI hfinUnits : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ :=
    Finite.of_injective (Units.val :
      (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ →
      IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) Units.val_injective
  -- the power map on the residue units is surjective, by `hres`
  have hsurj : Function.Surjective
      (fun x : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ => x ^ p) := by
    intro x
    haveI : Subsingleton ((IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ ⧸
        (powMonoidHom p : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ →*
          (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ).range) :=
      (Nat.card_eq_one_iff_unique.mp hres).1
    have h1 : (QuotientGroup.mk x : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ ⧸
        (powMonoidHom p : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ →*
          (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ).range) = 1 :=
      Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff] at h1
    exact MonoidHom.mem_range.mp h1
  -- the residue units have no nontrivial `p`-torsion
  have htor : ∀ h : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ, h ^ p = 1 → h = 1 := by
    intro h hh
    have hinj : Function.Injective
        (fun x : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ => x ^ p) :=
      Finite.injective_iff_surjective.mpr hsurj
    exact hinj (by simpa using hh)
  -- Step 1: the `p`-power quotient of `𝒪ˣ` equals that of the principal units
  have hstep1 : Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
          (𝔭.adicCompletionIntegers K)ˣ).range) =
      Nat.card (NK.LocalInputs.principalUnits K 𝔭 ⧸
        (powMonoidHom p : (NK.LocalInputs.principalUnits K 𝔭) →*
          (NK.LocalInputs.principalUnits K 𝔭)).range) := by
    have h := Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul
      (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom)
      (Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion 𝔭) p htor
    rw [hres, one_mul] at h
    exact h
  -- Step 2: the `p`-power quotient of `κˣ` is `p` times that of `𝒪ˣ`
  have htorZ : ∀ h : Multiplicative ℤ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h2 : Multiplicative.ofAdd ((p : ℤ) * Multiplicative.toAdd h) = 1 := by
      rw [← Commons.NumberTheory.NumberField.Completion.ofAdd_pow_eq (Multiplicative.toAdd h) p,
        ← ofAdd_toAdd h]
      exact hh
    have h3 : (p : ℤ) * Multiplicative.toAdd h = 0 := ofAdd_eq_one.mp h2
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hp0
    · rw [← ofAdd_toAdd h, h4, ofAdd_zero]
  have hker : (Commons.NumberTheory.NumberField.Completion.unitsValLog
        (𝔭.adicCompletion K)).ker = (𝔭.adicCompletionIntegers K).unitGroup := by
    simpa [Commons.NumberTheory.NumberField.Completion.adicUnitsVal] using
      Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup K 𝔭
  have hstep2 : Nat.card ((𝔭.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletion K)ˣ →* (𝔭.adicCompletion K)ˣ).range) =
      p * Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
          (𝔭.adicCompletionIntegers K)ˣ).range) := by
    have h := Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul
      (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K))
      (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective K 𝔭) p htorZ
    rw [Commons.NumberTheory.NumberField.Completion.natCard_multiplicative_int_quot_pow p] at h
    rw [hker] at h
    rw [natCard_unitGroup_quot_pow_eq 𝔭 p] at h
    exact h
  calc Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K))
      = Nat.card ((𝔭.adicCompletion K)ˣ ⧸
          (powMonoidHom p : (𝔭.adicCompletion K)ˣ →* (𝔭.adicCompletion K)ˣ).range) := rfl
    _ = p * Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
          (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
            (𝔭.adicCompletionIntegers K)ˣ).range) := hstep2
    _ = p * Nat.card (NK.LocalInputs.principalUnits K 𝔭 ⧸
          (powMonoidHom p : (NK.LocalInputs.principalUnits K 𝔭) →*
            (NK.LocalInputs.principalUnits K 𝔭)).range) := by rw [hstep1]
    _ = p * p ^ (NK.LocalInputs.localDegree K 𝔭 +
          NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) := by rw [hU]
    _ = p ^ (NK.LocalInputs.localDegree K 𝔭 + 1 +
          NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) := by
        rw [← pow_succ']
        congr 1
        omega

end

end NK.LocalInputs.PowerQuotient
