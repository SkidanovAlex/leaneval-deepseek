import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSandwich
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionArith
import Submission.NK.Unramified.normGroup_eq_unramifiedNormGroup
import Submission.NK.Unramified.exists_unramified_level_adicCompletion
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic input at the omitted place (`ChebAux/auxLocalCondition`)

The target is the arithmetic input of the descent of Hilbert reciprocity from the cyclic
cyclotomic case to the general cyclic case (Milne, *CFT*, Lemma VII.7.3 + III.3.6): for a cyclic
extension `L/K` of number fields and a place `v₀` of `K`, there is a cyclic cyclotomic level
`M = K(ζ_m)` such that, with `E = L·M`, every `x ∈ Kˣ` is a local norm from `E` over `M` at
*every* place of `M` above `v₀`.

The proof is the one assembled (independently, for the same interface) in
`Submission/Work/CFTLib/HRdescent/localConditionCyclotomicPrime.lean`:
`NK.CFTLib.HRdescent.localConditionCyclotomicPrime` produces the auxiliary fields with *all* the
algebraic structure required here, together with the local norm condition, and additionally the
fact that the conductor `m` is a unit at the finite place `v₀`; the latter is what makes `M/K`
unramified at `v₀` and hence reduces the local condition to the (elementary) counting argument of
`NK.KC.localBaseChange_aux`.  The present statement is that result with the conductor condition
dropped.

The two helper lemmas below are the elementary halves of the alternative (sandwich) computation of
the local norm group at an unramified place; they are kept because the counting argument in
`localBaseChange_aux` uses their content (`norm_units_surjective_of_ramificationIdx_eq_one` and
`unitsValLog_norm`), and because the sibling developments
(`NK.HR2.finrank_adicCompletion_of_compositum`) refer to them.
-/

namespace NK.NUV2.ChebAux

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **The index of the unramified norm group is the degree.** -/
theorem unramifiedNormGroup_index {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (m : ℕ) (hm : 1 ≤ m) :
    (NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m).index = m := by
  obtain ⟨E, θ, hE, hfd, hgal, hcomm, hfinrank, hN⟩ :=
    NK.Unramified.exists_unramified_level_adicCompletion K Q m hm
  haveI : FiniteDimensional (Q.adicCompletion K) ↥E := hfd
  haveI : IsGalois (Q.adicCompletion K) ↥E := hgal
  rw [← hN, NK.LocalReciprocity.normGroup_eq_range, Subgroup.index_eq_card]
  have h := Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base
    (K := K) Q (B := Q.adicCompletion K) (E := ↥E) hcomm
  rw [h, IsGalois.card_aut_eq_finrank]
  exact hfinrank

/-- **The norm group of a local extension is contained in the unramified norm group of degree
equal to its inertia degree.**  This is the "valuation of a norm is a multiple of the inertia
degree" half of the computation of `N_{L_q/K_Q}`. -/
theorem normGroup_le_unramifiedNormGroup {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hr : r.asIdeal.LiesOver Q.asIdeal) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) (r.adicCompletion L) ≤
      NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q
        (r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (r.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q r hr)
  intro x hx
  rw [NK.Unramified.NormGroupEqUnramified.mem_unramifiedNormGroup_iff]
  rw [NK.LocalReciprocity.normGroup_eq_range, MonoidHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ,
      (Commons.NumberTheory.NumberField.Completion.unitsValLog (r.adicCompletion L)) y
        = Multiplicative.ofAdd k := ⟨_, (ofAdd_toAdd _).symm⟩
  refine ⟨(NK.LocalReciprocityLubinTate.uniformizerUnit K Q) ^ (-k), ?_⟩
  rw [Commons.NumberTheory.NumberField.Completion.unitsValLog_norm (K := K) (L := L) Q r hr y, hk]
  rw [map_zpow, NK.Unramified.NormGroupEqUnramified.unitsValLog_uniformizerUnit Q]
  apply Multiplicative.toAdd.injective
  rw [Int.toAdd_pow, Int.toAdd_pow, Int.toAdd_zpow, toAdd_ofAdd,
    toAdd_ofAdd]
  ring

/-- **The arithmetic input at the omitted place** (Milne, *CFT*, Lemma VII.7.3 + III.3.6): for a
cyclic extension `L/K` of number fields and a place `v₀` of `K` there is a cyclic cyclotomic
extension `M/K` such that, with `E = L·M`, every `x ∈ Kˣ` is a local norm from `E` over `M_w` at
every place `w` of `M` above `v₀`. -/
theorem auxLocalCondition {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    (v₀ : NK.GlobalCFT.Place K) :
    ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E)
      (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E)
      (_ : IsScalarTower K L E) (_ : IsScalarTower K M E)
      (_ : FiniteDimensional K M) (_ : FiniteDimensional K E)
      (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M))
      (m : ℕ) (_ : 0 < m) (_ : IsCyclotomicExtension {m} K M),
      (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧
      (∀ (x : Kˣ) (w : NK.GlobalCFT.Place M), NK.GlobalCFT.Place.LiesOver w v₀ →
        Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) := by
  obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
    hgalE, hcycM, m, hm, hcycExt, hgen, -, hloc⟩ :=
    NK.CFTLib.HRdescent.localConditionCyclotomicPrime (K := K) (L := L) hcyc v₀
  exact ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM, hgalE,
    hcycM, m, hm, hcycExt, hgen, hloc⟩

end

end NK.NUV2.ChebAux
