import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.TUnitsPow

open scoped NumberField RestrictedProduct
open IntermediateField
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

section LocalUnitPow

/-- For a valuation subring, the subgroup of units of the ring agrees with the subgroup of
elements of valuation `1`. -/
theorem units_eq_unitGroup {K : Type} [Field K] (A : ValuationSubring K) :
    A.units = A.unitGroup := by
  ext u
  rw [ValuationSubring.mem_unitGroup_iff, Submonoid.mem_units_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hv1 : A.valuation (u : K) ≤ 1 := (A.valuation_le_one_iff (u : K)).mpr h1
    have hv2 : A.valuation (((u⁻¹ : Kˣ) : K)) ≤ 1 := (A.valuation_le_one_iff _).mpr h2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hv2
    have hne : A.valuation (u : K) ≠ 0 :=
      (Valuation.ne_zero_iff A.valuation).mpr (Units.ne_zero u)
    exact le_antisymm hv1 ((inv_le_one_iff₀.mp hv2).resolve_left
      (not_le.mpr (zero_lt_iff.mpr hne)))
  · intro h
    refine ⟨(A.valuation_le_one_iff _).mp (le_of_eq h), ?_⟩
    refine (A.valuation_le_one_iff _).mp ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]

/-- **Completely split primes admit `p`-th roots of local units.**  If the prime `q` of `K` splits
completely in `L`, `a = α ^ p` with `α ∈ L`, and `a` is a local unit at `q`, then `a` is the
`p`-th power of a unit of `𝒪_q`. -/
theorem exists_unit_pow_eq_of_splitsCompletely {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {p : ℕ} (hp : p.Prime) {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hsplit : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver q.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1)
    (hunit : Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (Units.mk0 a ha) ∈
      (q.adicCompletionIntegers K).units) :
    ∃ c : (q.adicCompletionIntegers K)ˣ,
      algebraMap K (q.adicCompletion K) a =
        ((c : q.adicCompletionIntegers K) : q.adicCompletion K) ^ p := by
  obtain ⟨Q, hQ⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) q
  letI : Algebra (q.adicCompletion K) (Q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q Q hQ)
  haveI hST : IsScalarTower K (q.adicCompletion K) (Q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion q Q hQ
  have hfr : Module.finrank (q.adicCompletion K) (Q.adicCompletion L) = 1 := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := K) (L := L) q Q hQ, (hsplit Q hQ).1, (hsplit Q hQ).2, mul_one]
  have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfr
  set α' : Q.adicCompletion L := algebraMap L (Q.adicCompletion L) α with hα'def
  obtain ⟨d, hd⟩ := hbij.2 α'
  have hd_pow : d ^ p = algebraMap K (q.adicCompletion K) a := by
    apply hbij.1
    rw [map_pow, hd]
    calc (α') ^ p = algebraMap L (Q.adicCompletion L) (α ^ p) := by rw [map_pow]
      _ = algebraMap L (Q.adicCompletion L) (algebraMap K L a) := by rw [hα]
      _ = algebraMap K (Q.adicCompletion L) a := by
            rw [IsScalarTower.algebraMap_apply K L (Q.adicCompletion L)]
      _ = algebraMap (q.adicCompletion K) (Q.adicCompletion L)
            (algebraMap K (q.adicCompletion K) a) := by
            rw [IsScalarTower.algebraMap_apply K (q.adicCompletion K) (Q.adicCompletion L)]
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hd_pow
    exact (map_ne_zero (algebraMap K (q.adicCompletion K))).mpr ha hd_pow.symm
  have hdunit : Units.mk0 d hd0 ∈ (q.adicCompletionIntegers K).unitGroup := by
    rw [← units_eq_unitGroup (q.adicCompletionIntegers K), ← Place.localUnits_ofFinite q]
    refine mem_localUnits_of_pow_mem (K := K) hp ?_
    have heq : (Units.mk0 d hd0) ^ p =
        Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (Units.mk0 a ha) := by
      refine Units.ext ?_
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      exact hd_pow
    rw [heq, Place.localUnits_ofFinite q]
    exact hunit
  refine ⟨(q.adicCompletionIntegers K).unitGroupMulEquiv ⟨Units.mk0 d hd0, hdunit⟩, ?_⟩
  rw [ValuationSubring.coe_unitGroupMulEquiv_apply]
  change algebraMap K (q.adicCompletion K) a = (d ^ p)
  exact hd_pow.symm


end LocalUnitPow

end NK.GlobalCFTdeep.SecondInequality.KummerCase
