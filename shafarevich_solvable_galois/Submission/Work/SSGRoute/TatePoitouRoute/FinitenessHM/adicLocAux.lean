import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletionExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocVal
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.helpersTotallyRamified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField WithZero
open IsDedekindDomain

section Local

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
  (Q0 : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  (hQ0 : Q0.asIdeal = Ideal.span
    ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
  (Q : HeightOneSpectrum (NumberField.RingOfIntegers K))
  (hQ : Q.asIdeal.LiesOver Q0.asIdeal)

/-- **The valuation exponent of an integer.**  For `n ≠ 0`, `v (n) = exp (-(e * v_p n))` in the
completion `Q.adicCompletion K`, where `e = Q.asIdeal.ramificationIdx (𝓞 ℚ)`. -/
theorem adicValExp_natCast (Q0 : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal)
    (n : ℕ) (hn : n ≠ 0) :
    adicValExp Q ((n : Q.adicCompletion K)) =
      (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) * padicValNat p n : ℕ) := by
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  have hne : ((n : ℤ) : ℚ) ≠ 0 := by
    simp [Nat.cast_ne_zero.mpr hn]
  -- the valuation on `ℚ_p` of `n`
  have hval : Valued.v (R := Q0.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ))
      (((n : ℤ) : ℚ) : Q0.adicCompletion ℚ) =
      WithZero.exp (-(padicValInt p (n : ℤ) : ℤ)) :=
    Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
      Q0 p (Fact.out) hmem (n : ℤ) (by simpa using (Nat.cast_ne_zero.mpr hn : (n : ℤ) ≠ 0))
  -- the identification of the arguments of the two valuations
  have harg : (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q hQ)
      (((n : ℤ) : ℚ) : Q0.adicCompletion ℚ) = ((n : ℕ) : Q.adicCompletion K) := by
    simp [map_intCast, map_natCast]
  have hpow : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((n : ℕ) : Q.adicCompletion K) =
      WithZero.exp (-((padicValNat p n : ℤ) *
        (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) : ℤ))) := by
    rw [← harg, Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
      Q0 Q hQ, hval, ← WithZero.exp_nsmul]
    congr 1
    rw [padicValInt.of_nat]
    push_cast
    ring
  rw [adicValExp, hpow, WithZero.log_exp]
  push_cast
  ring

/-- **The order of an element of the ring of integers is its valuation exponent.** -/
theorem ordAt_maximalIdeal_eq_toNat_adicValExp
    (x : Q.adicCompletionIntegers K) (hx : (x : Q.adicCompletion K) ≠ 0) :
    ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) x =
      (adicValExp Q (x : Q.adicCompletion K)).toNat := by
  haveI : IsDiscreteValuationRing (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
  set vB : HeightOneSpectrum (Q.adicCompletionIntegers K) :=
    ⟨IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K),
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime, hbot⟩ with hvB
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; rfl)
  have hmem1 : ∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^ n ↔
      n ≤ ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) x :=
    fun n => mem_pow_iff_le_ordAt vB hx0 n
  have hmem2 : ∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^ n ↔
      (n : ℤ) ≤ adicValExp Q (x : Q.adicCompletion K) :=
    fun n => mem_maximalIdeal_pow_iff_le_adicValExp Q hx n
  have hnonneg : 0 ≤ adicValExp Q (x : Q.adicCompletion K) := by
    have h := (hmem2 0).mp (by simp)
    simpa using h
  refine le_antisymm ?_ ?_
  · have hle : (ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) x : ℤ) ≤
        adicValExp Q (x : Q.adicCompletion K) :=
      (hmem2 _).mp ((hmem1 _).mpr le_rfl)
    omega
  · have hmem : x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^
        (adicValExp Q (x : Q.adicCompletion K)).toNat :=
      (hmem2 _).mpr (by omega)
    exact (hmem1 _).mp hmem

end Local

section LocalBounds

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
  (Q0 : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  (hQ0 : Q0.asIdeal = Ideal.span
    ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
  (Q : HeightOneSpectrum (NumberField.RingOfIntegers K))
  (hQ : Q.asIdeal.LiesOver Q0.asIdeal)

/-- **The count of the local different is bounded by the order of any of its nonzero elements.** -/
theorem adicLocExp_le_toNat_adicValExp (g : Q.adicCompletionIntegers K) (hg : g ≠ 0) (n : ℕ)
    (hn : (adicValExp Q (g : Q.adicCompletion K)).toNat ≤ n) :
    letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      RingHom.toAlgebra
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
    letI : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
        by_cases hr : r = 0
        · exact Or.inl hr
        · refine Or.inr ?_
          have h1 : algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) r * m = 0 := by
            rwa [Algebra.smul_def] at h
          rcases mul_eq_zero.mp h1 with h2 | h2
          · have h2' : (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ) r
                = 0 := by
              simpa [RingHom.algebraMap_toAlgebra] using h2
            exact absurd (adicCompletionMapIntegers_injective Q0 Q hQ (by
              rw [h2', map_zero])) hr
          · exact h2
    g ∈ differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) →
      adicLocExp Q0 Q hQ ≤ n := by
  letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
    RingHom.toAlgebra
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
  haveI : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr ?_
        have h1 : algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) r * m = 0 := by
          rwa [Algebra.smul_def] at h
        rcases mul_eq_zero.mp h1 with h2 | h2
        · have h2' : (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ) r
              = 0 := by
            simpa [RingHom.algebraMap_toAlgebra] using h2
          exact absurd (adicCompletionMapIntegers_injective Q0 Q hQ (by
            rw [h2', map_zero])) hr
        · exact h2
  intro hmem
  haveI : IsDiscreteValuationRing (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
  have hprime : (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hspan_ne : Ideal.span {g} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hg
  have hspan_le : Ideal.span {g} ≤ differentIdeal (Q0.adicCompletionIntegers ℚ)
      (Q.adicCompletionIntegers K) := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have hle := count_normalizedFactors_le_of_le (R := Q.adicCompletionIntegers K) hprime hbot
    hspan_ne hspan_le
  have hord : ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) g
      = (adicValExp Q (g : Q.adicCompletion K)).toNat :=
    ordAt_maximalIdeal_eq_toNat_adicValExp Q g (by
      rintro h
      exact hg (Subtype.ext h))
  simp only [adicLocExp]
  exact le_trans (by simpa [ordAt] using hle) (le_trans (le_of_eq hord) hn)

end LocalBounds
