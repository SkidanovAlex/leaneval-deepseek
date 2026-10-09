import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpInertia
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.helpersTotallyRamified
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocVal
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField

/-- The `P`-adic order of `0` vanishes, for an arbitrary ideal `P`. -/
lemma ordAt_apply_zero {R : Type*} [CommRing R] [IsDedekindDomain R] (P : Ideal R) :
    ordAt P (0 : R) = 0 := by
  rw [ordAt, (Ideal.span_singleton_eq_bot).mpr rfl, ← Ideal.zero_eq_bot,
    UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.count_zero]

theorem inertia_ordAt_algebraMap {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1))
    (hfin : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ))
    (hmax : (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))).IsMaximal)
    (hunder : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) =
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))) :
    ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c := by
  intro c
  by_cases hc : c = 0
  · subst hc
    simp only [map_zero, ordAt_apply_zero, mul_zero]
  · haveI : CharZero (Q.adicCompletion K) :=
      Commons.NumberTheory.NumberField.charZero_adicCompletion Q
    set 𝔪 : Ideal (Q.adicCompletionIntegers K) :=
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) with h𝔪
    set 𝔭 : Ideal ↥(inertiaRing Q0 Q ζ) :=
      Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) with h𝔭
    have hunder' : 𝔭 = 𝔪.comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
      rw [h𝔭, h𝔪]; exact hunder
    have hinj : Function.Injective
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
      rw [RingHom.algebraMap_toAlgebra]
      exact inertiaMap_injective Q0 Q ζ
    -- `p` is a nonzero element of the inertia ring
    have hpC : (p : ↥(inertiaRing Q0 Q ζ)) ≠ 0 := by
      intro h
      have h2 : (p : Q.adicCompletionIntegers K) = 0 := by
        have h1 : (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))
            (p : ↥(inertiaRing Q0 Q ζ)) = 0 := by
          rw [h, map_zero]
        simpa using h1
      have h3 : (p : Q.adicCompletion K) = 0 := by
        have h4 : ((p : Q.adicCompletionIntegers K) : Q.adicCompletion K) = 0 := by
          rw [h2]; rfl
        rwa [show ((p : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
            (p : Q.adicCompletion K) from
          map_natCast (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p] at h4
      exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero h3
    have h𝔭prime : 𝔭.IsPrime := by rw [h𝔭]; exact hmax.isPrime
    have h𝔭ne : 𝔭 ≠ ⊥ := by rw [h𝔭, Ne, Ideal.span_singleton_eq_bot]; exact hpC
    let v : IsDedekindDomain.HeightOneSpectrum ↥(inertiaRing Q0 Q ζ) := ⟨𝔭, h𝔭prime, h𝔭ne⟩
    -- the exponent `n` of `c` at `𝔭`
    set n : ℕ := ordAt 𝔭 c with hn
    have hmem : c ∈ 𝔭 ^ n := (mem_pow_iff_le_ordAt v hc n).mpr le_rfl
    have hnotmem : c ∉ 𝔭 ^ (n + 1) := fun h => by
      have h' : n + 1 ≤ ordAt 𝔭 c := (mem_pow_iff_le_ordAt v hc (n + 1)).mp h
      omega
    have hpow : ∀ k : ℕ, 𝔭 ^ k =
        Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ)) ^ k} : Set ↥(inertiaRing Q0 Q ζ)) :=
      fun k => by rw [h𝔭, Ideal.span_singleton_pow]
    -- write `c = p^n * a` with `a` not in `𝔭`
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hpow n ▸ hmem)
    have ha_notmem : a ∉ 𝔭 := by
      intro ha_mem
      apply hnotmem
      rw [ha]
      have hp_mem : (p : ↥(inertiaRing Q0 Q ζ)) ∈ 𝔭 := by
        rw [h𝔭]; exact Ideal.mem_span_singleton_self _
      have h1 : (p : ↥(inertiaRing Q0 Q ζ)) ^ n ∈ 𝔭 ^ n := Ideal.pow_mem_pow hp_mem n
      have h2 : (p : ↥(inertiaRing Q0 Q ζ)) ^ n * a ∈ 𝔭 ^ n * 𝔭 := Ideal.mul_mem_mul h1 ha_mem
      rwa [← pow_succ] at h2
    set y : Q.adicCompletionIntegers K :=
      algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) a with hy
    have hy_notmem : y ∉ 𝔪 := by
      intro h
      have h' : (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) a ∈ 𝔪 := by
        rw [hy] at h
        exact h
      exact ha_notmem (by rw [hunder']; exact Ideal.mem_comap.mpr h')
    have hyunit : IsUnit y := by
      by_contra h
      refine hy_notmem ?_
      rw [h𝔪]
      exact (IsLocalRing.mem_maximalIdeal _).mpr ((mem_nonunits_iff).mpr h)
    have hy_ne : algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y ≠ 0 :=
      (hyunit.map (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K))).ne_zero
    have hadic_zero : adicValExp Q
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y) = 0 := by
      have h0 : (0 : ℤ) ≤ adicValExp Q
          (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y) :=
        (mem_maximalIdeal_pow_iff_le_adicValExp Q (by
          rw [show ((y : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
              algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y from rfl]
          exact hy_ne) 0).mp (by simp)
      have h1 : ¬ ((1 : ℤ) ≤ adicValExp Q
          (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y)) := fun h => by
        refine hy_notmem ?_
        rw [h𝔪]
        have h2 : y ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ^ 1 :=
          (mem_maximalIdeal_pow_iff_le_adicValExp Q (by
            rw [show ((y : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
                algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y from rfl]
            exact hy_ne) 1).mpr (by simpa using h)
        simpa using h2
      omega
    -- the value of `p`
    have hpne : algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (p : Q.adicCompletionIntegers K) ≠ 0 := by
      rw [show algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (p : Q.adicCompletionIntegers K) = (p : Q.adicCompletion K) from
        map_natCast (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p]
      exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hvalp : adicValExp Q (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (p : Q.adicCompletionIntegers K)) =
        (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) : ℤ) := by
      have h := adicValExp_natCast p Q Q0 hQ0 hQ p (Fact.out : p.Prime).ne_zero
      rw [padicValNat_self] at h
      rw [← (show algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
          (p : Q.adicCompletionIntegers K) = (p : Q.adicCompletion K) from
        map_natCast (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p)] at h
      simpa using h
    -- the decomposition of `algebraMap c`
    have hφcB : algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c =
        (p : Q.adicCompletionIntegers K) ^ n * y := by
      rw [hy, ha, map_mul, map_pow, map_natCast]
    have hφcM : algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
            (p : Q.adicCompletionIntegers K)) ^ n *
          algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y := by
      rw [hφcB, map_mul, map_pow, map_natCast]
    have hφc_ne : ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c :
          Q.adicCompletionIntegers K) : Q.adicCompletion K) ≠ 0 := by
      rw [show ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c :
            Q.adicCompletionIntegers K) : Q.adicCompletion K) =
          algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
            (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) from rfl]
      rw [hφcM]
      exact mul_ne_zero (pow_ne_zero n hpne) hy_ne
    -- the valuation computation
    have hval : adicValExp Q ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c :
          Q.adicCompletionIntegers K) : Q.adicCompletion K) =
        (n : ℤ) * (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) : ℤ) := by
      rw [show ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c :
            Q.adicCompletionIntegers K) : Q.adicCompletion K) =
          algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)
            (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) from rfl]
      rw [hφcM, adicValExp_mul Q (pow_ne_zero n hpne) hy_ne, adicValExp_pow Q hpne n,
        hadic_zero, add_zero, hvalp]
    have hcast : (((n : ℤ) * (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) : ℤ))).toNat =
        n * Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
      rw [← Nat.cast_mul, Int.toNat_natCast]
    rw [h𝔪, ordAt_maximalIdeal_eq_toNat_adicValExp Q
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) hφc_ne, hval, hcast,
      Nat.mul_comm]

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
