import Mathlib
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

namespace Work.Tower.Chebotarev

open NumberField Ideal
open scoped Classical nonZeroDivisors NumberField

/-- Complete splitting descends along a finite extension of number fields: if `q` splits
completely in `L`, then `q` splits completely in any subfield `K` (here expressed as a finite
`ℚ`-algebra extension `K → L`). -/
theorem splits_of_algebra {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L] {q : ℕ}
    (h : Work.Tower.Splits q L) : Work.Tower.Splits q K := by
  have hq0 : 0 < q := h.1
  have hspanL : Ideal.span {(q : 𝓞 L)} ≠ ⊥ := Work.Tower.Splits.span_ne_bot h
  have hspanK : Ideal.span {(q : 𝓞 K)} ≠ ⊥ := by
    intro hc
    rw [Ideal.span_singleton_eq_bot] at hc
    have hco : ((q : 𝓞 K) : K) = (q : K) := by simp
    have hK : (q : K) = 0 := by rw [← hco, hc]; simp
    exact hq0.ne' (Nat.cast_eq_zero.mp hK)
  -- A rational prime that splits completely in a number field is prime: the residue field
  -- at any prime above it is `ZMod q`, hence a field.
  have hqprime : Nat.Prime q := by
    have hne :
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 L)})).toFinset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      have hc : (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {(q : 𝓞 L)})).toFinset.card = 0 := Finset.card_eq_zero.mpr h0
      rw [h.2.2.2] at hc
      exact (Module.finrank_pos (R := ℚ) (M := L)).ne' hc
    obtain ⟨𝔓, h𝔓mem0⟩ := hne
    rw [Multiset.mem_toFinset] at h𝔓mem0
    obtain ⟨h𝔓prime, h𝔓le⟩ := (Ideal.mem_normalizedFactors_iff hspanL).mp h𝔓mem0
    have h𝔓ne : 𝔓 ≠ ⊥ := fun h0 => hspanL (le_bot_iff.mp (h0 ▸ h𝔓le))
    haveI : 𝔓.IsPrime := h𝔓prime
    haveI : 𝔓.IsMaximal := h𝔓prime.isMaximal h𝔓ne
    obtain ⟨σ⟩ := h.2.2.1 𝔓 h𝔓mem0
    have hfield : IsField (ZMod q) :=
      σ.symm.toMulEquiv.isField
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔓).mp ‹𝔓.IsMaximal›)
    haveI : IsDomain (ZMod q) := hfield.isDomain
    rcases CharP.char_is_prime_or_zero (ZMod q) q with hq | hq
    · exact hq
    · exact absurd hq hq0.ne'
  have hpne : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    intro hbot
    exact hq0.ne' (by exact_mod_cast (Ideal.span_singleton_eq_bot.mp hbot))
  haveI hpPrime : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsPrime :=
    Work.Tower.Unramified.isPrime_span_singleton_int hqprime
  haveI hpMax : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal :=
    Work.Tower.Unramified.isMaximal_span_singleton_int hqprime
  -- Primes of `𝓞 K` above `q` are exactly the prime factors of `q 𝓞 K`.
  have hnf : ∀ P : Ideal (𝓞 K),
      P ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) ↔
        P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)}) := by
    intro P
    rw [Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) hpne,
      Work.Tower.Unramified.map_span_singleton_int_eq K q]
  -- Every prime above `q` has ramification index and inertia degree one, by divisibility of
  -- `e` and `f` in the tower `ℚ ⊆ K ⊆ L`.
  have hef : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)}),
      P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
    intro P hP
    obtain ⟨hPprime, hPle⟩ := (Ideal.mem_normalizedFactors_iff hspanK).mp hP
    have hPq : (q : 𝓞 K) ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hPle
    haveI : P.IsPrime := hPprime
    haveI : P.IsMaximal :=
      Work.Tower.Unramified.isMaximal_of_mem_primesOver_span hqprime ((hnf P).mpr hP)
    obtain ⟨𝔓, h𝔓max, h𝔓lie⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 L) P
    haveI : 𝔓.IsPrime := h𝔓max.isPrime
    haveI : 𝔓.LiesOver P := h𝔓lie
    have hq𝔓 : (q : 𝓞 L) ∈ 𝔓 := by
      have h1 : algebraMap (𝓞 K) (𝓞 L) (q : 𝓞 K) ∈ 𝔓 :=
        (Ideal.mem_of_liesOver 𝔓 P (q : 𝓞 K)).mp hPq
      simpa using h1
    have h𝔓memL : 𝔓 ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 L)}) :=
      (Ideal.mem_normalizedFactors_iff hspanL).mpr
        ⟨h𝔓max.isPrime, (Ideal.span_singleton_le_iff_mem 𝔓).mpr hq𝔓⟩
    obtain ⟨he, hf⟩ := h.2.1 𝔓 h𝔓memL
    exact ⟨Nat.dvd_one.mp (he ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P 𝔓),
      Nat.dvd_one.mp (hf ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P 𝔓)⟩
  -- Consequently every prime above `q` has residue field `ZMod q`.
  have hres : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)}),
      Nonempty (𝓞 K ⧸ P ≃+* ZMod q) := fun P hP =>
    Work.Tower.Unramified.nonempty_quot_equiv_zmod_of_inertiaDeg_eq_one hqprime
      ((hnf P).mpr hP) (hef P hP).2
  -- The fundamental identity counts the primes above `q`.
  haveI : Fintype ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span {(q : ℤ)})).fintype
  have hsum : ∑ Q : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K),
      Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ = Module.finrank ℤ (𝓞 K) :=
    Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(q : ℤ)}) (𝓞 K)
  have hcardPO : Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K := by
    have h1 : ∑ _Q : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), (1 : ℕ)
        = Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    rw [← h1, IsFractionRing.finrank_eq ℤ ℚ (𝓞 K) K, ← hsum]
    exact Finset.sum_congr rfl (fun Q _ => by
      rw [(hef Q.1 ((hnf Q.1).mp Q.2)).1, (hef Q.1 ((hnf Q.1).mp Q.2)).2, mul_one])
  have hbridge : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K) ≃
      ↥(UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset :=
    { toFun := fun P => ⟨P.1, Multiset.mem_toFinset.mpr ((hnf P.1).mp P.2)⟩
      invFun := fun P => ⟨P.1, (hnf P.1).mpr (Multiset.mem_toFinset.mp P.2)⟩
      left_inv := fun P => Subtype.ext rfl
      right_inv := fun P => Subtype.ext rfl }
  refine ⟨hq0, hef, hres, ?_⟩
  calc (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset.card
      = Fintype.card ↥(UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {(q : 𝓞 K)})).toFinset := (Fintype.card_coe _).symm
    _ = Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := Fintype.card_congr hbridge.symm
    _ = Module.finrank ℚ K := hcardPO

end Work.Tower.Chebotarev
