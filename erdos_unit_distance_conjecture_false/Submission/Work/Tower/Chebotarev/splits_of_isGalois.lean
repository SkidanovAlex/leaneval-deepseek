import Mathlib
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Tower.Chebotarev.forall_inertiaDeg_eq_one
import Submission.Work.Tower.Chebotarev.forall_ramificationIdx_eq_one_of_not_dvd_discr
import Submission.Work.Tower.Chebotarev.card_primesOver_eq_finrank

namespace Work.Tower.Chebotarev

open NumberField Polynomial Ideal UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- A ring of integers modulo a prime ideal `P` above `q` whose residue field has cardinality
`q` is isomorphic to `ZMod q`.  The isomorphism is obtained from the ring homomorphism
`ZMod q → 𝓞 K ⧸ P` induced by the `(ℤ ⧸ (q))`-algebra structure of `𝓞 K ⧸ P`: it is injective
(its source is a field and its target is nontrivial) and hence bijective because both sides have
`q` elements. -/
lemma exists_ringEquiv_zmod_of_cardQuot {K : Type} [Field K] [NumberField K] (q : ℕ)
    [Fact (Nat.Prime q)] (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hL : P.LiesOver (Ideal.span {(q : ℤ)})) (hcard : Nat.card (𝓞 K ⧸ P) = q) :
    Nonempty (𝓞 K ⧸ P ≃+* ZMod q) := by
  haveI hP' := hP
  haveI hL' := hL
  haveI : Nontrivial (𝓞 K ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  have hqnz : q ≠ 0 := (Fact.out : Nat.Prime q).ne_zero
  haveI : NeZero q := ⟨hqnz⟩
  haveI : FaithfulSMul (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 K ⧸ P) := inferInstance
  let isoF : ZMod q ≃+* (ℤ ⧸ Ideal.span {(q : ℤ)}) :=
    (ZMod.ringEquivCongr (Int.natAbs_natCast q)).symm.trans
      (Int.quotientSpanEquivZMod (q : ℤ)).symm
  let g : ZMod q →+* (𝓞 K ⧸ P) :=
    (algebraMap (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 K ⧸ P)).comp isoF.toRingHom
  have hg : Function.Injective g := by
    intro a b h
    exact isoF.injective
      (FaithfulSMul.algebraMap_injective (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 K ⧸ P) h)
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hqnz)
  haveI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcardZ : Fintype.card (ZMod q) = Fintype.card (𝓞 K ⧸ P) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
  have e := Fintype.equivOfCardEq hcardZ
  have hsurj : Function.Surjective g := Function.Injective.surjective_of_finite e hg
  exact ⟨(RingEquiv.ofBijective g ⟨hg, hsurj⟩).symm⟩

/-- The main assembly of the elementary split-prime theorem: for a Galois number field `K/ℚ`, a
primitive integral element `θ`, and a prime `q` that is coprime to the exponent of `θ` (so
Kummer–Dedekind applies), does not divide the discriminant of `K` (so `q` is unramified), and
divides a value of `minpoly ℤ θ` (so `minpoly ℤ θ` has a root mod `q`), the prime `q` splits
completely in `K`. -/
theorem splits_of_isGalois {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (θ : 𝓞 K) (q : ℕ)
    (hq : Nat.Prime q) (hp : ¬ q ∣ RingOfIntegers.exponent θ)
    (hq2 : ¬ (q : ℤ) ∣ NumberField.discr K) (a : ℤ)
    (ha : (q : ℤ) ∣ (minpoly ℤ θ).eval a) :
    Work.Tower.Splits q K := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  classical
  -- Elementary facts about the rational prime `q`.
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqZ0 : (q : ℤ) ≠ 0 := hqZ.ne_zero
  haveI hprimeZ : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime hqZ0).mpr hqZ
  have hneZ : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hqZ0
  haveI hmaxZ : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal := hprimeZ.isMaximal hneZ
  have hne : Ideal.span {(q : 𝓞 K)} ≠ ⊥ := by
    intro h
    rw [Ideal.span_singleton_eq_bot] at h
    exact hqZ0 (FaithfulSMul.algebraMap_injective ℤ (𝓞 K) (by simpa using h))
  -- Membership in the normalised factorisation of `q 𝓞 K` is exactly "prime ideal above `q`".
  have mem_iff : ∀ P : Ideal (𝓞 K),
      P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)}) ↔
        P.IsPrime ∧ P.LiesOver (Ideal.span {(q : ℤ)}) := by
    intro P
    rw [Ideal.mem_normalizedFactors_iff hne]
    constructor
    · rintro ⟨hP, hle⟩
      haveI := hP
      refine ⟨hP, ?_⟩
      have hlea : Ideal.span {(q : ℤ)} ≤ P.under ℤ := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
        rw [show algebraMap ℤ (𝓞 K) (q : ℤ) = (q : 𝓞 K) from by simp]
        exact (Ideal.span_singleton_le_iff_mem P).mp hle
      have hneP : P.under ℤ ≠ ⊤ := Ideal.comap_ne_top (algebraMap ℤ (𝓞 K)) hP.ne_top
      exact ⟨hmaxZ.eq_of_le hneP hlea⟩
    · rintro ⟨hP, hL⟩
      haveI := hP
      haveI := hL
      refine ⟨hP, ?_⟩
      rw [Ideal.span_singleton_le_iff_mem]
      have hmem : algebraMap ℤ (𝓞 K) (q : ℤ) ∈ P :=
        (Ideal.mem_of_liesOver (P := P) (p := Ideal.span {(q : ℤ)}) (q : ℤ)).mp
          (Ideal.mem_span_singleton_self (q : ℤ))
      simpa using hmem
  -- The two inputs of the elementary split-prime theorem.
  have h1 : ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.ramificationIdx ℤ = 1 :=
    forall_ramificationIdx_eq_one_of_not_dvd_discr (K := K) q hq2
  have h2 : ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.inertiaDeg ℤ = 1 :=
    forall_inertiaDeg_eq_one (K := K) θ q hp a ha
  -- The residue field at `(q)` in `ℤ` has cardinality `q`.
  have hp_card : (Ideal.span {(q : ℤ)}).cardQuot = q := by
    rw [Submodule.cardQuot_apply]
    haveI : NeZero (Int.natAbs (q : ℤ)) := ⟨by simpa using hq.ne_zero⟩
    rw [Nat.card_congr (Int.quotientSpanEquivZMod (q : ℤ)).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card]; simp
  -- Every prime above `q` has residue field `𝔽_q`.
  have hres : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)}),
      Nonempty (𝓞 K ⧸ P ≃+* ZMod q) := by
    intro P hPmem
    obtain ⟨hP, hL⟩ := (mem_iff P).mp hPmem
    haveI := hP
    haveI := hL
    haveI hPmax : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hneZ P)
    have hPi : P.inertiaDeg ℤ = 1 := h2 ⟨P, hP, hL⟩
    have hcard : Nat.card (𝓞 K ⧸ P) = q := by
      have hcq := Ideal.cardQuot_pow_inertiaDeg (R := ℤ) (Ideal.span {(q : ℤ)}) P
      rw [hPi, pow_one] at hcq
      rw [← Submodule.cardQuot_apply P, ← hcq, hp_card]
    exact exists_ringEquiv_zmod_of_cardQuot q P hP hL hcard
  -- There are exactly `[K : ℚ]` primes above `q`.
  have hcard : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset.card
      = Module.finrank ℚ K := by
    let e : {P : Ideal (𝓞 K) //
          P ∈ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset} ≃
          ↥((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun P => by
        rw [Multiset.mem_toFinset, mem_iff P]
        exact Iff.rfl)
    calc (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset.card
        = Fintype.card {P : Ideal (𝓞 K) //
            P ∈ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(q : 𝓞 K)})).toFinset} :=
          (Fintype.card_coe _).symm
      _ = Fintype.card ↥((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := Fintype.card_congr e
      _ = Nat.card ↥((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := Nat.card_eq_fintype_card.symm
      _ = Module.finrank ℚ K := card_primesOver_eq_finrank q h1 h2
  refine ⟨hq.pos, ?_, hres, hcard⟩
  intro P hPmem
  obtain ⟨hP, hL⟩ := (mem_iff P).mp hPmem
  exact ⟨h1 ⟨P, hP, hL⟩, h2 ⟨P, hP, hL⟩⟩

end Work.Tower.Chebotarev
