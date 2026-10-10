import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star
import Submission.NK.CFTLib.IdeleHasse.Descent.dvd_localDegree_of_isPrimitiveRoot
import Submission.NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p
import Submission.NK.LocalAnabelian.Kummer.kummerCorrespondence
import Submission.NK.LocalAnabelian.PadicField.FrattiniRank
import Submission.NK.LocalAnabelian.PadicField.RatAdic
import Submission.NK.LocalAnabelian.ResidueField.Recovery
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
import Submission.Work.SSGRoute.E7Arch.g1Assembly
import Submission.Work.SSGRoute.E7Arch.levelInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped NumberField IntermediateField

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.E7Arch

/-! ## Two elementary arithmetic lemmas -/

/-- **For `n ≥ 2` the integer `n ^ 2 + 1` has an odd prime divisor.**  If all its prime divisors were
`2`, it would be a power of `2`; but `n ^ 2 + 1 = 2 ^ k` with `k ≥ 3` forces `n ^ 2 ≡ 7 (mod 8)`,
which is impossible for a square. -/
theorem exists_odd_prime_dvd_sq_add_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ n ^ 2 + 1 := by
  by_contra h
  push Not at h
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ n ^ 2 + 1 → q = 2 := by
    intro q hq hdvd
    by_contra hq2
    exact h q hq hq2 hdvd
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd (by positivity : n ^ 2 + 1 ≠ 0) huniq
  set k := (n ^ 2 + 1).primeFactorsList.length with hkdef
  have hk3 : 3 ≤ k := by
    by_contra hk3'
    interval_cases k <;> simp at hk <;> nlinarith [hn]
  have h8 : (2 : ℕ) ^ k % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact pow_dvd_pow 2 hk3
  have hn2 : n ^ 2 % 8 = 7 := by
    have h1 : n ^ 2 = 2 ^ k - 1 := by omega
    rw [h1]
    omega
  have hsq : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := by
    have h : n ≡ n % 8 [MOD 8] := (Nat.mod_modEq n 8).symm
    exact h.pow 2
  have hmem : (n % 8) ^ 2 % 8 = 0 ∨ (n % 8) ^ 2 % 8 = 1 ∨ (n % 8) ^ 2 % 8 = 4 := by
    have hlt : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
    interval_cases n % 8 <;> norm_num
  omega

/-- **If an odd prime `q` divides `n ^ 2 + 1`, then `4` divides the order of `n` in `ℤ/q`**: there
`n ^ 2 = -1`, so `n ^ 4 = 1` while `n ^ 2 ≠ 1`. -/
theorem four_dvd_orderOf_of_dvd_sq_add_one {n q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ n ^ 2 + 1) : 4 ∣ orderOf ((n : ZMod q)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : (n : ZMod q) ^ 2 = -1 := by
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod q) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod q) q]
      exact hdvd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h4 : (n : ZMod q) ^ 4 = 1 := by
    have : (n : ZMod q) ^ 4 = ((n : ZMod q) ^ 2) ^ 2 := by ring
    rw [this, hsq]
    norm_num
  have hne : (-1 : ZMod q) ≠ 1 := by
    intro hcontra
    have h2 : (2 : ZMod q) = 0 := by
      have h3 : (-1 : ZMod q) - 1 = 0 := by rw [hcontra]; ring
      have h4 : (-1 : ZMod q) - 1 = -(2 : ZMod q) := by ring
      rw [h4] at h3
      exact neg_eq_zero.mp h3
    have hq2dvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2dvd with h | h
    · exact hq.ne_one h
    · exact hq2 h
  have hneq1 : (n : ZMod q) ≠ 1 := by
    intro h
    refine hne ?_
    rw [← hsq, h]
    norm_num
  have hne1 : orderOf ((n : ZMod q)) ≠ 1 := by
    intro h
    exact hneq1 (orderOf_eq_one_iff.mp h)
  have hne2 : orderOf ((n : ZMod q)) ≠ 2 := by
    intro h
    refine hne ?_
    rw [← hsq]
    have := pow_orderOf_eq_one (n : ZMod q)
    rw [h] at this
    exact this
  have hdvd4 : orderOf ((n : ZMod q)) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h4
  obtain ⟨c, hc⟩ := hdvd4
  have hc4 : c ≤ 4 := by
    have h1 : 0 < orderOf ((n : ZMod q)) :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
    nlinarith [hc]
  interval_cases c
  · omega
  · have h1 : orderOf ((n : ZMod q)) = 4 := by omega
    rw [h1]
  · exact absurd (by omega : orderOf ((n : ZMod q)) = 2) hne2
  · omega
  · exact absurd (by omega : orderOf ((n : ZMod q)) = 1) hne1

/-! ## The level realising local degree `≥ 3` -/

/-- **A finite normal level of `Ω` realising local degree ≥ 3 at a finite place.** -/
theorem exists_level_localDegree_ge_three
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ L : IntermediateField k Ω, LevelHasLocalDegreeGeThree k Ω A hA L := by
  classical
  -- the prime of `k` below `A`, and the cardinality of its residue field
  let 𝔭 := Submission.NeukirchUchida.primeOf A hA
  have h𝔭spec : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 :=
    Submission.NeukirchUchida.primeOf_spec A hA
  let n := Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
  haveI hfinq : Finite (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔭
  haveI hfieldq : Field (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  have hn2 : 2 ≤ n := by
    haveI : Fintype (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
    show 2 ≤ Nat.card (NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  -- an odd prime `q` with `q ∣ n ^ 2 + 1`
  obtain ⟨q, hq, hq2, hqdiv⟩ := exists_odd_prime_dvd_sq_add_one n hn2
  have hqndvd : ¬ q ∣ n := by
    intro h
    have h1 : q ∣ n ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_left h n
    have h2 : q ∣ n ^ 2 + 1 - n ^ 2 := Nat.dvd_sub hqdiv h1
    rw [Nat.add_sub_cancel_left] at h2
    exact hq.not_dvd_one h2
  have h4dvd : 4 ∣ orderOf ((n : ZMod q)) :=
    four_dvd_orderOf_of_dvd_sq_add_one hq hq2 hqdiv
  -- a primitive `q`-th root of unity in `Ω`, and the level `L = k⟮ζ⟯`
  haveI hsep : IsSepClosed Ω := (inferInstance : IsSepClosure k Ω).sep_closed
  haveI hqcast : NeZero ((q : ℕ) : Ω) := ⟨fun h => hq.ne_zero (by
    have h1 : ((q : ℕ) : k) = 0 := by
      apply (algebraMap k Ω).injective
      rw [map_natCast, h, map_zero]
    exact_mod_cast h1)⟩
  haveI hqne : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := q)
  let L : IntermediateField k Ω := k⟮ζ⟯
  haveI hcyc : IsCyclotomicExtension ({q} : Set ℕ) k ↥L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI hfd : FiniteDimensional k ↥L :=
    IsCyclotomicExtension.finiteDimensional ({q} : Set ℕ) k ↥L
  haveI hnorm : Normal k ↥L := (IsCyclotomicExtension.isGalois ({q} : Set ℕ) k ↥L).to_normal
  refine ⟨L, hfd, hnorm, ?_⟩
  -- the place of `L` below `A`
  have hlies : (levelPlace k Ω A hA L).asIdeal.LiesOver 𝔭.asIdeal :=
    Submission.NeukirchUchida.Local.placeOf_liesOver 𝔭 A h𝔭spec L
  -- a primitive `q`-th root of unity in `𝓞 L`
  have hζL : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩ : ↥L) q :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (by rw [show ((⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩ : ↥L) : Ω) = ζ from rfl]
          exact hζ)
  have hint : IsIntegral ℤ (⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩ : ↥L) :=
    hζL.isIntegral hq.pos
  obtain ⟨ζO, hζOeq⟩ := (IsIntegralClosure.isIntegral_iff
    (A := NumberField.RingOfIntegers ↥L) (R := ℤ) (B := ↥L)).mp hint
  have hζO : IsPrimitiveRoot ((ζO : ↥L)) q := by
    rw [show ((ζO : ↥L)) = (⟨ζ, IntermediateField.mem_adjoin_simple_self k ζ⟩ : ↥L) from hζOeq]
    exact hζL
  -- the general local-degree theorem
  have hdiv := NK.CFTLib.IdeleHasse.Descent.dvd_localDegree_of_isPrimitiveRoot
    (K := k) (M := ↥L) 𝔭 (levelPlace k Ω A hA L) hlies (N := 4) hq hqndvd h4dvd ζO hζO
  -- bridge from `ramificationIdx` to the `In`-form used by `card_levelDecomp_eq`
  letI : MulSemiringAction (↥L ≃ₐ[k] ↥L) (NumberField.RingOfIntegers ↥L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers k) k ↥L
      (NumberField.RingOfIntegers ↥L)
  haveI hGal : IsGaloisGroup (↥L ≃ₐ[k] ↥L) (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers ↥L) :=
    IsGaloisGroup.of_isFractionRing (↥L ≃ₐ[k] ↥L) (NumberField.RingOfIntegers k)
      (NumberField.RingOfIntegers ↥L) k ↥L
  have hram : 𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) =
      (levelPlace k Ω A hA L).asIdeal.ramificationIdx (NumberField.RingOfIntegers k) :=
    Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers ↥L) 𝔭.asIdeal (levelPlace k Ω A hA L).asIdeal
      (↥L ≃ₐ[k] ↥L)
  have hdeg : 𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) =
      (levelPlace k Ω A hA L).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers ↥L) 𝔭.asIdeal (levelPlace k Ω A hA L).asIdeal
      (↥L ≃ₐ[k] ↥L)
  rw [card_levelDecomp_eq k Ω A hA L, hram, hdeg]
  have hpos : 0 < (levelPlace k Ω A hA L).asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      (levelPlace k Ω A hA L).asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
    Nat.mul_pos ((levelPlace k Ω A hA L).asIdeal.ramificationIdx_pos
        (NumberField.RingOfIntegers k))
      ((levelPlace k Ω A hA L).asIdeal.inertiaDeg_pos (NumberField.RingOfIntegers k))
  have h4le := Nat.le_of_dvd hpos hdiv
  omega

/-- **The two families of local groups are disjoint** (`LocalGroupDisjoint` of
`Work.SSGRoute.E7Arch.g1Assembly`), now unconditional: no decomposition group of a finite place is
generated by an involution.  This discharges the hypothesis `hempty` of `glue_of_finiteHalf`. -/
theorem localGroupDisjoint (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] : LocalGroupDisjoint k Ω :=
  fun A hA c hc =>
    decomp_ne_zpowers_of_sq_eq_one_of_levelExists k Ω A hA
      (exists_level_localDegree_ge_three k Ω A hA) c hc

end Work.SSGRoute.E7Arch
