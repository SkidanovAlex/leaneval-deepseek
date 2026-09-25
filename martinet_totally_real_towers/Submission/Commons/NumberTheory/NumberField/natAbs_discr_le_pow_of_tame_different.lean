/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tame discriminant bound for number-field towers

The main result of this file is `natAbs_discr_le_pow_of_tame_different`: for a finite extension
`L/F` of number fields, if the relative different ideal is supported over a finite set `S` of
rational primes and the ramification at every prime over `S` is tame, then

  `|disc L| ≤ (|disc F| ⋅ ∏_{q ∈ S} q) ^ [L : ℚ]`.

This is the "tame tower" input of Martinet's asymptotically-good totally real towers
(the arithmetic heart of the tame route to the benchmark statement).

The proof combines
* the tower formula `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`,
* the tame different theorem in relative form (every prime over a tame prime has different
  exponent at most `e - 1`), and
* the resulting norm bound on the relative different.

The relative tame different theorem is proved by the trace-witness method: a trace-one element
of the (finite) residue extension is lifted modulo `P^e` and modulo the complementary factor `Q`
of `(P.under (𝓞 F)) 𝓞 L = P^e ⋅ Q`; its relative integer trace is then not in `P.under (𝓞 F)`,
which by Dedekind's different theorem excludes `P ^ e ∣ 𝔡_{L/F}`.
-/
import Mathlib
import Submission.Commons.RingTheory.DedekindDomain.mem_of_forall_mul_inv_mem
import Submission.Commons.NumberTheory.NumberField.tame_different
import Submission.Commons.NumberTheory.NumberField.not_dvd_pow_of_relative_witness
import Submission.Commons.NumberTheory.NumberField.absNorm_differentIdeal_le_prod_pow_of_tame_support
import Submission.Commons.NumberTheory.NumberField.tame_totallyRamified_different_not_pow_dvd
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_finrank_of_isGalois
import Mathlib.Algebra.CharZero.Infinite

open scoped NumberField BigOperators nonZeroDivisors
open NumberField
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField

namespace TameDiscrAux

/-- Chinese-remainder-style lift: if `P` and `Q` are coprime ideals of a commutative ring, then
any element `z` can be modified, modulo `P ^ e`, into an element of `Q`. -/
lemma exists_lift_of_sup_eq_top {R : Type*} [CommRing R] (P Q : Ideal R) (e : ℕ)
    (hsup : P ⊔ Q = ⊤) (z : R) : ∃ y : R, y - z ∈ P ^ e ∧ y ∈ Q := by
  classical
  have hcop : IsCoprime P Q := (Ideal.isCoprime_iff_sup_eq).mpr hsup
  have hcop' : IsCoprime (P ^ e) Q := IsCoprime.pow_left hcop
  have hsup' : P ^ e ⊔ Q = ⊤ := (Ideal.isCoprime_iff_sup_eq).mp hcop'
  have hone : (1 : R) ∈ P ^ e ⊔ Q := by rw [hsup']; trivial
  rcases (Submodule.mem_sup.mp hone) with ⟨a, ha, b, hb, hab⟩
  refine ⟨z * b, ?_, ?_⟩
  · have hb1 : b - 1 = -a := by
      rw [eq_neg_iff_add_eq_zero, add_comm, ← add_sub_assoc, hab]
      simp
    have hneg : -(z * a) ∈ P ^ e := (P ^ e).neg_mem (Ideal.mul_mem_left (P ^ e) z ha)
    rw [show z * b - z = -(z * a) by
      calc z * b - z = z * (b - 1) := by rw [mul_sub]; simp
        _ = z * (-a) := by rw [hb1]
        _ = -(z * a) := by rw [mul_neg]]
    exact hneg
  · exact Q.mul_mem_left z hb

/-- Compatibility of the trace with the quotient by a product of two coprime ideals: for ideals
`P ^ e` and `Q` of `B` with `(P ^ e) · Q = p 𝓞 L`, the trace over `B ⧸ pB` of the class of `y` is
the trace over `B ⧸ P ^ e` of the class of any `z` with `y ≡ z` modulo `P ^ e` and `y ∈ Q`.

(General form of `trace_mod_eq_trace_pow_quotient` with an arbitrary Dedekind base ring.) -/
theorem trace_mod_eq_trace_pow_quotient {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    {Q : Ideal B} (hsup : P ⊔ Q = ⊤)
    (hspl : Ideal.map (algebraMap A B) p = P ^ p.ramificationIdx' P * Q)
    (z y : B) (hyP : y - z ∈ P ^ p.ramificationIdx' P) (hyQ : y ∈ Q) :
    Algebra.trace (A ⧸ p) (B ⧸ Ideal.map (algebraMap A B) p) (Ideal.Quotient.mk _ y) =
      Algebra.trace (A ⧸ p) (B ⧸ P ^ p.ramificationIdx' P) (Ideal.Quotient.mk _ z) := by
  classical
  let I : Ideal B := Ideal.map (algebraMap A B) p
  let J : Ideal B := P ^ p.ramificationIdx' P
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  have hI_le_Q : I ≤ Q := by
    have hIeq : I = P ^ p.ramificationIdx' P * Q := hspl
    rw [hIeq]
    exact Ideal.mul_le_right
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (by simpa [I] using hI_le_Q))
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ Q) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite (A ⧸ p) (B ⧸ J) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ J)
  have hJQ : J ⊔ Q = ⊤ := by
    simpa [J] using (Ideal.pow_sup_eq_top (n := p.ramificationIdx' P) hsup)
  have hJQ_cop : IsCoprime J Q := (Ideal.isCoprime_iff_sup_eq).2 hJQ
  let eRing : (B ⧸ I) ≃+* ((B ⧸ J) × (B ⧸ Q)) :=
    (Ideal.quotEquivOfEq (by
        show Ideal.map (algebraMap A B) p = P ^ p.ramificationIdx' P * Q
        exact hspl)).trans (Ideal.quotientMulEquivQuotientProd J Q hJQ_cop)
  have eRing_mk (x : B) :
      eRing (Ideal.Quotient.mk I x) = (Ideal.Quotient.mk J x, Ideal.Quotient.mk Q x) := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    apply Prod.ext
    · rw [Ideal.quotientMulEquivQuotientProd_fst]
      exact Ideal.Quotient.factor_mk Ideal.mul_le_left x
    · rw [Ideal.quotientMulEquivQuotientProd_snd]
      exact Ideal.Quotient.factor_mk Ideal.mul_le_right x
  let e : (B ⧸ I) ≃ₐ[A ⧸ p] ((B ⧸ J) × (B ⧸ Q)) :=
    { __ := eRing, commutes' := by
        intro r
        rcases Ideal.Quotient.mk_surjective r with ⟨t, rfl⟩
        change eRing (Ideal.Quotient.mk I ((algebraMap A B) t)) =
          ((Ideal.Quotient.mk J ((algebraMap A B) t)),
            (Ideal.Quotient.mk Q ((algebraMap A B) t)))
        rw [eRing_mk] }
  have hE : e (Ideal.Quotient.mk I y) = (Ideal.Quotient.mk J z, (0 : B ⧸ Q)) := by
    have he0 : e (Ideal.Quotient.mk I y) = (Ideal.Quotient.mk J y, Ideal.Quotient.mk Q y) :=
      eRing_mk y
    rw [he0]
    exact Prod.ext (Ideal.Quotient.mk_eq_mk_iff_sub_mem y z |>.2 hyP)
      (Ideal.Quotient.eq_zero_iff_mem |>.2 hyQ)
  calc
    Algebra.trace (A ⧸ p) (B ⧸ I) (Ideal.Quotient.mk I y)
        = Algebra.trace (A ⧸ p) ((B ⧸ J) × (B ⧸ Q)) (e (Ideal.Quotient.mk I y)) := by
          rw [← Algebra.trace_eq_of_algEquiv e]
    _ = Algebra.trace (A ⧸ p) ((B ⧸ J) × (B ⧸ Q))
          ((Ideal.Quotient.mk J z), (0 : B ⧸ Q)) := by rw [hE]
    _ = Algebra.trace (A ⧸ p) (B ⧸ J) (Ideal.Quotient.mk J z) +
        Algebra.trace (A ⧸ p) (B ⧸ Q) 0 := by rw [Algebra.trace_prod_apply]
    _ = Algebra.trace (A ⧸ p) (B ⧸ J) (Ideal.Quotient.mk J z) := by simp

/-- **Trace witness for tame ramification (relative case).** Let `P` be a maximal ideal of
`𝓞 L` over the prime `p = P.under (𝓞 F)` of `𝓞 F`, with `p 𝓞 L = P ^ e · Q` and `P`, `Q` coprime.
If the e-th power of the residue characteristic does not divide `e` (the tameness condition,
expressed as `(e : 𝓞 F ⧸ p) ≠ 0`), then there is `y ∈ Q` whose relative integer trace is not in
`p`. -/
theorem exists_witness_of_tame
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L]
    (P : Ideal (𝓞 L)) [P.IsMaximal]
    {Q : Ideal (𝓞 L)} (hsup : P ⊔ Q = ⊤)
    (hspl : (P.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 L)) =
      P ^ (P.under (𝓞 F)).ramificationIdx' P * Q)
    (hp : P.under (𝓞 F) ≠ ⊥)
    (hunit : (((P.under (𝓞 F)).ramificationIdx' P : ℕ) : 𝓞 F ⧸ P.under (𝓞 F)) ≠ 0) :
    ∃ y : 𝓞 L, y ∈ Q ∧ Algebra.intTrace (𝓞 F) (𝓞 L) y ∉ P.under (𝓞 F) := by
  classical
  set p := P.under (𝓞 F) with hpdef
  haveI hp_max : p.IsMaximal := by
    rw [hpdef]; exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  haveI hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  letI : Field (𝓞 F ⧸ p) := Ideal.Quotient.field p
  letI : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  obtain ⟨u, hu⟩ : ∃ u : 𝓞 L ⧸ P, Algebra.trace (𝓞 F ⧸ p) (𝓞 L ⧸ P) u = 1 :=
    Algebra.trace_surjective (𝓞 F ⧸ p) (𝓞 L ⧸ P) 1
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective u
  have htrz : (Algebra.trace (𝓞 F ⧸ p) (𝓞 L ⧸ P)) (Ideal.Quotient.mk P z) = 1 := by
    rw [hz]; exact hu
  have hpow : Algebra.trace (𝓞 F ⧸ p) (𝓞 L ⧸ P ^ p.ramificationIdx' P)
      (Ideal.Quotient.mk _ z) = (p.ramificationIdx' P : ℕ) • (1 : 𝓞 F ⧸ p) := by
    rw [TracePow.trace_pow_quotient_eq_nsmul_idx' p P z hp hP_ne, htrz]
  have hz_ne : Algebra.trace (𝓞 F ⧸ p) (𝓞 L ⧸ P ^ p.ramificationIdx' P)
      (Ideal.Quotient.mk _ z) ≠ 0 := by
    rw [hpow]; simpa using hunit
  obtain ⟨y, hyP, hyQ⟩ := exists_lift_of_sup_eq_top P Q (p.ramificationIdx' P) hsup z
  refine ⟨y, hyQ, ?_⟩
  intro hmem
  have hzero : Ideal.Quotient.mk p (Algebra.intTrace (𝓞 F) (𝓞 L) y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hmain : Algebra.trace (𝓞 F ⧸ p) (𝓞 L ⧸ Ideal.map (algebraMap (𝓞 F) (𝓞 L)) p)
      (Ideal.Quotient.mk _ y) = 0 := by
    rw [Algebra.trace_quotient_eq_of_isDedekindDomain (R := 𝓞 F) (S := 𝓞 L) p y]
    exact hzero
  rw [trace_mod_eq_trace_pow_quotient (A := 𝓞 F) (B := 𝓞 L) hsup hspl z y hyP hyQ] at hmain
  exact hz_ne hmain

/-- **The relative tame different theorem.** Let `L/F` be a finite extension of number fields and
`P` a maximal ideal of `𝓞 L` lying over the rational prime `q`, such that the ramification index
`e = P.ramificationIdx (𝓞 F)` is coprime to `q`. Then `P ^ e` does not divide the relative
different ideal `differentIdeal (𝓞 F) (𝓞 L)`.

Together with Mathlib's `Ideal.pow_sub_one_dvd_differentIdeal` (giving `P ^ (e-1) ∣ 𝔡`)
this pins the exponent of `P` in the relative different to be exactly `e - 1`. -/
theorem relative_tame_different_not_pow_dvd
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] (q : ℕ) [Fact (Nat.Prime q)]
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))]
    (htame : ¬ q ∣ P.ramificationIdx (𝓞 F)) :
    ¬ P ^ P.ramificationIdx (𝓞 F) ∣ differentIdeal (𝓞 F) (𝓞 L) := by
  classical
  set p := P.under (𝓞 F) with hpdef
  haveI hp_max : p.IsMaximal := by
    rw [hpdef]; exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hq_mem : algebraMap ℤ (𝓞 F) (q : ℤ) ∈ p := by
    rw [hpdef, Ideal.mem_comap]
    have h1 : (q : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.LiesOver.over (p := Ideal.span ({(q : ℤ)} : Set ℤ)) (P := P)]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 F) (𝓞 L) (q : ℤ)]
    exact h1
  have hp_ne : p ≠ ⊥ := by
    intro hbot
    have h0 : algebraMap ℤ (𝓞 F) (q : ℤ) = 0 := by simpa [hbot] using hq_mem
    have h1 : (q : ℤ) = 0 :=
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 F)) (by simpa using h0)
    exact (Fact.out : Nat.Prime q).ne_zero (by exact_mod_cast h1)
  have heq : p.ramificationIdx' P = P.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx'_eq_ramificationIdx p P hp_ne
  have hmap_ne : p.map (algebraMap (𝓞 F) (𝓞 L)) ≠ ⊥ := by
    intro hbot
    exact hp_ne ((Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))).mp hbot)
  have hcount : (normalizedFactors (p.map (algebraMap (𝓞 F) (𝓞 L)))).count P =
      P.ramificationIdx (𝓞 F) := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hmap_ne]
  obtain ⟨Q, hsup, hQeq⟩ := Ideal.eq_prime_pow_mul_coprime (T := 𝓞 L) hmap_ne P
  have hspl : p.map (algebraMap (𝓞 F) (𝓞 L)) = P ^ p.ramificationIdx' P * Q := by
    rw [hQeq]
    exact congrArg (fun n => P ^ n * Q) (hcount.trans heq.symm)
  have hunit : (((p.ramificationIdx' P : ℕ)) : 𝓞 F ⧸ p) ≠ 0 := by
    intro h0
    have hmem : (((p.ramificationIdx' P : ℕ)) : 𝓞 F) ∈ p :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hmemP : algebraMap (𝓞 F) (𝓞 L) (((p.ramificationIdx' P : ℕ)) : 𝓞 F) ∈ P := by
      rw [hpdef] at hmem
      exact Ideal.mem_comap.mp hmem
    have hmemZ : (p.ramificationIdx' P : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply ℤ (𝓞 F) (𝓞 L)]
      simpa using hmemP
    rw [← Ideal.LiesOver.over (p := Ideal.span ({(q : ℤ)} : Set ℤ)) (P := P)] at hmemZ
    have hdvd : q ∣ p.ramificationIdx' P :=
      Int.ofNat_dvd.mp (Ideal.mem_span_singleton.mp hmemZ)
    exact htame (heq ▸ hdvd)
  obtain ⟨y, hyQ, hyint⟩ := exists_witness_of_tame P hsup hspl hp_ne hunit
  exact not_dvd_pow_of_relative_witness P hsup (by rw [hspl, heq]) y hyQ hyint

end TameDiscrAux

attribute [local instance] FractionRing.liftAlgebra

/-- **Martinet's asymptotically-good totally real towers: tame relative discriminant bound.**
Let `L/F` be a finite extension of number fields and `S` a finite set of rational primes such
that

* every prime ideal of `𝓞 L` dividing the relative different ideal `𝔡_{L/F}` lies over some
  `q ∈ S` (`hsup`), and
* for every `q ∈ S`, every maximal ideal `P` of `𝓞 L` over `(q)` is tame over `𝓞 F`, i.e.
  `q ∤ P.ramificationIdx (𝓞 F)` (`htame`).

Then `|disc L| ≤ (|disc F| · ∏_{q ∈ S} q) ^ [L : ℚ]`.

The proof: the tower formula
`|disc L| = N(𝔡_{L/F}) · |disc F| ^ [L : F]` reduces the claim to the norm bound
`N(𝔡_{L/F}) ≤ (∏_{q ∈ S} q) ^ [L : ℚ]` (where `N` is `Ideal.absNorm`, the index) for the
relative different, which is the standard tame count. -/
theorem natAbs_discr_le_pow_of_tame_different
    {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] (S : Finset ℕ)
    (hS : ∀ q ∈ S, Nat.Prime q)
    (hsup : ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) →
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)))
    (htame : ∀ q ∈ S, ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → ¬ q ∣ P.ramificationIdx (NumberField.RingOfIntegers F)) :
    (NumberField.discr L).natAbs ≤
      ((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ L := by
  classical
  have hnot : ∀ q ∈ S, ∀ (P : Ideal (𝓞 L)), P.IsMaximal →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) →
        ¬ P ^ P.ramificationIdx (𝓞 F) ∣ differentIdeal (𝓞 F) (𝓞 L) := by
    intro q hq P hPmax hPlie
    haveI : Fact (Nat.Prime q) := ⟨hS q hq⟩
    haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hPlie
    exact TameDiscrAux.relative_tame_different_not_pow_dvd q P (htame q hq P hPmax hPlie)
  have hT := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) L (𝓞 L)
  have hB := absNorm_differentIdeal_le_prod_pow_of_tame_support S hS hsup hnot
  have hdF : 1 ≤ (NumberField.discr F).natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F))
  have hnd : Module.finrank F L ≤ Module.finrank ℚ L := by
    have h := Module.finrank_mul_finrank (F := ℚ) (K := F) (A := L)
    have h1 : 1 ≤ Module.finrank ℚ F := Module.finrank_pos
    calc Module.finrank F L = 1 * Module.finrank F L := (one_mul _).symm
      _ ≤ Module.finrank ℚ F * Module.finrank F L := Nat.mul_le_mul_right _ h1
      _ = Module.finrank ℚ L := h
  calc (NumberField.discr L).natAbs
      = Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) *
          (NumberField.discr F).natAbs ^ Module.finrank F L := hT
    _ ≤ (∏ q ∈ S, q) ^ Module.finrank ℚ L *
          (NumberField.discr F).natAbs ^ Module.finrank F L := Nat.mul_le_mul_right _ hB
    _ ≤ (∏ q ∈ S, q) ^ Module.finrank ℚ L *
          (NumberField.discr F).natAbs ^ Module.finrank ℚ L :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hdF hnd)
    _ = ((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ L := by
        rw [mul_pow, mul_comm]

end Commons.NumberTheory.NumberField
