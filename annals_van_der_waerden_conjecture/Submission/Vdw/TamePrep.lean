import Mathlib
import Submission.Vdw.DifferentValuation
import Submission.Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
import Submission.Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg

open Classical
open scoped NumberField
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Tame-ramification preparation (the `m_P = e_P − 1` programme, input side)

For a number field `K` with ring of integers `𝒪`, a rational prime `p` and a
maximal ideal `P` of `𝒪` over `p`, write `e_P := P.ramificationIdx ℤ` and let
`m_P := (normalizedFactors (differentIdeal ℤ 𝒪)).count P` be the exponent of
`P` in the different ideal (so that `padicValNat p |discr K| = Σ_{P|p} f_P m_P`,
the decomposition `L60` of `Commons.NumberTheory.NumberField`).

The **tame-different theorem** states `m_P = e_P − 1` whenever `p ∤ e_P`
(`p` is *tame* at `P`); the free lower bound `m_P ≥ e_P − 1`
(`P^(e_P−1) | 𝔡`, Mathlib `Ideal.pow_sub_one_dvd_differentIdeal`) is already
available (`DifferentValuation.pow_sub_one_dvd_differentIdeal_of_over`), and
the unramified base case `e_P = 1 ⟹ m_P = 0` is `DifferentChar`.  The
missing *upper* bound `m_P ≤ e_P − 1` is the subject of the delegated commons
theorem `tame_different_not_pow_dvd` (divisibility form `¬ P^e_P | 𝔡`).

This module proves the *input side* of the programme, i.e. everything except
the tame upper bound itself, and the *interface lemmas* that the eventual
Lemma-24 (discriminant-index) assembly consumes:

* `ramIdx_mul_inertiaDeg_le_finrank` : `e_P·f_P ≤ [K : ℚ]` for `P` over `p`
  (fundamental identity `Ideal.sum_ramification_inertia_eq_finrank`);
* `tame_of_prime_gt_finrank` : `p > [K : ℚ]` prime ⟹ every prime `P` over
  `p` is tame (`¬ p ∣ e_P`) — this is exactly the `p > n` hypothesis of
  Bhargava's Lemma 24 / Case I, and it is *automatic* there since
  `e_P·f_P ≤ n < p`;
* `different_count_ge_ramIdx_sub_one` : the free lower bound `m_P ≥ e_P − 1`
  in count form (via the commons power-divisibility↔count bridge);
* `different_count_le_iff_not_pow_dvd` : the tame upper bound in count form
  `m_P ≤ e_P − 1` is *equivalent* to the divisibility form
  `¬ P^e_P | 𝔡` — so the delegated theorem gives the count-form equality
  `m_P = e_P − 1` once combined with the free bound;
* `discr_val_eq_sum_f_mul_sub_one` : under the per-prime tame-count
  hypothesis `m_P = e_P − 1` (∀ `P` dividing `𝔡` over `p`), the
  discriminant valuation collapses to the tame shape
  `v_p(|discr K|) = Σ_{P|p} f_P (e_P − 1)` — the exact input of the
  residue-side comparison of Lemma 24.

All statements are proven (0 sorries); nothing here depends on the delegated
tame upper bound itself.
-/

namespace Submission.Vdw

noncomputable section

open Ideal

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- For a prime `P` of `𝒪_K` over `p`, the product `e·f` of the ramification
index and the inertia degree does not exceed the degree `[K : ℚ]`. -/
theorem ramIdx_mul_inertiaDeg_le_finrank (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤ Module.finrank ℚ K := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  haveI : pZ.IsPrime := by
    exact ((Ideal.span_singleton_prime (p := (p : ℤ)) hp0).mpr (Nat.prime_iff_prime_int.mp hp))
  let S := 𝓞 K
  have hfin : Fintype (pZ.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (R := ℤ) (S := S) pZ).fintype
  letI : Fintype (pZ.primesOver S) := hfin
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := S) (p := pZ)
  have hterm : P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤
      ∑ q : pZ.primesOver S, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    have hP : P ∈ (pZ.primesOver S : Set (Ideal S)) := by
      simp [pZ]
      exact ⟨‹P.IsMaximal›.isPrime, ‹P.LiesOver (pZ)›⟩
    let x : pZ.primesOver S := ⟨P, hP⟩
    have hxmem : x ∈ (Finset.univ : Finset (pZ.primesOver S)) := Finset.mem_univ x
    simpa using (Finset.single_le_sum (s := (Finset.univ : Finset (pZ.primesOver S)))
      (f := fun y : pZ.primesOver S => y.1.ramificationIdx ℤ * y.1.inertiaDeg ℤ)
      (by intro y hy; exact Nat.zero_le _) hxmem)
  calc
    P.ramificationIdx ℤ * P.inertiaDeg ℤ
        ≤ ∑ q : pZ.primesOver S, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := hterm
    _ = Module.finrank ℤ S := hsum
    _ = Module.finrank ℚ K := by
      dsimp [S]
      exact NumberField.RingOfIntegers.rank (K := K)

/-- `p > [K : ℚ]` prime ⟹ every prime ideal of `𝒪_K` over `p` is *tame*
(`p ∤ e_P`): the automorphism of Case I's Lemma-24 hypothesis. -/
theorem tame_of_prime_gt_finrank (p : ℕ) (hp : Nat.Prime p)
    (hgt : Module.finrank ℚ K < p) (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ¬ p ∣ P.ramificationIdx ℤ := by
  have hef : P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤ Module.finrank ℚ K :=
    ramIdx_mul_inertiaDeg_le_finrank p hp P
  have hfpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have he_le_n : P.ramificationIdx ℤ ≤ Module.finrank ℚ K := by
    calc
      P.ramificationIdx ℤ ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ := Nat.le_mul_of_pos_right _ hfpos
      _ ≤ Module.finrank ℚ K := hef
  intro hpdvd
  have hlt : P.ramificationIdx ℤ < p := lt_of_le_of_lt he_le_n hgt
  have hpos : 0 < P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
  have hmod0 : P.ramificationIdx ℤ % p = 0 := Nat.mod_eq_zero_of_dvd hpdvd
  have hmod : P.ramificationIdx ℤ % p = P.ramificationIdx ℤ := Nat.mod_eq_of_lt hlt
  omega

/-- The exponent `m_P` of `P` in the different ideal is at least `e_P − 1`
(free direction, count form: `P^(e_P−1) | 𝔡`). -/
theorem different_count_ge_ramIdx_sub_one (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P.ramificationIdx ℤ - 1 ≤ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
  classical
  have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  haveI : P.IsPrime := ‹P.IsMaximal›.isPrime
  have hdiv : P ^ (P.ramificationIdx ℤ - 1) ∣ differentIdeal ℤ (𝓞 K) := by
    exact pow_sub_one_dvd_differentIdeal_of_over (K := K) p hp P
  exact (Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le (K := K) P
    (differentIdeal ℤ (𝓞 K)) hδ (P.ramificationIdx ℤ - 1)).mp hdiv

/-- The tame upper bound `m_P ≤ e_P − 1` in count form is equivalent to the
divisibility form `¬ P^e_P | 𝔡` (the statement of the delegated commons
theorem `tame_different_not_pow_dvd`). -/
theorem different_count_le_iff_not_pow_dvd (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤ P.ramificationIdx ℤ - 1 ↔
      ¬ P ^ P.ramificationIdx ℤ ∣ differentIdeal ℤ (𝓞 K) := by
  classical
  have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  have hpos : 0 < P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
  haveI : P.IsPrime := ‹P.IsMaximal›.isPrime
  constructor
  · intro hle hpe
    have hge : P.ramificationIdx ℤ ≤ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P :=
      (Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le (K := K) P
        (differentIdeal ℤ (𝓞 K)) hδ (P.ramificationIdx ℤ)).mp hpe
    omega
  · intro hnot
    by_contra hle
    have hge : P.ramificationIdx ℤ ≤ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
      omega
    exact hnot ((Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le (K := K) P
      (differentIdeal ℤ (𝓞 K)) hδ (P.ramificationIdx ℤ)).mpr hge)

/-- From `m_P ≥ e_P − 1` (free) and the tame upper bound `m_P ≤ e_P − 1` we
obtain the tame equality `m_P = e_P − 1` (interface assembly; instantiate the
second hypothesis with the delegated tame theorem). -/
theorem different_count_eq_sub_one_of_le (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hupper : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤ P.ramificationIdx ℤ - 1) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = P.ramificationIdx ℤ - 1 := by
  exact le_antisymm hupper (different_count_ge_ramIdx_sub_one (K := K) p hp P)

/-- The discriminant-valuation decomposition `L60` in *tame shape*: if every
prime dividing the different over `p` has `m_P = e_P − 1`, then
`v_p(|discr K|) = Σ_{P|p} f_P (e_P − 1)`.  This is the per-prime input of the
residue-side comparison in Bhargava's Lemma 24 (with tameness supplied by
`tame_of_prime_gt_finrank` and the count equality by the tame theorem). -/
theorem discr_val_eq_sum_f_mul_sub_one
    (p : ℕ) [Fact (Nat.Prime p)]
    (htame : ∀ P : Ideal (𝓞 K),
        P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset →
        P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) →
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = P.ramificationIdx ℤ - 1) :
    padicValNat p (NumberField.discr K).natAbs =
      (((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))).sum
        fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) := by
  classical
  rw [Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg
    (K := K) (p := p)]
  refine Finset.sum_congr rfl ?_
  intro P hP
  have hPmem : P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset :=
    (Finset.mem_filter.mp hP).1
  have hPover : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := (Finset.mem_filter.mp hP).2
  have hm : (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P = P.ramificationIdx ℤ - 1 :=
    htame P hPmem hPover
  rw [hm]
  ring

end
end Submission.Vdw
