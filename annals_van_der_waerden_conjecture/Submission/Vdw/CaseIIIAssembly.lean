import Mathlib
import Submission.Vdw.CaseIIIJointA
import Submission.Vdw.CaseIIIBox
import Submission.Vdw.CaseIIIHeight
import Submission.Vdw.PrimeBound
import Submission.Commons.Data.Set.ncard_eq_natCard
import Submission.Commons.Data.Nat.card_filter_primeFactors_ge_le

open Polynomial
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): the divisor-`A` assembly (pure counting)

Following the road-map Session-35 block, this module is the *pure counting*
assembly of Case III subcase (ii): for fixed `B` (a prime threshold, in the
application eventually larger than `n`), `3 ≤ n`, box polynomials whose
double discriminant does not vanish and admit a *large squarefree divisor*
`A` of `DD(u)` (`A > H`, all prime factors `≥ B`) such that `Disc(f)` is a
multiple of every `p | A` are few:

    #{f ∈ Box n H : DD(u_f) ≠ 0 ∧ ∃ A ∈ Adm(u_f), ∀ p | A, p | Disc(f)}
        ≤ (2H+1)^(n-1) · 2 · (2(n-1))^(K·(log_B H + 1))      (eventually)

The pieces (all pure ℕ / ℤ / polynomial — no number fields):

* `Adm B n H u` — the admissible squarefree divisors `A` of `DD(u)`;
* members of `Adm` have all prime factors among the big prime divisors of
  `|DD(u)|`, hence `ω(A) ≤ m(u)` and at most `2^(m(u))` such `A` exist
  (`adm_ncard_le_pow_two`);
* the per-`u` count of constant coefficients `c` with a witness `A` is
  bounded by the joint bound (CaseIIIJointA) summed over the `A ∈ Adm(u)`
  (`perUpper_ncard_le`);
* `m(u) ≤ K·(log_B H + 1)` whenever `|DD(u)| ≤ H^K` — an all-primes-free
  `PrimeBound`-style estimate (`bigPrimeDivs_card_le_log_mul_of_le`, from
  commons `Commons.Data.Nat.card_filter_primeFactors_ge_le`);
* the box bound `|DD(u)| ≤ H^K` (`CaseIIIHeight.concDDZ_box_pow_le`,
  transferred to `natAbs`), uniform over the `(2H+1)^(n-1)` upper
  coefficient vectors;
* the `(u,c)`-parametrisation of the box (`CaseIIIBox`), giving the final
  statement `caseIII_subcase2_box_ncard_le`.

(When Lemma 24 supplies the per-prime divisibility `p | DD(u)` for all primes
`p | A_f` of the Case-III large-prime part `A_f`, the Case-III-bad polynomials
will be shown to lie in the set counted here; the `DD(u) = 0` polys are counted
separately via `DoubleDisc.ddPoly_zero_box_ncard_le`.)
-/

namespace Submission.Vdw

/-- Case-III subcase-(ii) admissible `A`-values for upper coefficients `u`:
squarefree `A > H`, every prime divisor at least `B`, and `A` divides the
double discriminant `DD(u)`. -/
noncomputable def Adm (B n H : ℕ) (u : Fin (n - 1) → ℤ) : Set ℕ :=
  {A | H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p) ∧
    ((A : ℤ) ∣ concDDZ n u)}

/-- The big (≥ `B`) prime divisors of `|DD(u)|`. -/
noncomputable def bigDivs (B n : ℕ) (u : Fin (n - 1) → ℤ) : Finset ℕ :=
  bigPrimeDivs B (concDDZ n u).natAbs

/-- `m(u)` — the number of big prime divisors of `|DD(u)|`. -/
noncomputable def mBig (B n : ℕ) (u : Fin (n - 1) → ℤ) : ℕ :=
  (bigDivs B n u).card

/-- `(a : ℤ) ∣ b` is equivalent to `a ∣ b.natAbs`. -/
lemma ofNat_dvd_iff_natAbs_dvd (a : ℕ) (b : ℤ) : ((a : ℤ) ∣ b) ↔ a ∣ b.natAbs := by
  have h := (Int.natAbs_dvd_natAbs (a := (a : ℤ)) (b := b))
  have h2 : a ∣ b.natAbs ↔ (a : ℤ) ∣ b := by simpa using h
  exact h2.symm

/-- `(a : ℤ) ∣ b` implies `a ∣ b.natAbs`. -/
lemma natAbs_dvd_of_ofNat_dvd (a : ℕ) (b : ℤ) (h : (a : ℤ) ∣ b) : a ∣ b.natAbs := by
  exact (ofNat_dvd_iff_natAbs_dvd a b).mp h

lemma natAbs_ne_zero_of_ne_zero {b : ℤ} (hb : b ≠ 0) : b.natAbs ≠ 0 := by
  intro h
  exact hb (Int.natAbs_eq_zero.mp h)

/-- An admissible `A` divides `|DD(u)|`. -/
lemma dvd_natAbs_of_mem_adm {B n H : ℕ} {u : Fin (n - 1) → ℤ} {A : ℕ}
    (hA : A ∈ Adm B n H u) : A ∣ (concDDZ n u).natAbs :=
  natAbs_dvd_of_ofNat_dvd A (concDDZ n u) hA.2.2.2

/-- An admissible `A` (with `DD(u) ≠ 0`) lies in the filtered divisors of
`|DD(u)|`. -/
lemma mem_filter_divisors_of_mem_adm {B n H : ℕ} {u : Fin (n - 1) → ℤ}
    (hdd : concDDZ n u ≠ 0) {A : ℕ} (hA : A ∈ Adm B n H u) :
    A ∈ (Nat.divisors (concDDZ n u).natAbs).filter
      (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p)) := by
  have hAdiv : A ∣ (concDDZ n u).natAbs := dvd_natAbs_of_mem_adm hA
  have hz0 : (concDDZ n u).natAbs ≠ 0 := natAbs_ne_zero_of_ne_zero hdd
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hAdiv, hz0⟩, hA.1, hA.2.1, hA.2.2.1⟩

/-- `ω(A) ≤ m(u)` for admissible `A` (its prime divisors are among the big
prime divisors of `|DD(u)|`). -/
lemma omega_le_mBig_of_mem_adm {B n H : ℕ} {u : Fin (n - 1) → ℤ}
    (hdd : concDDZ n u ≠ 0) {A : ℕ} (hA : A ∈ Adm B n H u) :
    omega A ≤ mBig B n u := by
  unfold mBig bigDivs omega
  apply Finset.card_le_card
  intro p hp
  have hpdvd : p ∣ A := (Nat.mem_primeFactors.mp hp).2.1
  have hz : A ∣ (concDDZ n u).natAbs := dvd_natAbs_of_mem_adm hA
  have hpz : p ∣ (concDDZ n u).natAbs := dvd_trans hpdvd hz
  have hz0 : (concDDZ n u).natAbs ≠ 0 := natAbs_ne_zero_of_ne_zero hdd
  have hpz' : p ∈ Nat.primeFactors (concDDZ n u).natAbs :=
    Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpz, hz0⟩
  have hpB : B ≤ p := hA.2.2.1 p hp
  unfold bigPrimeDivs
  rw [Finset.mem_filter]
  exact ⟨hpz', hpB⟩

/-- The filtered squarefree divisors of `|DD(u)|` are at most `2^(m(u))`
in number. -/
lemma filterDivisors_card_le_pow_two (B n H : ℕ) (u : Fin (n - 1) → ℤ)
    (hdd : concDDZ n u ≠ 0) :
    (((Nat.divisors (concDDZ n u).natAbs).filter
      (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p))).card) ≤
      2 ^ mBig B n u := by
  classical
  let s : Finset ℕ := (Nat.divisors (concDDZ n u).natAbs).filter
    (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p))
  -- s injects into the powerset of the big prime divisors of |DD(u)|
  have h2 : s.card ≤ 2 ^ (bigDivs B n u).card := by
    have hle : s.card ≤ (bigDivs B n u).powerset.card := by
      refine Finset.card_le_card_of_injOn (fun A : ℕ => A.primeFactors) ?hmap ?hinj
      · intro A hA
        change A.primeFactors ∈ (bigDivs B n u).powerset
        rw [Finset.mem_powerset]
        intro p hp
        have hAmem := Finset.mem_filter.mp hA
        have hAdiv : A ∣ (concDDZ n u).natAbs := (Nat.mem_divisors.mp hAmem.1).1
        have hz0 : (concDDZ n u).natAbs ≠ 0 := natAbs_ne_zero_of_ne_zero hdd
        have hpz : p ∣ (concDDZ n u).natAbs :=
          dvd_trans (Nat.mem_primeFactors.mp hp).2.1 hAdiv
        have hpz' : p ∈ Nat.primeFactors (concDDZ n u).natAbs :=
          Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpz, hz0⟩
        have hpB : B ≤ p := hAmem.2.2.2 p hp
        unfold bigDivs bigPrimeDivs
        rw [Finset.mem_filter]
        exact ⟨hpz', hpB⟩
      · intro a ha b hb hab
        change a.primeFactors = b.primeFactors at hab
        have hsa : Squarefree a := (Finset.mem_filter.mp ha).2.2.1
        have hsb : Squarefree b := (Finset.mem_filter.mp hb).2.2.1
        calc
          a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsa).symm
          _ = ∏ p ∈ b.primeFactors, p := by rw [hab]
          _ = b := Nat.prod_primeFactors_of_squarefree hsb
    calc
      s.card ≤ (bigDivs B n u).powerset.card := hle
      _ = 2 ^ (bigDivs B n u).card := Finset.card_powerset _
  simpa [s, mBig] using h2

/-- The number of admissible `A`'s is at most `2^(m(u))` (each squarefree
`A` is determined by its set of prime factors, a subset of `bigDivs`). -/
lemma adm_ncard_le_pow_two {B n H : ℕ} {u : Fin (n - 1) → ℤ}
    (hdd : concDDZ n u ≠ 0) : (Adm B n H u).ncard ≤ 2 ^ mBig B n u := by
  classical
  let s : Finset ℕ := (Nat.divisors (concDDZ n u).natAbs).filter
    (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p))
  -- Adm(u) is contained in the finite filtered divisor set
  have hsub : Adm B n H u ⊆ (s : Set ℕ) := by
    intro A hA
    exact mem_filter_divisors_of_mem_adm (B := B) (n := n) (H := H) (u := u) hdd hA
  calc
    (Adm B n H u).ncard ≤ ((s : Set ℕ).ncard) := Set.ncard_le_ncard hsub s.finite_toSet
    _ = s.card := by
      have hnc : ((s : Set ℕ).ncard) = Nat.card ↥(s : Set ℕ) :=
        (Nat.card_coe_set_eq ((s : Set ℕ))).symm
      rw [hnc]
      simp
    _ ≤ 2 ^ mBig B n u := by
      have hfc := filterDivisors_card_le_pow_two (B := B) (n := n) (H := H) (u := u) hdd
      simpa [s] using hfc

end Submission.Vdw

namespace Submission.Vdw

noncomputable section

/-! ---------------------------------------------------------------
## 2. The per-`u` bound and the box assembly
----------------------------------------------------------------- -/

/-- An all-primes-free `PrimeBound`-type estimate: the number of prime
divisors of `z` that are `≥ B` is at most `K·(log_B H + 1)` as soon as
`z ≤ H^K`.  (Pure-ℕ; from the commons
`Commons.Data.Nat.card_filter_primeFactors_ge_le`.) -/
lemma bigPrimeDivs_card_le_log_mul_of_le {B z K H : ℕ} (hB : 1 < B) (hz : z ≠ 0)
    (hle : z ≤ H ^ K) : (bigPrimeDivs B z).card ≤ K * (Nat.log B H + 1) := by
  unfold bigPrimeDivs
  exact Commons.Data.Nat.card_filter_primeFactors_ge_le B z K H hB hz hle

/-- The per-`u` bound of Case-III subcase (ii): for `DD(u) ≠ 0` with
`|DD(u)| ≤ H^K`, the number of constant coefficients `c` for which some
`A ∈ Adm(u)` divides `Disc(f_{u,c})` prime-by-prime is at most
`2·(2(n-1))^(K·(log_B H + 1))`. -/
theorem perUpper_ncard_le (B n K H : ℕ) (hn : 3 ≤ n) (hB : n < B)
    (u : Fin (n - 1) → ℤ) (hdd : concDDZ n u ≠ 0) (hle : (concDDZ n u).natAbs ≤ H ^ K) :
    ({c : BddInt H | ∃ A ∈ Adm B n H u,
        ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} : Set (BddInt H)).ncard ≤
      2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1)) := by
  classical
  let z := (concDDZ n u).natAbs
  let s : Finset ℕ := (Nat.divisors z).filter
    (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p))
  let φ : ℕ → Set (BddInt H) := fun A => {c : BddInt H | ∀ p ∈ A.primeFactors,
    (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))}
  -- the counted set is contained in the union over A ∈ s
  have hsub : ({c : BddInt H | ∃ A ∈ Adm B n H u, ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} : Set (BddInt H))
        ⊆ ⋃ A ∈ s, φ A := by
    intro c hc
    rcases hc with ⟨A, hA, hφc⟩
    have hAs : A ∈ s := by
      change A ∈ (Nat.divisors z).filter
        (fun A => H < A ∧ Squarefree A ∧ (∀ p ∈ A.primeFactors, B ≤ p))
      have hm := mem_filter_divisors_of_mem_adm (B := B) (n := n) (H := H) (u := u) hdd hA
      simpa [s, z] using hm
    simpa using (⟨A, hAs, hφc⟩ : ∃ A ∈ s, c ∈ φ A)
  have hfin : (⋃ A ∈ s, φ A).Finite := by
    exact Set.Finite.subset (Set.finite_univ : (Set.univ : Set (BddInt H)).Finite) (by intro c hc; trivial)
  -- per-A joint bound
  have hφA (A : ℕ) (hAs : A ∈ s) : (φ A).ncard ≤ 2 * (n - 1) ^ omega A := by
    have hmem := Finset.mem_filter.mp hAs
    have hsq : Squarefree A := hmem.2.2.1
    have hAH : H < A := hmem.2.1
    have hpn : ∀ p ∈ A.primeFactors, ¬ p ∣ n := by
      intro p hp hpdvd
      have hpB : B ≤ p := hmem.2.2.2 p hp
      have hnp : n < p := lt_of_lt_of_le hB hpB
      have hple : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hpdvd
      omega
    have hb := bddInt_discr_modA_joint_le n H A (by omega : 2 ≤ n) hsq hAH hpn u
    dsimp [φ]
    rw [ncard_eq_natCard
      ({c : BddInt H | ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} : Set (BddInt H))]
    exact hb
  -- per-A : ω(A) ≤ m(u)
  have hωm (A : ℕ) (hAs : A ∈ s) : omega A ≤ mBig B n u := by
    have hmem := Finset.mem_filter.mp hAs
    have hAd : A ∣ z := (Nat.mem_divisors.mp hmem.1).1
    have hAdz : (A : ℤ) ∣ concDDZ n u :=
      (ofNat_dvd_iff_natAbs_dvd A (concDDZ n u)).mpr (by simpa [z] using hAd)
    have hAdm : A ∈ Adm B n H u := ⟨hmem.2.1, hmem.2.2.1, hmem.2.2.2, hAdz⟩
    exact omega_le_mBig_of_mem_adm (B := B) (n := n) (H := H) (u := u) hdd hAdm
  -- m(u) ≤ K·(log_B H + 1)
  have hmle : mBig B n u ≤ K * (Nat.log B H + 1) := by
    have hB1 : 1 < B := by omega
    have hz0 : z ≠ 0 := by
      dsimp [z]
      exact natAbs_ne_zero_of_ne_zero hdd
    have hb := bigPrimeDivs_card_le_log_mul_of_le (B := B) (z := z) (K := K) (H := H) hB1 hz0 hle
    simpa [mBig, bigDivs, z] using hb
  -- assemble
  calc
    ({c : BddInt H | ∃ A ∈ Adm B n H u, ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} : Set (BddInt H)).ncard
        ≤ (⋃ A ∈ s, φ A).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ ∑ A ∈ s, (φ A).ncard := Finset.set_ncard_biUnion_le s φ
    _ ≤ ∑ A ∈ s, (2 * (n - 1) ^ omega A) := by
      exact Finset.sum_le_sum (by intro A hA; exact hφA A hA)
    _ ≤ ∑ A ∈ s, (2 * (n - 1) ^ mBig B n u) := by
      refine Finset.sum_le_sum ?_
      intro A hA
      have hpow := pow_le_pow_right₀ (by omega : 1 ≤ n - 1) (hωm A hA)
      exact Nat.mul_le_mul_left 2 hpow
    _ = s.card * (2 * (n - 1) ^ mBig B n u) := by
      rw [Finset.sum_const]
      simp
    _ ≤ 2 ^ mBig B n u * (2 * (n - 1) ^ mBig B n u) := by
      have hfc := filterDivisors_card_le_pow_two (B := B) (n := n) (H := H) (u := u) hdd
      have hfc' : s.card ≤ 2 ^ mBig B n u := by simpa [s, z, mBig] using hfc
      exact Nat.mul_le_mul_right _ hfc'
    _ = 2 * (2 * (n - 1)) ^ mBig B n u := by
      rw [mul_pow]
      ring
    _ ≤ 2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1)) := by
      exact Nat.mul_le_mul_left 2 (pow_le_pow_right₀ (by omega : 1 ≤ 2 * (n - 1)) hmle)

/-- Cast form: `|z| : ℚ ≤ H^K` implies `z.natAbs ≤ H^K`. -/
lemma natAbs_le_of_abs_le_pow (z : ℤ) (H K : ℕ) (h : (|z| : ℚ) ≤ (H : ℚ) ^ K) :
    z.natAbs ≤ H ^ K := by
  have hz : |(z : ℚ)| = (z.natAbs : ℚ) := by
    calc
      |(z : ℚ)| = ((|z| : ℤ) : ℚ) := by exact (Int.cast_abs (R := ℚ)).symm
      _ = ((z.natAbs : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
      _ = (z.natAbs : ℚ) := by rfl
  rw [hz] at h
  exact_mod_cast h

/-- Natural-number form of the Case-III box height bound:
eventually in `H`, every box-bounded upper vector `u` satisfies
`(concDDZ n u).natAbs ≤ H^K`. -/
theorem concDDZ_natAbs_box_pow_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ K : ℕ, ∀ᶠ H : ℕ in atTop, ∀ u : Fin (n - 1) → ℤ, (∀ i, |u i| ≤ (H : ℤ)) →
      (concDDZ n u).natAbs ≤ H ^ K := by
  rcases concDDZ_box_pow_le n hn with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  rw [Filter.eventually_atTop] at hK ⊢
  rcases hK with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro H hH u hu
  exact natAbs_le_of_abs_le_pow (concDDZ n u) H K (hN H hH u hu)


/-- **Case III subcase (ii): box count.**  For a fixed prime threshold `B`
(eventually larger than `n`), the box polynomials whose double discriminant
`DD(u_f)` does not vanish and which admit an admissible divisor
`A ∈ Adm(u_f)` with `p | Disc(f)` for all `p | A` are at most
`(2H+1)^(n-1) · 2·(2(n-1))^(K·(log_B H + 1))` — eventually in `H`. -/
theorem caseIII_subcase2_box_ncard_le (B n : ℕ) (hn : 3 ≤ n) (hB : n < B) :
    ∃ K : ℕ, ∀ᶠ H : ℕ in atTop,
      ({f : ℤ[X] | f ∈ Box n H ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
          ∃ A ∈ Adm B n H (upperCoeffs n f),
            ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr f} : Set ℤ[X]).ncard ≤
        (2 * H + 1) ^ (n - 1) * (2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1))) := by
  classical
  have hn1 : 1 ≤ n := by omega
  rcases concDDZ_natAbs_box_pow_le n hn with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  rw [Filter.eventually_atTop] at hK ⊢
  rcases hK with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro H hH
  have hHN : N ≤ H := le_trans (le_max_left N 1) hH
  have hH1 : 1 ≤ H := le_trans (le_max_right N 1) hH
  have hleK : ∀ u : Fin (n - 1) → ℤ, (∀ i, |u i| ≤ (H : ℤ)) →
      (concDDZ n u).natAbs ≤ H ^ K := hN H hHN
  let S : Set ℤ[X] := {f | f ∈ Box n H ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
    ∃ A ∈ Adm B n H (upperCoeffs n f), ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr f}
  let UB := {u : Fin (n - 1) → ℤ // u ∈ upperBox n H}
  haveI : Fintype UB := Fintype.ofEquiv (Fin (n - 1) → BddInt H) (upperBoxEquiv n H).symm
  let F : UB → Type := fun u => {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
    ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
      (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
  haveI (u : UB) : Fintype (F u) := by
    dsimp [F]
    infer_instance
  let C : ℕ := 2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1))
  -- per-fiber bound
  have hFib (u : UB) : Nat.card (F u) ≤ C := by
    by_cases hdd : concDDZ n u.1 ≠ 0
    · have hu : ∀ i, |u.1 i| ≤ (H : ℤ) := u.2
      have hle := hleK u.1 hu
      have hpu := perUpper_ncard_le (B := B) (n := n) (K := K) (H := H) hn hB u.1 hdd hle
      let T1 : Type := {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
      let T2 : Type := {c : BddInt H // ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
      have hbij : T1 ≃ T2 := by
        refine ⟨fun c => (⟨c.1, c.2.2⟩ : T2), fun c => (⟨c.1, ⟨hdd, c.2⟩⟩ : T1), ?_, ?_⟩
        · intro c
          apply Subtype.ext
          rfl
        · intro c
          apply Subtype.ext
          rfl
      calc
        Nat.card {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
            ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
              (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
            = Nat.card {c : BddInt H // ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
                (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} := Nat.card_congr hbij
        _ = ({c : BddInt H | ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
              (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} : Set (BddInt H)).ncard := by
            exact (Nat.card_coe_set_eq
              ({c : BddInt H | ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
                (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} : Set (BddInt H))).symm
        _ ≤ C := by
          dsimp [C]
          exact hpu
    · have hz : concDDZ n u.1 = 0 := (Classical.not_not.mp hdd)
      have hIsEmpty : IsEmpty {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} :=
        ⟨fun c => c.2.1 hz⟩
      haveI : IsEmpty {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} := hIsEmpty
      simp [C]

  -- S injects into the disjoint union of the fibers
  have hSle : S.ncard ≤ Nat.card (Σ u : UB, F u) := by
    let g : {f : ℤ[X] // f ∈ S} → Σ u : UB, F u := fun f =>
      ⟨⟨upperCoeffs n f.1, fun j => upperCoeffs_bound f.2.1 hn1 j⟩,
        ⟨⟨f.1.coeff 0, coeff0_bound f.2.1 hn1⟩,
          ⟨f.2.2.1, by
            rcases f.2.2.2 with ⟨A, hA, hφ⟩
            refine ⟨A, hA, ?_⟩
            intro p hp
            change (p : ℤ) ∣ Polynomial.discr (monicOfUpper n (upperCoeffs n f.1) (f.1.coeff 0))
            rw [monicOfUpper_eq_self n hn1 f.1 f.2.1.1
              (Polynomial.natDegree_eq_of_degree_eq_some f.2.1.2.1)]
            exact hφ p hp⟩⟩⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hux : ((g x).1).1 = ((g y).1).1 := congrArg (fun w : Σ u : UB, F u => w.1.1) hxy
      have huc : upperCoeffs n x.1 = upperCoeffs n y.1 := by
        change ((g x).1).1 = ((g y).1).1
        exact hux
      have hcBdd : ((g x).2).1 = ((g y).2).1 := congrArg (fun w : Σ u : UB, F u => w.2.1) hxy
      have hc0 : x.1.coeff 0 = y.1.coeff 0 := by
        have hc0' := congrArg (fun c : BddInt H => (c : ℤ)) hcBdd
        change ((g x).2.1 : ℤ) = ((g y).2.1 : ℤ) at hc0'
        change x.1.coeff 0 = y.1.coeff 0
        exact hc0'
      have hboxx : x.1 ∈ Box n H := x.2.1
      have hboxy : y.1 ∈ Box n H := y.2.1
      have hdegx : x.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxx.2.1
      have hdegy : y.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxy.2.1
      have hxe : monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) = x.1 :=
        monicOfUpper_eq_self n hn1 x.1 hboxx.1 hdegx
      have hye : monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) = y.1 :=
        monicOfUpper_eq_self n hn1 y.1 hboxy.1 hdegy
      calc
        x.1 = monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) := hxe.symm
        _ = monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) := by rw [huc, hc0]
        _ = y.1 := hye
    have hnc : S.ncard = Nat.card {f : ℤ[X] // f ∈ S} := (Nat.card_coe_set_eq S).symm
    rw [hnc]
    exact Nat.card_le_card_of_injective g hinj
  -- cardinality chain
  have hcardUB : Fintype.card UB = (2 * H + 1) ^ (n - 1) := by
    calc
      Fintype.card UB = Nat.card UB := (Nat.card_eq_fintype_card).symm
      _ = (upperBox n H).ncard := by
        exact (ncard_eq_natCard (upperBox n H)).symm
      _ = (2 * H + 1) ^ (n - 1) := upperBox_ncard_eq n H
  calc
    S.ncard ≤ Nat.card (Σ u : UB, F u) := hSle
    _ = ∑ u : UB, Nat.card (F u) := by
      exact Nat.card_sigma
    _ ≤ ∑ _u : UB, C := by
      refine Finset.sum_le_sum ?_
      intro u hu
      exact hFib u
    _ = Fintype.card UB * C := by
      rw [Finset.sum_const]
      simp
    _ = (2 * H + 1) ^ (n - 1) * C := by rw [hcardUB]
