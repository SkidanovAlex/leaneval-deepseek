/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.prod_prime_pow_factorization
import Submission.Work.Analysis.IonescuWainger.iwW_factorization_le

/-!
# Monotonicity of the Ionescu–Wainger denominator sets `P_{≤l}`

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (2022), Appendix A.  The admissible denominators grow with `l`:
`P_{≤l} ⊆ P_{≤l'}` whenever `l ≤ l'`.  In the concrete regime this is the statement
`iwPconcrete ρ l ⊆ iwPconcrete ρ l'`.

Recall that `q ∈ iwPconcrete ρ l` means `q = Q * w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`
and `w ∈ W_{≤l}`, i.e. `w` is a product of at most `D_ρ` primes from `(N_0^{(l)}, 2^l]`, each
taken to a power in `[1, D_ρ]`.

For `0 ≤ ρ` and `l ≤ l'` one has `N_0^{(l)} ≤ N_0^{(l')}`, so `Q_0^{(l)} ∣ Q_0^{(l')}`.  The
prime ranges, however, are *not* nested (the lower end moves up): a prime `p` of `w` with
`p ≤ N_0^{(l')}` must be moved into the `Q_0`-factor, where it is harmless because `p ∣ N_0^{(l')}!`.
Writing `w = w_{≤N'} · w_{>N'}` (the splitting `iwLow`/`iwHigh` at the threshold `N' = N_0^{(l')}`)
therefore gives the required representation of `q` at level `l'`, with the two factors
`Q * w_{≤N'} ∣ Q_0^{(l')}` and `w_{>N'} ∈ W_{≤l'}`.

For `ρ < 0` the quantities degenerate (`D_ρ = 1`, `N_0^{(l)} = 1` for `l ≥ 1`) and the levels
are simply nested; this case is handled separately at the end.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

namespace IwMono

/-! ## The factorization of `iwProd` and `iwQ0` -/

/-- The `q`-adic valuation of `iwProd ρ l`. -/
theorem iwProd_factorization (ρ : ℝ) (l q : ℕ) :
    (iwProd ρ l).factorization q = if q ∈ iwPrimeRange ρ l then iwD ρ else 0 :=
  prod_prime_pow_factorization (fun _ hp => (Finset.mem_filter.mp hp).2) q

/-- The `q`-adic valuation of `iwQ0 ρ l = (N_0^{(l)}!)^{D_ρ}`. -/
theorem iwQ0_factorization (ρ : ℝ) (l q : ℕ) :
    (iwQ0 ρ l).factorization q = iwD ρ * (iwN0 ρ l).factorial.factorization q := by
  rw [iwQ0, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

/-- Membership in the prime range `(N_0^{(l)}, 2^l]`. -/
theorem mem_iwPrimeRange_iff {ρ : ℝ} {l p : ℕ} :
    p ∈ iwPrimeRange ρ l ↔ iwN0 ρ l < p ∧ p ≤ 2 ^ l ∧ p.Prime := by
  rw [iwPrimeRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨Nat.lt_of_succ_le h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨Nat.succ_le_of_lt h1, h2⟩, h3⟩

/-! ## Splitting an element of `W_{≤l}` at a threshold -/

/-- The part of `w` supported on primes `≤ m`. -/
noncomputable def iwLow (m w : ℕ) : ℕ :=
  ∏ p ∈ w.factorization.support.filter (fun p => p ≤ m), p ^ w.factorization p

/-- The part of `w` supported on primes `> m`. -/
noncomputable def iwHigh (m w : ℕ) : ℕ :=
  ∏ p ∈ w.factorization.support.filter (fun p => m < p), p ^ w.factorization p

theorem iwLow_factorization {m w q : ℕ} :
    (iwLow m w).factorization q
      = if q ∈ w.factorization.support.filter (fun p => p ≤ m) then w.factorization q else 0 :=
  prod_prime_pow_factorization (fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) q

theorem iwHigh_factorization {m w q : ℕ} :
    (iwHigh m w).factorization q
      = if q ∈ w.factorization.support.filter (fun p => m < p) then w.factorization q else 0 :=
  prod_prime_pow_factorization (fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) q

theorem mem_support_iwLow {m w q : ℕ} :
    q ∈ (iwLow m w).factorization.support ↔ q ∈ w.factorization.support ∧ q ≤ m := by
  rw [Finsupp.mem_support_iff, iwLow_factorization]
  by_cases h : q ∈ w.factorization.support.filter (fun p => p ≤ m)
  · rw [if_pos h]
    exact ⟨fun _ => Finset.mem_filter.mp h, fun _ => Finsupp.mem_support_iff.mp (Finset.mem_filter.mp h).1⟩
  · rw [if_neg h]
    exact ⟨fun h0 => absurd rfl h0, fun hq _ => h (Finset.mem_filter.mpr hq)⟩

theorem mem_support_iwHigh {m w q : ℕ} :
    q ∈ (iwHigh m w).factorization.support ↔ q ∈ w.factorization.support ∧ m < q := by
  rw [Finsupp.mem_support_iff, iwHigh_factorization]
  by_cases h : q ∈ w.factorization.support.filter (fun p => m < p)
  · rw [if_pos h]
    exact ⟨fun _ => Finset.mem_filter.mp h, fun _ => Finsupp.mem_support_iff.mp (Finset.mem_filter.mp h).1⟩
  · rw [if_neg h]
    exact ⟨fun h0 => absurd rfl h0, fun hq _ => h (Finset.mem_filter.mpr hq)⟩

theorem iwLow_support {m w : ℕ} :
    (iwLow m w).factorization.support = w.factorization.support.filter (fun p => p ≤ m) := by
  ext q; rw [mem_support_iwLow, Finset.mem_filter]

theorem iwHigh_support {m w : ℕ} :
    (iwHigh m w).factorization.support = w.factorization.support.filter (fun p => m < p) := by
  ext q; rw [mem_support_iwHigh, Finset.mem_filter]

theorem iwLow_mul_iwHigh {m w : ℕ} (hw : w ≠ 0) : iwLow m w * iwHigh m w = w := by
  classical
  have hcongr : w.factorization.support.filter (fun p => ¬ p ≤ m)
      = w.factorization.support.filter (fun p => m < p) :=
    Finset.filter_congr (fun p _ => not_le)
  rw [iwLow, iwHigh, ← hcongr, Finset.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hw

theorem iwLow_ne_zero (m w : ℕ) : iwLow m w ≠ 0 := by
  rw [iwLow, Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem iwHigh_ne_zero (m w : ℕ) : iwHigh m w ≠ 0 := by
  rw [iwHigh, Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

/-! ## Monotonicity of `N_0` and the exponent bounds in `W_{≤l}` -/

theorem iwN0_mono {ρ : ℝ} (hρ : 0 ≤ ρ) {l l' : ℕ} (h : l ≤ l') : iwN0 ρ l ≤ iwN0 ρ l' := by
  have hmono : (2:ℝ) ^ (ρ * (l:ℝ) / 2) ≤ (2:ℝ) ^ (ρ * (l':ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hl : (l:ℝ) ≤ (l':ℝ) := by exact_mod_cast h
      nlinarith [hρ, hl])
  simp only [iwN0]
  exact Nat.add_le_add_right (Nat.floor_mono hmono) 1

theorem factorization_pos_mem_iwPrimeRange {ρ : ℝ} {l w q : ℕ} (hw : w ∈ iwW ρ l)
    (hq : w.factorization q ≠ 0) : q ∈ iwPrimeRange ρ l ∧ w.factorization q ≤ iwD ρ := by
  have h := iwW_factorization_le hw (q := q)
  by_cases hmem : q ∈ iwPrimeRange ρ l
  · rw [if_pos hmem] at h; exact ⟨hmem, h⟩
  · rw [if_neg hmem] at h
    exact absurd (le_antisymm h (Nat.zero_le _)) hq

theorem factorization_le_of_dvd_iwQ0 {ρ : ℝ} {l Q : ℕ} (hQ : Q ∣ iwQ0 ρ l) (q : ℕ) :
    Q.factorization q ≤ iwD ρ * (iwN0 ρ l).factorial.factorization q := by
  have hQ0 : Q ≠ 0 := (Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))).ne'
  calc Q.factorization q ≤ (iwQ0 ρ l).factorization q :=
        (Nat.factorization_le_iff_dvd hQ0 (iwQ0_ne_zero ρ l)).mpr hQ q
    _ = iwD ρ * (iwN0 ρ l).factorial.factorization q := iwQ0_factorization ρ l q

theorem factorial_factorization_mono {m n : ℕ} (h : m ≤ n) (q : ℕ) :
    (m.factorial).factorization q ≤ (n.factorial).factorization q :=
  (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero n)).mpr
    (Nat.factorial_dvd_factorial h) q

theorem factorial_factorization_eq_zero_of_lt {N q : ℕ} (hq : q.Prime) (hN : N < q) :
    (N.factorial).factorization q = 0 := by
  by_contra h
  have hd : q ∣ N.factorial := Nat.dvd_of_factorization_pos h
  exact absurd ((Nat.Prime.dvd_factorial hq).mp hd) (not_le.mpr hN)

theorem one_le_factorial_factorization {N q : ℕ} (hq : q.Prime) (hN : q ≤ N) :
    1 ≤ (N.factorial).factorization q := by
  have hle := (Nat.factorization_le_iff_dvd hq.ne_zero (Nat.factorial_ne_zero N)).mpr
    ((Nat.Prime.dvd_factorial hq).mpr hN)
  have h1 : q.factorization q = 1 := by simp [hq.factorization]
  exact h1 ▸ hle q

/-! ## The two halves of the representation at level `l'` -/

/-- The large primes of `w ∈ W_{≤l}` still form an element of `W_{≤l'}`. -/
theorem iwHigh_mem_iwW {ρ : ℝ} {l l' : ℕ} (h : l ≤ l') {w : ℕ} (hw : w ∈ iwW ρ l) :
    iwHigh (iwN0 ρ l') w ∈ iwW ρ l' := by
  classical
  obtain ⟨hwdvd, hwcard⟩ := mem_iwW.mp hw
  refine mem_iwW.mpr ⟨?_, ?_⟩
  · refine (Nat.factorization_le_iff_dvd (iwHigh_ne_zero _ _) (iwProd_ne_zero ρ l')).mp (fun q => ?_)
    rw [iwHigh_factorization, iwProd_factorization]
    by_cases hc : q ∈ w.factorization.support.filter (fun p => iwN0 ρ l' < p)
    · rw [if_pos hc]
      have hqsupp : w.factorization q ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hc).1
      obtain ⟨hmeml, hleD⟩ := factorization_pos_mem_iwPrimeRange hw hqsupp
      have hlt : iwN0 ρ l' < q := (Finset.mem_filter.mp hc).2
      have hprime : q.Prime := (Finset.mem_filter.mp hmeml).2
      have hmeml' : q ∈ iwPrimeRange ρ l' := by
        obtain ⟨-, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hmeml).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt hlt, le_trans hhi (Nat.pow_le_pow_right (by norm_num) h)⟩, hprime⟩
      rw [if_pos hmeml']; exact hleD
    · rw [if_neg hc]; exact Nat.zero_le _
  · rw [iwHigh_support]
    calc (w.factorization.support.filter (fun p => iwN0 ρ l' < p)).card
        ≤ w.factorization.support.card := Finset.card_filter_le _ _
      _ ≤ iwD ρ := hwcard

/-- Absorbing the small primes of `w` into the `Q_0`-factor. -/
theorem iwLow_mul_dvd_iwQ0 {ρ : ℝ} (hρ : 0 ≤ ρ) {l l' : ℕ} (h : l ≤ l') {Q w : ℕ}
    (hQ : Q ∣ iwQ0 ρ l) (hw : w ∈ iwW ρ l) :
    Q * iwLow (iwN0 ρ l') w ∣ iwQ0 ρ l' := by
  classical
  have hQ0 : Q ≠ 0 := (Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))).ne'
  have hL0 : iwLow (iwN0 ρ l') w ≠ 0 := iwLow_ne_zero _ _
  refine (Nat.factorization_le_iff_dvd (mul_ne_zero hQ0 hL0) (iwQ0_ne_zero ρ l')).mp (fun q => ?_)
  rw [Nat.factorization_mul hQ0 hL0, Finsupp.add_apply, iwLow_factorization, iwQ0_factorization]
  by_cases hc : q ∈ w.factorization.support.filter (fun p => p ≤ iwN0 ρ l')
  · rw [if_pos hc]
    have hqsupp : w.factorization q ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hc).1
    have hqle : q ≤ iwN0 ρ l' := (Finset.mem_filter.mp hc).2
    obtain ⟨hmeml, hleD⟩ := factorization_pos_mem_iwPrimeRange hw hqsupp
    have hprime : q.Prime := (Finset.mem_filter.mp hmeml).2
    have hzero : Q.factorization q = 0 := by
      have h1 := factorization_le_of_dvd_iwQ0 hQ q
      rw [factorial_factorization_eq_zero_of_lt hprime (mem_iwPrimeRange_iff.mp hmeml).1, mul_zero] at h1
      exact Nat.le_zero.mp h1
    rw [hzero, Nat.zero_add]
    calc w.factorization q ≤ iwD ρ := hleD
      _ = iwD ρ * 1 := (mul_one _).symm
      _ ≤ iwD ρ * (iwN0 ρ l').factorial.factorization q :=
          Nat.mul_le_mul_left _ (one_le_factorial_factorization hprime hqle)
  · rw [if_neg hc, add_zero]
    calc Q.factorization q ≤ iwD ρ * (iwN0 ρ l).factorial.factorization q :=
          factorization_le_of_dvd_iwQ0 hQ q
      _ ≤ iwD ρ * (iwN0 ρ l').factorial.factorization q :=
          Nat.mul_le_mul_left _ (factorial_factorization_mono (iwN0_mono hρ h) q)

/-- The main step for `0 ≤ ρ`: a product `Q * w` representing an element of `P_{≤l}` is also an
element of `P_{≤l'}`. -/
theorem mul_mem_iwPconcrete_of_le {ρ : ℝ} (hρ : 0 ≤ ρ) {l l' : ℕ} (h : l ≤ l')
    {Q w : ℕ} (hQ : Q ∣ iwQ0 ρ l) (hw : w ∈ iwW ρ l) :
    Q * w ∈ iwPconcrete ρ l' := by
  classical
  have hw0 : w ≠ 0 := (pos_of_mem_iwW hw).ne'
  exact mem_iwPconcrete.mpr
    ⟨Q * iwLow (iwN0 ρ l') w, Nat.mem_divisors.mpr ⟨iwLow_mul_dvd_iwQ0 hρ h hQ hw, iwQ0_ne_zero ρ l'⟩,
     iwHigh (iwN0 ρ l') w, iwHigh_mem_iwW h hw, by rw [mul_assoc, iwLow_mul_iwHigh hw0]⟩

/-! ## The degenerate case `ρ < 0` -/

theorem iwD_eq_one_of_neg {ρ : ℝ} (hρ : ρ < 0) : iwD ρ = 1 := by
  rw [iwD]
  have h2 : (2 : ℝ) / ρ ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨by norm_num, le_of_lt hρ⟩)
  rw [Nat.floor_of_nonpos h2]

theorem iwN0_zero (ρ : ℝ) : iwN0 ρ 0 = 2 := by
  rw [iwN0]
  have h : ρ * ((0 : ℕ) : ℝ) / 2 = 0 := by norm_num
  rw [h, Real.rpow_zero, Nat.floor_one]

theorem iwN0_eq_one_of_neg {ρ : ℝ} (hρ : ρ < 0) {l : ℕ} (hl : 1 ≤ l) : iwN0 ρ l = 1 := by
  rw [iwN0]
  have hl' : (0 : ℝ) < (l : ℝ) := by
    have : 0 < l := Nat.lt_of_lt_of_le Nat.zero_lt_one hl
    exact_mod_cast this
  have hx : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  rw [Nat.floor_eq_zero.mpr hx]

theorem iwQ0_zero_of_neg {ρ : ℝ} (hρ : ρ < 0) : iwQ0 ρ 0 = 2 := by
  rw [iwQ0, iwN0_zero, iwD_eq_one_of_neg hρ]
  norm_num

theorem iwProd_zero (ρ : ℝ) : iwProd ρ 0 = 1 := by
  rw [iwProd]
  refine Finset.prod_eq_one fun p hp => ?_
  exfalso
  obtain ⟨hIcc, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
  rw [iwN0_zero] at hlo
  simp only [pow_zero] at hhi
  omega

theorem iwPrimeRange_eq_of_neg {ρ : ℝ} (hρ : ρ < 0) {m : ℕ} (hm : 1 ≤ m) :
    iwPrimeRange ρ m = (Finset.Icc 2 (2 ^ m)).filter Nat.Prime := by
  rw [iwPrimeRange, iwN0_eq_one_of_neg hρ hm]

/-- For `ρ < 0` and `1 ≤ m ≤ m'` the prime products are nested. -/
theorem iwProd_dvd_of_neg {ρ : ℝ} (hρ : ρ < 0) {m m' : ℕ} (hm : 1 ≤ m) (h : m ≤ m') :
    iwProd ρ m ∣ iwProd ρ m' := by
  rw [iwProd, iwProd, iwPrimeRange_eq_of_neg hρ hm, iwPrimeRange_eq_of_neg hρ (le_trans hm h)]
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (Nat.pow_le_pow_right (by norm_num) h)))

theorem iwPconcrete_mono_of_neg_aux {ρ : ℝ} (hρ : ρ < 0) {l l' : ℕ} (h : l ≤ l') :
    iwPconcrete ρ l ⊆ iwPconcrete ρ l' := by
  intro q hq
  rw [mem_iwPconcrete] at hq ⊢
  obtain ⟨Q, hQmem, w, hwmem, rfl⟩ := hq
  obtain ⟨hQdvd, -⟩ := Nat.mem_divisors.mp hQmem
  obtain ⟨hwdvd, hwcard⟩ := mem_iwW.mp hwmem
  by_cases hl' : l' = 0
  · subst hl'
    have hl : l = 0 := Nat.eq_zero_of_le_zero h
    subst hl
    exact ⟨Q, Nat.mem_divisors.mpr ⟨hQdvd, iwQ0_ne_zero ρ 0⟩, w, hwmem, rfl⟩
  · have hl'1 : 1 ≤ l' := Nat.one_le_iff_ne_zero.mpr hl'
    by_cases hl : l = 0
    · subst hl
      have hw1 : w = 1 := Nat.dvd_one.mp (by rwa [iwProd_zero] at hwdvd)
      have hQ2 : Q ∣ 2 := by rwa [iwQ0_zero_of_neg hρ] at hQdvd
      rw [hw1, mul_one]
      rcases (Nat.dvd_prime Nat.prime_two).mp hQ2 with hQ | hQ
      · subst hQ
        exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero ρ l'⟩, 1, one_mem_iwW ρ l',
          by simp⟩
      · subst hQ
        refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero ρ l'⟩, 2, ?_, by simp⟩
        rw [mem_iwW]
        refine ⟨?_, ?_⟩
        · rw [iwProd]
          have h2mem : (2 : ℕ) ∈ iwPrimeRange ρ l' := by
            rw [mem_iwPrimeRange_iff]
            exact ⟨by rw [iwN0_eq_one_of_neg hρ hl'1]; norm_num,
              Nat.le_self_pow hl' 2, Nat.prime_two⟩
          exact dvd_trans (by rw [iwD_eq_one_of_neg hρ]; exact ⟨1, by simp⟩)
            (Finset.dvd_prod_of_mem (f := fun p => p ^ iwD ρ) (s := iwPrimeRange ρ l') h2mem)
        · simp [Nat.support_factorization, Nat.Prime.primeFactors Nat.prime_two,
            iwD_eq_one_of_neg hρ]
    · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
      have hQ1 : Q = 1 := Nat.dvd_one.mp (by
        rw [show iwQ0 ρ l = 1 from by rw [iwQ0, iwN0_eq_one_of_neg hρ hl1]; norm_num] at hQdvd
        exact hQdvd)
      subst hQ1
      rw [one_mul]
      exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, iwQ0_ne_zero ρ l'⟩, w,
        mem_iwW.mpr ⟨hwdvd.trans (iwProd_dvd_of_neg hρ hl1 h), hwcard⟩, by rw [one_mul]⟩

end IwMono

open IwMono

/-- The sets `P_{≤l}` of Ionescu–Wainger denominators are monotone in `l`. -/
theorem iwPconcrete_mono {ρ : ℝ} {l l' : ℕ} (h : l ≤ l') : iwPconcrete ρ l ⊆ iwPconcrete ρ l' := by
  intro q hq
  rw [mem_iwPconcrete] at hq
  obtain ⟨Q, hQmem, w, hwmem, rfl⟩ := hq
  by_cases hρ : 0 ≤ ρ
  · exact mul_mem_iwPconcrete_of_le hρ h (Nat.mem_divisors.mp hQmem).1 hwmem
  · exact iwPconcrete_mono_of_neg_aux (not_le.mp hρ) h (mem_iwPconcrete.mpr ⟨Q, hQmem, w, hwmem, rfl⟩)

end Work.Analysis.IonescuWainger
