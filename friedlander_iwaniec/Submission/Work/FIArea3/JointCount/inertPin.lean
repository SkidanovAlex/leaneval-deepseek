/-
# `Work.FIArea3.JointCount.inertPin` — the exponent of an inert prime in `|w|²`

Let `q ≡ 3 (mod 4)` be a rational prime dividing `d` and `w ∈ S` (= `IsSPt d w`) an element of
`{z | z ∣ d ∧ d ∣ |z|²}` that is *minimal* in `S` for divisibility (as the generators of the
maximal pieces `maxPieceFinset d` are, `Smin_of_mem_maxPieceFinset`).  This file proves

  `(|w|²).factorization q = d.factorization q + d.factorization q % 2`,

i.e. writing `k = d.factorization q`, the exponent of the inert prime `q` in `|w|²` is
`k + (k mod 2) = 2 ⌈k/2⌉`.

Because `q` is inert in `ℤ[i]` (`GaussianInt.prime_of_nat_prime_of_mod_four_eq_three`) it is a
Gaussian prime, so `q` also divides `w` (`inert_dvd_of_dvd_gnorm`, from the classical fact that a
prime `≡ 3 (mod 4)` dividing a sum of two squares divides both summands).  The proof then combines
three elementary inputs:

* **lower bound** `k ≤ (|w|²).factorization q`:  `d ∣ |w|²`;
* **upper bound** `(|w|²).factorization q ≤ k + 1`:  the descent `descent` (applied with `ρ = q`)
  says `d ∤ |w/q|²` — otherwise `w/q` would be a strictly smaller element of `S` — and
  `factorization_le_succ_of_not_dvd_div_sq` converts this into the exponent bound;
* **parity** `2 ∣ (|w|²).factorization q`:  `|w|² = Re(w)² + Im(w)²` and a prime `≡ 3 (mod 4)`
  occurs in a sum of two squares to an even exponent (`two_dvd_factorization_gnorm`, proved by
  strong induction using `prime_three_mod_four_dvd_sq_add_sq`).

Since `k ≤ m ≤ k + 1` and `2 ∣ m`, the even number `m` is exactly `k + (k mod 2)`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.SStructure
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Gaussian norm as a sum of two squares of the coordinates:
`gnorm w = (Re w)² + (Im w)²`. -/
lemma gnorm_eq_sq_add_sq (w : GaussianInt) :
    gnorm w = w.re.natAbs ^ 2 + w.im.natAbs ^ 2 := by
  rw [gnorm, GaussianInt.natAbs_norm_eq, sq, sq]

/-- For a prime `q ≡ 3 (mod 4)`, the exponent of `q` in a sum of two squares `a² + b²` is even:
`q | a² + b²` forces `q | a` and `q | b`, so `q² | a² + b²`, and induction on `a² + b²` finishes. -/
lemma two_dvd_factorization_sq_add_sq {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (a b : ℕ) :
    2 ∣ (a ^ 2 + b ^ 2).factorization q := by
  have key : ∀ N : ℕ, (∀ a b : ℕ, a ^ 2 + b ^ 2 = N → 2 ∣ N.factorization q) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro a b hab
      rw [← hab]
      by_cases hN0 : a ^ 2 + b ^ 2 = 0
      · rw [hN0]; simp
      · by_cases hqab : q ∣ a ^ 2 + b ^ 2
        · obtain ⟨ha, hb⟩ :=
            Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq hq hq4 hqab
          obtain ⟨a', rfl⟩ := ha
          obtain ⟨b', rfl⟩ := hb
          have hrw : (q * a') ^ 2 + (q * b') ^ 2 = q ^ 2 * (a' ^ 2 + b' ^ 2) := by ring
          rw [hrw]
          have hN'0 : a' ^ 2 + b' ^ 2 ≠ 0 := by
            intro hh; apply hN0; rw [hrw, hh, mul_zero]
          have hq20 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq.ne_zero
          have hfac := congrArg (fun f : ℕ →₀ ℕ => f q) (Nat.factorization_mul hq20 hN'0)
          simp only [Finsupp.add_apply] at hfac
          rw [hfac]
          have hq2f : (q ^ 2).factorization q = 2 := by
            rw [Nat.factorization_pow, Nat.Prime.factorization hq]; simp
          rw [hq2f]
          have hlt : a' ^ 2 + b' ^ 2 < N := by
            rw [← hab, hrw]
            exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hN'0) (by nlinarith [hq.two_le])
          exact dvd_add (dvd_refl 2) (ih (a' ^ 2 + b' ^ 2) hlt a' b' rfl)
        · rw [Nat.factorization_eq_zero_of_not_dvd hqab]; simp
  exact key (a ^ 2 + b ^ 2) a b rfl

/-- For a prime `q ≡ 3 (mod 4)`, the exponent of `q` in `gnorm w` is even. -/
lemma two_dvd_factorization_gnorm {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (w : GaussianInt) :
    2 ∣ (gnorm w).factorization q := by
  rw [gnorm_eq_sq_add_sq]
  exact two_dvd_factorization_sq_add_sq hq hq4 _ _

/-- An inert prime `q ≡ 3 (mod 4)` dividing `gnorm w` divides `w` in `ℤ[i]`.  (Equivalently:
`q` is a Gaussian prime, and `q ∣ w.re`, `q ∣ w.im`.) -/
lemma inert_dvd_of_dvd_gnorm {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) {w : GaussianInt}
    (h : q ∣ gnorm w) : (q : GaussianInt) ∣ w := by
  have hsum : q ∣ w.re.natAbs ^ 2 + w.im.natAbs ^ 2 := by rwa [← gnorm_eq_sq_add_sq]
  obtain ⟨hre, him⟩ :=
    Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq hq hq4 hsum
  have hre' : (q : ℤ) ∣ w.re := by
    have h1 : (q : ℤ) ∣ ((w.re.natAbs : ℤ)) := by exact_mod_cast hre
    rwa [Int.dvd_natAbs] at h1
  have him' : (q : ℤ) ∣ w.im := by
    have h1 : (q : ℤ) ∣ ((w.im.natAbs : ℤ)) := by exact_mod_cast him
    rwa [Int.dvd_natAbs] at h1
  obtain ⟨a, ha⟩ := hre'
  obtain ⟨b, hb⟩ := him'
  refine ⟨⟨a, b⟩, ?_⟩
  ext <;> simp [ha, hb]

theorem inertPin {d : ℕ} (hd : 1 ≤ d) {w : GaussianInt}
    (hS : Work.FIArea3.JointCount.IsSPt d w)
    (hmin : ∀ v : GaussianInt, Work.FIArea3.JointCount.IsSPt d v → v ∣ w → w ∣ v)
    {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (hqd : q ∣ d) :
    (Work.FIPlan.gnorm w).factorization q = d.factorization q + d.factorization q % 2 := by
  have hd0 : d ≠ 0 := by omega
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hS.1
    rw [zero_mul] at hc
    exact hd0 (by exact_mod_cast hc)
  have hgnw0 : gnorm w ≠ 0 := fun h => hw0 ((gnorm_eq_zero_iff w).mp h)
  -- lower bound: `d ∣ |w|²`
  have hlow : d.factorization q ≤ (gnorm w).factorization q :=
    (Nat.factorization_le_iff_dvd hd0 hgnw0).mpr hS.2 q
  have hqgn : q ∣ gnorm w := hqd.trans hS.2
  -- `q` is a Gaussian prime dividing `w`
  have hqprime : Prime (q : GaussianInt) :=
    @GaussianInt.prime_of_nat_prime_of_mod_four_eq_three q ⟨hq⟩ hq4
  have hqdivw : (q : GaussianInt) ∣ w := inert_dvd_of_dvd_gnorm hq hq4 hqgn
  -- the descent at `ρ = q`
  have hdesc : ¬ d ∣ gnorm (w / (q : GaussianInt)) :=
    descent hd hS hmin (q : GaussianInt) hqprime hqdivw
  have hqn0 : (q : GaussianInt) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqm : gnorm (w / (q : GaussianInt)) * gnorm (q : GaussianInt) = gnorm w :=
    gnorm_div_mul hqn0 hqdivw
  have hgnq : gnorm (q : GaussianInt) = q * q := GaussPieceMax_arith_gnorm_natCast q
  have hq2dvd : q ^ 2 ∣ gnorm w := by
    refine ⟨gnorm (w / (q : GaussianInt)), ?_⟩
    rw [← hqm, hgnq]; ring
  have hex : q ^ 2 * (gnorm w / q ^ 2) = gnorm w := Nat.mul_div_cancel' hq2dvd
  have hdiv_eq : gnorm w / q ^ 2 = gnorm (w / (q : GaussianInt)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos 2)
    rw [hex, ← hqm, hgnq]; ring
  have hwq0 : w / (q : GaussianInt) ≠ 0 := by
    intro h
    apply hw0
    have hm := EuclideanDomain.mul_div_cancel' hqn0 hqdivw
    rw [h, mul_zero] at hm; exact hm.symm
  have hmq : gnorm w / q ^ 2 ≠ 0 := by
    rw [hdiv_eq]
    exact fun h => hwq0 ((gnorm_eq_zero_iff _).mp h)
  have hnd : ¬ d ∣ gnorm w / q ^ 2 := by rw [hdiv_eq]; exact hdesc
  -- upper bound
  have hup : (gnorm w).factorization q ≤ d.factorization q + 1 :=
    factorization_le_succ_of_not_dvd_div_sq hq hmq hd0 hex hS.2 hnd
  -- parity
  have hpar : 2 ∣ (gnorm w).factorization q := two_dvd_factorization_gnorm hq hq4 w
  -- assemble: `k ≤ m ≤ k+1` with `m` even forces `m = k + k % 2`
  have hfin : ∀ m k : ℕ, k ≤ m → m ≤ k + 1 → 2 ∣ m → m = k + k % 2 := by
    intro m k h1 h2 h3
    have hm : m = k ∨ m = k + 1 := by omega
    rcases hm with hk | hk
    · rw [hk]
      have hk2 : k % 2 = 0 := by
        have := Nat.dvd_iff_mod_eq_zero.mp h3
        rwa [hk] at this
      omega
    · rw [hk]
      have hk2 : k % 2 = 1 := by
        have h0 : (k + 1) % 2 = 0 := by
          have := Nat.dvd_iff_mod_eq_zero.mp h3
          rwa [hk] at this
        omega
      omega
  exact hfin _ _ hlow hup hpar

end

end Work.FIArea3.JointCount
