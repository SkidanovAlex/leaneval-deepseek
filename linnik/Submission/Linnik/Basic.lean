import ChallengeDeps
import Mathlib

open LeanEval.NumberTheory.Linnik
open scoped BigOperators

namespace Submission.Linnik

/-! Properties of `p a d`, the least prime in the progression `a, a+d, ...`.

`p a d` is `sInf` of `{a + k * d | k : ℕ} ∩ {p | p.Prime}`, where `sInf` on `ℕ`
is the least element of a nonempty set and `0` for the empty set
(`Nat.instInfSet`).  We develop the elementary theory of this function:
a prime in the progression bounds `p a d` from above; and (using Dirichlet's
theorem) the defining set is nonempty for `a.Coprime d`, so that `p a d` is a
prime congruent to `a` modulo `d`. -/

/-- The set of (prime) numbers of the progression `a mod d`. -/
def S (a d : ℕ) : Set ℕ := {a + k * d | k : ℕ} ∩ {p | p.Prime}

@[simp] lemma mem_S_iff {a d n : ℕ} : n ∈ S a d ↔ ∃ k : ℕ, n = a + k * d ∧ n.Prime := by
  constructor
  · rintro ⟨⟨k, hk⟩, hprim⟩
    exact ⟨k, hk.symm, hprim⟩
  · rintro ⟨k, rfl, hprim⟩
    exact ⟨⟨k, rfl⟩, hprim⟩

lemma p_eq_sInf {a d : ℕ} : p a d = sInf (S a d) := rfl

lemma mem_S_of_dvd_sub {a d r : ℕ} (hprime : r.Prime) (hle : a ≤ r) (hdvd : d ∣ r - a) :
    r ∈ S a d := by
  rw [mem_S_iff]
  rcases hdvd with ⟨k, hk⟩
  refine ⟨k, ?_, hprime⟩
  rw [← Nat.add_sub_of_le hle, hk, Nat.mul_comm]

/-- A prime `r ≥ a` that is congruent to `a` modulo `d` lies in the progression. -/
lemma mem_S_of_prime_modEq {a d r : ℕ} (hprime : r.Prime) (hle : a ≤ r)
    (hmod : r ≡ a [MOD d]) : r ∈ S a d := by
  exact mem_S_of_dvd_sub hprime hle ((Nat.modEq_iff_dvd' hle).1 hmod.symm)

/-- A prime in the progression bounds `p a d` from above. -/
theorem p_le_of_mem_S {a d n : ℕ} (hn : n ∈ S a d) : p a d ≤ n := by
  classical
  have hne : (S a d).Nonempty := ⟨n, hn⟩
  rw [p_eq_sInf, Nat.sInf_def hne]
  exact Nat.find_min' hne hn

/-- If a prime `r ≥ a` with `r ≡ a [MOD d]`, then `p a d ≤ r`. -/
theorem p_le_of_prime_modEq {a d r : ℕ} (hprime : r.Prime) (hle : a ≤ r)
    (hmod : r ≡ a [MOD d]) : p a d ≤ r :=
  p_le_of_mem_S (mem_S_of_prime_modEq hprime hle hmod)

/-- If `S a d` is nonempty, `p a d` is its least element (hence lies in it). -/
theorem p_mem_S_of_nonempty {a d : ℕ} (hne : (S a d).Nonempty) : p a d ∈ S a d := by
  classical
  rw [p_eq_sInf, Nat.sInf_def hne]
  exact Nat.find_spec hne

/-- Dirichlet's theorem: for `a.Coprime d` with `0 < d`, primes in the progression
`a mod d` exist arbitrarily far out. -/
theorem exists_prime_gt_modEq_of_coprime {a d n : ℕ} (hd : d ≠ 0) (h : a.Coprime d) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD d] := by
  exact Nat.forall_exists_prime_gt_and_modEq n hd h

/-- For `a.Coprime d` with `0 < d`, the progression contains primes. -/
theorem S_nonempty_of_coprime {a d : ℕ} (hd : d ≠ 0) (h : a.Coprime d) : (S a d).Nonempty := by
  rcases exists_prime_gt_modEq_of_coprime (a := a) (d := d) (n := a) hd h with
    ⟨p, hgt, hprim, hmod⟩
  exact ⟨p, mem_S_of_prime_modEq hprim hgt.le hmod⟩

/-- The least prime in the progression is prime. -/
theorem p_prime_of_coprime {a d : ℕ} (hd : d ≠ 0) (h : a.Coprime d) : (p a d).Prime := by
  have hp : p a d ∈ S a d := p_mem_S_of_nonempty (S_nonempty_of_coprime hd h)
  rw [mem_S_iff] at hp
  exact hp.choose_spec.2

/-- The least prime in the progression is congruent to `a` modulo `d`. -/
theorem p_modEq_of_coprime {a d : ℕ} (hd : d ≠ 0) (h : a.Coprime d) : p a d ≡ a [MOD d] := by
  have hp : p a d ∈ S a d := p_mem_S_of_nonempty (S_nonempty_of_coprime hd h)
  rw [mem_S_iff] at hp
  rcases hp with ⟨k, hk, _⟩
  have hpd : a ≤ p a d := by
    rw [hk]
    exact Nat.le_add_right a (k * d)
  have hsym : a ≡ p a d [MOD d] := by
    rw [Nat.modEq_iff_dvd' hpd]
    rw [hk, Nat.add_sub_cancel_left]
    exact ⟨k, Nat.mul_comm k d⟩
  exact hsym.symm

/-- A prime `p` congruent to `a` modulo `q` with `0 < a < q` satisfies `a ≤ p`. -/
theorem le_of_prime_modEq {a q p : ℕ} (haq : a < q) (_hp : p.Prime) (hmod : p ≡ a [MOD q]) :
    a ≤ p := by
  by_contra hna
  have hlt : p < a := lt_of_not_ge hna
  have hdvd : q ∣ a - p := (Nat.modEq_iff_dvd' (le_of_lt hlt)).1 hmod
  have hsub : 0 < a - p := Nat.sub_pos_of_lt hlt
  have hle1 : q ≤ a - p := Nat.le_of_dvd hsub hdvd
  have hltq : a - p < q := lt_of_le_of_lt (Nat.sub_le a p) haq
  omega

/-- If a prime `r ≤ X` with `r ≡ a [MOD d]` (and `r ≥ a`) then the least prime
of the progression is `≤ X`. -/
theorem p_le_of_prime_le {a d X : ℕ} {r : ℕ} (hprim : r.Prime) (hleX : r ≤ X)
    (hle : a ≤ r) (hmod : r ≡ a [MOD d]) : p a d ≤ X :=
  (p_le_of_prime_modEq hprim hle hmod).trans hleX


/-- A positive weighted sum over primes `p ≤ X` with `p ≡ a [MOD q]` shows that
such a prime exists.  (This is the shape of the conclusion of Heath-Brown's
weighted-sum argument in §13–§15: positivity of Σ forces the progression to
contain a prime inside the window.) -/
theorem exists_prime_modEq_of_weighted_sum_pos {q a X : ℕ} (w : ℕ → ℝ)
    (hpos : 0 < ∑ p ∈ (Finset.range (X + 1)).filter
        (fun p => p.Prime ∧ p ≡ a [MOD q]), w p) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p ≤ X := by
  classical
  have hne : (Finset.range (X + 1)).filter
      (fun p => p.Prime ∧ p ≡ a [MOD q]) ≠ ∅ := by
    intro he
    have hsum0 : (∑ p ∈ (Finset.range (X + 1)).filter
        (fun p => p.Prime ∧ p ≡ a [MOD q]), w p) = 0 := by
      rw [he]
      simp
    linarith
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hmem := Finset.mem_filter.mp hp
  have hle : p ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1)
  exact ⟨p, hmem.2.1, hmem.2.2, hle⟩

/-- Positivity of a weighted prime sum over `p ≤ X`, `p ≡ a [MOD q]` bounds the
least prime of the progression: `p a q ≤ X`. -/
theorem p_le_of_weighted_sum_pos {q a X : ℕ} (haq : a < q) (w : ℕ → ℝ)
    (hpos : 0 < ∑ p ∈ (Finset.range (X + 1)).filter
        (fun p => p.Prime ∧ p ≡ a [MOD q]), w p) :
    p a q ≤ X := by
  rcases exists_prime_modEq_of_weighted_sum_pos (q := q) (a := a) (X := X) w hpos with
    ⟨p, hpp, hmod, hle⟩
  have hle' : a ≤ p := le_of_prime_modEq haq hpp hmod
  exact (p_le_of_prime_modEq hpp hle' hmod).trans hle

end Submission.Linnik
