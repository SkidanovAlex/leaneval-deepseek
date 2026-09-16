import Mathlib

open scoped BigOperators

/-!
# Bounded gaps between primes

Formal groundwork for the Maynard--Polymath8 theorem `H₁ ≤ 246`:
for every `n` there are primes `p < q` with `n ≤ p` and `q - p ≤ 246`.

This file records the *endgame* of the proof: given a translate `n` for which an
admissible tuple `h : Fin k → ℕ` with all `h i ≤ D` has at least two prime
values among `n + h i`, one immediately obtains a pair of primes at distance
`≤ D`, together with the explicit 50-term admissible tuple of diameter `246`
(Polymath8a, "Variants of the Selberg sieve", Figure 1) which realizes
`H(50) = 246`.

The deep ingredient that remains (the Maynard multidimensional Selberg sieve,
showing that infinitely many translates `n` have at least two prime values among
`n + h₅₀ i`) is *not* developed here.
-/

namespace Submission.BoundedGaps

/-- The 50-element admissible tuple of diameter 246
(Polymath8a, "Variants of the Selberg sieve", Figure 1). -/
def h50 : Fin 50 → ℕ :=
  ![0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94, 100, 106,
    108, 114, 118, 126, 130, 136, 144, 148, 150, 156, 160, 168, 174, 178, 184, 190,
    196, 198, 204, 210, 214, 216, 220, 226, 228, 234, 238, 240, 244, 246]

/-- The tuple has 50 pairwise distinct entries. -/
lemma h50_injective : Function.Injective h50 := by
  decide

/-- Entries are strictly increasing. -/
lemma h50_strictMono : StrictMono h50 := by
  decide

/-- Every entry of the tuple lies in `[0, 246]`. -/
lemma h50_le_246 : ∀ i : Fin 50, h50 i ≤ 246 := by
  decide

/-- The first entry is 0. -/
lemma h50_zero : h50 ⟨0, by norm_num⟩ = 0 := by
  norm_num [h50]

/-- Admissibility of a `k`-tuple: pairwise distinct entries, and for every prime
`p` the entries fail to occupy all residue classes modulo `p`. -/
def IsAdmissible (k : ℕ) (h : Fin k → ℕ) : Prop :=
  Function.Injective h ∧
    ∀ p : ℕ, Nat.Prime p → ∃ r : ℕ, r < p ∧ ∀ i : Fin k, h i % p ≠ r

/-! The residue-avoidance checks for the finitely many primes `≤ 50`. -/

lemma h50_misses_mod_2 : ∃ r : ℕ, r < 2 ∧ ∀ i : Fin 50, h50 i % 2 ≠ r := ⟨1, by decide⟩
lemma h50_misses_mod_3 : ∃ r : ℕ, r < 3 ∧ ∀ i : Fin 50, h50 i % 3 ≠ r := ⟨2, by decide⟩
lemma h50_misses_mod_5 : ∃ r : ℕ, r < 5 ∧ ∀ i : Fin 50, h50 i % 5 ≠ r := ⟨2, by decide⟩
lemma h50_misses_mod_7 : ∃ r : ℕ, r < 7 ∧ ∀ i : Fin 50, h50 i % 7 ≠ r := ⟨5, by decide⟩
lemma h50_misses_mod_11 : ∃ r : ℕ, r < 11 ∧ ∀ i : Fin 50, h50 i % 11 ≠ r := ⟨10, by decide⟩
lemma h50_misses_mod_13 : ∃ r : ℕ, r < 13 ∧ ∀ i : Fin 50, h50 i % 13 ≠ r := ⟨11, by decide⟩
lemma h50_misses_mod_17 : ∃ r : ℕ, r < 17 ∧ ∀ i : Fin 50, h50 i % 17 ≠ r := ⟨1, by decide⟩
lemma h50_misses_mod_19 : ∃ r : ℕ, r < 19 ∧ ∀ i : Fin 50, h50 i % 19 ≠ r := ⟨9, by decide⟩
lemma h50_misses_mod_23 : ∃ r : ℕ, r < 23 ∧ ∀ i : Fin 50, h50 i % 23 ≠ r := ⟨5, by decide⟩
lemma h50_misses_mod_29 : ∃ r : ℕ, r < 29 ∧ ∀ i : Fin 50, h50 i % 29 ≠ r := ⟨9, by decide⟩
lemma h50_misses_mod_31 : ∃ r : ℕ, r < 31 ∧ ∀ i : Fin 50, h50 i % 31 ≠ r := ⟨14, by decide⟩
lemma h50_misses_mod_37 : ∃ r : ℕ, r < 37 ∧ ∀ i : Fin 50, h50 i % 37 ≠ r := ⟨1, by decide⟩
lemma h50_misses_mod_41 : ∃ r : ℕ, r < 41 ∧ ∀ i : Fin 50, h50 i % 41 ≠ r := ⟨1, by decide⟩
lemma h50_misses_mod_43 : ∃ r : ℕ, r < 43 ∧ ∀ i : Fin 50, h50 i % 43 ≠ r := ⟨9, by decide⟩
lemma h50_misses_mod_47 : ∃ r : ℕ, r < 47 ∧ ∀ i : Fin 50, h50 i % 47 ≠ r := ⟨18, by decide⟩

/-- Every prime `p ≤ 50` is one of the fifteen listed primes. -/
lemma prime_le_50_eq_list {p : ℕ} (hp : Nat.Prime p) (hp50 : p ≤ 50) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨
      p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 43 ∨ p = 47 := by
  interval_cases p <;> try norm_num at hp <;> try decide

/-- The tuple `h50` is admissible. -/
lemma h50_admissible : IsAdmissible 50 h50 := by
  constructor
  · exact h50_injective
  · intro p hp
    by_cases hp50 : p ≤ 50
    · rcases prime_le_50_eq_list hp hp50 with
        h2 | h3 | h5 | h7 | h11 | h13 | h17 | h19 | h23 | h29 | h31 | h37 | h41 | h43 | h47
      · subst p; exact h50_misses_mod_2
      · subst p; exact h50_misses_mod_3
      · subst p; exact h50_misses_mod_5
      · subst p; exact h50_misses_mod_7
      · subst p; exact h50_misses_mod_11
      · subst p; exact h50_misses_mod_13
      · subst p; exact h50_misses_mod_17
      · subst p; exact h50_misses_mod_19
      · subst p; exact h50_misses_mod_23
      · subst p; exact h50_misses_mod_29
      · subst p; exact h50_misses_mod_31
      · subst p; exact h50_misses_mod_37
      · subst p; exact h50_misses_mod_41
      · subst p; exact h50_misses_mod_43
      · subst p; exact h50_misses_mod_47
    · -- prime p > 50: pigeonhole among the p residue classes
      have hpgt : 50 < p := by omega
      classical
      let s : Finset ℕ := Finset.univ.image (fun i : Fin 50 => h50 i % p)
      have hcard : s.card < p := by
        calc
          s.card ≤ (Finset.univ : Finset (Fin 50)).card := Finset.card_image_le
          _ = 50 := by simp
          _ < p := hpgt
      have hsub : s ⊆ Finset.range p := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
        exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.Prime.pos hp))
      have hlt : s.card < (Finset.range p).card := by
        simpa [Finset.card_range] using hcard
      have hex : ∃ x ∈ Finset.range p, x ∉ s := by
        by_contra hnone
        have hall : ∀ x, x ∈ Finset.range p → x ∈ s := by
          intro x hx
          by_contra hxnot
          exact hnone ⟨x, hx, hxnot⟩
        have hsle : (Finset.range p).card ≤ s.card := Finset.card_le_card (by
          intro x hx
          exact hall x hx)
        omega
      rcases hex with ⟨r, hr, hrn⟩
      refine ⟨r, Finset.mem_range.mp hr, ?_⟩
      intro i hi
      exact hrn (Finset.mem_image.mpr ⟨i, by simp, hi⟩)

/-! ## From a translate with two prime values to a close prime pair -/

/-- If a filter of a finite set has cardinality at least two, it contains two
distinct elements satisfying the predicate. -/
lemma exists_two_of_two_le_card_filter {α : Type*} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] (hc : 2 ≤ (s.filter P).card) :
    ∃ a b : α, a ∈ s ∧ b ∈ s ∧ P a ∧ P b ∧ a ≠ b := by
  classical
  have h1 : 1 < (s.filter P).card := by omega
  rcases Finset.one_lt_card_iff.mp h1 with ⟨a, b, haf, hbf, hab⟩
  exact ⟨a, b, (Finset.mem_filter.mp haf).1, (Finset.mem_filter.mp hbf).1,
    (Finset.mem_filter.mp haf).2, (Finset.mem_filter.mp hbf).2, hab⟩

/-- If at least two values of `n + h i` (`i : Fin k`) are prime and all `h i ≤ D`,
then there are primes `p < q` with `n ≤ p` and `q - p ≤ D`. -/
theorem twoPrimes_of_card_filter {k : ℕ} {h : Fin k → ℕ} {D n : ℕ}
    (hmono : StrictMono h) (hD : ∀ i : Fin k, h i ≤ D)
    (hc : 2 ≤ ((Finset.univ : Finset (Fin k)).filter (fun i => Nat.Prime (n + h i))).card) :
    ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ D := by
  classical
  obtain ⟨i, j, _hi, _hj, hpi, hpj, hij⟩ :=
    exists_two_of_two_le_card_filter (Finset.univ : Finset (Fin k))
      (fun i => Nat.Prime (n + h i)) hc
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · refine ⟨n + h i, n + h j, ?_, hpi, hpj, ?_, ?_⟩
    · omega
    · exact Nat.add_lt_add_left (hmono hijlt) n
    · have hle : h i ≤ h j := le_of_lt (hmono hijlt)
      calc
        (n + h j) - (n + h i) = h j - h i := by omega
        _ ≤ h j := Nat.sub_le _ _
        _ ≤ D := hD j
  · refine ⟨n + h j, n + h i, ?_, hpj, hpi, ?_, ?_⟩
    · omega
    · exact Nat.add_lt_add_left (hmono hjilt) n
    · have hle : h j ≤ h i := le_of_lt (hmono hjilt)
      calc
        (n + h i) - (n + h j) = h i - h j := by omega
        _ ≤ h i := Nat.sub_le _ _
        _ ≤ D := hD i

/-- Endgame for the specific tuple: any translate with at least two prime values
among `n + h50 i` produces a prime pair at distance at most 246. -/
theorem twoPrimes_of_card_filter_h50 {n : ℕ}
    (hc : 2 ≤ ((Finset.univ : Finset (Fin 50)).filter (fun i => Nat.Prime (n + h50 i))).card) :
    ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ 246 := by
  exact twoPrimes_of_card_filter (k := 50) (h := h50) (D := 246) (n := n)
    h50_strictMono h50_le_246 hc


/-- The full bounded-gaps theorem follows from the (unproved, deep) Maynard
sieve statement that arbitrarily large translates `n` have at least two prime
values among `n + h50 i`.  Everything between that statement and the theorem
below is proved here. -/
theorem boundedPrimeGaps_of_maynardSieve
    (sieve : ∀ N : ℕ, ∃ n ≥ N,
      2 ≤ ((Finset.univ : Finset (Fin 50)).filter (fun i => Nat.Prime (n + h50 i))).card) :
    ∀ n : ℕ, ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ 246 := by
  intro n
  obtain ⟨m, hmn, hc⟩ := sieve n
  obtain ⟨p, q, hp_le_m, hp, hq, hpq, hgap⟩ := twoPrimes_of_card_filter_h50 (n := m) hc
  exact ⟨p, q, by omega, hp, hq, hpq, hgap⟩


/-- `DHL[k, 2]` (weak Dickson--Hardy--Littlewood, two primes in a translate):
every admissible `k`-tuple has arbitrarily large translates `n` with at least
two prime values among `n + h i`.  This is exactly the claim (for `k = 50`)
labelled `DHL[50, 2]` in Polymath8a, Theorem 3.2(i), which is established there
by the Maynard sieve. -/
def DHL (k : ℕ) : Prop :=
  ∀ h : Fin k → ℕ, IsAdmissible k h → ∀ N : ℕ,
    ∃ n ≥ N, 2 ≤ ((Finset.univ : Finset (Fin k)).filter
      (fun i => Nat.Prime (n + h i))).card

/-- `DHL[50, 2]` implies the bounded-gaps theorem with gap bound 246,
using the admissible 50-tuple `h50` of diameter 246. -/
theorem boundedPrimeGaps_of_DHL50 (h : DHL 50) :
    ∀ n : ℕ, ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ 246 := by
  exact boundedPrimeGaps_of_maynardSieve (h h50 h50_admissible)

end Submission.BoundedGaps
