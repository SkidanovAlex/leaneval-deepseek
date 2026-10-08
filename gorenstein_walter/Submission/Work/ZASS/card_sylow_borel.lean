import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic
import Submission.Work.Zassenhaus.zass_coprime_pow_half

namespace Work.ZASS

/-- **Z2 (blueprint §ZASS).** A Sylow `p`-subgroup of the Borel subgroup has order `q = p^k`:
`|B| = q * (q-1)/2` and `p ∤ (q-1)/2`
(`Work.Zassenhaus.zass_coprime_pow_half`), so the `p`-part of `|B|` is `q`.  Equivalently
`Nat.card P = p ^ Nat.factorization (Nat.card B) p` (Mathlib `Sylow.card_eq_multiplicity`),
and `.map subtype` preserves cardinality. -/
theorem card_sylow_borel {G X : Type} [Group G] [Finite G] [MulAction G X] {p k : ℕ}
    [Fact p.Prime] (hp : Odd p) {q : ℕ}
    (hq : q = p ^ k) {inf : X}
    (hB : Nat.card (Work.Zassenhaus.borel G inf) = q * ((q - 1) / 2))
    (P : Sylow p (Work.Zassenhaus.borel G inf)) :
    Nat.card ((P : Subgroup (Work.Zassenhaus.borel G inf)).map
      (Work.Zassenhaus.borel G inf).subtype) = q := by
  -- `k = 0` forces `q = 1` and hence `|B| = 0`, impossible for a group.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hq1 : q = 1 := by rw [hq, pow_zero]
    exact absurd (show (0 : ℕ) < Nat.card (Work.Zassenhaus.borel G inf) from Nat.card_pos)
      (by rw [hB, hq1]; simp)
  · -- For `k ≥ 1`, `p` does not divide `(q - 1)/2`, so the `p`-part of `|B|` is `q`.
    have hfac : (q * ((q - 1) / 2)).factorization p = k := by
      have hcop : Nat.Coprime q ((q - 1) / 2) := by
        rw [hq]
        exact Work.Zassenhaus.zass_coprime_pow_half (Fact.out) hp hkpos
      rw [Nat.factorization_mul_apply_of_coprime hcop]
      have h1 : q.factorization p = k := by
        rw [hq, Nat.factorization_pow_self (Fact.out)]
      have h2 : ((q - 1) / 2).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        have hpdvd : p ∣ q := by
          rw [hq]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hkpos)
        have : Nat.Coprime p ((q - 1) / 2) := Nat.Coprime.coprime_dvd_left hpdvd hcop
        exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mp this
      rw [h1, h2, add_zero]
    -- `|↑P| = p ^ factorization |B| p = p ^ k = q`, and `map subtype` preserves cardinality.
    rw [Subgroup.card_subtype, Sylow.card_eq_multiplicity, hB, hfac, hq]

end Work.ZASS
