import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.uparfacts
import Submission.Work.Params.nt1
import Submission.Work.Params.basic

/-!
# Cross-coprimality of the two families of `s_i` (paper §5.1)

The paper chooses the `s_i` to be *primes* in `((1-2η)t_i, (1-η)t_i]`, which makes them pairwise
coprime automatically.  The lead's PNT-free construction replaces them by the explicit numbers
`s_i = u₀ + F·(i+1)` (for the `t_i = r/2`) and `s_i = 2u₀ - 1 + 2F·(…)` (for the `t_i = r`), where
`F = (d-1)!` and `u₀ = Q(1+mF)`, `Q = ∏_{k<d}(2Fk+1)(2Fk-1)`.  Pairwise coprimality is then a
genuine arithmetic statement, proved here across the two families (the within-family cases are
`CoprimeG1`/`CoprimeG2`).

The key mechanism: `Q ∣ u₀`, so for any `k ≤ d-1` the whole factor `2Fk ± 1` of `Q` divides `u₀`.
If a prime `p` divided both `u₀ + Fa` and `2u₀ - 1 + 2Fc`, then (subtracting `2(u₀+Fa)` from the
second) `p ∣ 2F(a-c) + 1`; as `|a-c| ≤ d-2`, that number is `2Fm ± 1` for some `1 ≤ m ≤ d-1`, hence
divides `Q` and therefore `u₀`.  Then `p ∣ Fa`, so `p ∣ F` or `p ∣ a`; the first is absurd against
`2Fm ± 1 ≡ ±1 (mod p)`, and the second forces `p ≤ a ≤ d-1`, so `p ∣ F = (d-1)!` by `nt1`, again
absurd.  `Ffac_two_le` and `nt1` supply these last two facts.
-/

namespace Work.Params

open HvdH

theorem CoprimeCross (n : ℕ) {a c : ℕ} (ha : 1 ≤ a) (haD : a ≤ D - 1)
    (hc : 1 ≤ c) (hcD : c ≤ D - 1) :
    Nat.Coprime (upar n + Ffac * a) (2 * upar n - 1 + 2 * Ffac * c) := by
  have hc1 : 1 ≤ c := hc
  obtain ⟨hL, -, hQdvd, -, -⟩ := uparfacts n
  obtain ⟨hprimeF, hfac1, hfac2⟩ := nt1
  have hu1 : 1 ≤ upar n := le_trans (by unfold Lpar; exact Nat.le_add_left 1 _) hL
  have h2F : 1 ≤ 2 * Ffac :=
    le_trans (by norm_num : (1:ℕ) ≤ 2 * 2) (Nat.mul_le_mul_left 2 Ffac_two_le)
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpg
  have hpx : p ∣ upar n + Ffac * a := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpy : p ∣ 2 * upar n - 1 + 2 * Ffac * c := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  -- The integer combination `2·(u₀+Fa) - (2u₀-1+2Fc) = 2F·a - 2F·c + 1` is divisible by `p`.
  have hdvd : (p : ℤ) ∣ 2 * ((upar n + Ffac * a : ℕ) : ℤ)
      - ((2 * upar n - 1 + 2 * Ffac * c : ℕ) : ℤ) :=
    dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpx) 2)
      (Int.natCast_dvd_natCast.mpr hpy)
  have harith : 2 * ((upar n + Ffac * a : ℕ) : ℤ)
      - ((2 * upar n - 1 + 2 * Ffac * c : ℕ) : ℤ)
      = 2 * (Ffac : ℤ) * (a : ℤ) - 2 * (Ffac : ℤ) * (c : ℤ) + 1 := by
    have h1 : ((2 * upar n - 1 : ℕ) : ℤ) = 2 * (upar n : ℤ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ 2 * upar n by omega)]
      push_cast
      ring
    have hyZ : ((2 * upar n - 1 + 2 * Ffac * c : ℕ) : ℤ)
        = 2 * (upar n : ℤ) - 1 + 2 * (Ffac : ℤ) * (c : ℤ) := by
      push_cast [h1]
      ring
    have hxZ : ((upar n + Ffac * a : ℕ) : ℤ) = (upar n : ℤ) + (Ffac : ℤ) * (a : ℤ) := by
      push_cast
      ring
    rw [hxZ, hyZ]
    ring
  rw [harith] at hdvd
  -- `p ∣ F` plus `p ∣ 2Fm+1` is absurd, and so is `p ∣ F` plus `p ∣ 2Fm-1`.
  have aux : ∀ m : ℕ, p ∣ Ffac → p ∣ 2 * Ffac * m + 1 → False := by
    intro m hF hd
    have h2m : p ∣ 2 * Ffac * m := by
      obtain ⟨t, ht⟩ := hF
      exact ⟨2 * t * m, by rw [ht]; ring⟩
    have h1 : p ∣ 1 := by
      have h := Nat.dvd_sub hd h2m
      simpa using h
    exact hp.not_dvd_one h1
  have aux2 : ∀ m : ℕ, 1 ≤ m → p ∣ Ffac → p ∣ 2 * Ffac * m - 1 → False := by
    intro m hm hF hd
    have h2m : p ∣ 2 * Ffac * m := by
      obtain ⟨t, ht⟩ := hF
      exact ⟨2 * t * m, by rw [ht]; ring⟩
    have hle : 1 ≤ 2 * Ffac * m :=
      le_trans (by norm_num : (1:ℕ) ≤ 1 * 1) (Nat.mul_le_mul h2F hm)
    have h1 : p ∣ 1 := by
      have h := Nat.dvd_sub h2m hd
      rwa [Nat.sub_sub_self hle] at h
    exact hp.not_dvd_one h1
  -- A prime `p ≤ a ≤ D-1` divides `F`.
  have hpFacOf : p ∣ a → p ∣ Ffac := fun h =>
    hprimeF p hp (le_trans (Nat.le_of_dvd (by omega) h) (le_trans haD (Nat.sub_le D 1)))
  rcases lt_trichotomy a c with hac | hac | hac
  · -- a < c
    have hac' : a ≤ c := le_of_lt hac
    have hE : ((2 * Ffac * (c - a) - 1 : ℕ) : ℤ)
        = 2 * (Ffac : ℤ) * (c : ℤ) - 2 * (Ffac : ℤ) * (a : ℤ) - 1 := by
      have hle : 1 ≤ 2 * Ffac * (c - a) :=
        le_trans (by norm_num : (1:ℕ) ≤ 1 * 1)
          (Nat.mul_le_mul h2F (Nat.sub_pos_of_lt hac))
      rw [Nat.cast_sub hle]
      push_cast [Nat.cast_sub hac']
      ring
    have hE2 : 2 * (Ffac : ℤ) * (a : ℤ) - 2 * (Ffac : ℤ) * (c : ℤ) + 1
        = -(((2 * Ffac * (c - a) - 1 : ℕ)) : ℤ) := by rw [hE]; ring
    have hdivZ : (p : ℤ) ∣ -(((2 * Ffac * (c - a) - 1 : ℕ)) : ℤ) := hE2 ▸ hdvd
    have hdiv : p ∣ 2 * Ffac * (c - a) - 1 :=
      Int.natCast_dvd_natCast.mp (dvd_neg.mp hdivZ)
    have hm1 : 1 ≤ c - a := Nat.sub_pos_of_lt hac
    have hmD : c - a ≤ D - 1 := le_trans (Nat.sub_le c a) hcD
    have hpQ : p ∣ Qall := dvd_trans hdiv (hfac2 (c - a) hm1 hmD)
    have hpu : p ∣ upar n := dvd_trans hpQ hQdvd
    have hpFa : p ∣ Ffac * a := by
      have h := Nat.dvd_sub hpx hpu
      rwa [Nat.add_sub_cancel_left] at h
    have hpFac : p ∣ Ffac := by
      rcases (Nat.Prime.dvd_mul hp).mp hpFa with h | h
      · exact h
      · exact hpFacOf h
    exact aux2 (c - a) hm1 hpFac hdiv
  · -- a = c: the combination is `1`.
    have hE : 2 * (Ffac : ℤ) * (a : ℤ) - 2 * (Ffac : ℤ) * (c : ℤ) + 1 = (1 : ℤ) := by
      rw [hac]; ring
    have hd1 : (p : ℤ) ∣ (1 : ℤ) := hE ▸ hdvd
    exact hp.not_dvd_one (by exact_mod_cast hd1)
  · -- c < a
    have hca' : c ≤ a := le_of_lt hac
    have hE : ((2 * Ffac * (a - c) + 1 : ℕ) : ℤ)
        = 2 * (Ffac : ℤ) * (a : ℤ) - 2 * (Ffac : ℤ) * (c : ℤ) + 1 := by
      push_cast [Nat.cast_sub hca']
      ring
    have hdiv : p ∣ 2 * Ffac * (a - c) + 1 := Int.natCast_dvd_natCast.mp (hE.symm ▸ hdvd)
    have hm1 : 1 ≤ a - c := Nat.sub_pos_of_lt hac
    have hmD : a - c ≤ D - 1 := le_trans (Nat.sub_le a c) haD
    have hpQ : p ∣ Qall := dvd_trans hdiv (hfac1 (a - c) hm1 hmD)
    have hpu : p ∣ upar n := dvd_trans hpQ hQdvd
    have hpFa : p ∣ Ffac * a := by
      have h := Nat.dvd_sub hpx hpu
      rwa [Nat.add_sub_cancel_left] at h
    have hpFac : p ∣ Ffac := by
      rcases (Nat.Prime.dvd_mul hp).mp hpFa with h | h
      · exact h
      · exact hpFacOf h
    exact aux (a - c) hpFac hdiv

end Work.Params
