/-
Area BG (Bender–Glauberman 1981, Theorems A–C), pure arithmetic leaf.

**AR-BIG** (`ArithBigProp`): from the key identity `|G:H|(x-1)² = 2k²x(x+1)`
with `|G:H|` odd one deduces `1/3 < 2k²/|G:H| < 3` in the form
`|G:H| < 3·(2k²)` and `2k² < 3·|G:H|`.

The mathematics is: writing `L := 2k²` and `N := |G:H|` and using the identity
`N(x-1)² = L·x(x+1)`,

* `(3L - N)(x-1)² = L·(2x-1)(x-3)`,
* `(3N - L)(x-1)² = L·(2x²+5x-1)`,

so (with `x ≠ 1`, so that `(x-1)² > 0`) the two strict inequalities are
equivalent to `(2x-1)(x-3) > 0` and `2x²+5x-1 > 0`, which hold precisely for
`x ≥ 4` or `x ≤ -3`.  The exceptional integers `x ∈ {1,2,3,-2}` are excluded
by parity: reducing `N(x-1)² = 2k²x(x+1)` mod 2 and using `N` odd shows `x` is
odd (this kills `x = ±2`); `x = 1` gives `0 = 4k²` with `k > 0`; and `x = 3`
gives `N = 6k²`, forcing `N` even, a contradiction.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem arithBig : Work.GW2.C16.ArithBigProp := by
  intro N k x hNodd hkpos _ hx0 hxm1 hE
  have hKpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
  -- `N` odd, read in `ℤ`, says `2 ∤ N`.
  have hNoddZ : ¬ ((2 : ℤ) ∣ (N : ℤ)) := by
    rintro ⟨c, hc⟩
    obtain ⟨m, hm⟩ := hNodd
    omega
  -- `x = 1` is impossible: the identity would read `0 = 4k²`.
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hE
    nlinarith [hE, hKpos]
  -- Reducing the identity mod 2: `N` is odd and the right side is even, so
  -- `(x-1)²` is even, hence `x - 1` is even: `x` is odd.
  have hxodd : Odd x := by
    have h2 : (2 : ℤ) ∣ (N : ℤ) * (x - 1) ^ 2 :=
      ⟨(k : ℤ) ^ 2 * x * (x + 1), by rw [hE]; ring⟩
    have h3 : (2 : ℤ) ∣ (x - 1) ^ 2 := by
      rcases Int.prime_two.dvd_mul.mp h2 with h4 | h4
      · exact absurd h4 hNoddZ
      · exact h4
    have h4' : (2 : ℤ) ∣ (x - 1) := Int.prime_two.dvd_of_dvd_pow h3
    obtain ⟨c, hc⟩ := h4'
    exact ⟨c, by omega⟩
  -- `x = 3` is impossible: the identity would give `4N = 24k²`, i.e. `N = 6k²`,
  -- making `N` even.
  have hx3 : x ≠ 3 := by
    intro h
    rw [h] at hE
    have hE' : (N : ℤ) = 6 * (k : ℤ) ^ 2 := by nlinarith [hE]
    have hev : Even ((N : ℤ)) := ⟨3 * (k : ℤ) ^ 2, by linarith [hE']⟩
    have hodd : Odd ((N : ℤ)) := by
      obtain ⟨m, hm⟩ := hNodd
      exact ⟨(m : ℤ), by push_cast [hm]; ring⟩
    obtain ⟨a, ha⟩ := hev
    obtain ⟨b, hb⟩ := hodd
    omega
  -- Hence `x ≥ 5` or `x ≤ -3`.
  have hxcases : 5 ≤ x ∨ x ≤ -3 := by
    obtain ⟨c, hc⟩ := hxodd
    omega
  have hLpos : (0 : ℤ) < 2 * (k : ℤ) ^ 2 := by nlinarith [hKpos]
  have hsqpos : (0 : ℤ) < (x - 1) ^ 2 := sq_pos_of_ne_zero (by omega : x - 1 ≠ 0)
  -- The two linearised forms of the identity.
  have keyA : (3 * (2 * (k : ℤ) ^ 2) - (N : ℤ)) * (x - 1) ^ 2
      = (2 * (k : ℤ) ^ 2) * ((2 * x - 1) * (x - 3)) := by
    linear_combination -hE
  have keyB : (3 * (N : ℤ) - 2 * (k : ℤ) ^ 2) * (x - 1) ^ 2
      = (2 * (k : ℤ) ^ 2) * (2 * x ^ 2 + 5 * x - 1) := by
    linear_combination 3 * hE
  have hApos : 0 < 3 * (2 * (k : ℤ) ^ 2) - (N : ℤ) := by
    have hprod : 0 < (3 * (2 * (k : ℤ) ^ 2) - (N : ℤ)) * (x - 1) ^ 2 := by
      rw [keyA]
      exact mul_pos hLpos (by rcases hxcases with h | h <;> nlinarith [h])
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.mpr hsqpos.le)
  have hBpos : 0 < 3 * (N : ℤ) - 2 * (k : ℤ) ^ 2 := by
    have hsignB : 0 < 2 * x ^ 2 + 5 * x - 1 := by
      rcases hxcases with h | h
      · nlinarith [h]
      · have hh := mul_nonneg_of_nonpos_of_nonpos (show x + 3 ≤ 0 by omega)
          (show 2 * x - 1 ≤ 0 by omega)
        nlinarith [hh]
    have hprod : 0 < (3 * (N : ℤ) - 2 * (k : ℤ) ^ 2) * (x - 1) ^ 2 := by
      rw [keyB]
      exact mul_pos hLpos hsignB
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.mpr hsqpos.le)
  constructor
  · have h : (N : ℤ) < ((3 * (2 * k ^ 2) : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h
  · have h : (((2 * k ^ 2 : ℕ)) : ℤ) < ((3 * N : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h

end Work.BG
