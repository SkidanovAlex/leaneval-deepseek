import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting the occurrences of a minimal prime in a prime series

Let `I` be an ideal of a commutative ring `R` and let `P : Fin k → Ideal R` be a family of
prime ideals containing `I`.  Suppose that, at *every* prime `q ⊇ I`, the length of the
localization `(R/I)_q` equals the sum of the lengths `(R/P j)_q`:

`locLenAt q hq I = ∑ j, locLenAt q hq (P j)`.

Then for every minimal prime `q` of `I`, the number of indices `j` with `P j = q` is exactly
the multiplicity `primLen I q = length((R/I)_q)` of `I` at `q`.

The point is that for `q ∈ I.minimalPrimes` and `I ≤ P j` with `P j` prime, the localization
`(R/P j)_q` has length `1` when `P j = q` and length `0` otherwise: if `P j ≤ q` then
minimality of `q` forces `P j = q`, so `P j ≠ q` implies `P j ⊄ q` and the localization
vanishes.  Summing the indicator functions gives the count.
-/

namespace Work.BW

/-- For a minimal prime `q` of `I` and a prime `P j ⊇ I`, the local length of `P j` at `q`
is the indicator of `P j = q`. -/
private theorem locLenAt_eq_indicator {N : ℕ} (I : Ideal (MR N)) (Pj : Ideal (MR N))
    (hprime : Pj.IsPrime) (hle : I ≤ Pj) (q : Ideal (MR N)) (hq : q ∈ I.minimalPrimes) :
    locLenAt q hq.1.1 Pj = if Pj = q then (1 : ℕ∞) else 0 := by
  classical
  by_cases h : Pj = q
  · rw [h, locLenAt_self q hq.1.1]
    simp
  · -- `Pj ⊄ q`: otherwise minimality of `q` over `I` forces `Pj = q`.
    have hle' : ¬ Pj ≤ q := fun hle'' =>
      h (le_antisymm hle'' (hq.2 ⟨hprime, hle⟩ hle''))
    rw [locLenAt_eq_zero_of_not_le q hq.1.1 Pj hle']
    simp [h]

theorem count_eq_primLen {N : ℕ} (I : Ideal (MR N)) (k : ℕ) (P : Fin k → Ideal (MR N))
    (hprime : ∀ j, (P j).IsPrime) (hle : ∀ j, I ≤ P j)
    (hlen : ∀ (q : Ideal (MR N)) (hq : q.IsPrime), I ≤ q →
      locLenAt q hq I = ∑ j, locLenAt q hq (P j))
    (q : Ideal (MR N)) (hq : q ∈ I.minimalPrimes) :
    (Finset.univ.filter (fun j : Fin k => P j = q)).card = (primLen I q).toNat := by
  classical
  have hIq : I ≤ q := hq.1.2
  have hsum : locLenAt q hq.1.1 I = ∑ j, locLenAt q hq.1.1 (P j) := hlen q hq.1.1 hIq
  have hfinal : primLen I q = ((Finset.univ.filter (fun j : Fin k => P j = q)).card : ℕ∞) := by
    rw [primLen_eq_locLenAt I q hq.1.1, hsum]
    trans (∑ j : Fin k, if P j = q then (1 : ℕ∞) else 0)
    · exact Finset.sum_congr rfl fun j _ => locLenAt_eq_indicator I (P j) (hprime j) (hle j) q hq
    · exact sum_ite_eq_card (fun j : Fin k => P j = q)
  simpa using (congrArg ENat.toNat hfinal).symm

end Work.BW
