import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# `YMulTwiddleProp`: the twiddle parameters of `yMulS`

The butterfly word (`HasPair`) applies the twiddle `y^{sgn·t}` to a coefficient vector by calling
the shift word `yMulS` (`HasYMulShift`) with a *pre-computed* residue `s` and sign `sg` (so that
the word costs `O(r p)` rather than the `O(p²)` of `HasYMul`, which has to perform an `Int.fmod`
of two `p`-bit numbers).

For the twiddle exponent `t = (2r/m)·j = j·2^sh < r` the caller passes

* `sgn = 1`:  `s = if t = 0 then 0 else r - t` and `sg = if t ≠ 0 then -1 else 1`;
* `sgn = -1`: `s = t` and `sg = 1`,

which is exactly what `yMulList r (sgn·t)` computes from its own floored residue
`(-(sgn·t)).fmod r` and sign `if sgn·t + (-(sgn·t)).fmod r = 0 then 1 else -1`.  This file proves
that the two parameter sets agree for every `0 ≤ t < r`, i.e. that the pre-computed shift form is
the same list operation as `yMulList` at the twiddle exponent `sgn·t`.

The only mathematical input is the evaluation of `Int.fmod` at `±t`:
`(-t).fmod r = r - t` and `t.fmod r = t` for `0 ≤ t < r` (recall `r > 0`, so the floored and the
Euclidean remainder agree).  Both are packaged as the helper lemmas below.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- For `0 < r` and `0 < t < r` the floored remainder of `-t` modulo `r` is `r - t`
(the nontrivial branch of `Int.neg_emod`; the divisibility branch is impossible since `t ≠ 0`). -/
lemma fmod_neg_natCast_of_pos {r t : ℕ} (hr : 0 < r) (ht : t < r) (ht0 : 0 < t) :
    (-(t : ℤ)).fmod (r : ℤ) = ((r - t : ℕ) : ℤ) := by
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr.le
  have hlt : (t : ℤ) < (r : ℤ) := by exact_mod_cast ht
  have hpos : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht0
  -- `r` does not divide `t`: a positive multiple of `r` is at least `r > t`.
  have hnd : ¬ ((r : ℤ) ∣ (t : ℤ)) := fun h => absurd (Int.le_of_dvd hpos h) (not_le.mpr hlt)
  rw [Int.fmod_eq_emod_of_nonneg _ hr0, Int.neg_emod, ite_eq_right hnd,
    Int.natAbs_natCast, Int.emod_eq_of_lt hpos.le hlt]
  exact (Nat.cast_sub ht.le).symm

/-- For `t < r` the floored remainder of `t` modulo `r` is `t` (in particular `0.fmod r = 0`). -/
lemma fmod_natCast_of_lt {r t : ℕ} (ht : t < r) : (t : ℤ).fmod (r : ℤ) = (t : ℤ) :=
  Int.fmod_eq_of_lt (by positivity) (by exact_mod_cast ht)

theorem yMulTwiddle : Work.SynFFT.YMulTwiddleProp := by
  intro r hr sgn hsg t ht w
  rcases hsg with h1 | h1
  · -- `sgn = 1`: the shift is `r - t` with sign `-1` for `t ≠ 0`, plain identity for `t = 0`
    subst h1
    by_cases ht0 : t = 0
    · subst ht0
      rw [yMulList_eq_yMulS]
      norm_num [Int.fmod_eq_emod_of_nonneg]
    · -- `0 < t < r`: `yMulList`'s residue of `-t` is `r - t` with sign `-1`
      rw [yMulList_eq_yMulS, one_mul,
        ite_eq_left (rfl : (1:ℤ) = 1), ite_eq_right ht0,
        ite_eq_left (show (1:ℤ) = 1 ∧ t ≠ 0 from ⟨rfl, ht0⟩),
        fmod_neg_natCast_of_pos hr ht (Nat.pos_of_ne_zero ht0), Int.toNat_natCast]
      have hsig : ¬ ((t : ℤ) + ((r - t : ℕ) : ℤ) = 0) := by
        have h : ((t : ℤ) + ((r - t : ℕ) : ℤ)) = (r : ℤ) := by
          rw [Nat.cast_sub ht.le]; ring
        rw [h]; exact_mod_cast hr.ne'
      rw [ite_eq_right hsig]
  · -- `sgn = -1`: the shift is `t` with sign `1`
    subst h1
    rw [yMulList_eq_yMulS,
      ite_eq_right (by norm_num : ¬ ((-1:ℤ) = 1)),
      ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (by norm_num)),
      show (-1:ℤ) * (t:ℤ) = -(t:ℤ) by ring]
    have hf : (-(-(t:ℤ))).fmod (r:ℤ) = (t:ℤ) := by
      rw [show (-(-(t:ℤ))) = (t:ℤ) by ring]; exact fmod_natCast_of_lt ht
    rw [hf, Int.toNat_natCast, ite_eq_left (show (-(t:ℤ)) + (t:ℤ) = 0 by ring)]

end Work.SynFFT
