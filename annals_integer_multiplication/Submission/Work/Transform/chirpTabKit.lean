import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs
import Submission.Work.Transform.phiAux

/-!
# Helper lemmas for the chirp table word (`Work.Transform.chirpTabWordBnd`)

The word `chirpTabWordBnd` builds, from `int p :: int t`, the table `m ↦ ζ_t^{m²}` (`m < t`),
where `ζ_t = e^{πi/t}`.  Each entry is produced by `FxLib.cis` (`e^{2πi j/k}` with error `< 2`),
which computes `e^{2πi m²/(2t)} = ζ_t^{m²}` — the identity `zeta_double` / `exp_cis_eq_zeta`
below.  The remaining lemmas are the encoding-size estimates (`isz`, `vsz`) used in the cost
bounds and the small index lemmas for the list `(List.range t).map …` of records.

Contents:

* `zeta_double`, `exp_cis_eq_zeta` — the arithmetic identity identifying `cis`'s result with `ζ_t^{m²}`;
* `isz_natCast_le`, `isz_two_mul_le`, `isz_mul_self_le` — `isz` bounds from `n < 2^p`;
* `getD_map_range`, `getD_range` — indexing the index list.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- `ζ_{t+t}^{m+m} = ζ_t^m`, i.e. `ζ_{2t}^{2m} = ζ_t^m`: the phase `2πi m/(2t)` of a `cis`-call with
denominator `t + t` is the phase `πi m/t` of the chirp `ζ_t^m`. -/
lemma zeta_double (t m : ℕ) (ht : t ≠ 0) : zeta (t + t) (m + m) = zeta t m := by
  rw [zeta, zeta]
  congr 1
  have h2 : ((t + t : ℕ) : ℂ) = 2 * (t : ℂ) := by push_cast; ring
  have hm : ((m + m : ℕ) : ℂ) = 2 * (m : ℂ) := by push_cast; ring
  rw [h2, hm]
  field_simp

/-- The value of the `cis`-word on `(j, t + t)`: `e^{2πi j/(2t)} = ζ_t^j`. -/
lemma exp_cis_eq_zeta (t j : ℕ) (ht : t ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (((j : ℤ)) : ℂ) / ((t + t : ℕ) : ℂ)) =
      zeta t j := by
  rw [← zeta_double t j ht]
  show Complex.exp (2 * Real.pi * Complex.I * (((j : ℤ)) : ℂ) / ((t + t : ℕ) : ℂ)) =
    Complex.exp (Real.pi * Complex.I * ((j + j : ℕ) : ℂ) / ((t + t : ℕ) : ℂ))
  congr 1
  push_cast
  ring

/-- `isz n ≤ p + 2` when `n < 2^p`. -/
lemma isz_natCast_le {n p : ℕ} (h : n < 2 ^ p) : isz (n : ℤ) ≤ p + 2 := by
  have h1 : (n : ℤ).natAbs = n := Int.natAbs_natCast n
  have h2 : n.size ≤ p := Nat.size_le.mpr h
  simp only [isz, h1]
  omega

/-- `isz (t + t) ≤ p + 3` when `t < 2^p`. -/
lemma isz_two_mul_le {t p : ℕ} (h : t < 2 ^ p) : isz ((t + t : ℕ) : ℤ) ≤ p + 3 := by
  have h1 : (t + t : ℕ) < 2 ^ (p + 1) := by
    rw [pow_succ]
    have : (2 : ℕ) ^ p * 2 = 2 ^ p + 2 ^ p := by ring
    omega
  have h2 : (t + t).size ≤ p + 1 := Nat.size_le.mpr h1
  have h3 : ((t + t : ℕ) : ℤ).natAbs = (t + t : ℕ) := Int.natAbs_natCast _
  simp only [isz, h3]
  omega

/-- `isz (m * m) ≤ 2p + 2` when `m < 2^p`. -/
lemma isz_mul_self_le {m p : ℕ} (h : m < 2 ^ p) : isz (((m * m : ℕ)) : ℤ) ≤ 2 * p + 2 := by
  have h1 : m * m < 2 ^ (2 * p) := by
    have h2 : m * m < 2 ^ p * 2 ^ p := mul_lt_mul'' h h (Nat.zero_le _) (Nat.zero_le _)
    have h3 : (2 : ℕ) ^ p * 2 ^ p = 2 ^ (2 * p) := by
      rw [← pow_add, two_mul p]
    rwa [h3] at h2
  have h4 : (m * m).size ≤ 2 * p := Nat.size_le.mpr h1
  have h5 : ((m * m : ℕ) : ℤ).natAbs = (m * m : ℕ) := Int.natAbs_natCast _
  simp only [isz, h5]
  omega

/-- The `i`-th element of `(List.range n).map f` is `f i` (for `i < n`). -/
lemma getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- `(List.range n).getD i 0 = i` for `i < n`. -/
lemma getD_range {i n : ℕ} (h : i < n) : (List.range n).getD i 0 = i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

end Work.Transform
