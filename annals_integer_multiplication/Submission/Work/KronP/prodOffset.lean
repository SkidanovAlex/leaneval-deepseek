import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.KronP.math
import Submission.Work.KronP.offDefs

/-!
# `Work.KronP.prodOffset`

Pure arithmetic fact for the Kronecker word: the packed product of two coordinate lists, shifted by
the digit offset, is a nonnegative integer with at most `2r` base-`2^{3p}` digits.

With `pack l b = Σ_j l[j]·2^{b·j}`, `C = digitOffset p (2r) = Σ_{m<2r} T·B^m`
(`T = 2^{3p-1}`, `B = 2^{3p}`), if `l₁, l₂` have length `r` and all entries of absolute value
`≤ 2^p`, then `0 ≤ pack l₁ (3p)·pack l₂ (3p) + C < B^{2r}`.

The ingredients are, with `X = pack l₁ (3p)`, `Y = pack l₂ (3p)`, `N = 2r`, `V = B^N`:

* `|pack l (3p)| ≤ 2^p·2^{3p(r-1)+1}`, hence `|X·Y| ≤ 2^{2(p + 3p(r-1) + 1)}`
  (`pack_natAbs_le`, `packMulPow`);
* `7·C ≤ 4·V` (`seven_digitOffset`; for `p = 1` this is sharp: `7·C = 4·8^N - 4`);
  it follows from `4 + 7T ≤ 4B`, proved by induction on `N` from `C_{N+1} = C_N + T·B^N`;
* `V/2 = 2^{3pN-1} ≤ C` (`last_digitOffset`: the `ℕ` summand `m = N-1` is exactly `2^{3pN-1}`).

Combining: `|X·Y| ≤ 2^{3pN-1} ≤ C` gives `0 ≤ X·Y + C`, and
`28(X·Y + C) ≤ 28(|X·Y| + C) ≤ 7V + 16V = 23V < 28V` gives `X·Y + C < V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KronP

open HvdH

/-! ## Bounds on the digit offset -/

/-- `7·C ≤ 4·B^N` for `C = Σ_{m<N} T·B^m`, `T = 2^{3p-1}`, `B = 2^{3p}`. -/
theorem seven_digitOffset (p N : ℕ) (hp : 1 ≤ p) :
    7 * digitOffset p N ≤ 4 * (2 : ℤ) ^ (3 * p * N) := by
  have hbase : (4 : ℤ) + 7 * (2 : ℤ) ^ (3 * p - 1) ≤ 4 * (2 : ℤ) ^ (3 * p) := by
    have h1 : (3 * p - 1) + 1 = 3 * p := by omega
    have hB : (2 : ℤ) ^ (3 * p) = (2 : ℤ) ^ (3 * p - 1) * 2 := by
      conv_lhs => rw [← h1]
      rw [pow_succ]
    have h4 : (4 : ℤ) ≤ (2 : ℤ) ^ (3 * p - 1) := by
      have hnat : 4 ≤ 2 ^ (3 * p - 1) := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 2 ≤ 3 * p - 1 by omega)
      have hc : ((2 ^ (3 * p - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (3 * p - 1) := by
        simp [Nat.cast_pow]
      have hcl : ((4 : ℕ) : ℤ) = (4 : ℤ) := by norm_num
      rw [← hc, ← hcl]
      exact_mod_cast hnat
    rw [hB]
    nlinarith
  induction N with
  | zero => simp [digitOffset]
  | succ N ih =>
    rw [digitOffset_succ]
    have hT : (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * N)
        = (2 : ℤ) ^ (3 * p - 1) * ((2 : ℤ) ^ (3 * p)) ^ N := by rw [pow_mul]
    rw [hT]
    calc 7 * (digitOffset p N + (2 : ℤ) ^ (3 * p - 1) * ((2 : ℤ) ^ (3 * p)) ^ N)
        = 7 * digitOffset p N
            + 7 * ((2 : ℤ) ^ (3 * p - 1) * ((2 : ℤ) ^ (3 * p)) ^ N) := by ring
      _ ≤ 4 * (2 : ℤ) ^ (3 * p * N)
            + 7 * ((2 : ℤ) ^ (3 * p - 1) * ((2 : ℤ) ^ (3 * p)) ^ N) := by linarith
      _ = (4 + 7 * (2 : ℤ) ^ (3 * p - 1)) * ((2 : ℤ) ^ (3 * p)) ^ N := by ring
      _ ≤ (4 * (2 : ℤ) ^ (3 * p)) * ((2 : ℤ) ^ (3 * p)) ^ N :=
            mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = 4 * (2 : ℤ) ^ (3 * p * (N + 1)) := by
            have he : 3 * p * (N + 1) = 3 * p * N + 3 * p := by ring
            rw [he, pow_add]
            ring

/-- The last term of the digit offset: `2^{3pN-1} ≤ C` for `N ≥ 1`. -/
theorem last_digitOffset (p N : ℕ) (hp : 1 ≤ p) (hN : 1 ≤ N) :
    (2 : ℤ) ^ (3 * p * N - 1) ≤ digitOffset p N := by
  revert hN
  apply Nat.le_induction
  · have h : digitOffset p 1 = (2 : ℤ) ^ (3 * p - 1) := by
      have hs := digitOffset_succ p 0
      rw [Nat.zero_add] at hs
      rw [hs]
      simp [digitOffset]
    have he : 3 * p * 1 - 1 = 3 * p - 1 := by omega
    rw [h, he]
  · intro N hN ih
    have hnonneg : (0 : ℤ) ≤ digitOffset p N := digitOffset_nonneg p N
    rw [digitOffset_succ]
    have hpow : (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * N)
        = (2 : ℤ) ^ (3 * p * (N + 1) - 1) := by
      rw [← pow_add]
      congr 1
      have he : 3 * p * (N + 1) = 3 * p * N + 3 * p := by ring
      rw [he]
      omega
    rw [← hpow]
    linarith

/-! ## The product of the two packed lists -/

/-- `|X·Y| ≤ 2^{2(p + 3p(r-1) + 1)}` for two packed coordinate lists of length `r` whose entries
have absolute value at most `2^p` (`X = pack l₁ (3p)`, `Y = pack l₂ (3p)`). -/
theorem packMulPow (p r : ℕ) (hp : 1 ≤ p) {l₁ l₂ : List ℤ}
    (h1 : l₁.length = r) (h2 : l₂.length = r)
    (hb1 : ∀ x ∈ l₁, x.natAbs ≤ 2 ^ p) (hb2 : ∀ x ∈ l₂, x.natAbs ≤ 2 ^ p) :
    (pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs
      ≤ 2 ^ (2 * (p + (3 * p * (r - 1) + 1))) := by
  have h3p : 1 ≤ 3 * p := by omega
  have hX := pack_natAbs_le l₁ (3 * p) (2 ^ p) h3p hb1
  have hY := pack_natAbs_le l₂ (3 * p) (2 ^ p) h3p hb2
  rw [h1] at hX
  rw [h2] at hY
  have hfac : 2 ^ p * 2 ^ (3 * p * (r - 1) + 1) = 2 ^ (p + (3 * p * (r - 1) + 1)) := by
    rw [← pow_add]
  rw [hfac] at hX hY
  have hmul : (pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs
      ≤ 2 ^ (p + (3 * p * (r - 1) + 1)) * 2 ^ (p + (3 * p * (r - 1) + 1)) :=
    Nat.mul_le_mul hX hY
  have heq : 2 ^ (p + (3 * p * (r - 1) + 1)) * 2 ^ (p + (3 * p * (r - 1) + 1))
      = 2 ^ (2 * (p + (3 * p * (r - 1) + 1))) := by
    rw [← pow_add]; congr 1; ring
  rwa [heq] at hmul

/-! ## The main lemma -/

theorem prodOffset (p r : ℕ) (hp : 1 ≤ p) (hrlt : r < 2 ^ (p - 1))
    {l₁ l₂ : List ℤ} (h1 : l₁.length = r) (h2 : l₂.length = r)
    (hb1 : ∀ x ∈ l₁, x.natAbs ≤ 2 ^ p) (hb2 : ∀ x ∈ l₂, x.natAbs ≤ 2 ^ p) :
    0 ≤ Work.KronP.pack l₁ (3 * p) * Work.KronP.pack l₂ (3 * p) + Work.KronP.digitOffset p (2 * r) ∧
      Work.KronP.pack l₁ (3 * p) * Work.KronP.pack l₂ (3 * p) + Work.KronP.digitOffset p (2 * r) <
        (2 : ℤ) ^ (3 * p * (2 * r)) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · -- `r = 0`: both lists are empty, `X = Y = C = 0` and the bound is `0 < 1`.
    subst hr0
    have hlen1 : l₁ = [] := List.length_eq_zero_iff.mp h1
    have hlen2 : l₂ = [] := List.length_eq_zero_iff.mp h2
    rw [hlen1, hlen2]
    simp [pack, digitOffset]
  -- main case `1 ≤ r`
  have hXY := packMulPow p r hp h1 h2 hb1 hb2
  have hsub : 3 * p * (r - 1) = 3 * p * r - 3 * p := by rw [Nat.mul_sub_left_distrib, mul_one]
  have hrhs : 3 * p * (2 * r) = 2 * (3 * p * r) := by ring
  have hA : 3 * p ≤ 3 * p * r := by
    calc 3 * p = 3 * p * 1 := by ring
      _ ≤ 3 * p * r := Nat.mul_le_mul_left _ hr1
  have hexpA : 2 * (p + (3 * p * (r - 1) + 1)) ≤ 3 * p * (2 * r) - 1 := by
    rw [hsub, hrhs]; omega
  have hexpB : 2 + 2 * (p + (3 * p * (r - 1) + 1)) ≤ 3 * p * (2 * r) := by
    rw [hsub, hrhs]; omega
  have hA1 : (pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs ≤ 2 ^ (3 * p * (2 * r) - 1) :=
    le_trans hXY (Nat.pow_le_pow_right (by norm_num : 0 < 2) hexpA)
  have hA4 : 4 * ((pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs)
      ≤ 2 ^ (3 * p * (2 * r)) := by
    calc 4 * ((pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs)
        ≤ 4 * 2 ^ (2 * (p + (3 * p * (r - 1) + 1))) := Nat.mul_le_mul_left 4 hXY
      _ = 2 ^ (2 + 2 * (p + (3 * p * (r - 1) + 1))) := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add]
      _ ≤ 2 ^ (3 * p * (2 * r)) := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexpB
  -- the `ℤ`-level bounds
  have hZ1 : ((pack l₁ (3 * p)).natAbs : ℤ) * ((pack l₂ (3 * p)).natAbs : ℤ)
      ≤ digitOffset p (2 * r) := by
    have h : (((pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs : ℕ) : ℤ)
        ≤ ((2 ^ (3 * p * (2 * r) - 1) : ℕ) : ℤ) := Nat.cast_le.mpr hA1
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact le_trans h (last_digitOffset p (2 * r) hp (by omega))
  have hZ2 : 4 * (((pack l₁ (3 * p)).natAbs : ℤ) * ((pack l₂ (3 * p)).natAbs : ℤ))
      ≤ (2 : ℤ) ^ (3 * p * (2 * r)) := by
    have h : ((4 * ((pack l₁ (3 * p)).natAbs * (pack l₂ (3 * p)).natAbs) : ℕ) : ℤ)
        ≤ ((2 ^ (3 * p * (2 * r)) : ℕ) : ℤ) := Nat.cast_le.mpr hA4
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h
  have hZ3 : 7 * digitOffset p (2 * r) ≤ 4 * (2 : ℤ) ^ (3 * p * (2 * r)) :=
    seven_digitOffset p (2 * r) hp
  have hXYle : pack l₁ (3 * p) * pack l₂ (3 * p)
      ≤ ((pack l₁ (3 * p)).natAbs : ℤ) * ((pack l₂ (3 * p)).natAbs : ℤ) := by
    have h := Int.le_natAbs (a := pack l₁ (3 * p) * pack l₂ (3 * p))
    rw [Int.natAbs_mul, Nat.cast_mul] at h
    exact h
  have hneg : -(((pack l₁ (3 * p)).natAbs : ℤ) * ((pack l₂ (3 * p)).natAbs : ℤ))
      ≤ pack l₁ (3 * p) * pack l₂ (3 * p) := by
    have h := le_abs_self (-(pack l₁ (3 * p) * pack l₂ (3 * p)))
    rw [abs_neg, Int.abs_eq_natAbs, Int.natAbs_mul, Nat.cast_mul] at h
    linarith
  constructor
  · linarith
  · have h28 : 28 * (pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r))
        ≤ 23 * (2 : ℤ) ^ (3 * p * (2 * r)) := by
      have h4 : 28 * (((pack l₁ (3 * p)).natAbs : ℤ) * ((pack l₂ (3 * p)).natAbs : ℤ))
          ≤ 7 * (2 : ℤ) ^ (3 * p * (2 * r)) := by nlinarith [hZ2]
      have h7 : 28 * digitOffset p (2 * r) ≤ 16 * (2 : ℤ) ^ (3 * p * (2 * r)) := by
        nlinarith [hZ3]
      nlinarith [hXYle, h4, h7]
    have h23 : 23 * (2 : ℤ) ^ (3 * p * (2 * r)) < 28 * (2 : ℤ) ^ (3 * p * (2 * r)) := by
      nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) (3 * p * (2 * r))]
    have hfin : 28 * (pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r))
        < 28 * (2 : ℤ) ^ (3 * p * (2 * r)) := by linarith
    exact Int.lt_of_mul_lt_mul_left hfin (by norm_num)

end Work.KronP
