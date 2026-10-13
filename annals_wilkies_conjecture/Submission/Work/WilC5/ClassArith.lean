import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.lt_iff_VLe_of_not_SameArch

namespace Work.WilC5

section ClassArithAux

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Elementary arithmetic of `VLe` / `SameArch`

Throughout, `VLe x y` is `∃ N, |y| ≤ (N+1)|x|` ("`y` is bounded by a natural multiple of `x`", i.e.
`x` is at least as big as `y`), and `SameArch x y` is `VLe x y ∧ VLe y x` ("`x` and `y` lie in the
same archimedean class").  This file assembles the six elementary facts about this vocabulary that
vdDMM §3 uses, packaged as the single theorem `ClassArith` below. -/

/-- The multiplier identity `(N*M + N + M) + 1 = (N+1) * (M+1)`, i.e. products of natural
multipliers are again natural multipliers. -/
private lemma cast_mul_succ {K : Type} [Field K] (N M : ℕ) :
    (((N * M + N + M : ℕ)) : K) + 1 = ((N : K) + 1) * ((M : K) + 1) := by
  push_cast; ring

/-- **`VLe` depends only on the archimedean class of its first argument.**  If `a` and `a'` have the
same value then "`b` is bounded by a multiple of `a`" is the same statement as "`b` is bounded by a
multiple of `a'`": composing the witness `|b| ≤ (M+1)|a|` with `|a| ≤ (N+1)|a'|` turns the
multipliers into the single natural multiplier `(M+1)(N+1) = (M*N + M + N) + 1`. -/
theorem SameArch_VLe_left {a a' b : K} (h : SameArch a a') : (VLe a b ↔ VLe a' b) := by
  obtain ⟨N, hN1, hN2⟩ := h
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M * N + M + N, ?_⟩
    rw [cast_mul_succ]
    calc |b| ≤ ((M : K) + 1) * |a| := hM
      _ ≤ ((M : K) + 1) * (((N : K) + 1) * |a'|) :=
            mul_le_mul_of_nonneg_left hN1 (by positivity)
      _ = ((M : K) + 1) * ((N : K) + 1) * |a'| := by ring
  · rintro ⟨M, hM⟩
    refine ⟨M * N + M + N, ?_⟩
    rw [cast_mul_succ]
    calc |b| ≤ ((M : K) + 1) * |a'| := hM
      _ ≤ ((M : K) + 1) * (((N : K) + 1) * |a|) :=
            mul_le_mul_of_nonneg_left hN2 (by positivity)
      _ = ((M : K) + 1) * ((N : K) + 1) * |a| := by ring

/-- **`VLe` depends only on the archimedean class of its second argument.**  Here the bound
`|b'| ≤ (N+1)|b|` is the one that has to be composed with `|b| ≤ (M+1)|a|`. -/
theorem SameArch_VLe_right {a b b' : K} (h : SameArch b b') : (VLe a b ↔ VLe a b') := by
  obtain ⟨N, hN1, hN2⟩ := h
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M * N + M + N, ?_⟩
    rw [cast_mul_succ]
    calc |b'| ≤ ((N : K) + 1) * |b| := hN2
      _ ≤ ((N : K) + 1) * (((M : K) + 1) * |a|) :=
            mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ((M : K) + 1) * ((N : K) + 1) * |a| := by ring
  · rintro ⟨M, hM⟩
    refine ⟨M * N + M + N, ?_⟩
    rw [cast_mul_succ]
    calc |b| ≤ ((N : K) + 1) * |b'| := hN1
      _ ≤ ((N : K) + 1) * (((M : K) + 1) * |a|) :=
            mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ((M : K) + 1) * ((N : K) + 1) * |a| := by ring

/-- **`SameArch a a'` forces `a = 0 ↔ a' = 0`**: only `0` has the value of `0`.  If `a = 0` then
`|a'| ≤ (N+1)·0 = 0`, and symmetrically. -/
theorem SameArch_eq_zero_iff {a a' : K} (h : SameArch a a') : (a = 0 ↔ a' = 0) := by
  obtain ⟨N, hN1, hN2⟩ := h
  constructor
  · intro ha
    refine abs_eq_zero.mp (le_antisymm ?_ (abs_nonneg a'))
    rw [ha, abs_zero, mul_zero] at hN2
    exact hN2
  · intro ha'
    refine abs_eq_zero.mp (le_antisymm ?_ (abs_nonneg a))
    rw [ha', abs_zero, mul_zero] at hN1
    exact hN1

/-- **The converse of `SameArch_pow`.**  For `x, y > 0` and `1 ≤ n`, if the `n`-th powers lie in
the same archimedean class then so do `x` and `y`.  (The exponent hypothesis is needed: at `n = 0`
both powers equal `1`.)

From `x^n ≤ C y^n` with `C = N+1 ≥ 1` we get `(C y)^n = C^n y^n ≥ C y^n ≥ x^n`, because
`C ≤ C^n` for `n ≠ 0`; monotonicity of `t ↦ t^n` on the nonnegative elements then gives `x ≤ C y`,
which is `VLe y x`.  The other direction is the same computation. -/
theorem SameArch_pow_iff_nat {x y : K} {n : ℕ} (hn : 1 ≤ n) (hx : 0 < x) (hy : 0 < y) :
    SameArch (x ^ n) (y ^ n) ↔ SameArch x y := by
  refine ⟨fun h => ?_, fun h => SameArch_pow h n⟩
  obtain ⟨N, hN1, hN2⟩ := h
  have hn0 : n ≠ 0 := by omega
  have hC1 : (1 : K) ≤ (N : K) + 1 := by
    have : (0 : K) ≤ (N : K) := Nat.cast_nonneg N
    linarith
  have hxpow : |x ^ n| = x ^ n := abs_of_pos (pow_pos hx n)
  have hypow : |y ^ n| = y ^ n := abs_of_pos (pow_pos hy n)
  rw [hxpow, hypow] at hN1 hN2
  have hCpow : ((N : K) + 1) ≤ ((N : K) + 1) ^ n := le_self_pow₀ hC1 hn0
  refine (SameArch_iff_VLe x y).mpr ⟨?_, ?_⟩
  · -- `VLe x y`
    refine ⟨N, ?_⟩
    rw [abs_of_pos hx, abs_of_pos hy]
    have hkey : y ^ n ≤ (((N : K) + 1) * x) ^ n := by
      calc y ^ n ≤ ((N : K) + 1) * x ^ n := hN2
        _ ≤ ((N : K) + 1) ^ n * x ^ n :=
              mul_le_mul_of_nonneg_right hCpow (pow_nonneg (le_of_lt hx) n)
        _ = (((N : K) + 1) * x) ^ n := by rw [mul_pow]
    exact le_of_pow_le_pow_left₀ hn0 (by positivity) hkey
  · -- `VLe y x`
    refine ⟨N, ?_⟩
    rw [abs_of_pos hx, abs_of_pos hy]
    have hkey : x ^ n ≤ (((N : K) + 1) * y) ^ n := by
      calc x ^ n ≤ ((N : K) + 1) * y ^ n := hN1
        _ ≤ ((N : K) + 1) ^ n * y ^ n :=
              mul_le_mul_of_nonneg_right hCpow (pow_nonneg (le_of_lt hy) n)
        _ = (((N : K) + 1) * y) ^ n := by rw [mul_pow]
    exact le_of_pow_le_pow_left₀ hn0 (by positivity) hkey

/-- **Powers of positive elements.**  For `x, y > 0` and a positive integer exponent `Q`, the
`Q`-th powers lie in the same archimedean class exactly when `x` and `y` do.  The content is the
converse direction: `v(x^Q) ∈ v(K^×)` implies `v(x) ∈ v(K^×)`, which is `SameArch_pow_iff_nat` for
natural exponents; a positive integer exponent is one, by `Int.toNat_of_nonneg`. -/
theorem SameArch_zpow_iff {x y : K} (Q : ℤ) (hx : 0 < x) (hy : 0 < y) (hQ : 0 < Q) :
    SameArch (x ^ Q) (y ^ Q) ↔ SameArch x y := by
  have hQ0 : 0 ≤ Q := le_of_lt hQ
  have hnat : ((Q.toNat : ℕ) : ℤ) = Q := Int.toNat_of_nonneg hQ0
  have hn : 1 ≤ Q.toNat := by
    rw [Int.le_toNat hQ0]
    exact hQ
  rw [← hnat, zpow_natCast, zpow_natCast]
  exact SameArch_pow_iff_nat hn hx hy

/-- **Elements of the same archimedean class lie on the same side of any `t` lying in a different
class.**  If `c, c' > 0` have the same value and `t` has a different value, then `c < t ↔ c' < t`.

If `c < t` and not `c' < t`, then `t ≤ c' ≤ (N+1)c`, and since `c < t` also `|c| ≤ |t|`; those two
bounds say exactly `SameArch c t`, contradiction.  The reverse direction is symmetric, using
`SameArch c' t` together with transitivity of `SameArch`. -/
theorem lt_iff_lt_of_SameArch_of_not {c c' t : K} (hc : 0 < c) (hc' : 0 < c')
    (h1 : SameArch c c') (h2 : ¬ SameArch c t) : (c < t ↔ c' < t) := by
  have hcc' : SameArch c c' := h1
  obtain ⟨N, hN1, hN2⟩ := h1
  have hcabs : |c| = c := abs_of_pos hc
  have hc'abs : |c'| = c' := abs_of_pos hc'
  constructor
  · intro hct
    by_contra hcon
    have htle : t ≤ c' := not_lt.mp hcon
    have htabs : |t| = t := abs_of_pos (lt_trans hc hct)
    have hV1 : VLe c t := ⟨N, by
      rw [htabs, hcabs]
      calc t ≤ c' := htle
        _ = |c'| := hc'abs.symm
        _ ≤ ((N : K) + 1) * |c| := hN2
        _ = ((N : K) + 1) * c := by rw [hcabs]⟩
    have hV2 : VLe t c := ⟨0, by rw [hcabs, htabs]; simpa using le_of_lt hct⟩
    exact h2 ((SameArch_iff_VLe c t).mpr ⟨hV1, hV2⟩)
  · intro hc't
    by_contra hcon
    have htle : t ≤ c := not_lt.mp hcon
    have htabs : |t| = t := abs_of_pos (lt_trans hc' hc't)
    have hV1 : VLe c' t := ⟨N, by
      rw [htabs, hc'abs]
      calc t ≤ c := htle
        _ = |c| := hcabs.symm
        _ ≤ ((N : K) + 1) * |c'| := hN1
        _ = ((N : K) + 1) * c' := by rw [hc'abs]⟩
    have hV2 : VLe t c' := ⟨0, by rw [hc'abs, htabs]; simpa using le_of_lt hc't⟩
    have h3 : SameArch c' t := (SameArch_iff_VLe c' t).mpr ⟨hV1, hV2⟩
    exact h2 (SameArch_equiv.trans hcc' h3)

end ClassArithAux

/-- Elementary arithmetic of the archimedean vocabulary `VLe`/`SameArch` in an ordered field
(`VLe a b` means "`b` is bounded by a natural multiple of `a`", i.e. `a` is at least as big as `b`;
`SameArch` is equality of archimedean classes, i.e. both `VLe` directions).  The six components are:
* `VLe` only depends on the archimedean class of its first (resp. second) argument;
* `SameArch a a'` forces `a = 0 ↔ a' = 0`;
* powers: for `x, y > 0` and `Q > 0`, `SameArch (x^Q) (y^Q) ↔ SameArch x y`;
* two positive elements in *different* archimedean classes are compared by `VLe`:
  `w < t ↔ (VLe t w ∧ ¬ VLe w t)` and `t < w ↔ (VLe w t ∧ ¬ VLe t w)`;
* two positive elements in the *same* class are on the same side of any `t` whose class differs:
  `c < t ↔ c' < t`. -/
theorem ClassArith {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    (∀ {a a' b : F}, Work.WilC5.SameArch a a' → (Work.WilC5.VLe a b ↔ Work.WilC5.VLe a' b)) ∧
    (∀ {a b b' : F}, Work.WilC5.SameArch b b' → (Work.WilC5.VLe a b ↔ Work.WilC5.VLe a b')) ∧
    (∀ {a a' : F}, Work.WilC5.SameArch a a' → (a = 0 ↔ a' = 0)) ∧
    (∀ {x y : F} (Q : ℤ), 0 < x → 0 < y → 0 < Q →
      (Work.WilC5.SameArch (x ^ Q) (y ^ Q) ↔ Work.WilC5.SameArch x y)) ∧
    (∀ {w t : F}, 0 < w → 0 < t → ¬ Work.WilC5.SameArch w t →
      ((w < t ↔ (Work.WilC5.VLe t w ∧ ¬ Work.WilC5.VLe w t)) ∧
       (t < w ↔ (Work.WilC5.VLe w t ∧ ¬ Work.WilC5.VLe t w)))) ∧
    (∀ {c c' t : F}, 0 < c → 0 < c' → Work.WilC5.SameArch c c' →
      ¬ Work.WilC5.SameArch c t → (c < t ↔ c' < t)) :=
  ⟨SameArch_VLe_left, SameArch_VLe_right, SameArch_eq_zero_iff,
   SameArch_zpow_iff, lt_iff_VLe_of_not_SameArch, lt_iff_lt_of_SameArch_of_not⟩

end Work.WilC5
