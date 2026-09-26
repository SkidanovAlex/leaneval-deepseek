import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs
import Submission.Work.Rigidity.SigmaEntryBound.rnd_spec

namespace Work.Rigidity.SigmaEntryBound

open Matrix

/-!
# The one-step estimates for the Euclidean recursion `nxt`

This file proves `Work.Rigidity.SigmaEntryBound.nxt_estimates`, the collection of numerical
estimates satisfied by one step of the Euclidean recursion on `2 × 2` integer matrices.

For `M = !![a,b;c,d]` with `c ≠ 0` and `q = quo M = rnd a c`, `r = remz M = a - q c` one has
`M = T^q · S · nxt M` with `nxt M = !![c, d; -r, -(b - q d)]`, and the estimates say:

* `2 |r| ≤ |c|` — the remainder is at most half the divisor (this is `rnd_spec`);
* `uZ (nxt M) ≤ uZ M` — the "size" `|a| + |c|` of the first column does not increase;
* `(1 + |q|) uZ (nxt M) ≤ 3 uZ M` — the growth per step is controlled by `|q|`;
* `muZ (nxt M) < muZ M` — the termination measure `uZ ^ 2 + |c|` strictly decreases;
* `frob2Z (nxt M) ≤ 2 (1 + |q|) ^ 2 frob2Z M` — the squared Frobenius norm grows by at most
  a factor `2 (1 + |q|) ^ 2`.

The key inputs are `rnd_spec` (the two numerical estimates for the nearest-integer rounding)
together with the elementary remark that, whenever `q ≠ 0`, `|q| |c| ≥ |c| ≥ 2|r|` and hence
`|r| ≤ |a|`, since `|q c| ≤ |a| + |r|`.
-/

/-- `(x + y) ^ 2 ≤ 2 x ^ 2 + 2 y ^ 2` for natural numbers, from `2 x y ≤ x ^ 2 + y ^ 2`. -/
lemma add_sq_le_two_mul_sq (x y : ℕ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [two_mul_le_add_sq x y]

/-- Auxiliary arithmetic: if `r ≤ c` and `2 x c ≤ 2 u + c`, then
`(1 + x) (c + r) ≤ 3 (u + c)`. -/
lemma one_add_mul_le_three (x u c r : ℕ) (h1 : r ≤ c) (h2 : 2 * x * c ≤ 2 * u + c) :
    (1 + x) * (c + r) ≤ 3 * (u + c) := by
  have hCR : c + r ≤ 2 * c := by omega
  have h3 : 2 * c + 2 * x * c ≤ 2 * c + (2 * u + c) := Nat.add_le_add_left h2 _
  calc (1 + x) * (c + r) ≤ (1 + x) * (2 * c) := Nat.mul_le_mul_left _ hCR
    _ = 2 * c + 2 * x * c := by ring
    _ ≤ 2 * c + (2 * u + c) := h3
    _ = 2 * u + 3 * c := by ring
    _ ≤ 3 * u + 3 * c := by omega
    _ = 3 * (u + c) := by ring

/-- Auxiliary arithmetic: if `r ≤ u` and `r < c`, then `(c + r) ^ 2 + r < (u + c) ^ 2 + c`. -/
lemma sq_add_lt_sq_add (u c r : ℕ) (h1 : r ≤ u) (h2 : r < c) :
    (c + r) ^ 2 + r < (u + c) ^ 2 + c := by
  have hle : c + r ≤ u + c := by omega
  calc (c + r) ^ 2 + r < (c + r) ^ 2 + c := Nat.add_lt_add_left h2 _
    _ ≤ (u + c) ^ 2 + c := Nat.add_le_add_right (Nat.pow_le_pow_left hle 2) _

/-- Auxiliary arithmetic for the Frobenius estimate: if `r ≤ c` and `e ≤ 2 b ^ 2 + 2 x ^ 2 d ^ 2`
then `c ^ 2 + d ^ 2 + r ^ 2 + e ≤ 2 (1 + x) ^ 2 (u ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)`. -/
lemma frob_estimate_aux (x u b c d r e : ℕ) (h1 : r ≤ c)
    (h2 : e ≤ 2 * b ^ 2 + 2 * x ^ 2 * d ^ 2) :
    c ^ 2 + d ^ 2 + r ^ 2 + e ≤ 2 * (1 + x) ^ 2 * (u ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hr : r ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left h1 2
  have hA : 2 ≤ 2 * (1 + x) ^ 2 := by
    have h : 1 ≤ (1 + x) ^ 2 := Nat.one_le_pow 2 (1 + x) (by omega)
    omega
  have hB : 1 + 2 * x ^ 2 ≤ 2 * (1 + x) ^ 2 := by
    have h : 2 * (1 + x) ^ 2 = 2 + 4 * x + 2 * x ^ 2 := by ring
    omega
  have hb : 2 * b ^ 2 ≤ 2 * (1 + x) ^ 2 * b ^ 2 := by
    have := Nat.mul_le_mul_right (b ^ 2) hA
    rwa [show (2 * (1 + x) ^ 2) * b ^ 2 = 2 * (1 + x) ^ 2 * b ^ 2 by ring] at this
  have hc : 2 * c ^ 2 ≤ 2 * (1 + x) ^ 2 * c ^ 2 := by
    have := Nat.mul_le_mul_right (c ^ 2) hA
    rwa [show (2 * (1 + x) ^ 2) * c ^ 2 = 2 * (1 + x) ^ 2 * c ^ 2 by ring] at this
  have hd : d ^ 2 + 2 * x ^ 2 * d ^ 2 ≤ 2 * (1 + x) ^ 2 * d ^ 2 := by
    have := Nat.mul_le_mul_right (d ^ 2) hB
    rwa [show (1 + 2 * x ^ 2) * d ^ 2 = d ^ 2 + 2 * x ^ 2 * d ^ 2 by ring,
        show (2 * (1 + x) ^ 2) * d ^ 2 = 2 * (1 + x) ^ 2 * d ^ 2 by ring] at this
  have step1 : c ^ 2 + d ^ 2 + r ^ 2 + e ≤ 2 * c ^ 2 + d ^ 2 + (2 * b ^ 2 + 2 * x ^ 2 * d ^ 2) := by
    omega
  calc c ^ 2 + d ^ 2 + r ^ 2 + e
      ≤ 2 * c ^ 2 + d ^ 2 + (2 * b ^ 2 + 2 * x ^ 2 * d ^ 2) := step1
    _ = 2 * b ^ 2 + 2 * c ^ 2 + (d ^ 2 + 2 * x ^ 2 * d ^ 2) := by ring
    _ ≤ 2 * (1 + x) ^ 2 * b ^ 2 + 2 * (1 + x) ^ 2 * c ^ 2 + 2 * (1 + x) ^ 2 * d ^ 2 := by
          omega
    _ ≤ 2 * (1 + x) ^ 2 * u ^ 2 + 2 * (1 + x) ^ 2 * b ^ 2 + 2 * (1 + x) ^ 2 * c ^ 2
          + 2 * (1 + x) ^ 2 * d ^ 2 := by omega
    _ = 2 * (1 + x) ^ 2 * (u ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by ring

/-- The five one-step estimates, stated for the explicit matrix `!![a,b;c,d]` with `c ≠ 0`. -/
lemma nxt_estimates_fin_two (a b c d : ℤ) (hc : c ≠ 0) :
    (2 * (remz !![a,b;c,d]).natAbs ≤ c.natAbs) ∧
    (uZ (nxt !![a,b;c,d]) ≤ uZ !![a,b;c,d]) ∧
    ((1 + (quo !![a,b;c,d]).natAbs) * uZ (nxt !![a,b;c,d]) ≤ 3 * uZ !![a,b;c,d]) ∧
    (muZ (nxt !![a,b;c,d]) < muZ !![a,b;c,d]) ∧
    (frob2Z (nxt !![a,b;c,d]) ≤ 2 * (1 + (quo !![a,b;c,d]).natAbs) ^ 2 * frob2Z !![a,b;c,d]) := by
  have hq : quo !![a,b;c,d] = rnd a c := by simp [quo, hc]
  have hrz : remz !![a,b;c,d] = a - rnd a c * c := by simp [remz, hq]
  have hnx : nxt !![a,b;c,d] = !![c, d; -(a - rnd a c * c), -(b - rnd a c * d)] := by
    simp [nxt, hq, hrz, hc]
  rw [hnx, hrz, hq]
  simp only [uZ, frob2Z, muZ]
  try simp
  -- the goal now involves only `a.natAbs`, `b.natAbs`, `c.natAbs`, `d.natAbs`,
  -- `(rnd a c).natAbs` and the two remainders `a - rnd a c * c` and `b - rnd a c * d`
  have hs := rnd_spec a c hc
  have hswap : (rnd a c * c - a).natAbs = (a - rnd a c * c).natAbs := by
    have h : rnd a c * c - a = -(a - rnd a c * c) := by ring
    rw [h, Int.natAbs_neg]
  have h1 : 2 * (a - rnd a c * c).natAbs ≤ c.natAbs := hs.1
  have h2 : 2 * (rnd a c).natAbs * c.natAbs ≤ 2 * a.natAbs + c.natAbs := hs.2
  have hrc : (rnd a c * c - a).natAbs ≤ c.natAbs := by rw [hswap]; omega
  have hstrict : (rnd a c * c - a).natAbs < c.natAbs := by rw [hswap]; omega
  -- `|rnd a c * c| ≤ |a| + |rem|`, hence `|rem| ≤ |a|`
  have h3 : (rnd a c).natAbs * c.natAbs ≤ a.natAbs + (a - rnd a c * c).natAbs := by
    have h := Int.natAbs_sub_le a (a - rnd a c * c)
    rw [show a - (a - rnd a c * c) = rnd a c * c by ring, Int.natAbs_mul] at h
    exact h
  have h4 : (rnd a c * c - a).natAbs ≤ a.natAbs := by
    rw [hswap]
    rcases eq_or_ne (rnd a c) 0 with hq0 | hq0
    · rw [hq0]; simp
    · have hq1 : 1 ≤ (rnd a c).natAbs := Int.natAbs_pos.mpr hq0
      have hmm : c.natAbs ≤ (rnd a c).natAbs * c.natAbs := Nat.le_mul_of_pos_left c.natAbs hq1
      omega
  -- the second entry `- (b - rnd a c * d)` of `nxt`
  have horig : (b - rnd a c * d).natAbs ≤ b.natAbs + (rnd a c).natAbs * d.natAbs := by
    have h := Int.natAbs_sub_le b (rnd a c * d)
    rw [Int.natAbs_mul] at h
    exact h
  have hswap2 : (rnd a c * d - b).natAbs = (b - rnd a c * d).natAbs := by
    have h : rnd a c * d - b = -(b - rnd a c * d) := by ring
    rw [h, Int.natAbs_neg]
  have h5 : (rnd a c * d - b).natAbs ^ 2 ≤ 2 * b.natAbs ^ 2 + 2 * (rnd a c).natAbs ^ 2 * d.natAbs ^ 2 := by
    rw [hswap2]
    calc (b - rnd a c * d).natAbs ^ 2
        ≤ (b.natAbs + (rnd a c).natAbs * d.natAbs) ^ 2 := Nat.pow_le_pow_left horig 2
      _ ≤ 2 * b.natAbs ^ 2 + 2 * ((rnd a c).natAbs * d.natAbs) ^ 2 := add_sq_le_two_mul_sq _ _
      _ = 2 * b.natAbs ^ 2 + 2 * (rnd a c).natAbs ^ 2 * d.natAbs ^ 2 := by ring
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · omega
  · exact one_add_mul_le_three (rnd a c).natAbs a.natAbs c.natAbs
      (rnd a c * c - a).natAbs hrc h2
  · exact sq_add_lt_sq_add a.natAbs c.natAbs (rnd a c * c - a).natAbs h4 hstrict
  · exact frob_estimate_aux (rnd a c).natAbs a.natAbs b.natAbs c.natAbs d.natAbs
      (rnd a c * c - a).natAbs ((rnd a c * d - b).natAbs ^ 2) hrc h5

theorem nxt_estimates {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 ≠ 0) :
    (2 * (remz M).natAbs ≤ (M 1 0).natAbs) ∧
    (uZ (nxt M) ≤ uZ M) ∧
    ((1 + (quo M).natAbs) * uZ (nxt M) ≤ 3 * uZ M) ∧
    (muZ (nxt M) < muZ M) ∧
    (frob2Z (nxt M) ≤ 2 * (1 + (quo M).natAbs) ^ 2 * frob2Z M) := by
  have hc : M 1 0 ≠ 0 := h
  have key := nxt_estimates_fin_two (M 0 0) (M 0 1) (M 1 0) (M 1 1) hc
  rw [Matrix.eta_fin_two M]
  simpa using key

end Work.Rigidity.SigmaEntryBound
