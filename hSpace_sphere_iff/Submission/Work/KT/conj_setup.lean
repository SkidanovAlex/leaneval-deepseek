import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.conj_setup` — elementary bookkeeping for the homotopy-conjugation factorisation

This file provides the two elementary ingredients used by
`Work.KT.homotopy_conj_factors`:

* `Work.KT.idem_step` — the one-step conjugating identity: for idempotents `p`, `q` in a ring,
  `(1 + (2p-1)(q-p)) * q = p * (1 + (2p-1)(q-p))`.
* `Work.KT.seg` — the clamped equal partition `j ↦ clamp (j/N)` of `[0,1]`, together with its basic
  boundary values and the Lipschitz estimate `dist (seg N (j+1)) (seg N j) ≤ 1/N`.
-/

namespace Work.KT

open Matrix

noncomputable section

/-- **One elementary conjugating step.**  If `p` and `q` are idempotents of a ring, then the
factor `1 + (2p - 1)(q - p)` intertwines `q` on the right with `p` on the left.  No unit
hypothesis is needed: this is a purely algebraic identity. -/
theorem idem_step {A : Type*} [Ring A] {p q : A} (hp : p * p = p) (hq : q * q = q) :
    (1 + (2 * p - 1) * (q - p)) * q = p * (1 + (2 * p - 1) * (q - p)) := by
  set a : A := 2 * p - 1 with ha
  have h1 : a * p = p := by
    rw [ha, sub_mul, one_mul, mul_assoc, hp, two_mul, add_sub_cancel_left]
  have h2 : p * a = p := by
    rw [ha, mul_sub, mul_one, two_mul, mul_add, hp, add_sub_cancel_left]
  have h3 : 1 + a = 2 * p := by
    rw [ha]; abel
  have hadd : q + a * q = (1 + a) * q := by
    rw [add_mul, one_mul]
  have hu_eq : 1 + a * (q - p) = 1 + a * q - p := by
    rw [mul_sub, h1]; abel
  have hL : (1 + a * q - p) * q = p * q := by
    rw [sub_mul, add_mul, one_mul, mul_assoc, hq, hadd, h3, mul_assoc, two_mul, add_sub_cancel_left]
  have hR : p * (1 + a * q - p) = p * q := by
    rw [mul_sub, mul_add, mul_one, ← mul_assoc, h2, hp]; abel
  rw [hu_eq, hL, hR]

/-- The `j`-th point of the equal partition of `[0,1]` into `N` pieces (clamped to `[0,1]`, so it
is defined for every `j : ℕ`). -/
def seg (N j : ℕ) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) ((j : ℝ) / N)

/-- The partition starts at `0`. -/
lemma seg_zero (N : ℕ) : seg N 0 = 0 := by
  ext
  simp [seg]

/-- The partition ends at `1`. -/
lemma seg_last (N : ℕ) (hN : N ≠ 0) : seg N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hseg : seg N N = Set.projIcc (0 : ℝ) 1 (by norm_num) 1 := by
    simp only [seg, div_self hN']
  rw [hseg, Set.projIcc_of_mem _ hmem]
  rfl

/-- Consecutive partition points of the `N`-fold partition are at distance at most `1/N`. -/
lemma dist_seg_le (N : ℕ) (hN : 0 < N) (j : ℕ) :
    dist (seg N (j + 1)) (seg N j) ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h : dist (seg N (j + 1)) (seg N j) ≤
      dist (((j : ℝ) + 1) / (N : ℝ)) ((j : ℝ) / (N : ℝ)) := by
    have hL := (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num)).dist_le_mul
      (((j : ℝ) + 1) / (N : ℝ)) (((j : ℝ)) / (N : ℝ))
    simpa [seg, one_mul] using hL
  refine h.trans ?_
  rw [Real.dist_eq, show ((j : ℝ) + 1) / (N : ℝ) - (j : ℝ) / (N : ℝ) = 1 / (N : ℝ) by
    field_simp; ring]
  rw [abs_of_nonneg (by positivity)]

end

end Work.KT
