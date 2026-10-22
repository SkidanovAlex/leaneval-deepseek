import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels

/-!
# Lifting a compatible sequence of level-`n` dyadic simplices to a point of the Čech nerve

`Work.ANALYTIC.CechPt.cechTerm p` is the light profinite set of `(p+1)`-tuples of points of the
Cantor set `C = {0,1}^ℕ` having the same binary expansion, and `Level.lev (2^(n+1)) p` is the
level-`n` dyadic nerve of the interval (simplices of diameter `≤ 1`).  The level-`n` projection
of a point of the Čech nerve is obtained by truncating its digits (`truncVal`).

This module proves that the projections are *surjective*: every sequence
`y : ∀ n, Level.lev (2^(n+1)) p` of dyadic simplices which is compatible with the division maps
(`((y (n+1)).1 i : ℕ) / 2 = ((y n).1 i : ℕ)`, the "halving" of a level-`(n+1)` simplex gives the
level-`n` simplex) is the truncation of a point of `cechTerm p`.

The construction is the obvious one: the digit sequence of the `i`-th coordinate is the sequence
of the last binary digits `(y n).1 i % 2` (so the coherence `hcompat` is exactly what makes
`truncOf` of that digit sequence reproduce `(y n).1 i`); realising that digit sequence by a point
of the Cantor set (`exists_coord_eq`) yields the tuple, which lies in `cechCover p` because all
the coordinates of `y n` have diameter `≤ 1`, so the digit sequences are "close at every level",
and `hclose` turns closeness at every level into equality of the binary expansion.

`hclose` is the real-analytic input, supplied as a hypothesis; it is the (true) statement that
`|truncOf m d - truncOf m e| ≤ 1` for all `m` forces `Real.ofDigits d = Real.ofDigits e`.
-/

open CategoryTheory Limits LightProfinite

noncomputable section

namespace Work.ANALYTIC.CechPt

open Level

/-- Coherent level data is the truncation of the digit sequence of its last digits: if a sequence
`a` of natural numbers has `2^(m+1)`-bounded terms and is compatible with halving
(`a (m+1) / 2 = a m`), then `truncOf` of its sequence of last digits returns `a` at every level.

This is the arithmetic content of the surjectivity of the level projections of `cechTerm p`. -/
theorem truncOf_mod_two_eq (n : ℕ) (a : ℕ → ℕ) (hlt : ∀ m, a m < 2 ^ (m + 1))
    (hcompat : ∀ m, a (m + 1) / 2 = a m) :
    truncOf n (fun m => (⟨a m % 2, by have := hlt m; omega⟩ : Fin 2)) = a n := by
  induction n with
  | zero =>
    simp only [truncOf, Nat.zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, mul_one]
    have h2 : a 0 < 2 := by have := hlt 0; norm_num at this; omega
    exact Nat.mod_eq_of_lt h2
  | succ n ih =>
    rw [truncOf_succ, ih]
    show 2 * a n + a (n + 1) % 2 = a (n + 1)
    have h := Nat.mod_add_div (a (n + 1)) 2
    rw [hcompat n] at h
    omega

/-- The last digit of the level-`n` truncation of a point of the Cantor set is its `n`-th digit. -/
theorem truncVal_mod_two (n : ℕ) (c : ↥cantor) : truncVal n c % 2 = (digitsOf c n : ℕ) := by
  simpa only [truncVal] using truncOf_mod_two n (digitsOf c)

theorem exists_cechTerm_of_compat (p : ℕ)
    (y : ∀ n : ℕ, Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p)
    (hcompat : ∀ (n : ℕ) (i : Fin (p + 1)), ((y (n + 1)).1 i : ℕ) / 2 = ((y n).1 i : ℕ))
    (hclose : ∀ (d e : ℕ → Fin 2),
      (∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m d ≤ Work.ANALYTIC.CechPt.truncOf m e + 1) →
      (∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m e ≤ Work.ANALYTIC.CechPt.truncOf m d + 1) →
      Real.ofDigits d = Real.ofDigits e) :
    ∃ x : ↥(Work.ANALYTIC.CechPt.cechTerm p),
      ∀ (n : ℕ) (i : Fin (p + 1)), ((y n).1 i : ℕ) = Work.ANALYTIC.CechPt.truncVal n (x.1 i) := by
  -- the digit sequence of the `i`-th coordinate
  let d : Fin (p + 1) → ℕ → Fin 2 := fun i n =>
    ⟨((y n).1 i : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩
  -- `truncOf` of the digit sequence of a coordinate returns the coordinate of `y`
  have hd : ∀ (i : Fin (p + 1)) (n : ℕ), truncOf n (d i) = ((y n).1 i : ℕ) := by
    intro i n
    have h := truncOf_mod_two_eq n (fun m => ((y m).1 i : ℕ))
      (fun m => ((y m).1 i).isLt) (fun m => hcompat m i)
    simpa only [d] using h
  -- realised by points of the Cantor set
  choose c hc using fun i => exists_coord_eq (d i)
  have hdig : ∀ i, digitsOf (c i) = d i := fun i => funext (hc i)
  refine ⟨⟨c, mem_cechCover.mpr ?_⟩, ?_⟩
  · -- the coordinates have the same binary expansion, by `hclose` and the diameter condition
    intro i j
    apply Subtype.ext
    rw [binExp_coe, binExp_coe, hdig i, hdig j]
    exact hclose (d i) (d j)
      (fun m => by rw [hd i m, hd j m]; exact (y m).2 i j)
      (fun m => by rw [hd i m, hd j m]; exact (y m).2 j i)
  · -- and they reproduce `y` at every level
    intro n i
    simp only [truncVal, hdig i]
    exact (hd i n).symm

end Work.ANALYTIC.CechPt
