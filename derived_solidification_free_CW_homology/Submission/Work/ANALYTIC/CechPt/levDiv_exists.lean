import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels
import Submission.Work.ANALYTIC.CechPt.LevelAux

/-!
# Divisibility of the level structure on the dyadic nerves of the interval

The level-`n` dyadic nerve `Level.lev (2^(n+1)) p` (`Submission/Work/ANALYTIC/CechPt/
LevelDefs.lean`) has vertices `{0, …, 2^(n+1)-1}` and `p`-simplices of diameter at most one.

The subdivision `n ↦ n+1` refines the level-`n` nerve: dividing every coordinate of a
level-`(n+1)` simplex by `2` lands in the level-`n` nerve.  Iterating, the coordinatewise
division by `2^(n-m)` maps level-`n` simplices to level-`m` simplices whenever `m ≤ n`.  This
module constructs that map `trDiv` and proves the three properties the inverse system of the
Čech nerve needs: its explicit formula, the fact that `trDiv n n` is the identity, and
transitivity in the two level indices.

Main result: `levDiv_exists`.
-/

namespace Work.ANALYTIC.CechPt

/-- Coordinatewise division by `2^(n-m)`: a level-`n` simplex of the dyadic nerve of the
interval (coordinates in `{0, …, 2^(n+1)-1}`, diameter at most one) gives a level-`m` simplex
for every `m ≤ n`.  Division by `2^(n-m)` maps dyadic intervals of length `2^-(n+1)` into
dyadic intervals of length `2^-(m+1)` and preserves the "diameter at most one" condition,
because `⌊(v+1)/d⌋ ≤ ⌊v/d⌋ + 1` for `d = 2^(n-m) ≥ 1`. -/
private def trDiv (p n m : ℕ) (hm : m ≤ n) (y : Level.lev (2 ^ (n + 1)) p) :
    Level.lev (2 ^ (m + 1)) p :=
  Level.mkLev (fun i => ((y.1 i : Fin (2 ^ (n + 1))) : ℕ) / 2 ^ (n - m))
    (by
      intro i j
      have hd : 0 < 2 ^ (n - m) := pow_pos (by norm_num) _
      calc ((y.1 i : Fin (2 ^ (n + 1))) : ℕ) / 2 ^ (n - m)
          ≤ (((y.1 j : Fin (2 ^ (n + 1))) : ℕ) + 1) / 2 ^ (n - m) :=
            Nat.div_le_div_right (y.2 i j)
        _ ≤ (((y.1 j : Fin (2 ^ (n + 1))) : ℕ) + 2 ^ (n - m)) / 2 ^ (n - m) :=
            Nat.div_le_div_right (by omega)
        _ = ((y.1 j : Fin (2 ^ (n + 1))) : ℕ) / 2 ^ (n - m) + 1 := by
            rw [show (((y.1 j : Fin (2 ^ (n + 1))) : ℕ) + 2 ^ (n - m))
                  = ((y.1 j : Fin (2 ^ (n + 1))) : ℕ) + 1 * 2 ^ (n - m) by ring,
                Nat.add_mul_div_right _ 1 hd])
    (by
      intro i
      have hd : 0 < 2 ^ (n - m) := pow_pos (by norm_num) _
      rw [Nat.div_lt_iff_lt_mul hd]
      exact lt_of_lt_of_eq (y.1 i).isLt (by rw [← pow_add]; congr 1; omega))

private theorem trDiv_val (p n m : ℕ) (hm : m ≤ n) (y : Level.lev (2 ^ (n + 1)) p)
    (i : Fin (p + 1)) :
    ((trDiv p n m hm y).1 i : ℕ) = ((y.1 i : Fin (2 ^ (n + 1))) : ℕ) / 2 ^ (n - m) := rfl

theorem levDiv_exists (p : ℕ) :
    ∃ (tr : ∀ (n m : ℕ), m ≤ n → Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p →
        Work.ANALYTIC.CechPt.Level.lev (2 ^ (m + 1)) p),
      (∀ (n m : ℕ) (h : m ≤ n) (y : Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p)
          (i : Fin (p + 1)), ((tr n m h y).1 i : ℕ) = ((y.1 i : ℕ)) / 2 ^ (n - m)) ∧
      (∀ (n : ℕ) (y : Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p), tr n n le_rfl y = y) ∧
      (∀ (n m k : ℕ) (hm : m ≤ n) (hk : k ≤ m)
          (y : Work.ANALYTIC.CechPt.Level.lev (2 ^ (n + 1)) p),
        tr m k hk (tr n m hm y) = tr n k (hk.trans hm) y) := by
  refine ⟨fun n m h y => trDiv p n m h y, ?_, ?_, ?_⟩
  · intro n m h y i
    simp only [trDiv, Level.mkLev_val]
  · intro n y
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp only [trDiv, Level.mkLev_val]
    rw [Nat.sub_self, pow_zero, Nat.div_one]
  · intro n m k hm hk y
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp only [trDiv, Level.mkLev_val]
    rw [Nat.div_div_eq_div_mul]
    congr 1
    rw [← pow_add]
    congr 1
    omega

end Work.ANALYTIC.CechPt
