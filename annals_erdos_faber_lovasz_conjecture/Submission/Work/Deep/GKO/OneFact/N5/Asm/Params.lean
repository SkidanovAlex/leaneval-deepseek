import Submission.Work.Deep.GKO.NarrowImports

/-!
# The numeric parameters of the elementary one-factorization route (N5)

This module fixes the concrete choices of the `o(n)`-sized parameters of the elementary N5
assembly (`Submission/Work/Deep/GKO/OneFact/N5/oneFactLowerReg_elementary.lean`), so that the
purely arithmetic part of the argument (all the "for `n` large enough" conditions) can be stated
and proved separately from the combinatorial part.

The vertices are split into `A ⊔ B = univ` with `|A| = |B| = n/2` (the balanced cut
`Work.Deep.GKO.OneFact.exists_balancedCut`), so that

* the inside degrees of an `r`-regular lower-regular graph are in `r/2 ± 2 n^{2/3}`
  (`dpar` is the upper bound for Vizing's theorem on the inside graph),
* the cross degrees are at least `D0par`,
* the number of Vizing colour classes is `dpar n r + 1`, every vertex is uncovered in at most
  `mpar n` of them, and the classes with more than `spar α n` uncovered vertices ("bad" classes)
  number at most `bpar α β ε n`.

`ηpar β ε` is the density of the re-matching budget `Lpar β ε n` per class, chosen so that
`Lpar` is far below `β ε n` (the room the lower regularity of the cross graph provides).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.GKO.OneFact.N5.Asm

noncomputable section

/-- Upper bound for the number of neighbours of a vertex inside its own side of a balanced cut of
an `r`-regular graph: `r/2 + 2 n^{2/3}`, and hence the number of colours Vizing needs for the
inside graph. -/
def dpar (n r : ℕ) : ℕ := Nat.floor ((r : ℝ) / 2 + 2 * (n : ℝ) ^ ((2 : ℝ) / 3))

/-- The tolerance of the inside colouring: derived from the balanced cut, every vertex has at
least `r/2 - 2 n^{2/3}` inside edges, so `dpar n r ≤ (inside degree) + tpar n`. -/
def tpar (n : ℕ) : ℕ := Nat.ceil (4 * (n : ℝ) ^ ((2 : ℝ) / 3)) + 1

/-- Every vertex is uncovered in at most `mpar n` colour classes. -/
def mpar (n : ℕ) : ℕ := tpar n + 1

/-- A colour class is *bad* if more than `spar α n` of its vertices are uncovered; the good
classes are then completed one at a time. -/
def spar (α : ℝ) (n : ℕ) : ℕ := Nat.floor (α * (n : ℝ) / 64)

/-- The density of the re-matching budget. -/
def ηpar (β ε : ℝ) : ℝ := (β * ε / 64) ^ 2

/-- The number of times a vertex may be re-matched by the completion of a good class. -/
def Lpar (β ε : ℝ) (n : ℕ) : ℕ := Nat.floor (ηpar β ε * (n : ℝ))

/-- Lower bound for the cross degree of a vertex of a balanced cut. -/
def D0par (n r : ℕ) : ℕ := Nat.floor ((r : ℝ) / 2 - 2 * (n : ℝ) ^ ((2 : ℝ) / 3))

/-- Upper bound for the number of bad colour classes: each bad class has more than `spar α n`
uncovered vertices while `∑_j |uncov N_j| ≤ n · mpar n`. -/
def bpar (α : ℝ) (n : ℕ) : ℕ := n * mpar n / (spar α n + 1)

/-- **The arithmetic side conditions of the N5 assembly**, at a fixed `n`, `r`, `ε`, `β = p - ε`.

They are the numerical hypotheses of the three nodes (N5a's colour count, N5c's per-class room,
and the matching absorber's three rooms) after the concrete substitution of the parameters
`dpar`, `tpar`, `mpar`, `spar`, `Lpar`, `D0par`, `bpar`; `b` ranges over the number of classes
that are dropped because they cover too few vertices, so that the inequalities can be used for
the actual (unknown) number of bad classes. -/
def ArithOK (α : ℝ) (n r : ℕ) (ε β : ℝ) : Prop :=
  0 < Lpar β ε n ∧
  ((mpar n + Lpar β ε n : ℕ) : ℝ) ≤ β * ε * (n : ℝ) / 4 ∧
  ε * (n : ℝ) + ((3 * (5 * n * mpar n / Lpar β ε n) + 14 * spar α n
      + mpar n + Lpar β ε n + 1 : ℕ) : ℝ) < (D0par n r : ℝ) ∧
  dpar n r + 1 ≤ r ∧
  (∀ b : ℕ, b ≤ bpar α n →
    8 * (Nat.sqrt ((b + Lpar β ε n) * n) + 3) ≤ D0par n r - (mpar n + Lpar β ε n)) ∧
  (∀ b : ℕ, b ≤ bpar α n →
    ((Nat.sqrt ((b + Lpar β ε n) * n) + 3 : ℕ) : ℝ) < β / 2 * ε * (n : ℝ)) ∧
  (∀ b : ℕ, b ≤ bpar α n →
    2 * ε * (n : ℝ) ≤ ((D0par n r - (mpar n + Lpar β ε n) : ℕ) : ℝ))

end

end Work.Deep.GKO.OneFact.N5.Asm
