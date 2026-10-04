import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two sides of `Phi (Q2 R) X (bar X) = tr(Tmat R X * Rm R)`, expanded

This module fixes the explicit sums into which the two sides of

`Work.Diff.Alg.Pinch.Phi (Work.Diff.Alg.Pinch.Q2 R) X (Work.Diff.Alg.Pinch.bar X)
  = (Work.Diff.Alg.Pinch.Tmat R X * Work.Diff.Alg.Pinch.Rm R).trace`

unfold, so that the pieces can be proved separately:

* `S1`, `S2` -- the two sums appearing in the left-hand side
  `Phi (Q2 R) X (bar X) = 2 * S1 - 2 * S2` (from `Q2 R i j k l = 2∑(R i p k q * R j p l q) -
  2∑(R i p l q * R j p k q)`);
* `E1`, `E2`, `E3`, `E4` -- the four sums appearing in the right-hand side, coming from
  expanding `(Tmat R X * Rm R).trace` after writing `adMat X = Lmat X - Rmat X` and using
  `(Lmat X)ᴴ = (Lmat (bar X))ᵀ`, `(Rmat X)ᴴ = (Rmat (bar X))ᵀ`, namely
  `(Tmat R X * Rm R).trace = E1 - E2 - E3 + E4`.

The identifications `E1 = S1`, `E4 = S1`, `E2 = S2`, `E3 = S2`  (for `IsAlgCurv R`) are the
content of the index manipulation: each is a permutation of the six summation indices
combined with the antisymmetry and pair symmetry of `R`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The first sum of `Phi (Q2 R) X (bar X)`: `∑ R i p k q * R j p l q * X i j * conj (X k l)`. -/
noncomputable def S1 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
    (R i p k q : ℂ) * (R j p l q : ℂ) * X (i, j) * bar X (k, l)

/-- The second sum of `Phi (Q2 R) X (bar X)`: `∑ R i p l q * R j p k q * X i j * conj (X k l)`. -/
noncomputable def S2 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
    (R i p l q : ℂ) * (R j p k q : ℂ) * X (i, j) * bar X (k, l)

/-- First term of the expansion of `(Tmat R X * Rm R).trace`. -/
noncomputable def E1 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c,
    (R i j k l : ℂ) * (R c l a j : ℂ) * bar X (i, a) * X (k, c)

/-- Second term of the expansion of `(Tmat R X * Rm R).trace` (enters with a minus sign). -/
noncomputable def E2 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ d,
    (R i j k l : ℂ) * (R k d a j : ℂ) * bar X (i, a) * X (d, l)

/-- Third term of the expansion of `(Tmat R X * Rm R).trace` (enters with a minus sign). -/
noncomputable def E3 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ b, ∑ c,
    (R i j k l : ℂ) * (R c l i b : ℂ) * bar X (b, j) * X (k, c)

/-- Fourth term of the expansion of `(Tmat R X * Rm R).trace`. -/
noncomputable def E4 (R : Curv4 n) (X : Fin n × Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ b, ∑ d,
    (R i j k l : ℂ) * (R k d i b : ℂ) * bar X (b, j) * X (d, l)

end Work.Diff.Alg.Pinch
