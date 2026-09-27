import Mathlib

/-!
# Elementary Euclidean geometry on `Fin 3 → ℝ` and `Fin 2 → ℝ`

This file provides the hand-rolled Euclidean structure used by the proof of Mahler compactness
(component `C2` of the frozen EKL contract, lemma `Work.EKLComp.prove_X3`).

We deliberately avoid `EuclideanSpace` (a `WithLp` wrapper) and work directly with `Fin n → ℝ`,
whose default norm is the *sup* norm — which is exactly the norm used by `HasShortVec`/`Thick`
in `Submission/Work/EKLContract/Defs.lean`.
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Matrix

noncomputable section

/-- Euclidean inner product on `Fin 3 → ℝ`. -/
def dot3 (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

/-- Euclidean norm on `Fin 3 → ℝ`. -/
def enorm3 (v : Fin 3 → ℝ) : ℝ := Real.sqrt (dot3 v v)

/-- Euclidean inner product on `Fin 2 → ℝ`. -/
def dot2 (v w : Fin 2 → ℝ) : ℝ := ∑ i, v i * w i

/-- Euclidean norm on `Fin 2 → ℝ`. -/
def enorm2 (v : Fin 2 → ℝ) : ℝ := Real.sqrt (dot2 v v)

/-- The `i`-th standard basis vector of `Fin 3 → ℝ`. -/
def e3 (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The `i`-th column of a `3 × 3` matrix, as a vector. -/
def col3 (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : Fin 3 → ℝ := fun j => M j i

/-- The `i`-th column of a `2 × 2` matrix, as a vector. -/
def col2 (M : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : Fin 2 → ℝ := fun j => M j i

/-- Orthogonal projection `Fin 3 → ℝ → Fin 3 → ℝ` dropping the first coordinate, viewed as a
vector in `Fin 2 → ℝ`.  This is the orthogonal projection onto `(ℝ·e₀)ᗮ`. -/
def proj23 (x : Fin 3 → ℝ) : Fin 2 → ℝ := fun i => x i.succ

/-- The `2 × 2` determinant of two vectors of `Fin 2 → ℝ`. -/
def det2 (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

end

end Work.EKLComp
