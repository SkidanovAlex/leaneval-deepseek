import Mathlib
import Submission.Work.HP.Defs

/-!
# Integer data of a pair of vectors: the "first case" test quadric

For `x y : Fin (n+1) → ℤ` we set

* `pairA x = ∑ i, x i ^ 2`, `pairB y = ∑ i, y i ^ 2`, `pairC x y = ∑ i, x i * y i`;
* `pairW x y = pairA x * pairB y - pairC x y ^ 2`, the squared covolume of `ℤx ⊕ ℤy`;
* `pairU x y = pairA x • y - pairC x y • x` and `pairV x y = pairB y • x - pairC x y • y`.

One checks `⟨pairU, x⟩ = 0`, `⟨pairU, y⟩ = pairW`, `⟨pairV, x⟩ = pairW`, `⟨pairV, y⟩ = 0`, and
`‖pairU‖² = pairA * pairW`, `‖pairV‖² = pairB * pairW`.  Consequently the integral quadratic
form `σ(pairU, pairV)` (coefficient vector `sigma n (pairU x y) (pairV x y)`) vanishes at `x`
and `y`, takes the value `pairW²` at `x + y`, and has norm at most `√2‖pairU‖‖pairV‖`.
This is the test quadric used to bound the first-case vectors of the dual lattice
`dualLat (realify (Gam 2 n x y))` from below.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Vero

open Work.HP Finset

variable {n : ℕ}

/-- `∑ i, x i ^ 2`, the squared Euclidean norm of `x`, as an integer. -/
def pairA (x : Fin (n + 1) → ℤ) : ℤ := ∑ i, x i ^ 2

/-- `∑ i, x i * y i`, the Euclidean pairing of `x` and `y`, as an integer. -/
def pairC (x y : Fin (n + 1) → ℤ) : ℤ := ∑ i, x i * y i

/-- The squared covolume `pairA x * pairA y - pairC x y ^ 2` of `ℤx ⊕ ℤy`. -/
def pairW (x y : Fin (n + 1) → ℤ) : ℤ := pairA x * pairA y - pairC x y ^ 2

/-- `pairA x • y - pairC x y • x`: the component of `y` orthogonal to `x`, scaled by `pairA x`. -/
def pairU (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ := pairA x • y - pairC x y • x

/-- `pairB x • y ...`: the component of `x` orthogonal to `y`, scaled by `pairA y`. -/
def pairV (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ := pairA y • x - pairC x y • y

end Work.HP.Vero
