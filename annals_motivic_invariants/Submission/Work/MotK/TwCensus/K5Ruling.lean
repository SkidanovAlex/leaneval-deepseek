import Mathlib
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.MotK.TwCensus.Amat_mulVec

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# K5, assembled: the ruling lines of the T-twisted quadro map

The two proved ingredients of K5 are

* `Work.MotK.TGen.KleinTwFibre_eq_ker` (`Submission/Work/MotK/TGen/KleinTwFibre_eq_ker.lean`):
  the fibre of the twisted quadro map over `[c']` is the kernel of the ruling matrix `kleinTwM`;
* `Work.MotK.TwCensus.Amat_mulVec`: the same system, written linearly in `y`, is `Amat a b h c'`.

This module assembles them into the statement K5 needs: **the fibre of `kleinTwP` over `[c']` is the
kernel of the linear system `Amat a b h c'`** — i.e. a linear space, and (on the ruling base curve)
the ruling *line* of the divisor `{sT = 0}`, spanned by the explicit `A(c'), B(c')` of the design.
This is the interface against which the parametrisation (K5(b)) and the "lands on the surface"
identity (K5(c)) are stated.

(The module lives below `STClass` in the import order because the two lemmas it combines are stated
in `STClass`'s vocabulary.)
-/

namespace Work.MotK.TwCensus

open Matrix

variable {K : Type} [Field K]

/-- **K5: the ruling lines.**  For `c' ≠ 0`, the fibre of the T-twisted quadro map over `[c']` is
exactly the kernel of the linear system `Amat a b h c'`:

`Amat a b h c' *ᵥ y = 0  ↔  kleinTwP a b h y ∝ c'`. -/
theorem ruling_fibre_eq_ker (a b h : K) (hh : h ≠ 0) (y c' : Fin 5 → K)
    (hy : Work.MotK.kleinTwP a b h y ≠ 0) (hc' : c' ≠ 0) :
    Matrix.mulVec (Amat a b h c') y = 0 ↔
      ∃ l : K, l ≠ 0 ∧ ∀ k : Fin 5, Work.MotK.kleinTwP a b h y k = l * c' k := by
  rw [Amat_mulVec]
  exact Work.MotK.TGen.KleinTwFibre_eq_ker a b h hh y c' hy hc'

/-- **K5, the two points of the ruling line span it.**  If `y` and `y'` are both in the ruling
fibre over `[c']` (with `c' ≠ 0` and the fibre non-degenerate), then so is every linear combination
— the ruling fibre really is a linear subspace of `K⁵`, i.e. a line in `ℙ⁴`, as the design's
`ℓ'_{c'} = {y : M(y)·c' = 0}` requires. -/
theorem ruling_fibre_linear (a b h : K) (hh : h ≠ 0) (y y' c' : Fin 5 → K)
    (hy : Matrix.mulVec (Amat a b h c') y = 0) (hy' : Matrix.mulVec (Amat a b h c') y' = 0)
    (c d : K) :
    Matrix.mulVec (Amat a b h c') (fun i => c * y i + d * y' i) = 0 := by
  funext i
  have h1 : (∑ x, (Amat a b h c') i x * y x) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hy i
  have h2 : (∑ x, (Amat a b h c') i x * y' x) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hy' i
  show (∑ x, (Amat a b h c') i x * (c * y x + d * y' x)) = 0
  rw [show (∑ x, (Amat a b h c') i x * (c * y x + d * y' x))
      = c * (∑ x, (Amat a b h c') i x * y x)
        + d * (∑ x, (Amat a b h c') i x * y' x) by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring]
  rw [h1, h2, mul_zero, mul_zero, add_zero]

end Work.MotK.TwCensus
