/-
  Work.WilE2 — area E2.  The Khovanskii bound with the compactness step.

  The elimination of one chain function proceeds in two moves:

  * *Sphere step.*  Add a variable `x₀` and the equation `x₀² + ‖x‖² + ψ_{s+1}(x)² − R² = 0`.
    The augmented system has `n+1` equations in `n+1` unknowns, still `r+1` chain functions, and
    total degree `D + 2`; the lift of the augmented system is *proper*.  Every non-degenerate
    zero of the old system gives two non-degenerate zeros of the augmented system.
  * *Rolle step* (proper case).  For a system with a proper lifted map, Khovanskii–Rolle replaces
    it by a system with `n+1` equations, chain length `r` and total degree `≤ 2D+n+1`.

  So the bound satisfies `KhovB (r+1) n D = KhovB r (n+2) (2*D + n + 6)`, and after `r` steps
  one is left with Bézout `D^n`.  `KhovB r n D` is compared with the polynomial `khoPoly F` of
  `Bound.lean` in `KhovB_le_khoPoly`.
-/
import Submission.Work.WilE2.Bound

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.WilE2

/-- The Khovanskii bound with the compactness (sphere) step included: `KhovB r n D` bounds the
number of non-degenerate zeros of a system of `n` EA polynomials in `n` variables with a chain
of `r` functions and total degree `D`. -/
def KhovB : ℕ → ℕ → ℕ → ℕ
  | 0, n, D => D ^ n
  | (r + 1), n, D => KhovB r (n + 2) (2 * D + n + 6)

end Work.WilE2
