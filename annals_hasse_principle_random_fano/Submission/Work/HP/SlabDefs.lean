import Mathlib
import Submission.Work.HP.ArchDefs

/-!
# Auxiliary definitions for the slab volume bound `Work.HP.slab_vol`

* `gradKer d n x j m` is the derivative of the monomial `ν(x)_m` with respect to `x_j`, i.e.
  the coefficient of `a m` in `gradF d n a x j`.
* `spm d n hd i : Fin (n+1) → Mon d n` enumerates the `n+1` "special" monomials at `i`:
  position `0` is `x_i^d` (i.e. `smon i i`) and position `k+1` is `x_i^{d-1} x_{i.succAbove k}`.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators

namespace Work.HP

/-- The derivative of the monomial `ν(x)_m` in the direction `j`. -/
def gradKer (d n : ℕ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (m : Mon d n) : ℝ :=
  ((m.1 j : ℕ) : ℝ) * x j ^ ((m.1 j : ℕ) - 1) *
    ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ))

/-- `gradF` is the sum of `a m` times `gradKer` over all monomials. -/
theorem gradF_eq_sum_gradKer (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    gradF d n a x j = ∑ m, a m * gradKer d n x j m := by
  simp only [gradF, gradKer]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The `n+1` special monomials at `i`, in "peeling order". -/
def spm (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) : Fin (n + 1) → Mon d n :=
  Fin.cases (smon d n hd i i) (fun k => smon d n hd i (i.succAbove k))

@[simp] theorem spm_zero (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    spm d n hd i 0 = smon d n hd i i := rfl

@[simp] theorem spm_succ (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (k : Fin n) :
    spm d n hd i k.succ = smon d n hd i (i.succAbove k) := rfl

end Work.HP
