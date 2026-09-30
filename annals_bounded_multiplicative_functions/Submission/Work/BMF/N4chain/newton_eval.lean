import Mathlib
import Submission.Work.BMF.N4chain.linnik_newton_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

open Finset

/-- Sum over the antidiagonal `{(i, m - i) | i < m}` written as a sum over `range m`. -/
lemma sum_antidiagonal_filter_lt {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) (m : ℕ) :
    ∑ a ∈ (antidiagonal m).filter (fun a => a.1 < m), f a =
      ∑ i ∈ range m, f (i, m - i) := by
  rw [Finset.sum_filter]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  simp only [Nat.lt_irrefl, ↓reduceIte, add_zero]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [ite_eq_left (Finset.mem_range.mp hx)]

theorem newton_eval {p k : ℕ} (v : Fin k → ZMod p) (m : ℕ) :
    (m : ZMod p) * Work.BMF.N4chain.esymmEval v m =
      (-1) ^ (m + 1) * ∑ i ∈ Finset.range m,
        (-1) ^ i * Work.BMF.N4chain.esymmEval v i * Work.BMF.N4chain.psumEval v (m - i) := by
  have hkey : (m : ZMod p) * esymmEval v m =
      (-1) ^ (m + 1) *
        ∑ a ∈ (antidiagonal m).filter (fun a => a.1 < m),
          (-1) ^ a.1 * esymmEval v a.1 * psumEval v a.2 := by
    have h := congrArg (MvPolynomial.aeval v)
      (MvPolynomial.mul_esymm_eq_sum (Fin k) (ZMod p) m)
    simpa [esymmEval, psumEval, MvPolynomial.psum] using h
  rw [hkey, sum_antidiagonal_filter_lt]

end Work.BMF.N4chain
