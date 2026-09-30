import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.mvPolynomial_catenary
import Submission.Work.BW.RB.height_sup_span_le_add_one
import Submission.Work.BW.RB.mvpoly_dim_formula

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

set_option linter.style.haveILetI false

/-- **Height of a minimal prime over `p + (P)`.**

Let `R = MR N = ℂ[X_{ij}]` be the polynomial ring in `2(N+1)` variables over `ℂ`, let `p` be a
prime ideal, `P ∉ p`, and `q` a minimal prime over `p ⊔ (P)`.  Then

  `ht q = ht p + 1`.

* `≤`: the catenary inequality for the polynomial ring `ℂ[σ]` gives
  `ht q ≤ ht p + ht (q ⧸ p)`, and `ht (q ⧸ p) ≤ 1` is Krull's principal ideal theorem relative to
  `p` (`Ideal.map_height_le_one_of_mem_minimalPrimes`).
* `≥`: `p < q` since `P ∈ q \ p`, and a strict inclusion of primes raises the height by at
  least one. -/
theorem height_minimalPrimes_sup_span_singleton {N : ℕ} (p : Ideal (MR N)) (hp : p.IsPrime)
    (P : MR N) (hP : P ∉ p) {q : Ideal (MR N)}
    (hq : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes) :
    q.height = p.height + 1 := by
  haveI := hp
  haveI := hq.isPrime
  -- `p ≤ q` and `P ∈ q`, but `P ∉ p`, so the inclusion `p < q` is strict.
  have hpq : p ≤ q := le_sup_left.trans hq.le
  have hPq : P ∈ q := hq.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self P))
  have hlt : p < q := lt_of_le_of_ne hpq (fun he => hP (he.symm ▸ hPq))
  refine le_antisymm ?_ (Ideal.height_add_one_le_of_lt_of_isPrime hlt)
  -- `ht q ≤ ht p + ht (q ⧸ p) ≤ ht p + 1`.
  calc q.height ≤ p.height + (q.map (Ideal.Quotient.mk p)).height :=
        mvPolynomial_catenary hpq
    _ ≤ p.height + 1 := add_le_add le_rfl (Ideal.map_height_le_one_of_mem_minimalPrimes hq)

end Work.BW.RB
