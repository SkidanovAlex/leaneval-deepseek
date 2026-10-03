import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_mul
import Submission.Work.ORLyndon.CLDirect.clDelta_one

namespace Work.ORLyndon.CLDirect

/-- The telescoping formula `Δ (g^k) = (Σ_{i<k} π(g)^i) Δ g`. Sketch: induction on `k` using `pow_succ` and `clDelta_mul` at `g^k * g`; then `map_pow (MonoidAlgebra.of K _)`, `map_pow clPi`, `Finset.sum_range_succ`, `add_mul`; the `k = 0` case is `clDelta_one`. The left-factoring order `(Σ a^i) * Δ g` is the correct non-commutative one. -/
theorem clDelta_pow {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ)
    (g : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) (k : ℕ) :
    Work.ORLyndon.CLDirect.clDelta (K := K) D l (g ^ k) =
      (∑ i ∈ Finset.range k,
        (Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g)) ^ i) *
        Work.ORLyndon.CLDirect.clDelta (K := K) D l g := by
  induction k with
  | zero =>
    rw [pow_zero, clDelta_one]
    simp
  | succ k ih =>
    -- `Δ (g^(k+1)) = Δ (g^k * g) = Δ (g^k) + π(g^k) Δ g`, and `π(g^k) = π(g)^k`,
    -- so the right factor `Δ g` collects as `(Σ_{i<k} π(g)^i + π(g)^k) * Δ g`.
    rw [pow_succ, clDelta_mul, ih, Finset.sum_range_succ, add_mul,
      map_pow (MonoidAlgebra.of K _) g k, map_pow]

end Work.ORLyndon.CLDirect
