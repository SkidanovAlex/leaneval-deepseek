import Mathlib
import Submission.Work.LandLeaves.ccBet_angDouble_typeSet_fresh
import Submission.Work.LandLeaves.SigLeaves.finiteOfCcBetPeriodic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A `σ`-invariant set of angles containing a periodic point is finite

Requested `_v2` entry point for the finiteness lemma of the type of a repelling periodic point.

For `d ≥ 2`, let `σ x = Int.fract (d * x)`.  Let `K ⊆ [0,1)` carry `σ` into itself, with `σ` a
`ccBet`-order-preserving bijection of `K` onto itself (`hmap`, `hsurj`, `hinj`, `hord`).  If `K`
contains a point `p` which is periodic of period `q ≥ 1` under `σ`, then `K` is finite.

The mathematics (see `Submission/Work/LandLeaves/NOTES_finite_type_proof_sketch.md` and
`Submission/Work/LandLeaves/NOTES_FALSE_orderPreserving_finiteness.md`): order preservation alone
does *not* give finiteness (there are Sturmian counterexamples), but adding a *single* periodic
point does.  Put `τ = σ^[q]`, so `τ p = p`.  Cutting the circle at `p` via `ρ z = fract (z - p)`
turns the cyclic order `ccBet` into a linear order in which `ρ` is injective on `K`; `τ`
preserves `ccBet` and hence this linear order, so the `τ`-orbit of any `a ∈ K` is monotone.  Its
positive gaps `λ n` then telescope (`Σ_{n<N} λ n ≤ 1`) while satisfying
`λ (n+1) = fract (d^q * λ n)`, which contradicts `Work.LandLeaves.fract_orbit_sum_gt_one`.  Hence
every point of `K` is `σ`-periodic, and then `σ^[q]` fixes all of `K`
(`Work.LandLeaves.iterate_fixes_all_of_ccBet`), so `K` lies in the fixed-point set of
`x ↦ fract (d^q * x)`, which is finite (`Work.LandLeaves.finite_of_fixed_fract`).

The argument is carried out in full in `Submission/Work/LandLeaves/SigLeaves/finiteOfCcBetPeriodic.lean`
(in the namespace `Work.LandLeaves.SigLeaves`, so that it can coexist with the angle--side
vocabulary of `ccBet_v2_defs`, whose `fract_sub_fract_of_le` clashes with the identically named
helper of the original `finite_of_ccBet_periodic_point.lean`); the present file exposes it under
the requested name.
-/

namespace Work.LandLeaves

theorem finite_of_ccBet_periodic_point_v2 {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hmap : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hsurj : ∀ y ∈ K, ∃ x ∈ K, Int.fract ((d : ℝ) * x) = y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d:ℝ)*x) = Int.fract ((d:ℝ)*y) → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract ((d:ℝ)*a)) (Int.fract ((d:ℝ)*b))
        (Int.fract ((d:ℝ)*x)))
    {q : ℕ} (hq : 0 < q) {p : ℝ} (hp : p ∈ K)
    (hper : (fun x : ℝ => Int.fract ((d : ℝ) * x))^[q] p = p) : K.Finite :=
  Work.LandLeaves.SigLeaves.finite_of_ccBet_periodic_point hd hsub hmap hsurj hinj hord hq hp hper

end Work.LandLeaves
