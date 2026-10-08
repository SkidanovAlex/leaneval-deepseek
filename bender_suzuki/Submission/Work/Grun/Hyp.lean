/-
# The Hall transfer hypothesis (M. Hall, §14.4, Theorem 14.4.1)

This file records, as a single `def`, the hypothesis on the "choosable elements `z`" in P. Hall's
transfer theorem, in the form in which FT 1963, Lemma 17.2 supplies it:

for every `x ∉ H` there is `z ∈ P` with

* `z ∉ cosetKernel H P x` (`z` does not fix all cosets of `H` in `P x H`),
* `z ^ p ∈ cosetKernel H P x` (so `z` acts on those cosets with orbits of length `p`),
* `⁅u, z⁆ ∈ cosetKernel H P x` for all `u ∈ P` (so `z` acts centrally),
* `iterComm (p-1) u z = 1` for all `u ∈ P` (Hall's `e_p(u,z) = 1`).
-/
import Mathlib
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement

namespace Work.Grun

variable {G : Type*} [Group G]

/-- The hypothesis produced by FT §17 for P. Hall's transfer theorem: every double coset
`P x H ≠ H` carries an element `z ∈ P` acting as a "central `p`-cycle with `e_p(·,z) = 1`". -/
def HallHyp (p : ℕ) (P H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ H → ∃ z ∈ P,
    z ∉ cosetKernel H P x ∧ z ^ p ∈ cosetKernel H P x ∧
      (∀ u ∈ P, ⁅u, z⁆ ∈ cosetKernel H P x) ∧
      (∀ u ∈ P, iterComm (p - 1) u z = 1)

end Work.Grun
