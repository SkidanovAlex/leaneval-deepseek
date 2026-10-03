/-
Copyright: subproject `ORLocInd` -- the Cohen--Lyndon basis theorem (node N4).

# Karrass--Solitar: descent of the Cohen--Lyndon property along a malnormal subgroup

The construction of the Cohen--Lyndon basis theorem by induction on the length of the relator uses,
in the case where every letter of the relator has nonzero exponent sum ("Case 2"), Karrass--Solitar's
downward transfer: if `K ≤ G`, `r ∈ K` and the cyclic subgroup `⟨r⟩` is malnormal relative to `K`
(any `G`-conjugate of a nonzero power of `r` lying in `K` has its conjugating element in `K`), then
the Cohen--Lyndon property for `r` in `G` descends to `r` in `K`.

That transfer is proved in `Submission/Work/ORLocInd/CohenLyndon/ks_descent_malnormal.lean` by the
Bass--Serre/Kurosh argument (Karrass--Solitar 1972, Corollary of Theorem 1).  This file only
re-exports it under the name `CLDescent`, so that the induction of
`freeGroupCohenLyndon.lean` depends on exactly one bridge for the descent.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.ORLocInd.CohenLyndon.ks_descent_malnormal

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **Karrass--Solitar descent of the Cohen--Lyndon property.**  Let `K ≤ G`, `r ∈ K`, `r ≠ 1`.
If `r` has the Cohen--Lyndon property in `G`, and if `⟨r⟩` is malnormal relative to `K` in the
sense that `(x r x⁻¹)^j ∈ K` for some `j ≠ 0` forces `x ∈ K`, then `r` has the Cohen--Lyndon
property in `K`. -/
theorem CLDescent {G : Type u} [Group G] {K : Subgroup G} {r : K} (hr : r ≠ 1)
    (h : Work.CohenLyndon.CohenLyndonNC ((r : K) : G))
    (hmal : ∀ x : G, (∃ j : ℤ, j ≠ 0 ∧ (x * (r : G) * x⁻¹) ^ j ∈ K) → x ∈ K) :
    Work.CohenLyndon.CohenLyndonNC r :=
  ks_descent_malnormal hr h hmal

end Work.ORLocInd.CohenLyndon
