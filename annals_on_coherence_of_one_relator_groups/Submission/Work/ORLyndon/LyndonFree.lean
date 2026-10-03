import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.lyndon_ker_delta_free
import Submission.Work.ORLyndon.lyndonDelta_range_eq_augIdeal

/-!
# The base case `r = 1`: the Lyndon complex for a free group

For the trivial relator `r = 1` the presented group `⟨X | 1⟩` is the free group `F(X)`, and the
Lyndon complex

`0 → K[G] → K[G]^X → K[G] → K → 0`

is exact: the Fox derivative vector of `1` vanishes (so `θ = 0`), the augmentation ideal of the free
group algebra is free on `{x - 1}` (`δ` is injective, `Work.ORLyndon.lyndon_ker_delta_free`), and
`range δ = I_{K[G]}`.

This is the base case of Lyndon's identity theorem: for `r = 1` no root `u ≠ 1` exists, so the
hypothesis structure `Work.ORLyndon.LyndonIdentity` (which asks for `ker θ = K[G](u-1)`) does not
apply; the exactness is stated separately here.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} {K : Type v}

/-- The Fox derivative vector of the trivial relator is zero. -/
@[simp] theorem relatorVec_one (K : Type v) [Field K] [DecidableEq X] :
    relatorVec K (1 : FreeGroup X) = 0 := by
  ext w
  rw [relatorVec_apply, foxD_one, map_zero, Finsupp.zero_apply]

/-- For the trivial relator the first map of the Lyndon complex vanishes. -/
@[simp] theorem lyndonTheta_eq_zero_one (K : Type v) [Field K] [DecidableEq X] :
    lyndonTheta K (1 : FreeGroup X) = 0 := by
  ext a
  rw [lyndonTheta_apply, relatorVec_one, smul_zero, LinearMap.zero_apply]

/-- **The Lyndon complex of the free group**: for `r = 1` the sequence
`0 → K[G] → K[G]^X → K[G] → K → 0` is exact. -/
theorem lyndon_free_exact (K : Type v) [Field K] [DecidableEq X] :
    LinearMap.range (lyndonTheta K (1 : FreeGroup X)) =
        LinearMap.ker (lyndonDelta K (1 : FreeGroup X)) ∧
      LinearMap.ker (lyndonTheta K (1 : FreeGroup X)) = ⊤ ∧
      LinearMap.range (lyndonDelta K (1 : FreeGroup X)) =
        augIdeal K (OneRelatorGroup (1 : FreeGroup X)) :=
  ⟨by rw [lyndonTheta_eq_zero_one, LinearMap.range_zero, lyndon_ker_delta_free],
   by rw [lyndonTheta_eq_zero_one, LinearMap.ker_zero],
   lyndonDelta_range_eq_augIdeal (K := K) (1 : FreeGroup X)⟩

end Work.ORLyndon
