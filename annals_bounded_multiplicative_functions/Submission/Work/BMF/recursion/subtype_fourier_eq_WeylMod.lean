import Mathlib
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

open scoped BigOperators

/-- The Weyl sum restricted to a residue class, summed over the subtype of integers `≤ Q`
with `x ≡ y (mod p)`, agrees with `WeylMod`.  This is just bookkeeping: the left-hand sum
ranges over the subtype `Finset.Icc 1 Q` with the residue condition imposed, whereas `WeylMod`
ranges over the filtered finset of naturals; both equal the sum of
`if x % p = y % p then e(θ·mom1 k x) else 0` over `x ∈ [1,Q]`. -/
theorem subtype_fourier_eq_WeylMod (p k Q y : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    (∑ b ∈ (Finset.univ : Finset (Finset.Icc 1 Q)).filter (fun b => b.1 % p = y % p),
        UnitAddTorus.mFourier (mom1 k b.1) θ) = WeylMod p k Q y θ := by
  rw [WeylMod_apply]
  have hL : (∑ b ∈ (Finset.univ : Finset (Finset.Icc 1 Q)).filter (fun b => b.1 % p = y % p),
        UnitAddTorus.mFourier (mom1 k b.1) θ)
      = ∑ b : Finset.Icc 1 Q,
          if b.1 % p = y % p then UnitAddTorus.mFourier (mom1 k b.1) θ else 0 := by
    rw [Finset.sum_filter]
  have hR : (∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p),
        UnitAddTorus.mFourier (mom1 k x) θ)
      = ∑ b : Finset.Icc 1 Q,
          if b.1 % p = y % p then UnitAddTorus.mFourier (mom1 k b.1) θ else 0 := by
    rw [Finset.sum_filter]
    exact Finset.sum_subtype (Finset.Icc 1 Q) (fun x => Iff.rfl)
      (fun x => if x % p = y % p then UnitAddTorus.mFourier (mom1 k x) θ else 0)
  rw [hL, hR]

end Work.BMF.recursion
