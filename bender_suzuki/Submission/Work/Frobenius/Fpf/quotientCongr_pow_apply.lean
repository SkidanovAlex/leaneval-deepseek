import Mathlib
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Frobenius.Fpf

/-- The automorphism of `K ⧸ N` induced by an `N`-invariant `α : MulAut K` sends
`mk' N y` to `mk' N (α y)`. -/
theorem quotientCongr_mk'_apply {K : Type*} [Group K] {N : Subgroup K} [N.Normal]
    {α : MulAut K} (hN : Work.NPC.Fpf.IsInv α N) (y : K) :
    (QuotientGroup.congr N N α (by simpa using hN.map_eq)) (QuotientGroup.mk' N y)
      = QuotientGroup.mk' N (α y) :=
  QuotientGroup.congr_mk' N N α (by simpa using hN.map_eq) y

/-- Powers of the induced automorphism of `K ⧸ N` act as the corresponding powers of `α`:
`(α ⧸ N)^i (mk' N x) = mk' N (α^i x)`. -/
theorem quotientCongr_pow_apply {K : Type*} [Group K] {N : Subgroup K} [N.Normal] {α : MulAut K} (hN : Work.NPC.Fpf.IsInv α N) (i : ℕ) (x : K) : ((QuotientGroup.congr N N α (by simpa using hN.map_eq)) ^ i) (QuotientGroup.mk' N x) = QuotientGroup.mk' N ((α ^ i) x) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    rw [show (QuotientGroup.congr N N α (by simpa using hN.map_eq) *
        QuotientGroup.congr N N α (by simpa using hN.map_eq) ^ i) (QuotientGroup.mk' N x)
        = (QuotientGroup.congr N N α (by simpa using hN.map_eq))
            ((QuotientGroup.congr N N α (by simpa using hN.map_eq) ^ i)
              (QuotientGroup.mk' N x))
        from by simp]
    rw [ih, quotientCongr_mk'_apply hN]
    rw [pow_succ', MulAut.mul_apply]

end Work.Frobenius.Fpf
