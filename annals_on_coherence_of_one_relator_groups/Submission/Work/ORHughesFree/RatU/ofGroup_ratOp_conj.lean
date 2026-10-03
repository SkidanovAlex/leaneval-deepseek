import Mathlib
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.RTerm

namespace Work.ORHughesFree.RatU

/-- Conjugation by the image in `Rat(U)` of a group element commutes with the rational operation
`⋄`: this is the axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` of a rational `U`-semiring evaluated at the pair
`u = t ^ k`, `v = t ^ (-k)`, together with the identification of the two `U`-actions with
multiplication by `ofGroup`. -/
theorem ofGroup_ratOp_conj {Γ : Type} [Group Γ] (t : Γ) (k : ℤ) (x : RatU Γ) :
    RatU.ofGroup (t ^ k) * RatU.ratOp x * RatU.ofGroup (t ^ (-k))
      = RatU.ratOp (RatU.ofGroup (t ^ k) * x * RatU.ofGroup (t ^ (-k))) := by
  -- the rational axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` at `u = t^k`, `v = t^(-k)`
  have h := (RatU.rational (U := Γ)).rat_smul (t ^ k) (t ^ (-k)) x
  -- identify the argument of `⋄` on the left of `h` with the product in the goal
  have hk1 : RatU.ofGroup (t ^ k) * x * RatU.ofGroup (t ^ (-k))
      = RatU.smul (t ^ k) (RatU.smulRight x (t ^ (-k))) := by
    rw [RatU.smul_eq_ofGroup_mul, RatU.smulRight_eq_mul_ofGroup, mul_assoc]
  -- identify the value of `⋄` on the right of `h` with the conjugated product
  have hk2 : RatU.ofGroup (t ^ k) * RatU.ratOp x * RatU.ofGroup (t ^ (-k))
      = RatU.smulRight (RatU.smul (t ^ (-k))⁻¹ (RatU.ratOp x)) (t ^ k)⁻¹ := by
    rw [RatU.smulRight_eq_mul_ofGroup, RatU.smul_eq_ofGroup_mul]
    rw [← zpow_neg, neg_neg, ← zpow_neg, mul_assoc]
  rw [hk2, hk1]
  exact h.symm

end Work.ORHughesFree.RatU
