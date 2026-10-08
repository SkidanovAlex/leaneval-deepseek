import Mathlib
import Submission.Work.ThmF.ChV3.Prove.pow_swap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- Rewrites `u ^ b * v ^ d` in terms of `v ^ d * u ^ b`, paying the commutator
`c ^ (d * b)`; the reverse of `pow_swap`. -/
private lemma u_pow_v_pow_swap {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) (hcv : Commute c v)
    (b d : ℤ) :
    u ^ b * v ^ d = c ^ (d * b) * (v ^ d * u ^ b) := by
  rw [pow_swap u v c huv hcu hcv d b, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul]

lemma mono_inv {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) (hcv : Commute c v)
    (a b d : ℤ) :
    (c^a * u^b * v^d)⁻¹ = c^(-a - d*b) * u^(-b) * v^(-d) := by
  have hre : c ^ a * u ^ b * v ^ d = c ^ a * (u ^ b * v ^ d) := by rw [mul_assoc]
  rw [hre, u_pow_v_pow_swap u v c huv hcu hcv b d, ← mul_assoc, ← zpow_add]
  rw [mul_inv_rev, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← zpow_neg]
  have hE : Commute (u ^ (-b) * v ^ (-d)) (c ^ (-(a + d * b))) :=
    (((hcu.zpow_right (-b)).zpow_left (-(a + d * b))).mul_right
      ((hcv.zpow_right (-d)).zpow_left (-(a + d * b)))).symm
  rw [hE.eq, mul_assoc, show -(a + d * b) = -a - d * b by ring]

end Work.ThmF.ChV3.Prove
