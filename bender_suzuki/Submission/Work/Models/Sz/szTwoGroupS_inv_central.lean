import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Abstract.ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs

namespace Work.Models.Sz

open Submission.Sz

/-- The root elements `u(0,b)` of the Suzuki 2-group are central in the Suzuki 2-group: the
multiplication law `u(a,b)·u(c,d) = u(a+c, b+d+a·c^(2^(n+1)))` collapses to `u(c, b+d)` on both
sides when `a = 0`. -/
lemma szUg_zero_mul_comm (n : ℕ) (b c d : SzField n) :
    szUg n 0 b * szUg n c d = szUg n c d * szUg n 0 b := by
  have h0k : (0 : SzField n) ^ (2 ^ (n + 1)) = 0 := zero_pow (by positivity)
  rw [szUg_mul, szUg_mul, h0k, mul_zero, add_zero, zero_mul, add_zero, zero_add]
  simp [add_comm]

theorem szTwoGroupS_inv_central (n : ℕ) :
    ∀ u ∈ Submission.Sz.szTwoGroupS n, u * u = 1 →
      ∀ v ∈ Submission.Sz.szTwoGroupS n, u * v = v * u := by
  intro u hu huu v hv
  -- `szTwoGroupS n` is the Suzuki 2-group viewed inside `SzModel n`; transport membership.
  have hu' : (u : GL (Fin 4) (SzField n)) ∈ szTwoGroup n := by
    have h := hu
    rw [szTwoGroupS] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hv' : (v : GL (Fin 4) (SzField n)) ∈ szTwoGroup n := by
    have h := hv
    rw [szTwoGroupS] at h
    exact Subgroup.mem_subgroupOf.mp h
  -- Write the two elements as root elements `u(a,b)`, `u(c,d)`.
  obtain ⟨a, b, hab⟩ := hu'
  obtain ⟨c, d, hcd⟩ := hv'
  -- `u · u = 1` upgrades to `u(a,b)² = 1`, forcing `a = 0`.
  have h2' : (u : GL (Fin 4) (SzField n)) ^ 2 = 1 := by
    have := congrArg Subtype.val huu
    simpa [pow_two] using this
  have h2 : (szUg n a b) ^ 2 = 1 := by rw [← hab]; exact h2'
  have ha : a = 0 := (szUg_sq_eq_one_iff n a b).mp h2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hab, hcd, ha]
  exact szUg_zero_mul_comm n b c d

end Work.Models.Sz
