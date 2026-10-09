import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin.RedLattice

theorem sum_smul_inv_smul_mul {G : Type*} [Group G] [Fintype G]
    {A : Type*} [AddCommMonoid A] [SMul G A]
    {B : Type*} [MulAction G B]
    (F : B → A) (g : G) (b : B) :
    (∑ k : G, k • F (k⁻¹ • (g • b))) = ∑ k : G, (g * k) • F (k⁻¹ • b) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun k => (g * k) • F (k⁻¹ • b))]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_smul, mul_inv_cancel_left]

end Work.SSGRoute.E7Fin.RedLattice
