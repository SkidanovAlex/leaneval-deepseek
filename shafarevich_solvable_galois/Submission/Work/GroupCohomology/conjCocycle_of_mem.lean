import Mathlib
import Submission.Work.GroupCohomology.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Pointwise computation of the conjugated cocycle: for `n m : N` and a cocycle `f : Z¹(N, A)`,
conjugation by `n` coincides with `f` shifted by the coboundary `d⁰ (f n)`:
`conjCocycle n f m = m • f n - f n + f m`. -/
theorem conjCocycle_apply_eq_d0_add {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] (n m : N) (f : Z1 N A) :
    (conjCocycle (N := N) (n : G) f : N → A) m
      = m • (f : N → A) n - (f : N → A) n + (f : N → A) m := by
  rw [conjCocycle_apply]
  have hinv : (conjAutN N (n : G))⁻¹ m = (n : N)⁻¹ * m * n := by
    apply Subtype.coe_injective
    show ((conjAutN N (n : G))⁻¹ m : G) = (((n : N)⁻¹ * m * n : N) : G)
    rw [conjAutN_symm_apply]; simp
  rw [hinv]
  have h1 : (f : N → A) ((n : N)⁻¹ * m * n)
      = ((n : N)⁻¹ * m) • (f : N → A) n + (f : N → A) ((n : N)⁻¹ * m) := by
    rw [f.2]
  rw [h1, smul_add]
  have h2 : (f : N → A) ((n : N)⁻¹ * m)
      = (n : N)⁻¹ • (f : N → A) m + (f : N → A) (n : N)⁻¹ := f.2 (n : N)⁻¹ m
  rw [h2, smul_add]
  have h3 : (n : G) • (f : N → A) (n : N)⁻¹ = -(f : N → A) n := by
    rw [← subgroup_smul_coe]
    exact Z1.map_inv N A f.2 n
  rw [h3]
  simp only [subgroup_smul_coe]
  rw [← mul_smul, ← mul_smul]
  have e1 : (↑n : G) * ↑((n : N)⁻¹ * m) = (↑m : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have e2 : (↑n : G) * ↑(n : N)⁻¹ = 1 := by
    rw [Subgroup.coe_inv, mul_inv_cancel]
  rw [e1, e2, one_smul]
  abel

theorem conjCocycle_of_mem {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] (n : N)
    (f : Work.GroupCohomology.Z1 N A) :
    ((Work.GroupCohomology.conjCocycle (N := N) n f -
      f : Work.GroupCohomology.Z1 N A) : N → A) ∈ Work.GroupCohomology.B1 N A := by
  rw [mem_B1_iff]
  refine ⟨(f : N → A) n, ?_⟩
  funext m
  rw [d0_apply, AddSubgroup.coe_sub, Pi.sub_apply, conjCocycle_apply_eq_d0_add]
  abel

end Work.GroupCohomology
