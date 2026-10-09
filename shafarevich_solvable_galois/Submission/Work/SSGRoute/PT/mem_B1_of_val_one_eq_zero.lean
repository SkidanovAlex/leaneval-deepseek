import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.SSGRoute.PT

theorem mem_B1_of_val_one_eq_zero {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (f : Work.AbsoluteKummer.Z1 G (Work.SSGRoute.PT.Coind G U M))
    (hf : ∀ u : U, ((f : G → Work.SSGRoute.PT.Coind G U M) (u : G) : G → M) (1 : G) = 0) :
    (f : G → Work.SSGRoute.PT.Coind G U M) ∈
      Work.AbsoluteKummer.B1 G (Work.SSGRoute.PT.Coind G U M) := by
  rw [Work.AbsoluteKummer.mem_B1_iff]
  -- `f` is an additive crossed homomorphism `G → Coind G U M`
  have hcross : Work.GroupCohomology.IsCrossedHom G (Coind G U M)
      (f : G → Coind G U M) :=
    ((Work.AbsoluteKummer.mem_Z1_iff (f : G → Coind G U M)).mp f.2).1
  -- `f 1 = 0`
  have hone : (f : G → Coind G U M) 1 = 0 := by
    have h : (f : G → Coind G U M) 1
        = (f : G → Coind G U M) 1 + (f : G → Coind G U M) 1 := by
      simpa using hcross 1 1
    exact (add_left_cancel (a := (f : G → Coind G U M) 1) (by simpa using h)).symm
  -- the candidate coinduced element `a y = f (y⁻¹) 1`
  have hcoind : ∀ y : G, ∀ u : U,
      (fun y : G => ((f : G → Coind G U M) y⁻¹ : G → M) 1) (y * (u : G)) =
        u⁻¹ • (fun y : G => ((f : G → Coind G U M) y⁻¹ : G → M) 1) y := by
    intro y u
    have h := congrFun (congrArg (fun z : Coind G U M => (z : G → M))
      (hcross ((u : U) : G)⁻¹ y⁻¹)) (1 : G)
    simp only [AddSubgroup.coe_add, Pi.add_apply] at h
    rw [Coind.smul_apply, mul_one, inv_inv] at h
    have hcoe : (((f : G → Coind G U M) y⁻¹) : G → M) ((u : U) : G)
        = u⁻¹ • (((f : G → Coind G U M) y⁻¹) : G → M) 1 := by
      rw [← one_mul ((u : U) : G), Coind.coe_mul]
    rw [hcoe] at h
    have hz : ((((f : G → Coind G U M) (((u : U) : G)⁻¹)) : Coind G U M) : G → M) 1 = 0 := by
      simpa only [Subgroup.coe_inv] using hf u⁻¹
    rw [hz, add_zero] at h
    change ((f : G → Coind G U M) (y * (u : G))⁻¹ : G → M) 1
      = u⁻¹ • ((f : G → Coind G U M) y⁻¹ : G → M) 1
    rw [mul_inv_rev]
    exact h
  let a : Coind G U M :=
    ⟨fun y : G => ((f : G → Coind G U M) y⁻¹ : G → M) 1, hcoind⟩
  have ha : ∀ y : G, (a : G → M) y = ((f : G → Coind G U M) y⁻¹ : G → M) 1 :=
    fun y => rfl
  refine ⟨a, ?_⟩
  funext g
  apply Subtype.ext
  funext x
  simp only [Work.GroupCohomology.d0_apply, AddSubgroup.coe_sub, Pi.sub_apply,
    Coind.smul_apply, ha]
  -- now: `↑(f (g⁻¹ * x)⁻¹) 1 - ↑(f x⁻¹) 1 = ↑(f g) x`
  have h1 : ((f : G → Coind G U M) g : G → M) x
      = ((f : G → Coind G U M) (x⁻¹ * g) : G → M) 1
        + ((f : G → Coind G U M) x : G → M) x := by
    have h := hcross x (x⁻¹ * g)
    rw [show x * (x⁻¹ * g) = g from by group] at h
    have h' := congrFun (congrArg (fun z : Coind G U M => (z : G → M)) h) x
    simpa only [AddSubgroup.coe_add, Pi.add_apply, Coind.smul_apply, inv_mul_cancel] using h'
  have h2 : ((f : G → Coind G U M) x : G → M) x
      = -(((f : G → Coind G U M) x⁻¹ : G → M) 1) := by
    have h := hcross x⁻¹ x
    rw [inv_mul_cancel] at h
    rw [hone] at h
    have h' := congrFun (congrArg (fun z : Coind G U M => (z : G → M)) h) (1 : G)
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero, Pi.add_apply, Pi.zero_apply,
      Coind.smul_apply, mul_one, inv_inv] at h'
    exact eq_neg_of_add_eq_zero_left h'.symm
  rw [mul_inv_rev, inv_inv, h1, h2, sub_eq_add_neg]

end Work.SSGRoute.PT
