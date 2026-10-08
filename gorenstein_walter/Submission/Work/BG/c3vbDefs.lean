import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.HatInjDefs
import Submission.Work.GLUE.Defs

/-!
# Area BG: the conjugation actions of `t₁`, `t₂`, `t₁t₂` on `U = O(H)`

For `D : BGData G`, `C : Sec2Ctx G` compatible with `D`, the group `U = C.P.U` is the odd
core of `H = C_G(t)`, hence normal in `H`; every element of `H` therefore acts on `U` by
conjugation.  This module provides

* `Work.BG.conj_mem_U_of_mem_H` — conjugation by an element of `H` preserves `U`;
* `Work.BG.conjAutU D C hC x` — conjugation by `x ∈ H` as a `MulEquiv` of `↥C.P.U`;
* `Work.BG.sigmaU_eq_conjAutU`, `Work.BG.tauU`, `Work.BG.yU` — the three actions used in
  Theorem C: by `s = t₁`, by `t₂`, and by `y = t₁t₂`;
* `Work.BG.tauU_eq` (`τ = υ * σ`, from `y t₁ = t₂`) and `Work.BG.yU_mul_self` (`υ² = 1`,
  from `y²` centralizing `U`, the §3 hypothesis `Sec3Hyp`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by an element of `H = C_G(t)` preserves the odd core `U = O(H)`: the odd core
of a group is normal in it. -/
theorem conj_mem_U_of_mem_H (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C)
    {x : G} (hx : x ∈ C.P.H) {u : G} (hu : u ∈ C.P.U) : x * u * x⁻¹ ∈ C.P.U := by
  rw [hC.U_eq] at hu ⊢
  rw [hC.H_eq] at hx
  obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
  have hconj : (⟨x, hx⟩ : ↥D.H) * z * (⟨x, hx⟩ : ↥D.H)⁻¹ ∈ oddCore ↥D.H :=
    (inferInstance : (oddCore ↥D.H).Normal).conj_mem z hz ⟨x, hx⟩
  refine Subgroup.mem_map.mpr ⟨_, hconj, ?_⟩
  exact congrArg (fun y : G => x * y * x⁻¹) hzu

/-- `U ≤ H`. -/
theorem U_le_H_ctx (C : Sec2Ctx G) : C.P.U ≤ C.P.H :=
  le_trans C.P.U_le_H0 C.P.H0_le_H

/-- `U`, viewed as a normal subgroup of `H`. -/
theorem normal_subgroupOf_H (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) :
    (C.P.U.subgroupOf C.P.H).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (U_le_H_ctx C)).mpr ?_
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  exact conj_mem_U_of_mem_H D C hC hx hy

/-- Conjugation by `x ∈ H` as an automorphism of `U`, transported from the conjugation action
on `U.subgroupOf H`. -/
noncomputable def conjAutU (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) (x : ↥C.P.H) :
    ↥C.P.U ≃* ↥C.P.U := by
  letI := normal_subgroupOf_H D C hC
  exact (Subgroup.subgroupOfEquivOfLe (U_le_H_ctx C)).symm.trans
    ((ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := C.P.U.subgroupOf C.P.H) x).trans
      (Subgroup.subgroupOfEquivOfLe (U_le_H_ctx C)))

@[simp] theorem conjAutU_apply_coe (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C)
    (x : ↥C.P.H) (u : ↥C.P.U) :
    ((conjAutU D C hC x u : ↥C.P.U) : G) = (x : G) * (u : G) * (x : G)⁻¹ := by
  letI := normal_subgroupOf_H D C hC
  have h1 : ((conjAutU D C hC x u : ↥C.P.U) : G)
      = (((ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := C.P.U.subgroupOf C.P.H) x
          ((Subgroup.subgroupOfEquivOfLe (U_le_H_ctx C)).symm u)) : ↥(C.P.U.subgroupOf C.P.H)) : ↥C.P.H) :=
    rfl
  rw [h1, ClassFunction.conjByMulEquiv_apply]
  rfl

/-- `sigmaU C` is conjugation by `s = t₁`. -/
theorem sigmaU_eq_conjAutU (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) :
    sigmaU C = conjAutU D C hC C.s := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [sigmaU_apply_coe, conjAutU_apply_coe]

/-- `t₂`, as an element of `H`. -/
noncomputable def t2H (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) : ↥C.P.H :=
  ⟨D.t2, by rw [hC.H_eq]; exact S_le_H D D.t2_mem⟩

/-- `y = t₁t₂`, as an element of `H`. -/
noncomputable def yH (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) : ↥C.P.H :=
  ⟨D.t1 * D.t2, by
    rw [hC.H_eq]
    exact D.H.mul_mem (S_le_H D D.t1_mem) (S_le_H D D.t2_mem)⟩

/-- Conjugation by `t₂` as an automorphism of `U`. -/
noncomputable def tauU (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) :
    ↥C.P.U ≃* ↥C.P.U :=
  conjAutU D C hC (t2H D C hC)

/-- Conjugation by `y = t₁t₂` as an automorphism of `U`. -/
noncomputable def yU (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) :
    ↥C.P.U ≃* ↥C.P.U :=
  conjAutU D C hC (yH D C hC)

@[simp] theorem tauU_apply_coe (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C)
    (u : ↥C.P.U) :
    ((tauU D C hC u : ↥C.P.U) : G) = D.t2 * (u : G) * D.t2⁻¹ := by
  rw [tauU, conjAutU_apply_coe]
  rfl

@[simp] theorem yU_apply_coe (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C)
    (u : ↥C.P.U) :
    ((yU D C hC u : ↥C.P.U) : G) = (D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹ := by
  rw [yU, conjAutU_apply_coe]
  rfl

/-- `t₁ · t₁ = 1` in the BG data. -/
theorem t1_mul_self (D : BGData G) : D.t1 * D.t1 = 1 := by
  have h2 : D.t1 ^ 2 = 1 := by
    rw [← D.t1_order]
    exact pow_orderOf_eq_one D.t1
  simpa [pow_two] using h2

/-- `t₂ = t₁ · (t₁t₂)`: the two non-central involutions of `S ∖ S₀` differ by the generator
`t₁t₂` of `S₀`. -/
theorem t2_eq_t1_mul_y (D : BGData G) : D.t2 = D.t1 * (D.t1 * D.t2) := by
  rw [← mul_assoc, t1_mul_self D, one_mul]

/-- `τ = σ * υ`: conjugation by `t₂ = t₁·(t₁t₂)` is conjugation by `t₁t₂` followed by
conjugation by `t₁`. -/
theorem tauU_eq (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) :
    tauU D C hC = sigmaU C * yU D C hC := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (tauU D C hC u : G) = (sigmaU C (yU D C hC u) : G)
  rw [tauU_apply_coe, sigmaU_apply_coe, hC.s_eq, yU_apply_coe]
  calc D.t2 * (u : G) * D.t2⁻¹
      = (D.t1 * (D.t1 * D.t2)) * (u : G) * (D.t1 * (D.t1 * D.t2))⁻¹ := by
        conv_lhs => rw [t2_eq_t1_mul_y D]
    _ = D.t1 * ((D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹) * D.t1⁻¹ := by group

/-- `υ² = 1`: `y² = (t₁t₂)²` centralizes `U` (the §3 hypothesis). -/
theorem yU_mul_self (D : BGData G) (C : Sec2Ctx G) (hC : Compat D C) (hSec3 : Sec3Hyp D) :
    yU D C hC * yU D C hC = 1 := by
  have hy : D.t1 * D.t2 ∈ D.S0 := by rw [D.gen]; exact Subgroup.mem_zpowers _
  refine MulEquiv.ext fun u => Subtype.ext ?_
  show (yU D C hC (yU D C hC u) : G) = (u : G)
  have hcent : ((D.t1 * D.t2) * (D.t1 * D.t2)) * (u : G)
      = (u : G) * ((D.t1 * D.t2) * (D.t1 * D.t2)) := by
    simpa [pow_two] using hSec3 (D.t1 * D.t2) hy (u : G) (by rw [← hC.U_eq]; exact u.2)
  rw [yU_apply_coe, yU_apply_coe]
  calc (D.t1 * D.t2) * ((D.t1 * D.t2) * (u : G) * (D.t1 * D.t2)⁻¹) * (D.t1 * D.t2)⁻¹
      = ((D.t1 * D.t2) * (D.t1 * D.t2)) * (u : G) * ((D.t1 * D.t2) * (D.t1 * D.t2))⁻¹ := by
        group
    _ = (u : G) := by rw [hcent]; group

end Work.BG
