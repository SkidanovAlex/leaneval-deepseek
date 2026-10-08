/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: maximal `ξ`-invariant abelian normal subgroups

Higman, *Suzuki 2-groups* (1963), §3–§5.  This file sets up the family of `ξ`-invariant abelian
normal subgroups of a Suzuki 2-group, proves that it has maximal elements, and records the two
elementary consequences of maximality that every later argument uses:

* every maximal `ξ`-invariant abelian normal subgroup contains `Ω₁(P)`;
* every maximal `ξ`-invariant abelian normal subgroup contains the centre `Z(P)`.

Both are proved by joining: if `B` is central and `A` abelian, then `A ⊔ B` is abelian, and
`A ⊔ B` is `ξ`-invariant and normal.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `ξ` maps `Ω₁(P)` to itself. -/
theorem map_xi_omega1 (h : IsSuzuki2Grp P) :
    (omega1 P).map (h.xi : MulAut P).toMonoidHom = omega1 P := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    rw [h.mem_omega1, ← map_pow, h.mem_omega1.mp hy, map_one]
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, h.mem_omega1, ← map_pow, h.mem_omega1.mp hx, map_one]

/-- The family of `ξ`-invariant abelian normal subgroups of a Suzuki 2-group. -/
def IsXiAbelNormal (h : IsSuzuki2Grp P) (A : Subgroup P) : Prop :=
  A.Normal ∧ A.map (h.xi : MulAut P).toMonoidHom = A ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x

theorem IsXiAbelNormal.normal {h : IsSuzuki2Grp P} {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    A.Normal := hA.1

theorem IsXiAbelNormal.map_eq {h : IsSuzuki2Grp P} {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    A.map (h.xi : MulAut P).toMonoidHom = A := hA.2.1

theorem IsXiAbelNormal.abelian {h : IsSuzuki2Grp P} {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.2.2

/-- `Ω₁(P)` is a `ξ`-invariant abelian normal subgroup. -/
theorem omega1_isXiAbelNormal (h : IsSuzuki2Grp P) : IsXiAbelNormal h (omega1 P) :=
  ⟨Subgroup.normal_of_le_center h.omega1_le_center, map_xi_omega1 h,
   fun _ hx _ hy => h.omega1_comm hx hy⟩

/-- The family of `ξ`-invariant abelian normal subgroups has a maximal element. -/
theorem exists_maximal_isXiAbelNormal (h : IsSuzuki2Grp P) :
    ∃ A : Subgroup P, IsXiAbelNormal h A ∧
      ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A := by
  classical
  have hfin : ({A : Subgroup P | IsXiAbelNormal h A} : Set (Subgroup P)).Finite :=
    Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨A, hA⟩ := hfin.exists_maximal ⟨omega1 P, omega1_isXiAbelNormal h⟩
  exact ⟨A, hA.1, fun B hB hAB => le_antisymm (hA.2 hB hAB) hAB⟩

/-- If `A` is abelian and `B` is central then `A ⊔ B` is abelian. -/
theorem sup_comm_of_le_center {A B : Subgroup P}
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hB : B ≤ Subgroup.center P) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  haveI : B.Normal := Subgroup.normal_of_le_center hB
  intro x hx y hy
  obtain ⟨a, haA, b, hbB, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := A) (t := B)).mp hx
  obtain ⟨a', ha'A, b', hb'B, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := A) (t := B)).mp hy
  have hb_c : ∀ g : P, g * b = b * g := Subgroup.mem_center_iff.mp (hB hbB)
  have hb'_c : ∀ g : P, g * b' = b' * g := Subgroup.mem_center_iff.mp (hB hb'B)
  calc (a * b) * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [hb_c a']
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hAb a haA a' ha'A, hb'_c b]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hb'_c a]
    _ = (a' * b') * (a * b) := by group

/-- A maximal `ξ`-invariant abelian normal subgroup contains `Ω₁(P)`. -/
theorem omega1_le_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    omega1 P ≤ A := by
  haveI : A.Normal := hA.1
  haveI : (omega1 P).Normal := Subgroup.normal_of_le_center h.omega1_le_center
  have hsup : IsXiAbelNormal h (A ⊔ omega1 P) := by
    refine ⟨Subgroup.sup_normal A (omega1 P), ?_,
      sup_comm_of_le_center hA.abelian h.omega1_le_center⟩
    rw [Subgroup.map_sup, hA.map_eq, map_xi_omega1 h]
  have hEq : A ⊔ omega1 P = A := hmax (A ⊔ omega1 P) hsup le_sup_left
  rw [← hEq]
  exact le_sup_right

/-- An automorphism maps the centre into itself. -/
theorem aut_mem_center (φ : MulAut P) {z : P} (hz : z ∈ Subgroup.center P) :
    φ z ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  calc g * φ z = φ (φ.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = φ (z * φ.symm g) := by rw [hz (φ.symm g)]
    _ = φ z * g := by rw [map_mul, MulEquiv.apply_symm_apply]

/-- A maximal `ξ`-invariant abelian normal subgroup contains the centre `Z(P)`. -/
theorem center_le_of_maximal (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    Subgroup.center P ≤ A := by
  haveI : A.Normal := hA.1
  have hZinv : (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom = Subgroup.center P := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨z, hz, rfl⟩
      exact aut_mem_center (h.xi : MulAut P) hz
    · intro x hx
      refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
      exact aut_mem_center (h.xi : MulAut P).symm hx
  have hsup : IsXiAbelNormal h (A ⊔ Subgroup.center P) := by
    refine ⟨Subgroup.sup_normal A (Subgroup.center P), ?_,
      sup_comm_of_le_center hA.abelian le_rfl⟩
    rw [Subgroup.map_sup, hA.map_eq, hZinv]
  have hEq : A ⊔ Subgroup.center P = A := hmax (A ⊔ Subgroup.center P) hsup le_sup_left
  rw [← hEq]
  exact le_sup_right

end Work.Higman
