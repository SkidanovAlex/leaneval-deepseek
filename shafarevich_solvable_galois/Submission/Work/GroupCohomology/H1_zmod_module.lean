/-
Copyright (c) 2025. All rights reserved.

# `H¹` as a `𝔽_p`-vector space

Let `G` be a group and `A` a `ℤ[G]`-module whose underlying additive group is in addition a
`ZMod p`-module, compatibly with the `G`-action (`SMulCommClass G (ZMod p) A`).  Then the
group of `1`-cocycles `Z¹(G, A)` and the group of `1`-coboundaries `B¹(G, A)` are `ZMod p`-submodules
of the cochain group `C¹(G, A) = (G → A)` (with the pointwise `ZMod p`-module structure), and the
quotient `Z¹/B¹ = H¹(G, A)` inherits a `ZMod p`-module structure for which the identification
`Z¹/B¹ ≅ H¹` is `ZMod p`-linear.

This is packaged as the existence statement `H1_zmod_module`.
-/
import Mathlib
import Submission.Work.GroupCohomology.All
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

universe u v

namespace H1zmod

variable (p : ℕ) (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
  [DistribMulAction G A] [Module (ZMod p) A] [SMulCommClass G (ZMod p) A]

/-! ## `Z¹` and `B¹` are `ZMod p`-submodules of the cochains -/

theorem zmod_smul_mem_Z1 (a : ZMod p) {f : G → A} (hf : f ∈ Z1 G A) : a • f ∈ Z1 G A := by
  rw [mem_Z1_iff] at hf ⊢
  intro g h
  simp only [Pi.smul_apply]
  rw [hf g h, smul_add]
  congr 1
  exact (SMulCommClass.smul_comm g a (f h)).symm

theorem zmod_smul_mem_B1 (a : ZMod p) {f : G → A} (hf : f ∈ B1 G A) : a • f ∈ B1 G A := by
  obtain ⟨y, rfl⟩ := hf
  refine ⟨a • y, ?_⟩
  funext g
  simp only [d0_apply, Pi.smul_apply, smul_sub]
  congr 1
  rw [SMulCommClass.smul_comm]

/-- The `1`-cocycles as a `ZMod p`-submodule of the cochains `C¹(G, A) = (G → A)`. -/
noncomputable def Z1m : Submodule (ZMod p) (G → A) :=
  Submodule.mk (Z1 G A).toAddSubmonoid (fun a _ hx => zmod_smul_mem_Z1 p G A a hx)

/-- The `1`-coboundaries as a `ZMod p`-submodule of the cochains `C¹(G, A) = (G → A)`. -/
noncomputable def B1m : Submodule (ZMod p) (G → A) :=
  Submodule.mk (B1 G A).toAddSubmonoid (fun a _ hx => zmod_smul_mem_B1 p G A a hx)

theorem mem_Z1m (f : G → A) : f ∈ Z1m p G A ↔ f ∈ Z1 G A := Iff.rfl

theorem mem_B1m (f : G → A) : f ∈ B1m p G A ↔ f ∈ B1 G A := Iff.rfl

theorem B1m_le_Z1m : B1m p G A ≤ Z1m p G A := fun _ hf => B1_le_Z1 G A hf

/-! ## The identification of `Z1m ⧸ B1m` with `H¹` -/

/-- The additive equivalence `↥Z1m ≃+ ↥Z¹` identifying the two subtypes (same underlying
functions). -/
noncomputable def toZ1 : ↥(Z1m p G A) ≃+ ↥(Z1 G A) where
  toFun x := ⟨x.1, (mem_Z1m p G A x.1).mp x.2⟩
  invFun y := ⟨y.1, (mem_Z1m p G A y.1).mpr y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl

/-- `B1m` viewed as an `AddSubgroup` of `↥Z1m`. -/
noncomputable def comapB1 : AddSubgroup ↥(Z1m p G A) :=
  (Submodule.comap (Z1m p G A).subtype (B1m p G A)).toAddSubgroup

theorem mem_comapB1 (x : ↥(Z1m p G A)) : x ∈ comapB1 p G A ↔ x.1 ∈ B1 G A := by
  have h : x ∈ comapB1 p G A ↔ (Z1m p G A).subtype x ∈ B1m p G A := by
    rw [comapB1]; exact Submodule.mem_comap
  rw [h, mem_B1m]; rfl

theorem mem_comapB1' (y : ↥(Z1 G A)) : y ∈ (B1 G A).comap (Z1 G A).subtype ↔ y.1 ∈ B1 G A := by
  rw [AddSubgroup.mem_comap]; rfl

theorem map_toZ1_comap :
    AddSubgroup.map (toZ1 p G A).toAddMonoidHom (comapB1 p G A)
      = (B1 G A).comap (Z1 G A).subtype := by
  ext y
  constructor
  · intro hy
    rw [AddSubgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_comapB1']
    show ((toZ1 p G A) x : G → A) ∈ B1 G A
    rw [mem_comapB1] at hx; exact hx
  · intro hy
    rw [AddSubgroup.mem_map]
    refine ⟨⟨y.1, (mem_Z1m p G A y.1).mpr y.2⟩, ?_, ?_⟩
    · rw [mem_comapB1]; rw [mem_comapB1'] at hy; exact hy
    · ext; rfl

/-- The canonical additive equivalence `Z¹/B¹ ≅ H¹`. -/
noncomputable def e :
    (↥(Z1m p G A) ⧸ Submodule.comap (Z1m p G A).subtype (B1m p G A)) ≃+ H1 G A :=
  QuotientAddGroup.congr (comapB1 p G A) ((B1 G A).comap (Z1 G A).subtype) (toZ1 p G A)
    (map_toZ1_comap p G A)

/-! ## The `ZMod p`-module structure on `H¹` transported along `e` -/

/-- The scalar multiplication on `H¹` obtained by transporting the quotient module structure of
`Z1m ⧸ B1m` along the identification `e`. -/
noncomputable def smulH1 : SMul (ZMod p) (H1 G A) :=
  ⟨fun a x => e p G A (a • (e p G A).symm x)⟩

/-- `H¹(G, A)` is a `ZMod p`-module, with the scalar action transported from `Z1m ⧸ B1m`. -/
noncomputable def instH1 : Module (ZMod p) (H1 G A) :=
  letI := smulH1 p G A
  Function.Injective.module (ZMod p) (e p G A).symm.toAddMonoidHom (e p G A).symm.injective
    (fun a x => by
      show (e p G A).symm (e p G A (a • (e p G A).symm x)) = a • (e p G A).symm x
      rw [AddEquiv.symm_apply_apply])

end H1zmod

theorem H1_zmod_module (p : ℕ) [Fact p.Prime] (G A : Type) [Group G]
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A] :
    ∃ (Z1m B1m : Submodule (ZMod p) (G → A))
      (hZ1 : ∀ f : G → A, f ∈ Z1m ↔ f ∈ Work.GroupCohomology.Z1 G A)
      (hB1 : ∀ f : G → A, f ∈ B1m ↔ f ∈ Work.GroupCohomology.B1 G A)
      (e : (↥Z1m ⧸ Submodule.comap Z1m.subtype B1m) ≃+ Work.GroupCohomology.H1 G A)
      (inst : Module (ZMod p) (Work.GroupCohomology.H1 G A)),
      B1m ≤ Z1m ∧
      (∀ (f : G → A) (hf : f ∈ Work.GroupCohomology.Z1 G A),
        e (Submodule.Quotient.mk ⟨f, (hZ1 f).mpr hf⟩) = Work.GroupCohomology.H1π G A ⟨f, hf⟩) ∧
      (letI := inst
       ∀ (a : ZMod p) (f : ↥Z1m),
         a • e (Submodule.Quotient.mk f) = e (Submodule.Quotient.mk (a • f))) := by
  refine ⟨H1zmod.Z1m p G A, H1zmod.B1m p G A, H1zmod.mem_Z1m p G A, H1zmod.mem_B1m p G A,
    H1zmod.e p G A, H1zmod.instH1 p G A, H1zmod.B1m_le_Z1m p G A, ?_, ?_⟩
  · intro f hf; rfl
  · intro a f
    show (H1zmod.e p G A) (a • (H1zmod.e p G A).symm (H1zmod.e p G A (Submodule.Quotient.mk f)))
      = H1zmod.e p G A (Submodule.Quotient.mk (a • f))
    rw [AddEquiv.symm_apply_apply, Submodule.Quotient.mk_smul]

end Work.GroupCohomology
