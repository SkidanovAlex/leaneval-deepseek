/-
Copyright (c) 2024. All rights reserved.

# The layer dichotomy of a Suzuki 2-group: shared vocabulary

This file fixes the vocabulary used by the proof of
`Work.Higman.layers_card_dichotomy_alt` (Peterfalvi II, Ch. V §2; Higman 1963).

If `P` is a Suzuki 2-group with `FpfXi ξ` (so `|P| = q ^ 3`, `q = |Z(P)|`, `ξ` of order `q - 1`
acting fixed-point-freely), then `Z(P) = Ω₁(P)` is elementary abelian and `V := P / Z(P)` is an
elementary abelian group of order `q ^ 2`, carrying the `𝔽₂`-linear automorphism `σ` induced by
`ξ`.  The `ξ`-invariant layers `Z(P) ≤ M` of order `q ^ 2` correspond to the `σ`-invariant
subspaces of `V` of `𝔽₂`-dimension `n` (`q = 2 ^ n`).

Unlike `Work.Higman.Layers`, the vocabulary here uses the *linear* language, because the whole
proof goes through the `𝔽₂[X]`-module structure of `V` (`X` acting as `σ`).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped commutatorElement

namespace Work.Higman.LayersAlt

/-! ## Linear-algebraic vocabulary -/

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `U` is invariant under `σ`. -/
def IsInv (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop := ∀ v ∈ U, σ v ∈ U

/-- `U` is `σ`-irreducible: `U ≠ ⊥`, and the only `σ`-invariant subspaces of `U` are `⊥`, `U`. -/
def IsIrred (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop :=
  U ≠ ⊥ ∧ ∀ W : Submodule (ZMod 2) V, W ≤ U → IsInv σ W → W = ⊥ ∨ W = U

/-- The restriction of `σ` to an invariant subspace. -/
def restrInv (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) (hU : IsInv σ U) :
    U →ₗ[ZMod 2] U :=
  (σ.domRestrict U).codRestrict U (fun x => hU x.1 x.2)

/-- The `σ`-equivariant `𝔽₂`-linear maps `S → C`. -/
def HomInv (σ : V →ₗ[ZMod 2] V) (S C : Submodule (ZMod 2) V) (hS : IsInv σ S)
    (hC : IsInv σ C) : Type _ :=
  {φ : S →ₗ[ZMod 2] C // ∀ y : S, φ (restrInv σ S hS y) = restrInv σ C hC (φ y)}

/-- The `σ`-invariant subspaces of `𝔽₂`-dimension `n`. -/
def InvSubspaces (σ : V →ₗ[ZMod 2] V) (n : ℕ) : Type _ :=
  {U : Submodule (ZMod 2) V // IsInv σ U ∧ Module.finrank (ZMod 2) U = n}

/-- The `σ`-invariant subgroups of `𝔽₂`-cardinality `2 ^ n` (the form in which the
`ξ`-invariant layers are counted). -/
def InvSubgroupsCard (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    (σ : V ≃ₗ[ZMod 2] V) (n : ℕ) : Type _ :=
  {U : AddSubgroup V // (∀ v ∈ U, σ v ∈ U) ∧ Nat.card U = 2 ^ n}

/-- Over `𝔽₂` every additive subgroup of a module is a submodule: the scalars are only `0` and
`1`.  This identifies `AddSubgroup W` with `Submodule (ZMod 2) W`. -/
def addSubgroupSubmoduleEquiv (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] :
    AddSubgroup W ≃ Submodule (ZMod 2) W where
  toFun A :=
    ⟨A.toAddSubmonoid, by
      intro c x hx
      have h : c = 0 ∨ c = 1 := by revert c; decide
      rcases h with rfl | rfl
      · simpa using A.zero_mem
      · simpa using hx⟩
  invFun S := S.toAddSubgroup
  left_inv A := by
    ext x
    exact Iff.rfl
  right_inv S := by
    ext x
    exact Iff.rfl

@[simp]
theorem mem_addSubgroupSubmoduleEquiv (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    (A : AddSubgroup W) (x : W) :
    x ∈ (addSubgroupSubmoduleEquiv W A : Submodule (ZMod 2) W) ↔ x ∈ A :=
  Iff.rfl

theorem addSubgroupSubmoduleEquiv_symm (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    (A : AddSubgroup W) : (addSubgroupSubmoduleEquiv W A).toAddSubgroup = A := by
  ext x
  exact Iff.rfl

/-! ## The quotient `P / Z(P)` and the automorphism induced by `ξ` -/

variable {P : Type} [Group P] [Finite P]

theorem mem_center_mulAut {ξ : MulAut P} {z : P} (hz : z ∈ Subgroup.center P) :
    ξ z ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  obtain ⟨y', rfl⟩ := ξ.surjective y
  rw [← map_mul, ← map_mul, hz y']

theorem center_map_mulAut (ξ : MulAut P) :
    (Subgroup.center P).map ξ.toMonoidHom = Subgroup.center P := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_center_mulAut hw
  · intro hz
    exact ⟨ξ.symm z, mem_center_mulAut hz, by simp⟩

theorem center_le_comap_mulAut (ξ : MulAut P) :
    Subgroup.center P ≤ Subgroup.comap ξ.toMonoidHom (Subgroup.center P) :=
  fun z hz => mem_center_mulAut hz

/-- `P / Z(P)` is abelian whenever `P' ≤ Z(P)`. -/
theorem quot_mul_comm (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P)
    (a b : P ⧸ Subgroup.center P) : a * b = b * a := by
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have key : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [key]
  exact hcomm
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top y⁻¹) (Subgroup.mem_top x⁻¹))

/-- The `CommGroup` structure on `V = P / Z(P)` (its group structure is abelian). -/
def quotCommGroup (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) :
    CommGroup (P ⧸ Subgroup.center P) :=
  { (inferInstance : Group (P ⧸ Subgroup.center P)) with mul_comm := quot_mul_comm hcomm }

/-- `V = P / Z(P)` as an additive group: its addition is the multiplication of the quotient,
which is commutative.  (This is the additive group underlying the `𝔽₂`-vector space `V`.) -/
def quotAddCommGroup (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) :
    AddCommGroup (P ⧸ Subgroup.center P) := by
  letI : CommGroup (P ⧸ Subgroup.center P) := quotCommGroup hcomm
  exact (Additive.ofMul : P ⧸ Subgroup.center P ≃ Additive (P ⧸ Subgroup.center P)).addCommGroup

/-- **The automorphism of `V = P / Z(P)` induced by `ξ`.** -/
def quotMulEquiv (h : IsSuzuki2Grp P) (ξ : MulAut P) :
    (P ⧸ Subgroup.center P) ≃* (P ⧸ Subgroup.center P) where
  toFun := QuotientGroup.map (Subgroup.center P) (Subgroup.center P) ξ.toMonoidHom
    (center_le_comap_mulAut ξ)
  invFun := QuotientGroup.map (Subgroup.center P) (Subgroup.center P) ξ.symm.toMonoidHom
    (center_le_comap_mulAut ξ.symm)
  left_inv a := by
    refine Quotient.inductionOn a (fun x => ?_)
    rw [QuotientGroup.map_mk, QuotientGroup.map_mk]
    exact congrArg QuotientGroup.mk (by simp)
  right_inv a := by
    refine Quotient.inductionOn a (fun x => ?_)
    rw [QuotientGroup.map_mk, QuotientGroup.map_mk]
    exact congrArg QuotientGroup.mk (by simp)
  map_mul' a b := map_mul _ a b

theorem quotMulEquiv_mk (h : IsSuzuki2Grp P) (ξ : MulAut P) (x : P) :
    quotMulEquiv h ξ (QuotientGroup.mk x) = QuotientGroup.mk (ξ x) :=
  QuotientGroup.map_mk (Subgroup.center P) (Subgroup.center P) ξ.toMonoidHom
    (center_le_comap_mulAut ξ) x

theorem quotMulEquiv_pow_mk (h : IsSuzuki2Grp P) (ξ : MulAut P) (k : ℕ) (x : P) :
    (quotMulEquiv h ξ ^ k) (QuotientGroup.mk x) = QuotientGroup.mk ((ξ ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, quotMulEquiv_mk, ih]; rfl

/-! ## A named commutator of subgroups

So that statements can mention `⁅A, B⁆` without opening the `commutatorElement` scope. -/

/-- The commutator subgroup `⁅A, B⁆` of two subgroups. -/
def subComm (A B : Subgroup P) : Subgroup P := ⁅A, B⁆

@[simp] theorem subComm_eq (A B : Subgroup P) : subComm A B = ⁅A, B⁆ := rfl

end Work.Higman.LayersAlt
