/-
Copyright: the martinet_totally_real_towers team.

# `H¹(G,M)` for a module with trivial action

For a discrete `G`-module `M` with trivial action, `Z¹(G,M)` is the group of continuous additive
homomorphisms `G → M` and `B¹(G,M) = 0`, so `H¹(G,M) ≃ ContAddHom G M`.
-/

import Submission.Work.ConCohomology.Functoriality
import Submission.Work.ConCohomology.B1_eq_bot_of_trivial
import Submission.Work.ConCohomology.isCocycle1_iff_of_trivial

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section TrivialAction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]
variable (htriv : ∀ (σ : G) (m : M), σ • m = m)

/-- For trivial action, `1`-cocycles are exactly the continuous additive homomorphisms. -/
noncomputable def Z1EquivContAddHom : Z1 G M ≃+ ContAddHom G M where
  toFun z := ⟨z.1, z.1.isLocallyConstant, (isCocycle1_iff_of_trivial htriv _).mp (mem_Z1.mp z.2)⟩
  invFun φ := ⟨⟨φ.1, φ.2.1⟩, mem_Z1.mpr ((isCocycle1_iff_of_trivial htriv _).mpr φ.2.2)⟩
  left_inv z := by ext n; rfl
  right_inv φ := by ext n; rfl
  map_add' a b := by ext n; rfl

@[simp] lemma Z1EquivContAddHom_apply (z : Z1 G M) (σ : G) :
    (Z1EquivContAddHom htriv z : G → M) σ = z.1 σ := rfl

lemma B1'_eq_bot (htriv : ∀ (σ : G) (m : M), σ • m = m) : B1' G M = ⊥ := by
  rw [B1', B1_eq_bot_of_trivial htriv]
  ext z
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_bot, AddSubgroup.coe_subtype]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    rw [h]
    rfl

/-- The natural map `H¹(G,M) → ContAddHom G M` for trivial action, from the identification of
`1`-cocycles with continuous additive homomorphisms. -/
noncomputable def H1ToContAddHom (htriv : ∀ (σ : G) (m : M), σ • m = m) :
    H1 G M →+ ContAddHom G M :=
  QuotientAddGroup.lift (B1' G M) (Z1EquivContAddHom htriv).toAddMonoidHom
    (by rw [B1'_eq_bot htriv]; exact bot_le)

@[simp] lemma H1ToContAddHom_mk (htriv : ∀ (σ : G) (m : M), σ • m = m) (z : Z1 G M) :
    H1ToContAddHom htriv (H1.mk z) = Z1EquivContAddHom htriv z :=
  QuotientAddGroup.lift_mk _ _ z

/-- `H¹(G,M) ≃` continuous additive homomorphisms `G → M`, for trivial action. -/
noncomputable def H1EquivContAddHom (htriv : ∀ (σ : G) (m : M), σ • m = m) :
    H1 G M ≃ ContAddHom G M where
  toFun := H1ToContAddHom htriv
  invFun φ := H1.mk ((Z1EquivContAddHom htriv).symm φ)
  left_inv x := by
    refine QuotientAddGroup.induction_on x ?_
    intro z
    change H1.mk ((Z1EquivContAddHom htriv).symm (H1ToContAddHom htriv (H1.mk z))) = H1.mk z
    rw [H1ToContAddHom_mk, AddEquiv.symm_apply_apply]
  right_inv φ := by
    change H1ToContAddHom htriv (H1.mk ((Z1EquivContAddHom htriv).symm φ)) = φ
    rw [H1ToContAddHom_mk, AddEquiv.apply_symm_apply]

end TrivialAction

end Work.ConCohomology
