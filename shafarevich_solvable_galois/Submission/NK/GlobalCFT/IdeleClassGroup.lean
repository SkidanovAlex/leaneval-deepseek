import Mathlib.Order.CompletePartialOrder
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle class group

For a number field `K` the **idèle class group** is `C_K = 𝕀 K ⧸ Kˣ`, the quotient of the idèle
group by the principal idèles.  We also introduce

* `NK.GlobalCFT.IdeleClassGroup.rayClassGroup`: the ray class group `𝕀 K ⧸ (Kˣ · U)` attached to
  a subgroup `U ≤ 𝕀 K` of "congruence idèles"; every ray class group is a quotient of `C_K`,
* `NK.GlobalCFT.IdeleClassGroup.normOneClassGroup`: the norm-one idèle class group
  `C¹_K = 𝕀¹ K ⧸ Kˣ`, which is compact (finiteness of the class group and Dirichlet's unit
  theorem).

## Main definitions

* `NK.GlobalCFT.IdeleClassGroup K`, notation `C[K]`.
* `NK.GlobalCFT.IdeleClassGroup.mk`: the quotient map `𝕀 K →* C K`.
* `NK.GlobalCFT.IdeleClassGroup.rayClassGroup`.
* `NK.GlobalCFT.IdeleClassGroup.normOneClassGroup`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

/-- The **idèle class group** `C_K = 𝕀 K ⧸ Kˣ` of a number field. -/
abbrev IdeleClassGroup (K : Type*) [Field K] [NumberField K] : Type _ :=
  Idele K ⧸ Idele.principalSubgroup K

/-- `C[K]` is notation for the idèle class group of `K`. -/
scoped notation "C[" K "]" => IdeleClassGroup K

namespace IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The quotient map `𝕀 K →* C K`. -/
def mk (K : Type*) [Field K] [NumberField K] : Idele K →* IdeleClassGroup K :=
  QuotientGroup.mk' (Idele.principalSubgroup K)

@[simp] theorem mk_apply (x : Idele K) : mk K x = QuotientGroup.mk x := rfl

theorem mk_surjective (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (mk K) :=
  QuotientGroup.mk'_surjective _

/-- The principal idèles have content one (the product formula), so the content descends to the
idèle class group. -/
theorem principalSubgroup_le_ker_abs (K : Type*) [Field K] [NumberField K] :
    Idele.principalSubgroup K ≤ (Idele.abs K).ker := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  exact NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele k

/-- The **content** `|·| : C K →* ℝˣ`, induced by the idèle content. -/
def abs (K : Type*) [Field K] [NumberField K] : IdeleClassGroup K →* ℝˣ :=
  QuotientGroup.lift (Idele.principalSubgroup K) (Idele.abs K) (principalSubgroup_le_ker_abs K)

@[simp] theorem abs_mk (x : Idele K) : abs K (mk K x) = Idele.abs K x := rfl

/-- Two idèles have the same class iff they differ by a principal idèle. -/
theorem mk_eq_mk_iff {x y : Idele K} :
    mk K x = mk K y ↔ x⁻¹ * y ∈ Idele.principalSubgroup K :=
  QuotientGroup.eq

/-! ### Ray class groups -/

/-- The **ray class group** of `K` modulo a subgroup `U ≤ 𝕀 K` of congruence idèles:
the quotient `𝕀 K ⧸ (Kˣ · U)`. -/
abbrev rayClassGroup (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K)) : Type _ :=
  Idele K ⧸ (Idele.principalSubgroup K ⊔ U)

theorem principalSubgroup_le_comap_sup (U : Subgroup (Idele K)) :
    Idele.principalSubgroup K ≤ Subgroup.comap (MonoidHom.id (Idele K))
      (Idele.principalSubgroup K ⊔ U) := by
  rw [Subgroup.comap_id]
  exact le_sup_left

/-- The canonical surjection `C K →* 𝕀 K ⧸ (Kˣ · U)` exhibiting a ray class group as a quotient
of the idèle class group. -/
def rayClassGroupMk (K : Type*) [Field K] [NumberField K] (U : Subgroup (Idele K)) :
    IdeleClassGroup K →* rayClassGroup K U :=
  QuotientGroup.map _ _ (MonoidHom.id _) (principalSubgroup_le_comap_sup U)

theorem rayClassGroupMk_surjective (U : Subgroup (Idele K)) :
    Function.Surjective (rayClassGroupMk K U) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x => exact ⟨mk K x, QuotientGroup.map_mk _ _ _ _ x⟩

/-- The kernel of `C K →* 𝕀 K ⧸ (Kˣ · U)` is the image of `U` in `C K`. -/
theorem ker_rayClassGroupMk (U : Subgroup (Idele K)) :
    (rayClassGroupMk K U).ker = U.map (mk K) := by
  have hbot : Subgroup.map (QuotientGroup.mk' (Idele.principalSubgroup K))
      (Idele.principalSubgroup K) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [rayClassGroupMk,
    QuotientGroup.ker_map _ _ _ (principalSubgroup_le_comap_sup (K := K) U),
    Subgroup.comap_id, Subgroup.map_sup, hbot, bot_sup_eq]
  rfl

/-! ### The norm-one idèle class group -/

/-- The **norm-one idèle class group** `C¹_K = 𝕀¹ K ⧸ Kˣ`. -/
abbrev normOneClassGroup (K : Type*) [Field K] [NumberField K] : Type _ :=
  (Idele.normOne K) ⧸ ((Idele.principalSubgroup K).subgroupOf (Idele.normOne K))

end IdeleClassGroup

end NK.GlobalCFT
