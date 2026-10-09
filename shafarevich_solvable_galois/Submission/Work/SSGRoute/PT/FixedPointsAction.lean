import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-point module of a normal subgroup, as a module over the quotient

Let `Γ` be a group acting on a `ZMod p`-module `N` (`DistribMulAction` + `SMulCommClass`), and let
`V ⊴ Γ` be a normal subgroup.  This file provides

* `Work.SSGRoute.PT.fixedPoints p N V` : the `ZMod p`-submodule of `V`-fixed points `N^V`;
* `Work.SSGRoute.PT.quotientActionHom p N V` : the (well defined!) action of the quotient `Γ ⧸ V`
  on `N^V`, obtained by lifting `g ↦ (n ↦ g • n)` through `Γ → Γ ⧸ V` (well defined because
  elements of `V` act trivially on `N^V` by definition);
* the `DistribMulAction (Γ ⧸ V) N^V` instance induced from it, together with the `SMulCommClass`
  and `Finite` instances, so that the vanishing theorems for `2`-cocycles
  (`Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth`) apply to `Γ ⧸ V` with coefficients
  `N^V`.
-/

namespace Work.SSGRoute.PT

open scoped Pointwise

variable {Γ : Type} [Group Γ]

/-- The `ZMod p`-submodule of `V`-fixed points of the `Γ`-module `N`. -/
def fixedPoints (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N] (V : Subgroup Γ) :
    Submodule (ZMod p) N where
  carrier := {n | ∀ v ∈ V, v • n = n}
  zero_mem' := by intro v _; exact smul_zero v
  add_mem' := by intro a b ha hb v hv; rw [smul_add, ha v hv, hb v hv]
  smul_mem' := by intro c x hx v hv; rw [smul_comm v c x, hx v hv]

@[simp] lemma mem_fixedPoints {p : ℕ} [Fact p.Prime] {N : Type*} [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    {V : Subgroup Γ} {n : N} :
    n ∈ fixedPoints p N V ↔ ∀ v ∈ V, v • n = n := Iff.rfl

/-- The linear map `n ↦ g • n` on `N`. -/
noncomputable def gLinearMap (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (g : Γ) : N →ₗ[ZMod p] N where
  toFun := fun n => g • n
  map_add' := by intro a b; exact smul_add g a b
  map_smul' := by intro c a; exact smul_comm g c a

lemma gLinearMap_apply {p : ℕ} [Fact p.Prime] {N : Type*} [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (g : Γ) (n : N) : gLinearMap p N g n = g • n := rfl

/-- The induced linear map on the `V`-fixed points. -/
noncomputable def gOnFixed (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] (g : Γ) :
    ↥(fixedPoints p N V) →ₗ[ZMod p] ↥(fixedPoints p N V) :=
  ((gLinearMap p N g).comp (fixedPoints p N V).subtype).codRestrict
    (fixedPoints p N V)
    (fun n => by
      intro v hv
      have hconj : g⁻¹ * v * g ∈ V := by
        have h := (inferInstance : V.Normal).conj_mem v hv g⁻¹
        simpa using h
      show v • (g • ((n : ↥(fixedPoints p N V)) : N)) = g • ((n : ↥(fixedPoints p N V)) : N)
      rw [← mul_smul, show v * g = g * (g⁻¹ * v * g) from by group, mul_smul,
        (n : ↥(fixedPoints p N V)).2 (g⁻¹ * v * g) hconj])

lemma gOnFixed_apply (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] (g : Γ) (n : ↥(fixedPoints p N V)) :
    ((gOnFixed p N V g n : ↥(fixedPoints p N V)) : N) = g • ((n : ↥(fixedPoints p N V)) : N) :=
  rfl

/-- The action of `Γ ⧸ V` on the `V`-fixed points, by the action of any representative. -/
noncomputable def quotientActionHom (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] : Γ ⧸ V →* Module.End (ZMod p) ↥(fixedPoints p N V) :=
  QuotientGroup.lift V
    { toFun := gOnFixed p N V
      map_one' := by
        ext n : 1
        exact Subtype.ext (one_smul Γ ((n : ↥(fixedPoints p N V)) : N))
      map_mul' := by
        intro g h
        ext n : 1
        exact Subtype.ext (mul_smul g h ((n : ↥(fixedPoints p N V)) : N)) }
    (by
      intro g hg
      ext n : 1
      exact Subtype.ext ((n : ↥(fixedPoints p N V)).2 g hg))

lemma quotientActionHom_mk (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] (g : Γ) :
    quotientActionHom p N V (QuotientGroup.mk' V g) = gOnFixed p N V g :=
  QuotientGroup.lift_mk' V _ g

lemma quotientActionHom_mk_apply (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] (g : Γ) (n : ↥(fixedPoints p N V)) :
    ((quotientActionHom p N V (QuotientGroup.mk' V g)) n : N)
      = g • ((n : ↥(fixedPoints p N V)) : N) := by
  rw [quotientActionHom_mk]
  rfl

/-- The `Γ ⧸ V`-module structure on the `V`-fixed points. -/
noncomputable instance instDistribMulActionFixedPoints (p : ℕ) [Fact p.Prime] (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction Γ N]
    [SMulCommClass Γ (ZMod p) N] (V : Subgroup Γ) [V.Normal] :
    DistribMulAction (Γ ⧸ V) ↥(fixedPoints p N V) where
  smul q x := (quotientActionHom p N V q) x
  one_smul x := by
    change (quotientActionHom p N V 1) x = x
    rw [map_one]
    rfl
  mul_smul q q' x := by
    change (quotientActionHom p N V (q * q')) x
      = (quotientActionHom p N V q) ((quotientActionHom p N V q') x)
    rw [map_mul]
    rfl
  smul_zero q := (quotientActionHom p N V q).map_zero
  smul_add q x y := (quotientActionHom p N V q).map_add x y

@[simp] lemma smul_fixedPoints_coe (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] (q : Γ ⧸ V) (x : ↥(fixedPoints p N V)) :
    ((q • x : ↥(fixedPoints p N V)) : N) = (quotientActionHom p N V q) x := rfl

/-- The `Γ ⧸ V`-action on `N^V` is `ZMod p`-linear, so scaling commutes with it. -/
instance instSMulCommClassFixedPoints (p : ℕ) [Fact p.Prime] (N : Type*)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction Γ N]
    [SMulCommClass Γ (ZMod p) N] (V : Subgroup Γ) [V.Normal] :
    SMulCommClass (Γ ⧸ V) (ZMod p) ↥(fixedPoints p N V) where
  smul_comm q c x := by
    show (q • (c • x) : ↥(fixedPoints p N V)) = c • (q • x)
    exact (quotientActionHom p N V q).map_smul c x

instance instFiniteFixedPoints (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    (V : Subgroup Γ) [V.Normal] [Finite N] : Finite ↥(fixedPoints p N V) := inferInstance

end Work.SSGRoute.PT
