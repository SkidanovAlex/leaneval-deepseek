import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.EulerSymm.BaseAux
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `D_C`-action on the level field, its units and its `p`-Kummer group

This file supplies the vocabulary the arithmetic input `harith` (Milne, *Arithmetic Duality
Theorems*, I.2.11) needs on the Kummer side of the level:

* `EulerSymm.mupLevelField k Ω K A = K ⊔ Ω^{D_A}` — the **level field** of the `μ_p`-Kummer theory
  at the place `A`.  Its fixing subgroup is the level group `UD k Ω K A = D_A ⊓ Gal(Ω/K)`
  (`mupLevelField_fixingSubgroup`), so `KummerGroup p ↥(mupLevelField k Ω K A)` is the
  `𝔽_p[D_C]`-module whose class is the arithmetic content of I.2.11.
* `EulerSymm.mupLevelField_map_le` — every `δ ∈ D_C = decomp k A ⊓ res⁻¹(Γ)` maps the level field
  into itself (the compositum of the Galois field `K` with the fixed field `Ω^{D_A}`, and
  `δ ∈ D_A` normalises `D_A`);
* `EulerSymm.mupLevelFieldAut` / `mupLevelFieldAutHom` — the induced `k`-algebra automorphism of the
  level field, as a `↥D_C →* (↥E ≃ₐ[k] ↥E)`;
* `EulerSymm.mupLevelUnitsAutHom` — the induced action on the units `Eˣ` (`Units.map`);
* `EulerSymm.mupLevelKummerFrob` — the induced action on the `p`-Kummer group
  `Eˣ ⧸ (Eˣ)^p` (`QuotientGroup.map`), as a `↥D_C →* (KummerGroup p ↥E →* KummerGroup p ↥E)`.

This is the companion of `EulerSymm.lcHomsConjAction` (the same action on the `lcHoms` side) and the
prerequisite of the `σ`-equivariant Kummer isomorphism at the level group
`Work.SSGRoute.H1loc p k Ω K (DualMod p T) (UD k Ω K A) ≅ ↥(KummerGroup p ↥E)`
(template: `HSRow.kummerEquivInertia`, for the inertia; the non-equivariant version at the level is
`PT.kummer_rel_H1loc_equiv`).
-/

open scoped Pointwise
open Classical
open Additive

namespace Work.SSGRoute.EulerSymm

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (A : ValuationSubring Ω)

/-- **The level field** of the `μ_p`-Kummer theory at the place `A`: the compositum
`K ⊔ Ω^{D_A}` of the level field `K` with the decomposition field of `A`. -/
abbrev mupLevelField : IntermediateField k Ω := K ⊔ SSGRoute.mup.decompField k Ω A

lemma mupLevelField_decompField_le : SSGRoute.mup.decompField k Ω A ≤ mupLevelField k Ω K A :=
  le_sup_right

lemma mupLevelField_K_le : K ≤ mupLevelField k Ω K A := le_sup_left

/-- **The fixing subgroup of the level field is the level group `UD`.** -/
theorem mupLevelField_fixingSubgroup :
    (mupLevelField k Ω K A).fixingSubgroup = UD k Ω K A := by
  rw [mupLevelField, IntermediateField.fixingSubgroup_sup,
    Work.SSGRoute.PTembedding.fixingSubgroup_decompField k Ω A]
  exact inf_comm _ _

/-- **The Galois field `K` is stable under the absolute Galois group.** -/
theorem K_map_le (δ : Ω ≃ₐ[k] Ω) : K.map δ.toAlgHom ≤ K := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  intro y hy
  rw [IntermediateField.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← InfiniteGalois.fixedField_fixingSubgroup K] at hx ⊢
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro u hu
  have h1 : δ⁻¹ * u * δ ∈ K.fixingSubgroup := by
    simpa using
      Subgroup.Normal.conj_mem (inferInstance : (K.fixingSubgroup).Normal) u hu δ⁻¹
  calc u (δ x) = (u * δ) x := rfl
    _ = (δ * (δ⁻¹ * u * δ)) x := by rw [show u * δ = δ * (δ⁻¹ * u * δ) by group]
    _ = δ ((δ⁻¹ * u * δ) x) := rfl
    _ = δ x := by rw [hx _ h1]

/-- **The level field is stable under the decomposition group `D_A` and under `K`'s Galois
action**: for `δ ∈ D_C ⊆ D_A`, the image of the level field under `δ` lies in the level field. -/
theorem mupLevelField_map_le (Γ : Subgroup (K ≃ₐ[k] K)) {δ : Ω ≃ₐ[k] Ω}
    (hδ : δ ∈ DC k Ω K A Γ) :
    (mupLevelField k Ω K A).map δ.toAlgHom ≤ mupLevelField k Ω K A := by
  rw [mupLevelField, IntermediateField.map_sup]
  refine sup_le ((K_map_le (k := k) (Ω := Ω) (K := K) δ).trans le_sup_left) ?_
  refine (?_ : (SSGRoute.mup.decompField k Ω A).map δ.toAlgHom
      ≤ SSGRoute.mup.decompField k Ω A).trans le_sup_right
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [SSGRoute.mup.decompField, IntermediateField.mem_fixedField_iff] at hy ⊢
  intro u hu
  have h1 : δ⁻¹ * u * δ ∈ SSGRoute.decomp k A := (SSGRoute.decomp k A).mul_mem
    ((SSGRoute.decomp k A).mul_mem ((SSGRoute.decomp k A).inv_mem hδ.1) hu) hδ.1
  calc u (δ y) = (u * δ) y := rfl
    _ = (δ * (δ⁻¹ * u * δ)) y := by rw [show u * δ = δ * (δ⁻¹ * u * δ) by group]
    _ = δ ((δ⁻¹ * u * δ) y) := rfl
    _ = δ y := by rw [hy _ h1]

/-- **The `k`-algebra automorphism of the level field induced by `δ ∈ D_C`.** -/
noncomputable def mupLevelFieldAut (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ)) :
    ↥(mupLevelField k Ω K A) ≃ₐ[k] ↥(mupLevelField k Ω K A) where
  toFun x := ⟨(δ : Ω ≃ₐ[k] Ω) x,
    mupLevelField_map_le k Ω K A Γ δ.2
      ((IntermediateField.mem_map (S := mupLevelField k Ω K A)
        (f := (δ : Ω ≃ₐ[k] Ω).toAlgHom)).mpr ⟨x, x.2, rfl⟩)⟩
  invFun x := ⟨(δ : Ω ≃ₐ[k] Ω)⁻¹ x,
    mupLevelField_map_le k Ω K A Γ ((DC k Ω K A Γ).inv_mem δ.2)
      ((IntermediateField.mem_map (S := mupLevelField k Ω K A)
        (f := ((δ : Ω ≃ₐ[k] Ω)⁻¹).toAlgHom)).mpr ⟨x, x.2, rfl⟩)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ _)

@[simp] lemma mupLevelFieldAut_coe (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ))
    (x : ↥(mupLevelField k Ω K A)) :
    ((mupLevelFieldAut k Ω K A Γ δ x : ↥(mupLevelField k Ω K A)) : Ω)
      = (δ : Ω ≃ₐ[k] Ω) x := rfl

/-- The induced automorphisms, as a group homomorphism `↥D_C →* Aut_k(↥E)`. -/
noncomputable def mupLevelFieldAutHom (Γ : Subgroup (K ≃ₐ[k] K)) :
    ↥(DC k Ω K A Γ) →* (↥(mupLevelField k Ω K A) ≃ₐ[k] ↥(mupLevelField k Ω K A)) where
  toFun := mupLevelFieldAut k Ω K A Γ
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' a b := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rfl

/-- **The induced action on the units of the level field**: `Units.map` of the algebra automorphism.
-/
noncomputable def mupLevelUnitsAutHom (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ)) :
    (↥(mupLevelField k Ω K A))ˣ →* (↥(mupLevelField k Ω K A))ˣ :=
  Units.map ((mupLevelFieldAutHom k Ω K A Γ δ).toMonoidHom)

@[simp] lemma mupLevelUnitsAutHom_coe (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ))
    (x : (↥(mupLevelField k Ω K A))ˣ) :
    (((mupLevelUnitsAutHom k Ω K A Γ δ x : (↥(mupLevelField k Ω K A))ˣ) :
        ↥(mupLevelField k Ω K A)) : Ω)
      = (δ : Ω ≃ₐ[k] Ω) (x : ↥(mupLevelField k Ω K A)) := rfl

/-- **The induced action on the `p`-Kummer group of the level field.** -/
noncomputable def mupLevelKummerFrob (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ)) :
    SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A) →*
      SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A) :=
  QuotientGroup.map _ _ (mupLevelUnitsAutHom k Ω K A Γ δ) (by
    intro y hy
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hy
    have hz' : z ^ p = y := hz
    refine MonoidHom.mem_range.mpr ⟨mupLevelUnitsAutHom k Ω K A Γ δ z, ?_⟩
    show (mupLevelUnitsAutHom k Ω K A Γ δ z) ^ p
      = mupLevelUnitsAutHom k Ω K A Γ δ y
    rw [← map_pow (mupLevelUnitsAutHom k Ω K A Γ δ), hz'])

/-! ## Packaging the Kummer action as a `MulAction` and, on `Additive`, as a
`DistribMulAction` compatible with the `ZMod p`-module structure -/

/-- **The Kummer action of `1` is the identity.** -/
lemma mupLevelKummerFrob_one (Γ : Subgroup (K ≃ₐ[k] K)) :
    mupLevelKummerFrob p k Ω K A Γ 1
      = MonoidHom.id (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)) := by
  refine MonoidHom.ext fun y => ?_
  refine QuotientGroup.induction_on y fun z => ?_
  show mupLevelKummerFrob p k Ω K A Γ 1 (QuotientGroup.mk z) = QuotientGroup.mk z
  rw [show mupLevelKummerFrob p k Ω K A Γ 1 (QuotientGroup.mk z)
      = QuotientGroup.mk (mupLevelUnitsAutHom k Ω K A Γ 1 z) from rfl]
  congr 1

/-- **The Kummer action is multiplicative in `δ`.** -/
lemma mupLevelKummerFrob_mul (Γ : Subgroup (K ≃ₐ[k] K)) (a b : ↥(DC k Ω K A Γ)) :
    mupLevelKummerFrob p k Ω K A Γ (a * b)
      = (mupLevelKummerFrob p k Ω K A Γ a).comp (mupLevelKummerFrob p k Ω K A Γ b) := by
  refine MonoidHom.ext fun y => ?_
  refine QuotientGroup.induction_on y fun z => ?_
  show mupLevelKummerFrob p k Ω K A Γ (a * b) (QuotientGroup.mk z)
    = mupLevelKummerFrob p k Ω K A Γ a
        (mupLevelKummerFrob p k Ω K A Γ b (QuotientGroup.mk z))
  rw [show mupLevelKummerFrob p k Ω K A Γ (a * b) (QuotientGroup.mk z)
      = QuotientGroup.mk (mupLevelUnitsAutHom k Ω K A Γ (a * b) z) from rfl,
    show mupLevelKummerFrob p k Ω K A Γ b (QuotientGroup.mk z)
      = QuotientGroup.mk (mupLevelUnitsAutHom k Ω K A Γ b z) from rfl,
    show mupLevelKummerFrob p k Ω K A Γ a
          (QuotientGroup.mk (mupLevelUnitsAutHom k Ω K A Γ b z))
      = QuotientGroup.mk (mupLevelUnitsAutHom k Ω K A Γ a
          (mupLevelUnitsAutHom k Ω K A Γ b z)) from rfl]
  congr 1

/-- **The `↥D_C`-action on the `p`-Kummer group of the level field**: the class of a unit `u` is
sent to the class of `δ u`. -/
noncomputable instance mupLevelKummerMulAction (Γ : Subgroup (K ≃ₐ[k] K)) :
    MulAction ↥(DC k Ω K A Γ) (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)) where
  smul δ x := mupLevelKummerFrob p k Ω K A Γ δ x
  one_smul x := by
    show mupLevelKummerFrob p k Ω K A Γ 1 x = x
    rw [mupLevelKummerFrob_one]
    rfl
  mul_smul a b x := by
    show mupLevelKummerFrob p k Ω K A Γ (a * b) x
      = mupLevelKummerFrob p k Ω K A Γ a (mupLevelKummerFrob p k Ω K A Γ b x)
    rw [mupLevelKummerFrob_mul]
    rfl

/-- **The `p`-Kummer group of the level field has exponent `p`.** -/
lemma mupLevelKummerGroup_pow_eq_one
    (g : SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)) : g ^ p = 1 := by
  refine QuotientGroup.induction_on g fun z => ?_
  show (QuotientGroup.mk ((z : (↥(mupLevelField k Ω K A))ˣ) ^ p) :
      SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨z, rfl⟩)

/-- In an additive group with a distributive action of `G`, `g • (k • x) = k • (g • x)`: the action
of `G` is compatible with the `ℕ`-scalar action.  (Restated from
`Work.Shrinking.smul_nsmul_of_distribMulAction`.) -/
lemma smul_nsmul_comm_of_distribMulAction {G A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (g : G) (k : ℕ) (x : A) : g • (k • x) = k • (g • x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]

/-- **The `↥D_C`-action transported to `Additive (KummerGroup p ↥E)`**, i.e. the `𝔽_p`-vector space
underlying the level Kummer group (the `p`-torsion additive group of `Eˣ/(Eˣ)^p`). -/
noncomputable instance mupLevelKummerAdditiveDistribMulAction (Γ : Subgroup (K ≃ₐ[k] K)) :
    DistribMulAction ↥(DC k Ω K A Γ)
      (Additive (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A))) where
  smul δ x := Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ δ (Additive.toMul x))
  one_smul x := by
    show Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ 1 (Additive.toMul x)) = x
    rw [mupLevelKummerFrob_one]
    rfl
  mul_smul a b x := by
    show Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ (a * b) (Additive.toMul x))
      = Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ a
          (mupLevelKummerFrob p k Ω K A Γ b (Additive.toMul x)))
    rw [mupLevelKummerFrob_mul]
    rfl
  smul_zero δ := by
    show Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ δ 1) = 0
    rw [map_one]
    rfl
  smul_add δ x y := by
    show Additive.ofMul
        (mupLevelKummerFrob p k Ω K A Γ δ (Additive.toMul x * Additive.toMul y))
      = Additive.ofMul (mupLevelKummerFrob p k Ω K A Γ δ (Additive.toMul x)
          * mupLevelKummerFrob p k Ω K A Γ δ (Additive.toMul y))
    rw [map_mul]

/-- **The `ZMod p`-module structure on `Additive (KummerGroup p ↥E)`** (the level Kummer group has
exponent `p`). -/
noncomputable instance mupLevelKummerAdditiveModule :
    Module (ZMod p) (Additive (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A))) :=
  AddCommGroup.zmodModule (n := p)
    (G := Additive (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)))
    (fun x => by
      refine Additive.toMul.injective ?_
      rw [toMul_nsmul, toMul_zero]
      exact mupLevelKummerGroup_pow_eq_one (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
        (Additive.toMul x))

/-- **The `ZMod p`-scalars commute with the `↥D_C`-action** on the level Kummer group: it is an
`𝔽_p[↥D_C]`-module.  (`c • x = c.val • x` for the `ZMod p`-structure above, and the `↥D_C`-action
commutes with the `ℕ`-scalars by `smul_nsmul_comm_of_distribMulAction`.) -/
noncomputable instance mupLevelKummerAdditiveSMulCommClass (Γ : Subgroup (K ≃ₐ[k] K)) :
    SMulCommClass ↥(DC k Ω K A Γ) (ZMod p)
      (Additive (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A))) where
  smul_comm δ c x := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have hcv : ∀ y : Additive (SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)),
        (c : ZMod p) • y = c.val • y := by
      intro y
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul (ZMod p)]
    rw [hcv x, hcv (δ • x)]
    exact smul_nsmul_comm_of_distribMulAction δ c.val x

end

end Work.SSGRoute.EulerSymm
