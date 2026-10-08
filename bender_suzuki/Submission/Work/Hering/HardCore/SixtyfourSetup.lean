import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.aut_transitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace Work.Hering.HardCore

open scoped IsMulCommutative

/-! # Generic infrastructure for `Work.Hering.HardCore.exists_normal_sixtyfour_min`

This file collects the (configuration-independent) definitions used in the proof that in the
non-abelian configuration of Peterfalvi I §4 there is a normal subgroup `D` of order `64` between
`V` and `C = C_G(V)` which is minimal among the normal subgroups between `V` and `D`:

* `conj_transitive_on_V`: `G` is transitive by conjugation on the non-identity elements of `V`;
* `conjQ`: the conjugation action of `G` on a quotient `D/V` for `V, D ⊴ G`;
* `linOfMulAut`: group automorphisms of an elementary abelian `2`-group are linear;
* `QVgroup`, `EofW`: the correspondence between submodules of `Additive (D/V)` and subgroups
  of `G` between `V` and `D`.
-/

/-- If `V ⊴ G` has order `8` and exponent two and `G` realises every automorphism of `V`
(`ActsAsAut V hV`), then `G` is transitive by conjugation on the non-identity elements of `V`. -/
theorem conj_transitive_on_V {G : Type*} [Group G] [Finite G] (V : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hAut : Work.Hering.ActsAsAut V hV) :
    ∀ u w : G, u ∈ V → w ∈ V → u ≠ 1 → w ≠ 1 → ∃ g : G, g * u * g⁻¹ = w := by
  intro u w hu hw hu1 hw1
  have hexp' : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨φ, hφ⟩ := aut_transitive hcard hexp' ⟨u, hu⟩ ⟨w, hw⟩
    (by simpa using hu1) (by simpa using hw1)
  obtain ⟨g, hg⟩ := hAut φ
  refine ⟨g, ?_⟩
  have h1 := hg ⟨u, hu⟩
  rw [hφ] at h1
  exact (congrArg Subtype.val h1).symm

/-- The conjugation automorphism of `↥D` (for `D ⊴ G`) maps the (normal) subgroup `V.subgroupOf D`
to itself. -/
lemma map_conjNormal_subgroupOf {G : Type*} [Group G] (V D : Subgroup G) [hV : V.Normal]
    [D.Normal] (g : G) :
    Subgroup.map (↑(MulAut.conjNormal (H := D) g)) (V.subgroupOf D) = V.subgroupOf D := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have h1 : (x : G) = g * (y : G) * g⁻¹ := by
      have := congrArg (fun t : ↥D => (t : G)) hyx
      simpa [MulAut.conjNormal_apply] using this.symm
    rw [h1]
    exact Subgroup.Normal.conj_mem hV (y : G) hy g
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conjNormal (H := D) g).symm x, ?_,
      (MulAut.conjNormal (H := D) g).apply_symm_apply x⟩
    rw [Subgroup.mem_subgroupOf]
    rw [MulAut.conjNormal_symm_apply]
    exact Subgroup.Normal.conj_mem' hV (x : G) (by rwa [Subgroup.mem_subgroupOf] at hx) g

/-- The conjugation action of `G` on the quotient `↥D ⧸ V.subgroupOf D`, for `V, D ⊴ G`
(`V` need not be contained in `D`; in applications it is). -/
noncomputable def conjQ {G : Type*} [Group G] (V D : Subgroup G) [V.Normal] [D.Normal] :
    G →* MulAut (↥D ⧸ V.subgroupOf D) where
  toFun g := QuotientGroup.congr (V.subgroupOf D) (V.subgroupOf D)
    (MulAut.conjNormal (H:=D) g) (map_conjNormal_subgroupOf V D g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ a => simp [QuotientGroup.congr_apply, MulAut.conjNormal_apply]
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ a => simp [QuotientGroup.congr_apply, MulAut.conjNormal_apply, mul_assoc]

lemma conjQ_mk {G : Type*} [Group G] (V D : Subgroup G) [V.Normal] [D.Normal] (g : G) (a : ↥D) :
    conjQ V D g (QuotientGroup.mk' (V.subgroupOf D) a) =
      QuotientGroup.mk' (V.subgroupOf D) (MulAut.conjNormal (H := D) g a) := by
  simp [conjQ, QuotientGroup.congr_apply]

section LinConv

variable {Q : Type*} [CommGroup Q] [Module (ZMod 2) (Additive Q)]

/-- A group automorphism of an elementary abelian `2`-group, seen as a linear automorphism of the
corresponding `𝔽₂`-vector space (linearity over `𝔽₂` is automatic). -/
noncomputable def linOfMulAut (φ : MulAut Q) : Additive Q ≃ₗ[ZMod 2] Additive Q where
  toFun x := Additive.ofMul (φ (Additive.toMul x))
  invFun x := Additive.ofMul (φ.symm (Additive.toMul x))
  left_inv x := by simp [toMul_ofMul, MulEquiv.apply_symm_apply, ofMul_toMul]
  right_inv x := by simp [toMul_ofMul, MulEquiv.symm_apply_apply, ofMul_toMul]
  map_add' x y := by simp [toMul_add, ofMul_mul]
  map_smul' c x := by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · simp only [RingHom.id_apply, zero_smul, toMul_zero, map_one, ofMul_one]
    · simp only [RingHom.id_apply, one_smul]

/-- `linOfMulAut` as a monoid homomorphism. -/
noncomputable def linOfMulAutHom :
    MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) where
  toFun := linOfMulAut
  map_one' := by ext x; simp [linOfMulAut]
  map_mul' f g := by ext x; simp [linOfMulAut]

@[simp] lemma linOfMulAut_apply (φ : MulAut Q) (x : Q) :
    linOfMulAut φ (Additive.ofMul x) = Additive.ofMul (φ x) := rfl

end LinConv

section EofW

variable {G : Type*} [Group G]

/-- The quotient `D/V`, for subgroups `V, D` of `G` (in applications `V ≤ D`). -/
abbrev QV (V D : Subgroup G) [V.Normal] [D.Normal] : Type _ := ↥D ⧸ V.subgroupOf D


variable (V D : Subgroup G) [V.Normal] [D.Normal] [hQ : IsMulCommutative (QV V D)]
  [hmod : Module (ZMod 2) (Additive (QV V D))]

/-- The subgroup of `↥D` corresponding to a submodule `W` of `Additive (D/V)`: the preimage of
`W` under the quotient map `↥D → D/V`. -/
noncomputable def EofWD (W : Submodule (ZMod 2) (Additive (QV V D))) : Subgroup ↥D where
  carrier := {y : ↥D | Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) y) ∈ W}
  one_mem' := by
    show Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) 1) ∈ W
    rw [map_one, ofMul_one]
    exact W.zero_mem
  mul_mem' := by
    intro a b ha hb
    show Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) (a * b)) ∈ W
    rw [map_mul, ofMul_mul]
    exact W.add_mem ha hb
  inv_mem' := by
    intro a ha
    show Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) a⁻¹) ∈ W
    rw [map_inv, ofMul_inv]
    exact W.neg_mem ha

@[simp] lemma mem_EofWD (W : Submodule (ZMod 2) (Additive (QV V D))) (y : ↥D) :
    y ∈ EofWD V D W ↔ Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) y) ∈ W :=
  Iff.rfl

/-- The subgroup of `G` corresponding to a submodule `W` of `Additive (D/V)`. -/
noncomputable def EofW (W : Submodule (ZMod 2) (Additive (QV V D))) : Subgroup G :=
  (EofWD V D W).map D.subtype

lemma mem_EofW_iff (W : Submodule (ZMod 2) (Additive (QV V D))) (y : ↥D) :
    (y : G) ∈ EofW V D W ↔ Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) y) ∈ W := by
  rw [EofW, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    rwa [hzy', mem_EofWD] at hz
  · intro hy
    exact ⟨y, by rwa [mem_EofWD], rfl⟩

lemma V_le_EofW (hVD : V ≤ D) (W : Submodule (ZMod 2) (Additive (QV V D))) :
    V ≤ EofW V D W := by
  intro x hx
  rw [mem_EofW_iff V D W ⟨x, hVD hx⟩]
  have h1 : QuotientGroup.mk' (V.subgroupOf D) (⟨x, hVD hx⟩ : ↥D) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [h1, ofMul_one]
  exact W.zero_mem

lemma EofW_le_D (W : Submodule (ZMod 2) (Additive (QV V D))) : EofW V D W ≤ D := by
  intro x hx
  rw [EofW, Subgroup.mem_map] at hx
  obtain ⟨z, -, rfl⟩ := hx
  exact z.2

lemma EofW_eq_D_imp (W : Submodule (ZMod 2) (Additive (QV V D))) (h : EofW V D W = D) :
    W = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (V.subgroupOf D) (Additive.toMul m)
  have hxD : (x : G) ∈ EofW V D W := by rw [h]; exact x.2
  rw [mem_EofW_iff V D W x] at hxD
  have hm : m = Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) x) := by
    rw [hx, ofMul_toMul]
  rw [hm]
  exact hxD

lemma EofW_eq_V_imp (W : Submodule (ZMod 2) (Additive (QV V D))) (h : EofW V D W = V) :
    W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (V.subgroupOf D) (Additive.toMul m)
  have hxW : Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) x) ∈ W := by
    have hm' : Additive.ofMul (Additive.toMul m) ∈ W := by rwa [ofMul_toMul]
    rwa [← hx] at hm'
  have hxE : (x : G) ∈ EofW V D W := (mem_EofW_iff V D W x).mpr hxW
  rw [h] at hxE
  have h1 : QuotientGroup.mk' (V.subgroupOf D) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hxE
  have hm0 : m = Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) x) := by
    rw [hx, ofMul_toMul]
  rw [hm0, h1, ofMul_one]

lemma EofW_normal_of_invariant (W : Submodule (ZMod 2) (Additive (QV V D)))
    (hW : ∀ g : G, ∀ w ∈ W, linOfMulAut (conjQ V D g) w ∈ W) : (EofW V D W).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [EofW, Subgroup.mem_map] at hx ⊢
  obtain ⟨z, hz, hzx⟩ := hx
  rw [mem_EofWD] at hz
  refine ⟨MulAut.conjNormal (H := D) g z, ?_, ?_⟩
  · rw [mem_EofWD]
    have h2 : Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D)
        (MulAut.conjNormal (H := D) g z)) = linOfMulAut (conjQ V D g)
          (Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) z)) := by
      rw [linOfMulAut_apply, conjQ_mk]
    rw [h2]
    exact hW g _ hz
  · show (((MulAut.conjNormal (H := D) g) z : ↥D) : G) = g * x * g⁻¹
    rw [MulAut.conjNormal_apply]
    exact congrArg (fun t : G => g * t * g⁻¹) hzx

end EofW

end Work.Hering.HardCore
