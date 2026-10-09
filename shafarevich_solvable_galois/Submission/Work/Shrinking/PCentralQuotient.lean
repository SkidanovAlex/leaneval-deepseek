/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The subquotients of the descending `p`-central series as `𝔽_p[G]`-modules

The quotients `P_i/P_{i+1}` of the descending `p`-central series of a `p`-group are
elementary abelian `p`-groups (Schmidt–Wingberg, Section 2, after Definition 3), hence
`𝔽_p`-vector spaces; the modules of Proposition 5 of the paper are these quotients.  If a
group `G` acts on `P` by automorphisms, the action descends to each quotient, so that the
quotients are `𝔽_p[G]`-modules.

## Main results

* `Work.Shrinking.isMulCommutative_pCentralQuotient` : `P_n/P_{n+1}` is commutative.
* `Work.Shrinking.pow_eq_one_pCentralQuotient` : every element of `P_n/P_{n+1}` has order
  dividing `p`.
* `Work.Shrinking.instModuleZModPCentralQuotient` : the induced `𝔽_p`-vector space structure
  on `Additive (P_n/P_{n+1})` (`AddCommGroup.zmodModule`).
* `Work.Shrinking.quotActionHom`, `Work.Shrinking.instMulDistribMulActionPCentralQuotient` :
  the induced action of `G` on `P_n/P_{n+1}`.
* `Work.Shrinking.instDistribMulActionAdditivePCentralQuotient`,
  `Work.Shrinking.instSMulCommClassPCentralQuotient` : the resulting `𝔽_p[G]`-module
  structure: the action of `G` is by `𝔽_p`-linear maps.

Note on the `Additive` wrapper: `Module (ZMod p) M` requires an *additive* commutative group,
so the `𝔽_p`-vector space of a multiplicative abelian quotient `Q` is `Additive Q`.  The
`AddCommGroup (Additive Q)` instance requires `CommGroup Q`, which is obtained from
`IsMulCommutative Q` through the scoped instance `open scoped IsMulCommutative`; this file
provides dedicated (non-scoped) instances for the series quotients so that a caller does not
have to open the scope.
-/

import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.pCentralSeries_normal
import Submission.Work.Shrinking.pCentralSeries_characteristic
import Submission.Work.Shrinking.pCentralSeries_le_succ
import Submission.Work.Shrinking.pow_mem_pCentralSeries_succ
import Submission.Work.Shrinking.commutator_le_pCentralSeries_succ
import Submission.Work.Shrinking.isMulCommutative_subquotient
import Submission.Work.Shrinking.pow_eq_one_subquotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

universe u

/-! ## Descending an action by automorphisms to a subquotient

Let `G` act on `P` by automorphisms (a `MulDistribMulAction`).  If `H, K ≤ P` are invariant
under the action, then `G` acts on `H` (restriction) and on `H ⧸ K.subgroupOf H`. -/

section SubquotientAction

variable {G P : Type*} [Group G] [Group P] [MulDistribMulAction G P]

/-- The image of `x ∈ H` under the action of `g`, which lies in `H` because `H` is invariant. -/
lemma mem_smul_mem (H : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H) {x : P} (hx : x ∈ H) :
    MulDistribMulAction.toMulAut G P g x ∈ H := by
  rw [← hH]
  exact Subgroup.mem_map_of_mem _ hx

/-- The inverse image of `x ∈ H` under the action of `g`, which lies in `H` when `H` is
invariant. -/
lemma mem_inv_smul_mem (H : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H) {x : P} (hx : x ∈ H) :
    (MulDistribMulAction.toMulAut G P g)⁻¹ x ∈ H := by
  have h := Subgroup.mem_map_iff_mem (f := (MulDistribMulAction.toMulAut G P g).toMonoidHom)
    (MulDistribMulAction.toMulAut G P g).injective (K := H)
    (x := (MulDistribMulAction.toMulAut G P g)⁻¹ x)
  rw [hH] at h
  exact h.mp (by simpa using hx)

/-- The automorphism of an invariant subgroup `H` induced by `g`. -/
def subAut (H : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H) : H ≃* H where
  toFun x := ⟨MulDistribMulAction.toMulAut G P g x, mem_smul_mem H g hH x.2⟩
  invFun x := ⟨(MulDistribMulAction.toMulAut G P g)⁻¹ x, mem_inv_smul_mem H g hH x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[simp]
lemma subAut_coe (H : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H) (x : H) :
    ((subAut H g hH x : H) : P) = MulDistribMulAction.toMulAut G P g x := rfl

@[simp]
lemma subAut_symm_coe (H : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H) (x : H) :
    (((subAut H g hH).symm x : H) : P) = (MulDistribMulAction.toMulAut G P g)⁻¹ x := rfl

lemma subAut_trans (H : Subgroup P) (g h : G)
    (hg : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hh : H.map (MulDistribMulAction.toMulAut G P h).toMonoidHom = H)
    (hgh : H.map (MulDistribMulAction.toMulAut G P (g * h)).toMonoidHom = H) (x : H) :
    subAut H (g * h) hgh x = subAut H g hg (subAut H h hh x) := by
  refine Subtype.ext ?_
  rw [subAut_coe, subAut_coe, subAut_coe, map_mul]
  rfl

lemma subAut_one (H : Subgroup P) (h1 : H.map (MulDistribMulAction.toMulAut G P 1).toMonoidHom = H)
    (x : H) : subAut H 1 h1 x = x := by
  refine Subtype.ext ?_
  rw [subAut_coe, map_one]
  rfl

/-- An invariant subgroup of `H` remains invariant under the restricted action. -/
lemma map_subgroupOf_subAut (H K : Subgroup P) (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hK : K.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = K) :
    (K.subgroupOf H).map (subAut H g hH).toMonoidHom = K.subgroupOf H := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change ((subAut H g hH) x : P) ∈ K
    rw [subAut_coe]
    exact mem_smul_mem K g hK hx
  · intro hy
    refine Subgroup.mem_map.mpr ⟨(subAut H g hH).symm y, ?_, (subAut H g hH).apply_symm_apply y⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [subAut_symm_coe]
    exact mem_inv_smul_mem K g hK hy

/-- The automorphism of the subquotient `H/K` induced by `g`. -/
def quotAut (H K : Subgroup P) [K.Normal] (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hK : K.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = K) :
    (H ⧸ K.subgroupOf H) ≃* (H ⧸ K.subgroupOf H) :=
  QuotientGroup.congr (K.subgroupOf H) (K.subgroupOf H) (subAut H g hH)
    (map_subgroupOf_subAut H K g hH hK)

@[simp]
lemma quotAut_mk (H K : Subgroup P) [K.Normal] (g : G)
    (hH : H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hK : K.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = K) (x : H) :
    quotAut H K g hH hK (QuotientGroup.mk' (K.subgroupOf H) x)
      = QuotientGroup.mk' (K.subgroupOf H) (subAut H g hH x) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- The action of `G` on the subquotient `H/K` induced by the action on `P`. -/
def quotActionHom (H K : Subgroup P) [K.Normal]
    (hH : ∀ g : G, H.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = H)
    (hK : ∀ g : G, K.map (MulDistribMulAction.toMulAut G P g).toMonoidHom = K) :
    G →* MulAut (H ⧸ K.subgroupOf H) where
  toFun g := quotAut H K g (hH g) (hK g)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) x
    show QuotientGroup.mk' (K.subgroupOf H) (subAut H 1 (hH 1) y)
      = (1 : MulAut (H ⧸ K.subgroupOf H)) (QuotientGroup.mk' (K.subgroupOf H) y)
    rw [subAut_one]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) x
    show QuotientGroup.mk' (K.subgroupOf H) (subAut H (g * h) (hH (g * h)) y)
      = quotAut H K g (hH g) (hK g)
          (quotAut H K h (hH h) (hK h) (QuotientGroup.mk' (K.subgroupOf H) y))
    rw [quotAut_mk]
    exact congrArg (QuotientGroup.mk' (K.subgroupOf H))
      (subAut_trans H g h (hH g) (hH h) (hH (g * h)) y)

end SubquotientAction

/-! ## The subquotients of the `p`-central series -/

section Series

variable {P : Type*} [Group P]

/-- Every term of the descending `p`-central series is a normal subgroup (instance form). -/
instance instNormalPCentralSeries (p : ℕ) (n : ℕ) : (pCentralSeries p P n).Normal :=
  pCentralSeries_normal p P n

/-- Every term of the descending `p`-central series is characteristic (instance form). -/
instance instCharacteristicPCentralSeries (p : ℕ) (n : ℕ) :
    (pCentralSeries p P n).Characteristic :=
  pCentralSeries_characteristic p P n

/-- Every term of the descending `p`-central series is invariant under every automorphism
of `P`. -/
theorem map_pCentralSeries_eq (p : ℕ) (φ : P ≃* P) (n : ℕ) :
    (pCentralSeries p P n).map φ.toMonoidHom = pCentralSeries p P n :=
  Subgroup.characteristic_iff_map_eq.mp (pCentralSeries_characteristic p P n) φ

/-- The quotient `P_n/P_{n+1}` of the descending `p`-central series (the modules of
Proposition 5 of Schmidt–Wingberg). -/
abbrev pCentralQuotient (p : ℕ) (P : Type*) [Group P] (n : ℕ) : Type _ :=
  pCentralSeries p P n ⧸ (pCentralSeries p P (n + 1)).subgroupOf (pCentralSeries p P n)

/-- The quotients of the descending `p`-central series are commutative. -/
theorem isMulCommutative_pCentralQuotient (p : ℕ) (n : ℕ) :
    IsMulCommutative (pCentralQuotient p P n) :=
  isMulCommutative_subquotient (commutator_le_pCentralSeries_succ p P n).2

/-- Every element of `P_n/P_{n+1}` has order dividing `p`. -/
theorem pow_eq_one_pCentralQuotient (p : ℕ) (n : ℕ) (x : pCentralQuotient p P n) :
    x ^ p = 1 :=
  pow_eq_one_subquotient (p := p) (fun _ hx => pow_mem_pCentralSeries_succ p P hx) x

instance instIsMulCommutativePCentralQuotient (p : ℕ) (n : ℕ) :
    IsMulCommutative (pCentralQuotient p P n) :=
  isMulCommutative_pCentralQuotient p n

open scoped IsMulCommutative in
/-- The `𝔽_p`-vector space structure on the quotient `P_n/P_{n+1}`, written additively as
`Additive (P_n/P_{n+1})` (the quotient is a multiplicative group). -/
noncomputable instance instAddCommGroupPCentralQuotient (p : ℕ) (n : ℕ) :
    AddCommGroup (Additive (pCentralQuotient p P n)) :=
  inferInstanceAs (AddCommGroup (Additive (pCentralQuotient p P n)))

/-- The `𝔽_p`-module structure on the quotient `P_n/P_{n+1}` (exponent `p`). -/
noncomputable instance instModuleZModPCentralQuotient (p : ℕ) (n : ℕ) :
    Module (ZMod p) (Additive (pCentralQuotient p P n)) :=
  AddCommGroup.zmodModule (fun x => by
    refine (Additive.toMul).injective ?_
    rw [toMul_nsmul, toMul_zero]
    exact pow_eq_one_pCentralQuotient p n (Additive.toMul x))

end Series

/-! ## The descended `G`-action -/

section SeriesAction

variable {G P : Type*} [Group G] [Group P] [MulDistribMulAction G P]

/-- The `G`-action on `P_n/P_{n+1}` induced by an action of `G` on `P` by automorphisms. -/
noncomputable def pCentralQuotientActionHom (p : ℕ) (n : ℕ) :
    G →* MulAut (pCentralQuotient p P n) :=
  quotActionHom (pCentralSeries p P n) (pCentralSeries p P (n + 1))
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) n)
    (fun g => map_pCentralSeries_eq p (MulDistribMulAction.toMulAut G P g) (n + 1))

/-- The `G`-action on `P_n/P_{n+1}` by group automorphisms, induced by the action on `P`. -/
noncomputable instance instMulDistribMulActionPCentralQuotient (p : ℕ) (n : ℕ) :
    MulDistribMulAction G (pCentralQuotient p P n) where
  smul g x := pCentralQuotientActionHom (G := G) p n g x
  one_smul x := by
    show pCentralQuotientActionHom (G := G) p n 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    show pCentralQuotientActionHom (G := G) p n (g * h) x
      = pCentralQuotientActionHom (G := G) p n g (pCentralQuotientActionHom (G := G) p n h x)
    rw [map_mul]
    rfl
  smul_mul g x y := map_mul (pCentralQuotientActionHom (G := G) p n g) x y
  smul_one g := map_one (pCentralQuotientActionHom (G := G) p n g)

/-- The corresponding action on the additive group `Additive (P_n/P_{n+1})`. -/
noncomputable instance instDistribMulActionAdditivePCentralQuotient (p : ℕ) (n : ℕ) :
    DistribMulAction G (Additive (pCentralQuotient p P n)) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := by
    show Additive.ofMul ((1 : G) • Additive.toMul x) = x
    rw [one_smul, ofMul_toMul]
  mul_smul g h x := by
    show Additive.ofMul ((g * h) • Additive.toMul x)
      = Additive.ofMul (g • Additive.toMul (Additive.ofMul (h • Additive.toMul x)))
    rw [mul_smul, toMul_ofMul]
  smul_zero g := by
    show Additive.ofMul (g • Additive.toMul (0 : Additive (pCentralQuotient p P n))) = 0
    rw [toMul_zero, smul_one, ofMul_one]
  smul_add g x y := by
    show Additive.ofMul (g • Additive.toMul (x + y))
      = Additive.ofMul (g • Additive.toMul x) + Additive.ofMul (g • Additive.toMul y)
    rw [toMul_add, MulDistribMulAction.smul_mul, ofMul_mul]

/-- In an additive commutative group with a distributive action of `G`,
`g • (k • x) = k • (g • x)`: the action of `G` is compatible with the `ℕ`-scalar action. -/
lemma smul_nsmul_of_distribMulAction {G A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (g : G) (k : ℕ) (x : A) : g • (k • x) = k • (g • x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]

/-- The descended action of `G` on `P_n/P_{n+1}` is by `𝔽_p`-linear maps: the quotient is an
`𝔽_p[G]`-module. -/
instance instSMulCommClassPCentralQuotient (p : ℕ) [NeZero p] (n : ℕ) :
    SMulCommClass G (ZMod p) (Additive (pCentralQuotient p P n)) where
  smul_comm g c x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    conv_rhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact smul_nsmul_of_distribMulAction g c.val x

/-- The quotient `P_n/P_{n+1}`, with the descended `G`-action, is an `𝔽_p[G]`-module. -/
theorem isFpGModule_pCentralQuotient (p : ℕ) [NeZero p] (n : ℕ) :
    IsFpGModule p G (Additive (pCentralQuotient p P n)) :=
  instSMulCommClassPCentralQuotient (G := G) p n

end SeriesAction

end Work.Shrinking
