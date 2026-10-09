import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.pt_char_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corestriction transfer on `Ext` (`E6Ω` infrastructure)

Two facts about `Work.SSGRoute.extCor` (the corestriction on derived `Ext` of
`Submission/Work/SSGRoute/ext_corestriction.lean`) that the Sylow descent `E6Ω` needs and that the
existential form `Work.SSGRoute.ext_corestriction` does not provide:

* `Work.SSGRoute.CorTransfer.extCor_extRes_eq_index` — the **identity** `cor (res x) = [G : S] • x`
  for the *specific* map `extCor` (the theorem `ext_corestriction` only asserts that *some* family
  of additive maps has this property; its proof is `extCor`, but the identity is not exported);
* `Work.SSGRoute.CorTransfer.extCor_injective_of_fundamental` — **`extCor` is injective** as soon as
  the class formation provides (a) an element `α` of `Hⁿ(G, A)` of order `|G|` and (b) the
  cardinality `|Hⁿ(S, res A)| = |S|`.

The second is the input that `E6Ω`'s transfer step needs: for the class formation
`A = classesK k L` both hypotheses hold (`H²(·, C_L)` is cyclic of order the degree, with a
generator of full order), and then a `p`-torsion value over `Gal(L/k')` vanishing after
corestriction to `Gal(L/k)` must itself vanish.  Unlike the "dual" identity
`res ∘ cor = [G : S]` — which is *false* for arbitrary coefficients (double-coset formula) — this
needs no coprimality: corestriction on the class formation is injective outright.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace CorTransfer

section Identity

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G)
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]

/-- **The corestriction identity for `extCor`.**  `cor (res x) = [G : S] • x`, for the explicit
corestriction `Work.SSGRoute.extCor` (the identity asserted existentially by
`Work.SSGRoute.ext_corestriction`, with `cor` = `extCor`). -/
theorem extCor_extRes_eq_index (M A : Rep Coeff G) (n : ℕ) (x : Abelian.Ext M A n) :
    extCor S M A n (extRes S.subtype x) = S.index • x := by
  have hnat : (x.mapExactFunctor (Rep.resFunctor S.subtype ⋙
        Rep.coindFunctor Coeff S.subtype)).comp
        (Abelian.Ext.mk₀ (coindTrace S A)) (add_zero n)
      = (Abelian.Ext.mk₀ (coindTrace S M)).comp x (zero_add n) :=
    ext_mapExactFunctor_naturality_aux (C := Rep Coeff G)
      (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor Coeff S.subtype) (coindTraceNat S) n M A x
  have hlast : (S.index • Abelian.Ext.mk₀ (𝟙 M)).comp x (zero_add n) = S.index • x := by
    rw [nsmul_comp_aux, Abelian.Ext.mk₀_id_comp x]
  have hmk : (Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
        (Abelian.Ext.mk₀ (coindTrace S M)) (add_zero 0) = S.index • Abelian.Ext.mk₀ (𝟙 M) := by
    rw [Abelian.Ext.mk₀_comp_mk₀, unit_comp_coindTrace S M, mk₀_nsmul_aux]
  have hcomp := ext_mapExactFunctor_comp_functor_aux (C := Rep Coeff G) (D := Rep Coeff ↥S)
    (E := Rep Coeff G) (Rep.resFunctor S.subtype) (Rep.coindFunctor Coeff S.subtype) n M A x
  rw [extCor_apply]
  change ((Abelian.Ext.mk₀ ((Rep.resCoindAdjunction Coeff S.subtype).unit.app M)).comp
      ((x.mapExactFunctor (Rep.resFunctor S.subtype)).mapExactFunctor
        (Rep.coindFunctor Coeff S.subtype)) (zero_add n)).comp
      (Abelian.Ext.mk₀ (coindTrace S A)) (add_zero n) = S.index • x
  rw [hcomp, Abelian.Ext.comp_assoc_of_third_deg_zero, hnat,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, hmk, hlast]

end Identity

section Injective

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G)
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]

/-- **Corestriction is injective when the class formation supplies a generator and the cardinality
of the smaller `Hⁿ`.**  If `α ∈ Hⁿ(G, A)` has order `|G|` (a "fundamental class", so that
`Hⁿ(G, A) = ⟨α⟩` is cyclic of order `|G|`) and `|Hⁿ(S, res A)| = |S|`, then
`extCor S : Hⁿ(S, res A) → Hⁿ(G, A)` is injective.

Indeed `β := res α` satisfies `cor β = [G : S] • α` of order `|G| / gcd(|G|, [G:S]) = |S|`, so
`addOrderOf β = |S| = |Hⁿ(S, res A)|` and `β` generates; then `cor (m • β) = m [G:S] α ≠ 0` unless
`|S| ∣ m`. -/
theorem extCor_injective_of_fundamental (A : Rep Coeff G) (n : ℕ)
    (hα : ∃ α : extH A n, addOrderOf α = Nat.card G)
    (hcard : Nat.card (Abelian.Ext (Rep.res S.subtype (unitRep G)) (Rep.res S.subtype A) n)
      = Nat.card ↥S) :
    Function.Injective (extCor S (unitRep G) A n) := by
  obtain ⟨α, hα⟩ := hα
  have hcardS : Nat.card ↥S ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcarddom : Nat.card (Abelian.Ext (Rep.res S.subtype (unitRep G))
      (Rep.res S.subtype A) n) ≠ 0 := by
    rw [hcard]; exact hcardS
  haveI : Finite (Abelian.Ext (Rep.res S.subtype (unitRep G)) (Rep.res S.subtype A) n) :=
    (Nat.card_ne_zero.mp hcarddom).2
  have hindex : S.index ≠ 0 := by
    intro h0
    have h := Subgroup.card_mul_index S
    rw [h0, mul_zero] at h
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩ h.symm
  have hord : addOrderOf (S.index • α) = Nat.card ↥S := by
    rw [addOrderOf_nsmul' α hindex, hα, ← Subgroup.card_mul_index S,
      Nat.gcd_eq_right (dvd_mul_left S.index (Nat.card ↥S)),
      Nat.mul_div_cancel (Nat.card ↥S) (Nat.pos_of_ne_zero hindex)]
  have hcor : extCor S (unitRep G) A n (extRes S.subtype α) = S.index • α :=
    extCor_extRes_eq_index S (unitRep G) A n α
  have hcor' : extCor S (unitRep G) A n (extRes S.subtype α) = (S.index : ℤ) • α := by
    rw [hcor, Nat.cast_smul_eq_nsmul]
  have hordβ : addOrderOf (extRes S.subtype α) = Nat.card ↥S := by
    have h2 : addOrderOf (extCor S (unitRep G) A n (extRes S.subtype α)) ∣
        addOrderOf (extRes S.subtype α) := addOrderOf_map_dvd _ _
    rw [hcor, hord] at h2
    have h4 : addOrderOf (extRes S.subtype α) ≤ Nat.card ↥S := by
      rw [← hcard, ← Nat.card_zmultiples (extRes S.subtype α)]
      exact Nat.card_le_card_of_injective (AddSubgroup.subtype _) (AddSubgroup.subtype_injective _)
    exact le_antisymm h4 (Nat.le_of_dvd (addOrderOf_pos _) h2)
  rw [injective_iff_map_eq_zero]
  intro v hv
  have htop : AddSubgroup.zmultiples (extRes S.subtype α) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hordβ, hcard])
  have hvz : v ∈ AddSubgroup.zmultiples (extRes S.subtype α) := by
    rw [htop]; exact AddSubgroup.mem_top v
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hvz
  have h5 : (m * (S.index : ℤ)) • α = 0 := by
    have hv2 : m • ((S.index : ℤ) • α) = 0 := by
      rw [← hm, map_zsmul, hcor'] at hv
      exact hv
    rwa [← mul_zsmul] at hv2
  have h6 : ((addOrderOf α : ℕ) : ℤ) ∣ m * (S.index : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr h5
  rw [hα, ← Subgroup.card_mul_index S] at h6
  push_cast at h6
  have h7 : ((Nat.card ↥S : ℕ) : ℤ) ∣ m :=
    (mul_dvd_mul_iff_right (by exact_mod_cast hindex)).mp h6
  have h8 : m • (extRes S.subtype α) = 0 := by
    rw [← hordβ] at h7
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mp h7
  rw [← hm, h8]

end Injective

end CorTransfer

/-! ## The class formation in the `Ext`/`Coeff` spelling

`Work.SSGRoute.extH_classesK_two_addEquiv` (`Submission/Work/SSGRoute/pt_char_pTorsion.lean`) is the
additive isomorphism between `H²(Gal(L/K), C_L)` in the `Ext`/`Coeff` spelling used by the
Poitou–Tate core and in the `ℤ`/group-cohomology spelling used by `NK`; it is built from the `E0b`
bridge and the coefficient-ring transfer.  Composing it with the class formation
(`NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement
NK.CFTLib.fundamentalClassElement`) transports the fundamental class to the `Ext` world. -/

section ClassFormation

/-- **The fundamental class in the `Ext`/`Coeff` spelling** (hypothesis (a) of
`Work.SSGRoute.CorTransfer.extCor_injective_of_fundamental` for the class formation): for finite
Galois number fields `L/K` there is `α ∈ H²(Gal(L/K), C_L) = extH (classesK K L) 2` of order
`[L : K]`. -/
theorem extH_classesK_two_fundamental (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ α : extH (classesK K L) 2, addOrderOf α = Nat.card (L ≃ₐ[K] L) := by
  obtain ⟨e⟩ := Work.SSGRoute.extH_classesK_two_addEquiv K L
  obtain ⟨α, hα⟩ := (NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement
    NK.CFTLib.fundamentalClassElement).fundamentalClass (K := K) (L := L)
  exact ⟨e.symm α, (AddEquiv.addOrderOf_eq e.symm α).trans hα⟩

end ClassFormation
end Work.SSGRoute
