import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicallyTrivial

open CategoryTheory

section Helpers

attribute [local instance 10000] TensorProduct.instModule LinearMap.module

theorem zmod_linearEquiv_of_card_prime {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (hcard : Nat.card V = p) :
    Nonempty (V ≃ₗ[ZMod p] ZMod p) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : p ≠ 0 := by omega
  have hfin : Finite V := (Nat.card_ne_zero.mp (by rw [hcard]; omega)).2
  haveI : Fintype V := Fintype.ofFinite V
  have hcard' : Fintype.card V = p := by rw [← Nat.card_eq_fintype_card, hcard]
  have hnt : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcard']; omega
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ZMod p) V v) ?_).symm⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by rw [ZMod.card, hcard']⟩
  intro a b hab
  rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply] at hab
  by_contra hne
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
  have h2 : ((a - b)⁻¹ * (a - b)) • v = 0 := by rw [mul_smul, h, smul_zero]
  rw [inv_mul_cancel₀ hne', one_smul] at h2
  exact hv h2

theorem smul_span_singleton_top_eq_bot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : R} (h : ∀ m : M, r • m = 0) :
    Ideal.span {r} • (⊤ : Submodule R M) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Submodule.smul_eq_map₂]
  refine Submodule.map₂_le.mpr ?_
  intro m hm n hn
  simp only [Submodule.mem_bot]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  rw [ha, LinearMap.lsmul_apply, mul_smul]
  exact h _

noncomputable def tensorQuotSpanEquiv {p : ℕ} {W : Type} [AddCommGroup W] [Module ℤ W]
    (hW : ∀ w : W, p • w = 0) :
    (TensorProduct ℤ (ℤ ⧸ Ideal.span {(p:ℤ)}) W) ≃ₗ[ℤ] W :=
  (TensorProduct.quotTensorEquivQuotSMul W (Ideal.span {(p:ℤ)})).trans
    ((Ideal.span {(p:ℤ)} • (⊤ : Submodule ℤ W)).quotEquivOfEqBot
      (smul_span_singleton_top_eq_bot (r := (p:ℤ)) (by
        intro w; rw [Nat.cast_smul_eq_nsmul]; exact hW w)))

theorem tensorQuotSpanEquiv_mk_tmul {p : ℕ} {W : Type} [AddCommGroup W] [Module ℤ W]
    (hW : ∀ w : W, p • w = 0) (r : ℤ) (w : W) :
    tensorQuotSpanEquiv hW (Ideal.Quotient.mk (Ideal.span {(p:ℤ)}) r ⊗ₜ[ℤ] w) = (LinearMap.lsmul ℤ W r) w := by
  unfold tensorQuotSpanEquiv
  rw [LinearEquiv.trans_apply, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    Submodule.quotEquivOfEqBot_apply_mk]
  rfl

noncomputable def zmodLinearEquivQuotSpan (p : ℕ) :
    ZMod p ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
  ((Int.quotientSpanNatEquivZMod p).symm).toAddEquiv.toLinearEquiv (by
    intro c x
    show (Int.quotientSpanNatEquivZMod p).symm (c • x) = c • (Int.quotientSpanNatEquivZMod p).symm x
    rw [zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast])

noncomputable def zmodToIntLinearEquiv {p : ℕ} {M N : Type} [AddCommGroup M]
    [Module ℤ M] [Module (ZMod p) M] [AddCommGroup N] [Module ℤ N] [Module (ZMod p) N]
    (e : M ≃ₗ[ZMod p] N) : M ≃ₗ[ℤ] N :=
  e.toAddEquiv.toLinearEquiv (fun c x => by
    show e.toAddEquiv ((LinearMap.lsmul ℤ M c) x) = (LinearMap.lsmul ℤ N c) (e.toAddEquiv x)
    have hx : (LinearMap.lsmul ℤ M c) x = (c • 1 : ZMod p) • x := by
      rw [LinearMap.lsmul_apply, IsScalarTower.smul_assoc, one_smul]
      first
        | rfl
        | exact int_smul_eq_zsmul _ c x
        | exact (int_smul_eq_zsmul _ c x).symm
    have hy : (LinearMap.lsmul ℤ N c) (e.toAddEquiv x) = (c • 1 : ZMod p) • e.toAddEquiv x := by
      rw [LinearMap.lsmul_apply, IsScalarTower.smul_assoc, one_smul]
      first
        | rfl
        | exact int_smul_eq_zsmul _ c (e.toAddEquiv x)
        | exact (int_smul_eq_zsmul _ c (e.toAddEquiv x)).symm
    rw [hx, hy]
    first
      | exact map_smul e (c • 1) x
      | exact (map_smul e (c • 1) x).trans rfl)

end Helpers


theorem tensor_iso_of_isPTorsion_trivial {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (T A : Rep.{0, 0, 0} ℤ G) (hTp : ∀ t : T.V, p • t = 0) (hAp : ∀ a : A.V, p • a = 0)
    (hTtriv : ∀ (g : G) (t : T.V), T.ρ g t = t) (hTcard : Nat.card T.V = p) :
    Nonempty (CategoryTheory.MonoidalCategoryStruct.tensorObj T A ≅ A) := by
  classical
  letI : Module (ZMod p) T.V := AddCommGroup.zmodModule hTp
  letI : Module ℤ T.V := T.hV2
  letI : Module ℤ A.V := A.hV2
  letI : Module ℤ (TensorProduct ℤ (ℤ ⧸ Ideal.span {(p:ℤ)}) A.V) := TensorProduct.instModule
  letI : Module ℤ (TensorProduct ℤ T.V A.V) := TensorProduct.instModule
  obtain ⟨e⟩ := zmod_linearEquiv_of_card_prime (V := T.V) hTcard
  let e' : T.V ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(p:ℤ)}) :=
    (zmodToIntLinearEquiv e).trans (zmodLinearEquivQuotSpan p)
  let Ψ : (TensorProduct ℤ T.V A.V) ≃ₗ[ℤ] A.V :=
    (TensorProduct.congr e' (LinearEquiv.refl ℤ A.V)).trans (tensorQuotSpanEquiv hAp)
  refine ⟨Rep.mkIso (Representation.Equiv.mk Ψ ?_)⟩
  intro g
  refine TensorProduct.ext' (fun v w => ?_)
  simp only [Ψ, LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    hTtriv g v, LinearEquiv.coe_trans, Function.comp_apply]
  change tensorQuotSpanEquiv hAp (e' v ⊗ₜ[ℤ] (A.ρ g) w) = (A.ρ g) (tensorQuotSpanEquiv hAp (e' v ⊗ₜ[ℤ] w))
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e' v)
  rw [← hr]
  simp only [tensorQuotSpanEquiv_mk_tmul, LinearMap.lsmul_apply, LinearMap.map_smul]

end Work.CohomologicallyTrivial
