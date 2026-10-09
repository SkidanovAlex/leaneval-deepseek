import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtChain.himgExtDeltaInput_inf_odd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The `p ≠ 2` vanishing of `H²(⟨σ⟩, Hom_ℤ(N.V,Ωˣ))` for an involution `σ`.**

Here `N = e1aN0 p k Ω K T E = DualMod p (E ⊗ T)` is the canonical `p`-torsion coefficient of the
E1a chain and `σ ∈ Gal(Ω/k)` satisfies `σ² = 1`, so `⟨σ⟩` is finite of order dividing `2`.

Since `p` is odd, `|⟨σ⟩|` is invertible in `ZMod p`; along the cyclotomic-dual Kummer
identification `e1aCoeffNat : E ≃+ Hom_ℤ(N.V,Ωˣ)` (`K` contains a primitive `p`-th root `ζ`, and
`T` is its cyclotomic dual) the scalar `|⟨σ⟩| • ·` therefore corresponds to the bijective scalar
`|⟨σ⟩| • ·` on the finite `ZMod p`-module `E`.  Transporting back gives the bijectivity of
`|⟨σ⟩| • ·` on the coinduced module, and
`subsingleton_H2_abs_of_fintype_card_smul_bijective` (a finite `T₁` group whose order acts
bijectively has vanishing continuous `H²`) concludes. -/
theorem subsingleton_H2_zpowers_homCoind_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) :
    Subsingleton (Work.AbsoluteKummer.H2 ↥(Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) := by
  classical
  -- finiteness of the coefficient `T`
  haveI hTfin : Finite T := e1aFiniteT p k Ω K ζ T hT
  -- ### the subgroup `⟨σ⟩` is finite (and hence discrete)
  haveI hUfin : Finite ↥(Subgroup.zpowers σ) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers]
    exact Nat.pos_iff_ne_zero.mp
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hσ⟩).orderOf_pos
  haveI : Fintype ↥(Subgroup.zpowers σ) := Fintype.ofFinite _
  -- ### `|⟨σ⟩| ∣ 2` is invertible in `ZMod p`
  have hcard_eq : Fintype.card ↥(Subgroup.zpowers σ) = orderOf σ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
  have hcard_dvd : Fintype.card ↥(Subgroup.zpowers σ) ∣ 2 := by
    rw [hcard_eq]
    exact orderOf_dvd_iff_pow_eq_one.mpr hσ
  have hcard_unit : IsUnit ((Fintype.card ↥(Subgroup.zpowers σ) : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.symm (((Fact.out : Nat.Prime p).coprime_iff_not_dvd).mpr ?_)
    intro hd
    exact hp (le_antisymm (Nat.le_of_dvd (by norm_num) (dvd_trans hd hcard_dvd))
      (Fact.out : Nat.Prime p).two_le)
  -- ### `|⟨σ⟩| • ·` is bijective on `E`
  have hbijE : Function.Bijective (fun e : E => Fintype.card ↥(Subgroup.zpowers σ) • e) := by
    obtain ⟨u, hu⟩ := hcard_unit
    have h1 : (↑u : ZMod p) * (↑u⁻¹ : ZMod p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (↑u⁻¹ : ZMod p) * (↑u : ZMod p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨fun a b h => ?_, fun b => ⟨(↑u⁻¹ : ZMod p) • b, ?_⟩⟩
    · have h' : (↑u : ZMod p) • a = (↑u : ZMod p) • b := by
        rw [hu, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        exact h
      have h'' := congrArg (fun z => (↑u⁻¹ : ZMod p) • z) h'
      rw [smul_smul, smul_smul, h2, one_smul, one_smul] at h''
      exact h''
    · show Fintype.card ↥(Subgroup.zpowers σ) • ((↑u⁻¹ : ZMod p) • b) = b
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) (Fintype.card ↥(Subgroup.zpowers σ)), ← hu,
        smul_smul, h1, one_smul]
  -- ### … and hence on `Hom_ℤ(N.V, Ωˣ)`, by transport along the cyclotomic-dual Kummer
  -- identification `e1aCoeffNat : E ≃+ Hom_ℤ(N.V,Ωˣ)`
  have hbij : Function.Bijective (fun m : Work.SSGRoute.homCoind k Ω K
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) =>
      Fintype.card ↥(Subgroup.zpowers σ) • m) := by
    refine ⟨fun a b h => ?_, fun b => ?_⟩
    · have h' : Fintype.card ↥(Subgroup.zpowers σ) •
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm a
        = Fintype.card ↥(Subgroup.zpowers σ) •
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm b := by
        have hh := congrArg (fun z =>
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm z) h
        rw [map_nsmul, map_nsmul] at hh
        exact hh
      exact (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm.injective
        (hbijE.injective h')
    · obtain ⟨e, he⟩ := hbijE.surjective
        ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm b)
      have he' : Fintype.card ↥(Subgroup.zpowers σ) • e
          = (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm b := he
      refine ⟨(Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E) e, ?_⟩
      show Fintype.card ↥(Subgroup.zpowers σ) •
        (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E) e = b
      have hkey : Fintype.card ↥(Subgroup.zpowers σ) •
          (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E) e
          = (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E)
            (Fintype.card ↥(Subgroup.zpowers σ) • e) :=
        (map_nsmul _ _ _).symm
      rw [hkey, he', AddEquiv.apply_symm_apply]
  -- ### `H²(⟨σ⟩, Hom_ℤ(N.V,Ωˣ))` is a subsingleton
  exact subsingleton_H2_abs_of_fintype_card_smul_bijective
    (G := ↥(Subgroup.zpowers σ)) hbij

end Work.SSGRoute.ExtChain
