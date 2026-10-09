import Mathlib
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective
import Submission.Work.GroupCohomology.Vanishing
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

/-- On a discrete space every function is locally constant for the locally constant predicate of
`Work.AbsoluteKummer` (which is *not* Mathlib's `IsLocallyConstant`). -/
theorem abs_isLocallyConstant_of_discrete {X : Type} [TopologicalSpace X] [DiscreteTopology X]
    {A : Type} (f : X → A) : Work.AbsoluteKummer.IsLocallyConstant f :=
  fun x => ⟨{x}, isOpen_discrete _, rfl, fun y hy => by rw [Set.mem_singleton_iff.mp hy]⟩

/-- **Vanishing of the continuous `2`-cohomology of a finite discrete group with coefficients in a
module where the group order is invertible.**  If `G` is finite and `T1` (hence discrete, so every
cochain is locally constant) and multiplication by `|G|` is a bijection of `A`, then
`H²_c(G,A) = 0`.

The explicit primitive of the abstract theory
(`Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective`) is an arbitrary function `G → A`, hence a
*continuous* `1`-cochain (`abs_isLocallyConstant_of_discrete`), which is what the comparison
`Z²_c ⊆ B²_c` of `Work.AbsoluteKummer` needs. -/
theorem subsingleton_H2_abs_of_fintype_card_smul_bijective {G : Type} [TopologicalSpace G]
    [Group G] [Fintype G] [T1Space G] {A : Type} [AddCommGroup A] [DistribMulAction G A]
    (hA : Function.Bijective (fun a : A => Fintype.card G • a)) :
    Subsingleton (Work.AbsoluteKummer.H2 G A) := by
  haveI : DiscreteTopology G := Finite.instDiscreteTopology
  have hle : Work.AbsoluteKummer.Z2 G A ≤ Work.AbsoluteKummer.B2 G A := by
    intro c hc
    rw [Work.AbsoluteKummer.mem_B2_iff]
    have hcZ : c ∈ Work.GroupCohomology.Z2 G A := (AddSubgroup.mem_inf.mp hc).1
    obtain ⟨f, hf⟩ := AddMonoidHom.mem_range.mp
      (Work.GroupCohomology.Z2_le_B2_of_card_smul_bijective (G := G) (A := A) hA hcZ)
    exact ⟨f, (Work.AbsoluteKummer.mem_C1c_iff f).mpr (abs_isLocallyConstant_of_discrete f), hf⟩
  rw [QuotientAddGroup.subsingleton_iff]
  refine le_antisymm le_top (fun x _ => ?_)
  rw [AddSubgroup.mem_comap]
  exact hle x.2

/-- **The `p ≠ 2` case of the involution input of `himg`.**  For odd `p` the coefficient `E` is a
`p`-torsion module and `⟨σ⟩` has order `2`, so `H²(⟨σ⟩, E)` is a subsingleton and the required
vanishing is *formal*: the target reduces (via `deltaH2_restriction` and the injectivity of the
restricted connecting map, whose kernel is `H¹(⟨σ⟩, homCoindFreeT) = 0`) to
`resH2_{⟨σ⟩} (e1aChainC (extDelta x)) = 0`, an element of the subsingleton `H²(⟨σ⟩, E)`. -/
theorem himgExtDeltaInput_inf_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (x : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.classesK k K) 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
          (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))) = 0 := by
  classical
  -- finiteness of the coefficient `T` and of the canonical coefficient `N.V`
  haveI hTfin : Finite T := e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  -- ### the subgroup `⟨σ⟩` is finite (and hence closed)
  haveI hUfin : Finite ↥(Subgroup.zpowers σ) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers]
    exact Nat.pos_iff_ne_zero.mp
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hσ⟩).orderOf_pos
  haveI : Fintype ↥(Subgroup.zpowers σ) := Fintype.ofFinite _
  have hUclosed : IsClosed ((Subgroup.zpowers σ : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) :=
    Set.Finite.isClosed (Set.toFinite _)
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
  -- ### … and hence on `Hom_ℤ(N.V, Ωˣ)`: transport along the canonical coefficient identification
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
  haveI hsub : Subsingleton (Work.AbsoluteKummer.H2 ↥(Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) :=
    subsingleton_H2_abs_of_fintype_card_smul_bijective
      (G := ↥(Subgroup.zpowers σ)) hbij
  -- ### assembly: the restricted connecting map is injective, and `δ ∘ resH1` is `resH2 ∘ δ`
  have hinj := deltaH2_restrictSES_e1aSES_injective' (k := k) (Ω := Ω) (K := K)
    (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (Subgroup.zpowers σ) hUclosed
  have hzero : (Work.SSGRoute.ExtChain.restrictSES
      (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (Subgroup.zpowers σ)).deltaH2
      (Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
        (Work.SSGRoute.ExtChain.e1cMap
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
          ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
              (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
            (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x)))) = 0 := by
    rw [← Work.SSGRoute.ExtChain.deltaH2_restriction
      (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)) (Subgroup.zpowers σ)
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
          (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
          (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x)))]
    exact Subsingleton.elim _ 0
  exact hinj.eq_iff.mp (by simpa using hzero)

end Work.SSGRoute.ExtChain
