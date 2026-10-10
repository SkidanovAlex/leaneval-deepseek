import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.AcOdd
import Submission.Work.SSGRoute.ArchDictionary.ac_addEquiv_H1
import Submission.Work.SSGRoute.ArchDictionary.archimedeanLocalExt1Subsingleton_of_ne_bot
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PT.gcH1Transfer_exists
import Submission.Work.SSGRoute.PTdualControl.archimedeanLambda_injective_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local dictionary in degree one

For a nonsplit infinite place `w` (`D_w ≠ ⊥`) of a finite Galois number field `K/k`, an involution
`c` of `Gal(Ω/k)` with `D_w = ⟨res c⟩` (the "complex conjugation" linked to `w`), and the
coefficient module `E' = DualMod p (E ⊗ T)` (`T` the cyclotomic dual of `μ_p`), the local
`Ext¹_{D_w}(E'|, K_wˣ)` is the group `H¹(⟨c⟩,E) = Ac` of the involution acting on `E`.

* `p = 2`: `D_w ≅ ⟨c⟩ ≅ ℤ/2` and `K_w = ℂ` has *divisible* units, so the divisible-coefficient
  dictionary `ext_one_iso_divisible_cohomology` together with the degree-one internal-`Hom`
  identification `ArchLocPrep.ext_one_homRep_iso_H1` computes the `Ext¹` as
  `H¹(D_w, Hom_ℤ(E'|, ℂˣ)) ≅ H¹(D_w, E)`, and `gcH1Transfer_exists` (along `D_w ≅ ⟨c⟩`) and
  `ac_addEquiv_H1` finish the identification with `Ac`.
* `p ≠ 2`: both sides are trivial — `ac_subsingleton_of_odd` (every cocycle on an involution is a
  coboundary when `2` is invertible) and
  `archimedeanLocalExt1Subsingleton_of_ne_bot` (the odd-primary archimedean local `Ext¹` vanishes).
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

theorem archLocDictionaryEquiv (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    Nonempty (CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 ≃+
      Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c) := by
  classical
  -- `w` is the infinite place cut out by `φ`
  subst hw
  set w₀ : NumberField.InfinitePlace ↥K :=
    NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)) with hw₀
  by_cases hp2 : p = 2
  · -- ## The case `p = 2`
    subst hp2
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    -- the action of the cyclic subgroup `⟨c⟩` on `E` (through `res k K`)
    letI instZp : DistribMulAction ↥(Subgroup.zpowers c) E :=
      @Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c)
    -- at `p = 2` the cyclotomic dual is the trivial module, and the coefficient identification
    -- `Hom_ℤ(E'|, K_wˣ) ≅ E` is `coeffEquiv_p2`
    have hTtriv : ∀ (τ : ↥K ≃ₐ[k] ↥K) (t : T), τ • t = t :=
      SSGRoute.PTdualControl.T_trivial_p2 k Ω K ζ hζ T hT
    obtain ⟨Ψ, hΨ⟩ := SSGRoute.PTdualControl.coeffEquiv_p2 k ↥K E T hTtriv hT.1 w₀
    -- the decomposition group is the image of `⟨c⟩`
    have hDw : SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w₀) = (Subgroup.zpowers c).map (SSGRoute.res k K) := by
      rw [hw₀]
      exact SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink
    obtain ⟨Φ, hΦ⟩ := SSGRoute.PTdualControl.decompK_zpowers_iso k Ω K w₀ c hc2
      (le_of_eq hDw) hne
    -- `w` is a complex place, so `K_wˣ` is divisible
    have hwC : w₀.IsComplex :=
      SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne
    have hdiv : ∀ n : ℕ, 0 < n → ∀ y : (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w₀)).V, ∃ x, n • x = y :=
      SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := ↥K) hwC
    -- the divisible-coefficient dictionary
    obtain ⟨e1⟩ := SSGRoute.ext_one_iso_divisible_cohomology
      ↥(SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w₀))
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w₀)) hdiv
    -- the degree-one internal-`Hom` identification
    obtain ⟨e2⟩ := Work.SSGRoute.ArchDictionary.ext_one_homRep_iso_H1
      ↥(SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w₀))
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w₀))
    -- the coefficient equivalence, in the shape needed by the transfer
    let Ψ' : ((Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E)).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)).V) ≃+ E := Ψ
    have hΨ'' : ∀ (d : ↥(SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofInfinite w₀)))
        (f : (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E)).V →ₗ[SSGRoute.PTExt.Coeff]
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w₀)).V),
        Ψ' (d • f) = Φ d • Ψ' f := by
      intro d f
      rw [show (d • f) = Work.SSGRoute.homSMul (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w₀)) d f from rfl]
      show Ψ (Work.SSGRoute.homSMul (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofInfinite w₀)) d f) = Φ d • Ψ f
      rw [hΨ d f]
      show (d : ↥K ≃ₐ[k] ↥K) • Ψ f
        = (SSGRoute.res k K ((Φ d : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω)) • Ψ f
      rw [hΦ d]
    -- the transfer `H¹(D_w, Hom_ℤ(E'|,K_wˣ)) ≅ H¹(⟨c⟩,E)`
    obtain ⟨e3⟩ := Work.SSGRoute.PT.gcH1Transfer_exists Φ Ψ' hΨ''
    -- `Ac = H¹(⟨c⟩,E)`
    obtain ⟨e4⟩ := Work.SSGRoute.ArchDictionary.ac_addEquiv_H1 K 2 E c
    exact ⟨e1.trans (e2.trans (e3.trans e4.symm))⟩
  · -- ## The case `p ≠ 2`: both sides are trivial
    have hptor' : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T), p • x = 0 := by
      intro x
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
    have hptor : ∀ x : (Eprime p k Ω K T E).V, p • x = 0 := hptor'
    haveI hTfin : Module.Finite (ZMod p) T :=
      Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    let u₀ : T ≃ₗ[ZMod p] ZMod p :=
      LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
    haveI hTfin' : Finite T := Finite.of_injective u₀ u₀.injective
    haveI hXfin : Finite (TensorProduct (ZMod p) E T) :=
      Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) E T
    haveI hMfin' : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
      Finite.of_injective (fun f : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) =>
        (f : (TensorProduct (ZMod p) E T) → ZMod p)) DFunLike.coe_injective
    haveI hMfin : Finite (Eprime p k Ω K T E).V := hMfin'
    haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)) 1) :=
      Work.SSGRoute.ArchDictionary.archimedeanLocalExt1Subsingleton_of_ne_bot p hp2 k ↥K
        (Eprime p k Ω K T E) hptor w₀ hne
    haveI hac : Subsingleton (Ac (K := K) (E := E) c) :=
      Ac_subsingleton_of_odd K p E hp2 c hc2
    exact ⟨{ toFun := fun _ => 0, invFun := fun _ => 0,
             left_inv := fun x => Subsingleton.elim _ _,
             right_inv := fun y => Subsingleton.elim _ _,
             map_add' := fun x y => Subsingleton.elim _ _ }⟩

end Work.SSGRoute.ArchDictionary
