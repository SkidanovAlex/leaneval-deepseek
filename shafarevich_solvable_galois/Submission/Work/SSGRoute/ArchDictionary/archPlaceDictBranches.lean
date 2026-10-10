import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.AcOdd
import Submission.Work.SSGRoute.ArchDictionary.archimedeanLocalExt1Subsingleton_of_ne_bot
import Submission.Work.SSGRoute.ArchSplit2.archPlaceDict_of_psi
import Submission.Work.SSGRoute.ArchSplit2.archSplit2_canonical
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
import Submission.Work.SSGRoute.PT.prime_eq_two_of_decompK_eq_bot
import Submission.Work.Shrinking.finite_tensorProduct_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two of the three branches of `ArchPlaceDict` at an archimedean place

`Work.SSGRoute.LeadNatWit.ArchPlaceDict p k Ω K ζ hζ hζK T hT c w` is the `E`-indexed comparison
square of the archimedean dictionary: an `E`-indexed family of additive equivalences
`Ac c E ≃+ Ext¹_{D_w}(E'|, K_wˣ)`, natural in the coefficient `E`, whose value on the class of a
globally defined cocycle is the `w`-component of the canonical global dictionary.

This file discharges two of the three cases of the case split:

* **split** (`decompK w = ⊥`): the place is real, necessarily `p = 2`
  (`PT.prime_eq_two_of_decompK_eq_bot`), and the dictionary is A1–A3 of
  `_lead_design/ssg_arch2_2320.md`, executed in `Submission/Work/SSGRoute/ArchSplit2/`
  (`ArchSplit2.archSplit2_canonical` ∘ `ArchSplit2.archPlaceDict_of_psi`) — case `archPlaceDict_of_split`.

* **nonsplit, odd `p`** (`decompK w ≠ ⊥`, `p ≠ 2`): both sides of every clause are subsingletons —
  `Ac = H¹(⟨c⟩,E) = 0` because `2` is invertible (`AcOdd.Ac_subsingleton_of_odd`) and
  `Ext¹_{D_w}(E'|,K_wˣ) = 0` because `w` is a complex place
  (`ArchDictionary.archimedeanLocalExt1Subsingleton_of_ne_bot`) — so the zero family works.  Case
  `archPlaceDict_of_nonsplit_odd`.

The remaining case (`decompK w ≠ ⊥`, `p = 2`, the complex place) is the arithmetic content.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The split (`decompK w = ⊥`) branch of `ArchPlaceDict`.** -/
theorem archPlaceDict_of_split
    (p : ℕ) [Fact p.Prime]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥) :
    Work.SSGRoute.LeadNatWit.ArchPlaceDict p k Ω K ζ hζ hζK T hT c w := by
  subst hw
  have hbot' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) = ⊥ := hbot
  have hp : p = 2 :=
    SSGRoute.PT.prime_eq_two_of_decompK_eq_bot p k Ω K ζ hζ hζK c hc2 hc1
      (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) φ rfl hlink hbot'
  obtain ⟨ψ, hψ, hψnat, hψsq⟩ :=
    SSGRoute.ArchSplit2.archSplit2_canonical p hp k Ω K ζ hζ hζK T hT
      (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) hbot'
      ⟨c, φ, hc2, hc1, hlink, rfl⟩
  have hψsq' : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ψ E (b c) = SSGRoute.PTExt.extLoc (k := k)
        (NK.GlobalCFT.Place.ofInfinite
          (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) :=
    fun E _ _ _ _ _ b hb hl => hψsq E c hc2 hc1 φ hlink rfl b hb hl
  exact SSGRoute.ArchSplit2.archPlaceDict_of_psi p hp k Ω K ζ hζ hζK T hT c hc2 hc1 φ hlink
    (NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) rfl hbot' ψ hψ hψnat hψsq'

/-- **The nonsplit, odd-`p` branch of `ArchPlaceDict`.**  Both the involution cohomology
`Ac = H¹(⟨c⟩,E)` and the local `Ext¹_{D_w}(E'|,K_wˣ)` are subsingletons, so the zero family is a
dictionary with both clauses. -/
theorem archPlaceDict_of_nonsplit_odd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    Work.SSGRoute.LeadNatWit.ArchPlaceDict p k Ω K ζ hζ hζK T hT c w := by
  classical
  subst hw
  set w₀ : NumberField.InfinitePlace ↥K :=
    NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)) with hw₀
  have hne' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite w₀) ≠ ⊥ := by
    rw [hw₀]; simpa only [hw₀] using hne
  -- the local `Ext¹` is a subsingleton, for every finite `p`-torsion coefficient `X`
  have hExtSub : ∀ (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V]
      (hX : ∀ x : X.V, p • x = 0),
      Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite w₀)).subtype X)
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)) 1) :=
    fun X _ hX => archimedeanLocalExt1Subsingleton_of_ne_bot p hp2 k ↥K X hX w₀ hne'
  have hptor : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)), p • x = 0 := by
    intro E _ _ _ _ _ x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
  refine ⟨?_, ?_, ?_⟩
  · -- ## the family `Φ`
    intro E _ _ _ _ _
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
    haveI : Subsingleton (Ac (K := K) (E := E) c) :=
      Ac_subsingleton_of_odd K p E hp2 c hc2
    haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)) 1) :=
      hExtSub (Eprime p k Ω K T E) (hptor E)
    exact { toFun := fun _ => 0, invFun := fun _ => 0,
            left_inv := fun x => Subsingleton.elim _ _, right_inv := fun y => Subsingleton.elim _ _,
            map_add' := fun x y => Subsingleton.elim _ _ }
  · -- ## the comparison square
    intro E _ _ _ _ _ b _ _
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
    haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)) 1) :=
      hExtSub (Eprime p k Ω K T E) (hptor E)
    exact Subsingleton.elim _ _
  · -- ## naturality in the coefficient
    intro E _ _ _ _ _ E₂ _ _ _ _ _ f hf F' hF' x
    haveI : Subsingleton (Ac (K := K) (E := E) c) :=
      Ac_subsingleton_of_odd K p E hp2 c hc2
    haveI : Subsingleton (Ac (K := K) (E := E₂) c) :=
      Ac_subsingleton_of_odd K p E₂ hp2 c hc2
    haveI hTfin : Module.Finite (ZMod p) T :=
      Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    let u₀ : T ≃ₗ[ZMod p] ZMod p :=
      LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
    haveI hTfin' : Finite T := Finite.of_injective u₀ u₀.injective
    haveI hXfin : Finite (TensorProduct (ZMod p) E₂ T) :=
      Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) E₂ T
    haveI hMfin' : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) :=
      Finite.of_injective (fun f : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T) =>
        (f : (TensorProduct (ZMod p) E₂ T) → ZMod p)) DFunLike.coe_injective
    haveI hMfin : Finite (Eprime p k Ω K T E₂).V := hMfin'
    haveI hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite w₀)).subtype (Eprime p k Ω K T E₂))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofInfinite w₀)) 1) :=
      hExtSub (Eprime p k Ω K T E₂) (hptor E₂)
    exact Subsingleton.elim _ _

end Work.SSGRoute.ArchDictionary

#print axioms Work.SSGRoute.ArchDictionary.archPlaceDict_of_split
#print axioms Work.SSGRoute.ArchDictionary.archPlaceDict_of_nonsplit_odd
