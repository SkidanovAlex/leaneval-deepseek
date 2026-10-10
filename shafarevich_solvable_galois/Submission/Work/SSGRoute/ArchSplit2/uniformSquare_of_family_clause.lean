import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchNat.archUniformNatural
import Submission.Work.SSGRoute.ArchSplit2.splitPlace_family_clause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchSplit2

open Work.SSGRoute.ArchDictionary

set_option maxHeartbeats 1000000

/-! ## Descending a `⟨c⟩`-dictionary along `Z¹/B¹`

The helpers below are the pure group-theoretic content of the statement:  a cochain function `β` on
`(Ω ≃ₐ[k] Ω) → E` that is additive on `⟨c⟩`-cocycles (`hadd`) and whose zero set among the cocycles
is exactly the coboundaries (`hker`) restricts to an additive map `Z¹(⟨c⟩,E) →+ A`, which kills
`B¹(⟨c⟩,E)` and hence descends along `QuotientAddGroup.lift` to an additive map
`Ac c E = Z¹/B¹ →+ A`.  The kernel clause makes that descent injective and a surjectivity clause
makes it bijective, so it is an additive equivalence. -/

section Descent

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} [Normal k K]
variable {E A : Type} [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] [AddCommGroup A]

/-- The additive map `Z¹(⟨c⟩,E) →+ A` obtained by restricting a cochain function `β` to the
`⟨c⟩`-cocycles. -/
noncomputable def acLift (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) :
    ↥(Zc K E c) →+ A where
  toFun b := β (b : (Ω ≃ₐ[k] Ω) → E)
  map_zero' := by
    have hc0 : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (0 : (Ω ≃ₐ[k] Ω) → E) := by
      intro g hg h hh; simp
    have hcb : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (0 : (Ω ≃ₐ[k] Ω) → E) := ⟨0, fun g hg => by simp⟩
    show β ((0 : ↥(Zc K E c)) : (Ω ≃ₐ[k] Ω) → E) = 0
    exact (hker 0 hc0).mpr hcb
  map_add' := by
    intro b b'
    show β (((b + b' : ↥(Zc K E c))) : (Ω ≃ₐ[k] Ω) → E)
      = β (b : (Ω ≃ₐ[k] Ω) → E) + β (b' : (Ω ≃ₐ[k] Ω) → E)
    exact hadd (b : _ → E) (b' : _ → E) (mem_Zc.mp b.2) (mem_Zc.mp b'.2)

/-- **The descent of `β` to `Ac c E = H¹(⟨c⟩,E)`.** -/
noncomputable def acPhi (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) :
    Ac (K := K) (E := E) c →+ A :=
  QuotientAddGroup.lift (Bc K E c) (acLift c β hadd hker) (fun x hx => by
    show acLift c β hadd hker x = 0
    show β (x : (Ω ≃ₐ[k] Ω) → E) = 0
    exact (hker _ (mem_Zc.mp x.2)).mpr (mem_Bc.mp hx))

/-- The value of the descent on the class of a cocycle: `acPhi [b] = β b`. -/
theorem acPhi_Acπ (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (b : ↥(Zc K E c)) :
    acPhi c β hadd hker (Acπ (K := K) (E := E) c b) = β (b : (Ω ≃ₐ[k] Ω) → E) := by
  rw [Acπ_apply, QuotientAddGroup.mk'_apply]
  unfold acPhi
  rw [QuotientAddGroup.lift_mk']
  rfl

/-- The value of the descent on the class of a function that is a `⟨c⟩`-cocycle. -/
theorem acPhi_AcOfFun (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    {b : (Ω ≃ₐ[k] Ω) → E} (hb : b ∈ Zc K E c) :
    acPhi c β hadd hker (AcOfFun (K := K) (E := E) c b) = β b := by
  rw [AcOfFun_eq (K := K) (E := E) c b hb]
  exact acPhi_Acπ c β hadd hker ⟨b, hb⟩

/-- The kernel clause makes the descent injective. -/
theorem acPhi_injective (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) :
    Function.Injective (acPhi c β hadd hker) := by
  intro x y hxy
  have hsub : acPhi c β hadd hker (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨w, hw⟩ := Acπ_surjective (K := K) (E := E) c (x - y)
  have h1 : β (w : (Ω ≃ₐ[k] Ω) → E) = 0 := by
    rw [← hw] at hsub
    rw [acPhi_Acπ c β hadd hker w] at hsub
    exact hsub
  have h2 : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
      (w : (Ω ≃ₐ[k] Ω) → E) :=
    (hker _ (mem_Zc.mp w.2)).mp h1
  have h3 : Acπ (K := K) (E := E) c w = 0 := (Acπ_eq_zero_iff w).mpr (mem_Bc.mpr h2)
  have h4 : x - y = 0 := by rw [← hw, h3]
  exact sub_eq_zero.mp h4

/-- The surjectivity clause makes the descent surjective. -/
theorem acPhi_surjective (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (honto : ∀ y : A, ∃ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ β b = y) :
    Function.Surjective (acPhi c β hadd hker) := by
  intro y
  obtain ⟨b, hb, hy⟩ := honto y
  exact ⟨Acπ (K := K) (E := E) c ⟨b, mem_Zc.mpr hb⟩, by
    rw [acPhi_Acπ c β hadd hker ⟨b, mem_Zc.mpr hb⟩]
    exact hy⟩

/-- The kernel and surjectivity clauses make the descent bijective. -/
theorem acPhi_bijective (c : Ω ≃ₐ[k] Ω) (β : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hadd : ∀ b b', SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        β (b + b') = β b + β b')
    (hker : ∀ b, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (honto : ∀ y : A, ∃ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ β b = y) :
    Function.Bijective (acPhi c β hadd hker) :=
  ⟨acPhi_injective c β hadd hker, acPhi_surjective c β hadd hker honto⟩

end Descent

/-- **The `Φ` attached to a place by a `βc`-family with the five archimedean clauses (the `hsq`
input of `ArchNat.archimedeanDictUniformNat`).**

`p = 2`; `c` a nontrivial involution; `w` **any** place (the lemma is place-independent: the split
hypothesis `decompK w = ⊥` used to be carried along and is never used — verified by `grep`, and the
statement is strictly stronger without it).  Given the `E`-indexed dictionary `βc` at `w` with its
five clauses (`add`, `kernel`, `onto`, `square`, `naturality`) — exactly the output of
`ArchSplit2.splitPlace_family_clause` in the split case, and the input the nonsplit (`decompK w ≠ ⊥`)
case must produce — produce the `E`-indexed family of equivalences

    Φ E : Ac c E ≃+ Ext¹_{D_w}(E'|, K_wˣ)        (Ac c E = Z¹(⟨c⟩,E)/B¹(⟨c⟩,E))

with the comparison square `Φ E (AcOfFun c b) = extLoc w (extToIdeles (γ b))` on global locally
constant cocycles and **naturality** in the coefficient.  This is literally the `hsq` argument of the
proved `ArchNat.archimedeanDictUniformNat` (its second conjunct up to the identity
`AcMap f (AcOfFun c b) = AcOfFun c (f ∘ b)`, `ArchNat.AcMap_AcOfFun`), and the `Φ`-shaped companion of
`PT.archSplitPlace_dictionary_natural_of_h2E₂` / `ArchDictionary.archimedeanDictNonsplit_of_square`
(whose `∃ Φ` shape it matches).  For the `ArchPlaceDict`-shaped wrapper see
`ArchSplit2.archPlaceDict_of_family_clause`.

Proof: `βc` kills the coboundaries `Bc` on `Zc` (kernel clause), so it descends along
`QuotientAddGroup.lift` to an additive `Φ E : Ac c E →+ Ext`; the kernel clause makes `Φ E` injective
and the onto clause makes it surjective, so it is an `AddEquiv`; the square is the `square` clause
evaluated at `AcOfFun c b = [b|⟨c⟩]`, and naturality is the `naturality` clause (the root of the
quotient being `AcOfFun c (f ∘ b) = [f ∘ b]` when `b` is a `⟨c⟩`-cocycle).

File: `Submission/Work/SSGRoute/ArchSplit2/uniformSquare_of_family_clause.lean`; namespace
`Work.SSGRoute.ArchSplit2`. -/
theorem uniformSquare_of_family_clause
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K)
    (βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hadd : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b b' : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc E (b + b') = βc E b + βc E b')
    (hker : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (honto : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1),
        ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc E b = y)
    (hsq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        βc E b = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)))
    (hnat : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
          Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
        (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
            (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
        (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        βc E₂ (fun σ => f (b σ)) = (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (βc E b) (zero_add 1)) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        Φ E (Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E) c b) =
          SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
          Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
        (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
            (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
        (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        Φ E₂ (Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E₂) c (fun σ => f (b σ))) =
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp
            (Φ E (Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E) c b)) (zero_add 1)) := by
  classical
  let Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    fun E _ _ _ _ _ =>
      AddEquiv.ofBijective (acPhi c (βc E) (hadd E) (hker E))
        (acPhi_bijective c (βc E) (hadd E) (hker E) (honto E))
  refine ⟨Φ, ?_, ?_⟩
  · -- the comparison square on the canonical global class
    intro E _ _ _ _ _ b hb hl
    have hmb : b ∈ Zc K E c := mem_Zc_of_global hb
    dsimp only [Φ]
    rw [AddEquiv.ofBijective_apply, acPhi_AcOfFun c (βc E) (hadd E) (hker E) hmb]
    exact hsq E b hb hl
  · -- naturality in the coefficient module
    intro E _ _ _ _ _ E₂ _ _ _ _ _ f hf F' hF' b hb
    have hmb : b ∈ Zc K E c := mem_Zc.mpr hb
    have hmb₂ : (fun σ => f (b σ)) ∈ Zc K E₂ c :=
      Work.SSGRoute.ArchNat.mem_Zc_of_equivariant (f : E →+ E₂) hf hmb
    dsimp only [Φ]
    rw [AddEquiv.ofBijective_apply, AddEquiv.ofBijective_apply,
      acPhi_AcOfFun c (βc E₂) (hadd E₂) (hker E₂) hmb₂,
      acPhi_AcOfFun c (βc E) (hadd E) (hker E) hmb]
    exact hnat E E₂ f hf F' hF' b hb

end Work.SSGRoute.ArchSplit2
