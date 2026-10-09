import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
-- (cut 3 of `ACTION_leaf_endgame_cycles_and_cut_list.md`): `archSwapHalf` was imported for the single
-- declaration `archW`, which now lives (leaf-free) in `PT.archWDef`.
import Submission.Work.SSGRoute.PT.archWDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean dictionary, **uniformly in the coefficient** and with its **naturality** clause

`Work.SSGRoute.ArchDictionary.archimedeanDictionaryCanon` produces `βc` at a *fixed* coefficient
module `E`, with the four clauses (add, ker, onto, square).  But the archimedean conjunct of
`Work.SSGRoute.E1aClean.localDictionary_natural_family_arch` needs the family
`βc : ∀ E, ((Ω ≃ₐ[k] Ω) → E) → Ext¹_{D_w}(E′, K_wˣ)` **uniformly in `E`** and with a *fifth* clause,
naturality in `E` — and, as H161's `ArchDictionary/ACTION_lead_ruling_and_naturality.md` records, the
five clauses cannot be recovered from four: a `βc` obtained as an arbitrary isomorphism
`H¹(⟨c⟩,E) ≅ Ext¹` (which is what the four clauses leave free) is not natural.

This file isolates exactly that difficulty and removes it from the arithmetic:  it assembles the
uniform family **and** its naturality from the *one* extra input that the canonical construction has
to supply — an `E`-indexed family of equivalences `Φ E : H¹(⟨c⟩,E) ≃+ Ext¹`, which

* satisfies the comparison square at every `E` (the four-clause input of the present
  `archimedeanDictionaryCanon`), and
* is **natural** in `E` with respect to the induced map `AcMap` on `H¹(⟨c⟩,·)`.

Everything else is formal: `βc E b := Φ E [b|⟨c⟩]` (with `0` off the cocycles), the four clauses are
the same computations as in `ArchDictionary/assemblyOfSquare.lean`, and the fifth clause is
`Φ`'s naturality composed with the identity `AcMap f [b] = [f ∘ b]` (`AcMap_AcOfFun` below).

The two ingredients of the naturality that are *about the local theory* and not about `Φ` are proved
here under no hypotheses at all:

* `mem_Zc_of_equivariant` / `mem_Bc_of_equivariant` — an equivariant additive map carries
  `1`-cocycles on `⟨c⟩` to `1`-cocycles and coboundaries to coboundaries;
* `AcMap` — the induced map `H¹(⟨c⟩,E) →+ H¹(⟨c⟩,E₂)`, with `AcMap_AcOfFun`:
  `AcMap f [b] = [f ∘ b]`.

Consumers: the `ArchDictionary` lane (restate `archimedeanDictionaryCanon` uniformly and apply
`archimedeanDictUniformNat` with the canonical `Φ`), and through it the archimedean conjunct of
`localDictionary_natural_family_arch`.
-/

namespace Work.SSGRoute.ArchNat

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct
open Work.SSGRoute.ArchDictionary

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} [Normal k K]
variable {E E₂ : Type} [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
  [AddCommGroup E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]

/-! ## 1. The cocycle and coboundary conditions transport along an equivariant map -/

/-- The cocycles on `⟨c⟩` are transported by an additive equivariant map. -/
theorem mem_Zc_of_equivariant (f : E →+ E₂)
    (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    {c : Ω ≃ₐ[k] Ω} {b : (Ω ≃ₐ[k] Ω) → E} (hb : b ∈ Zc K E c) :
    (fun σ => f (b σ)) ∈ Zc K E₂ c := by
  intro g hg h hh
  have h1 := hb g hg h hh
  show f (b (g * h)) = f (b g) + (SSGRoute.res k K) g • f (b h)
  rw [h1, map_add]
  rw [hf ((SSGRoute.res k K) g) (b h)]

/-- The coboundaries on `⟨c⟩` are transported by an additive equivariant map. -/
theorem mem_Bc_of_equivariant (f : E →+ E₂)
    (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    {c : Ω ≃ₐ[k] Ω} {b : ↥(Zc K E c)} (hb : b ∈ Bc K E c) :
    (⟨fun σ => f ((b : (Ω ≃ₐ[k] Ω) → E) σ), mem_Zc_of_equivariant f hf b.2⟩ :
      ↥(Zc K E₂ c)) ∈ Bc K E₂ c := by
  obtain ⟨m, hm⟩ := hb
  refine ⟨f m, fun g hg => ?_⟩
  have h1 := hm g hg
  show f ((b : (Ω ≃ₐ[k] Ω) → E) g) = (SSGRoute.res k K) g • f m - f m
  rw [h1, map_sub]
  rw [hf ((SSGRoute.res k K) g) m]

/-! ## 2. The induced map `H¹(⟨c⟩,E) →+ H¹(⟨c⟩,E₂)` -/

/-- The additive map `Z¹(⟨c⟩,E) →+ H¹(⟨c⟩,E₂)` sending `b` to the class of `f ∘ b`. -/
def AcMapPre (f : E →+ E₂)
    (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (c : Ω ≃ₐ[k] Ω) : ↥(Zc K E c) →+ Ac (K := K) (E := E₂) c where
  toFun b := Acπ (K := K) (E := E₂) c
    ⟨fun σ => f ((b : (Ω ≃ₐ[k] Ω) → E) σ), mem_Zc_of_equivariant f hf b.2⟩
  map_zero' := by
    have h0 : (⟨fun σ => f (((0 : ↥(Zc K E c)) : (Ω ≃ₐ[k] Ω) → E) σ),
        mem_Zc_of_equivariant f hf (0 : ↥(Zc K E c)).2⟩ : ↥(Zc K E₂ c)) = 0 := by
      apply Subtype.ext
      funext σ
      simp
    rw [h0, map_zero]
  map_add' := by
    intro a b
    rw [← map_add]
    congr 1
    apply Subtype.ext
    funext σ
    exact map_add f ((a : (Ω ≃ₐ[k] Ω) → E) σ) ((b : (Ω ≃ₐ[k] Ω) → E) σ)

/-- **The map induced on `H¹(⟨c⟩,·)` by an additive equivariant `f : E →+ E₂`.** -/
def AcMap (f : E →+ E₂)
    (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (c : Ω ≃ₐ[k] Ω) : Ac (K := K) (E := E) c →+ Ac (K := K) (E := E₂) c :=
  QuotientAddGroup.lift (Bc K E c) (AcMapPre f hf c) (fun x hx => by
    change Acπ (K := K) (E := E₂) c
      ⟨fun σ => f ((x : (Ω ≃ₐ[k] Ω) → E) σ), mem_Zc_of_equivariant f hf x.2⟩ = 0
    rw [Acπ_eq_zero_iff]
    exact mem_Bc_of_equivariant f hf hx)

/-- **The defining property of `AcMap` on the class of a cocycle**: `AcMap f [b] = [f ∘ b]`. -/
theorem AcMap_AcOfFun (f : E →+ E₂)
    (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (c : Ω ≃ₐ[k] Ω) {b : (Ω ≃ₐ[k] Ω) → E} (hb : b ∈ Zc K E c) :
    AcMap f hf c (AcOfFun (K := K) (E := E) c b)
      = AcOfFun (K := K) (E := E₂) c (fun σ => f (b σ)) := by
  rw [AcOfFun_eq (K := K) (E := E) c b hb,
    AcOfFun_eq (K := K) (E := E₂) c (fun σ => f (b σ))
      (mem_Zc_of_equivariant f hf hb)]
  unfold AcMap
  rfl

/-! ## 3. The uniform family with its naturality clause

The main theorem: given the `E`-indexed, **natural** comparison square `hsq`, the family
`βc E b := Φ E [b|⟨c⟩]` has the four clauses *uniformly* in `E` and is natural in `E`. -/

set_option maxHeartbeats 8000000

/-- **The archimedean dictionary, uniformly in the coefficient and with its naturality clause.**

The input `hsq` is the `E`-indexed form of the comparison square of
`ArchDictionary.archimedeanDictionaryCanon`, *together with* the naturality of the family `Φ` in the
coefficient.  The output is the family `βc` with the five clauses required by the archimedean
conjunct of `Work.SSGRoute.E1aClean.localDictionary_natural_family_arch`. -/
theorem archimedeanDictUniformNat
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hsq : ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (b : (Ω ≃ₐ[k] Ω) → E),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          Φ E (AcOfFun (K := K) (E := E) c b) =
            SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
          [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
          (F' : Eprime p k Ω K T E₂ ⟶ Eprime p k Ω K T E)
          (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
            (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
              (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
          (x : Ac (K := K) (E := E) c),
          Φ E₂ (AcMap (f : E →+ E₂) (fun g e => hf g e) c x) =
            (CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp
              (Φ E x) (zero_add 1))) :
    ∃ βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
          βc E (b + b') = βc E b + βc E b') ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          (βc E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
        (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc E b = y) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          SSGRoute.PTExt.extLoc (k := k) w
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
            = βc E b) ∧
        (∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
            [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
            (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
            (F' : Eprime p k Ω K T E₂ ⟶ Eprime p k Ω K T E)
            (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
              (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
                (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
            (b : (Ω ≃ₐ[k] Ω) → E),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
            βc E₂ (fun σ => f (b σ)) =
              (CategoryTheory.Abelian.Ext.mk₀
                (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp
                (βc E b) (zero_add 1))) := by
  classical
  obtain ⟨Φ, hsq, hnat⟩ := hsq
  let βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    fun E _ _ _ _ _ b =>
      if h : b ∈ Zc K E c then Φ E (Acπ (K := K) (E := E) c ⟨b, h⟩) else 0
  refine ⟨βc, ?_⟩
  intro E instA instM instD instS instF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) additivity on the cocycles of `⟨c⟩`
    intro b b' hb hb'
    have hmb : b ∈ Zc K E c := hb
    have hmb' : b' ∈ Zc K E c := hb'
    have hmb'' : (b + b') ∈ Zc K E c := (Zc K E c).add_mem hmb hmb'
    dsimp only [βc]
    rw [dif_pos hmb'', dif_pos hmb, dif_pos hmb']
    rw [show (⟨b + b', hmb''⟩ : ↥(Zc K E c)) = ⟨b, hmb⟩ + ⟨b', hmb'⟩ from Subtype.ext rfl,
      map_add, map_add]
  · -- (2) the kernel is the coboundaries
    intro b hb
    have hmb : b ∈ Zc K E c := hb
    dsimp only [βc]
    rw [dif_pos hmb, AddEquiv.map_eq_zero_iff, Acπ_eq_zero_iff, mem_Bc]
  · -- (3) surjectivity
    intro y
    obtain ⟨z, hz⟩ := Acπ_surjective (K := K) (E := E) c ((Φ E).symm y)
    refine ⟨(z : (Ω ≃ₐ[k] Ω) → E), z.2, ?_⟩
    dsimp only [βc]
    rw [dif_pos z.2, hz, AddEquiv.apply_symm_apply]
  · -- (4) the comparison square
    intro b hb hl
    have hmb : b ∈ Zc K E c := mem_Zc_of_global (K := K) (E := E) hb
    dsimp only [βc]
    rw [dif_pos hmb]
    exact (hsq E b hb hl).symm.trans (congrArg (Φ E) (AcOfFun_eq (K := K) (E := E) c b hmb))
  · -- (5) naturality in the coefficient module
    intro E₂ instA₂ instM₂ instD₂ instS₂ instF₂ f hf F' hF' b hb
    have hmb : b ∈ Zc K E c := hb
    have hmb₂ : (fun σ => f (b σ)) ∈ Zc K E₂ c :=
      mem_Zc_of_equivariant (f : E →+ E₂) (fun g e => hf g e) hmb
    dsimp only [βc]
    rw [dif_pos hmb₂, dif_pos hmb]
    rw [← AcOfFun_eq (K := K) (E := E₂) c (fun σ => f (b σ)) hmb₂]
    have hstep : AcOfFun (K := K) (E := E₂) c (fun σ => f (b σ))
        = AcMap (f : E →+ E₂) (fun g e => hf g e) c (AcOfFun (K := K) (E := E) c b) :=
      (AcMap_AcOfFun (K := K) (E := E) (E₂ := E₂) (f : E →+ E₂) (fun g e => hf g e) c hmb).symm
    rw [hstep]
    rw [← AcOfFun_eq (K := K) (E := E) c b hmb]
    exact hnat E E₂ f hf F' hF' (AcOfFun (K := K) (E := E) c b)

/-- **The same, at the seam place `archW k Ω K φ` of the involution `c`** — the exact place at
which the archimedean conjunct of `localDictionary_natural_family_arch` asserts the five clauses.
This is `archimedeanDictUniformNat` with `w := archW k Ω K φ` and its two defining facts
(`Place.ofInfinite_ne_ofFinite` and `rfl`) discharged. -/
theorem archimedeanDictUniformNat_archW
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hsq : ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (SSGRoute.PT.archW k Ω K φ)).subtype (Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) (SSGRoute.PT.archW k Ω K φ)) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (b : (Ω ≃ₐ[k] Ω) → E),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          Φ E (AcOfFun (K := K) (E := E) c b) =
            SSGRoute.PTExt.extLoc (k := k) (SSGRoute.PT.archW k Ω K φ)
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
          [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
          (F' : Eprime p k Ω K T E₂ ⟶ Eprime p k Ω K T E)
          (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
            (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
              (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
          (x : Ac (K := K) (E := E) c),
          Φ E₂ (AcMap (f : E →+ E₂) (fun g e => hf g e) c x) =
            (CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
                (SSGRoute.PT.archW k Ω K φ)).subtype F')).comp
              (Φ E x) (zero_add 1))) :
    ∃ βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (SSGRoute.PT.archW k Ω K φ)).subtype (Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) (SSGRoute.PT.archW k Ω K φ)) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
          βc E (b + b') = βc E b + βc E b') ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          (βc E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
        (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc E b = y) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          SSGRoute.PTExt.extLoc (k := k) (SSGRoute.PT.archW k Ω K φ)
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
            = βc E b) ∧
        (∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
            [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
            (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
            (F' : Eprime p k Ω K T E₂ ⟶ Eprime p k Ω K T E)
            (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
              (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
                (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
            (b : (Ω ≃ₐ[k] Ω) → E),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
            βc E₂ (fun σ => f (b σ)) =
              (CategoryTheory.Abelian.Ext.mk₀
                (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
                  (SSGRoute.PT.archW k Ω K φ)).subtype F')).comp
                (βc E b) (zero_add 1))) :=
  archimedeanDictUniformNat p k Ω K ζ hζ hζK T hT c hc2 hc1 (SSGRoute.PT.archW k Ω K φ) φ
    (fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q) rfl hφ hsq

end

end Work.SSGRoute.ArchNat
