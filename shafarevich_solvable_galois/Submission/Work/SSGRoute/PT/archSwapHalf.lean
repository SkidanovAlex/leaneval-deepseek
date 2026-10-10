import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.archYoneda_perfect
import Submission.Work.SSGRoute.PT.classFormation_reciprocity_allPlaces
import Submission.Work.SSGRoute.PT.vfShared
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean half of `G1⁺` by the class-formation pairing ("the swap")

`_lead_design/flags_1730/flags_1730.md` §4(c) (lead ruling, 10-05 17:5x) confirms the
class-formation involution half for **all** `p`, but **not at level `K`**: at a real place
`χ_K ∘ ι_{w_c} ∘ yonedaPair (βc c a) [b]` is identically `0` and clause (4) fails at `p = 2`.  The
hub must therefore define

  `pair M ⟨c⟩ a b := χ_L (ι_u (levelPair (decompKRestrict) (localUnitsMap) (βc c a) [b|_{D_u}]))`

at a level `L ≥ K` with `res_L c ≠ 1` (e.g. `K(√−1)`) and `u = mk (φc c |_L)` (the seam place).
The two extra inputs are dispatched as separate nodes
(`SSGRoute/PT/archLevelPair_injective`, `SSGRoute/PT/archPair_level_independent`) and must not be
re-proved here.

This file holds the **archimedean dictionary extraction**: the components `βl`, `βg`, `βc` of the
single witness of `E1aClean.localDictionary_natural_family_arch`, read off so that they are
*definitionally* the same `Classical.choose` that `PT.finZB`/`PT.finZBg` use (the lead's re-point of
`PT/finHalfData.lean`, 10-05 17:45).  That is what makes every place of the class-formation sum a
term of one and the same global dictionary.

`archW` is the place `w = mk (φ|_K)` of a seam embedding `φ : Ω →+* ℂ` (the form in which
`localDictionary_natural_family_arch_v2`, `_lead_design/flags_1730/…v2.stmt`, states the archimedean
clauses).  The clause accessors of `βc` (additivity, kernel, surjectivity, the square with `βg`, and
the coefficient-naturality added in v2) are stated against that form and are added once H3755's
restatement of the family lands under the same name.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 2000000

section ArchData

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- The **local dictionary `βl`** of the archimedean family: the first component of the witness of
`E1aClean.localDictionary_natural_family_arch` — definitionally the same term as `PT.finZB`. -/
noncomputable def archβl :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (A : ValuationSubring Ω)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)),
      ((Ω ≃ₐ[k] Ω) → E) →
      Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)) 1 :=
  Classical.choose
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)

/-- The **global dictionary `βg`** of the archimedean family — definitionally the same term as
`PT.finZBg`. -/
noncomputable def archβg :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ((Ω ≃ₐ[k] Ω) → E) →
      Abelian.Ext
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 1 :=
  Classical.choose (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))

/-- The **archimedean dictionary `βc`** of the archimedean family. -/
noncomputable def archβc :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K),
      ((Ω ≃ₐ[k] Ω) → E) →
      Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)))

end ArchData

section GBClauses

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **Additivity of the global dictionary `finZBg`**, read off the archimedean family.  Since the
lead's re-point (`PT/finHalfData.lean`, 10-05 17:32) `finZBg` is `βg` of
`E1aClean.localDictionary_natural_family_arch`, so its clauses sit *after* the archimedean conjunct
of the per-`E` bundle (`.2.1`, not `.1`).  This is the corrected replacement for
`PT.G1plusOwn.finZBg_add`, whose three `finZBg`-accessors still project off the derived (non-arch)
family `localDictionary_natural_family` and therefore no longer elaborate. -/
theorem finZBg_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (b b' : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b') (hl' : SSGRoute.IsLocConstOn ⊤ b') :
    finZBg p K ζ hζ hζK T hT M (b + b')
      = finZBg p K ζ hζ hζK T hT M b + finZBg p K ζ hζ hζK T hT M b' :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) M).2.1
    b b' hb hl hb' hl'

/-- **The square of the natural family in the `finZB`/`finZBg` spelling**: for a global
locally-constant cocycle `b`, the localisation of the global dictionary class is the local
dictionary class.  Stated here so that the hub does not have to import
`PT.G1plusOwn.globalClauses` (whose other three declarations are broken by the re-point). -/
theorem finZB_square (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
        (SSGRoute.PTExt.extToIdeles (k := k) (finZBg p K ζ hζ hζK T hT M b))
      = finZB p K ζ hζ hζK T hT M A hA b :=
  (finZB_spec p M A hA).2.2.2.1 b hb hl

end GBClauses

-- `Work.SSGRoute.PT.archW` used to be defined here; it has been moved, verbatim, to the leaf-free
-- module `Submission/Work/SSGRoute/PT/archWDef.lean` (imported above), so that
-- `ArchNat/archUniformNatural.lean` — the only other consumer — can use it *without* importing this
-- module, which needs the leaf `E1aClean.localDictionary_natural_family_arch` for `archβl`/`archβc`.
-- See H161's `SSGRoute/ACTION_leaf_endgame_cycles_and_cut_list.md`, cut 3.  The name and type of
-- `archW` are unchanged, so no consumer of this file is affected.

section ArchPair

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (χ : G1pOwn.ChiK p k Ω K T)

/-- **The class-formation value of `G1⁺`'s pairing at an involution group, at a seam place and a
level `L`.**  This is verbatim the right-hand side of `finiteS_converse_canonical_v6`'s `hpairArch`:

  `χ_L (ι_u (levelPair (decompKRestrict) (localUnitsMap) (βc c a) (extHRestrict D_u (levelClassOf ψ))))`,

where
* `φ : Ω →+* ℂ` is the *seam* of the involution `c` (`φ ∘ c = conj ∘ φ`, supplied by the hub's
  `φc`/`hseam`), and `archW k Ω K φ = mk (φ|_K)` is the linked place of `K` (`flags_1730/decompK_linked`);
* `L ≥ K` is a level with `res_L c ≠ 1` (`u` is then complex over the linked place), `u : Place ↥L` lies
  over `archW k Ω K φ` (`flags_1730/liesOver_linked`) and has `D_u = (⟨c⟩).map (res k L)`;
* `ψ` is a level-`L` `1`-cocycle on which the `⟨c⟩`-cocycle `b` of the pairing factors,
  `b σ = ψ (res k L σ)` for `σ ∈ ⟨c⟩` (such a `ψ` exists because `res_L c ≠ 1`);
* `βc` is the archimedean dictionary extracted (definitionally) from
  `E1aClean.localDictionary_natural_family_arch`; `a` is any `M`-valued function on `G_k`
  (the value is `0` off the cocycles, where `βc` is).

Stated for **every** `p`: for odd `p`, `βc c a = 0` (both `Ext¹_{D_{w_c}}(M', K_wˣ)` and
`H¹(D_{w_c}, M')` vanish), so no case split on `p` is needed anywhere downstream. -/
noncomputable def archPairValue
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ) (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (ψ : (↥L ≃ₐ[k] ↥L) → VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g) : ZMod p :=
  χ L hKL (iota (k := k) (L := ↥L) u
    (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
      (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a)
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ))))

/-- **The defining formula of `archPairValue`** (the shape `finiteS_converse_canonical_v6`'s
`hpairArch` asks for). -/
theorem archPairValue_def
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (φ : Ω →+* ℂ) (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (ψ : (↥L ≃ₐ[k] ↥L) → VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g) :
    archPairValue p k Ω K ζ hζ hζK T hT χ M c φ a L hKL u hu ψ hψ
      = χ L hKL (iota (k := k) (L := ↥L) u
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
          (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a)
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
            (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)))) := rfl

end ArchPair

end Work.SSGRoute.PT
