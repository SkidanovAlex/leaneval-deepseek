import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archPairLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abstract seam dictionary: `archPairValueZAbs` / `archPairLocalAbs`

The lead's ruling on the **type taint** (`PT/PING_s18c_type_taint_blocks_certification.md`): a
declaration whose *type* mentions `PT.archβc` (or `PT.finZB`, or anything defined from
`Classical.choose` of `E1aClean.localDictionary_natural_family_arch`) can never pass
`declare_proven`, because `#print axioms` traverses the type and `localDictionary_natural_family_arch`
still has one `sorry`.  The fix is to state the archimedean half over an **abstract** seam dictionary

```
bc : ∀ E …, (c : Ω ≃ₐ[k] Ω) → (w : Place ↥K) → ((Ω ≃ₐ[k] Ω) → E) → Ext … (localUnitsK w) 1
```

with the spec conjuncts the proof uses as *hypotheses*.  This file contains the definitions of that
abstract layer — they are `PT.archPairValueZ` / `PT.archPairLocal` with `archβc` replaced verbatim by
the parameter `bc`, so no `archβc` (and hence no `sorryAx`) occurs in their types or bodies — the
expanding lemma for the wrapper (what the wrapper-level clauses consume), and the two instantiation
lemmas (`archPairValueZAbs_archβc`, `archPairLocalAbs_archβc`), which are the only declarations of
this file that mention `archβc`.  All binder lists are explicit (no `variable` machinery), so call
sites are positional.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000

/-- **The abstract seam dictionary**: the `βc`-component's type, with no dependence on the chosen
witness of `E1aClean.localDictionary_natural_family_arch`. -/
abbrev SeamDict (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Type _ :=
  ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K),
    ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1

/-- **`PT.archPairValueZ` with an abstract seam dictionary.** -/
noncomputable def archPairValueZAbs (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K) (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (z : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1) : ZMod p :=
  χ L hKL (iota (k := k) (L := ↥L) u
    (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) (bc M c w a) z))

/-- **`PT.archPairLocal` with an abstract seam dictionary**: the same guard, the same fixed level
`PT.archPairLocalL` and the same `z_b = PT.zLocal …`. -/
noncomputable def archPairLocalAbs (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) : ZMod p := by
  classical
  exact
    if h : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b then
      let L := archPairLocalL k Ω K c hc1
      haveI : FiniteDimensional k L := archPairLocalL_fin k Ω K c hc1
      haveI : IsGalois k L := archPairLocalL_gal k Ω K c hc1
      have hKL : K ≤ L := archPairLocalL_le k Ω K c hc1
      have hres : SSGRoute.res k L c ≠ 1 := archPairLocalL_res k Ω K c hc1
      letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
      letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI : NumberField ↥L := inferInstance
      let u : NK.GlobalCFT.Place ↥L :=
        NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥L Ω)))
      have hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ) := liesOver_linked k Ω K L φ
      have hDu : SSGRoute.PTExt.decompK (k := k) u
          = (Subgroup.zpowers c).map (SSGRoute.res k L) :=
        decompK_linked k Ω L c hc2 hc1 φ hφ
      archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu b h (archW k Ω K φ) hu)
    else 0

/-- **Expanding lemma for `PT.archPairLocalAbs`** (the `letI`-form, with the instances of the chosen
level in scope, exactly as `PT.archPairLocal_unfold` does for `PT.archPairLocal`). -/
theorem archPairLocalAbs_unfold (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b
      = (let L := archPairLocalL k Ω K c hc1
         haveI : FiniteDimensional k L := archPairLocalL_fin k Ω K c hc1
         haveI : IsGalois k L := archPairLocalL_gal k Ω K c hc1
         haveI : NumberField ↥L := inferInstance
         have hKL : K ≤ L := archPairLocalL_le k Ω K c hc1
         letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
         letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
         letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
         let u : NK.GlobalCFT.Place ↥L :=
           NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥L Ω)))
         archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u
           (liesOver_linked k Ω K L φ)
           (zLocal p k Ω K T M c hc2 L hKL
             (archPairLocalL_res k Ω K c hc1) u
             (decompK_linked k Ω L c hc2 hc1 φ hφ) b hb
             (archW k Ω K φ) (liesOver_linked k Ω K L φ))) := by
  simp only [archPairLocalAbs, dif_pos hb]

/-- The concrete seam dictionary of the workspace witness. -/
noncomputable def archβcSeam (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    SeamDict p k Ω K ζ hζ hζK T hT :=
  fun E _ _ _ _ _ c w b => archβc p k Ω K ζ hζ hζK T hT E c w b

/-- **`PT.archPairValueZ` is `PT.archPairValueZAbs` at the concrete seam dictionary.** -/
theorem archPairValueZAbs_archβc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K) (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (z : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1) :
    archPairValueZAbs p k Ω K ζ hζ hζK T hT (archβcSeam p k Ω K ζ hζ hζK T hT) χ M c w a
        L hKL u hu z
      = archPairValueZ p k Ω K ζ hζ hζK T hT χ M c w a L hKL u hu z :=
  rfl

/-- **`PT.archPairLocal` is `PT.archPairLocalAbs` at the concrete seam dictionary.** -/
theorem archPairLocalAbs_archβc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT (archβcSeam p k Ω K ζ hζ hζK T hT) χ M c hc2 hc1 φ
        hφ a b
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b :=
  rfl

end Work.SSGRoute.PT
