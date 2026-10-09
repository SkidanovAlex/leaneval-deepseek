import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archPairLocal
import Submission.Work.SSGRoute.PT.archβcClauses
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (1) at the value level: `archPairValueZ` is additive in its first argument

`PT.archPairValueZ` is `χ_L (ι_u (levelPair (decompKRestrict) (localUnitsMap) (βc c a) z))`.  Once the
level, the place and `z` are fixed (they do not depend on `a`), additivity in `a` is

* `PT.archβc_add` for the `Ext` argument of `levelPair`, and
* `PT.chi_iota_levelPair_add_fst` (`G1plusLevelClauses`), which is the generic additivity of
  `χ ∘ ι ∘ levelPair` in that argument and already contains the `p`-torsion bookkeeping.

Stating it at the **value level** (no `let`-chain, all data explicit) is what makes the wrapper-level
clause (1) a one-liner: `simp only [archPairLocal, dif_pos hb]` reduces both sides to this statement
because `exists_level_res_ne_one k Ω K c hc1` is the same term on every side, so the `let`-bound data
is syntactically identical — see `PT/NOTE_s17d_flags2305_local_archPair.md` §14.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000

/-- **Clause (1) at the value level**: additivity of `archPairValueZ` in the first (`Ext`) argument,
on `⟨c⟩`-cocycles. -/
theorem archPairValueZ_add_left (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a a' : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (z : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a') :
    archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) (a + a') L hKL u hu z
      = archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu z
        + archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a' L hKL u hu z := by
  simp only [archPairValueZ]
  rw [archβc_add p k Ω K ζ hζ hζK T hT M c hc2 hc1 φ hφ a a' ha ha']
  exact chi_iota_levelPair_add_fst (k := k) (L := ↥L) p u (χ L hKL) (hχadd L hKL)
    (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
    (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a)
    (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a') z
    (by
      have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
      exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX
        (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a))
    (by
      have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
      exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX
        (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a'))



/-- **Unfolding of `PT.archPairLocal`** in the `letI`-form: the right-hand side carries the chosen
level `L_c`, its `K ≤ L_c` proof, the seam place `u_c` and `z_b` as `let`-bound data with their
instances in scope (which is what makes it usable downstream — `Classical.choose` in the goal cannot
supply `NumberField ↥L_c`; see `PT/NOTE_s17d_flags2305_local_archPair.md` §16–§17). -/
theorem archPairLocal_unfold (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b
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
         archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u
           (liesOver_linked k Ω K L φ)
           (zLocal p k Ω K T M c hc2 L hKL
             (archPairLocalL_res k Ω K c hc1) u
             (decompK_linked k Ω L c hc2 hc1 φ hφ) b hb
             (archW k Ω K φ) (liesOver_linked k Ω K L φ))) := by
  simp only [archPairLocal, dif_pos hb, archPairLocalL]


end Work.SSGRoute.PT
