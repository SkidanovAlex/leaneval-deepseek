import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.exists_level_res_ne_one
import Submission.Work.SSGRoute.PT.liesOver_linked
import Submission.Work.SSGRoute.PT.localCocycle_descent_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `z_b`: the class in `H¹(D_{u_c}, res M')` of a local `⟨c⟩`-cocycle — `flags_2305`

`G1⁺`'s archimedean pairing is defined (`_lead_design/flags_2305/flags_2305.md`) at one fixed level
`L_c` with `res_{L_c} c ≠ 1` (`PT.exists_level_res_ne_one`), its seam place `u_c = mk (φ|_{L_c})`
(`PT.decompK_linked`), by

  `archPair c a b = χ_{L_c} (ι_{u_c} (levelPair (decompKRestrict) (localUnitsMap) (βc c a) (z_b)))`,

where `z_b` is the class of the local `⟨c⟩`-cocycle `b` transported to `D_{u_c} ≅ ⟨c⟩`.  This file
builds `z_b`: `PT.localCocycle_descent_exists` gives the descended cocycle `bD` on `D_{u_c}` (a
cocycle for the action of `D_{u_c}` through `galRes`), and `z_b` is its image under
`eCoh ∘ H1π` in `extH (Rep.res (decompK u_c).subtype (Rep.res (galRes) M')) 1` — the very type in
which `levelPair` of `archPairValue` consumes its second argument, so that at a level `L ⊇ L_c` the
two spellings agree through `PT.archPair_level_independent_loc`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 2000000

section ZLocal

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
  (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
  (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
  (hres : SSGRoute.res k L c ≠ 1)
  (u : NK.GlobalCFT.Place ↥L)
  (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
  (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
  (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
  (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)

/-- The coefficient representation of `M'` at the decomposition group `D_{u_c}`, with the
`Gal(K/k)`-action pulled back along `galRes ∘ (decompK u_c).subtype`. -/
noncomputable abbrev zRep : Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) u) :=
  Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
    (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))

/-- The descended cocycle `bD` on `D_{u_c}` (`PT.localCocycle_descent_exists`), chosen once. -/
noncomputable def bDaux :
    ↥(SSGRoute.PTExt.decompK (k := k) u) → (zRep p k Ω K T M L u w hu : Type) :=
  Classical.choose (localCocycle_descent_exists p k Ω K T M c hc2 L hKL hres u hDu b hb)

/-- The defining property of `bDaux`. -/
theorem bDaux_spec :
    (∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) u),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu (g * h)
        = bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu g
          + (zRep p k Ω K T M L u w hu).ρ g
              (bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu h)) ∧
    ∀ σ : ↥(Subgroup.zpowers c),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu
        ⟨SSGRoute.res k L σ.1,
          by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ = b σ.1 :=
  Classical.choose_spec (localCocycle_descent_exists p k Ω K T M c hc2 L hKL hres u hDu b hb)

/-- `bDaux` is a `1`-cocycle for the representation `zRep`. -/
theorem bDaux_mem :
    bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu
      ∈ groupCohomology.cocycles₁ (zRep p k Ω K T M L u w hu) := by
  refine (groupCohomology.mem_cocycles₁_iff (A := zRep p k Ω K T M L u w hu)
    (bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu)).mpr (fun g h => ?_)
  rw [(bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu b hb w hu).1 g h]
  abel

/-- **`z_b`**: the class in `H¹(D_{u_c}, res M')` of the local `⟨c⟩`-cocycle `b`. -/
noncomputable def zLocal :
    SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1 :=
  SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
    (zRep p k Ω K T M L u w hu)
    ((groupCohomology.H1π (zRep p k Ω K T M L u w hu)).hom
      ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
        bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩)

end ZLocal

section ArchPairLocalL

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The fixed level `L_c` of `flags_2305`, named once (`PT.exists_level_res_ne_one`), so that every
occurrence of the level — in `PT.archPairLocal`'s body, in its unfolding lemma and in the
wrapper-level clause statements — is the *same* term and the instance keys agree
(`PT/NOTE_s17d_flags2305_local_archPair.md` §19–§20). -/
noncomputable def archPairLocalL (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1) : IntermediateField k Ω :=
  Classical.choose (exists_level_res_ne_one k Ω K c hc1)

theorem archPairLocalL_fin (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1) :
    FiniteDimensional k (archPairLocalL k Ω K c hc1) :=
  (Classical.choose_spec (exists_level_res_ne_one k Ω K c hc1)).choose

theorem archPairLocalL_gal (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1) :
    IsGalois k (archPairLocalL k Ω K c hc1) :=
  (Classical.choose_spec (Classical.choose_spec (exists_level_res_ne_one k Ω K c hc1))).choose

theorem archPairLocalL_le (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1) :
    K ≤ archPairLocalL k Ω K c hc1 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (exists_level_res_ne_one k Ω K c hc1)))).1

theorem archPairLocalL_res (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1)
    [IsGalois k (archPairLocalL k Ω K c hc1)] :
    SSGRoute.res k (archPairLocalL k Ω K c hc1) c ≠ 1 :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (exists_level_res_ne_one k Ω K c hc1)))).2

end ArchPairLocalL

section ArchPairValueZ

/-- **The class-formation value at a level `L` and its place `u`, with the second `levelPair`
argument supplied directly as the local class `z`.**  Same shape as `PT.archPairValue` but with
`z : H¹(D_u, res M')` — which is what `PT.zLocal` produces.  Fully explicit binder list (the
`archSwapHalf` pattern), so call sites are positional and no `variable`-insertion guessing is needed. -/
noncomputable def archPairValueZ (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1) : ZMod p :=
  χ L hKL (iota (k := k) (L := ↥L) u
    (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
      (archβc p k Ω K ζ hζ hζK T hT M c w a) z))

end ArchPairValueZ

section ArchPairLocal

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **`G1⁺`'s pairing at the involution group `⟨c⟩`, in the local single-level form of
`flags_2305`**: the level `L_c` comes from `PT.exists_level_res_ne_one` (independent of `b`),
`u_c = mk (φ|_{L_c})` is its seam place, and the second `levelPair` argument is `z_b = PT.zLocal …`.
The guard is the **local** cocycle condition on `⟨c⟩`; off it the value is `0`. -/
noncomputable def archPairLocal (χ : G1pOwn.ChiK p k Ω K T)
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
      archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu b h (archW k Ω K φ) hu)
    else 0

end ArchPairLocal

end Work.SSGRoute.PT
