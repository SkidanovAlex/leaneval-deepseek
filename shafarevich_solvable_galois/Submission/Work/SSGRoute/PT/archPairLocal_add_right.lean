import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.PT.archPairLocalClauses
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (2) at `⟨c⟩` for the local single-level archimedean pairing `PT.archPairLocal`

The wrapper-level statement `PT.archPairLocal_add_right` is assembled here from two pieces:

* `PT.archPairValueZ_add_snd` — clause (2) at the **value level** (additivity of
  `PT.archPairValueZ` in its second `H¹`/`DualMod` argument at a fixed level, place and first
  argument), over `chi_iota_levelPair_add_snd`;
* `PT.zLocal_add` — the **new** additivity of the descent `b ↦ zLocal (b)`, which is what makes the
  three second arguments `zLocal (b + b')`, `zLocal b`, `zLocal b'` comparable at all;

and `PT.archPairValueZ_add_snd_local` glues them at the level of the three `zLocal` terms, so that
the wrapper-level proof is the same three-step shape as `PT.archPairLocal_add_left`.

## Verification status (measured)

* `archPairLocal_add_right` is **proved here** (this module builds, no open proof obligation), and the
  proof uses **no property of the chosen dictionary `archβc`**: clause (2) is additivity in the
  second (`H¹`) variable, so `chi_iota_levelPair_add_snd` (generic in the first argument) suffices.
* `bDaux_add` and `zLocal_add` — the genuinely new descent additivity — are **axiom-clean**
  (`[propext, Classical.choice, Quot.sound]`).
* The *statement* of `archPairLocal_add_right` mentions `PT.archPairLocal`, whose definitional
  closure reaches `PT.archβc`, which is built from
  `E1aClean.localDictionary_natural_family_arch` — still an unproved obligation
  (`E1aClean/localDictionary_natural_family.lean:337`), itself gated on
  `ArchDictionary.archimedeanDictionaryCanon` (the localisation-comparison chapter).  The axiom
  checker traverses the *statement*, so the placeholder axiom appears for the type alone: even
  `theorem t (h : archPairLocal … b = archPairLocal … b) : True := trivial` is rejected.
  Hence no proof of this statement (by anyone) can pass the permitted-axiom check until that gate is
  closed or `archβc` is defined from a clean source — at which point this module verifies unchanged.
  See `PT/PING_archPairLocal_add_right_gate.md`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Clause (2) at the value level**: additivity of `PT.archPairValueZ` in its second
(`H¹`/`DualMod`) argument `z`, at a fixed level `L`, place `u` and first argument `a`.  Exact mirror
of `PT.archPairValueZ_add_left` with `chi_iota_levelPair_add_snd` in place of `..._add_fst`; the two
`p`-torsion facts `p • z = 0`, `p • z' = 0` are discharged by `E6Util.ext_nsmul_p_torsion` against
the pointwise `p`-torsion of the coefficient module `VFcoef p M T`. -/
theorem archPairValueZ_add_snd (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (z z' : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1) :
    archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu (z + z')
      = archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu z
        + archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu z' := by
  simp only [archPairValueZ]
  refine chi_iota_levelPair_add_snd (k := k) (L := ↥L) p u (χ L hKL) (hχadd L hKL)
    (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
    (archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a) z z' ?_ ?_
  · have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
    exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hX z
  · have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
    exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hX z'

/-- **`bDaux` is additive in the cocycle `b`.**  `bDaux` is `Classical.choose` of
`PT.localCocycle_descent_exists`, whose spec pins it on *all* of `D_{u_c} = (⟨c⟩).map (res k L)`
(`bDaux_spec`); since `res k L` maps `⟨c⟩` onto `D_{u_c}` (`hDu`), every `g : D_{u_c}` is
`⟨res k L σ, _⟩`, so `bDaux` is determined by `b` alone and is additive pointwise. -/
theorem bDaux_add
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
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
    (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b')
    (hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b'))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    bDaux p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum w hu
      = bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu
        + bDaux p k Ω K T M c hc2 L hKL hres u hDu b' hb' w hu := by
  -- `bDaux` at an element of the form `⟨res k L σ, _⟩` is `b σ`, for *every* proof of membership.
  have key : ∀ (b₀ : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
      (hb₀ : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b₀)
      (σ : ↥(Subgroup.zpowers c))
      (h : SSGRoute.res k L σ.1 ∈ SSGRoute.PTExt.decompK (k := k) u),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b₀ hb₀ w hu ⟨SSGRoute.res k L σ.1, h⟩ = b₀ σ.1 := by
    intro b₀ hb₀ σ h
    rw [show (⟨SSGRoute.res k L σ.1, h⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
        = ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩
      from Subtype.ext rfl]
    exact (bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu b₀ hb₀ w hu).2 σ
  funext g
  -- `bDaux`'s declared codomain is the carrier of `zRep`, which is only *definitionally* the bare
  -- module `VFcoef p M T`; rewriting inside the goal needs the two spellings unified, so the
  -- pointwise goal is moved to the bare module first (`show` at default transparency).
  show ((bDaux p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum w hu g : VFcoef p M T)
      = (bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu g : VFcoef p M T)
        + (bDaux p k Ω K T M c hc2 L hKL hres u hDu b' hb' w hu g : VFcoef p M T))
  obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp (by rw [← hDu]; exact g.2)
  have hg : g = ⟨SSGRoute.res k L σ, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ :=
    Subtype.ext hσeq.symm
  rw [hg]
  rw [key (b + b') hsum ⟨σ, hσ⟩, key b hb ⟨σ, hσ⟩, key b' hb' ⟨σ, hσ⟩]
  rfl

/-- **Additivity of `PT.zLocal` in the cocycle `b`**: `z_b` is additive, i.e. the descent
`b ↦ bDaux b` commutes with addition (`bDaux_add`) and the packaging `eCoh ∘ H1π` is additive. -/
theorem zLocal_add
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
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
    (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b')
    (hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b'))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    zLocal p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum w hu
      = zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu
        + zLocal p k Ω K T M c hc2 L hKL hres u hDu b' hb' w hu := by
  have h1 : (⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum w hu,
        bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum w hu⟩
      : ↥(groupCohomology.cocycles₁ (zRep p k Ω K T M L u w hu)))
      = ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
          bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩
        + ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b' hb' w hu,
          bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b' hb' w hu⟩ :=
    Subtype.ext (bDaux_add p k Ω K T M c hc2 L hKL hres u hDu b b' hb hb' hsum w hu)
  simp only [zLocal]
  rw [h1, LinearMap.map_add, AddEquiv.map_add]

/-- **Clause (2) with the descent applied**: the value `PT.archPairValueZ` of
`zLocal (b + b')` is the sum of the values of `zLocal b` and `zLocal b'` (at a fixed level, place
and first argument).  `zLocal_add` rewrites the second argument, and `archPairValueZ_add_snd` is the
value-level clause. -/
theorem archPairValueZ_add_snd_local
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b')
    (hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b')) :
    archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum (archW k Ω K φ) hu)
      = archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu
          (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
        + archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu
          (zLocal p k Ω K T M c hc2 L hKL hres u hDu b' hb' (archW k Ω K φ) hu) := by
  rw [zLocal_add p k Ω K T M c hc2 L hKL hres u hDu b b' hb hb' hsum (archW k Ω K φ) hu]
  exact archPairValueZ_add_snd p k Ω K ζ hζ hζK T hT χ hχadd M c hc2 hc1 φ hφ a L hKL u hu
    (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
    (zLocal p k Ω K T M c hc2 L hKL hres u hDu b' hb' (archW k Ω K φ) hu)

/-- **Clause (2) at `⟨c⟩` for the local single-level archimedean pairing `PT.archPairLocal`**:
additivity in the second variable (the `H¹`/`DualMod` argument), on `⟨c⟩`-cocycles.

Route.  `PT.archPairLocal_unfold` (`PT/archPairValueZ_add_left.lean`) rewrites all three values into
the `let`-chain with the named level `PT.archPairLocalL k Ω K c hc1`; install the instances for that
term (`archPairLocalL_fin`, `archPairLocalL_gal`, `NumberField`, `Algebra ↥K ↥L`,
`IsScalarTower k ↥K ↥L`, `IsScalarTower ↥K ↥L Ω`) exactly as `PT.archPairLocal_add_left` does
(`PT/archPairLocalClauses.lean`).  Then the `a`-argument is the same on all three sides and only
`z := PT.zLocal … b` changes, so the value-level statement

* `archPairValueZ … y L hKL u hu (z + z') = archPairValueZ … y L hKL u hu z + archPairValueZ … y L hKL u hu z'`,
  proved by `PT.chi_iota_levelPair_add_snd` (`PT/G1plusLevelClauses.lean:249`) with the `p`-torsion of
  the two `Ext` classes supplied as in `PT.archPairValueZ_add_left`
  (`Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left` against
  `fun x : VFcoef p M T => nsmul_eq_zero_of_zmod' p x`),

is the whole mathematical content, together with the **new** additivity of the descent

* `PT.zLocal … (b + b') hsum = PT.zLocal … b hb + PT.zLocal … b' hb'`
  (same `L`, `u`, `w`, `hu`), the one genuinely new lemma: `PT.bDaux` is
  `Classical.choose (PT.localCocycle_descent_exists …)`, whose spec pins it on *all* of
  `D_u = (zpowers c).map (res k L)`; since `res k L` is onto `D_u`, every `g : D_u` is
  `⟨res k L σ, _⟩` for some `σ ∈ zpowers c`, so `bDaux` is a function of `b` alone and is additive
  pointwise: `bDaux (b + b') g = bDaux b g + bDaux b' g`.
  `zLocal` is `eCoh 1 _ _ ((H1π _).hom ⟨bDaux, bDaux_mem⟩)` and `H1π`/`eCoh` are additive, so
  additivity follows from `map_add` plus the pointwise identity of the cocycles (`Subtype.ext rfl`). -/
theorem archPairLocal_add_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
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
    (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b') :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a (b + b')
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b
        + archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b' := by
  -- `b + b'` is again a `⟨c⟩`-cocycle, so the third unfolding lemma applies to it.
  have hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b') :=
    Work.SSGRoute.isCocycleOn_add hb hb'
  rw [archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a (b + b') hsum,
    archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b hb,
    archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b' hb']
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZ_add_snd_local p k Ω K ζ hζ hζK T hT χ hχadd M c hc2 hc1 φ hφ a
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (archPairLocalL_res k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ)
    b b' hb hb' hsum

end Work.SSGRoute.PT
