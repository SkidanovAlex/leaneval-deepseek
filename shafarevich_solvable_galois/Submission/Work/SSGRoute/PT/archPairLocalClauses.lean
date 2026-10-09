import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archPairValueZ_add_left
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The clauses of the local single-level archimedean pairing `PT.archPairLocal`

`flags_2305` defines `G1⁺`'s pairing at an involution group `⟨c⟩` as the **class-formation value**
`χ_{L_c} (ι_{u_c} (levelPair (decompKRestrict) (localUnitsMap) (βc c a) (z_b)))` at one fixed level
`L_c` with `res_{L_c} c ≠ 1` (`PT.exists_level_res_ne_one`), its seam place `u_c = mk (φ|_{L_c})`, and
`z_b = PT.zLocal …` the descended class of the local `⟨c⟩`-cocycle `b`.

This file proves the local clauses of that pairing, in the exact shape `H1Pair.PairClauses` consumes
them, at the **wrapper level** (`PT.archPairLocal` itself, not the value `PT.archPairValueZ`), because
that is the form the glued family of the hub needs.

The wrapper-level proofs all have the same three-step shape (this is the point of the `archPairLocalL`
refactor of `PT/NOTE_s17d_flags2305_local_archPair.md` §19–§20, which removed the
`Classical.choose`-vs-`obtain` instance-key mismatch that blocked them):

1. `rw [archPairLocal_unfold …]` on every occurrence — the right-hand side is the `let`-chain with
   the chosen level `PT.archPairLocalL k Ω K c hc1`, a *single named term* everywhere;
2. install the instances for that very term (`archPairLocalL_fin/_gal`, `NumberField`, and the
   `Algebra`/`IsScalarTower` instances of the inclusion);
3. `exact <value-level lemma> …`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

/-- **Clause (1) at `⟨c⟩` for the local single-level archimedean pairing**: additivity in the first
(`Ext`) variable, on `⟨c⟩`-cocycles. -/
theorem archPairLocal_add_left (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a')
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ (a + a') b
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b
        + archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a' b := by
  rw [archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ (a + a') b hb,
    archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b hb,
    archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a' b hb]
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZ_add_left p k Ω K ζ hζ hζK T hT χ hχadd M c hc2 hc1 φ hφ a a'
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (zLocal p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
      (archPairLocalL_res k Ω K c hc1)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ) b hb
      (archW k Ω K φ) (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ))
    ha ha'

end Work.SSGRoute.PT
