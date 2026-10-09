import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archFamilyLocal
import Submission.Work.SSGRoute.PT.archPairLocalClauses
import Submission.Work.SSGRoute.PT.archPairLocal_add_right
import Submission.Work.SSGRoute.PT.archPairLocal_coboundary
import Submission.Work.SSGRoute.PT.archPairLocal_perfect
import Submission.Work.SSGRoute.PT.archPairLocal_natural
import Submission.Work.SSGRoute.H1Pair.omega_functional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The clauses of the involution half `PT.archFamily` of the hub

`PT.archFamily` is `PT.archPairLocal` at the canonical generator of the involution group, and `0`
off the involution groups and on `⊥`.  This file assembles its clauses in the exact shape
`E7Arch.glueOfTwoHalves` (and hence `H1Pair.PairClauses`) consumes: `archFamily_clauses` (clauses
(1)–(4) at `Subgroup.zpowers c` for every involution `c`, i.e. also at `⊥ = zpowers 1`) and
`archFamily_natural` (clause (5)).

The two cases are `PT.archFamily_zpowers` (nontrivial `c`, where the family *is* `archPairLocal`, so
the concrete clause lemmas `archPairLocal_add_left`/`_add_right`/`_coboundary`/`_perfect` apply) and
`PT.archFamily_bot` (`c = 1`, where the pairing is `0` and every cocycle on `⊥` is already a
coboundary).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **On the trivial group every cocycle is a coboundary**: the cocycle condition at `g = h = 1`
reads `f 1 = f 1 + 1 • f 1`, i.e. `f 1 = 0`, which is exactly the coboundary condition. -/
theorem isCoboundaryOn_bot_of_isCocycleOn
    {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]
    (act : Γ →* G) (f : Γ → M) (hf : SSGRoute.IsCocycleOn act ⊥ f) :
    SSGRoute.IsCoboundaryOn act ⊥ f := by
  refine ⟨0, fun g hg => ?_⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  have h := hf 1 (Subgroup.mem_bot.mpr rfl) 1 (Subgroup.mem_bot.mpr rfl)
  simp only [mul_one, map_one, one_smul] at h
  have h0 : f 1 = 0 := add_left_cancel (by rw [add_zero]; exact h.symm)
  simp [h0]

/-- **Clauses (1)–(4) at an involution group for `PT.archFamily`.** -/
theorem archFamily_clauses
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
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    H1Pair.PairClauses p K T M
      (fun a b => archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b)
      (Subgroup.zpowers c) := by
  by_cases hc1 : c = 1
  · subst hc1
    rw [Subgroup.zpowers_one_eq_bot]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a a' b _ _ _
      simp [archFamily_bot]
    · intro a b b' _ _ _
      simp [archFamily_bot]
    · intro a b _ _ _
      simp [archFamily_bot]
    · intro a ha _
      exact isCoboundaryOn_bot_of_isCocycleOn (SSGRoute.res k K) a ha.1
    · intro b hb _
      exact isCoboundaryOn_bot_of_isCocycleOn (SSGRoute.res k K) b hb.1
  · have hval : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T),
        archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b
          = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc hc1 (φc c hc hc1) (hφc c hc hc1) a b :=
      fun a b => archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc hc1 a b
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a a' b ha ha' hb
      change archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) (a + a') b
        = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b
          + archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a' b
      rw [hval (a + a') b, hval a b, hval a' b]
      exact archPairLocal_add_left p k Ω K ζ hζ hζK T hT χ hχadd M c hc hc1 (φc c hc hc1)
        (hφc c hc hc1) a a' b ha.1 ha'.1 hb.1
    · intro a b b' ha hb hb'
      change archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a (b + b')
        = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b
          + archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b'
      rw [hval a (b + b'), hval a b, hval a b']
      exact archPairLocal_add_right p k Ω K ζ hζ hζK T hT χ hχadd M c hc hc1 (φc c hc hc1)
        (hφc c hc hc1) a b b' hb.1 hb'.1
    · intro a b ha hb hcob
      change archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b = 0
      rw [hval a b]
      exact archPairLocal_coboundary p k Ω K ζ hζ hζK T hT χ hχadd M c hc hc1 (φc c hc hc1)
        (hφc c hc hc1) a b ha.1 hb.1 hcob
    · intro a ha h
      refine (archPairLocal_perfect p k Ω K ζ hζ hζK T hT χ hχinj M c hc hc1 (φc c hc hc1)
        (hφc c hc hc1)).1 a ha.1 ?_
      intro b hb
      rw [← hval a b]
      exact h b ⟨hb, SSGRoute.H1Pair.isLocConstOn_zpowers_of_sq_eq_one c hc b⟩
    · intro b hb h
      refine (archPairLocal_perfect p k Ω K ζ hζ hζK T hT χ hχinj M c hc hc1 (φc c hc hc1)
        (hφc c hc hc1)).2 b hb.1 ?_
      intro a ha
      rw [← hval a b]
      exact h a ⟨ha, SSGRoute.H1Pair.isLocConstOn_zpowers_of_sq_eq_one c hc a⟩

/-- **Clause (5) at an involution group for `PT.archFamily`.** -/
theorem archFamily_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ)
    (hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) b) :
    archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M₂ (Subgroup.zpowers c) (fun σ => f (a σ)) b
      = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a
          (fun σ => f' (b σ)) := by
  by_cases hc1 : c = 1
  · subst hc1
    rw [Subgroup.zpowers_one_eq_bot, archFamily_bot, archFamily_bot]
  · rw [archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M₂ c hc hc1,
      archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc hc1]
    exact archPairLocal_natural p k Ω K ζ hζ hζK T hT χ hχcompat M M₂ f hf f' hff' c hc hc1
      (φc c hc hc1) (hφc c hc hc1) a b ha.1 hb.1

end Work.SSGRoute.PT
