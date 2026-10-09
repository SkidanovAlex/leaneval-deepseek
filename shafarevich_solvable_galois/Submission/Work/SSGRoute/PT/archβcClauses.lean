import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archSwapHalf
import Submission.Work.SSGRoute.E1aClean.localDictionary_natural_family
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The clause accessors of the archimedean dictionary `βc`, at a **seam place** `mk (φ|_K)`

`E1aClean.localDictionary_natural_family_arch` has (v2 restatement, 10-05 20:31) the archimedean
conjunct **universal over seam embeddings** `φ`:

`∀ c ≠ 1, ∀ φ, (φ ∘ c = conj ∘ φ) → (βc add) ∧ (βc ker) ∧ (βc onto) ∧ (square with βg) ∧ (natural)`

at the place `archW k Ω K φ = mk (φ|_K)`.  These are exactly the clauses the local single-level
`PT.archPairLocal` consumes (clauses (1)–(5)), so this file reads them off the **single** witness of
the family — the same witness that `PT.finZB`/`finZBg` and `PT.archβc` use.

Every accessor takes the place **as an explicit argument** (`φ`, `hφ`): under the existential form of
v1 the clauses were available only at a `Classical.choose` of the place, and stating them there times
out in `whnf` (`PT/NOTE_s17_archPairDatum_two_lean_obstacles.md` §2).  The v2 form removes the choice,
so each projection below is immediate.

Every declaration carries an **explicit binder list** (no `variable` machinery): a variable unused in
a declaration's type *and* body is silently dropped, which is what produced the
`p : ℕ expected Type` cascade recorded in `PT/NOTE_s17d_flags2305_local_archPair.md` §11.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000

/-- **Additivity of `βc`** at the seam place, on cocycles of `⟨c⟩`. -/
theorem archβc_add (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (b b' : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b') :
    archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) (b + b')
      = archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b
        + archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b' :=
  (((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) E).1
      c hc2 hc1 φ hφ).1) b b' hb hb'

/-- **The kernel of `βc`** at the seam place is the coboundaries on `⟨c⟩`. -/
theorem archβc_eq_zero_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    (archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b = 0 ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :=
  (((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) E).1
      c hc2 hc1 φ hφ).2.1) b hb

/-- **Surjectivity of `βc`** at the seam place. -/
theorem archβc_surjective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (y : Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1) :
    ∃ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
      archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b = y :=
  (((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) E).1
      c hc2 hc1 φ hφ).2.2.1) y

/-- **The square of `βc` with the global dictionary `βg`** at the seam place. -/
theorem archβc_square (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (archW k Ω K φ)
        (SSGRoute.PTExt.extToIdeles (k := k) (archβg p k Ω K ζ hζ hζK T hT E b))
      = archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b :=
  (((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) E).1
      c hc2 hc1 φ hφ).2.2.2.1) b hb hl

/-- **Naturality of `βc`** in the coefficient module, at the seam place (the mirror of `βl`'s
clause; this is what clause (5) of `G1⁺` needs at involution groups). -/
theorem archβc_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
    (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
    (hF' : ∀ (ψ : DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
      (show DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
        (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archβc p k Ω K ζ hζ hζK T hT E2 c (archW k Ω K φ) (fun σ => f (b σ)) =
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype F')).comp
        (archβc p k Ω K ζ hζ hζK T hT E c (archW k Ω K φ) b) (zero_add 1) :=
  (((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT))) E).1
      c hc2 hc1 φ hφ).2.2.2.2) E2 f hf F' hF' b hb

end Work.SSGRoute.PT
