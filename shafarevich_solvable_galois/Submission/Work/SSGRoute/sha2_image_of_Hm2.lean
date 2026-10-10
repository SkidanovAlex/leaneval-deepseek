import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTembedding.ptAssembly
import Submission.Work.SSGRoute.Sha2Lib.pt_core_via_c6
import Submission.Work.SSGRoute.hm2Map_finite_factor
import Submission.Work.SSGRoute.sha2_image_of_Hm2_of_dualControl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- TF-FAST (IsTorsionFree local instance)
/-- Build-speed: `IsAlgClosure k Ω` needs `Module.IsTorsionFree k Ω`, which is otherwise
re-synthesized (about 2 s) at every occurrence. File-local, Prop-valued. -/
private theorem tfFast_isTorsionFree {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] tfFast_isTorsionFree
-- TF-FAST-END
-- (A parallel assembly of the E1a landing clause from the two named dictionaries,
-- `SSGStage.e1aBetaCan_le_ker_via_landing`, is available in
-- `Sha2Lib/e1a_landing_via_dictionary.lean`; the node below does *not* use it — see the comment at
-- the landing-clause step of `E1aInput_of_le_ker`.)

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Ш²(k,E) is a natural image of Ĥ^{-2}(Gal(K/k), E ⊗ μ_p^∨) — genuine new arithmetic

SW §5, "Claim" in Step 2. Here E is a finite 𝔽_p[G]-module (G = Gal(K/k), μ_p ⊆ K) and c is a continuous
2-cocycle locally trivial at every finite place and at every involution. Produce x with: for every G-map f,
Hm2Map(f ⊗ id) x = 0 ⇒ f_*c is a continuous coboundary.

**Math.**
- Ш²(k,E) ≅ Ш¹(k,E')^∨ with E' = Hom(E, μ_p) (Poitou–Tate).
- Ш¹(k,E') ↪ H¹(G, E'): restriction to G_K lands in locally trivial homs G_K → E', which are 0 by
  `SSGRoute.bauer_of_chebotarev`.
- Dualise: H¹(G,E')^∨ ≅ H₁(G, E ⊗ μ_p^∨) = Ĥ^{-2} ↠ Ш²(k,E), naturally in E. The workspace model is
  `Work.Tate.Hm2` = Ĥ^{-1}(G, E^♯); the bridge is `Work.CohomologicalShrinking.exists_bridge`.

**Recommended structure.** One PT workshop, shared with `coker_obstruction`.
- (PT-1) local Tate duality for finite 𝔽_p-modules, from `NK.NUV2.kernelCondition_all`, local Kummer
  (`Work.AbsoluteKummer.kummerEquiv` over the completion) and restriction to the splitting field.
- (PT-2) Tate–Nakayama for C_N:
  - `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_ideleClassGroup'`;
  - `NK.CFTLib.fundamentalClassElement`;
  - `natCard_tateCohomology_eq_of_fundamental_class` and `addEquiv_tateCohomology_of_fundamental_class`
    (in `Submission/Commons/...`; they assume `IsSolvable`, which you remove via Sylow).
- (PT-3) Ш² duality: Milne ADT I.4.10, NSW 8.6.8.
- First reduce by restriction to the fixed field of a p-Sylow. It is injective on the p-primary
  obstruction, and afterwards μ_p ⊆ k.
- HBN in μ_p-coefficients: `NK.GlobalCFTdeep.hbnUnits`, `NK.HassePrinciple.hbnIdele`.

**Imports.** Interfaces, `Submission.NK.GlobalCFTdeep.HasseNormTheorem`,
`Submission.NK.CFTLib.fundamentalClassElement`, `Submission.NK.NUV2.kernelCondition_all`,
`Submission.NK.HassePrinciple.hbnIdele`, `Submission.Work.AbsoluteKummer.All`, and the Commons Tate files.
-/

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct

/-- A one-dimensional `𝔽_p`-module is finite as a type.  (Local copy: importing
`coker_assembly` would clash on the duplicated `selmer_dual_inflated` declarations.) -/
private theorem finite_of_finrank_eq_one' (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
    (LinearEquiv.injective _)


/-
# `sha2_image_of_Hm2` — status and mathematical content

**Statement.**  For a number field `k`, a finite Galois `K/k` with `μ_p ⊆ K` (`p` prime), a
finite `𝔽_p[Gal(K/k)]`-module `E` and its cyclotomic dual `T = μ_p^∨`, and a continuous
`2`-cocycle `c : G_k × G_k → E` which is a coboundary on the decomposition group of every finite
place and on `⟨σ⟩` for every involution `σ`, there is a class `x ∈ Ĥ⁻²(Gal(K/k), E ⊗ T)` such
that for every `G`-equivariant `f : E → E₂` with `Hm2Map (f ⊗ T) x = 0` the pushed-forward
cocycle `f ∘ c` is a continuous coboundary on `G_k`.

**Why it is true.**  `c` represents a class in `Ш²(k,E) = ker(H²(k,E) → ∏_v H²(k_v,E))`.  The
Poitou–Tate duality at degree 2 (Milne, *Arithmetic Duality Theorems*, I.4.10; NSW 8.6.8) is a
canonical perfect pairing `Ш¹(k,E') × Ш²(k,E) → ℚ/ℤ` with `E' = Hom(E,μ_p)`, natural in `E`
(note `E ⊗ T ≅ Hom(E',𝔽_p)`).  Take `x` to be any element whose functional
`H¹(Gal(K/k),E') → 𝔽_p` extends `φ ↦ ⟨φ, c⟩` along the Chebotarev inclusion
`Ш¹(k,E') ↪ H¹(Gal(K/k),E')` — it exists because the dual of an injective map is surjective.
By naturality of the pairing, `Hm2Map(f ⊗ T) x = 0` forces `⟨·, f_*c⟩ = 0` on `Ш¹(k,E₂')`, and
nondegeneracy gives `[f_*c] = 0`, i.e. `f_*c` is a coboundary.  (Consistency check: for `f = id`
the hypothesis is `x = 0`, which correctly forces `c` itself to be a coboundary.)

**What has been proved and what is missing.**

*proved* (verified, no `sorry`):

* `Work.SSGRoute.hassePrinciple_h1_cocycles` — the Chebotarev/Bauer input: a continuous
  `1`-cocycle `G_k → M` (`M` a finite `𝔽_p[Gal(K/k)]`-module) which is a coboundary on the
  decomposition group of every finite place and on `⟨σ⟩` for every involution is inflated from
  `Gal(K/k)` (so `Ш¹ ⊆ H¹(Gal(K/k),·)`);
* `Work.SSGRoute.tateDuality_hm2_dual` (with the sub-library `Work.SSGRoute.TateDual.*`) —
  finite-group Tate duality in the degrees used here:
  `Ĥ⁻²(G, M^∨) ≅ H¹(G,M)^∨`, i.e. `Work.Tate.Hm2 G (DualMod p M) ≅ (H¹(G,M) →+ 𝔽_p)`;
* the elementary bookkeeping lemmas below (push-forward of the cocycle/coboundary conditions
  along a `G`-equivariant map, the normalisations of a `2`-cocycle, `δ ∘ δ = 0`), plus
  `Work.SSGRoute.DualMod` (the dual module `Hom(M,𝔽_p)` with its dual action).

*SUPERSEDED* (orchestrator's `DESIGN2.md`, 2026-09-25 20:25).  This statement is *true* but
*over-formulated*: it asks for a natural surjection `Ĥ⁻²(G,E⊗T) ↠ Ш²(k,E)` defined on **all**
coefficient modules and natural into arbitrary `E₂`, i.e. the full Tate--Poitou duality in degree 2
plus the filtered-colimit extension.  The consumer `stage_global_lifting` only uses `E₂ = E p G n i j`
(a *finite* module), and the intended replacement is the pair

* `Work.SSGRoute.sha2_dual_control` — the arithmetic core ("`c` is controlled by one functional on
  `Ш¹(k,E')`"), replacing `tatePoitou_sha2_image`;
* `Work.SSGRoute.sha2_image_of_Hm2_fin_of_dualControl` — the *assembly* (delegated from this file),
  which turns that functional into the witness `x` for the **finite-`E₂`** version.

The assembly `sha2_image_of_Hm2_of_tatePoitou` proved below in this file is the same formal
argument in the older (Ψ-form) shape; it is kept as the record of the reduction, and it is *not*
sufficient on its own for the unbounded statement because the Tate duality
(`tateDuality_hm2_dual_natural`, `Sha1 ↪ H¹`) is only available for finite coefficient modules: the
infinite-`E₂` case needs naturality of `Ψ` at maps with infinite targets, which is exactly what
`DESIGN2` removes from the design.

**What is proved in this file** (no `sorry`):

* the elementary API for the cocycle/coboundary predicates of `Interfaces.lean` (now in
  `Work.SSGRoute.ShaCocycles`), including push-forward of the conditions along a `G`-equivariant
  map, the normalisations of a `2`-cocycle, and `δ ∘ δ = 0`;
* `Work.SSGRoute.sha2_image_of_Hm2_of_tatePoitou`: the assembly — from the Tate--Poitou input above
  (its hypothesis) it derives the full conclusion of `sha2_image_of_Hm2`.  So *only* the
  Tate--Poitou input separates this file from a complete proof of its main theorem.
-/

/-! ## The reduction to the Tate--Poitou input

The theorem `sha2_image_of_Hm2` below is the assembly of the Tate--Poitou statement
(Ш²(k,E) is naturally a quotient of `Ĥ⁻²(Gal(K/k), E ⊗ μ_p^∨)`, delegated to
`Work.SSGRoute.tatePoitou_sha2_image`) with the Chebotarev/Bauer Hasse principle for continuous
`1`-cocycles (`Work.SSGRoute.hassePrinciple_h1_cocycles`) and the finite-group Tate duality
(`Work.SSGRoute.tateDuality_hm2_dual`).

The lemma `sha2_image_of_Hm2_of_tatePoitou` isolates the assembly: its hypothesis is exactly the
statement of `Work.SSGRoute.tatePoitou_sha2_image` instantiated at the given data, and it derives
the conclusion of `sha2_image_of_Hm2`.  (This is where the Chebotarev/Bauer input enters, through
the surjectivity of `Ψ` for finite coefficient modules: it is exactly the statement that Ш¹(k,E') is
the kernel of the localisation, so that the dual of the injection Ш¹(k,E') ↪ H¹(Gal(K/k),E') — which
is the surjection Ĥ⁻²(G, E ⊗ μ_p^∨) ↠ Ш²(k,E) — is onto.) -/

theorem sha2_image_of_Hm2_of_tatePoitou (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c)
    (hPT : ∃ Ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E],
        Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T) →+ Sha2 p k Ω K E,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Surjective (Ψ E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T)),
        Ψ E₂ (Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x) =
          Sha2Map p k Ω K E E₂ f hf (Ψ E x))) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  obtain ⟨Ψ, hsurj, hnat⟩ := hPT
  obtain ⟨x, hx⟩ := hsurj E (sha2Class p k Ω K E hc hcc hloc hinf)
  refine ⟨x, fun E₂ _ _ _ _ f hf hzero => ?_⟩
  have hn := hnat E E₂ f hf x
  rw [hzero, hx] at hn
  rw [map_zero] at hn
  have hz : Sha2Map p k Ω K E E₂ f hf (sha2Class p k Ω K E hc hcc hloc hinf) = 0 := hn.symm
  rw [Sha2Map_sha2Class] at hz
  exact (sha2Class_eq_zero_iff p k Ω K E₂ _ _ _ _).mp hz

/-! ## The reduction of the unbounded statement to the finite-`E₂` one

`Work.SSGRoute.hm2Map_finite_factor` — the formal core of the reduction: a class in
`Ĥ⁻²(G, E ⊗ T)` which dies in `Ĥ⁻²(G, E₂ ⊗ T)` dies already in `Ĥ⁻²(G, W ⊗ T)` for a factorisation
`f = j ∘ g` of `f` through a *finite* `𝔽_p[G]`-module `W`.  (The vanishing is a membership in the
augmentation ideal of the coinduced module, and since `G` is finite the witness has finite support.)

Hence the *infinite*-`E₂` statement of `sha2_image_of_Hm2` follows from the *finite*-`E₂`
statement `sha2_image_of_Hm2_fin`: given `f : E → E₂` with `Hm2Map (f ⊗ T) x = 0`, factor
`f = j ∘ g` through a finite `W` with the vanishing persisting in `W`; the finite statement gives
`g_* c ∈ B²`, and `f_* c = j_*(g_* c) ∈ B²` because coboundaries push forward
(`Work.SSGRoute.isCoboundary2On_push`).

So the statement of `sha2_image_of_Hm2` is *not* over-formulated: no naturality of the
Tate--Poitou duality at infinite coefficient modules is needed, only its finite-module form
(`Work.SSGRoute.sha2_dual_control`).

## State of this node (2026-09-25, later)

`Work.SSGRoute.hm2Map_finite_factor` is **proved** (axiom-clean) and
`Work.SSGRoute.sha2_image_of_Hm2_of_fin` (the reduction above) is **proved** (axiom-clean): with
`sha2_image_of_Hm2_of_fin` in hand the present file's main theorem is *formal*.

The main theorem `sha2_image_of_Hm2` is therefore proved in this file from the single arithmetic
input `Work.SSGRoute.sha2_image_of_Hm2_fin`, i.e. the chain

  `sha2_image_of_Hm2`  ⟸  `sha2_image_of_Hm2_fin`  ⟸  `sha2_dual_control`  ⟸
  `tatePoitouEmbedding` (the injectivity half of Tate--Poitou duality for *finite* modules)

in which every step is a proved assembly.  The chain passes through two arithmetic
`sorry`s: `Work.SSGRoute.sha2_dual_control` (whose own file already contains the proved assembly
`sha2_dual_control_of_tatePoitouEmbedding`, so it is a *one-line* consequence of the next item) and
`Work.SSGRoute.tatePoitouEmbedding` (`Submission/Work/SSGRoute/tatePoitouEmbedding.lean`, the
injectivity half of Tate--Poitou duality for finite modules), which carries the whole content.
Accordingly `#print axioms Work.SSGRoute.sha2_image_of_Hm2` reports `sorryAx` until
`tatePoitouEmbedding` is proved (equivalently: until `sha2_dual_control` is filled in, which is the
same statement — `sha2_image_of_Hm2` can also be proved directly from `tatePoitouEmbedding` by
inlining that one line).
Two remarks for whoever attacks it:

* the `E₂`-quantifier of this statement is *not* a piece of extra arithmetic: it is discharged by
  `hm2Map_finite_factor`, so the Ψ-form `Work.SSGRoute.tatePoitou_sha2_image` (naturality for
  arbitrary targets) is *unnecessary* for this node and for `sha2_dual_control`;
* consequently the route to attack is the finite-module Tate--Poitou duality only, i.e. the route
  described in the header of `sha2_dual_control.lean` (`E ↪ Coind E`, `Ш²(k, Coind E) = 0` by
  Hasse--Brauer--Noether, degree-one global duality for induced modules, local Tate duality, and a
  diagram chase).  Note that the alternative "dévissage of `Ш¹`/`Ш²` along long exact sequences"
  sketched in some docstrings is *invalid*: `Ш¹` and `Ш²` have no long exact sequences (the local
  conditions destroy exactness), as `DESIGN2.md` notes. -/

theorem sha2_image_of_Hm2_of_fin (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hfin : ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ))) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  obtain ⟨x, hx⟩ := hfin
  refine ⟨x, fun E₂ _ _ _ _ f hf hzero => ?_⟩
  obtain ⟨W, hWadd, hWmod, hWact, hWcomm, hWfin, j, hj, hjinj, g, hg, hfac, hred⟩ :=
    hm2Map_finite_factor p (K ≃ₐ[k] K) E E₂ T f hf x hzero
  letI := hWadd
  letI := hWmod
  letI := hWact
  letI := hWcomm
  haveI := hWfin
  have hcob := hx W g hg hred
  have hpush := isCoboundary2On_push hcob j.toAddMonoidHom hj
  have hEq : (fun σ τ : Ω ≃ₐ[k] Ω => j.toAddMonoidHom (g (c σ τ))) =
      (fun σ τ => f (c σ τ)) := by
    funext σ τ
    exact hfac (c σ τ)
  rwa [hEq] at hpush

/-! ## Reduction to the vanishing of `Ш²` in finite coefficients (the witness `x = 0`)

The node's hypotheses say that the class of `c` lies in the *all-places* Shafarevich group
`Ш²(k,E) = Z²_loc(k,E)/B²(k)`: `c` is a continuous `2`-cocycle which is a coboundary on the
decomposition group of every finite place and on `⟨σ⟩` for every involution.

A locally trivial cocycle which is already a global coboundary pushes forward to a global
coboundary along any `G`-equivariant coefficient map (`isCoboundary2On_push`).  Hence **if
`Ш²(k,M) = 0` for every finite `𝔽_p[Gal(K/k)]`-module `M`, the conclusion of
`sha2_image_of_Hm2_fin` holds with the explicit witness `x = 0`**: for an equivariant `f : E → E₂`
the pushed cocycle `f ∘ c` is again locally trivial (`Z2loc_pushC2_mem`), so it is a global
coboundary by the hypothesis, and the vanishing hypothesis `Hm2Map (f ⊗ T) 0 = 0` is automatic.

This isolates the node's arithmetic content in a form which involves *neither* the local Tate
duality *nor* the global nine-term Poitou–Tate sequence; it is the "Hasse principle for `H²` with
finite `𝔽_p`-coefficients" at *all* places.  The case of *trivially acted* `M` is the classical
Hasse–Brauer–Noether statement (`Work.SSGRoute.sha2_trivial_vanish`). -/

/-- **Reduction to the vanishing of `Ш²` in finite coefficients.**  If every locally trivial
continuous `2`-cocycle with values in a finite `𝔽_p[Gal(K/k)]`-module is a global coboundary, then
the finite-`E₂` conclusion of `sha2_image_of_Hm2_fin` holds, with the witness `x = 0`. -/
theorem sha2_image_of_Hm2_fin_of_sha2vanishing (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c)
    (hZ : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      ∀ c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M, c' ∈ Z2loc p k Ω K M →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ c') :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  refine ⟨0, fun E₂ _ _ _ _ _ f hf _ => ?_⟩
  have hmem : pushC2 p k Ω K E E₂ f c ∈ Z2loc p k Ω K E₂ :=
    Z2loc_pushC2_mem p k Ω K E E₂ f hf c ⟨hc, hcc, hloc, hinf⟩
  have h := hZ E₂ (pushC2 p k Ω K E E₂ f c) hmem
  have hEq : pushC2 p k Ω K E E₂ f c = fun σ τ => f (c σ τ) := by
    funext σ τ
    exact pushC2_apply p k Ω K E E₂ f c σ τ
  rwa [hEq] at h

/-- **The finite form of the node directly from `Work.SSGRoute.tatePoitouEmbedding`** (the
fleet's Tate–Poitou duality, i.e. SW §5 Step 2's Claim).  This route bypasses
`Work.SSGRoute.sha2_dual_control`: the dual-control hypothesis is
`sha2_dual_control_of_tatePoitouEmbedding` applied to the family `Φ` of `tatePoitouEmbedding`. -/
theorem sha2_image_of_Hm2_fin_of_tatePoitouEmbedding
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  haveI hTfin : Finite T := finite_of_finrank_eq_one' (p := p) T hT.1
  obtain ⟨Φ, hΦinj, hΦnat⟩ :=
    tatePoitouEmbedding p k Ω K ζ hζ hζK T hT
  exact sha2_image_of_Hm2_of_dualControl p k Ω K E T c
    (sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c
      ⟨hc, hcc, hloc, hinf⟩ Φ hΦinj hΦnat)

/-! ## A second sufficient condition: the two halves of Milne I.4.10(a)

SW's proof of the Claim (`§5`, Step 2) goes through the single arithmetic input
`Ш²(k,E) ≅ Ш¹(k,E^∨(1))^∨` (Tate–Poitou duality).  The workspace has *two* equivalent packages of
that input:

* `Work.SSGRoute.tatePoitouEmbedding` — the family `Φ` itself (used by `sha2_dual_control`);
* the pair (`Work.SSGRoute.PTembedding.poitouTate_pairing`,
  `Work.SSGRoute.PTembedding.sha_card_euler`) — a natural pairing `Ш¹ × Ш² → 𝔽_p` with zero left
  kernel, plus the global Euler characteristic `#Ш² = #Ш¹`; their combination *is* the family `Φ` by
  the (proved) linear algebra assembly `Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_pairing`.

The lemma below wires the node to the second package as well, so that whichever of the two the fleet
lands first suffices for `sha2_image_of_Hm2`. -/

/-- **The finite form of the node from the two halves of Tate–Poitou duality.**  With a natural
pairing `pair` of the two Tate–Shafarevich groups (zero kernel on the left) and the global Euler
characteristic `#Ш²(k,E') = #Ш¹(k,E'^∨(1))`, the conclusion of `sha2_image_of_Hm2_fin` holds. -/
theorem sha2_image_of_Hm2_fin_of_pairing_and_euler
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcard : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Nat.card (Sha2 p k Ω K E')
          = Nat.card (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T))))
    (pair : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T)) →ₗ[ZMod p]
          (Sha2 p k Ω K E' →ₗ[ZMod p] ZMod p))
    (hleft : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Function.Injective (pair E'))
    (hnat : ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
        [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (a : Sha1 p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))) (b : Sha2 p k Ω K E₁),
        pair E₂ a (Sha2Map p k Ω K E₁ E₂ f hf b)
          = pair E₁ (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a) b)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  haveI hTfin : Finite T := finite_of_finrank_eq_one' (p := p) T hT.1
  -- the family `Φ` of `tatePoitouEmbedding`, from the pairing and the Euler characteristic
  obtain ⟨Φ, hΦinj, hΦnat⟩ :=
    Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_pairing p k Ω K ζ hζ hζK T hT hTfin
      hcard pair hleft hnat
  -- `Φ` is the dual-control hypothesis, hence the node's finite form
  exact sha2_image_of_Hm2_of_dualControl p k Ω K E T c
    (sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c
      ⟨hc, hcc, hloc, hinf⟩ Φ hΦinj hΦnat)


/-! ## The node from an explicit family `Φ`, and from the live inputs (`E1a` + `E9`)

The fleet's route to the atom `Work.SSGRoute.tatePoitouEmbedding` is *route A*: the assembly
`Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_extInputs` produces the family `Φ` out of the two
arithmetic inputs `E1aInput` (node `E1a`, `ext_sha2_bridge`) and `E9Input` (node `E9`,
`pt_sha2_core`).  The lemmas below record the two lines that then close *this* node, so that no
further work is needed on this file once those inputs land:

* `sha2_image_of_Hm2_fin_of_Phi` — the node's finite-`E₂` content from an explicit `Φ` (injective,
  natural in `E`), i.e. exactly the output shape of `tatePoitouEmbedding_of_extInputs` /
  `tatePoitouEmbedding`;
* `sha2_image_of_Hm2_fin_of_extInputs` — the same, from `E1aInput` + `E9Input` directly;
* `sha2_image_of_Hm2_of_extInputs` — the full statement (the `E₂`-quantifier is discharged by
  `hm2Map_finite_factor`). -/

/-- **The node's finite-`E₂` form from an explicit family `Φ`.** -/
theorem sha2_image_of_Hm2_fin_of_Phi
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (Φ : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Sha2 p k Ω K E' →ₗ[ZMod p]
          (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p))
    (hΦinj : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Function.Injective (Φ E'))
    (hΦnat : ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
        [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (b : Sha2 p k Ω K E₁),
        Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
          = (Φ E₁ b).comp
              (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                (DualMod p (E₁ ⊗[ZMod p] T)) f' hf'))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  haveI hTfin : Finite T := finite_of_finrank_eq_one' (p := p) T hT.1
  exact sha2_image_of_Hm2_of_dualControl p k Ω K E T c
    (sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c
      ⟨hc, hcc, hloc, hinf⟩ Φ hΦinj hΦnat)

/-- **The node's finite-`E₂` form from the live inputs `E1aInput` + `E9Input`** (route A of the
PT workshop). -/
theorem sha2_image_of_Hm2_fin_of_extInputs
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE1a : Work.SSGRoute.PTembedding.E1aInput p k Ω K T)
    (hE9 : Work.SSGRoute.PTembedding.E9Input p k ↥K)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  obtain ⟨Φ, hΦinj, hΦnat⟩ :=
    Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_extInputs p k Ω K ζ hζ hζK T hT hE1a hE9
  exact sha2_image_of_Hm2_fin_of_Phi p k Ω K ζ hζ hζK E T hT Φ hΦinj hΦnat c hc hcc hloc hinf

/-- **The full statement of the node from the live inputs `E1aInput` + `E9Input`.** -/
theorem sha2_image_of_Hm2_of_extInputs
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE1a : Work.SSGRoute.PTembedding.E1aInput p k Ω K T) (hE9 : Work.SSGRoute.PTembedding.E9Input p k ↥K)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) :=
  sha2_image_of_Hm2_of_fin p k Ω K E T c
    (sha2_image_of_Hm2_fin_of_extInputs p k Ω K ζ hζ hζK E T hT hE1a hE9 c hc hcc hloc hinf)


/-! ## Route A from the *guarded* E9 core (the shape of `pt_sha2_core`), and the interface remark

`Work.SSGRoute.pt_sha2_core` (`Submission/Work/SSGRoute/pt_sha2_core.lean`) is stated with
`(ζ : K) (hζ : IsPrimitiveRoot ζ p) : ...`, whereas the input consumed by
`PTembedding.tatePoitouEmbedding_of_extInputs` is `PTembedding.E9Input`, a `Prop` indexed by
`(p, k, K)` alone.  At a level `K` that contains a primitive `p`-th root of unity the two agree:
`ζ` does not occur in `pt_sha2_core`'s *conclusion*, so instantiating that conclusion at any root
supplies `E9Input`'s body verbatim.  Since the atom `tatePoitouEmbedding` (and hence this node) has
`hζK : ζ ∈ K` among its hypotheses, route A is closable from the guarded core alone; the two lemmas
below record that reduction.  (The root of `K` itself is obtained from `hζ`, `hζK` by
`IsPrimitiveRoot.of_map_of_injective` applied to the coercion `↥K → Ω`.) -/

/-- **`E9Input` from the `ζ`-guarded E9 core** (the shape of `Work.SSGRoute.pt_sha2_core`), at a
level carrying a primitive `p`-th root of unity: the core's `ζ`-argument does not occur in its
conclusion. -/
theorem E9Input_of_core_with_root (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (hcore : ∀ (ζ' : K) (hζ' : IsPrimitiveRoot ζ' p),
      ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M], (∀ m : M, p • m = 0) →
      ∀ x : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.classesK k K) 1,
        (∀ h : SSGRoute.PTExt.extH M 1,
          SSGRoute.PTExt.IsLocTrivial h → SSGRoute.PTExt.pairK x h = 0) →
        ∃ z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) 1,
          SSGRoute.PTExt.extToClasses z = x)
    (hroot : ∃ ζ' : K, IsPrimitiveRoot ζ' p) :
    Work.SSGRoute.PTembedding.E9Input p k K := by
  obtain ⟨ζ', hζ'⟩ := hroot
  intro M _ hM x hx
  exact hcore ζ' hζ' M hM x hx

/-- **The node's finite-`E₂` form from `E1aInput` and the `ζ`-guarded E9 core** — i.e. from exactly
what the two arithmetic lanes prove, with no appeal to the unguarded `E9Input`. -/
theorem sha2_image_of_Hm2_fin_of_e1a_and_core
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE1a : Work.SSGRoute.PTembedding.E1aInput p k Ω K T)
    (hcore : ∀ (ζ' : ↥K) (hζ' : IsPrimitiveRoot ζ' p),
      ∀ (M : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)) [Finite M], (∀ m : M, p • m = 0) →
      ∀ x : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.classesK k ↥K) 1,
        (∀ h : SSGRoute.PTExt.extH M 1,
          SSGRoute.PTExt.IsLocTrivial h → SSGRoute.PTExt.pairK x h = 0) →
        ∃ z : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k ↥K) 1,
          SSGRoute.PTExt.extToClasses z = x)
    (hroot : ∃ ζ' : ↥K, IsPrimitiveRoot ζ' p)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) :=
  sha2_image_of_Hm2_fin_of_extInputs p k Ω K ζ hζ hζK E T hT hE1a
    (E9Input_of_core_with_root p k ↥K hcore hroot) c hc hcc hloc hinf

/-- **`PTembedding.E1aInput` from the landing clause `PT.e1aBetaCan_le_ker` (node `E1a`).**

The family `β = PT.e1aBetaFamily` is canonical (`PT.e1a_sha2_mem_range_chainC`), injective and
natural in `E` (both *proved*, axiom-clean); the only remaining ingredient of `E1aInput` is that its
values are locally trivial, which is `PT.e1aBetaCan_le_ker` fed through the exactness of the class
formation (`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`).  This is the proof of
`Work.SSGRoute.ssg_E1aInput_of_le_ker` (`stage_global_lifting.lean`), reproduced here so that the
node's own file does not depend on that (currently mid-edit) module. -/
theorem E1aInput_of_le_ker (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    Work.SSGRoute.PTembedding.E1aInput p k Ω K T := by
  have : NumberField ↥K := NumberField.of_module_finite (K := k) (L := ↥K)
  have hcr := fun (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] =>
    Work.SSGRoute.PT.e1a_sha2_mem_range_chainC p k Ω K ζ hζ hζK T hT E
  refine ⟨fun E _ _ _ _ _ => Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E,
    ?_, ?_, ?_⟩
  · intro E _ _ _ _ _
    exact Work.SSGRoute.PT.e1aBetaFamily_injective p k Ω K ζ hζ hζK T hT hcr E
  · intro E _ _ _ _ _ b
    refine Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero (k := k)
      (K := ↥K) ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ?_
    -- Kept on the *filed* statement `PT.e1aBetaCan_le_ker` (a correct statement, and the E1a
    -- lane's own target).  A cleaned-up assembly from the two *named* dictionaries
    -- (`e1aLandingFinCompat` = `e1aBetaCan_localDictionary_fin_compat`, and `e1aLandingInfLocal`)
    -- is available in `Sha2Lib/e1a_landing_via_dictionary.lean` as
    -- `SSGStage.e1aBetaCan_le_ker_via_landing`; it is deliberately *not* used here because the
    -- `e1aBetaCan_localDictionary_fin_compat` statement is the abstract-`H²` formalisation that
    -- `PT/NOTE_e1aBetaCan_localDictionary_fin_injective_analysis.md` §3 flags as possibly
    -- mis-stated, whereas `e1aBetaCan_le_ker` is provable through the E1aClean level-change route.
    exact Work.SSGRoute.PT.e1aBetaCan_le_ker p k Ω K ζ hζ hζK T hT E
      (Work.SSGRoute.PT.e1aChainC_mem_range p k Ω K ζ hζ hζK T hT E (hcr E))
      ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ⟨b, rfl⟩
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF b
    exact Work.SSGRoute.PT.e1aBetaFamily_natural p k Ω K ζ hζ hζK T hT hcr E₁ E₂ f hf F hF b

theorem sha2_image_of_Hm2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  -- **The live route (2026-09-30).**  The node is assembled from the two arithmetic inputs that the
  -- fleet is actually closing:
  --  * `PTembedding.E1aInput`, from the per-place landing clause `PT.e1aBetaCan_le_ker` (node `E1a`)
  --    via the canonical family `PT.e1aBetaFamily` (`E1aInput_of_le_ker` below);
  --  * the E9 core `Work.SSGRoute.pt_sha2_core`, whose only remaining input is clause 3.
  -- This avoids the atom `Work.SSGRoute.tatePoitouEmbedding`, whose proof is written nowhere.
  have hroot : ∃ ζ' : ↥K, IsPrimitiveRoot ζ' p :=
    ⟨⟨ζ, hζK⟩, IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω)
      (by simpa using hζ) (RingHom.injective _)⟩
  exact sha2_image_of_Hm2_of_fin p k Ω K E T c
    (sha2_image_of_Hm2_fin_of_e1a_and_core p k Ω K ζ hζ hζK E T hT
      (E1aInput_of_le_ker p k Ω K ζ hζ hζK T hT)
      (fun ζ' hζ' M _ hM x hx =>
        Work.SSGRoute.pt_sha2_core_clean p (k := k) (K := ↥K) ζ' hζ' M hM x hx)
      hroot c hc hcc hloc hinf)

/-- **The node from the atom `Work.SSGRoute.tatePoitouEmbedding`** (the older route: it needs the
atom's proof to be written, and the atom in turn needs `E1a` and `E9`).  Kept as a named
alternative to `sha2_image_of_Hm2`. -/
theorem sha2_image_of_Hm2_of_tatePoitouEmbedding (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) :=
  sha2_image_of_Hm2_of_fin p k Ω K E T c
    (sha2_image_of_Hm2_fin_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c hc hcc hloc hinf)

end Work.SSGRoute
