import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.SSGRoute.canonical_localPairing_with_reciprocity
import Submission.Work.SSGRoute.pt_selmer_relaxed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

CORRECTED STATEMENT (2026-09-25 19:0x): the previous version was declared FALSE (see .fm3_host/reports/lemma-SSGRoute_coker_obstruction.md for the counterexample); this version fixes it. FULL ROUTE: Submission/Work/SSGRoute/DESIGN.md. Shared vocabulary Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available (see DESIGN). Reuse the proved pieces already in Submission/Work/SSGRoute/ (cohomology_bridge, naturality_gluing, eq_zero_on_fixingSubgroup_of_eq_zero_on_split, groupCohomology_res_injective_of_pSylow, H1_tateDual/TateDual/H1Dual/DualMod, local_tate_duality_*).

# Guidance: the Grunwald/Poitou–Tate obstruction with ramification at split primes — genuine new arithmetic

This is SW Lemma 10 + Lemma 12. Given local cocycles α_A at a finite set S of places (pairwise distinct
primes, containing Ram(N) and p) and at all real places (C), there is a class x ∈ H₁(Gal(N/k), E ⊗ μ_p^∨)
such that, for every intermediate level (N₂, E₂, f) where x maps to 0, the pushed data f∘α comes from a
global cocycle unramified outside S ∪ cs(N₂).

**Math.**
- Lemma 10 (PT at H¹): coker(k_S, T, E) ↪ (Ш¹(k_S, S∖T, E'))^∨.
- Lemma 12 + `SSGRoute.bauer_of_chebotarev`: Ш¹(k_S, S∖T, E') ⊆ H¹(Gal(N/k), E') when S ⊇ cs(N).
- Dualise: H₁(Gal(N/k), E ⊗ μ_p^∨) ≅ H¹(Gal(N/k), E')^∨ ↠ Ш¹(…)^∨ ⊇ coker. Take x := a preimage of the
  obstruction of α.
- Naturality in (N₂ ⊆ N, E → E₂) is the paper's diagram before Lemma 10. `groupHomology.map q F` is the dual
  of inflation∘f^∨.

**Trivial-module special case (Grunwald over K).** For E = 𝔽_p^r with μ_p ⊆ K = k this is idèlic CFT:
- Kummer: H¹(k,μ_p) = k^×/p;
- the local pairing on k_v^×/p is perfect (`NK.NUV2.kernelCondition_all`);
- global reciprocity: `NK.CFTLib.artinReciprocityIdeal_proved`;
- existence at prime index: `NK.CFTLib.Existence.classField_exists_primeIndex`. It is **unramified only**.
  Generalise it by dropping the integral-idèle hypothesis; the Kummer S-unit proof recorded in its header
  goes through. Make this a sub-lemma.

Suggested order: prove the trivial case first as a warm-up, then the general E via the PT workshop (see
`sha2_image_of_Hm2.md`: PT-1, PT-2, and the H¹ part of the 9-term sequence, Milne ADT I.4.10). Sylow
reduction first.

**Statement conventions.**
- S is a Finset of places of Ω, one per prime, and C holds one involution per real place.
- x lives in `groupHomology.H1 (Rep.res πN (Rep.of (ofDistribMulAction (ZMod p) G (E ⊗ T))))`, the same
  shape as `flowRep`.
- F is any Rep morphism whose underlying map is f ⊗ id.

**Imports.** Interfaces, `Submission.NK.CFTLib.ArtinReciprocityIdealProved`,
`Submission.NK.CFTLib.Existence.classField_exists_primeIndex`, `Submission.NK.NUV2.kernelCondition_all`,
`Submission.NK.CFTLib.fundamentalClassElement`, `Submission.NK.GlobalCFTdeep.HasseNormTheorem`,
`Submission.Work.AbsoluteKummer.All`.

**Revision 2026-09-25.** Added `hCdisj`: the elements of C are pairwise non-conjugate (one involution per
real place, mirroring `hSdisj`). Without it, two conjugate c, c' carrying different β data contradict the
conjugation invariance of global classes. Reuse the proved pieces already in the workspace:
`cohomology_bridge`, `coker_obstruction_of_level_gluing` (the x = 0 case),
`eq_zero_on_fixingSubgroup_of_eq_zero_on_split` and `groupCohomology_res_injective_of_pSylow`.
-/

namespace Work.SSGRoute



/-
## UPDATE 2 (end of this session): the formal pieces are IN

Proved, sorry-free, in this workspace (both lanes of the assembly may import them):

* `Submission/Work/SSGRoute/tateDual_natural.lean` -- `Work.SSGRoute.tateDual_natural`: a *single*
  family `pad G M : H₁(G,M) ⟶ Dual (H¹(G, M^∨))`, an iso for **every** finite `G` and finite
  `M : Rep (ZMod p) G`, natural in `(φ : G₁ →* G₂, F : M₁ ⟶ Rep.res φ M₂)`; this is exactly the
  ingredient steps 4/5 needed (`H1_tateDual_clean` alone gives only a `Nonempty` iso, and a
  per-`(q,F)` version degenerates to a vacuous rank equality).  Internals: `tatePsi`, `padLin`,
  `padLin_apply_mk`, `padLin_bijective`, `padLin_natural`.
* `Submission/Work/SSGRoute/h1_bridge.lean` -- `Work.SSGRoute.h1_bridge`: Mathlib's
  `groupCohomology.cocycles₁`/`coboundaries₁` of `Rep.of (ofDistribMulAction (ZMod p) G M)` are
  exactly `SSGRoute.IsCocycleOn (MonoidHom.id G) ⊤` / `SSGRoute.IsCoboundaryOn`, and a functional on
  the cocycles killing the coboundaries descends to `groupCohomology.H1`.  Needed to write
  `ω`/`Φ`/`⟨x,·⟩` on the right spaces.
* This file: `Work.SSGRoute.isRamifiedIn_of_le` (`N₁ ≤ N₂` ⇒ ramified in `N₁` ⇒ ramified in `N₂`)
  and `Work.SSGRoute.isSplitIn_of_le` (`N₁ ≤ N₂` ⇒ split in `N₂` ⇒ split in `N₁`, i.e.
  `cs(N₁) ⊆ cs(N₂)`), the two place-monotonicity facts the assembly needs to re-use `hSram` at the
  intermediate level `N₂` and to do the `cs(N) ⊆ cs(N₂)` bookkeeping.
* G3 `Work.SSGRoute.selmer_dual_inflated`: sorry-free in the lead's
  `Submission/Work/SSGRoute/selmer_dual_inflated.lean` (line ~283, plus helpers
  `decomp_closure_normal_except`, `isConjPlace_comap_eq`,
  `eq_zero_on_fixingSubgroup_of_coboundary_on_split`); the same constant is also declared in
  `sha2_dual_control.lean` -- import at most one of the two files.

Still running: `Work.SSGRoute.h1_finite_stage` (finite-coefficient shrinking of step 5; reviewed and
delegated, the file currently holds the prover's scratch).

On G1: its statement file `pt_localPairing.lean` was deleted from disk mid-session.  The assembly
consumes `pair` only through (a) additivity, (b) vanishing on coboundaries, (c) perfectness,
(d) naturality in the coefficient module, (e) global reciprocity -- and `pt_selmer_relaxed` (G2)
already takes (a)+(b)+(c) as `hloc` and (e) as `hrec`.  So the assembly can carry `pair` as an
explicit hypothesis (G2's own signature) and G1 is needed only to instantiate it.

## UPDATE 2026-09-26 (later): what changed on disk, and the parallel lane

* `Work.SSGRoute.selmer_dual_inflated` (G3) is now **PROVED** twice over: in
  `Submission/Work/SSGRoute/sha2_dual_control.lean` (~line 272) and in the lead's
  `Submission/Work/SSGRoute/selmer_dual_inflated.lean` (line ~283, sorry-free, together with its
  helpers `decomp_closure_normal_except`, `isConjPlace_comap_eq`,
  `eq_zero_on_fixingSubgroup_of_coboundary_on_split`).  **The two files declare the same constant**,
  so only ONE of them may be imported in any module.
* The lead's statement file `Submission/Work/SSGRoute/pt_localPairing.lean` (G1) **no longer exists**
  on disk (it was removed after 00:34); G1 is currently *not* available as an import.  G2
  (`Submission/Work/SSGRoute/pt_selmer_relaxed.lean`) still exists, still with `sorry`.
* **A second lane is working on this same node**: `Submission/Work/SSGRoute/coker_obstruction_pt.lean`
  (module `Submission.Work.SSGRoute.coker_obstruction_pt`) re-states `coker_obstruction` under a
  fresh name and derives it from a `GlueableAt` predicate (it proves the pushforward/monotonicity
  part and records the same missing `tateDual_natural`).  **It imports THIS module**, so this file
  can never import it back: if the parallel lane finishes, the only way to use it here is to make
  `coker_obstruction` a *definitional duplicate* (copy the proof) or to have the other lane drop
  its import.
* Formal pieces delegated from this lane (they are needed by BOTH lanes of the assembly):
  * `Work.SSGRoute.tateDual_natural` (spawned; `Submission/Work/SSGRoute/tateDual_natural.lean`) --
    the *natural* family of Tate-duality isomorphisms `H₁(G,M) ≃ₗ (H¹(G,M^∨))^∨`; the proved
    `H1_tateDual_clean` gives only a `Nonempty` iso.
  * `Work.SSGRoute.h1_bridge` (**PROVED**, `Submission/Work/SSGRoute/h1_bridge.lean`):
    Mathlib's `groupCohomology.cocycles₁`/`coboundaries₁` of `Rep.of (ofDistribMulAction (ZMod p) G M)`
    are exactly `SSGRoute.IsCocycleOn (MonoidHom.id G) ⊤` / `IsCoboundaryOn`, and a linear functional
    on the cocycles vanishing on the coboundaries descends to `groupCohomology.H1`.
  * `Work.SSGRoute.h1_finite_stage` (spawned; `Submission/Work/SSGRoute/h1_finite_stage.lean`) --
    the finite-coefficient shrinking for step 5.

## STATUS / PLAN for `Work.SSGRoute.coker_obstruction`  (rewritten 2026-09-26 after DESIGN_PT.md)

The project lead landed `Submission/Work/SSGRoute/DESIGN_PT.md` and stopped the old
"dimension-count local Tate duality" lane (`local_tate_duality*`, `hasPerfectLocalPairing*`): a
pairing manufactured from a dimension count has neither naturality nor reciprocity, so no global
argument can consume it.  The corrected route (the lead's DAG) is

  **G4 = coker_obstruction**  is the assembly of
  * **G1** `Submission/Work/SSGRoute/pt_localPairing`   -- the *canonical* local Tate pairing family
    (one per finite `F_p[Gal(K/k)]`-module `M`), with: additivity on cocycles, vanishing on
    coboundaries, **perfectness**, **naturality in `M`** (via the transpose `f'` of `f ⊗ id_T`),
    orthogonal unramified classes at good places, and **global reciprocity** (the sum over one
    place per prime of `S` and one involution per real place vanishes on global classes).
  * **G2** `Submission/Work/SSGRoute/pt_selmer_relaxed`  -- Poitou–Tate in degree 1, *relaxed at
    `cs(N)`*, for ANY locally-perfect reciprocal pairing: local data `(α, β)` orthogonal to every
    global class of `DualMod p (M ⊗ T)` that is unramified outside `S ∪ cs(N)` and locally trivial
    at `cs(N) ∖ S` glue to a global cocycle `ε` unramified outside `S ∪ cs(N)`.
  * **G3** `Work.SSGRoute.selmer_dual_inflated` (**ALREADY PROVED**, in
    `Submission/Work/SSGRoute/sha2_dual_control.lean`, line ~272; import that module -- do NOT
    import the lead's *statement* file of the same name, it clashes): a continuous `1`-cocycle
    which is a coboundary on the decomposition group of every place split in `N`, off the
    conjugates of `S`, factors through `res k N`.
  * the finite-group Tate duality `Work.SSGRoute.H1_tateDual_clean`
    (`H₁(G,M) ≅ H¹(G,M^∨)^∨`).

### Assembly (the prover's job, G4)

1. Fix the level-`N` local data `(α, β)` and the pair `pair` of G1.  On the space `W` of classes
   `[b₀] ∈ H¹(Gal(N/k), DualMod p (E⊗T))` whose pull-back `b₀ ∘ res k N` satisfies the two Selmer
   conditions of `pt_selmer_relaxed` at level `N`, define
   `ω([b₀]) := ∑_{A∈S} pair (decomp k A) (α A) (b₀ ∘ res k N) + ∑_{c∈C} pair (zpowers c) (β c) (…)`.
   Well-defined by the "kills coboundaries" clause of G1 (a difference of two representatives is a
   coboundary, restricts to a coboundary on `decomp k A`).
2. Extend `ω` to a functional `Φ` on all of `H¹(Gal(N/k), DualMod p (E⊗T))` (`LinearMap.exists_extend`;
   the target `F_p` is a field, so no injectivity hypothesis is needed).
3. `x := (H1_tateDual_clean).symm Φ`.
4. For a level `D = (N₂, q, π₂, E₂, f, F)` with `(groupHomology.map q F 1) x = 0`: by the
   **naturality of the Tate pairing** (piece `Work.SSGRoute.tateDual_natural`, delegated) this is
   equivalent to `Φ ∘ ν = 0`, where `ν` is the pull-back `H¹(Gal(N₂/k), E₂^∨(1)) → H¹(Gal(N/k),E^∨(1))`;
   by the **naturality of `pair` in `M`** (G1) this is `∑ pair (f ∘ α_A) b₂ + ∑ pair (f ∘ β_c) b₂ = 0`
   for all `b₂` satisfying the Selmer conditions at level `N₂` (using `cs(N) ⊆ cs(N₂)`, so a
   level-`N₂` Selmer class is also a level-`N` one after pulling back).
5. Apply **G2** at level `N₂` with `M := E₂⁰`, a *finite* `Gal(K/k)`-stable submodule of `E₂`
   containing `f(E)`, and compose the resulting `ε⁰` with `E₂⁰ ↪ E₂`.  This is where the finiteness
   of `M` in G1/G2 forces the reduction of the arbitrary `E₂` to a finite submodule
   (**piece `Work.SSGRoute.h1_finite_stage`**, to be delegated: `H₁` commutes with filtered colimits
   of coefficient modules, so a vanishing class in `H₁(G₂, E₂⊗T)` already vanishes at a finite
   `Gal(K/k)`-stable stage containing `f(E)`).
6. The `x = 0 / level-N data already glues` case is `coker_obstruction_of_level_gluing` below.

### Formal pieces still missing (besides G1, G2 which are the genuine new arithmetic)

* `Work.SSGRoute.tateDual_natural` (DELEGATED): a *natural* family of isomorphisms
  `H₁(G,M) ≃ₗ (H¹(G,M^∨))^∨`, natural in `(φ : G₁ →* G₂, F : M₁ ⟶ Rep.res φ M₂)`.  The proved
  `H1_tateDual_clean` is only a `Nonempty` iso (no naturality), which is not enough for step 4.
* (**still to delegate**) the *bridge*: Mathlib's `groupCohomology.H1 (Rep.of ρ)` is
  `cocycles₁ ⧸ coboundaries₁` (`groupCohomology.H1π` is an epi with kernel `coboundaries₁`), and
  `cocycles₁`/`coboundaries₁` agree with `SSGRoute.IsCocycleOn`/`IsCoboundaryOn`; needed to make
  sense of `Φ` and of `⟨x, ·⟩` on the right spaces (there is no such bridge for the *Mathlib* Rep
  cohomology yet -- `cohomology_bridge.lean` only bridges to `Work.GroupCohomology.H1`).
* (**still to delegate**) `Work.SSGRoute.h1_finite_stage`: the finite-coefficient reduction of step 5.

### Already proved and reusable here

* `Work.SSGRoute.coker_obstruction_of_level_gluing` (this file, sorry-free): the `x = 0` case.
* `Work.SSGRoute.selmer_dual_inflated` (`sha2_dual_control.lean`).
* `Work.SSGRoute.H1_tateDual_clean`.
* `Work.SSGRoute.naturality_gluing`, `hassePrinciple_h1_cocycles`,
  `eq_zero_on_fixingSubgroup_of_eq_zero_on_split`, `bauer_of_chebotarev`, `ShaCocycles`,
  `cohomology_bridge`.

### Dead ends / warnings

* Do NOT use the orphan lane `local_tate_duality*` / `hasPerfectLocalPairing*` / `exists_perfect_pairing`:
  the pairing is arbitrary (no naturality, no reciprocity); the lead has stopped that lane.
* The lead's statement files `pt_localPairing.lean`, `pt_selmer_relaxed.lean`,
  `selmer_dual_inflated.lean` in this directory *clash by name* with `sha2_dual_control.lean`
  (`Work.SSGRoute.selmer_dual_inflated` is declared in both).  Import at most one of them.
-/
open SSGRoute
open scoped TensorProduct

/-! ## Monotonicity of the place predicates in the extension

Both are used by the assembly of `coker_obstruction`: the hypothesis `hSram` of the theorem is
stated at the top level `N`, while the relaxed Poitou--Tate statement `pt_selmer_relaxed` has to be
applied at the intermediate level `N₂ ≤ N` (step 5 of the STATUS/PLAN above), and
`selmer_dual_inflated` / the "`cs(N) ⊆ cs(N₂)`" bookkeeping of step 4 need the one on split
primes. -/

theorem coker_obstruction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) :
    ∃ x : groupHomology.H1 (Rep.res πN
        (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))),
      ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂],
        K ≤ N₂ → N₂ ≤ N →
        ∀ (q : (N ≃ₐ[k] N) →* (N₂ ≃ₐ[k] N₂)),
        (∀ σ : Ω ≃ₐ[k] Ω, q (SSGRoute.res k N σ) = SSGRoute.res k N₂ σ) →
        ∀ (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K)),
        (∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ) →
        ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
          (f : E →ₗ[ZMod p] E₂), (∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e) →
        ∀ (F : Rep.res πN
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))) ⟶
            Rep.res q (Rep.res π₂
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E₂ ⊗[ZMod p] T))))),
        (∀ z : E ⊗[ZMod p] T, F.hom z = f.rTensor T z) →
        (groupHomology.map q F 1).hom x = 0 →
        ∃ ε : (Ω ≃ₐ[k] Ω) → E₂,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - f (α A σ))) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - f (β c σ))) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  obtain ⟨pair, hclauses, hrec⟩ :=
    canonical_localPairing_with_reciprocity p k Ω K ζ hζ hζK T hT
  -- The canonical pairing is only defined and claused at *local* groups; make it total by setting
  -- it to `0` away from the local groups (where it is never evaluated).
  let pairTot : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p :=
    fun M _ _ _ _ _ H a b =>
      if Work.SSGRoute.H1Pair.IsLocalGroup k Ω H then pair M H a b else 0
  have hpt : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (H : Subgroup (Ω ≃ₐ[k] Ω)), Work.SSGRoute.H1Pair.IsLocalGroup k Ω H →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        pairTot M H a b = pair M H a b := by
    intro M _ _ _ _ _ H hH a b
    change (if Work.SSGRoute.H1Pair.IsLocalGroup k Ω H then pair M H a b else 0) = pair M H a b
    exact if_pos hH
  have hlocal : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (H : Subgroup (Ω ≃ₐ[k] Ω)), Work.SSGRoute.H1Pair.IsLocalGroup k Ω H →
        Work.SSGRoute.H1Pair.PairClauses p K T M (fun a b => pairTot M H a b) H := by
    intro M _ _ _ _ _ H hH
    obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hclauses M H hH
    have hfun : (fun a b => pairTot M H a b) = (fun a b => pair M H a b) :=
      funext fun a => funext fun b => hpt M H hH a b
    rw [hfun]
    exact ⟨h1, h2, h3, h4, h5⟩
  have hnat : ∀ (M M₂ : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
      (f' : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
        Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
      (hff' : ∀ (φ : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
        f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
      (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pairTot M₂ H (fun σ => f (a σ)) b = pairTot M H a (fun σ => f' (b σ)) := by
    intro M M₂ _ _ _ _ _ _ _ _ _ _ f hf f' hff' H a b ha hb
    by_cases hH : Work.SSGRoute.H1Pair.IsLocalGroup k Ω H
    · obtain ⟨-, -, -, -, -, h6, -⟩ := hclauses M H hH
      rw [hpt M₂ H hH (fun σ => f (a σ)) b, hpt M H hH a (fun σ => f' (b σ))]
      exact h6 M₂ f hf f' hff' a b ha hb
    · change (if Work.SSGRoute.H1Pair.IsLocalGroup k Ω H
          then pair M₂ H (fun σ => f (a σ)) b else 0)
        = (if Work.SSGRoute.H1Pair.IsLocalGroup k Ω H
          then pair M H a (fun σ => f' (b σ)) else 0)
      rw [if_neg hH, if_neg hH]
  refine coker_obstruction_of_inputs p k Ω K N hKN ζ hζ hζK E T hT πN hπN S hSfin hSdisj hSram
    C hCinv hC hCdisj α hα β hβ pairTot hlocal hnat ?_
  -- the Poitou--Tate input, with the canonical reciprocity clause
  intro N₂ _ _ hKN₂ hSram₂ M _ _ _ _ _ α' β' hα' hβ' horth
  have hrec' : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
      ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
      (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
      (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
      ∑ A ∈ S', pairTot M (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', pairTot M (Subgroup.zpowers c) a b = 0 := by
    intro a b ha hb hc hd S' hS' hS'd hS'g C' hC'1 hC'2 hC'3
    rw [Finset.sum_congr rfl (fun A hA => hpt M (SSGRoute.decomp k A)
          (Or.inl ⟨A, hS' A hA, rfl⟩) a b),
      Finset.sum_congr rfl (fun c hc' => hpt M (Subgroup.zpowers c)
          (Or.inr ⟨c, hC'1 c hc', rfl⟩) a b)]
    exact hrec M a b ha hb hc hd S' hS' hS'd hS'g C' hC'1 hC'2 hC'3
  exact pt_selmer_relaxed p k Ω K N₂ hKN₂ ζ hζ hζK T hT M (pairTot M) (hlocal M) hrec'
    S hSfin hSdisj hSram₂ C hCinv hC hCdisj α' hα' β' hβ' horth

end Work.SSGRoute
