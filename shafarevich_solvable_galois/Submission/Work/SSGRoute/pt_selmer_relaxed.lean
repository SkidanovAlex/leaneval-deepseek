import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.PT.pt_classes_finite
import Submission.Work.SSGRoute.PT.pt_counting_identity_h1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_PT.md (the lead's Poitou–Tate workshop design) + DESIGN.md/DESIGN2.md. Interfaces namespace SSGRoute (do NOT edit). NK.* CFT library available. DualMod p (E⊗T) is Hom(E, μ_p), NOT E⊗μ_p.

# pt_selmer_relaxed  (Poitou–Tate H¹, relaxed at cs(N); DEEP; the arithmetic core of coker_obstruction)

**Statement.** Fix a finite `M` and ANY family `pair` of local pairings on `M` that satisfies `hloc`
(additive, zero on coboundaries, perfect) and `hrec` (global reciprocity). Let `α` be local data at
`S` (one place per prime, containing `Ram(N)` and the places over `p`) and `β` local data at the real
places `C`. Suppose `(α, β)` is orthogonal to every global class `b` of `M' = DualMod p (M ⊗ T)` that
is locally trivial at `cs(N) ∖ S` and unramified outside `S ∪ cs(N)`. Then there is a global
continuous cocycle `ε` with the prescribed local classes at `S ∪ C` that is unramified outside
`S ∪ cs(N)`.

**Why "any pair" is honest, and needs no canonical pairing in the statement.** Let:
- `P = ⊕_{S∪C} H¹(H, M)`, which is finite;
- `W` = the image in `P'` of the dual Selmer classes `b`;
- `V` = the image in `P` of the admissible `ε`.

For the canonical pairing, Poitou–Tate gives `V = W^⊥`. For any other `pair`:
- `hrec` gives `V ⊆ W^{⊥pair}`. Take `S' = S ∪` (finitely many places of `cs(N)` where `ε` ramifies).
  There `b` is a coboundary, so those terms vanish by `hloc`.
- `hloc` perfectness gives `|W^{⊥pair}| = |P|/|W| = |V|`.

So `V = W^{⊥pair}` for every such pair. The prover must still construct the canonical pairing
internally.

**Proof route (DESIGN_PT.md, E9).**
1. Take the level-`K` exact sequence `P¹(M) → Ext¹_G(M', C_K) → …` together with
   `H¹(k,M) = Ext¹_G(M', K^×)` (E1, Hilbert 90).
2. By E5/E6, `φ¹ : Ext¹_G(M',C_K) ↪ H¹(k,M')^∨`. Hence `im(H¹(k,M) → P¹(M)) = ann(loc H¹(k,M'))`
   over all places, in the restricted product.
3. Relax: intersect with the open subgroup
   `U = {x : x_S = 0, x_v unramified for v ∉ S ∪ cs(N), x_v arbitrary on cs(N)}`.
   - `U^⊥ = {y : y_v unramified off S ∪ cs(N), y_v = 0 on cs(N) ∖ S}`, using that `H¹_ur` is its
     own annihilator at good places.
   - `loc(H¹(k,M')) ∩ U^⊥ = loc(B_T)`.
   - The sum `ann + U` is open, hence closed, so no topology beyond finite-dimensionality at each
     place is needed.
4. Transfer to the given `pair` by the counting above.

**Consumer: `coker_obstruction`.**
1. Reduce `E₂` to a finite `G`-stable `E₂⁰ ⊇ f(E)`. `H₁` commutes with directed unions, so the
   hypothesis `map x = 0` already holds at a finite stage.
2. Set `ω(b) = Σ_S pair(α_A, b) + Σ_C pair(β_c, b)` on `B_T(N)`.
3. `selmer_dual_inflated` places `B_T(N)` inside `H¹(Gal(N/k), E')`. Extend `ω` (`LinearMap.exists_extend`).
4. `x := H1_tateDual_clean⁻¹(ω)`.
5. For `(N₂, f)`: `map x = 0` means `ω ∘ inf ∘ f' = 0`. Pair naturality gives
   `ω(f' b₂) = Σ pair(f α, b₂)`. Then `f' b₂ ∈ B_T(N)`, because `cs(N) ⊆ cs(N₂)` and `b₂` is zero
   on `cs(N₂) ∖ S`. So `horth` holds for `(f α, f β)` at level `N₂`.
6. Apply this lemma with `M = E₂⁰` and the pair from `pt_localPairing`.

**Imports (statement).** `Submission.Work.SSGRoute.Interfaces`, `Submission.Work.SSGRoute.DualMod.Main`.

**Size.** Very large, since it sits on the Ext core E0–E9. Relaxation plus counting is about 800
lines on top.
-/

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct


/-!
## Exact reduction of `pt_selmer_relaxed` to three inputs (session 2026-09-26)

The theorem is proved by the counting argument.  With the vocabulary of
`Submission/Work/SSGRoute/PT/pt_selmer_counting.lean`:

* `P = primalClasses p k Ω K M S C` (the product of the local `H¹`-spaces at `S` and `C`),
* `V = primalClassSet` (the classes realized by a global cocycle unramified outside `S ∪ cs(N)`),
* `W = dualClassSet` (the relaxed dual Selmer classes),

and for any family `pair` of local pairings satisfying `hloc`:

* (`V ⊆ W^⊥`) for `x ∈ V` with realizing cocycle `ε` and `y ∈ W` with class `b`,
  `Σ_{A∈S} pair (D_A) (ε) b + Σ_{c∈C} pair (⟨c⟩) (ε) b = 0` — this is
  `Work.SSGRoute.PT.pt_orthogonality_of_realizable` (`PT/pt_canonical_aux.lean`, proved), applied
  with a reciprocal place set `S' ⊇ S`; the existence of `S'` is
  `Work.SSGRoute.PT.exists_good_placeSet` (`PT/exists_good_placeSet.lean`), proved from
  `Work.SSGRoute.PT.vanishingInertia_finite` (`PT/vanishingInertia_finite.lean`, proved: a locally
  constant cocycle vanishes on the inertia of all but finitely many places) plus the local
  conditions `hεinertia`, `hbsplit`, `hbnon` and `hSram`;
* the pairing `β` on `P × P'` is built from the *given* `pair`: at each local group of `S ∪ C` the
  clauses of `hloc` make `pair H` descend to a bilinear, both-sides non-degenerate pairing on
  `H¹(H,M) × H¹(H,M^∨(1))` (`Work.SSGRoute.PT.exists_pairing_on_H1loc`,
  `PT/pt_counting_assembly.lean`, proved), and `β` is their sum
  (`Work.SSGRoute.PT.productFormFun`, with additivity `productFormFun_add_left/right` and
  non-degeneracy `productFormFun_ndL/ndR`, and the identification
  `productFormFun_classMap` with the sums of the original local pairings);
* (`W^⊥ ⊆ V`) the counting identity `|V| · |W| = |P| =
  Work.SSGRoute.PT.pt_selmer_counting_identity` (`PT/pt_selmer_counting_identity.lean`; the Euler
  characteristic of the relaxed Selmer complex, Milne ADT I.4.10 / NSW 8.6.8) converts
  `V ⊆ W^⊥` into `V = W^⊥` through the abstract counting step
  `Work.SSGRoute.PT.wbot_le_of_additive` (`PT/pt_counting_assembly.lean`, proved), using the
  cardinality form `natCard_counting` (`|V| · |W| = |P|` in submodule form);
* `horth` is exactly the statement that the class of `(α,β)` is orthogonal to `W`, so
  `wbot_le_of_additive` returns `primalClassOf α β ∈ primalClassSet`; `mem_primalClassSet_iff`
  then produces a global cocycle realizing the *class*, and
  `sub_mem_coboundaries_of_toClass_eq` upgrades the class equality to the coboundary conditions
  for the originally given `(α,β)`.

Everything except the labelled input (the counting identity) is proved in the workspace, and the
wiring of the last bullet is **done** in this file: `PT.pt_selmer_relaxed_assembly` (below) is the
statement of the target with the pair as an explicit parameter, and `pt_selmer_relaxed` is a
one-line consequence of it.

## Status (session of 2026-09-27, this file)

> **Update (2026-09-28).**  The residual input is now taken from the *counting lane's development
> file*: `have hcount := pt_counting_identity_h1 …` (line marked "the counting lane's development
> file"), whose target `Work.SSGRoute.PT.CountingIdentity` **is** the proposition of
> `PT.pt_selmer_counting_identity` by definition (`PT/pt_canonical_assembly.lean`, `def
> CountingIdentity`).  `PT/pt_counting_identity_h1.lean` is the actively developed file (its own
> account: the whole proof except step 3, the exactness `W^⊥ ⊆ V`); `PT/pt_selmer_counting_identity`
> is the older *statement* file holding the same proposition.  So this node closes as soon as
> **either** file is `sorry`-free; nothing in *this* file needs to change when that happens.
> Also measured this session: `Work.SSGRoute.phi1_mono_sylow_in` (E6Ω) is now **axiom-clean**
> (`[propext, Classical.choice, Quot.sound]`), and `Work.SSGRoute.H2loc_inertia_subsingleton`
> (missing module, supplied by this lane) plus `Work.SSGRoute.inertiaStructureOfFinPlace_inf` build
> axiom-clean.
>
> **Update (2026-09-29 ~01:00, measured).**  `lake build
> Submission.Work.SSGRoute.pt_selmer_relaxed` succeeds and `#print axioms
> Work.SSGRoute.pt_selmer_relaxed = [propext, sorryAx, Classical.choice, Quot.sound]`, the
> `sorryAx` coming from `PT.pt_counting_identity_h1` alone.  Frontier, measured on disk:
> * `Work.SSGRoute.milne210` (= Milne *ADT* I.2.10, the `hartin` input of E7a) is **proved and
>   axiom-clean** (`[propext, Classical.choice, Quot.sound]`): `artin_relation_charP` (Serre 16.1
>   Thm 33, via Brauer's decomposition map) → `artin_brauer_operator` → `milne210`.  See
>   `SSGRoute/MISSING_MODULES_STATUS.md`.
> * `PT/E9Nodes/e9_local_decomposition.lean` is **proved** (0 `sorry`, 2026-09-28 20:27) — the E9
>   lane's local-decomposition node.  The E9 files above it (`pt_sha2_core`,
>   `local_phi_realization_in`) are *mid-edit*: `local_phi_realization_in.lean` currently fails to
>   elaborate (syntax errors at 00:48), so `pt_sha2_core.olean` does not exist — its 0-`sorry`
>   marker is therefore not yet a proof.  Do not repair: it is an active lane's work in progress.
> * E7a is re-pointed by the lead from the `ε`-valued Milne I.2.8 to `SSGRoute/euler_symm_input`
>   (`χ_D(M) = χ_D(M^∨(1))`, live: `EulerSymm/*`), so `PT/euler_notResidueChar_proof`,
>   `hs_twoRow_decomp` and `euler_trivial_module` are *not* on the critical path any more.
> * The counting node's own measured remainder (`PT/PT_COUNTING_IDENTITY_STATUS.md` §8.4) is:
>   (1) `hAB`/`hBcl` at `ptA`/`ptB'` (node E9), (2) the local clauses
>   `hβL`,`hβR`,`hβ0fin`,`hUnram` (E7 local Tate duality, with the `p = 2` annihilator-form
>   caveat of its §6), (3) the transports `e`,`e'` and `hcompat` (canonicity of the local pairing).
>   Given them, `PT.converse_of_relaxation` + `PT.countingIdentity_of_reciprocity_and_converse`
>   (both in `PT/pt_counting_identity_h1.lean`) give `CountingIdentity`, hence this node.

* `pt_selmer_relaxed` is **proved modulo exactly one statement**,
  `Work.SSGRoute.PT.pt_selmer_counting_identity` (`PT/pt_selmer_counting_identity.lean`), which is
  still a `sorry`.  `#print axioms Work.SSGRoute.pt_selmer_relaxed` therefore reports `sorryAx`;
  every other ingredient of the proof (`pt_classes_finite`, `natCard_counting`,
  `wbot_le_of_additive`, `counting_step_concrete`, the reciprocity `pt_orthogonality_of_realizable`,
  the finiteness lemmas, and the pairing calculus of `PT/pt_counting_assembly.lean` /
  `PT/pt_relaxed_assembly.lean`) is axiom-clean.

* Why the assembly had to be re-done in this file rather than taken from
  `PT.pt_canonical_relaxed_of_inputs`: that theorem *hides* its pair in an `∃`, so its output is
  `Realiz (witness) α β` and the witness does not reduce definitionally to the given `pair`
  (`Exists.witness` is opaque for a theorem application).  `PT.pt_selmer_relaxed_assembly` is the
  same argument with the pair as an explicit parameter.

* `PT.pt_selmer_counting_identity` is *equivalent* to this node (given the proved assembly and the
  proved reciprocity), and equivalent in turn to the middle exactness of the relaxed Poitou–Tate
  sequence — the single deepest node of the Shafarevich development.  Its remaining inputs, as of
  this session, are the arithmetic nodes `E4Ω` (`phi0_trivial_epi_in`), the two local nodes `E7`
  (`local_tate_duality_euler`, `local_tate_duality_02`) and the assembly `E9`, plus a few gaps
  inside `Submission/NK`.  In particular `E6` (`phi1_mono_sylow`/`phi1_mono_sylow_in`), `E1`
  (`ext_h1_bridge`) and `E8` (`brauer_single_place`) are *proved on disk* but still depend on
  `sorryAx` through `phi0_trivial_epi_in` and through the `NK` gaps, so the chain is not yet
  axiom-clean.

* **Axiom hygiene of the chain (measured).**  A declaration with no literal `sorry` can still be
  `sorryAx`-tainted through its imports.  Measured with `#print axioms` (this workspace, this
  session): `Work.SSGRoute.brauer_single_place` (E8), `Work.SSGRoute.PT.pt_classes_finite`,
  `PT.natCard_counting`, `PT.wbot_le_of_additive` are clean (`propext`, `Classical.choice`,
  `Quot.sound` only), while `Work.SSGRoute.phi1_mono_sylow_in`, `Work.SSGRoute.phi1_mono_sylow` (E6),
  `Work.SSGRoute.ext_h1_bridge` (E1) and `Work.SSGRoute.pt_selmer_relaxed` are `sorryAx`-tainted.
  The files in the import closure of the E5/E6 lane that still contain a literal `sorry` are
  `Submission.Work.SSGRoute.phi0_trivial_epi_in` (E4Ω), `Submission.Work.SSGRoute.level_family_of_delta`,
  `Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B`, `Submission.NK.CFTLib.HR.TransferAux.transferClass`,
  `Submission.NK.NumberTheory.NumberField.Completion.exists_galois_unramified_extension_of_inertiaDeg`,
  `Submission.NeukirchUchida.Core` and `Submission.Shafarevich`; for `ext_h1_bridge` the only one in
  its closure is `Submission.Shafarevich`.  So closing E4Ω and the listed `NK`/`NeukirchUchida` gaps
  is part of making this node axiom-clean, and syntactic "no `sorry` here" scans of the ledger
  overstate the state of the chain.

* **The relaxation, made concrete (this session).**  Mathlib's restricted product
  (`Mathlib.Topology.Algebra.RestrictedProduct`, `Πʳ i, [X i, U i]`) is exactly the setting of the
  relaxation, and the piece that this node still owed has been isolated and dispatched:

  * `Submission/Work/SSGRoute/PT/pt_restrictedPairing.lean` (this session, sorry-free) defines the
    pairing `Πʳ [X i,U i] → Πʳ [Y i,U' i] → 𝔽_p` (`restrictedPairing`) and proves its computation
    rule `restrictedPairing_eq_sum` (the sum over *any* finite set outside which both arguments are
    unramified), using that the "unramified" subgroups annihilate each other;
  * `Work.SSGRoute.PT.restrictedProduct_relaxation` (`PT/restrictedProduct_relaxation.lean`) is the
    relaxation step itself, **proved and axiom-clean** (with the supporting material
    `PT/pt_localPairingDual.lean`, `PT/pt_piPairingDual.lean`, `PT/pt_isCompact_separation.lean`):
    from the *unrestricted* exactness `A = B^⊥` (in the restricted products) plus the two
    compactness inputs, it produces a class `a ∈ A` unramified off `Ram` with prescribed
    `T`-coordinates, for every `x` orthogonal to the Selmer part of `B`.  With it `V = W^⊥` — hence
    the counting identity, via `natCard_annihilator_mul`/`natCard_counting` — follows from the
    unrestricted middle exactness, and no Euler characteristic is needed.

    What the *instantiation* of that statement with the arithmetic data still needs: (a) the
    "unramified" subgroups `U_A ≤ H1loc(D_A,M)` (definable as the image of the inertia-vanishing
    locally constant cocycles; `U'_A` is then *defined* as its annihilator, so `hβ0`/`hU` are free),
    (b) the localisation of the global classes into the restricted product over the finite places
    and the involutions (needs "a global locally constant cocycle is unramified outside a finite
    set", via `exists_levelSub_le_of_isOpen`), (c) the *compactness* of the image `A` — this is the
    one genuinely new formal ingredient, since the workspace's `H1contS` carries no topology: one
    has to give `Z¹cont ⧸ B¹cont` the profinite quotient topology (`Z¹cont` is closed in the compact
    space of maps `G → M` and `B¹cont` is the image of the finite group `M`), and (d) the
    *exactness* `hAB` itself, i.e. the unrestricted Poitou–Tate middle exactness in this
    (H¹-local-product) vocabulary, which is the `E9` lane's content.

* **A watch-out on the shape of the Selmer conditions (cocycle level vs class level).**  This node
  (like `PT.primalSelmer`, `PT.dualSelmer` and `PT.IsRealizableClass`) states the unramified
  conditions *on the cocycle*: `ε σ = 0` for `σ ∈ I_B`, not "the local *class* `[ε|D_B]` is
  unramified".  The two differ: for a global class whose local class at `B` is unramified one gets
  `ε σ = σ m_B - m_B` for `σ ∈ I_B` with a local parameter `m_B`, and a *global* coboundary shifts
  all parameters `m_B` by one common `m ∈ M`; so the cocycle-level Selmer group can be strictly
  smaller than the class-level one, and the classical (class-level) Poitou–Tate statements do not by
  themselves give the cocycle-level counting identity.  Consumers of this node should check where
  their Poitou–Tate input sits: the `E8`/annihilator lane (`brauer_single_place`, `localGlobal_annihilator`)
  is natively at the cocycle level, while the `Ext`-core lane (`E1`–`E9`, `tatePoitouEmbedding`) is
  class-level and would need the bridge; the counting route via `natCard_counting` only needs the
  *counting identity as stated here* (cocycle level), which is pairing-independent.

* The one piece of this node that is *not* in any of the arithmetic lanes and that is still missing
  is the **relaxation** (`DESIGN_PT.md` §3, step 3): the passage from the *unrestricted* middle
  exactness `im(loc_M) = ann(loc_{M'})` in the restricted product to the *local-condition* form
  used here.  It is a closedness/openness argument: with
  `U = {x : x_v = 0 (v ∈ S ∪ C), x_v unramified for v ∉ S ∪ cs(N), x_v arbitrary on cs(N)}` one has
  `(A + U)^⊥ = loc_{M'}(H¹) ∩ U^⊥ = im(dual Selmer)` for `A = im(loc_M)`, so `A + U` is open hence
  closed, and every `x` orthogonal to the dual Selmer lies in `A + U`, i.e. agrees with a class of
  `A` on `S ∪ C` and is unramified outside `S ∪ cs(N)`.  Formalising it needs the restricted-product
  topology, which the workspace does not yet have.

## Session 3 (2026-09-27): the class-level/cocycle-level bridge, and the unramified subgroup

New module of this lane (sorry-free, axiom-clean):
`Submission/Work/SSGRoute/PT/pt_unramifiedSub.lean`, whose namespace is `Work.SSGRoute`:

* `Work.SSGRoute.unramifiedSub p k Ω K M B ≤ H¹(D_B, M)` — the **unramified subgroup**: the image
  in `H¹(D_B,M)` of the locally constant cocycles on `D_B` that vanish on the inertia subgroup
  `I_B` (`Work.SSGRoute.inertiaTrivialCocycles`);
* `Work.SSGRoute.mem_unramifiedSub_iff` and `Work.SSGRoute.exists_toClass_mem_unramifiedSub` — its
  class-level characterisation (a class is unramified iff some representative vanishes on `I_B`);
* **`Work.SSGRoute.toClass_mem_unramifiedSub_iff`** — the *bridge*: at a place `B` unramified in
  `K`, the local class of a locally constant cocycle `b` is unramified **iff** `b σ = 0` for all
  `σ ∈ I_B` (because `I_B` then acts trivially on the `Gal(K/k)`-module `M`, so that every
  coboundary vanishes on `I_B`).  This is the resolution of the cocycle-level/class-level watch-out
  recorded above: the two formulations of the Selmer conditions agree on the Selmer range, i.e. at
  the finite places outside the conjugacy classes of `S`
  (`Work.SSGRoute.toClass_mem_unramifiedSub_iff_of_not_isConjPlace`, and the consumer-shaped
  `Work.SSGRoute.dualSelmer_localClass`, which translates `PT.IsDualSelmerClass` into class form);
* `Work.SSGRoute.exists_finset_localClass_unramified` — a *global* locally constant cocycle has
  unramified local class at all but finitely many finite places (class-level form of
  `PT.vanishingInertia_finite`).  This is what makes the localisation of a global class land in the
  *restricted* product `Πʳ_B [H¹(D_B,M), H¹_ur(D_B,M)]`.

These are the "no arithmetic" prerequisites of the relaxation instantiation (the step that converts
the all-places middle exactness into this node).  The remaining ingredients of that instantiation
are: (i) the canonical local pairing's clauses (node `E7`), in particular its class-level clause
(6) (unramified classes pair trivially — the consumer of the local pairing in the relaxation), (ii)
the middle exactness `A = B^⊥` in the restricted product (node `E9`), and (iii) compactness of the
image `B` — note that in this workspace's model `Z¹cont` is a *countable union of finite sets* (the
locally constant cocycles factoring through some open subgroup), so `PT.restrictedProduct_relaxation`'s
compactness hypothesis must be established by hand (via the quotient topology on the compact space
of cocycles) or the lemma restated for `B` closed.

Also added to that module in this session: `Work.SSGRoute.pairing_annihilates_unramifiedSub`
(the *class-level* form of clause (6) of the canonical local pairing: `Bh x y = 0` for `x`, `y` in
the two unramified subgroups), which is the form in which the relaxation is applied with
`U'_A := (U_A)^⊥`.

**A design warning for the restricted-product instantiation (found by review, this session).**  The
index type of the restricted product `Πʳ` must be one place *per prime of `k`* (one per
`IsConjPlace`-class), **not** the type of all finite places of `Ω`.  The cofinite ("unramified
outside a finite set") condition is false for the latter: the bad set is a union of full
`Gal(Ω/k)`-orbits, each infinite when non-empty, so one ramified prime already produces infinitely
many bad places of `Ω`.  The instantiation therefore has to index by the conjugacy quotient, which
needs the conjugacy-invariance of the local conditions (`Work.SSGRoute.PT.inertiaVanishing_conj`,
dispatched) and the identification of the local `H¹`'s at conjugate places
(`h1loc_conjLinearMap`).  `Work.SSGRoute.exists_finset_localClass_unramified` is the same statement
already in the "one place per class" form.

**Second design warning (this session): the compactness hypothesis of
`PT.restrictedProduct_relaxation` is a genuine obstruction, not a formality.**
`restrictedProduct_relaxation` takes `hBcomp : IsCompact (B : Set (Πʳ …))`, where `B` is the image
of the *global* dual classes in the restricted product over all places.  That image is a countable
subgroup of the compact restricted product, and closedness is *not* automatic: for `M' = 𝔽_p`
trivial and `k = ℚ` one gets `B = ℚ*/ℚ*^p ↪ Πʳ_v ℚ_v*/ℚ_v*^p`, a countable subgroup of a compact
group (the same shape as `ℚ ⊆ 𝕋`, which is dense and not closed); its closedness is a form of the
statement one is trying to prove, not a consequence of it.  So the relaxed route has to be run
either with the *level* structure (the finite quotients `G_{S'}` of `G_k`, where the images live in
*finite* products and compactness is trivial — this is also what the counting identity itself
reflects: `P = ∏_{S∪C} H¹` is a finite set, `PT.pt_classes_finite`), or with `B` closed *by
construction*.  Everything the module proved above is agnostic to that choice.

**Session 3 (continued): the localisation into the restricted product, and the class-level Selmer
conditions.**  Four further modules were added, all sorry-free and axiom-clean:

* `Submission/Work/SSGRoute/PT/inertiaVanishing_conj.lean` (delegated, proved):
  `Work.SSGRoute.PT.inertiaVanishing_conj` — for a global cocycle `b`, the inertial vanishing
  condition `b σ = 0 (σ ∈ I_B)` at a place `B` unramified in `K` is invariant under replacing `B` by
  a conjugate place;
* `Submission/Work/SSGRoute/PT/unramifiedSub_conj.lean`:
  `Work.SSGRoute.toClass_mem_unramifiedSub_conj` — the class-level form of the same invariance;
* `Submission/Work/SSGRoute/PT/selmer_classLevel.lean`:
  `Work.SSGRoute.PT.hSram_of_hSram_N`, and the translation theorems
  `Work.SSGRoute.PT.isRealizableClass_iff_classLevel` /
  `Work.SSGRoute.PT.isDualSelmerClass_iff_classLevel` — the Selmer predicates of
  `PT/pt_selmer_counting.lean` are *literally* the class-level ones in the Selmer range (the
  cocycle-level/class-level bridge of the watch-out above), so a class-level duality statement can
  be fed directly into this vocabulary;
* `Submission/Work/SSGRoute/PT/pt_localisationRestricted.lean`:
  `Work.SSGRoute.PT.finPlaceConjSetoid` (the setoid of conjugacy of finite places),
  `Work.SSGRoute.PT.exists_restrictedProduct_localization` and its additive form
  `…_add` — **the localisation of a global locally constant cocycle into the restricted product
  `Πʳ_v [H¹(D_v, M), H¹_ur(D_v, M)]`, indexed by the finite places of `Ω` *up to conjugacy*** (i.e.
  by the primes of `k`, as the design warning above requires), with the computation rule "the `v`-th
  component is the local class of `b` at the representative of `v`".  This is precisely the
  localisation step that `PT/pt_counting_identity_h1.lean` (session 5) lists as still missing from
  the relaxation *instantiation*; the remaining missing piece of that instantiation is the
  compactness/closedness of the image of the global classes.

The target itself is unchanged: `pt_selmer_relaxed` still rests on exactly one statement,
`Work.SSGRoute.PT.pt_selmer_counting_identity`.

-/


namespace PT

open scoped TensorProduct Pointwise
open Classical

/-! ## The assembly with the pair given explicitly

`PT.pt_canonical_relaxed_of_inputs` states its conclusion as `∃ pair, … ∧ Realiz pair α β`; the
pair is existentially hidden, so its output cannot be used for the *given* `pair` of the target
(the witness does not reduce to the given pair definitionally).  The present theorem is the same
assembly with the pair as an explicit parameter, which is what `pt_selmer_relaxed` needs. -/

section Assembly

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

local instance instDualAddCommGroup' :
    AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

local instance instDualModule' :
    Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

local instance instDualDistribMulAction' :
    DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance

local instance instDualSMulCommClass' :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

theorem pt_selmer_relaxed_assembly
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      ((∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) ∨
        (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
      (∀ (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair H (a + a') b = pair H a b + pair H a' b) ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
        pair H a (b + b') = pair H a b + pair H a b') ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
        pair H a b = 0) ∧
      (∀ a : (Ω ≃ₐ[k] Ω) → M,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
          pair H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
          pair H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b))
    (hrec : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
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
      ∑ A ∈ S', pair (SSGRoute.decomp k A) a b + ∑ c ∈ C', pair (Subgroup.zpowers c) a b = 0)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        SSGRoute.IsSplitIn k N B → SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ¬ SSGRoute.IsSplitIn k N B → ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S, pair (SSGRoute.decomp k A) (α A) b + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) :
    ∃ ε : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
      (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  -- `hT` makes `T` a line over `𝔽_p`, hence a finite type (needed by the finiteness of the local
  -- class spaces and by the arithmetic at the Tate dual).
  haveI hTfin : Finite T := by
    haveI : Module.Free (ZMod p) T := inferInstance
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
      rw [hT.1, Module.finrank_self]
    exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
      (LinearEquiv.injective _)
  -- Finiteness of the two local class spaces at `S ∪ C`.
  obtain ⟨hfinP, hfinQ⟩ := pt_classes_finite p k Ω K T M S hSfin C hCinv
  -- The Poitou–Tate counting identity: the single arithmetic input of the assembly.
  -- The counting identity, taken from the counting lane's development file
  -- (`PT.pt_counting_identity_h1`, whose target `PT.CountingIdentity` *is* this proposition by
  -- definition), so that this node closes as soon as that file is sorry-free; its statement
  -- file `PT.pt_selmer_counting_identity` holds the same proposition.
  have hcount : Nat.card {x : Work.SSGRoute.PT.primalClasses p k Ω K M S C //
      Work.SSGRoute.PT.IsRealizableClass p k Ω K N hKN M S C x} *
      Nat.card {y : Work.SSGRoute.PT.primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C //
        Work.SSGRoute.PT.IsDualSelmerClass p k Ω K N hKN T M S C y} =
      Nat.card (Work.SSGRoute.PT.primalClasses p k Ω K M S C) :=
    pt_counting_identity_h1 p k Ω K N hKN ζ hζ hζK T hT M S
      hSfin hSdisj hSram C hCinv hC hCdisj
  have hloc' : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H :=
    fun H hH => hloc H hH
  let B := localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc'
  have hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A) →
      B (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b) = pair (SSGRoute.decomp k A) a b := by
    intro A hA a b ha hb
    exact localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inl ⟨A, hSfin A hA, rfl⟩) a b ha hb
  have hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c) →
      B (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b) = pair (Subgroup.zpowers c) a b := by
    intro c hc a b ha hb
    exact localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inr ⟨c, hCinv c hc, rfl⟩) a b ha hb
  have hndL : ∀ A ∈ S, ∀ x : H1loc p k Ω K M (SSGRoute.decomp k A),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A), B (SSGRoute.decomp k A) x y = 0) → x = 0 :=
    fun A hA => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hndLc : ∀ c ∈ C, ∀ x : H1loc p k Ω K M (Subgroup.zpowers c),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c), B (Subgroup.zpowers c) x y = 0) → x = 0 :=
    fun c hc => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inr ⟨c, hCinv c hc, rfl⟩)
  have hndR : ∀ A ∈ S, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A),
      (∀ x : H1loc p k Ω K M (SSGRoute.decomp k A), B (SSGRoute.decomp k A) x y = 0) → y = 0 :=
    fun A hA => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hndRc : ∀ c ∈ C, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c),
      (∀ x : H1loc p k Ω K M (Subgroup.zpowers c), B (Subgroup.zpowers c) x y = 0) → y = 0 :=
    fun c hc => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc' (Or.inr ⟨c, hCinv c hc, rfl⟩)
  have hcard : Nat.card (primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M)
        (S := S) (C := C)) *
      Nat.card (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
        (S := S) (C := C)) = Nat.card (primalClasses p k Ω K M S C) :=
    natCard_counting (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN) (T := T) (M := M)
      (S := S) (C := C) hCinv hcount
  have hVW : ∀ x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M)
        (S := S) (C := C),
      ∀ y : dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
        (S := S) (C := C),
        productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
          B x y.1 = 0 := by
    intro x hx y
    rw [mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
      (M := M) (S := S) (C := C) hCinv x] at hx
    obtain ⟨α', β', ε, hcls, hε1, hε2, hεα', hεβ', hεunr⟩ := hx
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp y.2
    have hby : dualClassMap (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
        (C := C) b.1 = y := hb
    rw [← hby, ← hcls]
    have hεmem : ε ∈ primalSelmer p k Ω K N M S := ⟨hε1, hε2, hεunr⟩
    have hεα'lc : ∀ A ∈ S, (fun σ => ε σ - α' A σ) ∈
        lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
      fun A hA => coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A)
        ((mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mpr (hεα' A hA))
    have hεβ'lc : ∀ c ∈ C, (fun σ => ε σ - β' c σ) ∈
        lcCocycles p k Ω K M (Subgroup.zpowers c) :=
      fun c hc => coboundaries_le_lcCocycles p k Ω K M (Subgroup.zpowers c)
        ((mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mpr (hεβ' c hc))
    have hα'lc : ∀ A ∈ S, α' A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) := by
      intro A hA
      have hεA : ε ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
        ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
      have heq : α' A = ε - (fun σ => ε σ - α' A σ) := by
        ext σ; simp only [Pi.sub_apply]; abel
      rw [heq]
      exact Submodule.sub_mem _ hεA (hεα'lc A hA)
    have hβ'lc : ∀ c ∈ C, β' c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) := by
      intro c hc
      have hεc : ε ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
        ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
      have heq : β' c = ε - (fun σ => ε σ - β' c σ) := by
        ext σ; simp only [Pi.sub_apply]; abel
      rw [heq]
      exact Submodule.sub_mem _ hεc (hεβ'lc c hc)
    obtain ⟨S', hS'sub, hS'fin, hS'disj, hS'good, hS'cob⟩ :=
      exists_reciprocal_set (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
        (T := T) (M := M) (S := S) hSfin hSdisj hSram ε hεmem b.1 b.2
    have hzero : ∑ A ∈ S, pair (SSGRoute.decomp k A) (α' A) b.1 +
        ∑ c ∈ C, pair (Subgroup.zpowers c) (β' c) b.1 = 0 :=
      pt_orthogonality_of_realizable (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
        pair hloc' hrec S hSfin C α' β' ε ⟨hε1, hε2⟩
        (fun A hA => hα'lc A hA) hεα' (fun A hA => hεα'lc A hA)
        (fun c hc => (hβ'lc c hc).1) hεβ' (fun c hc => hεβ'lc c hc)
        b.1 ⟨b.2.1, b.2.2.1⟩ S' hS'sub hS'fin hS'disj hS'good hS'cob hCinv hC hCdisj
    rw [productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T)
      (M := M) (S := S) (C := C) pair B hB hBc α' β' hα'lc hβ'lc b.1 b.2,
      Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (α' A) b.1),
      Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β' c) b.1)]
    exact hzero
  haveI := hfinP
  haveI := hfinQ
  let βfun := productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
    (C := C) B
  let Vset := primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
    (C := C)
  let Wset := dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
    (S := S) (C := C)
  have hVW' : ∀ x ∈ Vset, ∀ y : Wset, βfun x y.1 = 0 := hVW
  have hcard' : Nat.card Vset * Nat.card Wset = Nat.card (primalClasses p k Ω K M S C) := hcard
  have hmain : ∀ x : primalClasses p k Ω K M S C,
      (∀ y : Wset, βfun x y.1 = 0) → x ∈ Vset :=
    counting_step_concrete (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C) hfinP hfinQ βfun
      (fun x x' y => productFormFun_add_left (p := p) (k := k) (Ω := Ω) (K := K)
        (T := T) (M := M) (S := S) (C := C) B x x' y)
      (fun x y y' => productFormFun_add_right (p := p) (k := k) (Ω := Ω) (K := K)
        (T := T) (M := M) (S := S) (C := C) B x y y')
      (fun x hx => productFormFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T)
        (M := M) (S := S) (C := C) B hndL hndLc x hx)
      (fun y hy => productFormFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T)
        (M := M) (S := S) (C := C) B hndR hndRc y hy)
      Vset Wset hVW' hcard'
  have hxmem : primalClassOf p k Ω K M S C α β ∈
      primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S) (C := C) := by
    refine hmain _ (fun y => ?_)
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp y.2
    have hby : dualClassMap (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
        (C := C) b.1 = y := hb
    rw [← hby]
    simp only [βfun]
    rw [productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
      (T := T) (M := M) (S := S) (C := C) pair B hB hBc α β hα
      (fun c hc => ⟨hβ c hc, isLocConstOn_zpowers c (hCinv c hc) (β c)⟩) b.1 b.2,
      Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (α A) b.1),
      Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β c) b.1)]
    exact horth b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2
  obtain ⟨α', β', ε, hcls, hε1, hε2, hεα', hεβ', hεunr⟩ :=
    (mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
      (M := M) (S := S) (C := C) hCinv _).mp hxmem
  have hα'lc : ∀ A ∈ S, α' A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) := by
    intro A hA
    have hεA : ε ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have hsub : (fun σ => ε σ - α' A σ) ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
      coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A)
        ((mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mpr (hεα' A hA))
    have heq : α' A = ε - (fun σ => ε σ - α' A σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεA hsub
  have hβ'lc : ∀ c ∈ C, β' c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) := by
    intro c hc
    have hεc : ε ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have hsub : (fun σ => ε σ - β' c σ) ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
      coboundaries_le_lcCocycles p k Ω K M (Subgroup.zpowers c)
        ((mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mpr (hεβ' c hc))
    have heq : β' c = ε - (fun σ => ε σ - β' c σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεc hsub
  have hαlc : ∀ A ∈ S, α A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    fun A hA => hα A hA
  have hβlc : ∀ c ∈ C, β c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
    fun c hc => ⟨hβ c hc, isLocConstOn_zpowers c (hCinv c hc) (β c)⟩
  have htoA : ∀ A ∈ S, toClass p k Ω K M (SSGRoute.decomp k A) (α' A) =
      toClass p k Ω K M (SSGRoute.decomp k A) (α A) := by
    intro A hA
    exact congrArg (fun z : primalClasses p k Ω K M S C => z.1 ⟨A, hA⟩) hcls
  have htoC : ∀ c ∈ C, toClass p k Ω K M (Subgroup.zpowers c) (β' c) =
      toClass p k Ω K M (Subgroup.zpowers c) (β c) := by
    intro c hc
    exact congrArg (fun z : primalClasses p k Ω K M S C => z.2 ⟨c, hc⟩) hcls
  refine ⟨ε, hε1, hε2, ?_, ?_, hεunr⟩
  · intro A hA
    have h1 : (fun σ => ε σ - α' A σ) ∈ coboundaries p k Ω K M (SSGRoute.decomp k A) :=
      (mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mpr (hεα' A hA)
    have h2 : (fun σ => α' A σ - α A σ) ∈ coboundaries p k Ω K M (SSGRoute.decomp k A) :=
      sub_mem_coboundaries_of_toClass_eq p k Ω K M (SSGRoute.decomp k A) (hα'lc A hA) (hαlc A hA)
        (htoA A hA)
    have h3 : (fun σ => ε σ - α A σ) =
        (fun σ => ε σ - α' A σ) + (fun σ => α' A σ - α A σ) := by
      ext σ; simp only [Pi.add_apply, Pi.sub_apply]; abel
    rw [h3]
    exact (mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mp (add_mem h1 h2)
  · intro c hc
    have h1 : (fun σ => ε σ - β' c σ) ∈ coboundaries p k Ω K M (Subgroup.zpowers c) :=
      (mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mpr (hεβ' c hc)
    have h2 : (fun σ => β' c σ - β c σ) ∈ coboundaries p k Ω K M (Subgroup.zpowers c) :=
      sub_mem_coboundaries_of_toClass_eq p k Ω K M (Subgroup.zpowers c) (hβ'lc c hc) (hβlc c hc)
        (htoC c hc)
    have h3 : (fun σ => ε σ - β c σ) =
        (fun σ => ε σ - β' c σ) + (fun σ => β' c σ - β c σ) := by
      ext σ; simp only [Pi.add_apply, Pi.sub_apply]; abel
    rw [h3]
    exact (mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mp (add_mem h1 h2)

end Assembly

end PT


/-- Poitou–Tate in degree `1`, relaxed at the primes split in `N` (SW Lemma 10 before dualising):
for ANY family of local pairings on `M` that is additive, zero on coboundaries, perfect and satisfies
global reciprocity, local data `α` at `S` and `β` at the real places glue to a global continuous
cocycle unramified outside `S ∪ cs(N)` as soon as they are orthogonal to every global class of
`M^∨(1)` that is unramified outside `S ∪ cs(N)` and locally trivial at `cs(N) ∖ S`. -/
theorem pt_selmer_relaxed (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      ((∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) ∨
        (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
      (∀ (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair H (a + a') b = pair H a b + pair H a' b) ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
        pair H a (b + b') = pair H a b + pair H a b') ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
        pair H a b = 0) ∧
      (∀ a : (Ω ≃ₐ[k] Ω) → M,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
          pair H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
          pair H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b))
    (hrec : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)),
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
      ∑ A ∈ S', pair (SSGRoute.decomp k A) a b + ∑ c ∈ C', pair (Subgroup.zpowers c) a b = 0)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        SSGRoute.IsSplitIn k N B → SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ¬ SSGRoute.IsSplitIn k N B → ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S, pair (SSGRoute.decomp k A) (α A) b + ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) :
    ∃ ε : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
      (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  exact PT.pt_selmer_relaxed_assembly (N := N) (hKN := hKN) (ζ := ζ) (hζ := hζ) (hζK := hζK)
    (hT := hT) (S := S) (hSfin := hSfin) (hSdisj := hSdisj) (hSram := hSram)
    (C := C) (hCinv := hCinv) (hC := hC) (hCdisj := hCdisj) (pair := pair) (hloc := hloc)
    (hrec := hrec) (α := α) (hα := hα) (β := β) (hβ := hβ) (horth := horth)

end Work.SSGRoute
