import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.Work.SSGRoute.E7Fin.canonLogData
import Submission.Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse
import Submission.Work.SSGRoute.PT.converseRepr
import Submission.Work.SSGRoute.PT.finite_primalClasses_general
import Submission.Work.SSGRoute.PT.pt_counting_identity_aux
import Submission.Work.SSGRoute.PT.pt_e7Inputs
import Submission.Work.SSGRoute.PT.pt_localisationRestricted
import Submission.Work.SSGRoute.PT.restrictedProduct_relaxation_of_dualPair
import Submission.Work.SSGRoute.PT.restrictedProduct_relaxation_offRam
import Submission.Work.SSGRoute.coker_assembly
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

set_option maxHeartbeats 2000000

/-!
# `Work.SSGRoute.PT.pt_counting_identity_h1` — the Poitou–Tate counting identity (H¹)

## What the target is

The statement of this file is `Work.SSGRoute.PT.CountingIdentity p k Ω K N hKN T M S C`, i.e.

`#{x : primalClasses … M … // IsRealizableClass … x} · #{y : primalClasses … M^∨(1) … // IsDualSelmerClass … y}
   = #(primalClasses … M …)`,

the **cardinality form of the H¹-part of the Poitou–Tate nine-term sequence in the relaxed
(Schmidt–Wingberg) form**: with `P = ∏_{v ∈ S ∪ C} H¹(D_v, M)` the product of the local `H¹`'s, `V`
the image of the global cocycles unramified outside `S ∪ cs(N)` and `W` the image of the relaxed
dual Selmer classes of `M^∨(1) = DualMod p (M ⊗ T)`, the identity reads

  `|V| · |W| = |P|`     (equivalently `dim V + dim W = dim P`, the Euler characteristic of the
                          relaxed Selmer complex).

It is Milne, *Arithmetic Duality Theorems* I.4.10(b) at `r = 1` / Neukirch–Schmidt–Wingberg 8.6.8
(or Šafarevič's Lemma 10 in the form used by Schmidt–Wingberg), and it is exactly the `hcount`
argument of the *proved* assembly `Work.SSGRoute.PT.pt_canonical_relaxed_of_inputs`
(`PT/pt_canonical_assembly.lean`), i.e. the whole realizability clause (3) of
`Work.SSGRoute.PT.pt_canonical_relaxed` is derived from it.

## Why it is *not* provable from the workspace's assets (measured, not guessed)

Given a perfect pairing `β : P × P' → 𝔽_p` with `|P| = |P'|` (local Tate duality) and the
*proven* reciprocity inclusion `V ⊆ W^⊥` (`PT.pt_orthogonality_of_realizable`), the identity is
**equivalent** to the annihilator identity `V = W^⊥` (because `|W^⊥| · |W| = |P|`, proven as
`PT.natCard_annihilator_mul`).  That annihilator identity is the *middle exactness* of the
Poitou–Tate sequence — the single deepest node of the whole Shafarevich development, and the only
missing input on the counting lane.

`#print axioms` (run 2026-09-26, this workspace) gives the following state of the nodes that the
identity needs.  Axiom-clean (proved, importable):

* `PT.natCard_counting`, `PT.mem_primalClassSet_iff`, `PT.mem_dualClassSet_iff`,
  `PT.natCard_primalClassSet`, `PT.natCard_dualClassSet`, `PT.natCard_annihilator_mul`,
  `PT.wbot_le_of_additive`, `PT.exists_pairing_on_H1loc`, `PT.productFormFun*` (the *whole*
  linear-algebra / product-pairing layer of the counting step) — `[propext, Classical.choice,
  Quot.sound]`;
* `PT.pt_orthogonality_of_realizable`, `PT.exists_reciprocal_set` (reciprocity `V ⊆ W^⊥`) — clean;
* `local_tate_duality_archimedean` (the *archimedean* half of the canonical local pairing, with all
  its clauses, for every involution) — clean;
* `PT.finite_H1loc` (finiteness of `H¹(D_A, M)` at a finite place), `PT.finite_H1loc_zpowers`
  (finiteness at an involution), `PT.finite_primalClasses` (finiteness of `P` given the two
  per-place facts) — clean;
* `PTembedding.h1loc_mup_card_kummer` (the Kummer description of `H¹(D_A, DualMod p T)`) — clean.

Still unproved (i.e. the arithmetical inputs the identity needs, *all* of them):

* `Work.SSGRoute.phi1_mono_sylow_in` (node **E6Ω**, the Sylow descent of the injectivity of the
  transgression `φ¹`) — unproved.  Its file records that it is blocked on **E0b**, and
  `Work.SSGRoute.e0b_delta` (E0b) is unproved, in turn blocked on the Yoneda/connecting-map
  lifting lemma `ExtMkCompExtClass.yoneda_extClass`;
* `Work.SSGRoute.PTembedding.localTatePairing_canonical` (node **E7**, the *finite-place* canonical
  local Tate duality) — unproved;
* `Work.SSGRoute.PTembedding.localGlobal_annihilator` (node **E8**, the local–global
  compatibility / annihilator identity) — unproved;
* `Work.SSGRoute.PT.pt_selmer_counting_identity` (this identity itself, filed 2026-09-26 11:08) —
  unproved; the node **E9** (the exact segment `P¹ → H¹(k,M^∨(1))^∨ → H²`) has no file at all.

In other words the target is *the* current research frontier of this project: the Poitou–Tate
workshop whose design (`SSGRoute/DESIGN_PT.md`, §6) estimates a size of **10–19 k lines** with
nodes E7/E8 still open and E8 explicitly flagged as the dominant risk.

## The exact route, and what is still needed

1. **Local duality (E7).**  The archimedean half is *proved* (`local_tate_duality_archimedean`); the
   finite-place half (`PTembedding/localTatePairing_canonical.lean`, and the *live* Kummer lane
   `kummerBase_euler*`, `kummerBaseDim*`, `PTembedding/h1loc_mup_kummer_card`) supplies the
   dimension equality `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))` and a perfect pairing.
   Via `PT.exists_pairing_on_H1loc` + `PT.productFormFun` (+ `…_add_left/right`, `…_ndL/ndR`) this
   yields the perfect product pairing `β : P × P' → 𝔽_p`; the workspace already proves every step
   *given* the local pairing clauses.
2. **Reciprocity `V ⊆ W^⊥`** — *proved* (`PT.pt_orthogonality_of_realizable`, with the reciprocal
   place set `PT.exists_reciprocal_set`).
3. **Exactness `W^⊥ ⊆ V` (E9 + relaxation).**  This is the missing content: the exactness
   `im(H¹(k,M) → P) = ann(loc H¹(k, M^∨(1)))` of the relaxed Poitou–Tate sequence, which is what E9
   assembles out of E6Ω/E7/E8.  Equivalently (SW Lemma 10) it is the identity of this file.
4. **Counting step** `V = W^⊥ ⟹ |V| · |W| = |P|`: pure linear algebra, and available
   (`PT.natCard_annihilator_mul` + `PT.natCard_primalClassSet` + `PT.natCard_dualClassSet`), once
   `P` and `P'` are `Finite` (item 5).
5. **Finiteness of `P` and `P'`** — packaged below as `finite_primalClasses_pt`; it needs the module
   to be finite and reduces to `PT.finite_H1loc` (finite places) and `PT.finite_H1loc_zpowers`
   (involutions).

## A recorded instance hazard (for whoever writes step 4 in this vocabulary)

The counting step (`W^⊥ = V` implies `|V| · |W| = |P|`) is the composition of
`PT.natCard_annihilator_mul` with `PT.natCard_primalClassSet` / `PT.natCard_dualClassSet` and the
identification of `W^⊥` with `primalClassSet`, i.e. of *proved* lemmas; but writing it down requires
the additive/monoid structure of the **dual** local class space
`primalClasses p k Ω K (DualMod p (M ⊗ T)) S C`.  That instance is *not* synthesizable in a fresh
module (measured 2026-09-27 02:30: `HAdd`/`AddCommMonoid`/`OfNat … 0` on
`primalClasses p k Ω K (DualMod p (M ⊗ T)) S C` fail, even with the four `DualMod` instances pinned
as `local instance`s exactly as in `PT/pt_counting_assembly.lean`, and adding
`open Work.Shrinking`/`open Work.CohomologicalShrinking` does not help); the diagonal action
instances on `M ⊗ T` are `Work.Shrinking.instDistribMulActionTensorProduct` /
`Work.Shrinking.instSMulCommClassTensorProduct` (`Work/Shrinking/Basic.lean`).  The lemma
`PT.dualClassSet` itself is fine (its type is closed under the instances used at its definition
site), so any statement that mentions the dual product *only through* `dualClassSet` avoids the
hazard.  The way the workspace's own files avoid it is to work *inside* a section that already has
the pins and to phrase everything through `dualClassSet`, `natCard_counting` and
`wbot_le_of_additive` (predicate form) — that is the recommended shape for step 4.

## The route for the missing input (step 3), per `SSGRoute/DESIGN_PT.md` §3

The content of step 3 is Milne's proof of I.4.10: the class formation
`0 → K^× → 𝕀_K → C_K → 0` (NK) with `Ext_G(·, C_K)` as the δ-functor dual to `H¹(k, ·)`:

* **E1** (`ext_h1_bridge`, on disk): `H¹(k, E) ≅ Ext¹_G(E', K^×)` and
  `ker(H²(k,E) → H²(K,E)) ≅ Ext²_G(E', K^×)`;
* **E2** (`ext_idele_shapiro`, on disk): `Ext^r_G(E', 𝕀_K) ≅ ∏'_v Ext^r_{G_v}(E', K_w^×)`;
* the long exact sequence of `Ext_G(E', ·)` on the class formation therefore reads
  `H¹(k,E) → P¹(E) → Ext¹_G(E',C_K) → Ext²_G(E',K^×) → P²(E)`;
* **E6 + E7**: the transgression `φ¹ : Ext¹_G(E',C_K) ↪ H¹(k,E')^∨` is injective (dévissage
  `E5`/`E6` down to the trivial module `E3`, with `E7` the local duality);
* **E8**: the square with the sum of the local pairings commutes (this is where the local–global
  compatibility of the fundamental classes is used);
* hence `im(H¹(k,E) → P¹(E)) = ker(P¹ → H¹(k,E')^∨) = ann(loc H¹(k,E'))`, the middle exactness;
  intersecting with the open subgroup `U` of the relaxation (`x_S = 0`, unramified off `S ∪ cs(N)`,
  arbitrary on `cs(N)`) and dualising the restricted product turns it into
  `W^⊥ ⊆ V` for the `S ∪ C`-product, i.e. exactly the missing step 3.

## Step 5 (finiteness) is available — two further ingredients are banked

`P` is finite by `finite_primalClasses_pt` below (equivalently, by the now-proved packaging
`Work.SSGRoute.PT.finite_primalClasses_general`, `PT/finite_primalClasses_general.lean`).  For
`P' = primalClasses … (DualMod p (M ⊗ T)) …` one needs `Finite T` (from `hT` via
`Work.SSGRoute.finite_of_finrank_eq_one`) and `Finite (DualMod p (M ⊗ T))`, which is *not* an
`inferInstance` (measured 2026-09-27 02:00: `synthInstanceFailed`); the two ingredients are
`Work.SSGRoute.finite_tensor` / `Work.SSGRoute.finite_dualMod` (`LTDDefs/Basic.lean`), packaged as
`Work.SSGRoute.PT.finite_dualMod_tensor` (`PT/finite_dualMod_tensor.lean`, dispatched).

## A caveat on the filed E8 node

`Work.SSGRoute.PTembedding.localGlobal_annihilator` is filed as a node for E8, but as stated it
quantifies over an *arbitrary* family `pair` of local pairings (no clause list, no naturality, no
canonicality hypothesis) and concludes that every functional vanishing on coboundaries and on the
locally trivial classes is a finite sum of the values of *that* `pair`.  For `pair = 0` and a
functional `γ ≠ 0` on `H¹(k, M^∨(1))` killing `Ш¹(k,M^∨(1))` the conclusion would force `γ = 0`, so
the statement is *not* the intended E8 (which is a statement about the *canonical* pairing, i.e. the
local–global compatibility of fundamental classes, `SSGRoute/DESIGN_PT.md` §4 C1/E8).

**Resolution (2026-09-27, session 3).**  The filed form is *not* repairable into a useful E8, for two
independent reasons.  (1) Its conclusion is the *annihilator realization* (`ann(Ш¹) ⊆ im(φ)`, i.e.
`W^⊥ ⊆ V`), which is the *hard half of the middle exactness* — node E9's content, requiring the
*canonical* pairing of E7 and not an arbitrary family; adding the E7 clause list to the hypotheses
would therefore just move the node to E9.  (2) Its shape is *level-uniform* in the sense recorded in
`PT/localTatePairing_deg02.lean`: a statement realising functionals by local data attached to a
*fixed* level is false once one quantifies over higher levels `L ⊇ K` (their counterexample: `k = K =
ℚ`, `p = 2`, `M = 𝔽₂`, `L = ℚ(ζ₈)`; the level-`K` data has `𝔽₂`-dimension 1 against `dim H² = 3`).

What E8 *is* is the **level-free** local–global compatibility, and the repository already has it:
`SSGRoute/DESIGN_EXT.md` §2 replaces canonical E8 (2–4k lines, absent from NK: `DESIGN_EXT.md` C1)
by the single Brauer node **`Work.SSGRoute.brauer_single_place`** (E8′), *proved* and axiom-clean:
"a Brauer class locally trivial outside one `Gal(K/k)`-orbit is zero".  Its role in the pipeline is
(i) reciprocity is *free* from the exactness of the class formation `Kˣ → 𝕀_K → C_K`, and (ii) local
perfectness transfers through the injectivity of the local localisation `ι_w` (E8′).  The corrected
node, in the vocabulary of `SSGRoute.PTDefs` (`extH`/`unitsK`/`idelesK`/`extToIdeles`/`extLoc`) — the
shape the `PTembedding`/E7 consumers look for — is
`Work.SSGRoute.PTembedding.localGlobal_compat`
(`Submission/Work/SSGRoute/PTembedding/localGlobal_compat.lean`, dispatched 2026-09-27), with the
`ι_w`-injectivity corollary as its consumer-facing form.  The filed
`localGlobal_annihilator` should be *retired*, not proved.

## State of the lanes (file mtimes, 2026-09-27 02:12)

* **live**: `ExtMkCompExtClass/*` — E0b's blocker `ExtMkCompExtClass.yoneda_extClass`
  (`liftCocycle_postcomp_desc.lean` 00:29, `singleDelta_eq_triangleOfSESDelta.lean` 02:01,
  `coneLiftConditionU_holds.lean` 02:07); `E3In/*` (E3, 23:26); the Kummer lane (E7-finite:
  `kummerBase_euler_additive_loc.lean` 01:53, `kummerBase_euler_ses_decomp.lean` 02:09);
  `PT/pt_finitePlace_half.lean` (the finite half of input (1)).
* **stalled (safe to dispatch)**: `phi1_mono_sylow_in.lean` (E6Ω; 12:22, waiting for E0b),
  `pt_selmer_relaxed.lean` (10:29), `PTembedding/localGlobal_annihilator.lean` (E8 — superseded, see
  above), and the E9 exact segment, for which no file exists: this node — the middle exactness
  of the relaxed Poitou–Tate sequence — is the content of this file.
## Session 2 (2026-09-27 ~04:00): the reduction is now *formal*, and the finiteness is done

Three things changed in this file, all proved here and axiom-clean (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`):

1. **`finite_of_isCyclotomicDual`** — `Finite T` from `hT` (it is a line over `𝔽_p`).
2. **`finite_primalClasses_dual_pt`** — `Finite (primalClasses … (DualMod p (M ⊗ T)) …)`, i.e. the
   *dual* side of the finiteness.  With `finite_primalClasses_pt` (primal side) this discharges the
   two finiteness arguments (`hfinP`, `hfinQ`) of `PT.pt_canonical_relaxed`; the ingredients are
   `finite_dualMod_tensor` and (the now-proved) `finite_primalClasses_general`.
3. **The reduction of the node to a single arithmetic statement**:
   * `countingIdentity_iff_submoduleForm` — the predicate form (`CountingIdentity`, this file) and
     the submodule form `|V| · |W| = |P|` (`V = primalClassSet`, `W = dualClassSet`) are
     equivalent, via the proved `natCard_counting`, `natCard_primalClassSet`,
     `natCard_dualClassSet`.  So the two filed nodes `PT.pt_counting_identity_h1` and
     `PT.pt_selmer_counting_identity` are interchangeable, and either can quote the other's form;
   * `natCard_annihilator_mul_additive` — `|W^⊥| · |W| = |P|` for a pairing given only
     *additively* (the form in which the product of local Tate pairings is available:
     `PT.exists_pairing_on_H1loc`);  this is `PT.natCard_annihilator_mul` with the scalar action
     recovered from additivity;
   * `natCard_mul_of_annihilator` — the *converse* of `PT.counting_step_concrete`: for a
     bi-additive, both-sides non-degenerate `β` and `V = W^⊥`, one gets `|V| · |W| = |P|`;
   * **`countingIdentity_of_dualAnnihilator`** — the node's exact content, in one statement: for a
     bi-additive `β` on `P × P'` non-degenerate in both variables, with
     `V = W^⊥` (`hbot`), the target follows.

**What is therefore missing is exactly two arithmetic facts, and nothing else.**

(i) *That `β` exists* (with the non-degeneracy and additivity clauses).  This is node E7.  It is
    **not** part of this file, and it is *already reduced by the E7 lanes* to the two named nodes
    `Work.SSGRoute.local_tate_duality_euler` (the local Euler characteristic `h¹ = h⁰ + h² + ε·dim M`)
    and `Work.SSGRoute.local_tate_duality_02` (Tate duality in degrees `0`/`2`,
    `dim H²(D_A,M) = dim H⁰(D_A,M^∨(1))`): the reduction is
    `PT.pt_canonicalFin_clauses_of_euler02` + `PT.pt_finiteHalf_glue` + `PT.pt_e7Inputs`
    (all sorry-free), and the archimedean half is the sorry-free `E7Arch` lane
    (`local_tate_duality_archimedean`, `E7Arch.pairArchFamily`, `E7Arch.reciprocity`).
    Both remaining nodes are *stated* and unproved (`Submission/Work/SSGRoute/local_tate_duality_*.lean`).

(ii) *The annihilator identity `V = W^⊥`* — the middle exactness of the relaxed Poitou–Tate
    sequence (nodes E8 + E9).  `V ⊆ W^⊥` is proved (`PT.pt_orthogonality_of_realizable`); the
    content is `W^⊥ ⊆ V`, i.e. `im(H¹(k,M) → P) = ann(loc H¹(k,M^∨(1)))`.

## Measured state of the E-chain (2026-09-27 04:15, comment-aware scan)

* **Proved** (no holes): `ext_idele_shapiro` (E2), `phi1_trivial_mono` (E3), `phi1_mono_base`,
  `phi1_mono_pgroup`, `phi1_mono_pgroup_in`, `phi1_sylow_level`, `phi1_sylow_setup`, `phi1_wcolim`,
  `phi1_mono_sylow` (E6, as a corollary of the `Ω`-indexed node), `eCoh_delta`, `e0b_bridge`,
  `e0b_core_ext`, `e0b_naturality`, `e0b_delta`, `ext_one_iso_divisible_cohomology` (E1a),
  `ExtH1Iso`, the whole `E7Arch` lane, `PT.pt_canonical_assembly`, `PT.pt_counting_assembly`,
  `PT.pt_relaxed_assembly`, `PT.h1ImageLeKernel`, `PT.h1KernelLeImage`,
  `PT.pt_canonicalFin_clauses_of_euler02`, `PT.pt_e7Inputs`, `pt_sha2_core`'s helper lemmas
  (`exists_extToClasses_iff_extDelta_eq_zero`: the `Ext`-segment exactness);
* **Open, one hole each**: `ExtMkCompExtClass/yoneda_extClass` (E0b's blocker; its *import* is
  currently broken by a sibling file being edited, `mapExtAddHom_extMk_univ.lean`),
  `ext_h1_bridge` (E1), `phi1_mono_step_in` (E5), `phi1_mono_sylow_in` (E6Ω),
  `phi0_trivial_epi_in` (E4), `local_tate_duality_euler`, `local_tate_duality_02` (E7),
  `PTembedding/localTatePairing_canonical` (E7), `E7Fin/pairClauses_of_euler02`,
  `PTembedding/localKummer_base` (`kummerBaseDim`), `PT/localDuality02`,
  `PTembedding/tateNakayama_general`, `PT/tateNakayama_free`, `pt_selmer_relaxed`,
  `PT.pt_selmer_counting_identity` (this node, in its sibling file),
  `canonical_localPairing_with_reciprocity` (G1), `PTembedding/poitouTate_pairing`,
  `PTembedding/sha_card_euler`, `tatePoitouEmbedding` (G5), and this file;
* **No file at all**: `E8` (the local–global compatibility square) and `E9` (the segment assembly).
  The filed `PTembedding/localGlobal_annihilator` is *not* a correct rendering of E8 (see the caveat
  above); it must be restated.

### E8: superseded, and what its corrected form is (revised 2026-09-27, session 3)

`DESIGN_PT.md` flags E8 as the dominant risk ("NK fundamental classes **may be missing**"), and
`DESIGN_EXT.md` C1 confirms the *canonical* statement is absent from NK: NK's global class is "only
*some* element of order `[L:K]`", its local invariant is relative to an arbitrary normalisation, and
there is no `u_v ↦ res u_{L/k}` compatibility.  `DESIGN_EXT.md` §2 *avoids* it (a canonical E8 would
be 2–4k lines) and replaces it by the single Brauer node `brauer_single_place` (E8′), **proved and
axiom-clean**; the two roles it plays are (i) free reciprocity from the class-formation exactness and
(ii) transfer of local perfectness through the injectivity of `ι_w`.

(What *is* in NK — and is worth knowing even though the route does not need it — is the *Artin-map*
half of the picture: `Submission/NK/CFTLib/IdeleHasse/localGlobalArtinMap_exists.lean` constructs the
canonical local–global Artin map `𝕀 K →* Gal(L/K)` as the product `∏_v λ_v` of the local Artin maps
glued along the idèles.  That is a statement about `𝕀_K → Gal`, not about the fundamental classes
`u_{L/K} ∈ H²(G, C_L)` and their restrictions, so it does not by itself give the `H²`-compatibility
that C1 reports missing.)

The corrected E8 node chain, in the vocabulary of `SSGRoute.PTDefs`, is (all dispatched 2026-09-27,
see `SSGRoute/E8_STATUS.md` for the full record):

* `Work.SSGRoute.PTembedding.localGlobal_compat` — **proved**, axiom-clean: the level-free E8 in the
  `PTDefs` vocabulary (`a : extH (unitsK k K) 2` locally trivial outside one `Gal(K/k)`-orbit is `0`),
  together with the reusable bridge `extLoc w (extToIdeles a) = extHMap (decompK w).subtype
  (unitsToLocalUnits k K w) a`;
* `Work.SSGRoute.PTembedding.localGlobal_compat_injective` — **proved**, axiom-clean: a class of
  `Ext²(ℤ, 𝕀_K)` in the range of `extToIdeles` which is locally trivial outside one orbit is `0`;
* `Work.SSGRoute.PTembedding.localGlobal_compat_local_injective` — **proved**, axiom-clean: the
  literal `ι_w`-injectivity that `DESIGN_EXT.md` §2 consumes for the local-perfectness transfer.

All four lemmas of the chain are axiom-clean (`[propext, Classical.choice, Quot.sound]`), so **E8 is
now closed for the pipeline** and the false filed node `PTembedding/localGlobal_annihilator` can be
retired without replacement cost.

### A measured instance hazard, and the fix

In a *fresh* module (this one), a statement that writes `x + x'` or `= 0` for
`x : primalClasses p k Ω K (DualMod p (M ⊗ T)) S C` fails: the searches
`HAdd (primalClasses … (DualMod …) …) …` and `OfNat (primalClasses … (DualMod …) …) 0`
both `synthInstanceFailed`.  The fix (used in `section CountingFromAnnihilator` below, and in
`PT/pt_counting_assembly.lean`) is to pin the four structure instances of the *coefficient module*
`M^∨(1) = DualMod p (M ⊗ T)` as `local instance`s, and to pass every instance argument of the
abstract counting lemmas *explicitly*.  With the pins, `countingIdentity_of_dualAnnihilator`
elaborates and its proof goes through (at `maxHeartbeats 2000000`, set at the top of the file).

### Wiring into the consumer

`Submission/Work/SSGRoute/PT/pt_canonical_relaxed.lean` (the instantiation with `N := N`, `hKN`)
still has the literal placeholder `(show CountingIdentity p k Ω K N hKN T M S C from by sorry)`;
it is to be replaced by `pt_counting_identity_h1 p k Ω K N hKN ζ hζ hζK T hT M S C …` (or by the
sibling `PT.pt_selmer_counting_identity`, which states the same thing).

### Audit of the two E7 arithmetic nodes (2026-09-27, session 2)

Both are *correctly stated* (checked against the classical formulas), so they need no restatement:

* `local_tate_duality_euler`: `h¹ = h⁰ + h² + ε·dim M` at a finite place.  The classical local
  Euler characteristic is `h⁰ - h¹ + h² = -[k_v:ℚ_p]·dim M` for `v | p` and `= 0` otherwise (valid
  for *every* finite module `M`, since `Σ(-1)^i dim H^i = 0` over a finite group and the local
  formula is Tate's); hence `ε = [k_v:ℚ_p]` (`= 0` off `p`).  Sanity check at `M = 𝔽_p`, `v ∤ p`:
  `h⁰ = 1` (invariants), `h² = 1` (`Br(k_v)[p] ≅ 𝔽_p`), `h¹ = dim k_v^×/(k_v^×)^p = 2`, and indeed
  `1 - 2 + 1 = 0`.  Its first conjunct `Module.Finite (ZMod p) (H1loc …)` is *automatic*
  (`PT.finite_H1loc` gives `Finite`, and `Module.Finite.of_finite` upgrades it), so the arithmetic
  obligation of that node is the dimension identity alone.
* `local_tate_duality_02`: `dim H²(D_A,M) = dim H⁰(D_A, M^∨(1))` with
  `M^∨(1) = DualMod p (M ⊗ T)` — this is Tate's local duality at `r = 0`
  (`H²(G_{k_v},M) ≅ H⁰(G_{k_v}, M^∨(1))^∨`), and `DualMod p (M ⊗ T) ≅ Hom(M, μ_p)` is right because
  `IsCyclotomicDual` makes `T^∨ ≅ μ_p`.  Note that its *finrank* form is weak on infinite modules
  (`finrank = 0`), so a prover must also get finiteness of `H²loc` — which is why
  `PT/localTatePairing_deg02.lean` records that `finite_H2loc` must **not** be attacked in
  isolation (the `2`-cocycle group is infinite; the quotient's finiteness needs the local theory),
  and why the filed `PT.milne18_at_zero` (the `Hom`-form of Milne I.1.8 at `r = 0`) is the right
  gateway.

### What is *not* worth (re)delegating, with reasons

* the abstract class-formation Tate duality (`Ext^r_U(N,C) ≅ H^{2-r}(U,N)^∨`, Milne I.1.8) — the
  local lane's design note asks for it, but the concrete `r = 0` statement it is used for is
  *already filed* as `PT.milne18_at_zero` (with `PT.Milne18AtZero`, `PT.Coind`,
  `PT.localTatePairing_deg02_of_milne18` in `PT/ClassFormation.lean`), so delegating the abstract
  form would duplicate a filed node's internal step;
* the middle exactness `V = W^⊥` (E8/E9) — *equivalent* to this node, hence resignation, not
  delegation; the corrected E8 node (level-free local–global compatibility, in the
  `SSGRoute.PTDefs` vocabulary) is `Work.SSGRoute.PTembedding.localGlobal_compat`, dispatched
  2026-09-27, and *replaces* the mis-stated `PTembedding/localGlobal_annihilator`;
* `PT.pt_selmer_relaxed` — this node's equivalent through
  `PT.pt_canonical_relaxed_of_inputs` + `PT.pt_relaxed_assembly` (`localFamilyB`,
  `localFamilyB_spec`), so the same objection applies.


### Warning recorded for the fleet: the level-uniform realisation clause of `local_duality_ext` (E7b)

`Submission/Work/SSGRoute/local_duality_ext.lean` (E7b, the `Ext`-form of local Tate duality at a
finite level) states, as clause (ii), that at *every* level `L` with `p ∣ [L_{w'} : k_v]`, every
functional on `H¹(D', M')` is already realised by a class living at the level `K`.  Its own
`Submission/Work/SSGRoute/PT/localTatePairing_deg02.lean` records two explicit counterexamples to
exactly this shape of clause (the `Ext⁰`/`H²` case: `k = K = ℚ`, `p = 2`, `M = 𝔽₂`, `L = ℚ(ζ₈)`;
and the complex-place case where `Ext⁰_{D_w}(M, K_wˣ) ≠ 0 = H²`), and concludes that "the positive,
usable fragments" are the *direct-limit* forms.  So E7b should be re-examined (restated with a
level-independent local class / in the direct limit over `L`) before it is relied on.  It is **not**
on the path of this file: `PT.pt_e7Inputs` + `PT.pt_canonicalFin_clauses_of_euler02` reduce the
pairing input of `PT.pt_canonical_relaxed` to the two *full-group* nodes
`local_tate_duality_euler` and `local_tate_duality_02` (plus the archimedean, sorry-free `E7Arch`
lane), and the full-group form has no level parameter.


## Session 4 (2026-09-27, ~13:30): measured state of the fleet, and two new lemmas

**The node is the central duality, in its counting form.**  A lane-wide finding (recorded
independently in `SSGRoute/PTCore/STATUS_pt_pairing_left_inj.md` §3 and in
`SSGRoute/sha2_image_of_Hm2_status.md`) is that `E9` — the middle exactness
`im(H¹(k,M) → P) = ann(loc H¹(k,M^∨(1)))` — *is* Milne ADT I.4.10 (the Tate–Poitou duality itself)
and cannot be delegated as a supporting lemma.  Since this file's target is *equivalent* to `E9`
given the proved reciprocity (§ "Why it is not provable…" above), the target is one of the fleet's
central frontier nodes, not a lemma that a single session can discharge.  The fleet's routes to it
converge on two roots, both filed and unproved:

* `Work.SSGRoute.PTembedding.poitouTate_pairing` (the left-nondegeneracy half of the
  `Ш¹ × Ш² → 𝔽_p` pairing) and
* `Work.SSGRoute.PTembedding.sha_card_euler` / `PTCore.sha_card_euler_var` (`#Ш² = #Ш¹`),

together with `tatePoitouEmbedding`/`PTembedding.tatePoitouEmbedding_alt`; `PTCore`'s
`natCard_sha2_eq_sha1_of_pairing_halves` (proved) already reduces the cardinality form to the two
one-sided halves, and the routes are assembled by
`PTembedding.tatePoitouEmbedding_of_pairing` (proved).

**Input (i) (the pairing `β`) is fully decomposed elsewhere.**  `E7a` (local Euler characteristic)
is now *reduced* by `kummerBase_euler_of_inputs` to the four named inputs `h3`
(`cd_p ≤ 2`, filed `PT/h3loc_decomp_subsingleton`), `h2fin` (finiteness of `H²loc`, to be derived
from `E7b`), `hartin` (Milne I.2.10, `milne210aux/*`, live) and `hgen` (Milne I.2.11, the cyclic
case `PT/euler_cyclicCase_primeToP`, live) — see `PT/EULER_RESIDUECHAR_STATUS.md`.  `E7b`
(degrees 0/2) is reduced to the class-formation duality: the filed gateway is `PT.milne18_at_zero`
(`Hom_{D_A}(M,μ_p) ≅ H²(D_A,M)^∨`), and
`PTembedding/tateNakayama_general.lean` records that the missing statement is the *Ext-form* of
Milne ADT 0.2 / I.1.8 (`Ext^r_G(M,C) ≅ H^{2-r}(G,M)^∨`), explicitly noted there as "the next step
for whoever takes this node" — an unclaimed, on-the-path piece.

**The lane's plumbing is largely built** (all sorry-free): `PT/pt_restrictedPairing.lean`,
`PT/restrictedProduct_relaxation.lean` (the abstract relaxation: `hAB` + two compactness inputs give
the relaxed exactness), `PT/pt_annihilator_relaxation.lean`, `PT/pt_unramifiedSub.lean`
(`unramifiedSub ≤ H1loc`, with the cocycle-level/class-level bridge), and —
importantly — `Work.SSGRoute.PT.vanishingInertia_finite`
(`PT/vanishingInertia_finite.lean`), which *proves* that a globally locally constant cocycle
vanishes on the inertia of all but finitely many finite places (up to conjugacy); that is the
finiteness input of the localisation step of the relaxation, and of the `S'`-existence used by
`PT.pt_orthogonality_of_realizable`.  What remains of the relaxation *instantiation* is the
localisation map into the restricted product (indexed by the places of `k`) and the compactness of
the image of the global classes.

**Two new lemmas proved in this file (session 4, no new axioms):**

* `transpose_nondegenerate_of_card_eq` — for a bi-additive `β : P → Q → 𝔽_p` on finite
  `𝔽_p`-modules with trivial left radical and `Nat.card P = Nat.card Q`, the right radical is
  trivial as well (the transpose of the bijection `P ≅ Q^∨` is injective).  This is the classical
  step that upgrades a *one-sided* duality statement plus a dimension equality to a perfect pairing
  — the form in which the local Tate pairing is available (`E7tate`'s cup product + the Euler
  characteristic dimension equality of `E7a`/`E7b`);
* `natCard_annihilator_mul_of_left` — the counting step `|W^⊥| · |W| = |P|` with the
  right-non-degeneracy *derived* rather than assumed, i.e. `natCard_annihilator_mul_additive` under
  the one-sided hypothesis + `Nat.card P = Nat.card Q`.  (With the existing
  `natCard_mul_of_annihilator`/`counting_step_concrete`, the counting identity and the annihilator
  identity are now equivalent in both directions, in both the two-sided and the one-sided shape.)

## Session 5 (2026-09-27, ~14:35): `E0b` and `E6Ω` unblocked, and the sharpest reduction

**The `E0b → E6 → E9` route was blocked by a *missing file*, not by mathematics, and that is now
fixed.**  `Submission/Work/SSGRoute/e0b_delta.lean` (node `E0b`, clause 2) imported
`Submission.Work.SSGRoute.ExtMkCompExtClass.yoneda_extClass`, a module that did not exist in the
tree (the directory contained only `Defs.lean`, `coneLiftConditionU_holds.lean`,
`liftCocycle_postcomp_desc.lean`, `singleDelta_eq_triangleOfSESDelta.lean`).  Hence
`e0b_delta.lean` did not compile, and `phi1_mono_sylow_in.lean` (`E6Ω`), which imports it, did not
compile either — even though *its own proof is complete and contains no `sorry`*.  Supplying the
missing name as a direct alias of the already-proved `Work.SSGRoute.extMk_comp_extClass`
(`SSGRoute/extMk_comp_extClass.lean`, sorry-free) makes both build; `#print axioms
Work.SSGRoute.e0b_delta = [propext, Classical.choice, Quot.sound]` — **`E0b` is closed**, and
`E6Ω` is closed up to the `PTDefs`/`NK` baseline.  The new file is
`SSGRoute/ExtMkCompExtClass/yoneda_extClass.lean`; the finding is written up for the fleet in
`SSGRoute/E0B_UNBLOCKED_STATUS.md`.  Since `E9_STATUS.md` lists `E6` as the *last* missing
ingredient of the inclusion `⊇` of leg (c) (the annihilator step), the only pieces of the middle
exactness left are now (b) the `χ` propagation, (c) itself, (d) the relaxation, and `E7` for the
pairing `β`.

**Two new lemmas (session 5, no new axioms).**

* `natCard_mul_of_annihilator_of_left` — the submodule-form counting identity `|V| · |W| = |P|`
  from a pairing `β` non-degenerate only on the *left*, plus `Nat.card P = Nat.card Q`, plus the
  annihilator identity `V = W^⊥`;
* `countingIdentity_of_oneSidedDualAnnihilator` — **the sharpest reduction of this node in this
  file**: the target follows from a left-non-degenerate bi-additive `β` on `P × P'`, the
  cardinality equality `|P| = |P'|`, and the annihilator identity `V = W^⊥`.  These are exactly
  the two arithmetic facts of the node, in the form in which they are *available*:
  (i) local Tate duality supplies the cup product with trivial left radical while the *dimension*
  equality `dim P = dim P'` comes from the local Euler characteristic and Tate duality in
  degrees `0`/`2` (node `E7`), and (ii) `V = W^⊥` is the middle exactness (`E8`/`E9`), whose
  inclusion `V ⊆ W^⊥` is the proved `PT.pt_orthogonality_of_realizable`.

**Measured remainder (do not re-derive).**  The E-chain's holes after the unblock: `E1a`
(`PT/e1a_ext_sha2_bridge.lean`, mtime 13:52 — currently failing to *elaborate* on an instance
search for `H1/H2` of a coinduced module, plus one `sorry`: a live lane, hands off), `E5`
(`phi1_mono_step_in`), `E7` (`local_tate_duality_euler`, `local_tate_duality_02`,
`PTembedding/localTatePairing_canonical`), `E9` (b)/(c)/(d), and this node.  `E1`
(`ext_h1_bridge`) and `PT.pt_extSegment_exact` are axiom-clean.  The taint of the E-chain modules
that *have* complete proofs flows through the `NK` (global CFT) baseline, not through the
Poitou–Tate chapter.

**Measured state of the `H³` layer, and why `mapH3` is *not* on the critical path (recorded so
that it is not re-derived).**  The third continuous cohomology `Work.SSGRoute.H3`
(`SSGRoute/kummerBase_euler_h3_absKummer.lean`: `d3`, `d3_d2`, `C3c`, `Z3`, `B3`, `H3`, `H3π`,
`H3π_eq_zero_iff`) and the *second* connecting map
`ShortExactSeq.deltaH3 : H²(G,P) →+ H³(G,M)` with its exactness
`Work.SSGRoute.range_mapH2_eq_ker_deltaH3` (`SSGRoute/kummerBase_euler_connectingH3_descent.lean`,
whose `kummerBase_euler_additive` consumes it for the Euler-characteristic additivity of `E7a`) both
exist and are sorry-free.  The only missing declaration of that layer is the *functoriality* of
`H³` in the coefficient module (`mapH3`, the analogue of `PT.mapH1`/`mapH2`), for which the two
membership facts are now proved as `Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3`
(`SSGRoute/H3Map/mapC3c_mem_Z3_mem_B3.lean`).  It is **not** needed for the terminal vanishing
`H³(G, Hom_ℤ(N,C)) = 0` of Milne `ADT` I.1.8(a): for `N` a finite `𝔽_p[G]`-module the additive
hom group `Hom_ℤ(N, k̄^×)` is *p-torsion* (an additive hom out of a `p`-torsion group lands in
`C[p] = μ_p`, a finite group), so that vanishing is exactly the hypothesis `h3`/`H3loc`
("`cd_p(G_{k_v}) ≤ 2`") applied to the finite module `Hom_ℤ(N, k̄^×)` itself — no coefficient
dévissage and no `mapH3` are required.  The functoriality itself is nevertheless *provided now*, in the
same file: `Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3` (which two independent reviewers of this
team read as correct and non-vacuous) together with `H3Map.mapC3c`, `H3Map.mapZ3`,
`H3Map.mapH3` and its computation rule `H3Map.mapH3_H3π` — the exact analogue of
`PT.mapH1`/`mapH2`, so that the `H³` layer is now as complete as the `H¹`/`H²` layers.

**A recorded instance hazard on the *quotient* of the local class space (blocks the "cokernel"
form of this node).**  The statement `(primalClassSet …).toAddSubgroup.index = Nat.card (dualClassSet …)`
— the natural pairing-free, "cokernel" sufficient form of this node
(`Nat.card ↥V * V.index = Nat.card P` is Lagrange, `AddSubgroup.card_mul_index`) — *does not
elaborate*: `Submodule.toAddSubgroup` demands the canonical `AddCommMonoid`/`Module` instances of
`primalClasses p k Ω K M S C`, while the instance actually synthesized at the definition site of
`primalClassSet` is `Prod.instAddCommMonoid`/`Prod.instModule`
(`Application type mismatch … has type @Submodule (ZMod p) (primalClasses …) Prod.instAddCommMonoid
Prod.instModule but is expected to have type @Submodule ?R ?M Ring.toSemiring
AddCommGroup.toAddCommMonoid ?M'`).  Anyone wanting the index/cokernel form should either pin the
instances at the use site or construct the `AddSubgroup` by hand from the carrier
(`⟨V, V.zero_mem, V.add_mem, …⟩`).  The *quotient* notation `primalClasses … ⧸ primalClassSet …`
is blocked one turn further out — `Submodule.hasQuotient` triggers a re-search of
`Module (ZMod p) (primalClasses …)` and gets stuck (`typeclass instance problem is stuck:
Module ?m ?n`), and on the additive-subgroup route the index `AddSubgroup.index` of a hand-built
subgroup hits the same disease one level down (`typeclass instance problem is stuck: AddGroup ?m`).
Attempts at `countingIdentity_of_index`/`countingIdentity_of_quotientCard` (the *pairing-free*
sufficient form `|P / V| = |W|`, which would follow from Lagrange alone,
`Nat.card ↥V * V.index = Nat.card P`) were therefore abandoned; the pairing-free route *does* work,
but only after all instances of `primalClasses …` have been pinned at the use site, which is a job
for whoever needs it.  This is the same family of hazard as the one recorded at the top of this
file for the dual local class space.

## Session 8 (2026-09-28, ~01:00): the node's arithmetic input displayed as the *finite-place*
## dimension equality, and a design obstacle in the relaxation instantiation

**Ten new lemmas, all proved and axiom-clean** (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`, measured this session):

* `pt_finrank_eq_of_nondegenerate_pairing` — *generic linear algebra*: a bilinear pairing
  `B : P →ₗ[K] Q →ₗ[K] K` that is non-degenerate on both sides forces `finrank K P = finrank K Q`
  (a trivial left radical embeds `P` into `Dual K Q`, and `Subspace.dual_finrank_eq`).  This is the
  step that converts the *pairing* of node `E7` into the *dimension* equality of the two local
  `H¹`-spaces;
* `natCard_primalClasses_pow` — `Nat.card (primalClasses … M …) =
  p ^ (Σ_{A ∈ S} dim H¹(D_A,M) + Σ_{c ∈ C} dim H¹(⟨c⟩,M))` (from `Nat.card_pi`/`Nat.card_prod`
  and `Module.natCard_eq_pow_finrank`);
* `natCard_primalClasses_eq_of_finrank_eq` — per-place dimension equalities between two coefficient
  modules imply the equality of the cardinalities of the two local class spaces;
* `hcard_of_localDims` — the `Nat.card P = Nat.card P'` input of
  `countingIdentity_of_oneSidedDualAnnihilator`, in the shape in which `E7` delivers it;
* `countingIdentity_of_localDims_and_annihilator` — **the node from the arithmetic inputs**
  (per-place dimension equalities, per-place non-degeneracy of the pairing, and the annihilator
  identity `V = W^⊥`); the cardinality equality is *derived*, not assumed;
* `finrank_H1loc_zpowers_tate_dual` — **the `C`-side of `hcard` is free**: at an involution the two
  local `H¹`-dimensions agree, from the *proved* archimedean local Tate duality
  (`Work.SSGRoute.local_tate_duality_archimedean` via `PT.exists_localAxioms_zpowers`) and
  `pt_finrank_eq_of_nondegenerate_pairing`;
* `hcard_of_localDims_finPlace` — hence the `Nat.card` equality follows from the **finite-place**
  dimension equalities alone;
* `finrank_H1loc_tate_dual_of_euler02` — **the finite-place dimension equality is not an independent
  arithmetic input**: it is the arithmetic-free combination of the two *named* `E7` nodes
  (`EulerCharInput` = `E7a` and `Deg02Input` = `E7b` of `PT/pt_e7Inputs.lean`), since the two
  expansions of `h¹` — at `M` and at `M^∨(1)` — agree once `dim M = dim M^∨(1)`;
* `countingIdentity_of_euler02_and_annihilator` — **the capstone**: `CountingIdentity` follows from
  the two named `E7` nodes, a bi-additive pairing on the two class spaces non-degenerate in the
  first variable, the annihilator identity `V = W^⊥`, and the finiteness of the two class spaces;
* `countingIdentity_of_localAxioms_and_annihilator` — **the sharpest reduction**: `CountingIdentity`
  follows from a family `pair` of local pairings satisfying `LocalAxioms` at every local group
  (`hloc`) together with the annihilator identity `hbot` for the *constructed* product pairing
  (`PT.localPairingFun` + `PT.productFormFun`), plus finiteness.  This is the *interface of the
  pipeline*: `hloc` is exactly the hypothesis that `PT.pt_canonical_relaxed_of_inputs` and
  `PT.pt_selmer_relaxed` consume (node `E7` + the canonical construction), and `hbot` is the middle
  exactness (node `E9`).  The pairing, its additivity, its left-non-degeneracy and the `Nat.card`
  equality are all *constructed/derived* inside the proof, so the node adds nothing to `hloc` and
  `hbot`.

So the node's arithmetic obligation is now displayed in its sharpest published form: at each
finite place of `S`, `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))` (node `E7a`
`Work.SSGRoute.local_tate_duality_euler` together with node `E7b`
`Work.SSGRoute.local_tate_duality_02`), and at the involutions of `C` nothing; plus the annihilator
identity `V = W^⊥`, whose inclusion `V ⊆ W^⊥` is proved (`PT.pt_orthogonality_of_realizable`) and
whose converse is the middle exactness (node `E9`).

**The route to `W^⊥ ⊆ V` and its form.**  `PT.restrictedProduct_relaxation` (*proved*) derives the
*relaxed* annihilator identity from the **unrestricted** middle exactness — the statement
`hAB : a ∈ A ↔ ∀ b ∈ B, ⟨a,b⟩ = 0` of the design, which is the `E9` lane's content — and the
localisation into the restricted product `Πʳ_v [H¹(D_v,M), H¹_ur(D_v,M)]` (indexed by the *primes*
of `k`, i.e. the conjugacy classes of finite places) is built in
`PT/pt_localisationRestricted.lean` (`finPlaceConjSetoid`, `exists_restrictedProduct_localization`,
`…_add`).  What is *not* built is the instantiation of the lemma at the arithmetic data; the sister
lane `ZSplit` instantiates the same machinery at the level `↥K` (its files import this one).

**The `C`-block, and a *withdrawn* claim.**  In session 8 I first recorded that the involutions of
`C` cannot be placed inside the restricted product of `PT.restrictedProduct_relaxation` at all.
**That was wrong**, and the correct treatment is now built and proved (section `PtIndexBlock` of this
file): put the `C`-indices inside the restricted product with

* primal family `ptU := ⊤` at a `C`-index, and
* dual family `ptU' := ⊥` at a `C`-index.

Then the two hypotheses of the relaxation lemma are automatic at the `C`-indices, *because `C` is
finite*: the cofinite condition "all but finitely many components lie in `U'`" may exclude all
finitely many `C`-indices, so `U' = ⊥` there imposes **no** condition on the dual values
(`mem_restrictedProduct_ptU'`); `hβ0` is trivial since the dual side is `⊥` (`ptB_zero_at_C`); and
`hU` (`U' = U^⊥`) reduces to the right-non-degeneracy of the local pairing at the involution
(`ptU'_eq_orthogonal_at_C`), which is the archimedean local Tate duality — proved.  The prescribed
set `T` contains `C`, so the relaxation subgroup is `0` there, and the relaxation output then
matches the *`C`-components* of the prescribed data as well; no separate "the `C`-projection of the
dual Selmer module is everything" input is needed.  The *entire* arithmetic input of the
instantiation is thereby confined to the finite places, in exactly the shape the `E7`/`E8` lanes
deliver it:

* `hβ0` at the finite places: the unramified subgroups annihilate each other
  (`ptB_zero_of_localInput`: finite-place input ⟹ the lemma's `hβ0` at every index);
* `hU` at the finite places: the unramified subgroup of the dual side is the annihilator of the
  unramified subgroup of the primal side (`ptU'_eq_orthogonal_of_localInput`);
* the localisation of a global cocycle into the restricted product, indexed by the conjugacy classes
  of finite places: `PT/pt_localisationRestricted.lean`
  (`finPlaceConjSetoid`, `exists_restrictedProduct_localization`, `…_add`);
* the *unrestricted* middle exactness `hAB : a ∈ A ↔ ∀ b ∈ B, ⟨a,b⟩ = 0` — the `E9` lane's content.

**The `C`-block architecture, landed** (section `PtIndexBlock`, all proved and axiom-clean):

* `PtIndex`, `ptGroup`, `ptX`, `ptU`, `ptU'` with `ptU_inl`/`ptU_inr`/`ptU'_inl`/`ptU'_inr`: the
  index type (finite places modulo conjugacy ⊕ the involutions of `C`) and the local data, the
  `C`-indices carrying `⊤` on the primal side and `⊥` on the dual side;
* `badSet_ptU'_subset`, `mem_restrictedProduct_ptU'`: arbitrary values at the `C`-indices are
  admissible in the restricted products;
* `ptB_zero_at_C`: `hβ0` at a `C`-index is free; `ptU'_eq_orthogonal_at_C`: `hU` at a `C`-index is
  the right-non-degeneracy of the archimedean local pairing;
* `ptB_zero_of_localInput`, `ptU'_eq_orthogonal_of_localInput`: the relaxation lemma's `hβ0` and
  `hU` at *every* index, from the **finite-place** inputs only;
* `pt_relaxation_instantiation`: the finite-place-indexed instantiation of
  `PT.restrictedProduct_relaxation` at the `PtIndex` data, with the `C`-block handled — so the
  relaxation step of node `E9` is available in the relaxation's own vocabulary, with its entire
  arithmetic input confined to the finite places.

The remaining bridge to *this node's* vocabulary is the identification of `A`/`B` with the images of
the global classes and of the prescribed set `T` with `S ∪ C` (a reindexing
`∏_{i ∈ T} ptX i ≃ primalClasses p k Ω K M S C`, together with
`PT/pt_localisationRestricted.lean`'s localisation); that bridge is the next piece.

**The local-`H¹` conjugacy transport, landed.**  The reindexing needs the identification of the
local `H¹`'s at *conjugate* places, which the workspace did not have.  It is now built in this file:

* generic subgroup transport (`conjSubSub`, `mem_conjSubSub`, `conjSubSub_conjSubSub_inv`) and the
  transport of the cochain conditions (`isCocycleOn_conjSubSub`, `isLocConstOn_conjSubSub`,
  `isCoboundaryOn_conjSubSub`, `isLocConstOn_const_smul`);
* the cochain-level conjugation shift (`h1locConjShift_apply`, `h1locConjShift_inv_comp`,
  `h1locConjShift_comp_inv`) transferred to the locally constant cocycles
  (`h1locConjShift_mem_lcCocycles_conj`, `h1locConjShift_mem_coboundaries_conj`), giving the linear
  equivalence `lcConjEquiv : ↥(lcCocycles … N) ≃ₗ ↥(lcCocycles … (σ N σ⁻¹))` with the explicit
  inverse `lcConjHomInv`;
* `map_cobQ_lcConjEquiv` (the coboundary submodule is carried onto the coboundary submodule) and
  hence **`h1locConjEquiv σ N : H1loc … N ≃ₗ H1loc … (σ N σ⁻¹)`** via `Submodule.Quotient.equiv`,
  together with `h1locConjEquiv_of_eq` and the place-level form
  **`h1loc_conjEquiv_nonempty : H1loc … (decomp k A) ≃ₗ H1loc … (decomp k B)` for
  `IsConjPlace k A B`** (using `SSGRoute.decomp_conj`).

With this, the reindexing `∏_{i ∈ T} ptX i ≃ primalClasses p k Ω K M S C` is expressible: at the
`S`-indices it is the transport `h1loc_conjEquiv_nonempty` along `IsConjPlace k A (Quot.out (mk A))`
(whose local groups are conjugate), and at the `C`-indices it is the identity.  The identification
of `A`/`B` with the images of the global classes (using `PT/pt_localisationRestricted.lean`) and the
`hAB` input remain.

**State of the two pipeline gaps** (`PT/pt_canonical_relaxed.lean`, 2026-09-28 01:00).  Gap (1)
(`FiniteHalfExistsMixed` = the *canonical* pairing with its mixed reciprocity law) is untouched
(`SSGRoute/canonical_localPairing_with_reciprocity.lean` and
`PTembedding/localTatePairing_canonical.lean`, both filed, both stalled since 2026-09-26; the `E7`
and `E8` lanes supply the clause halves, the canonical *construction* is the missing piece).  Gap (2)
is this node.  The `E9` lane (`E9Nodes/`, `E9c/`) is building the `Ext`/`phiAt` machinery for the
unrestricted middle exactness; the `E7b` lane (`PT/AlphaTwo*`, `PT/DevissageSES*`) is running the
five-lemma dévissage of Milne I.1.8; `PT/h3loc_decomp_subsingleton.lean` (node `E7a`'s
`cd_p ≤ 2`) and `PT/euler_cyclicCase_primeToP.lean` (node `E7a`'s `hgen`, Milne I.2.11) are **still
unfiled**, although `PT/EULER_RESIDUECHAR_STATUS.md` refers to them both.


## Session 9 (2026-09-28, ~08:30–10:00): the relaxation instantiation made *usable*, the prescribed
## index set `ptT`, and the `p = 2` obstruction recorded

**Twelve new declarations, all proved** (the first batch measured axiom-clean,
`[propext, Classical.choice, Quot.sound]`; the later ones use the same ingredients only):

* **`pt_relaxation_instantiation_of_dualPair`** — the same statement as
  `pt_relaxation_instantiation`, but with the two compactness hypotheses `hAcomp`/`hBcomp` replaced
  by the single `hBcl` ("the annihilator of `A` is `B`").  This is the **usable form at the
  arithmetic data**: the restricted product over the infinite index set `PtIndex k Ω C` is *not*
  compact and the image of the global classes there need not be closed (`pt_selmer_relaxed.lean`,
  §"The relaxation, made concrete", item (c) — the obstruction is real: `B` is a countable subgroup
  of a non-compact group, cf. the `ℚ ⊆ 𝕋` analogy), whereas `hBcl` is exactly the shape in which
  node `E9` delivers the duality.  The compactness-free relaxation step itself is
  `PT.restrictedProduct_relaxation_of_dualPair` (`PT/restrictedProduct_relaxation_of_dualPair.lean`,
  proved, by another lane): it uses compactness at exactly one place, through
  `PT.pt_compact_annihilator_dual`, only to derive `hBcl`; that lemma is strictly more general
  (`hBcomp` + `hAB` imply `hBcl`), so nothing is lost.
* **`finite_ptX`** — `∀ i : PtIndex k Ω C, Finite (ptX p k Ω K M C i)`, from `PT.finite_H1loc` (a
  finite place) and `PT.finite_H1loc_zpowers` (an involution, hence `hCinv`).  This discharges the
  three `∀ i, Finite (ptX …)` instance arguments of the instantiation — they were *inputs* until now;
  the local `H¹` of a decomposition group with finite coefficients is finite because a locally
  constant cocycle is determined by its values on a finite transversal of `D_A ⊓ G_K` and on the
  continuous homs of that (open, `K`-finite) kernel (`local_tate_duality_finite.lean`).
* **the prescribed index set** `ptT k Ω S hSfin C` (one index per conjugacy class of a place of
  `S`, one per involution of `C`) with `mem_ptT_inl`, `mem_ptT_inr` and the decomposition
  **`mem_ptT_iff`**: `i ∈ ptT ↔ (∃ A ∈ S, i = inl (mk A)) ∨ (∃ c ∈ C, i = inr c)`;
* the *named* index maps **`ptTIdxInl` / `ptTIdxInr`** (with `ptTIdxInl_val`, `ptTIdxInr_val` by
  `rfl`), which keep the heavy membership proofs out of the statements that use them, and the
  bookkeeping of those maps: **`ptTIdxInl_injective`** (needs `hSdisj`: two places of `S` in the same
  conjugacy class are conjugate, hence equal), **`ptTIdxInr_injective`**,
  **`ptTIdxInl_ne_inr`**, and **`ptT_card : (ptT k Ω S hSfin C).card = S.card + C.card`** — the
  counting bookkeeping of the prescribed data (one place per prime, one involution per class).
* **the transport at the canonical representative**: `isConjPlace_out_mk`
  (`Quotient.mk_out`), `ptT_conjEquiv_nonempty` and its `ptX`-form `ptT_ptX_conjEquiv_nonempty` —
  the local `H¹` at the index of a place `A ∈ S` is that of `A` up to conjugacy
  (`h1loc_conjEquiv_nonempty`).  With this, the **only** missing piece of the reindexing
  `∏_{i ∈ ptT} ptX i ≃ primalClasses p k Ω K M S C` is the `Equiv` itself (glue the named
  transports on the `S`-indices and the identity on the `C`-indices; injectivity on the `S`-block is
  `ptTIdxInl_injective`).

**A real obstruction, recorded so that it is not re-derived: `p = 2` and the identity `U' = U^⊥`.**
`PT/relaxation_annihilator.lean` (proved, another lane) shows that the hypothesis
`hU : y ∈ U' i ↔ ∀ x ∈ U i, β i x y = 0` of the relaxation *fails* at `p = 2` when both `U` and `U'`
are the arithmetic unramified subgroup: `dim H¹(ℚ₂, μ₂) = 3` while `dim unr = 1`, so
`unr ⊊ unr^⊥` (for odd `p` the inertia-vanishing subgroup is Lagrangian and `hU` holds).  Hence
*this file's* instantiation (`ptU = ptU' = unramified` at the finite places) is correct for odd `p`
and must be replaced at `p = 2` by the **annihilator form**
`PT.restrictedProduct_relaxation_annihilator` (`U' := dualConditions β U`), whose residual obligation
is the identification (at `p = 2`) of the annihilator conditions with the arithmetic dual Selmer
conditions.  Note that at the `C`-indices this issue does *not* arise: there the primal family is
`⊤` and the dual family `⊥`, so `hU` is `⊥ = ⊤^⊥`, i.e. trivial.

**Three elaboration hazards of this file's vocabulary** (all measured this session):

1. A statement that mentions `Classical.choice (ptT_ptX_conjEquiv_nonempty …)` *directly* runs into
   `whnf` timeouts (`800000` heartbeats) — the `ptX`/`ptGroup`/`H1loc` types are too heavy to
   compare.  Introduce a **named** `def` for the chosen transport and mention only that.
2. Statements about `ptT` written inside a section with unused variables (`p`, `K`, `M`) acquire
   those as *leading explicit* arguments (`mem_ptT_inl C hA` was rejected as `@mem_ptT_inl (↥C) hA`);
   call such lemmas with named arguments, or place them in a section carrying only the variables
   they use (as the `PtIndexBookkeeping` section of this file does).
3. `Finset.card_image_of_injective` must see the *same* function as the goal (`unfold ptT` first);
   stating injectivity through a `def` (`ptTIdxInl`) does not match the lambda in the unfolded
   `Finset.image`, so `ptT_card` proves the lambda-injectivity inline.

**The forward half of the annihilator identity, proved, and the sharpest reduction of the node.**

* `primalClassSet_orthogonal_dualClassSet` — **every realizable class is orthogonal to every relaxed
  dual Selmer class**, under a pairing `B` on the local `H¹`-spaces that agrees with the local family
  `pair` on local classes (`hB`, `hBc`): the reciprocity half of the middle exactness.  It is the
  `hVW` argument of `pt_selmer_relaxed_assembly`, extracted as a standalone theorem: the *proved*
  `PT.pt_orthogonality_of_realizable` (Hasse reciprocity) applied with the reciprocal place set
  `PT.exists_reciprocal_set`, glued to the goal by the product-formula
  `PT.productFormFun_primalClassOf`.  Its inputs are the pipeline's `pair`, `hloc` (the local clauses)
  and `hrec` (the mixed reciprocity law), i.e. *no* new arithmetic.
* **`countingIdentity_of_reciprocity_and_converse` — the sharpest reduction in this file.**
  `CountingIdentity` follows from the pipeline inputs (`pair`, `hloc`, `hrec`), from the **converse**
  inclusion `W^⊥ ⊆ V`, and from the finiteness of the two class spaces: the inclusion `V ⊆ W^⊥` is
  *no longer an input*.  So the node now owes exactly *one* mathematical statement — the
  realizability half of the middle exactness of the relaxed Poitou–Tate sequence — together with the
  pipeline's local pairing and reciprocity, exactly as `PT.pt_canonical_relaxed_of_inputs` consumes
  them.

**The reindexing, delegated with the transports as a hypothesis.**  The `Equiv`
`∏_{i ∈ ptT} ptX i ≃ primalClasses p k Ω K M S C` is filed as
`SSGRoute/PT/ptT_equiv_primalClasses` (**PROVED** by the colleague `H343-L1837`: 306 lines, sorry-free, axiom-clean; `Submission/Work/SSGRoute/PT/ptT_equiv_primalClasses.lean`) in the form that keeps
the elaboration cheap: the conjugacy transports are a *hypothesis*
`e : ∀ A ∈ S, ptX … (ptTIdxInl … A).1 ≃ₗ H1loc … (decomp k A.1)`, and the conclusion is the `Equiv`
together with its two component formulas (`(Φ ξ).2 c = ξ (ptTIdxInr … c)` and
`e A (ξ (ptTIdxInl … A)) = (Φ ξ).1 A`).  The review gate caught a genuine omission in the first
version: **without `hSdisj` the statement is false** — if two places of `S` are conjugate then the two
component formulas force the corresponding two coordinates of `Φ ξ` to be equal, so `Φ` cannot be
surjective (the domain has one factor per conjugacy class, `primalClasses` one per place of `S`).
With `hSdisj` the `Equiv` is the natural reindexing and its injectivity is `ptTIdxInl_injective`.
For instantiation, the chosen transport is **`ptXConjEquiv`** (the conjugacy transport along
`isConjPlace_out_mk`, chosen once and for all).  Note that naming it was *necessary*: defining it in
the `ptTIdxInl` form (i.e. with the argument `(ptTIdxInl … A).1` rather than the raw
`Sum.inl (mk A)`) times out at `whnf` even with `maxHeartbeats 2000000`, so it is stated at the raw
index.

**Lane state at the end of this session** (file mtimes, 2026-09-28 ~10:00): `PTCore/h3loc_decomp_subsingleton.lean`
(node `E7a`'s `cd_p ≤ 2`, 07:25, still one `sorry`, *live*: it has been split into the tame case and
the residue-characteristic case, the latter needing the Demushkin input) ; `PT/milne18_kummer_base.lean`
(05:12, live) and `PT/milne18_at_zero.lean`, `PT/localDuality02.lean` (node `E7b`); the `E9b` lane's
`chi_pTor_classLevelLimit.lean` (the `χ` interface, leg (b) of `E9`); `PT/pt_sub_counting_identity_v2.lean`
(06:23, *imports this file*, the same single hole at the sub-base `k₀`); `PTCore/cyclic_vanishes_clean.lean`
(08:19, the cyclic case of `E7a`'s `hgen`).  `PT/euler_cyclicCase_primeToP.lean` is *still unfiled*
(the cyclic computation is being done under other names).  `request_lemma` was refused three times
("the team is busy"), so everything new in this file was proved here.

## Session 10 (2026-09-28, ~17:00–24:00): the localisation, the pairing identity of the prescribed
data, and the bridge `converse_of_relaxation`

Three new modules of this lane (all `sorry`-free, all axiom-clean
`[propext, Classical.choice, Quot.sound]`), carrying the *assembly* of the node from the relaxation
output; see `PT/PT_COUNTING_IDENTITY_STATUS.md` §7–§8 for the full statement list and the recipes.

* `PT/pt_localisationSelmer.lean` — `ptLocFin`(+`_apply`), `mem_restrictedProduct_of_finite_bad`,
  `ptLocFunRaw`, `ptLocCocycle`, `primalSelmerToCocycles`, **`ptLocPrimal`**, **`ptA`**
  (+ the abbreviation `ptRPprimal`): the localisation of the relaxed primal Selmer module into
  `Πʳ i : PtIndex k Ω C, [ptX M i, ptU M i]`, with the computation rule "the component at an index
  is the local class of the global cocycle".
* `PT/pt_localisationSelmerDual.lean` — the same for the Tate dual `M^∨(1) = DualMod p (M ⊗ T)` and
  the family `ptU'`: `dualSelmerToCocycles`, **`ptLocDual`**, **`ptB'`** (+ `ptRPdual`).
* `PT/pt_converse_of_relaxation.lean` — **`sum_ptT_eq_productFormFun`** (the pairing of the
  prescribed data against the localisation of a dual Selmer class is the product form, under the
  transport rules `he'` and the pairing compatibility `hcompat`), **`converse_of_relaxation`** (the
  converse inclusion `W^⊥ ⊆ V` of the node from the *relaxation output* `hrelax`), and the bundled
  `PtRelaxationOutput`.

Delegated and **proved** by colleagues this session (all importable):
`Work.SSGRoute.PT.h1locConjEquiv_toClass` (`PT/h1locConjEquiv_toClass.lean`),
`Work.SSGRoute.PT.toClass_h1locConjShift_eq` (`PT/toClass_h1locConjShift_eq.lean`) — the class rule
of the conjugacy transport and the invariance of the class of a global cocycle under the conjugation
shift; and (in flight at the end of the session)
`Work.SSGRoute.PT.exists_conjTransport_toClass` (`PT/exists_conjTransport_toClass.lean`).

**The node now reduces to three groups of inputs** (see §8.4 of the status file): (1) `hAB`/`hBcl`
at `ptA`/`ptB'` — node `E9`; (2) the local clauses `hβL`,`hβR`,`hβ0fin`,`hUnram` (with the `p = 2`
annihilator-form caveat); (3) the transports `e`,`e'` with `he`,`he'` (`exists_conjTransport_toClass`)
and `hcompat` (canonicity of the local pairing).  Given them, `converse_of_relaxation` gives the
converse inclusion and `countingIdentity_of_reciprocity_and_converse` gives `CountingIdentity`.

## Session 11 (2026-09-29, ~01:10–03:00): the *formal* part of the node is CLOSED

Three new `sorry`-free, axiom-clean modules of this lane complete the *formal* (non-arithmetic)
reduction of this file's target — the node is now one application of a single theorem once its
inputs exist (see `PT/PT_COUNTING_IDENTITY_STATUS.md` §10 for the full account):

* `PT/pt_relaxationOutput_of_inputs.lean` — `PT.pt_relaxationOutput_of_inputs`: the bundled
  relaxation output `PtRelaxationOutput` from `hAB`, `hBcl`, `hTRam` and the four local clauses;
* `PT/pt_counting_of_relaxation.lean` — `PT.countingIdentity_of_localAxioms_and_relaxationOutput`:
  the target from `pair`/`hloc`/`hrec`, the relaxation output, `hcompat` and finiteness;
* `PT/pt_counting_reduction.lean` — `PT.ptPair` (the pairing `localPairingFun pair hloc` on the
  indices of `PtIndex`), `PT.pt_relaxationOutput_of_localAxioms` (the relaxation output with the
  local non-degeneracy *derived* from `hloc`), and

  **`PT.countingIdentity_of_localAxioms_and_middleExactness`** — this file's target from exactly:
  the local Tate system `pair`/`hloc`, the reciprocity law `hrec`, the two unramified-subgroup
  clauses `hβ0fin`/`hUnram`, the middle exactness `hAB` (with its separation companion `hBcl` and
  the support condition `hTRam`), the conjugation compatibility `hcompat`, the data
  (`hSfin`,`hSdisj`,`hSram`,`hCinv`,`hC`,`hCdisj`) and the finiteness of the two local class spaces.

Everything else in the chain is derived in-tree: the local non-degeneracy, `V ⊆ W^⊥`, the counting
step, `Nat.card P = Nat.card P'`, the localisation images `ptA`/`ptB'`, `ptT`, `ptTPhi`, and the
conjugacy transports `ptConjTransport` (with their class rules).  The residual is therefore exactly
the *arithmetic* package `E7`-canonical (`pair`,`hloc`,`hβ0fin`,`hUnram`,`hcompat`) + `E8` (`hrec`)
+ `E9` (`hAB`,`hBcl`) of the Poitou–Tate workshop — nothing formal.

Also repaired in this session (see §10.3 of the status file): the node's copy of the linear-algebra
lemma `finrank_eq_of_nondegenerate_pairing` was renamed to
`pt_finrank_eq_of_nondegenerate_pairing`, removing a duplicate-declaration clash with
`PT/localTatePairing_deg02.lean` that prevented any module from importing both the `PT/mkb_euler`
closure and this file.

## Session 12 (2026-09-29, ~06:00): the *sharpest* reduction of the target

The node's target is now implied by the **sub-base package** as well — the *same* package that the
sub-base node `PT.pt_sub_counting_identity_v2` consumes:

* `PT/pt_counting_via_subbase.lean` — **`PT.countingIdentity_of_subbasePackage`**: this file's target
  from `pair`/`hloc` (the local Tate system), `hrec` (reciprocity), the isotropy clause `h𝓤`,
  the separation clause `hBcl` (the relaxed Poitou–Tate middle exactness with the dual local family
  *defined* as the annihilator family), `[Finite M]`, `hT` and the data.  It is the two-line
  instantiation of `PT.pt_sub_counting_identity_v2_of_duality` at `k₀ := k`
  (`PT/sub_counting_final.lean`) through `PT.pt_sub_counting_identity_v2_self_iff`
  (`PT/pt_sub_counting_identity_v2.lean`), the sub-base predicates at `k₀ = k` being the level-`k`
  ones.

This package is satisfiable at **every** prime `p` (no Lagrangian clause, no conjugation-compatibility
clause), and it has four arithmetic inputs against the seven of the all-places package
(`countingIdentity_of_localAxioms_and_middleExactness_offRam`, `PT/pt_counting_reduction.lean`,
which remains the interface matching the shape of `SSGRoute/E9_STATUS.md`'s `E9` deliverable).  See
§12 of `PT/PT_COUNTING_IDENTITY_STATUS.md` and `PT/PING_subbase_closes_level_k.md` — the `E7`/`E8`/`E9`
lanes now have a *single* target for both counting identities.


## Session 13 (2026-09-29, evening): the `α¹` route's *formal* part is CLOSED (the two-pass
## induction of Milne *ADT* I.1.8(b) at `r = 1`), and the node's remaining inputs are named

The node's residual (`G1` + `hBcl`) is unchanged, but the `G1` half is now reduced to *named*
arithmetic inputs, because the Shapiro/cup transfer and the two-pass descent of `α¹` are on disk.
Three new modules of this lane (all `lake build`-green, `#print axioms` = `[propext,
Classical.choice, Quot.sound]`; see `PT/NOTE_alphaOne_assembly_done.md` for the full write-up):

* `PT/alphaOne_coind_transfer.lean` — the `α¹` Shapiro/cup square (`PT.akShapiroBijective`'s
  `alphaOne_coind_eq_cor`) re-read as the factorization
  `α¹_G(Coind) = postCorFun ∘ preShapiroFun ∘ α¹_U ∘ sourceMap`, and the *transfer* in the `(β)`
  (post-composition with the corestriction) form, in all three one-sided shapes the two passes of
  the five lemma consume: `AlphaOneCoind.alphaOne_coind_bijective_of_cor`,
  `…_surjective_of_cor`, `…_injective_of_cor` (the `α¹` twins of the `α²` lane's
  `alphaTwo_coind_bijective_of_cor`);
* `PT/alphaOne_devissage_data.lean` — the instantiation of `PT.alphaOneExactness`'s one-sided
  descents at the dévissage `0 → N → Coind^G_U N → devissageM1 U → 0` of an open finite-index
  `U ≤ G` acting trivially on `N`:
  **`PT.alphaOne_surjective_of_devissage_data`** (the first pass) and
  **`PT.alphaOne_bijective_of_devissage_data`** (both passes), from the trivially-acting base case
  at `U` (Kummer/Hilbert ⟸ local CFT), the `(β)`-input at `U` (*ADT* (1.1b)), `α²` at the two ends
  (the `mkb_ld02_core` chain ⟸ `cd_p ≤ 2`), the `𝔽_p`-linearity facts of the dévissage and the
  first pass at the quotient;
* `PT/kerAction.lean` — `kerAction G N` (the intersection of the stabilisers), open for a discrete
  action on a finite module (`isOpen_kerAction`), of finite index (`finiteIndex_kerAction`): the
  subgroup Milne's induction feeds into the dévissage;
* `PT/devissageSES_linearity.lean` — **the `𝔽_p`-linearity of the dévissage SES, at a canonical
  site** (`devissageSESDef_{pi,iota,delta}_smul_site`), pushed through `AKZmodLin.mapH1_smul` to the
  exact `hlinψ`/`hlinφ` slot shapes (`mapH1_devissageSESDef_{pi,iota}_smul`).  Since
  `Coind G U M` is a subtype, its `ZMod p`-scalar action has two (extensionally equal, syntactically
  different) instances, and `exact`-ing the `devissageLinear` lemmas fails with `Type mismatch`; the
  working route is to prove the facts *directly at the fresh site* (`rfl` for `pi`, the pointwise
  `Subtype.ext` computation for `iota`, the stored `SESDef`-form for `delta`).  Consequence:
  `PT.alphaOne_{surjective,bijective}_of_devissage_data` carry **no** linearity hypotheses.
* `PT/akH1_exponent.lean` — `H1_nsmul_eq_zero` (`H¹(G,N)` has exponent `p` when `N` does), the input
  that lets `AlphaOneCoind.postCorFun_*_of_ptorsion` turn the `p`-torsion arithmetic
  (`PT.corH2_bijective_units_openSubgroup`, i.e. *ADT* (1.1b)) into the `(β)`-hypothesis of the
  transfer.

**`(β)` is *not* a constraint on `U`.**  The double-coset identity `cor ∘ res = [G:U]·id`
(`PT.corH2_resH2`) tempts one to read `cor` as multiplication by the index on the `p`-torsion and
hence to require `p ∤ [G:U]` (and then `U ⊆ kerAction G N`); but the map that occurs is `cor`
itself, which under the *canonical* local invariants `H²(·,\bar k_v^×) ≅ ℚ/ℤ` is the **identity**
(`inv_{D_A}(cor β) = inv_U(β)`, the compatibility (1.1b)).  It is proved unconditionally — at every
open `U`, with no coprimality — as `PT.corH2_bijective_units_openSubgroup` (on the `p`-torsion,
which is all the base cases need since the hom-groups involved have exponent-`p` domains), and
`PT.hcor_of_corH2_ptorsion` bridges it to the post-composition shape used here.  So the two passes
are *not* blocked for modules whose Galois action has `p`-power image.

## Session 14 (2026-09-30, ~04:00): Milne *ADT* I.1.8(b) at `r = 1` is PROVED (the whole two-pass
## assembly), so the `α¹`/`h4` half of `G1` is now exactly three named arithmetic inputs

`PT/alphaOne_devissage_data.lean` (session 13) instantiates the two passes of Milne's five-lemma
descent at the dévissage of an open finite-index subgroup, but its *second* pass carries the
surjectivity of `α¹_G(N₁)` at the quotient as a hypothesis.  Session 14 performs Milne's
uniform-surjectivity bookkeeping and obtains, with **no leftover hypotheses**, a new module

* `Submission/Work/SSGRoute/PT/alphaOne_uniform.lean`
  (module `Submission.Work.SSGRoute.PT.alphaOne_uniform`), `lake build`-green, every declaration
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`:

  | declaration | content |
  |---|---|
  | `PT.finite_coind` | `Finite (Coind G U M)` from `[U.FiniteIndex]`, `[Finite M]` — *no* normality and *no* trivial-action hypothesis (via `PT.coindEquivFun`) |
  | `PT.finite_devissageM1` | `Finite (devissageM1 U)` |
  | **`PT.alphaOne_bijective_of_uniform_data`** | **Milne *ADT* 1.8(b) at `r = 1`**: `α¹_G(N)` bijective from the trivially-acting base case at every open `U`, the `(β)`-input, and `α²` bijective for all finite modules |
  | `PT.baseShape_of_kummerHilbertBase` | the named node `PT.KummerHilbertBase` in the exact shape the descent consumes |
  | **`PT.alphaOne_bijective_of_cyclic_base`** | the same with the base case in the *book's* shape: `PT.KummerHilbertCyclic p U (Additive Ωˣ)` for every open `U`, i.e. Milne's hypothesis "`α¹(U,ℤ/mℤ)` bijective for all open `U`, `m`" at `m = p` (the perfectness of the Kummer/Hilbert pairing), through the proved `PT.kummerHilbertBase_of_cyclic` |

  (`PT.alphaOne_bijective_of_data`, delegated the same session and landed separately, removes the two
  subgroup choices `U`/`U₁` by instantiating them at `PT.kerAction G N` and
  `PT.kerAction G (devissageM1 (M := N) U)`; `Submission/Work/SSGRoute/PT/alphaOne_data_expP.lean`
  provides the `_expP` variant of it — see below.)

  **The `(β)`-hypothesis must be restricted to `𝔽_p`-modules** (`_expP` forms).  Asking `hcor` at
  *all* finite `G`-modules is a hypothesis nobody can discharge: the only route the tree supports is
  `PT.AlphaOneCoind.postCorFun_bijective_of_ptorsion`, which needs
  `hVp : ∀ v : H¹(G, Coind^G_U N), p • v = 0` from `PT.H1_nsmul_eq_zero`, whose hypotheses include
  `[Module (ZMod p) (Coind^G_U N)]` — without the `ZMod p`-structure on `N` one cannot even *state*
  `hVp`.  The `_expP` variants ask for `hcor` only at finite `𝔽_p[G]`-modules `N` with trivial
  `U`-action, which is all the assembly consumes (`N` and `N₁ = devissageM1 U` are `𝔽_p`-modules).
  The unrestricted forms under the plain names are kept as wrappers.  The complete, usable interface
  is therefore `PT.alphaOne_bijective_of_data_expP` (`PT/alphaOne_data_expP.lean`).

  **At the local data the input list shrinks to two.**  `Submission/Work/SSGRoute/PT/alphaOne_local_data.lean`
  proves `PT.alphaOne_bijective_decomp`: for a finite place `A` of an algebraic closure `Ω` of a
  number field `k` and every finite discrete `𝔽_p[D_A]`-module `M`,

    `Bijective (PT.alphaOneMap (G := ↥(SSGRoute.decomp k A)) (N := M) (C := Additive Ωˣ) _)`

  follows from `hcyc` (the Kummer/Hilbert perfectness at every open `U ≤ D_A`) and `hα₂` (`α²`
  bijective for all finite modules) **alone** — `hcor` is discharged by the delegated
  `Work.PT.hcor_local_data` (`Submission/Work/PT/hcor_local_data.lean`, the local form of
  `PT.AlphaOneCoind.postCorFun_bijective_of_ptorsion` from `PT.corH2_bijective_units_openSubgroup` +
  `PT.H1_nsmul_eq_zero`, i.e. *ADT* (1.1b)), and `hCdisc` by
  `PTembedding.MupCard.isDiscreteModule_decomp_addUnits`.  This is the ready-made input of the
  `hclass`/`h4` route (instantiate at `M := DualMod p (M₀ ⊗ T)`), and it validates the interfaces of
  three lanes at once.  Its two remaining inputs are the *named* arithmetic nodes
  `PT.KummerHilbertCyclic` (delegated this session as `SSGRoute/PT/kummerHilbertCyclic_decomp`) and
  `α²`-bijectivity (the `PT/AlphaTwoAssembly.lean` + `PT/AlphaTwoDevissageAux.lean` lane).

  The `hclass` route's other bridge, the **Kummer injection** `H²(D_A, μ_p) ↪ H²(D_A, Ωˣ)`, is
  proved in `Submission/Work/SSGRoute/PT/kummerH2Injective.lean` (`PT.injective_mapH2_of_subsingleton_H1`,
  `PT.injective_mapH2_addUnits_of_decomp`, `PT.kummer_h2_decomp_injective`).  See
  `PT/PING_hclass_bridges.md` for the whole ledger, including the warning that `decomp k A` is a
  **closed** subgroup of *infinite* index — hence not open — so neither the absolute Hilbert 90 nor
  the open-subgroup one applies to it (use `PTembedding.MupCard.hilbert90_decompH1`).

  **The Kummer/Hilbert arithmetic is now one-sided.**  `PT/kummerHilbertCyclic_decomp.lean` split
  `PT.KummerHilbertCyclic` into left non-degeneracy plus the *counting* (finiteness and equal
  `Nat.card` of the source and target of `α¹`); the counting is **proved**
  (`PT/kummerHilbertCyclic_finite_card`), and injective + equal cardinality = bijective, so

    `PT.kummerHilbertCyclic_of_leftNondeg` (`PT/kummerHilbertCyclic_leftNondeg.lean`) :
      `PT.KummerHilbertLeftNondeg p k Ω A  ⟹  KummerHilbertCyclic p U (Additive Ωˣ)` for all open `U`.

  Its classical content is Milne *ADT* (1.7)/(0.14) — "the cup product is the norm-residue symbol" —
  plus the density of the reciprocity map; it is *the* last arithmetic input of the `α¹` layer and it
  is the same frontier as the `E7Fin`/`HRec` `hclass` obligation and the
  `ZDataMup.localTate_reciprocityFamily` gate.  The node is filed, with a detailed roadmap, as
  `Submission/Work/SSGRoute/PT/kummerHilbertPairing_leftNondegenerate.lean`.

  **The project state (2026-10-01).**  The `E7Fin` lane closed the whole *formal* chain
  `α¹ ⟹ hclass ⟹ h4L ⟹ h4 ⟹ G1` (`E7Fin/hclassAssembly.lean`, `E7Fin/h4FromAlphaOne.lean`,
  `E7Fin/G1FromArithmetic.lean`; see `E7Fin/PING_hclass_assembly_done.md`), consuming this file's
  `PT.alphaOne_bijective_of_cyclic_base_expP` (through the `_pt` port
  `E7Fin.alphaOneMap_injective_decomp_of_cyclic_pt`, which additionally corrects the `hα₂`-binder —
  the `hα₂` of the wrappers *in this lane* is asked for at all finite modules and is **not**
  dischargeable, see `PT/PING_hclass_bridges.md` §7).  So this node's residual is now

    `COUNT  ⟸  hBcl`  (the relaxed Poitou–Tate middle exactness; sub-base/`PTCore` lanes)

  + the named arithmetic inputs of `G1` (`hLeft` = `KummerHilbertLeftNondeg` above, `hnz`, `hdim`,
  the `hα₂_pt` form — proved as `E7Fin.alphaTwo_bijective_finite_module_pt` — and `ArchConsistent`
  at `p = 2`).  Nothing of the `α¹` layer is outstanding.

  Consequence for the node: `G1`'s `h4` half (local Tate duality in degree one = bijectivity of
  `α¹` at the local data) is now **reduced to exactly four named inputs**:
  (i) `hcyc` = the perfectness of the Kummer/Hilbert pairing at every open subgroup (local CFT —
  Milne *ADT* I.2.1), (ii) `hcor` = the `(β)`-input of Shapiro's transfer, i.e. that post-composition
  with `cor` on the relevant hom-group is bijective (Milne's (1.1b); the `p`-torsion
  bijectivity is the *proved* `PT.corH2_bijective_units_openSubgroup`, bridged by
  `PT.hcor_of_corH2_ptorsion`; its local-data form is the delegated `Work.PT.hcor_local_data`),
  (iii) `hα₂` = `α²` bijective for all finite modules (the `PT/mkb_ld02_core_of_h3` chain
  ⟸ `cd_p ≤ 2`), and (iv) `hCdisc` = discreteness of `C = Additive Ωˣ`.  *Nothing else* — the
  dévissage, the exactness of both rows, the Leibniz square, the Shapiro transfer, the two passes
  and the `𝔽_p`-linearity are all on disk.

  **Measured hazards (do not rediscover).**  (`a`) `Fintype (G ⧸ U)` is *not* synthesized from
  `[U.FiniteIndex]` in a statement (`Subgroup.fintypeQuotientOfFiniteIndex` carries
  `instance_reducible` only on its `to_additive` twin): it must be an explicit binder or a
  `letI`/`haveI` at the use site; that is why the `(β)`-hypothesis above carries `[Fintype (G ⧸ U)]`.
  (`b`) `Function.Bijective` is `Injective ∧ Surjective`, so `.1` is the *injectivity* and `.2` the
  *surjectivity* half — the two one-sided descents take them in the opposite order from their
  names' first letters.  (`c`) A hypothesis stated in the `G`-valued membership form
  (`∀ u : G, u ∈ U → …`) must be passed as such; the `↥U`-valued form
  `fun u n => htriv u u.2 n` is for `PT.isDiscreteModule_of_smul_eq` and for `KummerHilbertBase`,
  not for the descent's own `htriv` slot.  (`d`) `Subgroup.fintypeQuotientOfFiniteIndex` *is* an
  instance for `Fintype (G ⧸ U)` in *proof* position (cf. (`a`), it is only the statement-position
  elaboration that balks).

## Session 23 (2026-10-01, evening): the relative Kummer dictionary (piece 1 of the `hcyc` roadmap)

The node's residual is unchanged (`G1` + `hBcl`, both on the arithmetic frontier).  This session
shipped the **Kummer dictionary at a level group** — piece 1 ("Kummer theory for the source") of the
roadmap of `PT/kummerHilbertPairing_leftNondegenerate.lean`, i.e. of `G1`'s `hcyc` slot — as a new
`sorry`-free, axiom-clean module:

* `PT/kummerRelative.lean` (module `Submission.Work.SSGRoute.PT.kummerRelative`):
  * `PT.h0_addUnits_fixingSubgroup_equiv` : `Additive Fˣ ≃+ H⁰(H, Ωˣ)` for `H = F.fixingSubgroup`
    (Krull correspondence);
  * `PT.kummer_rel_delta` : the connecting map `δ : H⁰(H,Ωˣ) →+ H¹(H, DualMod p T)` of the Kummer
    sequence is **surjective** (Hilbert 90, `PT.hilbert90_H1_fixingSubgroup`) with
    `ker δ = range (mapH0 S.pi)`;
  * `PT.kummer_rel_equiv` : `H⁰(H,Ωˣ) ⧸ p·H⁰(H,Ωˣ) ≃+ H¹(H, DualMod p T)`;
  * `PT.kummer_rel_addUnits_equiv` : the classical form `Fˣ/Fˣ^p ≃+ H¹(H, DualMod p T)`;
  * `PT.kummer_rel_equiv_of_cyclotomicDual` / `PT.kummer_rel_addUnits_equiv_of_cyclotomicDual` :
    the same two, instantiated at `PT.kummerSES_dualMod`;
  * the two children **landed** (same file family, each `sorry`-free and axiom-clean):
    `PT.kummer_rel_rootsOfUnity_equiv` (`≃ H¹(H, Additive (rootsOfUnity p Ω))`) and
    `PT.kummer_rel_conjHom_equiv` (`≃ H¹(H, ConjHom (TrivMod ↥H p) (Additive Ωˣ))` — the *source
    module of `PT.alphaOneMap`*, i.e. the dictionary in the vocabulary of the `hcyc` lane).
  `#print axioms` of every landed declaration is `[propext, Classical.choice, Quot.sound]`.
  The measured statement-level hazards are recorded in `PT/PING_kummer_relative_done.md` §5.

### The node's residual, as sharpened today by the sibling lane

`PT/NOTE_count_residual_value_formula.md` (written 2026-10-01 22:14 by the owner of
`PT.pt_selmer_counting_identity`) measures that **`E9` is complete in the `Ext` vocabulary modulo
the single node `C6`** (`E9a`/`E9b`/`E9c`, `PT.exists_glue_extLoc`, `PT.extLoc_yonedaPair`,
`PT.pt_extSegment_exact`, and `pt_sha2_core`/`pt_sha2_core_clean` are all `sorry`-free, with `C6` as
their only taint), and that the node's residual is

> `COUNT  ⟺  G1  +  (VF)`,

where **(VF)** (the *value formula*) is: for `x ∈ Ext¹_G(M', 𝕀_K)` and `h ∈ H¹(k,M')`,

  `phiAt (extToClasses x) h = 0  ⟺  ⟨x, loc h⟩ = 0`,

i.e. *`α = extToClasses` is the transpose of the localisation `loc` under the local Tate pairings*
("the invariant of a global class is the sum of the local invariants of its idèle-localisations").
Given (VF), `W^⊥ ⊆ V` is three lines (via the *proved* `E6` = `SSGRoute.phi1_mono_sylow_in` and the
*proved* clause (i) of `PT.pt_extSegment_exact`), and `V ⊆ W^⊥` is the proved reciprocity.  The
whole of (VF) is the single compatibility of the invariant map `χ` (`SSGRoute.pt_char_pTorsion`)
with inflation/localisation; the `⟸` half in the special case of *vanishing local classes* is the
proved `SSGRoute.e9c_phiAt_eq_zero_of_local`, and the sum decomposition over orbit-supported pieces
is the proved `SSGRoute.e9_glue_phiAt`.  **A future session should aim at (VF) — not at `hBcl` in
the restricted-product form, which re-wraps the same statement** (see the warning in §7 of
`PT/pt_sub_counting_identity_v2.lean`).

**Re-scoped the same evening (measured; see `PT/ACTION_value_formula.md` §7–§8).**  The
"sum of invariants" formulation of (VF) is *not* reachable by composition: the tree has **no
concrete global invariant map** (only the abstract `χ` of `SSGRoute.pt_char_pTorsion`, and the
*local* invariants `NK.NUV2.LC.localInvariant` / `NK.NUV2.RouteC.invariantOf`), while
`NK.GlobalCFTdeep.hbnUnits` and `NK.HassePrinciple.HBNIdele` are **component zero-tests**
("all localisations trivial ⟹ the class is 0"), not invariant comparisons.  The decisive find is
that the *component* zero-test is already available in the E9/Ext vocabulary:
**`Work.SSGRoute.extIdele_localisation_injective_of_finite`** (proved, `0 sorry`,
`extToIdeles_eq_zero_iff_extLoc.lean`, any finite `M` over `ℤ` and any degree `r`).  Hence
**(VF) = (A) + (B)**: (A) = the reciprocity half (`G1`'s clause (7) `hrec`, proved — its `PtIndex`
face is `PT.primalClassSet_orthogonal_dualClassSet`), and (B) = the converse, which is the only new
content and reduces to "the *annihilator* family turns pairing-orthogonality into
component-vanishing (local Tate duality, `G1`'s clause (4) `hloc`), and then
`extIdele_localisation_injective_of_finite` finishes" — the annihilator mechanism being exactly what
`PT/sub_ptindex*.lean` and `PT/relaxation_annihilator.lean` implement.  So (B) is the node's true
residual, stated at the class level (`hconv`), and no new invariant-map chapter is needed.

### Session 25 (2026-10-02): correction of the paragraph above, and the two routes

**The paragraph above is wrong in its second half** and must not be acted on.  A component
zero-test (`extIdele_localisation_injective_of_finite`, `HBNIdele`) gives only the **uniqueness**
half "vanishing *local classes* ⟹ the global class vanishes" — which is the *reciprocity* half
`B ⊆ A^⊥`, already proved (`PT.SubAnnihilatorHalf`).  (B) needs the **existence** half
"pairing-orthogonality ⟹ the class is a global idèle class"; the separation route through
`pt_piPairingDual` fails because `subB` is **not closed** in the restricted product, and the
converse of `natCard_annihilator_mul` cannot be applied either (it needs *finite* `P`, while the
`PtIndex` restricted product is infinite).  (B) remains open.

What *is* measured (2026-10-02) is that the node has **no strictly easier residual**: given the
proved reciprocity and `PT.natCard_annihilator_mul`, `CountingIdentity`, `hBcl`,
`SubMiddleExactness`, `(VF)`, `E9`, `sha_card_euler_var`, `pt_pairing_left_inj` (Route A) and
`hreal`/`W^⊥ ⊆ V` are all equivalent to one another.  The node's sharpest formal residual is
`hconv` (`W^⊥ ⊆ V`, the hypothesis of `countingIdentity_of_reciprocity_and_converse` below), and its
only named missing input on the classical route is `(VF)⟸` = "`phiAt (extToClasses x) h = 0`
whenever all local pairings of `x` and `loc h` vanish".  See `PT/ACTION_value_formula.md` §9 and
`PT/PING_count_faces_and_routes.md` for the full measurement, the second (PTCore/HSRow) route via
`#Ш¹ = #Ш²`, and the one missing *downward* bridge that would repoint this node to the actively
worked nodes `PTCore.pt_pairing_left_inj` (Route B), `PT.e1aBetaCan_le_ker` and `C6`.

### Session 27 (2026-10-02, late): the residual is **`G1⁺`** — and the re-pointing wiring is PROVED

Per the lead design (`_lead_design/ssg_pt_design_1002/DESIGN.md` §4), the node's residual is now the
**single** dispatched node

> **`G1⁺`** = `Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`,

whose conclusion is `∃ pair, (G1's clauses (1)–(7) verbatim) ∧ (clause (8))`, where clause (8) is
the **representative-form converse**: local data `(α, β)` at `S ∪ C` whose `pair`-sum vanishes
against every relaxed dual Selmer class `b` is realized by a global cocycle `ε` unramified outside
`S ∪ cs(N)` (i.e. `PT.IsRealizableClass`).  Clause (8) is *verbatim* the `horth` of
`PT.pt_selmer_relaxed_assembly` — the relaxed middle exactness, produced there by the canonical
construction (the value formula of §9's `(VF)` holds *by definition* of that `pair`).

The re-pointing wiring is **proved** in `PT/pt_counting_from_G1plus.lean` (axiom-clean,
`[propext, Classical.choice, Quot.sound]`):

* **`PT.hconv_of_converse`** — clause (8) plus the pairing clauses give the *class-level* converse
  `hconv` (`W^⊥ ⊆ V`) of `countingIdentity_of_reciprocity_and_converse`, via the proved
  `PT.productFormFun_primalClassOf` and `PT.localPairingFun_toClass`;
* **`PT.countingIdentity_of_canonical_and_converse`** — `pair` + clauses (1)–(4) + (7) + (8) give
  `CountingIdentity p k Ω K N hKN T M S C`, via the proved
  `PT.countingIdentity_of_reciprocity_and_converse` (+ `finite_primalClasses_pt`/`_dual_pt`).

**DONE (same session).**  The node's `sorry` has been replaced by exactly that application: its body
now extracts `pair`, `hloc`, `hrec` (clause (7)) and `hconv8` (clause (8)) from
`canonical_localPairing_reciprocity_converse`, turns clause (8) into the class-level `hconv` with
`PT.hconv_of_converse` (node-free, `PT/converseRepr.lean`), and closes with the proved
`PT.countingIdentity_of_reciprocity_and_converse`.  Measured: the file has **no in-code `sorry`**,
and `#print axioms Work.SSGRoute.PT.pt_counting_identity_h1` reports
`[propext, sorryAx, Classical.choice, Quot.sound]` — the single `sorryAx` source is now **`G1⁺`**
itself (every other ingredient is measured clean: `hconv_of_converse`,
`countingIdentity_of_reciprocity_and_converse`, `finite_primalClasses_pt`, `finite_primalClasses_dual_pt`).
So `COUNT` is **off the frontier**: it closes automatically the moment `G1⁺` is proved, and the
branch-B frontier is now `G1⁺`'s own three sub-nodes (S1, S2, S6) plus `G1⁺`.

### Session 28 (2026-10-03): the route to `G1⁺`, and three measured facts that decide it

The full account is `PT/PING_g1plus_classformation_route.md`; the three facts:

1. **`G1⁺` cannot be got from `G1` by `PT.pt_selmer_relaxed_assembly`.**  That theorem's `horth`
   *is* clause (8) verbatim and it concludes clause (8)'s `∃ε`, so extracting `hloc`/`hrec` from
   `G1`'s clauses (1)–(7) and applying it looks like a one-step proof of `G1⁺` — but
   `pt_selmer_relaxed_assembly` *uses* `pt_counting_identity_h1` internally (the counting identity
   is its `wbot_le_of_additive` input), so that route makes `COUNT` depend on `COUNT`.  (Importing
   `Submission.Work.SSGRoute.pt_selmer_relaxed` from the `G1⁺` statement file is impossible anyway:
   it imports this file.)  Clause (8) must therefore be proved for the class-formation `pair` by the
   direct route of `DESIGN.md` §4 (value formula + `phi1_mono_sylow_in` + `pt_extSegment_exact`).
2. **The engines are on disk.**  `Work.SSGRoute.phi1_mono_sylow_in` (E6Ω) is **proved and
   axiom-clean** (`[propext, Classical.choice, Quot.sound]`) — the older notes calling it
   `sorryAx`-tainted predate the closure of `PT.phi0_trivial_epi_in`.  `Work.SSGRoute.pt_sha2_core`
   (the E9 core) has **0 `sorry`** in its file (still `sorryAx`-tainted through imports).  The value
   formula `PT.e9_glue_phiAt`, the exact segment `PT.pt_extSegment_exact`, the localisation/Yoneda
   square `PT.extLoc_yonedaPair` and the Shapiro gluing `PT.exists_glue_extLoc` are all proved, and
   `phiAt` and the design's `pair` are built from the *same* `levelPair`.
3. **`ι_w` is canonical and available.**  `PT/g1plus_iota.lean` now builds: `PT.iotaLift`,
   `PT.iota` (the orbit-placement map), `PT.iotaLift_spec`, `PT.eq_iotaLift_of_spec` (**the
   orbit-supported lift is unique**, from the proved
   `E7cOmega.eq_of_extLoc_eq_of_orbitSupported`) and `PT.iota_injective_of_ptorsion` (from S2), all
   axiom-clean.  So the orbit-placement construction is done *and* canonical, and the only new
   bookkeeping left for it is the level compatibility (`ι_{w'} (infl z) = infl (ι_w z)` on
   orbit-supported classes, which reduces to the localisation/inflation functoriality of
   `extRes`/`extHMap`).

`PT.exists_level_factors_locConstOnTwo` (the joint finite-Galois level through which `a|_H` and
`b|_H` factor; reviewed twice, delegated) is the remaining enabling lemma of the definition of `fin`.

-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

/-- **Finiteness of the local class space `P` at `S ∪ C`.**

This is step 5 of the route in the module docstring: the counting identity is an identity between
`Nat.card`s, and the counting step `natCard_annihilator_mul` needs `P` and `P'` to be finite.  The
two per-place facts are `PT.finite_H1loc` (a finite place, from the arithmetic input
`finite_localField_homs`) and `PT.finite_H1loc_zpowers` (an involution), packaged by
`PT.finite_primalClasses`.

Also useful to the consumer `PT.pt_canonical_relaxed`, whose two remaining `Finite (primalClasses …)`
arguments are discharged by this lemma at `M` and at `M^∨(1)` (with `Finite T` from `hT` via
`Work.SSGRoute.finite_of_finrank_eq_one`). -/
theorem finite_primalClasses_pt [Finite M]
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    Finite (primalClasses p k Ω K M S C) :=
  finite_primalClasses p k Ω K M S C
    (fun A hA => finite_H1loc p k Ω K M A (hSfin A hA))
    (fun c hc => finite_H1loc_zpowers p k Ω K M c (hCinv c hc))

end

end Work.SSGRoute.PT

/-! ## Session 2 additions: the exact content of the target, and the finiteness bookkeeping

The lemmas below put the target of this file into the exact shape that the arithmetic input
(`V = W^⊥`, the middle exactness of the relaxed Poitou–Tate sequence) produces, and they discharge
the finiteness bookkeeping at both coefficient modules.  Together with

* `PT.natCard_primalClassSet`, `PT.natCard_dualClassSet` (proved: the two class *sets* are
  `Nat.card`-equivalent to the two subtypes appearing in `CountingIdentity`),
* `PT.pt_orthogonality_of_realizable` (proved: `V ⊆ W^⊥`, reciprocity), and
* `PT.wbot_le_of_additive` / `PT.counting_step_concrete` (proved: the *reverse* counting step,
  `|V| · |W| = |P|` and `V ⊆ W^⊥` give `W^⊥ ⊆ V`),

the target is *equivalent* to the annihilator identity `V = W^⊥` for a pairing `β` on the two local
class spaces that is non-degenerate in both variables.  Nothing below proves that identity: it is
the arithmetic content of the node (Milne, *Arithmetic Duality Theorems* I.4.10, the middle
exactness `im(H¹(k,M) → P) = ann(loc H¹(k,M^∨(1)))`), which is *not* available in this workspace —
its proof is the Poitou–Tate workshop E0–E9 of `SSGRoute/DESIGN_PT.md`, whose E-nodes
(`E0b` `ExtMkCompExtClass.yoneda_extClass`, `E7` `PTembedding.localTatePairing_canonical`,
`E8` local–global compatibility, `E9` the exact segment) are all still open.  What is *new* here is
that the reduction is now formal: `countingIdentity_of_dualAnnihilator` names exactly what is
missing, so that the node is a single arithmetic statement rather than a chain. -/

namespace Work.SSGRoute.PT

noncomputable section

open scoped TensorProduct

/-! ## A pairing non-degenerate on both sides forces equal dimensions

The counting identity needs `Nat.card P = Nat.card P'` for the two local class spaces.  The
arithmetic of `E7` supplies this as an equality of `𝔽_p`-dimensions, and the passage from a
*both-sides non-degenerate* bilinear pairing to the dimension equality is the elementary lemma
below (the linear-algebra content of "a perfect pairing identifies a space with its dual"). -/

/-- **A bilinear pairing that is non-degenerate on both sides forces equality of dimensions.**
Over a field, a pairing `B : P →ₗ[K] Q →ₗ[K] K` whose left radical is trivial embeds `P` into the
dual of `Q` (hence `dim P ≤ dim Q`), and symmetrically for the right radical; a two-sided
non-degenerate pairing therefore has `dim P = dim Q`.  This is the step that converts the local
Tate duality *pairing* of node `E7` into the dimension — equivalently cardinality — equality of the
two local `H¹`-spaces. -/
theorem pt_finrank_eq_of_nondegenerate_pairing {K P Q : Type*} [Field K] [AddCommGroup P]
    [Module K P] [AddCommGroup Q] [Module K Q] [Module.Finite K P] [Module.Finite K Q]
    (B : P →ₗ[K] Q →ₗ[K] K)
    (hndL : ∀ x : P, (∀ y : Q, B x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, B x y = 0) → y = 0) :
    Module.finrank K P = Module.finrank K Q := by
  have hinjL : Function.Injective (fun x : P => (B x : Q →ₗ[K] K)) := by
    intro x y hxy
    have hzero : ∀ q : Q, B (x - y) q = 0 := by
      intro q
      have h2 : B (x - y) q = B x q - B y q := by
        rw [map_sub]; rfl
      rw [h2, congrArg (fun f : Q →ₗ[K] K => f q) hxy, sub_self]
    exact sub_eq_zero.mp (hndL (x - y) hzero)
  let B' : Q →ₗ[K] P →ₗ[K] K :=
    { toFun := fun y => { toFun := fun x => B x y, map_add' := by intro a b; simp, map_smul' := by intro c a; simp }
      map_add' := by intro a b; ext x; simp
      map_smul' := by intro c a; ext x; simp }
  have hinjR : Function.Injective (fun y : Q => (B' y : P →ₗ[K] K)) := by
    intro x y hxy
    have hzero : ∀ p : P, B' (x - y) p = 0 := by
      intro p
      have h2 : B' (x - y) p = B' x p - B' y p := by
        rw [map_sub]; rfl
      rw [h2, congrArg (fun f : P →ₗ[K] K => f p) hxy, sub_self]
    exact sub_eq_zero.mp (hndR (x - y) hzero)
  have h1 : Module.finrank K P ≤ Module.finrank K Q :=
    le_trans (LinearMap.finrank_le_finrank_of_injective hinjL) (le_of_eq Subspace.dual_finrank_eq)
  have h2 : Module.finrank K Q ≤ Module.finrank K P :=
    le_trans (LinearMap.finrank_le_finrank_of_injective hinjR) (le_of_eq Subspace.dual_finrank_eq)
  exact le_antisymm h1 h2

/-! ## The cyclotomic dual `T` is finite -/

section CyclotomicDualFinite

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **The cyclotomic dual `T` of `μ_p` is a finite type**: `IsCyclotomicDual` makes it a line over
`𝔽_p`.  This is the `Finite T` that the local-field arithmetic at the Tate dual
`M^∨(1) = DualMod p (M ⊗ T)` needs. -/
theorem finite_of_isCyclotomicDual (ζ : Ω)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Finite T := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [hT.1, Module.finrank_self]
  exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
    (LinearEquiv.injective _)

end CyclotomicDualFinite

/-! ## Finiteness of the Tate-dual class space -/

section DualClassFinite

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **Finiteness of the Tate-dual local class space** `P' = primalClasses … (DualMod p (M ⊗ T)) …`.

Together with `finite_primalClasses_pt` (the primal side) this discharges the two finiteness inputs
of `PT.pt_canonical_relaxed` (`hfinP`, `hfinQ`).  The ingredients are `finite_of_isCyclotomicDual`
(the `Finite T` from `hT`) and `PT.finite_dualMod_tensor`, fed into the general packaging
`PT.finite_primalClasses_general`. -/
theorem finite_primalClasses_dual_pt
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) := by
  haveI : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  haveI : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  exact finite_primalClasses_general p k Ω K
    (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S hSfin C hCinv

end DualClassFinite

/-! ## Finiteness of the local `H¹` as a module -/

section LocalH1ModuleFinite

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **Finiteness of the local `H¹` as a module at a finite place.**  The node
`Work.SSGRoute.local_tate_duality_euler` carries `Module.Finite (ZMod p) (H1loc …)` as its first
conjunct; it is *automatic* from the proved finiteness of the local `H¹`
(`Work.SSGRoute.PT.finite_H1loc`), so the arithmetic obligation of that node is the dimension
identity alone. -/
theorem moduleFinite_H1loc_finPlace
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A)) := by
  haveI : Finite (H1loc p k Ω K M (SSGRoute.decomp k A)) := finite_H1loc p k Ω K M A hA
  exact Module.Finite.of_finite

/-- **Finiteness of the local `H¹` as a module at an involution.**  The archimedean analogue of
`moduleFinite_H1loc_finPlace`, from the proved `Work.SSGRoute.PT.finite_H1loc_zpowers`. -/
theorem moduleFinite_H1loc_zpowers
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c)) := by
  haveI : Finite (H1loc p k Ω K M (Subgroup.zpowers c)) :=
    finite_H1loc_zpowers p k Ω K M c hc
  exact Module.Finite.of_finite

end LocalH1ModuleFinite


/-! ## The annihilator cardinality in the additive interface, and the two forms of the target -/

section AnnihilatorCard

/-- **The cardinality form of the annihilator identity, for a pairing given only additively.**
For a bi-additive `β : P → Q → 𝔽_p` which is non-degenerate in both variables and a subspace
`W ≤ Q`, the annihilator of `W` satisfies `|W^⊥| · |W| = |P|`.

This is `PT.natCard_annihilator_mul` (which is stated for a `→ₗ`-bilinear form) with the scalar
action recovered from the additive one: over the field `𝔽_p` an additive map is automatically
`𝔽_p`-linear, so nothing is lost.  The additive interface is the one in which the product pairing of
local Tate pairings is available (`PT.exists_pairing_on_H1loc` supplies it additively). -/
theorem natCard_annihilator_mul_additive {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y : W, β x y = 0} * Nat.card W = Nat.card P := by
  classical
  let inner : ∀ (_ : P), Q →+ ZMod p := fun x => AddMonoidHom.mk' (β x) (fun y y' => haddR x y y')
  have hinner : ∀ x x' : P, inner (x + x') = inner x + inner x' := by
    intro x x'
    ext y
    exact haddL x x' y
  let F : P →+ (Q →ₗ[ZMod p] ZMod p) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.toZModLinearMap p (inner x))
      (fun x x' => by rw [hinner x x']; ext y; rfl)
  let βlin : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p := AddMonoidHom.toZModLinearMap p F
  have hβ : ∀ x y, βlin x y = β x y := fun x y => rfl
  have hcard := natCard_annihilator_mul (p := p) βlin
    (fun x hx => hndL x (fun y => by rw [← hβ]; exact hx y))
    (fun y hy => hndR y (fun x => by rw [← hβ]; exact hy x)) W
  have hEq : Nat.card {x : P // ∀ y : W, β x y = 0}
      = Nat.card {x : P // ∀ y ∈ W, βlin x y = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : P => ∀ y : W, β x y = 0)
      (q := fun x : P => ∀ y ∈ W, βlin x y = 0) ?_)
    intro x
    constructor
    · intro h y hy
      rw [hβ]
      exact h ⟨y, hy⟩
    · intro h y
      rw [← hβ]
      exact h y.1 y.2
  rw [hEq]
  exact hcard

/-- **The counting identity from the annihilator identity.**  For a bi-additive, both-sides
non-degenerate `β : P → Q → 𝔽_p` and subspaces `V ≤ P`, `W ≤ Q` with `V = W^⊥`, one has
`|V| · |W| = |P|`.

This is the *converse* of `PT.counting_step_concrete` (`|V| · |W| = |P|` and `V ⊆ W^⊥` give
`W^⊥ ⊆ V`); together the two say that the counting identity *is* the annihilator identity. -/
theorem natCard_mul_of_annihilator {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (V : Submodule (ZMod p) P) (W : Submodule (ZMod p) Q)
    (hbot : ∀ x : P, x ∈ V ↔ ∀ y : Q, y ∈ W → β x y = 0) :
    Nat.card V * Nat.card W = Nat.card P := by
  classical
  have h1 : Nat.card V = Nat.card {x : P // ∀ y : W, β x y = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : P => x ∈ V)
      (q := fun x : P => ∀ y : W, β x y = 0)
      (fun x => ⟨fun hx y => (hbot x).mp hx y.1 y.2,
        fun h => (hbot x).mpr (fun y hy => h ⟨y, hy⟩)⟩))
  rw [h1]
  exact natCard_annihilator_mul_additive β haddL haddR hndL hndR W


/-- **One-sided non-degeneracy plus equal cardinality gives the other side.**

For a bi-additive pairing `β : P → Q → 𝔽_p` between finite `𝔽_p`-modules whose left radical is
trivial and whose two sides have the same cardinality (equivalently, the same dimension), the right
radical is trivial as well.  Indeed `x ↦ β x ·` is an injective map `P → Q^∨`; the cardinality
hypothesis makes it a bijection, and a bijection `P ≅ Q^∨` dualises to an injective map
`Q → P^∨` (the transpose of an isomorphism), which is exactly the vanishing of the right radical.

This is the classical step "left-non-degeneracy + `|P| = |Q|` ⟹ right-non-degeneracy", and it is
the form in which a one-sided duality statement (a cup product with a trivial left radical, or a
transgression) upgrades to a perfect pairing once the dimension equality of the two sides is known
— the situation of the local Tate pairings of `E7`, where the dimension equality comes from the
local Euler characteristic and Tate duality in degrees `0`/`2`. -/
theorem transpose_nondegenerate_of_card_eq {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hcard : Nat.card P = Nat.card Q) :
    ∀ y : Q, (∀ x : P, β x y = 0) → y = 0 := by
  classical
  haveI hPf : Module.Finite (ZMod p) P := Module.Finite.of_finite
  haveI hQf : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  -- linearise the additive pairing
  let inner : ∀ (_ : P), Q →+ ZMod p := fun x => AddMonoidHom.mk' (β x) (fun y y' => haddR x y y')
  have hinner : ∀ x x' : P, inner (x + x') = inner x + inner x' := by
    intro x x'
    ext y
    exact haddL x x' y
  let F : P →+ (Q →ₗ[ZMod p] ZMod p) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.toZModLinearMap p (inner x))
      (fun x x' => by rw [hinner x x']; ext y; rfl)
  let βlin : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p := AddMonoidHom.toZModLinearMap p F
  have hβ : ∀ x y, βlin x y = β x y := fun x y => rfl
  have hinj : Function.Injective βlin := by
    intro x x' hxx'
    have h3 : βlin x = βlin x' := hxx'
    have h : x - x' = 0 := hndL (x - x') (fun y => by
      rw [← hβ (x - x') y, map_sub, LinearMap.sub_apply, DFunLike.congr_fun h3 y, sub_self])
    rwa [sub_eq_zero] at h
  -- equal cardinalities give equal dimensions
  have hP : Nat.card P = p ^ Module.finrank (ZMod p) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hQ : Nat.card Q = p ^ Module.finrank (ZMod p) Q := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hpow : p ^ Module.finrank (ZMod p) P = p ^ Module.finrank (ZMod p) Q := by
    rw [← hP, ← hQ, hcard]
  have hfin : Module.finrank (ZMod p) P = Module.finrank (ZMod p) Q :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  have hsurj : Function.Surjective βlin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq]; exact hfin)).mp hinj
  -- the right radical is trivial: `y` is annihilated by every functional on `Q`
  intro y hy
  have hall : ∀ φ : Module.Dual (ZMod p) Q, φ y = 0 := by
    intro φ
    obtain ⟨x, rfl⟩ := hsurj φ
    exact hy x
  have h0 : (Module.evalEquiv (ZMod p) Q) y = 0 := by
    rw [Module.evalEquiv_apply]
    ext φ
    rw [Module.Dual.eval_apply]
    simpa using hall φ
  exact (Module.evalEquiv (ZMod p) Q).injective (by rw [h0, map_zero])

/-- **The annihilator identity with a one-sided hypothesis.**  For a bi-additive pairing
`β : P → Q → 𝔽_p` which is non-degenerate on the *left* and whose two sides have equal cardinality,
and any subspace `W ≤ Q`, one has `|W^⊥| · |W| = |P|`.

This is `natCard_annihilator_mul_additive` with the right-non-degeneracy no longer assumed but
derived from `transpose_nondegenerate_of_card_eq`; it is the form in which the counting step
applies when only one side of the duality is available (a one-sided cup product or transgression)
together with the dimension equality of the two local `H¹`-spaces. -/
theorem natCard_annihilator_mul_of_left {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hcard : Nat.card P = Nat.card Q)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y : W, β x y = 0} * Nat.card W = Nat.card P :=
  natCard_annihilator_mul_additive β haddL haddR hndL
    (transpose_nondegenerate_of_card_eq β haddL haddR hndL hcard) W

/-- **The counting identity `|V| · |W| = |P|` from a one-sided annihilator identity.**  Variant of
`natCard_mul_of_annihilator` in which `β` is assumed non-degenerate only on the *left* and the
non-degeneracy on the right is derived from `Nat.card P = Nat.card Q`.

This is the exact shape in which the arithmetic input of this file arrives: local Tate duality is
available on one side (a cup product with trivial left radical, or a transgression) together with
the *dimension* equality `dim P = dim Q` coming from the local Euler characteristic and Tate duality
in degrees `0`/`2`, and the annihilator identity `V = W^⊥` is the statement of the middle exactness
of the relaxed Poitou–Tate sequence. -/
theorem natCard_mul_of_annihilator_of_left {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hcard : Nat.card P = Nat.card Q)
    (V : Submodule (ZMod p) P) (W : Submodule (ZMod p) Q)
    (hbot : ∀ x : P, x ∈ V ↔ ∀ y : Q, y ∈ W → β x y = 0) :
    Nat.card V * Nat.card W = Nat.card P :=
  natCard_mul_of_annihilator β haddL haddR hndL
    (transpose_nondegenerate_of_card_eq β haddL haddR hndL hcard) V W hbot


end AnnihilatorCard

/-! ## The cardinality of the product of the local `H¹`-spaces, and the dimension input of the node

The counting identity is an identity of `Nat.card`s, and the only place where the *arithmetic* of
local Tate duality enters its proof (once a pairing on the two class spaces is available) is the
cardinality equality

  `Nat.card (primalClasses … M …) = Nat.card (primalClasses … M^∨(1) …)`,

whose content is the dimension equality `dim H¹(D_v, M) = dim H¹(D_v, M^∨(1))` at every place of
`S ∪ C` — this is what the local Tate duality nodes deliver for the pairing `β` of the counting step
(`Work.SSGRoute.local_tate_duality_02` in degrees `0`/`2`, assembled with the local Euler
characteristic `Work.SSGRoute.local_tate_duality_euler`).  The two lemmas below perform the
bookkeeping: they express `Nat.card` of a product of local `H¹`'s as `p` to the sum of the
`𝔽_p`-dimensions, and they deduce the cardinality equality from the per-place dimension equalities.

With them, the reduction `countingIdentity_of_oneSidedDualAnnihilator` needs only

* the per-place dimension equalities (`hdS`, `hdC` below — the arithmetic of `E7`), and
* the annihilator identity `V = W^⊥` (`E9`, the middle exactness),

in addition to the per-place non-degeneracy of the local pairings. -/

section LocalDimensionCard

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The cardinality of the product of the local `H¹`-spaces.**  For any coefficient module `M`
whose local `H¹`'s at the places of `S` and the involutions of `C` are finite-dimensional over
`𝔽_p`,

  `Nat.card (primalClasses … M …) = p ^ (Σ_{A ∈ S} dim H¹(D_A,M) + Σ_{c ∈ C} dim H¹(⟨c⟩,M))`.

This is the `Nat.card` computation underlying the counting identity: the product type is a product
of two `Π`-types, `Nat.card` of a product is the product of the `Nat.card`s and `Nat.card` of a
finite product of finite `𝔽_p`-vector spaces is `p ^ (sum of dimensions)`. -/
theorem natCard_primalClasses_pow (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (hS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
    (hC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1))) :
    Nat.card (primalClasses p k Ω K M S C) =
      p ^ ((∑ A : {A : ValuationSubring Ω // A ∈ S},
              Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
            + (∑ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
              Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)))) := by
  rw [primalClasses, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  have h1 : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Nat.card (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = p ^ Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)) := by
    intro A
    haveI := hS A
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have h2 : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Nat.card (H1loc p k Ω K M (Subgroup.zpowers c.1))
        = p ^ Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)) := by
    intro c
    haveI := hC c
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [Finset.prod_congr rfl (fun A _ => h1 A), Finset.prod_congr rfl (fun c _ => h2 c)]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add]

/-- **The cardinality of the two local class spaces agrees as soon as the local dimensions do.**
For two coefficient modules `M`, `M'` whose local `H¹`'s at the places of `S ∪ C` are
finite-dimensional, per-place equalities of `𝔽_p`-dimensions imply the equality of the
cardinalities of the two products.  Instantiated at `M' = M^∨(1) = DualMod p (M ⊗ T)`, this is the
`Nat.card P = Nat.card P'` input of `countingIdentity_of_oneSidedDualAnnihilator`, and it shows
that the arithmetic obligation is the *dimension* equality at each place (node `E7`), not a
cardinality statement. -/
theorem natCard_primalClasses_eq_of_finrank_eq
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M' : Type) [AddCommGroup M'] [Module (ZMod p) M']
    [DistribMulAction (K ≃ₐ[k] K) M'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (hS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
    (hS' : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M' (SSGRoute.decomp k A.1)))
    (hC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)))
    (hC' : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M' (Subgroup.zpowers c.1)))
    (hdS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K M' (SSGRoute.decomp k A.1)))
    (hdC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K M' (Subgroup.zpowers c.1))) :
    Nat.card (primalClasses p k Ω K M S C) = Nat.card (primalClasses p k Ω K M' S C) := by
  rw [natCard_primalClasses_pow p k Ω K M S C hS hC,
    natCard_primalClasses_pow p k Ω K M' S C hS' hC']
  congr 1
  rw [Finset.sum_congr rfl (fun A _ => hdS A), Finset.sum_congr rfl (fun c _ => hdC c)]

end LocalDimensionCard

section CountingFromAnnihilator

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

/-- The four structure instances of the Tate dual `M^∨(1) = DualMod p (M ⊗ T)`, pinned as local
instances.  The instance search for the additive structure of the *product*
`primalClasses … (DualMod p (M ⊗ T)) …` does not terminate without this pinning (measured: `HAdd`
and `OfNat … 0` on that product fail); the same pinning is used in `PT/pt_counting_assembly.lean`. -/
local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The two forms of the counting identity are equivalent.**  The *predicate* form
(`CountingIdentity`, the target of this file, with the subtypes of `IsRealizableClass` and
`IsDualSelmerClass`) and the *submodule* form `|V| · |W| = |P|` (`V = primalClassSet`,
`W = dualClassSet`), in which the arithmetic input is naturally stated.  The two directions are
`PT.natCard_counting` and `PT.natCard_primalClassSet` / `PT.natCard_dualClassSet`. -/
theorem countingIdentity_iff_submoduleForm (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    CountingIdentity p k Ω K N hKN T M S C ↔
      Nat.card (primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C)) *
        Nat.card (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
          (S := S) (C := C)) =
      Nat.card (primalClasses p k Ω K M S C) := by
  constructor
  · intro h
    exact natCard_counting (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN) (T := T)
      (M := M) (S := S) (C := C) hCinv h
  · intro h
    rw [natCard_primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN) (M := M)
        (S := S) (C := C) hCinv,
      natCard_dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN) (T := T)
        (M := M) (S := S) (C := C)] at h
    exact h

/-- **The target from the annihilator identity `V = W^⊥`.**  If the two local class spaces carry a
pairing `β` that is additive in each variable and non-degenerate in both, and the realizable classes
`V` are exactly the classes orthogonal to the relaxed dual Selmer classes `W`, then
`|V| · |W| = |P|`, which is the target.

This names the *whole* remaining arithmetic content of the node: `β` is the sum of the canonical
local Tate pairings (node E7) and `V = W^⊥` is the middle exactness of the relaxed Poitou–Tate
sequence (nodes E8/E9).  The other half, `V ⊆ W^⊥`, is proved (`PT.pt_orthogonality_of_realizable`),
as is the reverse counting step (`PT.counting_step_concrete`). -/
theorem countingIdentity_of_dualAnnihilator
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (β : primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : primalClasses p k Ω K M S C, (∀ y, β x y = 0) → x = 0)
    (hndR : ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      S C, (∀ x, β x y = 0) → y = 0)
    (hbot : ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) ↔
        ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
          y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C) →
            β x y = 0)
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C := by
  rw [countingIdentity_iff_submoduleForm (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
    (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hCinv]
  -- Every instance argument is supplied explicitly, so that no instance search over the two
  -- concrete class spaces is left to the elaborator (the search on the Tate-dual product does not
  -- terminate without it).
  exact @natCard_mul_of_annihilator p (inferInstance : Fact p.Prime)
    (primalClasses p k Ω K M S C)
    (primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)
    (inferInstance : AddCommGroup (primalClasses p k Ω K M S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K M S C))
    hfinP
    (inferInstance : AddCommGroup (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    hfinQ
    β haddL haddR hndL hndR
    (primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S) (C := C))
    (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M) (S := S)
      (C := C)) hbot

/-- **The target from a one-sided pairing and the annihilator identity.**  The same statement as
`countingIdentity_of_dualAnnihilator`, but with the non-degeneracy of `β` assumed only on the left
and the *cardinality equality* `|P| = |P'|` assumed instead of the right-non-degeneracy; the latter
is then derived (`transpose_nondegenerate_of_card_eq`).

This is the sharpest form of the reduction proved in this file: the two hypotheses that are *not*
formal are exactly the two arithmetic facts of the node —
(i) the existence of the product pairing of local Tate pairings with trivial left radical together
with `|P| = |P'|` (node `E7`: `local_tate_duality_euler` + `local_tate_duality_02`, consumed through
`PT.pt_e7Inputs` / `PT.exists_pairing_on_H1loc` / `PT.productFormFun`), and
(ii) the annihilator identity `V = W^⊥` (the middle exactness of the relaxed Poitou–Tate sequence,
`E8` + `E9`; the reverse inclusion `V ⊆ W^⊥` is the *proved* `PT.pt_orthogonality_of_realizable`).
Everything else — the counting step, the finiteness, the identification of the predicate and
submodule forms — is proved here. -/
theorem countingIdentity_of_oneSidedDualAnnihilator
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (β : primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : primalClasses p k Ω K M S C, (∀ y, β x y = 0) → x = 0)
    (hcard : Nat.card (primalClasses p k Ω K M S C) =
      Nat.card (primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        S C))
    (hbot : ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) ↔
        ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
          y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C) →
            β x y = 0)
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C := by
  -- All instance arguments are supplied explicitly: the instance search on the product
  -- `primalClasses …` does not terminate reliably without it (the hazard recorded in the module
  -- docstring), and `transpose_nondegenerate_of_card_eq` is applied with `@` for the same reason.
  refine countingIdentity_of_dualAnnihilator (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
    (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hCinv β haddL haddR hndL ?_ hbot hfinP hfinQ
  exact @transpose_nondegenerate_of_card_eq p (inferInstance : Fact p.Prime)
    (primalClasses p k Ω K M S C)
    (primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)
    (inferInstance : AddCommGroup (primalClasses p k Ω K M S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K M S C))
    hfinP
    (inferInstance : AddCommGroup (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    hfinQ β haddL haddR hndL hcard

/-- **The `Nat.card` equality of the two local class spaces, from the per-place dimension
equalities.**  This is the `hcard` input of `countingIdentity_of_oneSidedDualAnnihilator`, with the
arithmetic obligation displayed as the *local dimension* equality `dim H¹(D_v, M) =
dim H¹(D_v, M^∨(1))` at every place of `S ∪ C` — which is exactly the output of the local Tate
duality nodes (`Work.SSGRoute.local_tate_duality_02` at the places of `S`, and the archimedean
duality at the involutions of `C`) — rather than as a cardinality statement.  This is the form in
which the `E7` lane delivers the arithmetic of the node. -/
theorem hcard_of_localDims
    (hS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
    (hS' : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)))
    (hC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)))
    (hC' : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1)))
    (hdS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)))
    (hdC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1))) :
    Nat.card (primalClasses p k Ω K M S C) =
      Nat.card (primalClasses p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :=
  natCard_primalClasses_eq_of_finrank_eq (p := p) (k := k) (Ω := Ω) (K := K)
    (M := M) (M' := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (S := S) (C := C)
    hS hS' hC hC' hdS hdC

/-- **The node from the *arithmetic* inputs, in the form the `E7` lane delivers them**: a
bi-additive pairing `β` on the two local class spaces which is non-degenerate in the first variable,
the per-place dimension equalities `dim H¹(D_v, M) = dim H¹(D_v, M^∨(1))` (from which
`Nat.card P = Nat.card P'` follows by `hcard_of_localDims`), and the annihilator identity
`V = W^⊥` in the predicate form.  The cardinality equality is *derived* here rather than assumed;
hence the node's hypotheses are exactly

* the local pairings together with the per-place dimension equalities (node `E7`, whose arithmetic
  is `Work.SSGRoute.local_tate_duality_euler` plus `Work.SSGRoute.local_tate_duality_02`), and
* the middle exactness `W^⊥ ⊆ V` of the relaxed Poitou–Tate sequence (node `E9`; the inclusion
  `V ⊆ W^⊥` is the proved `PT.pt_orthogonality_of_realizable`),

and nothing else. -/
theorem countingIdentity_of_localDims_and_annihilator
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (β : primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : primalClasses p k Ω K M S C, (∀ y, β x y = 0) → x = 0)
    (hS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
    (hS' : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)))
    (hC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)))
    (hC' : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1)))
    (hdS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)))
    (hdC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1)))
    (hbot : ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) ↔
        ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
          y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C) →
            β x y = 0)
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C :=
  countingIdentity_of_oneSidedDualAnnihilator (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
    (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hCinv β haddL haddR hndL
    (hcard_of_localDims (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
      hS hS' hC hC' hdS hdC) hbot hfinP hfinQ


end CountingFromAnnihilator

/-! ## The archimedean dimension equality: the `C`-side of `hcard` is *free*

The half of the `hcard` input of `countingIdentity_of_oneSidedDualAnnihilator` that concerns the
involutions in `C` is not an arithmetic input: the archimedean local Tate duality is *proved*
(`Work.SSGRoute.local_tate_duality_archimedean`, assembled into the clause list by
`PT.exists_localAxioms_zpowers`), and a both-sides non-degenerate pairing gives the dimension
equality by `pt_finrank_eq_of_nondegenerate_pairing`.  Consequently `hcard_of_localDims` only needs the
*finite-place* dimension equalities: the `E7` obligations of the node are exactly the finite-place
ones (`Work.SSGRoute.local_tate_duality_euler` together with
`Work.SSGRoute.local_tate_duality_02`). -/

section ArchimedeanDimension

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The archimedean dimension equality of local Tate duality.**  At an involution `c`, the local
`H¹`-spaces of a finite module `M` and of its Tate dual `M^∨(1) = DualMod p (M ⊗ T)` have the same
`𝔽_p`-dimension.  This is the `C`-side input of `hcard`, and it needs no arithmetic: it follows from
the *proved* archimedean local Tate duality together with the elementary
`pt_finrank_eq_of_nondegenerate_pairing`. -/
theorem finrank_H1loc_zpowers_tate_dual (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c)) =
      Module.finrank (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c)) := by
  haveI hTfin : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  haveI hQfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  obtain ⟨pairc, hax⟩ := exists_localAxioms_zpowers (p := p) (k := k) (Ω := Ω) (K := K)
    (T := T) (M := M) ζ hζ hζK hT c hc
  obtain ⟨B, -, hndL, hndR⟩ := exists_pairing_on_H1loc (p := p) (k := k) (Ω := Ω) (K := K)
    M (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c)
    (pairc (Subgroup.zpowers c)) hax.1 hax.2.1
    (fun a b ha hb hcob => hax.2.2.1 a b ha hb (Or.inl hcob))
    (fun a b ha hb hcob => hax.2.2.1 a b ha hb (Or.inr hcob)) hax.2.2.2.1 hax.2.2.2.2
  haveI : Finite (H1loc p k Ω K M (Subgroup.zpowers c)) :=
    finite_H1loc_zpowers p k Ω K M c hc
  haveI : Finite (H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c)) :=
    finite_H1loc_zpowers p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) c hc
  haveI : Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c)) :=
    Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c)) :=
    Module.Finite.of_finite
  exact pt_finrank_eq_of_nondegenerate_pairing (K := ZMod p) B hndL hndR

end ArchimedeanDimension

/-! ## The finite-place dimension equality from the two `E7` nodes

The finite-place dimension equality `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))` — the input of
`hcard_of_localDims_finPlace`, and hence of the node — is *not* an independent arithmetic statement:
it is the arithmetic-free combination of the two named `E7` nodes

* `EulerCharInput` (`E7a`, the local Euler characteristic
  `Work.SSGRoute.local_tate_duality_euler`): `h¹(M') = h⁰(M') + h²(M') + ε·dim M'` uniformly in
  `M'`, and
* `Deg02Input` (`E7b`, `Work.SSGRoute.local_tate_duality_02`):
  `h²(M) = h⁰(M^∨(1))` and `h²(M^∨(1)) = h⁰(M)`,

because the two expansions of `h¹` (at `M` and at `M^∨(1)`) agree once `dim M = dim M^∨(1)`
(`finrank_dualMod` and `finrank_tensor_rankOne`).  The lemma below is that computation; it is the
sharpest displayed form of the node's finite-place obligation. -/

section FinPlaceDimFromE7

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The finite-place dimension equality from the Euler characteristic and the degrees `0`/`2`
duality.**  Given the `E7a` input `hE` and the `E7b` input `h02` at the place `A`, the local `H¹`'s
of `M` and of `M^∨(1) = DualMod p (M ⊗ T)` have the same `𝔽_p`-dimension. -/
theorem finrank_H1loc_tate_dual_of_euler02 (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE : EulerCharInput p k Ω K) (h02 : Deg02Input p k Ω K ζ hζ hζK T hT)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  haveI hTfin : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  haveI hQfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  obtain ⟨ε, hε⟩ := hE A hA
  have h1 := (hε M).2
  have h2 := (hε (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))).2
  have hM := (h02 A hA M).1
  have hM' := (h02 A hA M).2
  have hdim : Module.finrank (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      = Module.finrank (ZMod p) M := by
    rw [finrank_dualMod, Module.finrank_tensorProduct, hT.1, mul_one]
  have h2' := h2
  rw [hdim] at h2'
  rw [h1, hM, h2', hM']
  ring

end FinPlaceDimFromE7

/-! ## `hcard` from the finite-place dimension equalities alone

Combining `hcard_of_localDims` with the *free* archimedean dimension equality
`finrank_H1loc_zpowers_tate_dual`: the `Nat.card` equality of the two local class spaces — one of
the two inputs of `countingIdentity_of_oneSidedDualAnnihilator` — follows from the **finite-place**
dimension equalities `dim H¹(D_A, M) = dim H¹(D_A, M^∨(1))` alone.  This displays the arithmetic
obligation of the node in its sharpest form: at finite places, the local Euler characteristic
(`Work.SSGRoute.local_tate_duality_euler`, node `E7a`) together with the degrees `0`/`2` duality
(`Work.SSGRoute.local_tate_duality_02`, node `E7b`); at the involutions, nothing. -/

section FinitePlaceCard

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The `Nat.card` equality of the two local class spaces, from the *finite-place* dimension
equalities.**  The archimedean side is free (`finrank_H1loc_zpowers_tate_dual`), so the arithmetic
input of the counting step is exactly the local dimension equality at the places of `S`. -/
theorem hcard_of_localDims_finPlace (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)))
    (hS' : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)))
    (hdS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1))) :
    Nat.card (primalClasses p k Ω K M S C) =
      Nat.card (primalClasses p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) := by
  haveI hTfin : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  haveI hQfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  refine hcard_of_localDims (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
    (S := S) (C := C) hS hS' ?_ ?_ hdS ?_
  · intro c
    exact moduleFinite_H1loc_zpowers p k Ω K M c.1 (hCinv c.1 c.2)
  · intro c
    exact moduleFinite_H1loc_zpowers p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) c.1 (hCinv c.1 c.2)
  · intro c
    exact finrank_H1loc_zpowers_tate_dual (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      ζ hζ hζK hT c.1 (hCinv c.1 c.2)

end FinitePlaceCard

/-! ## The node from the two named `E7` nodes, the pairing, and the middle exactness

The capstone of this file's reduction chain: `CountingIdentity` follows from

* `EulerCharInput` (node `E7a`, `Work.SSGRoute.local_tate_duality_euler`),
* `Deg02Input` (node `E7b`, `Work.SSGRoute.local_tate_duality_02`),
* a bi-additive pairing `β` on the two local class spaces, non-degenerate in the first variable
  (the local pairings of `E7` descend to such a `β` — `PT.exists_pairing_on_H1loc` plus the product
  construction of `PT/pt_counting_assembly.lean`), and
* the annihilator identity `V = W^⊥` (`hbot`; its inclusion `V ⊆ W^⊥` is the *proved*
  `PT.pt_orthogonality_of_realizable`, so this is the middle exactness of the relaxed
  Poitou–Tate sequence, node `E9`),

together with the finiteness of the two class spaces.  Nothing else in this file's chain is an
input: the `Nat.card` equality and the per-place dimension equalities are *derived*. -/

section NodeFromE7AndE9

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The node from the two `E7` nodes, the pairing, and the middle exactness.** -/
theorem countingIdentity_of_euler02_and_annihilator (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE : EulerCharInput p k Ω K) (h02 : Deg02Input p k Ω K ζ hζ hζK T hT)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (β : primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : primalClasses p k Ω K M S C, (∀ y, β x y = 0) → x = 0)
    (hbot : ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) ↔
        ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
          y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C) →
            β x y = 0)
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C := by
  haveI hTfin : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  haveI hQfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  refine countingIdentity_of_localDims_and_annihilator (p := p) (k := k) (Ω := Ω) (K := K)
    (N := N) (hKN := hKN) (T := T) (M := M) (S := S) (C := C)
    hCinv β haddL haddR hndL ?_ ?_ ?_ ?_ ?_ ?_ hbot hfinP hfinQ
  · intro A
    exact moduleFinite_H1loc_finPlace p k Ω K M A.1 (hSfin A.1 A.2)
  · intro A
    exact moduleFinite_H1loc_finPlace p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A.1 (hSfin A.1 A.2)
  · intro c
    exact moduleFinite_H1loc_zpowers p k Ω K M c.1 (hCinv c.1 c.2)
  · intro c
    exact moduleFinite_H1loc_zpowers p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) c.1 (hCinv c.1 c.2)
  · intro A
    exact finrank_H1loc_tate_dual_of_euler02 (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      ζ hζ hζK hT hE h02 A.1 (hSfin A.1 A.2)
  · intro c
    exact finrank_H1loc_zpowers_tate_dual (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      ζ hζ hζK hT c.1 (hCinv c.1 c.2)

end NodeFromE7AndE9

/-! ## The node from the local Tate system and the middle exactness — the interface of the pipeline

The sharpest reduction of this file: `CountingIdentity` follows from

* a family `pair` of local pairings satisfying `LocalAxioms` at every local group (`hloc`) — the
  *exact* interface that `PT.pt_canonical_relaxed_of_inputs` and `PT.pt_selmer_relaxed` consume as
  their `hloc` (node `E7` plus the canonical construction, gap (1) of the pipeline), and
* the annihilator identity `V = W^⊥` for the product pairing built from `pair` (`hbot`) — the
  middle exactness of the relaxed Poitou–Tate sequence (node `E9`; the inclusion `V ⊆ W^⊥` is the
  *proved* `PT.pt_orthogonality_of_realizable`),

together with the finiteness of the two class spaces.  The pairing on the two local class spaces is
*constructed* here (`PT.localPairingFun` followed by `PT.productFormFun`), its additivity and
left-non-degeneracy are read off `hloc`, and the `Nat.card` equality `Nat.card P = Nat.card P'` is
derived from the per-place dimension equalities produced by
`pt_finrank_eq_of_nondegenerate_pairing` at each place.  So the node adds *nothing* to `hloc` and
`hbot`: it is exactly their consequence. -/

section NodeFromLocalAxioms

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The node from the local Tate system `hloc` and the annihilator identity `hbot`.** -/
theorem countingIdentity_of_localAxioms_and_annihilator
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hbot : ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) ↔
        ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
          y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C) →
            productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
              (C := C)
              (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
              x y = 0)
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C := by
  haveI hQfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  let B := localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
  have hndS : ∀ A ∈ S, ∀ x : H1loc p k Ω K M (SSGRoute.decomp k A),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A), B (SSGRoute.decomp k A) x y = 0) → x = 0 :=
    fun A hA => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hndSc : ∀ c ∈ C, ∀ x : H1loc p k Ω K M (Subgroup.zpowers c),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c), B (Subgroup.zpowers c) x y = 0) → x = 0 :=
    fun c hc => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inr ⟨c, hCinv c hc, rfl⟩)
  have hndR : ∀ A ∈ S, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A),
      (∀ x : H1loc p k Ω K M (SSGRoute.decomp k A), B (SSGRoute.decomp k A) x y = 0) → y = 0 :=
    fun A hA => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hndRc : ∀ c ∈ C, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c),
      (∀ x : H1loc p k Ω K M (Subgroup.zpowers c), B (Subgroup.zpowers c) x y = 0) → y = 0 :=
    fun c hc => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inr ⟨c, hCinv c hc, rfl⟩)
  have hfinS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1)) :=
    fun A => moduleFinite_H1loc_finPlace p k Ω K M A.1 (hSfin A.1 A.2)
  have hfinS' : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)) :=
    fun A => moduleFinite_H1loc_finPlace p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A.1 (hSfin A.1 A.2)
  have hfinC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1)) :=
    fun c => moduleFinite_H1loc_zpowers p k Ω K M c.1 (hCinv c.1 c.2)
  have hfinC' : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.Finite (ZMod p) (H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1)) :=
    fun c => moduleFinite_H1loc_zpowers p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) c.1 (hCinv c.1 c.2)
  have hdS : ∀ A : {A : ValuationSubring Ω // A ∈ S},
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1)) :=
    fun A => pt_finrank_eq_of_nondegenerate_pairing (K := ZMod p) (B (SSGRoute.decomp k A.1))
      (hndS A.1 A.2) (hndR A.1 A.2)
  have hdC : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      Module.finrank (ZMod p) (H1loc p k Ω K M (Subgroup.zpowers c.1))
        = Module.finrank (ZMod p) (H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1)) :=
    fun c => pt_finrank_eq_of_nondegenerate_pairing (K := ZMod p) (B (Subgroup.zpowers c.1))
      (hndSc c.1 c.2) (hndRc c.1 c.2)
  refine countingIdentity_of_oneSidedDualAnnihilator (p := p) (k := k) (Ω := Ω) (K := K)
    (N := N) (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hCinv
    (productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B)
    ?_ ?_ ?_ ?_ hbot hfinP hfinQ
  · intro x x' y
    exact productFormFun_add_left (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C) B x x' y
  · intro x y y'
    exact productFormFun_add_right (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C) B x y y'
  · intro x hx
    exact productFormFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C) B hndS hndSc x hx
  · exact natCard_primalClasses_eq_of_finrank_eq (p := p) (k := k) (Ω := Ω) (K := K)
      (M := M) (M' := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (S := S) (C := C)
      hfinS hfinS' hfinC hfinC' hdS hdC

section ReciprocityHalf

include hKN

/-- **The forward half of the annihilator identity.**  Every realizable class is orthogonal, under a
pairing `B` on the local `H¹`-spaces that agrees with the local family `pair` on local classes
(`hB`, `hBc`), to every relaxed dual Selmer class.  This is the reciprocity half of the middle
exactness of the relaxed Poitou–Tate sequence; the converse is the middle exactness proper. -/
theorem primalClassSet_orthogonal_dualClassSet
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hrec : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
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
      ∑ A ∈ S', pair (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', pair (Subgroup.zpowers c) a b = 0)
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A) →
      B (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b) = pair (SSGRoute.decomp k A) a b)
    (hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c) →
      B (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b) = pair (Subgroup.zpowers c) a b)
    (x : primalClasses p k Ω K M S C)
    (hx : x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
      (C := C))
    (y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)
    (hy : y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
      (S := S) (C := C)) :
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
      B x y = 0 := by
  classical
  rw [mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
    (M := M) (S := S) (C := C) hCinv x] at hx
  obtain ⟨α', β', ε, hcls, hε1, hε2, hεα', hεβ', hεunr⟩ := hx
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
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
      pair hloc hrec S hSfin C α' β' ε ⟨hε1, hε2⟩
      (fun A hA => hα'lc A hA) hεα' (fun A hA => hεα'lc A hA)
      (fun c hc => (hβ'lc c hc).1) hεβ' (fun c hc => hεβ'lc c hc)
      b.1 ⟨b.2.1, b.2.2.1⟩ S' hS'sub hS'fin hS'disj hS'good hS'cob hCinv hC hCdisj
  rw [productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T)
    (M := M) (S := S) (C := C) pair B hB hBc α' β' hα'lc hβ'lc b.1 b.2,
    Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (α' A) b.1),
    Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β' c) b.1)]
  exact hzero

/-- **The node from the pipeline inputs and the *converse* inclusion alone.**  This is the sharpest
form of the reduction in this file: the inclusion `V ⊆ W^⊥` is *proved*
(`primalClassSet_orthogonal_dualClassSet`, from the pipeline's reciprocity law `hrec`), so the only
non-pipeline input left is the converse `W^⊥ ⊆ V` — the realizability half of the middle exactness of
the relaxed Poitou–Tate sequence, i.e. the annihilator identity proper. -/
theorem countingIdentity_of_reciprocity_and_converse
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hrec : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
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
      ∑ A ∈ S', pair (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', pair (Subgroup.zpowers c) a b = 0)
    (hconv : ∀ x : primalClasses p k Ω K M S C,
      (∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
        y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
          (S := S) (C := C) →
        productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
          (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
          x y = 0) →
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
        (C := C))
    (hfinP : Finite (primalClasses p k Ω K M S C))
    (hfinQ : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)) :
    CountingIdentity p k Ω K N hKN T M S C := by
  classical
  let B := localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
  have hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A) →
      B (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b) = pair (SSGRoute.decomp k A) a b :=
    fun A hA => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c) →
      B (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b) = pair (Subgroup.zpowers c) a b :=
    fun c hc => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inr ⟨c, hCinv c hc, rfl⟩)
  refine countingIdentity_of_localAxioms_and_annihilator (p := p) (k := k) (Ω := Ω) (K := K)
    (N := N) (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hSfin hCinv pair hloc ?_ hfinP hfinQ
  intro x
  refine ⟨fun hx y hy => ?_, fun h => hconv x h⟩
  have h1 : productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
      (C := C) B x y = 0 :=
    primalClassSet_orthogonal_dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
      (hKN := hKN) (T := T) (M := M) (S := S) (C := C) hSfin hSdisj hSram hCinv hC hCdisj
      pair hloc hrec B hB hBc x hx y hy
  exact h1

end ReciprocityHalf

end NodeFromLocalAxioms

/-! ## The index set of the relaxed Poitou–Tate product, and the `C`-block

This is the architecture of the *instantiation* of `PT.restrictedProduct_relaxation` at the
arithmetic data, i.e. the finite-place-indexed form of node `E9`.

**The index type.**  `PtIndex k Ω C` = the finite places of `Ω` over `k` **modulo conjugacy** (one
index per prime of `k`; the cofinite "unramified almost everywhere" condition is false for the type
of *all* places of `Ω`, cf. `PT/pt_unramifiedSub.lean`), together with the given involutions `C`.

**The `C`-block.**  The involutions are handled by their *own* case, and the two constraints of the
relaxation lemma are chosen so that at a `C`-index they are automatic:

* primal family `ptU := unramified` at a finite place, `⊤` at a `C`-index;
* dual family `ptU' := unramified` at a finite place, `⊥` at a `C`-index.

Then

* the restricted-product condition is **vacuous** at the `C`-indices (`mem_restrictedProduct_ptU'`:
  the `C`-indices are finitely many, so the cofinite condition may exclude them all) — so every
  local value at `C` is admissible, both for the primal and for the dual side;
* `hβ0` (the two "unramified" subgroups annihilate each other) is **trivial** at a `C`-index, since
  the dual side is `⊥` there (`ptβ_zero_at_C`);
* `hU` (`U' = U^⊥`) at a `C`-index reduces to the *right-non-degeneracy* of the local pairing there
  (`ptU'_eq_orthogonal_at_C`), which is the archimedean local Tate duality — a proved statement.

So the whole arithmetic input of the instantiation is confined to the **finite places**
(`ptβ_zero_of_localInput`, `ptU'_eq_orthogonal_of_localInput`), which is exactly the shape in which
the `E7`/`E8` lanes deliver it: the unramified subgroup is its own annihilator at a good finite
place, and the *relaxation* then produces an element of the unrestricted localisation image which is
unramified off `Ram` and matches the prescribed data — including the `C`-components, because the
relaxation subgroup is `0` on the prescribed set `T` (which contains `C`). -/

section PtIndexBlock

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- The index type of the relaxed Poitou–Tate product: the finite places of `Ω` over `k` modulo
conjugacy, together with the given involutions of `C`. -/
abbrev PtIndex (C : Finset (Ω ≃ₐ[k] Ω)) : Type :=
  Quotient (finPlaceConjSetoid k Ω) ⊕ {c : Ω ≃ₐ[k] Ω // c ∈ C}

/-- The local group at an index: the decomposition group of a finite place, or the procyclic group
generated by an involution. -/
def ptGroup (C : Finset (Ω ≃ₐ[k] Ω)) : PtIndex k Ω C → Subgroup (Ω ≃ₐ[k] Ω)
  | Sum.inl i => SSGRoute.decomp k (Quotient.out i).1
  | Sum.inr c => Subgroup.zpowers c.1

/-- The local `H¹`-class space at an index. -/
abbrev ptX (C : Finset (Ω ≃ₐ[k] Ω)) : PtIndex k Ω C → Type :=
  fun i => H1loc p k Ω K M (ptGroup k Ω C i)

/-- The "unramified" subgroup family of the primal side: the unramified subgroup at a finite
place, everything at a `C`-index (the local conditions at the involution groups are relaxed in the
primal direction). -/
def ptU (C : Finset (Ω ≃ₐ[k] Ω)) : ∀ i : PtIndex k Ω C, Submodule (ZMod p) (ptX p k Ω K M C i) :=
  fun i => match i with
    | Sum.inl j => unramifiedSub p k Ω K M (Quotient.out j).1
    | Sum.inr _ => ⊤

/-- The "unramified" subgroup family of the dual side: the unramified subgroup at a finite place,
the zero subgroup at a `C`-index. -/
def ptU' (C : Finset (Ω ≃ₐ[k] Ω)) : ∀ i : PtIndex k Ω C, Submodule (ZMod p) (ptX p k Ω K M C i) :=
  fun i => match i with
    | Sum.inl j => unramifiedSub p k Ω K M (Quotient.out j).1
    | Sum.inr _ => ⊥

@[simp] lemma ptU_inl (C : Finset (Ω ≃ₐ[k] Ω)) (j : Quotient (finPlaceConjSetoid k Ω)) :
    ptU p k Ω K M C (Sum.inl j) = unramifiedSub p k Ω K M (Quotient.out j).1 := rfl

@[simp] lemma ptU_inr (C : Finset (Ω ≃ₐ[k] Ω)) (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) :
    ptU p k Ω K M C (Sum.inr c) = ⊤ := rfl

@[simp] lemma ptU'_inl (C : Finset (Ω ≃ₐ[k] Ω)) (j : Quotient (finPlaceConjSetoid k Ω)) :
    ptU' p k Ω K M C (Sum.inl j) = unramifiedSub p k Ω K M (Quotient.out j).1 := rfl

@[simp] lemma ptU'_inr (C : Finset (Ω ≃ₐ[k] Ω)) (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) :
    ptU' p k Ω K M C (Sum.inr c) = ⊥ := rfl

/-- **The bad set of the `C`-block family.**  The indices at which a family fails to lie in
`ptU'` are contained in the finite-place bad set (mapped into `PtIndex`) together with the finitely
many `C`-indices. -/
theorem badSet_ptU'_subset {C : Finset (Ω ≃ₐ[k] Ω)}
    (y : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i) :
    {i : PtIndex k Ω C | y i ∉ ptU' p k Ω K M C i} ⊆
      (Sum.inl '' {j : Quotient (finPlaceConjSetoid k Ω) |
          y (Sum.inl j) ∉ ptU' p k Ω K M C (Sum.inl j)}) ∪
        (Sum.inr '' (Set.univ : Set {c : Ω ≃ₐ[k] Ω // c ∈ C})) := by
  intro i hi
  rcases i with j | c
  · exact Or.inl ⟨j, hi, rfl⟩
  · exact Or.inr ⟨c, trivial, rfl⟩

/-- **Admissibility of the `C`-block in the restricted product.**  A family that is unramified
almost everywhere on the finite places lies in the restricted product with the family `ptU'`,
whatever its values at the `C`-indices: the `C`-indices are finitely many, so they may all be
excluded from the cofinite condition. -/
theorem mem_restrictedProduct_ptU' {C : Finset (Ω ≃ₐ[k] Ω)}
    (y : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i)
    (hy : ({j : Quotient (finPlaceConjSetoid k Ω) |
      y (Sum.inl j) ∉ ptU' p k Ω K M C (Sum.inl j)}).Finite) :
    ∀ᶠ i in Filter.cofinite, y i ∈ ptU' p k Ω K M C i := by
  classical
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    (Set.Finite.union (hy.image (f := fun j => (Sum.inl j : PtIndex k Ω C)))
      (Set.finite_univ.image (f := fun c => (Sum.inr c : PtIndex k Ω C)))) ?_
  intro i hi
  rcases i with j | c
  · exact Or.inl ⟨j, hi, rfl⟩
  · exact Or.inr ⟨c, trivial, rfl⟩

variable (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]

/-- **`hβ0` at a `C`-index is free**: the dual family vanishes there, so the local product with
anything is `0`. -/
theorem ptB_zero_at_C {C : Finset (Ω ≃ₐ[k] Ω)}
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (c : {c : Ω ≃ₐ[k] Ω // c ∈ C})
    (x : ptX p k Ω K M C (Sum.inr c)) (y : ptX p k Ω K N C (Sum.inr c))
    (hy : y ∈ ptU' p k Ω K N C (Sum.inr c)) :
    B (Sum.inr c) x y = 0 := by
  have hy0 : y = 0 := by simpa using hy
  rw [hy0, map_zero]

/-- **`hU` at a `C`-index**: the annihilator identity `U' = U^⊥` there reduces to the
right-non-degeneracy of the local pairing at the involution, i.e. to the archimedean local Tate
duality. -/
theorem ptU'_eq_orthogonal_at_C {C : Finset (Ω ≃ₐ[k] Ω)}
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hndR : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      ∀ y : ptX p k Ω K N C (Sum.inr c), (∀ x : ptX p k Ω K M C (Sum.inr c),
        B (Sum.inr c) x y = 0) → y = 0)
    (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) (y : ptX p k Ω K N C (Sum.inr c)) :
    y ∈ ptU' p k Ω K N C (Sum.inr c) ↔
      ∀ x : ptX p k Ω K M C (Sum.inr c), x ∈ ptU p k Ω K M C (Sum.inr c) →
        B (Sum.inr c) x y = 0 := by
  constructor
  · intro hy x _
    exact ptB_zero_at_C (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N) (C := C) B c x y hy
  · intro hy
    have hy0 : y = 0 := hndR c y (fun x => hy x trivial)
    simpa using hy0

/-- **The `hβ0` input of the relaxation, assembled from the finite places.**  If the unramified
subgroups annihilate each other at every finite place (the input `hβ0fin`, the "unramified classes
are orthogonal" clause of the local Tate system), then they do so at *every* index of `PtIndex`: the
`C`-case is free. -/
theorem ptB_zero_of_localInput {C : Finset (Ω ≃ₐ[k] Ω)}
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hβ0fin : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
      ∀ y : ptX p k Ω K N C (Sum.inl j), y ∈ ptU' p k Ω K N C (Sum.inl j) →
        B (Sum.inl j) x y = 0) :
    ∀ i : PtIndex k Ω C, ∀ x : ptX p k Ω K M C i, x ∈ ptU p k Ω K M C i →
      ∀ y : ptX p k Ω K N C i, y ∈ ptU' p k Ω K N C i → B i x y = 0 := by
  intro i
  rcases i with j | c
  · exact hβ0fin j
  · intro x _ y hy
    exact ptB_zero_at_C (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N) (C := C) B c x y hy

/-- **The `hU` input of the relaxation, assembled from the finite places.**  If the unramified
subgroup of the dual side is the annihilator of the unramified subgroup of the primal side at every
finite place (`hUnram`), and the local pairing at each involution is right-non-degenerate
(`hndR`, the archimedean local Tate duality), then `U' = U^⊥` holds at *every* index of
`PtIndex`. -/
theorem ptU'_eq_orthogonal_of_localInput {C : Finset (Ω ≃ₐ[k] Ω)}
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hndR : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      ∀ y : ptX p k Ω K N C (Sum.inr c), (∀ x : ptX p k Ω K M C (Sum.inr c),
        B (Sum.inr c) x y = 0) → y = 0)
    (hUnram : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ y : ptX p k Ω K N C (Sum.inl j),
        y ∈ ptU' p k Ω K N C (Sum.inl j) ↔
          ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
            B (Sum.inl j) x y = 0) :
    ∀ i : PtIndex k Ω C, ∀ y : ptX p k Ω K N C i,
      y ∈ ptU' p k Ω K N C i ↔
        ∀ x : ptX p k Ω K M C i, x ∈ ptU p k Ω K M C i → B i x y = 0 := by
  intro i
  rcases i with j | c
  · exact hUnram j
  · exact ptU'_eq_orthogonal_at_C (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N)
      (C := C) B hndR c


/-- **The `hU` input of the relaxation at the indices outside `Ram`.**  Same as
`ptU'_eq_orthogonal_of_localInput`, but the finite-place clause `hUnram` is required only at the
indices outside `Ram` and the `C`-indices are handled by the archimedean duality `hndR` — this is the
form in which the relaxation step needs it (`PT.restrictedProduct_relaxation_offRam`), and it
removes the *Lagrangian* requirement at the places of `S ∪ C`. -/
theorem ptU'_eq_orthogonal_offRam {C : Finset (Ω ≃ₐ[k] Ω)}
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hndR : ∀ c : {c : Ω ≃ₐ[k] Ω // c ∈ C},
      ∀ y : ptX p k Ω K N C (Sum.inr c), (∀ x : ptX p k Ω K M C (Sum.inr c),
        B (Sum.inr c) x y = 0) → y = 0)
    (Ram : Set (PtIndex k Ω C))
    (hUnram : ∀ j : Quotient (finPlaceConjSetoid k Ω), Sum.inl j ∉ Ram →
      ∀ y : ptX p k Ω K N C (Sum.inl j),
        y ∈ ptU' p k Ω K N C (Sum.inl j) ↔
          ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
            B (Sum.inl j) x y = 0) :
    ∀ i : PtIndex k Ω C, i ∉ Ram → ∀ y : ptX p k Ω K N C i,
      y ∈ ptU' p k Ω K N C i ↔
        ∀ x : ptX p k Ω K M C i, x ∈ ptU p k Ω K M C i → B i x y = 0 := by
  intro i hi
  rcases i with j | c
  · exact hUnram j hi
  · exact ptU'_eq_orthogonal_at_C (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N)
      (C := C) B hndR c

open scoped RestrictedProduct

set_option maxHeartbeats 16000000 in
/-- **The instantiation of the relaxation step, in the relaxation's own vocabulary, with the
`C`-block inside the restricted product.**

This is the finite-place-indexed instantiation of node `E9`'s relaxation: the hypothesis `hAB` is the
*unrestricted* middle exactness (`a ∈ A ↔ ∀ b ∈ B, ⟨a,b⟩ = 0`), the local input is required only at
the **finite places** (`hβ0fin`: the unramified subgroups annihilate each other; `hUnram`: the
unramified subgroup of the dual side is the annihilator of the unramified subgroup of the primal
side), and the `C`-indices carry the families `ptU = ⊤`, `ptU' = ⊥` so that the two hypotheses
`hβ0` and `hU` of `PT.restrictedProduct_relaxation` are *automatic* there.  The conclusion is the
relaxed statement: the prescribed data `x` on `T` is realised by an element of `A` unramified off
`Ram`.  It is one application of `PT.restrictedProduct_relaxation`. -/
theorem pt_relaxation_instantiation {C : Finset (Ω ≃ₐ[k] Ω)}
    [∀ i, TopologicalSpace (ptX p k Ω K M C i)] [∀ i, DiscreteTopology (ptX p k Ω K M C i)]
    [∀ i, Finite (ptX p k Ω K M C i)]
    [∀ i, TopologicalSpace (ptX p k Ω K N C i)] [∀ i, DiscreteTopology (ptX p k Ω K N C i)]
    [∀ i, Finite (ptX p k Ω K N C i)]
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i : PtIndex k Ω C, ∀ x : ptX p k Ω K M C i,
      (∀ y : ptX p k Ω K N C i, B i x y = 0) → x = 0)
    (hβR : ∀ i : PtIndex k Ω C, ∀ y : ptX p k Ω K N C i,
      (∀ x : ptX p k Ω K M C i, B i x y = 0) → y = 0)
    (hβ0fin : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
      ∀ y : ptX p k Ω K N C (Sum.inl j), y ∈ ptU' p k Ω K N C (Sum.inl j) →
        B (Sum.inl j) x y = 0)
    (hUnram : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ y : ptX p k Ω K N C (Sum.inl j),
        y ∈ ptU' p k Ω K N C (Sum.inl j) ↔
          ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
            B (Sum.inl j) x y = 0)
    (Ram : Set (PtIndex k Ω C)) (T : Finset (PtIndex k Ω C)) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (A : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i]))
    (B' : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i]))
    (hAcomp : IsCompact (A : Set (Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i])))
    (hBcomp : IsCompact (B' : Set (Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i])))
    (hAB : ∀ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ↔ ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i],
        b ∈ B' → restrictedPairing (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
          (ptU p k Ω K M C) (ptU' p k Ω K N C) B a b = 0)
    (x : (i : T) → ptX p k Ω K M C i)
    (hx : ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i], b ∈ B' →
      (∀ i, i ∉ Ram → (b i : ptX p k Ω K N C i) ∈ ptU' p k Ω K N C i) →
      (∀ i, i ∈ Ram → i ∉ T → (b i : ptX p k Ω K N C i) = 0) →
      ∑ i : T, B (i : PtIndex k Ω C) (x i) (b (i : PtIndex k Ω C)) = 0) :
    ∃ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ∧ (∀ i, i ∉ Ram → (a i : ptX p k Ω K M C i) ∈ ptU p k Ω K M C i) ∧
        (∀ i : T, a (i : PtIndex k Ω C) = x i) :=
  restrictedProduct_relaxation (p := p)
    (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
    (ptU p k Ω K M C) (ptU' p k Ω K N C) B hβL hβR
    (ptB_zero_of_localInput (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N) (C := C)
      B hβ0fin)
    (ptU'_eq_orthogonal_of_localInput (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N)
      (C := C) B (fun (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) y hy => hβR (Sum.inr c) y hy) hUnram)
    Ram T hTRam A B' hAcomp hBcomp hAB x hx

/-! ## The finite index set of the relaxed product

The relaxation is instantiated below with the finite set of indices at which local data are
prescribed: one index per conjugacy class of a place of `S`, and one per involution of `C`.  The
local `H¹` at the index of a place `A ∈ S` is that of the *canonical representative*
`(Quotient.out (mk A)).1` of its conjugacy class; the transport to the original place `A` — the
identification that turns the prescribed data of the relaxed product into the `S`-components of
`primalClasses` — is `ptT_conjEquiv_nonempty`, from the conjugacy transport
`h1loc_conjEquiv_nonempty` above. -/

/-- **The finite set of indices at which local data are prescribed**: one index per conjugacy class
of a place of `S`, and one per involution of `C`. -/
noncomputable def ptT (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω)) :
    Finset (PtIndex k Ω C) := by
  classical
  exact (S.attach.image (fun A => (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω)
      ⟨A.1, hSfin A.1 A.2⟩) : PtIndex k Ω C))) ∪
    (C.attach.image (fun c => (Sum.inr c : PtIndex k Ω C)))

lemma mem_ptT_inl {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    {A : ValuationSubring Ω} (hA : A ∈ S) :
    (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩) : PtIndex k Ω C) ∈
      ptT k Ω S hSfin C := by
  classical
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach S ⟨A, hA⟩, rfl⟩)

lemma mem_ptT_inr {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    {c : Ω ≃ₐ[k] Ω} (hc : c ∈ C) :
    (Sum.inr ⟨c, hc⟩ : PtIndex k Ω C) ∈ ptT k Ω S hSfin C := by
  classical
  exact Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_attach C ⟨c, hc⟩, rfl⟩)

/-- **The index set `ptT` consists of the conjugacy classes of the places of `S` and the
involutions of `C`.**  This is the combinatorial half of the identification of the prescribed data
of the relaxed product with the components of `primalClasses`. -/
theorem mem_ptT_iff {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    (i : PtIndex k Ω C) :
    i ∈ ptT k Ω S hSfin C ↔
      (∃ (A : ValuationSubring Ω) (hA : A ∈ S),
        i = Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩)) ∨
      (∃ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ C), i = Sum.inr ⟨c, hc⟩) := by
  classical
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_image.mp h with ⟨A, -, rfl⟩
      exact Or.inl ⟨A.1, A.2, rfl⟩
    · rcases Finset.mem_image.mp h with ⟨c, -, rfl⟩
      exact Or.inr ⟨c.1, c.2, rfl⟩
  · rintro (⟨A, hA, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach S ⟨A, hA⟩, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_attach C ⟨c, hc⟩, rfl⟩)

/-- **The index of `ptT` attached to a place `A ∈ S`**: the conjugacy class of `A`.  This is the
element of the subtype `↥(ptT k Ω S hSfin C)` at which the local data of the relaxed product at `A`
sit; stating it as a definition keeps the (heavy) membership proof out of the statements that use
it. -/
noncomputable def ptTIdxInl (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω))
    (A : {A : ValuationSubring Ω // A ∈ S}) : ↥(ptT k Ω S hSfin C) :=
  ⟨Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩), by
    classical
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨A, Finset.mem_attach S A, rfl⟩)⟩

/-- **The index of `ptT` attached to an involution `c ∈ C`.** -/
noncomputable def ptTIdxInr (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω))
    (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) : ↥(ptT k Ω S hSfin C) :=
  ⟨Sum.inr c, by
    classical
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨c, Finset.mem_attach C c, rfl⟩)⟩

@[simp] lemma ptTIdxInl_val (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω))
    (A : {A : ValuationSubring Ω // A ∈ S}) :
    (ptTIdxInl k Ω S hSfin C A).1 =
      (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩) :
        PtIndex k Ω C) := rfl

@[simp] lemma ptTIdxInr_val (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω))
    (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) :
    (ptTIdxInr k Ω S hSfin C c).1 = (Sum.inr c : PtIndex k Ω C) := rfl



/-- **Finiteness of the local class spaces of the relaxed product.**  Each `ptX i` is the local
`H¹` of a decomposition group at a finite place (finite by `PT.finite_H1loc`) or of the procyclic
group generated by an involution (finite by `PT.finite_H1loc_zpowers`, which is why the hypothesis
`hCinv` is needed).  This discharges the `Finite` instance arguments of the relaxation
instantiation at the arithmetic data. -/
theorem finite_ptX [Finite M] {C : Finset (Ω ≃ₐ[k] Ω)} (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    ∀ i : PtIndex k Ω C, Finite (ptX p k Ω K M C i) := by
  intro i
  rcases i with j | c
  · show Finite (H1loc p k Ω K M (SSGRoute.decomp k (Quotient.out j).1))
    exact finite_H1loc p k Ω K M (Quotient.out j).1 (Quotient.out j).2
  · show Finite (H1loc p k Ω K M (Subgroup.zpowers c.1))
    exact finite_H1loc_zpowers p k Ω K M c.1 (hCinv c.1 c.2)

set_option maxHeartbeats 16000000 in
/-- **The relaxation instantiation in the compactness-free form.**

Same statement as `pt_relaxation_instantiation`, but the two compactness hypotheses
`hAcomp`/`hBcomp` (which are *not* available at the arithmetic data: the restricted product over the
infinite index set `PtIndex k Ω C` is not compact, and the image of the global classes need not be
closed there) are replaced by the single hypothesis `hBcl` — *the annihilator of `A` is `B`* —
which is the shape in which node `E9` supplies the duality (`restrictedProduct_relaxation_of_dualPair`
is the compactness-free relaxation step; `hBcomp` + `hAB` implied `hBcl`, so nothing is lost). -/
theorem pt_relaxation_instantiation_of_dualPair {C : Finset (Ω ≃ₐ[k] Ω)}
    [∀ i, TopologicalSpace (ptX p k Ω K M C i)] [∀ i, DiscreteTopology (ptX p k Ω K M C i)]
    [∀ i, Finite (ptX p k Ω K M C i)]
    [∀ i, TopologicalSpace (ptX p k Ω K N C i)] [∀ i, DiscreteTopology (ptX p k Ω K N C i)]
    [∀ i, Finite (ptX p k Ω K N C i)]
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i : PtIndex k Ω C, ∀ x : ptX p k Ω K M C i,
      (∀ y : ptX p k Ω K N C i, B i x y = 0) → x = 0)
    (hβR : ∀ i : PtIndex k Ω C, ∀ y : ptX p k Ω K N C i,
      (∀ x : ptX p k Ω K M C i, B i x y = 0) → y = 0)
    (hβ0fin : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
      ∀ y : ptX p k Ω K N C (Sum.inl j), y ∈ ptU' p k Ω K N C (Sum.inl j) →
        B (Sum.inl j) x y = 0)
    (hUnram : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ y : ptX p k Ω K N C (Sum.inl j),
        y ∈ ptU' p k Ω K N C (Sum.inl j) ↔
          ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
            B (Sum.inl j) x y = 0)
    (Ram : Set (PtIndex k Ω C)) (T : Finset (PtIndex k Ω C)) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (A : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i]))
    (B' : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i]))
    (hBcl : ∀ y : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i],
      (∀ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
        a ∈ A → restrictedPairing (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
          (ptU p k Ω K M C) (ptU' p k Ω K N C) B a y = 0) → y ∈ B')
    (hAB : ∀ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ↔ ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i],
        b ∈ B' → restrictedPairing (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
          (ptU p k Ω K M C) (ptU' p k Ω K N C) B a b = 0)
    (x : (i : T) → ptX p k Ω K M C i)
    (hx : ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i], b ∈ B' →
      (∀ i, i ∉ Ram → (b i : ptX p k Ω K N C i) ∈ ptU' p k Ω K N C i) →
      (∀ i, i ∈ Ram → i ∉ T → (b i : ptX p k Ω K N C i) = 0) →
      ∑ i : T, B (i : PtIndex k Ω C) (x i) (b (i : PtIndex k Ω C)) = 0) :
    ∃ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ∧ (∀ i, i ∉ Ram → (a i : ptX p k Ω K M C i) ∈ ptU p k Ω K M C i) ∧
        (∀ i : T, a (i : PtIndex k Ω C) = x i) :=
  restrictedProduct_relaxation_of_dualPair (p := p)
    (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
    (ptU p k Ω K M C) (ptU' p k Ω K N C) B hβL hβR
    (ptB_zero_of_localInput (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N) (C := C)
      B hβ0fin)
    (ptU'_eq_orthogonal_of_localInput (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N)
      (C := C) B (fun (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) y hy => hβR (Sum.inr c) y hy) hUnram)
    Ram T hTRam A B' hBcl hAB x hx

set_option maxHeartbeats 16000000 in
/-- **The instantiation of the relaxation step, with the annihilator clause required only off
`Ram`.**

Same statement as `pt_relaxation_instantiation_of_dualPair`, but the finite-place clause `hUnram` is
required only at the indices outside `Ram` (the `C`-indices are handled by the archimedean duality,
which is a consequence of `hndR`).  Since the places above `p` all lie in `S` and hence in `Ram`,
this is the form of the relaxation step that is available at **every** prime `p`, without the
Lagrangian hypothesis `unr = unr^⊥` at the places above `p` (which fails at `p = 2`). -/
theorem pt_relaxation_instantiation_of_dualPair_offRam {C : Finset (Ω ≃ₐ[k] Ω)}
    [∀ i, TopologicalSpace (ptX p k Ω K M C i)] [∀ i, DiscreteTopology (ptX p k Ω K M C i)]
    [∀ i, Finite (ptX p k Ω K M C i)]
    [∀ i, TopologicalSpace (ptX p k Ω K N C i)] [∀ i, DiscreteTopology (ptX p k Ω K N C i)]
    [∀ i, Finite (ptX p k Ω K N C i)]
    (B : ∀ i : PtIndex k Ω C, ptX p k Ω K M C i →ₗ[ZMod p] ptX p k Ω K N C i →ₗ[ZMod p] ZMod p)
    (hβL : ∀ i : PtIndex k Ω C, ∀ x : ptX p k Ω K M C i,
      (∀ y : ptX p k Ω K N C i, B i x y = 0) → x = 0)
    (hβR : ∀ i : PtIndex k Ω C, ∀ y : ptX p k Ω K N C i,
      (∀ x : ptX p k Ω K M C i, B i x y = 0) → y = 0)
    (hβ0fin : ∀ j : Quotient (finPlaceConjSetoid k Ω),
      ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
      ∀ y : ptX p k Ω K N C (Sum.inl j), y ∈ ptU' p k Ω K N C (Sum.inl j) →
        B (Sum.inl j) x y = 0)
    (Ram : Set (PtIndex k Ω C)) (T : Finset (PtIndex k Ω C)) (hTRam : ∀ i ∈ T, i ∈ Ram)
    (hUnram : ∀ j : Quotient (finPlaceConjSetoid k Ω), Sum.inl j ∉ Ram →
      ∀ y : ptX p k Ω K N C (Sum.inl j),
        y ∈ ptU' p k Ω K N C (Sum.inl j) ↔
          ∀ x : ptX p k Ω K M C (Sum.inl j), x ∈ ptU p k Ω K M C (Sum.inl j) →
            B (Sum.inl j) x y = 0)
    (A : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i]))
    (B' : Submodule (ZMod p) (Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i]))
    (hBcl : ∀ y : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i],
      (∀ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
        a ∈ A → restrictedPairing (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
          (ptU p k Ω K M C) (ptU' p k Ω K N C) B a y = 0) → y ∈ B')
    (hAB : ∀ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ↔ ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i],
        b ∈ B' → restrictedPairing (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
          (ptU p k Ω K M C) (ptU' p k Ω K N C) B a b = 0)
    (x : (i : T) → ptX p k Ω K M C i)
    (hx : ∀ b : Πʳ i : PtIndex k Ω C, [ptX p k Ω K N C i, ptU' p k Ω K N C i], b ∈ B' →
      (∀ i, i ∉ Ram → (b i : ptX p k Ω K N C i) ∈ ptU' p k Ω K N C i) →
      (∀ i, i ∈ Ram → i ∉ T → (b i : ptX p k Ω K N C i) = 0) →
      ∑ i : T, B (i : PtIndex k Ω C) (x i) (b (i : PtIndex k Ω C)) = 0) :
    ∃ a : Πʳ i : PtIndex k Ω C, [ptX p k Ω K M C i, ptU p k Ω K M C i],
      a ∈ A ∧ (∀ i, i ∉ Ram → (a i : ptX p k Ω K M C i) ∈ ptU p k Ω K M C i) ∧
        (∀ i : T, a (i : PtIndex k Ω C) = x i) :=
  restrictedProduct_relaxation_offRam (p := p)
    (X := ptX p k Ω K M C) (Y := ptX p k Ω K N C)
    (ptU p k Ω K M C) (ptU' p k Ω K N C) B hβL hβR
    (ptB_zero_of_localInput (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N) (C := C)
      B hβ0fin)
    Ram T hTRam
    (ptU'_eq_orthogonal_offRam (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (N := N)
      (C := C) B (fun (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) y hy => hβR (Sum.inr c) y hy) Ram hUnram)
    A B' hBcl hAB x hx

end PtIndexBlock

/-! ## The bookkeeping of the prescribed index set `ptT`

The lemmas below are the combinatorial facts about `ptT` that the identification of the prescribed
data of the relaxation with the components of `primalClasses` needs: the index maps of the places of
`S` and of the involutions of `C` are injective, their ranges are disjoint, and the cardinality of
`ptT` is therefore `#S + #C`. -/

section PtIndexBookkeeping

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The index of a place of `S` is injective on `S`**: two places of `S` with the same conjugacy
class are conjugate, hence equal by `hSdisj`. -/
theorem ptTIdxInl_injective (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (C : Finset (Ω ≃ₐ[k] Ω)) :
    Function.Injective (ptTIdxInl k Ω S hSfin C) := by
  intro A B h
  refine Subtype.ext (hSdisj A.1 A.2 B.1 B.2 ?_)
  have h2 : (ptTIdxInl k Ω S hSfin C A).1 = (ptTIdxInl k Ω S hSfin C B).1 :=
    congrArg Subtype.val h
  simp only [ptTIdxInl_val] at h2
  exact Quotient.exact (Sum.inl_injective (β := {c : Ω ≃ₐ[k] Ω // c ∈ C}) h2)

/-- The index of an involution of `C` is injective. -/
theorem ptTIdxInr_injective (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω)) :
    Function.Injective (ptTIdxInr k Ω S hSfin C) := by
  intro c c' h
  have h2 : (ptTIdxInr k Ω S hSfin C c).1 = (ptTIdxInr k Ω S hSfin C c').1 :=
    congrArg Subtype.val h
  simp only [ptTIdxInr_val] at h2
  have h3 := Sum.inr_injective (α := Quotient (finPlaceConjSetoid k Ω)) h2
  exact Subtype.ext (by simpa using h3)

/-- The set of indices of the places of `S` and the set of indices of the involutions of `C` are
disjoint. -/
theorem ptTIdxInl_ne_inr (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) (C : Finset (Ω ≃ₐ[k] Ω))
    (A : {A : ValuationSubring Ω // A ∈ S}) (c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) :
    ptTIdxInl k Ω S hSfin C A ≠ ptTIdxInr k Ω S hSfin C c := by
  intro h
  have h2 : (ptTIdxInl k Ω S hSfin C A).1 = (ptTIdxInr k Ω S hSfin C c).1 :=
    congrArg Subtype.val h
  simp only [ptTIdxInl_val, ptTIdxInr_val] at h2
  exact absurd h2 (by intro hh; cases hh)

/-- **The cardinality of the prescribed index set**: one index per place of `S` plus one per
involution of `C`.  This is the counting bookkeeping of the prescribed data of the relaxation
(one place per prime, one involution per conjugacy class). -/
theorem ptT_card (S : Finset (ValuationSubring Ω))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (C : Finset (Ω ≃ₐ[k] Ω)) :
    (ptT k Ω S hSfin C).card = S.card + C.card := by
  classical
  have hinj : Function.Injective (fun A : {A : ValuationSubring Ω // A ∈ S} =>
      (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩) : PtIndex k Ω C)) := by
    intro A B h
    refine Subtype.ext (hSdisj A.1 A.2 B.1 B.2 ?_)
    exact Quotient.exact (Sum.inl_injective (β := {c : Ω ≃ₐ[k] Ω // c ∈ C}) h)
  have hinj' : Function.Injective (fun c : {c : Ω ≃ₐ[k] Ω // c ∈ C} =>
      (Sum.inr c : PtIndex k Ω C)) := by
    intro c c' h
    have h3 := Sum.inr_injective (α := Quotient (finPlaceConjSetoid k Ω)) h
    exact Subtype.ext (by simpa using h3)
  have hdisj : Disjoint (S.attach.image (fun A : {A : ValuationSubring Ω // A ∈ S} =>
        (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩) : PtIndex k Ω C)))
      (C.attach.image (fun c : {c : Ω ≃ₐ[k] Ω // c ∈ C} => (Sum.inr c : PtIndex k Ω C))) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rcases Finset.mem_image.mp hi with ⟨A, -, hA⟩
    rcases Finset.mem_image.mp hi' with ⟨c, -, hc⟩
    exact absurd (hA.trans hc.symm) (by intro hh; cases hh)
  unfold ptT
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, Finset.card_attach,
    Finset.card_image_of_injective _ hinj', Finset.card_attach]

end PtIndexBookkeeping

section GenericConj

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

/-- The conjugate `σ N σ⁻¹` of a subgroup. -/
def conjSubSub (σ : Γ) (N : Subgroup Γ) : Subgroup Γ := N.map (MulAut.conj σ).toMonoidHom

lemma mem_conjSubSub {σ : Γ} {N : Subgroup Γ} {g : Γ} :
    g ∈ conjSubSub σ N ↔ σ⁻¹ * g * σ ∈ N := by
  constructor
  · rintro ⟨n, hn, hgn⟩
    have hg : g = σ * n * σ⁻¹ := by
      rw [← hgn]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hg, show σ⁻¹ * (σ * n * σ⁻¹) * σ = n by group]
    exact hn
  · intro hg
    refine ⟨σ⁻¹ * g * σ, hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

lemma conjSubSub_conjSubSub_inv (σ : Γ) (N : Subgroup Γ) :
    conjSubSub σ⁻¹ (conjSubSub σ N) = N := by
  rw [conjSubSub, conjSubSub, Subgroup.map_map]
  have h : (MulAut.conj σ⁻¹).toMonoidHom.comp (MulAut.conj σ).toMonoidHom
      = MonoidHom.id Γ := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

/-- The cocycle condition is carried from `N` to the conjugate subgroup. -/
theorem isCocycleOn_conjSubSub (ρ : Γ →* G) {N : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn ρ N f) (σ : Γ) :
    SSGRoute.IsCocycleOn ρ (conjSubSub σ N) (fun n : Γ => ρ σ • f (σ⁻¹ * n * σ)) := by
  intro g hg h hh
  rw [mem_conjSubSub] at hg hh
  show ρ σ • f (σ⁻¹ * (g * h) * σ) = ρ σ • f (σ⁻¹ * g * σ) + ρ g • (ρ σ • f (σ⁻¹ * h * σ))
  have hgh : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) := by group
  rw [hgh, hf _ hg _ hh, smul_add]
  congr 1
  rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
  congr 1
  group

/-- Local constancy is carried from `N` to the conjugate subgroup. -/
theorem isLocConstOn_conjSubSub [IsTopologicalGroup Γ] {N : Subgroup Γ}
    {f : Γ → M} (hf : SSGRoute.IsLocConstOn N f) (σ : Γ) :
    SSGRoute.IsLocConstOn (conjSubSub σ N) (fun n : Γ => f (σ⁻¹ * n * σ)) := by
  obtain ⟨U, hU, hfU⟩ := hf
  refine ⟨U.comap (MulAut.conj σ⁻¹).toMonoidHom, ?_, ?_⟩
  · exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · intro g hg u hu huH
    have hmem : σ⁻¹ * u * σ ∈ U := by simpa using hu
    have hg' : σ⁻¹ * g * σ ∈ N := mem_conjSubSub.mp hg
    have huH' : σ⁻¹ * u * σ ∈ N := mem_conjSubSub.mp huH
    have hgu : σ⁻¹ * (g * u) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * u * σ) := by group
    show f (σ⁻¹ * (g * u) * σ) = f (σ⁻¹ * g * σ)
    rw [hgu]
    exact hfU _ hg' _ hmem huH'

/-- The coboundary condition is carried from `N` to the conjugate subgroup. -/
theorem isCoboundaryOn_conjSubSub (ρ : Γ →* G) {N : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn ρ N f) (σ : Γ) :
    SSGRoute.IsCoboundaryOn ρ (conjSubSub σ N) (fun n : Γ => ρ σ • f (σ⁻¹ * n * σ)) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨ρ σ • m, ?_⟩
  intro g hg
  have hg' : σ⁻¹ * g * σ ∈ N := mem_conjSubSub.mp hg
  show ρ σ • f (σ⁻¹ * g * σ) = ρ g • (ρ σ • m) - ρ σ • m
  rw [hm _ hg', smul_sub]
  have h2 : ρ σ • (ρ (σ⁻¹ * g * σ) • m) = ρ g • (ρ σ • m) := by
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
    congr 1
    group
  rw [h2]

/-- Pointwise scaling by a constant preserves local constancy. -/
theorem isLocConstOn_const_smul {N : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsLocConstOn N f)
    (g : G) : SSGRoute.IsLocConstOn N (fun n : Γ => g • f n) := by
  obtain ⟨U, hU, hfU⟩ := hf
  refine ⟨U, hU, ?_⟩
  intro a ha u hu huH
  show g • f (a * u) = g • f a
  rw [hfU a ha u hu huH]

end GenericConj

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- The computation rule for the conjugation shift. -/
lemma h1locConjShift_apply (σ : Ω ≃ₐ[k] Ω) (f : (Ω ≃ₐ[k] Ω) → M) (n : Ω ≃ₐ[k] Ω) :
    h1locConjShift p k Ω K M σ f n = SSGRoute.res k K σ • f (σ⁻¹ * n * σ) := rfl

/-- The shift of the inverse is the inverse of the shift, on cochains. -/
lemma h1locConjShift_inv_comp (σ : Ω ≃ₐ[k] Ω) (f : (Ω ≃ₐ[k] Ω) → M) :
    h1locConjShift p k Ω K M σ⁻¹ (h1locConjShift p k Ω K M σ f) = f := by
  funext n
  rw [h1locConjShift_apply, h1locConjShift_apply]
  simp only [inv_inv]
  rw [show σ⁻¹ * (σ * n * σ⁻¹) * σ = n by group]
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The shift of `σ` after the shift of `σ⁻¹` is the identity, on cochains. -/
lemma h1locConjShift_comp_inv (σ : Ω ≃ₐ[k] Ω) (f : (Ω ≃ₐ[k] Ω) → M) :
    h1locConjShift p k Ω K M σ (h1locConjShift p k Ω K M σ⁻¹ f) = f := by
  funext n
  rw [h1locConjShift_apply, h1locConjShift_apply]
  simp only [inv_inv]
  rw [show σ * (σ⁻¹ * n * σ) * σ⁻¹ = n by group]
  rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

/-- The conjugation shift carries the locally constant cocycles on `N` to those on `σ N σ⁻¹`. -/
lemma h1locConjShift_mem_lcCocycles_conj (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω))
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : f ∈ lcCocycles p k Ω K M N) :
    h1locConjShift p k Ω K M σ f ∈ lcCocycles p k Ω K M (conjSubSub σ N) := by
  have hfl : (h1locConjShift p k Ω K M σ) f
      = fun n : Ω ≃ₐ[k] Ω => SSGRoute.res k K σ • f (σ⁻¹ * n * σ) := by
    funext n
    rw [h1locConjShift_apply]
  rw [hfl]
  exact ⟨isCocycleOn_conjSubSub (SSGRoute.res k K) (f := f) hf.1 σ,
    isLocConstOn_const_smul (isLocConstOn_conjSubSub (f := f) hf.2 σ) (SSGRoute.res k K σ)⟩

/-- The conjugation shift carries coboundaries on `N` to coboundaries on `σ N σ⁻¹`. -/
lemma h1locConjShift_mem_coboundaries_conj (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω))
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : f ∈ coboundaries p k Ω K M N) :
    h1locConjShift p k Ω K M σ f ∈ coboundaries p k Ω K M (conjSubSub σ N) :=
  isCoboundaryOn_conjSubSub (SSGRoute.res k K) (f := f) hf σ

/-- Membership in the workspace's `cobQ` is membership of the underlying cochain in the
coboundaries. -/
lemma pt_mem_cobQ_iff {N : Subgroup (Ω ≃ₐ[k] Ω)} (f : ↥(lcCocycles p k Ω K M N)) :
    f ∈ cobQ p k Ω K M N ↔ f.1 ∈ coboundaries p k Ω K M N := Iff.rfl

/-- The conjugation shift on locally constant cocycles, from `N` to `σ N σ⁻¹`. -/
noncomputable def lcConjHom (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    ↥(lcCocycles p k Ω K M N) →ₗ[ZMod p] ↥(lcCocycles p k Ω K M (conjSubSub σ N)) where
  toFun f := ⟨h1locConjShift p k Ω K M σ f.1,
    h1locConjShift_mem_lcCocycles_conj p k Ω K M σ N f.2⟩
  map_add' f g := Subtype.ext ((h1locConjShift p k Ω K M σ).map_add f.1 g.1)
  map_smul' c f := Subtype.ext ((h1locConjShift p k Ω K M σ).map_smul c f.1)

/-- The inverse conjugation shift on locally constant cocycles, from `σ N σ⁻¹` back to `N`. -/
noncomputable def lcConjHomInv (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    ↥(lcCocycles p k Ω K M (conjSubSub σ N)) →ₗ[ZMod p] ↥(lcCocycles p k Ω K M N) where
  toFun g := ⟨h1locConjShift p k Ω K M σ⁻¹ g.1, by
    have h := h1locConjShift_mem_lcCocycles_conj p k Ω K M σ⁻¹ (conjSubSub σ N) g.2
    rwa [conjSubSub_conjSubSub_inv] at h⟩
  map_add' f g := Subtype.ext ((h1locConjShift p k Ω K M σ⁻¹).map_add f.1 g.1)
  map_smul' c f := Subtype.ext ((h1locConjShift p k Ω K M σ⁻¹).map_smul c f.1)

lemma lcConjHomInv_comp (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    (lcConjHomInv p k Ω K M σ N).comp (lcConjHom p k Ω K M σ N) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  show (h1locConjShift p k Ω K M σ⁻¹) ((h1locConjShift p k Ω K M σ) f.1) = f.1
  exact h1locConjShift_inv_comp p k Ω K M σ f.1

lemma lcConjHom_comp_inv (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    (lcConjHom p k Ω K M σ N).comp (lcConjHomInv p k Ω K M σ N) = LinearMap.id := by
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  show (h1locConjShift p k Ω K M σ) ((h1locConjShift p k Ω K M σ⁻¹) g.1) = g.1
  exact h1locConjShift_comp_inv p k Ω K M σ g.1

/-- The conjugation shift is a linear equivalence of the locally constant cocycle modules. -/
noncomputable def lcConjEquiv (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    ↥(lcCocycles p k Ω K M N) ≃ₗ[ZMod p] ↥(lcCocycles p k Ω K M (conjSubSub σ N)) :=
  LinearEquiv.ofBijective (lcConjHom p k Ω K M σ N) ⟨by
    intro f g hfg
    have h := congrArg (lcConjHomInv p k Ω K M σ N) hfg
    simpa only [← LinearMap.comp_apply, lcConjHomInv_comp, LinearMap.id_apply] using h
  , by
    intro g
    refine ⟨lcConjHomInv p k Ω K M σ N g, ?_⟩
    apply Subtype.ext
    show (h1locConjShift p k Ω K M σ) ((h1locConjShift p k Ω K M σ⁻¹) g.1) = g.1
    exact h1locConjShift_comp_inv p k Ω K M σ g.1⟩

@[simp] lemma lcConjEquiv_apply (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω))
    (f : ↥(lcCocycles p k Ω K M N)) :
    lcConjEquiv p k Ω K M σ N f = lcConjHom p k Ω K M σ N f := rfl

@[simp] lemma lcConjEquiv_symm_apply (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω))
    (g : ↥(lcCocycles p k Ω K M (conjSubSub σ N))) :
    (lcConjEquiv p k Ω K M σ N).symm g = lcConjHomInv p k Ω K M σ N g := by
  apply (lcConjEquiv p k Ω K M σ N).injective
  rw [LinearEquiv.apply_symm_apply, lcConjEquiv_apply]
  exact (LinearMap.congr_fun (lcConjHom_comp_inv p k Ω K M σ N) g).symm

/-- The conjugation shift carries the coboundary submodule of `N` onto that of `σ N σ⁻¹`. -/
lemma map_cobQ_lcConjEquiv (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    (cobQ p k Ω K M N).map (lcConjEquiv p k Ω K M σ N : ↥(lcCocycles p k Ω K M N) →ₗ[ZMod p]
      ↥(lcCocycles p k Ω K M (conjSubSub σ N))) = cobQ p k Ω K M (conjSubSub σ N) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (lcConjEquiv p k Ω K M σ N y).1 ∈ coboundaries p k Ω K M (conjSubSub σ N)
    rw [lcConjEquiv_apply]
    exact h1locConjShift_mem_coboundaries_conj p k Ω K M σ N (f := y.1) hy
  · intro hx
    refine ⟨(lcConjEquiv p k Ω K M σ N).symm x, ?_, (lcConjEquiv p k Ω K M σ N).apply_symm_apply x⟩
    show ((lcConjEquiv p k Ω K M σ N).symm x).1 ∈ coboundaries p k Ω K M N
    have h1 : ((lcConjEquiv p k Ω K M σ N).symm x).1 = h1locConjShift p k Ω K M σ⁻¹ x.1 := by
      rw [lcConjEquiv_symm_apply]; rfl
    rw [h1]
    have h := h1locConjShift_mem_coboundaries_conj p k Ω K M σ⁻¹ (conjSubSub σ N)
      (f := x.1) hx
    rwa [conjSubSub_conjSubSub_inv] at h

/-- **The transport of the local `H¹` to a conjugate subgroup.** -/
noncomputable def h1locConjEquiv (σ : Ω ≃ₐ[k] Ω) (N : Subgroup (Ω ≃ₐ[k] Ω)) :
    H1loc p k Ω K M N ≃ₗ[ZMod p] H1loc p k Ω K M (conjSubSub σ N) :=
  Submodule.Quotient.equiv (cobQ p k Ω K M N) (cobQ p k Ω K M (conjSubSub σ N))
    (lcConjEquiv p k Ω K M σ N) (map_cobQ_lcConjEquiv p k Ω K M σ N)

/-- **The transport, in the form used when the conjugate subgroup is presented by an equality.** -/
theorem h1locConjEquiv_of_eq {N N' : Subgroup (Ω ≃ₐ[k] Ω)} (σ : Ω ≃ₐ[k] Ω)
    (h : conjSubSub σ N = N') :
    Nonempty (H1loc p k Ω K M N ≃ₗ[ZMod p] H1loc p k Ω K M N') :=
  ⟨cast (by rw [h]) (h1locConjEquiv p k Ω K M σ N)⟩

/-- **The local `H¹`'s at conjugate places are isomorphic.** -/
theorem h1loc_conjEquiv_nonempty {A B : ValuationSubring Ω}
    (h : SSGRoute.IsConjPlace k A B) :
    Nonempty (H1loc p k Ω K M (SSGRoute.decomp k A) ≃ₗ[ZMod p]
      H1loc p k Ω K M (SSGRoute.decomp k B)) := by
  obtain ⟨σ, hσ⟩ := h
  refine h1locConjEquiv_of_eq (N := SSGRoute.decomp k A) (N' := SSGRoute.decomp k B)
    p k Ω K M σ ?_
  rw [← hσ, SSGRoute.decomp_conj]
  rfl

/-- **The conjugacy transport at the representative of a place of `S`.**  The canonical
representative `(Quotient.mk (finPlaceConjSetoid k Ω) ⟨A,_⟩).out` of the conjugacy class of a place
`A ∈ S` is conjugate to `A`, and hence its local `H¹` is `𝔽_p`-linearly isomorphic to that of `A`
(`h1loc_conjEquiv_nonempty`).  This is the transport that identifies the prescribed data of the
relaxed product at the index of `A` with the `A`-component of `primalClasses`. -/
lemma isConjPlace_out_mk {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} {A : ValuationSubring Ω} (hA : A ∈ S) :
    SSGRoute.IsConjPlace k
      (Quotient.out (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩)).1 A :=
  Quotient.mk_out (s := finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩

/-- **The transport of the local `H¹` at a place of `S` to its index in `ptT`.** -/
theorem ptT_conjEquiv_nonempty {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    {A : ValuationSubring Ω} (hA : A ∈ S) :
    Nonempty (H1loc p k Ω K M (SSGRoute.decomp k
        (Quotient.out (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A, hSfin A hA⟩)).1) ≃ₗ[ZMod p]
      H1loc p k Ω K M (SSGRoute.decomp k A)) :=
  h1loc_conjEquiv_nonempty p k Ω K M (isConjPlace_out_mk (k := k) (Ω := Ω) hA)

/-- **The transport in the `ptX` form**: the local `H¹` space of the relaxed product at the index of
a place `A ∈ S` is that of `A` up to conjugacy.  This is the form in which the identification is
used when the prescribed data of the relaxation is compared with the `S`-components of
`primalClasses`. -/
theorem ptT_ptX_conjEquiv_nonempty {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    {A : ValuationSubring Ω} (hA : A ∈ S) :
    Nonempty (ptX p k Ω K M C (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω)
        ⟨A, hSfin A hA⟩)) ≃ₗ[ZMod p] H1loc p k Ω K M (SSGRoute.decomp k A)) :=
  ptT_conjEquiv_nonempty (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (S := S) (C := C) hA

/-- **The chosen conjugacy transport** from the local `H¹` at the index of a place `A ∈ S` in the
relaxed product to the local `H¹` of `A` itself: the conjugacy transport `h1loc_conjEquiv_nonempty`
along `isConjPlace_out_mk`, *chosen* once and for all (and stated at the *raw* index
`Sum.inl (mk A)`; see the session-9 note in the module docstring on why the `ptTIdxInl`-form of the
same statement is expensive to elaborate). -/
noncomputable def ptXConjEquiv {S : Finset (ValuationSubring Ω)}
    {hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A} (C : Finset (Ω ≃ₐ[k] Ω))
    (A : {A : ValuationSubring Ω // A ∈ S}) :
    ptX p k Ω K M C (Sum.inl (Quotient.mk (finPlaceConjSetoid k Ω) ⟨A.1, hSfin A.1 A.2⟩)) ≃ₗ[ZMod p]
      H1loc p k Ω K M (SSGRoute.decomp k A.1) :=
  Classical.choice (ptT_ptX_conjEquiv_nonempty (p := p) (k := k) (Ω := Ω) (K := K) (M := M)
    (S := S) (C := C) A.2)



end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

theorem pt_counting_identity_h1 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') :
    _root_.Work.SSGRoute.PT.CountingIdentity p k Ω K N hKN T M S C := by
  -- See the module docstring: the proof is steps 1–5 of the route, and the *only* missing input is
  -- step 3, the exactness `W^⊥ ⊆ V` (nodes E9 + E8 of `SSGRoute/DESIGN_PT.md`, equivalently the
  -- filed node `Work.SSGRoute.pt_selmer_relaxed`).  Given it, the ticket is
  --   1. the perfect product pairing `β` (`PT.exists_pairing_on_H1loc` + `PT.productFormFun`,
  --      with the local clauses supplied by `local_tate_duality_archimedean` at `C` and by E7 at `S`);
  --   2. `V ⊆ W^⊥` (`PT.pt_orthogonality_of_realizable`, proved);
  --   3. `W^⊥ ⊆ V` (the missing exactness, `PT.mem_primalClassSet_iff` reads it off the realizing
  --      cocycle);
  --   4. the counting step `PT.natCard_annihilator_mul` + `PT.natCard_primalClassSet` +
  --      `PT.natCard_dualClassSet`;
  --   5. finiteness of `P` and `P'`: `finite_primalClasses_pt` applied at `M` and at
  --      `DualMod p (M ⊗ T)` (whose `Finite` instance comes from `hT` via
  --      `Work.SSGRoute.finite_of_finrank_eq_one`).
  --
  -- Session 27: the node is RE-POINTED to `G1⁺` (`canonical_localPairing_reciprocity_converse`,
  -- the lead design of `_lead_design/ssg_pt_design_1002/DESIGN.md` §4).  Extract `pair`, the
  -- pairing clauses (1)-(4), the reciprocity clause (7) and the converse clause (8) from `G1⁺`;
  -- `PT.hconv_of_converse` (node-free, `PT/converseRepr.lean`) turns clause (8) into the
  -- class-level `hconv`; then the proved `countingIdentity_of_reciprocity_and_converse` closes.
  haveI hTfin : Finite T := finite_of_isCyclotomicDual p k Ω K T ζ hT
  obtain ⟨pair, hmain, hrec7, hconv8full⟩ :=
    canonical_localPairing_reciprocity_converse p k Ω K ζ hζ hζK T hT
  have hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) H := by
    intro H hH
    obtain ⟨c1, c2, c3, c4, c5⟩ := hmain M H hH
    exact ⟨c1, c2, c3, c4, c5.1⟩
  have hrec : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
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
      ∑ A ∈ S', pair M (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', pair M (Subgroup.zpowers c) a b = 0 :=
    hrec7 M
  have hconv8 : ConverseRepr p k Ω K N hKN T M S C (pair M) :=
    fun α β hα hβ hsum =>
      hconv8full M N hKN S hSfin hSdisj hSram C hCinv hC hCdisj α β hα hβ hsum
  exact countingIdentity_of_reciprocity_and_converse (p := p) (k := k) (Ω := Ω) (K := K)
    (N := N) (hKN := hKN) (T := T) (M := M) (S := S) (C := C)
    (hSfin := hSfin) (hSdisj := hSdisj) (hSram := hSram) (hCinv := hCinv) (hC := hC)
    (hCdisj := hCdisj) (pair := pair M) (hloc := hloc) (hrec := hrec)
    (hconv := hconv_of_converse (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
      (T := T) (M := M) (S := S) (C := C) (pair := pair M) (hloc := hloc) (hSfin := hSfin)
      (hCinv := hCinv) (hconv8 := hconv8))
    (hfinP := finite_primalClasses_pt (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (S := S)
      (C := C) hSfin hCinv)
    (hfinQ := finite_primalClasses_dual_pt (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (T := T)
      (M := M) (S := S) (C := C) hT hSfin hCinv)

end Work.SSGRoute.PT
