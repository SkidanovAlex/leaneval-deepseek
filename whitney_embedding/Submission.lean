import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.OneDim.exists_embedding_euclidean_two
import Submission.Work.Embedding.exists_embedding_of_components_general
import Submission.Work.Whitney.EndgameSigned
import Submission.Work.Whitney.hasInsertionSigned
import Submission.Work.Noncompact.Compression
import Submission.Work.Drive.hasCompression_drive
import Submission.Work.Drive.hasPushSignedSmooth_milnor
import Submission.Work.Drive.exists_embedding_of_compact_connected_smooth
import Submission.Work.Drive.N2.exists_isMorseDistinct
import Submission.Work.Drive.N2.hasLevelFlow_of_noCritical
import Submission.Work.Drive.N2.morseLemma2
import Submission.Work.Drive.N2.embedding_of_morse_movie
-- Development towards Whitney's strong embedding theorem (see the module docs below).
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Projection.exists_countable_chart_cover
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.dimH_badImmCharts
import Submission.Work.Projection.dimH_badInjCharts
import Submission.Work.Projection.exists_good_direction
import Submission.Work.Projection.compact_embedding
import Submission.Work.Projection.immersion
-- Generalisation of the projection machinery to an arbitrary (boundaryless) model with corners.
import Submission.Work.Projection.GeneralDefs
import Submission.Work.Projection.dimH_badImmCharts_general
import Submission.Work.Projection.dimH_badInjCharts_general
import Submission.Work.Projection.exists_countable_chart_cover_general
import Submission.Work.Projection.mfderiv_extChartAt_decomp
import Submission.Work.Projection.exists_good_direction_general
import Submission.Work.Projection.exists_embedding_euclidean_of_compact_general
-- Non-compact foundations and isotopy vocabulary.
import Submission.Work.Noncompact.exists_proper_contMDiff
import Submission.Work.Noncompact.exists_proper_contMDiff_nonneg
-- The weak Whitney embedding theorem for second countable manifolds (non-compact case).
import Submission.Work.Projection.exists_good_direction_ne_zero
import Submission.Work.Noncompact.parity_sum
import Submission.Work.Noncompact.reduce_steps_on
import Submission.Work.Noncompact.exists_local_map
import Submission.Work.Noncompact.exists_pack_data
import Submission.Work.Noncompact.exists_bounded_injective_map
import Submission.Work.Noncompact.weak_whitney
import Submission.Work.Isotopy.Basic
import Submission.Work.Isotopy.Linear
import Submission.Work.Isotopy.Smooth
import Submission.Work.Isotopy.exists_smoothAmbientIsotopy_extending
import Submission.Work.Embedding.exists_smooth_retraction
import Submission.Work.Embedding.exists_isolated_double_point
import Submission.Work.Embedding.finite_double_points_of_transverse
import Submission.Work.Embedding.Proper
import Submission.Work.Embedding.exists_unique_closest_point
import Submission.Work.Projection.exists_projection_transverse
import Submission.Work.Embedding.finite_of_isClosed_forall_isolated
-- The Whitney self-intersection chapter: the local model, the sign of a double point, and the
-- "glue in one double point" move.
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.model_immersion
import Submission.Work.Whitney.model_double_point
import Submission.Work.Whitney.model_transverse
import Submission.Work.Whitney.mirror_det_neg
import Submission.Work.Whitney.exists_tubular_param
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.doubleDet_swap
import Submission.Work.Whitney.doubleDet_ne_zero_iff
import Submission.Work.Whitney.isEmbedding_of_injective_of_compactSpace
import Submission.Work.Whitney.isEmbedding_of_isProperMap_of_doubleSet_eq_empty
import Submission.Work.Whitney.exists_addDoublePoint
import Submission.Work.Whitney.exists_bump_model_pair_smooth
import Submission.Work.Whitney.exists_reflection_det_neg
import Submission.Work.Whitney.DoubleDetC
import Submission.Work.Whitney.exists_tubular_param_general_smooth
import Submission.Work.Whitney.exists_addDoublePoint_smooth
import Submission.Work.Whitney.exists_addDoublePoint_both_signs
import Submission.Work.Whitney.doubleDetC_untouched
import Submission.Work.Whitney.exists_addDoublePoint_general_chart
import Submission.Work.Whitney.PairDet
import Submission.Work.Whitney.exists_addDoublePoint_general_chart_located
import Submission.Work.Whitney.exists_addDoublePoint_chart_like
import Submission.Work.Whitney.exists_clean_point_and_chart
import Submission.Work.Whitney.OrientedAtlas
import Submission.Work.Whitney.oppositeSign_iff
import Submission.Work.Whitney.exists_clean_ball
-- SESSION 12: this import was COMMENTED OUT because the file transitively imports
-- `Submission/Work/Whitney/collar_push_local.lean`, which currently contains a `sorry` from
-- another agent's in-progress work, and *nothing* in the proof chain needs
-- `Work.Whitney.cancel_double_points_in_chart` (it is recorded in the module docstring as
-- available and as the model of the cut-and-paste, but the endgame interfaces are what is used).
-- Restore it once that chain compiles.
-- import Submission.Work.Whitney.cancel_double_points_in_chart
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_chart_like
-- NOTE (session 8): `cancel_double_points_oriented` is temporarily NOT imported here: its dependency
-- chain reaches `local_push_cut_nontransverse_full.lean`, which is being edited right now, so the
-- import would make this file fail to elaborate.  The module is intact and importable by anyone who
-- needs it; nothing in this development depends on it (the `HasCancellation` interface in
-- `Submission/Work/Whitney/reduce_double_points_abstract.lean` records everything needed from it).
-- RESTORE once the push chain compiles again.
-- import Submission.Work.Whitney.cancel_double_points_oriented
import Submission.Work.Whitney.oppositeSign_iff_doubleDetC
import Submission.Work.Whitney.ncard_doubleSet_cancel
import Submission.Work.Whitney.exists_chart_globally_smooth_symm
import Submission.Work.Whitney.exists_tubular_data_smooth
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_located
import Submission.Work.Whitney.SignCompare
import Submission.Work.Whitney.CleanRegion
import Submission.Work.Whitney.clean_data_shrink
import Submission.Work.Whitney.clean_region_of_arcs
import Submission.Work.Whitney.insert_double_point_oriented
import Submission.Work.Whitney.EndgameAux
import Submission.Work.Whitney.fderiv_transition_det_ne_zero
-- SESSION 8: the interfaces and the assembly of the endgame for the compact case.
import Submission.Work.Whitney.InsertedDoublePoint
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.endgame_abstract
import Submission.Work.Whitney.projection_transverse_immersion
import Submission.Work.Whitney.pairDet_ne_zero_iff
import Submission.Work.Whitney.assembly_compact
import Submission.Work.Whitney.cancellation_of_pushData
import Submission.Work.Whitney.hasReduction
import Submission.Work.Whitney.assembly_compact_full
import Submission.Work.Embedding.exists_embedding_of_components
-- SESSION 13: the *countable* component gluing: for an arbitrary (possibly disconnected, possibly
-- non-compact) manifold, embeddings of its connected components (each placed in a disjoint ball)
-- glue to a global embedding.  This reduces the target to the connected cases.
import Submission.Work.Embedding.exists_embedding_of_components_general
-- SESSION 9: the general position input and the atlas restriction (both proved).
import Submission.Work.Whitney.exists_simple_transverse_immersion
import Submission.Work.Whitney.exists_isSmoothOrientedAtlas_restrict
import Submission.Work.Whitney.assembly_compact_orientable
-- SESSION 9: the bigon-framing framework for the non-orientable case (definitions).
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.exists_isArcChain
import Submission.Work.Whitney.exists_oppositeType_of_insertion
import Submission.Work.Whitney.posTransitionAt_of_isArcChain
-- SESSION 10: the *atlas-free* endgame.  The push construction in this workspace never uses the
-- oriented atlas or the sign hypothesis (see the docstring of `ambient_push_data_full`), so the
-- whole endgame can be run without any orientation input; this covers the non-orientable case
-- without the framing machinery.
import Submission.Work.Whitney.EndgameNF
import Submission.Work.Whitney.hasInsertionNF
-- NOTE (SESSION 13): `Submission/Work/Whitney/hasPushNF_of_localPush.lean` is temporarily broken
-- because another agent removed the definition `Work.Whitney.LocalPushNF` from `EndgameNF.lean`
-- (the file now only carries `Work.Whitney.LocalPushNTrans`).  Nothing in this development needs
-- it: the compact branch is driven by `Work.Whitney.hasPushNFT_of_localPushNTrans`
-- (`EndgameNFTrans`), which takes `LocalPushNTrans` as its input.  Restore this import if the
-- definition reappears (or after the file is re-stated in terms of `LocalPushNTrans`).
-- import Submission.Work.Whitney.hasPushNF_of_localPush
-- SESSION 12: the `Trans`-variant of the endgame (transversality-carrying push/cancellation
-- interfaces) plus the extraction of intrinsic transversality from the `TransDP'` certificate;
-- the compact branch `exists_embedding_of_compact_NFT` is driven by
-- `hasPushNFT_of_localPushNTrans` (from the local push at a *transverse* double point).
import Submission.Work.Whitney.EndgameNFTrans
-- SESSION 14: the compact case of the target, isolated as a single lemma conditional on the
-- local Whitney push (`Work.Whitney.LocalPushNTrans`): with the push in hand, the compact branch
-- of `whitney_embedding` is a one-line application of
-- `Work.Whitney.exists_embedding_of_compact_of_localPush`.
import Submission.Work.Whitney.compact_of_localPush
import Submission.Work.Whitney.PushSigned
import Submission.Work.Whitney.CancelSigned
import Submission.Work.Whitney.InsertSigned
import Submission.Work.Whitney.hasInsertionSigned
-- SESSION 15: the *signed* endgame packaging: the reduction interface from the signed insertion and
-- the signed cancellation, and the compact/compact-connected branches of the target in signed form.
import Submission.Work.Whitney.EndgameSigned
-- SESSION 12: the general position input of the compact case, weakened to `1 ≤ n` (this is what
-- the `n = 2` branch would need; the `3 ≤ n` of the original statement is unused).
import Submission.Work.Whitney.exists_simple_transverse_immersion_of_ge_one
-- SESSION 12: the structured form of the proper weak Whitney embedding, used to build a *proper*
-- immersion into `ℝ^{2n}` (see the plan for the non-compact case).
import Submission.Work.Noncompact.exists_structured_proper_embedding_weak
import Submission.Work.Projection.exists_projection_transverse_avoiding
import Submission.Work.Noncompact.proper_immersion_transverse
import Submission.Work.Noncompact.finite_preimages_and_discrete_doubleSet
-- SESSION 9: the `n = 1` case of the target (classification of 1-manifolds), now sorry-free.
import Submission.Work.OneDim.exists_embedding_euclidean_two
-- SESSION 13: the non-compact case of the target, reduced to the *compression* of the domain
-- (`Work.Noncompact.HasCompression`): a self-embedding of `M` whose image's closure omits one
-- preimage of every double point of a proper general-position immersion `h`; the modified map
-- `h ∘ φ` is then an embedding.  The geometric input (tubes to infinity, the shrink) is delegated
-- to `Work.Noncompact.hasCompression`; the design is in
-- `Submission/Work/Noncompact/NOTES_compression.md`.
import Submission.Work.Noncompact.Compression

/-!
## Status of this formalisation of Whitney's strong embedding theorem

Target (theorem `whitney_embedding` below): every smooth `n`-manifold (`n ≥ 1`, Hausdorff,
second countable) admits a smooth embedding `e : M → ℝ^{2n}` which is an immersion
(`mfderiv e x` injective for every `x`).

### What is already proved

**The projection argument (model `𝓡 n`).**

* `Work.Projection.exists_good_direction` — the analytic core of Whitney's projection argument.
  For a smooth embedding `f : M → ℝ^{k+1}` of a smooth `n`-manifold with `2n < k`, plus a
  countable cover of `M` by chart sources, there is a linear projection
  `projVec u : ℝ^{k+1} → ℝ^k` (with kernel spanned by `(u,1)`) such that `projVec u ∘ f` is
  again injective with injective derivative.  The set of *bad* directions is shown to be a
  countable union of images of explicit `C¹` maps from open subsets of `ℝ^{2n}`, hence has
  Hausdorff dimension `≤ 2n < k`.
* `Work.Projection.exists_embedding_euclidean_of_compact` — the **weak Whitney embedding
  theorem**, compact case: a compact smooth `n`-manifold embeds in `ℝ^{2n+1}` with injective
  derivative.
* `Work.Projection.exists_immersion_euclidean_of_compact` — a compact smooth `n`-manifold
  immerses in `ℝ^{2n}` (the immersion-bad set has Hausdorff dimension `≤ 2n-1`, a *sharp* bound
  proved via scale invariance, file `dimH_badImmCharts_sharp.lean`).
* Ancillary: `dimH_badImmCharts`, `dimH_badInjCharts`, `dimH_badImmCharts_sharp`,
  `dimH_image_le_of_contDiffOn`, `exists_countable_chart_cover`, `mfderiv_chartAt_decomp`.

**Generalisation to an arbitrary boundaryless model with corners.**  The chartwise bad-direction
sets are redefined using the *extended* charts `extChartAt I p : M → E` (so that the domains of the
parametrising maps are subsets of `E × E`), in `Submission/Work/Projection/GeneralDefs.lean`:
`chartRepI`, `badImmChartsI`, `badInjChartsI`, `immParamI`, `immDomI`, `injParamI`, `injDomI`, plus
the containments `badImmChartsI_subset`, `badInjChartsI_subset` and the simplification
`fderivWithin_range_I` (used when `I` is boundaryless).  On top of these:
`Work.Projection.dimH_badImmCharts_general`, `Work.Projection.dimH_badInjCharts_general` (both
`≤ 2 * finrank ℝ E`), `Work.Projection.mfderiv_extChartAt_decomp` (the chain-rule decomposition of
`mfderiv` through an extended chart) and `Work.Projection.exists_countable_chart_cover_general`.
*Caution*: a chart representation is honest (`fderiv` is the true derivative) only at *interior*
points of the manifold; the hypothesis `[I.Boundaryless]` is used throughout this branch.

**Non-compact foundations.**

* `Work.Noncompact.exists_proper_contMDiff` — a σ-compact smooth manifold admits a proper smooth
  function `M → ℝ` (built from a `CompactExhaustion` and a subordinate smooth partition of unity).
  Mathlib's `CompactExhaustion` (`Mathlib/Topology/Compactness/SigmaCompact.lean`) already provides
  the nested exhaustion `K n ⊆ interior (K (n+1))` used everywhere below, so no separate lemma is
  needed for that.
* `Work.Isotopy.Basic` — the vocabulary of isotopy theory: `Work.Isotopy.AmbientIsotopy E` (a
  homeomorphism of `E × ℝ` over `ℝ` fixing `E × {0}`, with `apply`, `comp`, `IsSupportedOn`),
  `Work.Isotopy.Isotopy X E` (a continuous family of embeddings), the action
  `AmbientIsotopy.isotopy` of an ambient isotopy on embeddings, and `Work.Isotopy.Isotopic`.
* `Work.Embedding.isClosedEmbedding_of_isProperMap_injective`,
  `Work.Embedding.isEmbedding_of_isProperMap_injective` — a proper injective map is a closed
  embedding.  (For non-compact `M` the target `IsEmbedding` will be obtained by *properness*.)
* `Work.Isotopy.AmbientIsotopy.translation`, `Work.Isotopy.AmbientIsotopy.dilation` — the
  translation and dilation ambient isotopies of a normed space (with
  `Work.Isotopy.AmbientIsotopy.dilationScale`, a convex combination of `1` and `ε` built from
  `Real.smoothTransition` so that every time slice is invertible).
* `Work.Isotopy.SmoothAmbientIsotopy` — smooth ambient isotopies of `ℝ^N`, with the derived time
  slice smoothness `SmoothAmbientIsotopy.contMDiff_apply`, composition, and the smooth versions
  `SmoothAmbientIsotopy.translation`, `SmoothAmbientIsotopy.dilation` of the two basic moves.

**General weak Whitney theorem (compact, boundaryless model).**
`Work.Projection.exists_embedding_euclidean_of_compact_general` — a compact smooth manifold
modelled on an arbitrary finite dimensional real vector space `E` with a boundaryless model with
corners `I` embeds smoothly and immersively in `ℝ^{2n+1}`, `n = finrank ℝ E`.  Its proof goes
through `Work.Projection.exists_good_direction_general` (which contains the general versions
`injective_projVec_comp_general` and `injective_projVec_comp_mfderiv_general` of the two
injectivity lemmas).

### The weak Whitney embedding theorem for second countable manifolds (proved in `Work.Noncompact`)

* `Work.Noncompact.exists_proper_embedding_euclidean_weak` and
  `Work.Noncompact.exists_embedding_euclidean_weak` — every Hausdorff, second countable smooth
  `n`-manifold admits a *proper* smooth embedding into `ℝ^{2n+1}` which is an immersion (for compact
  `M` this is the classical weak Whitney theorem, and it is now proved for *all* second countable
  `M`).  Together with `Work.Embedding.isEmbedding_of_isProperMap_injective` this gives the
  `IsEmbedding` conclusion.
* `Work.Noncompact.exists_immersion_euclidean` — the **Whitney immersion theorem**: every such `M`
  immerses into `ℝ^{2n}` (one projection step further, using the sharp bound
  `dimH badImmCharts ≤ 2n - 1` from `Work.Projection.exists_good_direction_immersion`).

The non-compact case is handled by the **parity (band) sum**:

* `Work.Noncompact.exists_proper_contMDiff_nonneg` — a nonnegative proper smooth function `f`
  (the construction of `Work.Noncompact.exists_proper_contMDiff`, whose witness is a locally finite
  sum of nonnegative terms, hence nonnegative);
* `Work.Noncompact.exists_local_map` — for every compact `K ⊆ M` there is a smooth map
  `M → ℝ^{2n+1+m}` which is injective and immersive on `K` (finitely many charts covering `K`,
  a smooth partition of unity subordinate to that finite cover together with `Kᶜ`, and Mathlib's
  `SmoothBumpCovering.embeddingPiTangent` pattern);
* `Work.Noncompact.reduce_steps_on` — the projection argument *localised* to `K`, lowering
  `ℝ^{2n+1+m}` to `ℝ^{2n+1}` (the bad direction sets have Hausdorff dimension `≤ 2n < k` without any
  global injectivity hypothesis);
* `Work.Noncompact.band`, `bandSum`, `exists_band_bump`, `locallyFinite_band`, `band_disjoint` —
  the bands `f⁻¹'(i-1/4, i+5/4)`, which are locally finite and disjoint for indices differing by at
  least `2`, with bump functions equal to `1` on `f⁻¹'[i-1/8, i+9/8]` and support exactly
  `f⁻¹'(i-1/4, i+5/4)`;
* `Work.Noncompact.exists_injective_immersion_of_local_maps` — the **parity sum**: given smooth
  `φ i` injective and immersive on the core band `f⁻¹'[i, i+1]`,
  `Φ x = (∑ᶠ j, ρ_{2j+1}(x) • φ_{2j+1}(x), ∑ᶠ j, ρ_{2j}(x) • φ_{2j}(x), f x)`
  is an injective immersion of `M` (at a point of the band `i` only the summand `i` survives in the
  sum of its parity, by the disjointness of bands whose indices differ by `≥ 2`), transported into
  `ℝ^{2n+1+(2n+2)}`;
* `Work.Noncompact.exists_bounded_injective_map` (`y ↦ y/√(1+‖y‖²)`, injective with injective
  derivative and image in the unit ball), `Work.Noncompact.exists_pack_data` (the coordinate packing
  `P : ℝ^{2n+1} × ℝ → ℝ^{2n+2}` with `projVec u (P (z,t)) = z - t • u` and `P` injective) and
  `Work.Projection.exists_good_direction_ne_zero` (a good direction `u ≠ 0`) make the final
  projection *proper*: `‖projVec u (P (e x, f x))‖ ≥ f x ‖u‖ - 1`, so the preimage of a bounded set
  is contained in a compact sublevel set of the proper `f`.

### Remaining gap towards the target

**The step `2n+1 → 2n`** — this is now the only remaining gap (the weak theorem, i.e. the
`2n+1` statement, is settled for every second countable `M`).

The projection argument cannot be pushed below `2n+1`: the injectivity-bad set is the image of the
*chord map* `(x,y) ↦ extract (f x - f y)` from `M × M ∖ Δ` (dimension `2n`) into the
`(2n)`-dimensional space of directions, and the bad set is *open* for a self-transverse immersion
(e.g. the trefoil in `ℝ³`).  Closing this step requires Whitney's self-intersection cancellation
(Ann. of Math. 1944).

### The new chapter `Work.Whitney` (Whitney's self-intersection machinery)

* `Submission/Work/Whitney/LocalModel.lean` — Whitney's local model
  `model n x = (fun i ↦ x i - (if i = 0 then 2 * x i / uu n x else 0),
  fun i ↦ if i = 0 then 1 / uu n x else x 0 * x i / uu n x)` with `uu n x = ∏ i, (1 + x i ^ 2)`:
  a map `ℝⁿ → ℝⁿ × ℝⁿ` with exactly one (transverse) double point at `±e₀`, "approximately" the
  linear inclusion `inclModel n x = (x, 0)` at infinity; `mirrorFun n` negates the first coordinate
  of the *second* block, fixes `inclModel`, has determinant `-1`, and hence flips the sign of the
  model's double point.
* `Work.Whitney.model_immersion`, `model_double_point`, `model_transverse` — the model is a smooth
  immersion, its double point set is exactly `{±e₀}`, and its double point is transverse
  (`LinearMap.det` of the "two sheets" map `(u,v) ↦ D model e₀ u + D model (-e₀) v` is nonzero).
* `Work.Whitney.mirror_det_neg` — mirroring flips the sign of that determinant.
* `Work.Whitney.exists_tubular_param` — **tubular parametrisation of a chart representation**: for
  a smooth immersion `φ : ℝⁿ → ℝⁿ × ℝⁿ` there is a smooth `H`, injective and immersive on a ball
  around `0`, with `H (u, 0) = φ u`.  This is what makes the local model *glueable*: the glued map
  is `y ↦ H (β ((chartAt x) y))`.
* `Submission/Work/Whitney/DoublePoint.lean` — the sign framework: `doubleSet f` (the set of
  ordered double points `(p, q)` of a map) and `doubleDet f p q u v`, the **signed determinant** of
  a double point: the determinant of the "two sheets" map read through the block identification
  `Work.Projection.pairEquiv`, computed in the charts at `p` and `q`.
* `Work.Whitney.exists_addDoublePoint` — **proved**, but *with the analytic order*: a colleague
  proved it for `ContDiff ℝ ⊤ β` / `ContDiff ℝ ⊤ H`, i.e. for *analytic* models, which cannot exist
  (see the third lesson below).  **The usable statement must be restated with `ContDiff ℝ ∞`**, and
  the restated proof has to be redone; only the double-point bookkeeping (the case analysis in the
  proof) is reusable.
* in flight: `exists_bump_model_pair_smooth` (the smooth cut-off model in either sign, glued to
  `inclModel` outside a ball; the previous `exists_bump_model_pair` with `ContDiff ℝ ⊤` was declared
  false by its prover and removed — its helper files under `Submission/Work/Whitney/BumpModel/`
  remain and are reusable), and the older `exists_bump_model_pair` (the cut-off model in either sign, glued to `inclModel`
  outside a ball), `doubleDet_swap` (`(-1)^n` under swapping the sheets), `doubleDet_ne_zero_iff`
  (vanishing of `doubleDet` = failure of transversality), `exists_addDoublePoint` (**gluing one
  double point into an immersion**, the "introduce a double point" move of Whitney's proof).

### Plan for the remaining gap (refined in session 5)

The step `2n+1 → 2n` is the only gap.  Everything below is the *current* design; it supersedes the
older plan recorded in earlier revisions of this docstring.

**Pieces that are in place.**

* *(A) Cut-off model, both signs.*  `Work.Whitney.exists_bump_model_pair_smooth`: for every
  `δ > 0`, `R₀ > 0` there are smooth (`C^∞`!) immersions `β⁺, β⁻ : ℝⁿ → ℝⁿ × ℝⁿ`, equal to
  `inclModel n` outside a ball of radius `R ≤ R₀`, `δ`-close to it, with one transverse double
  point at the *same* pair `a ≠ b`, second block nonzero on the ball, and opposite determinant
  signs.
* *(B) The gluing move.*  `Work.Whitney.exists_addDoublePoint` (analytic-order version, existing)
  and **`Work.Whitney.exists_addDoublePoint_smooth`** (the usable `ContDiff ℝ ∞` version): gluing a
  cut-off model into a chart representation of a smooth immersion adds exactly one transverse
  double point.
* *(C) Insertion with either sign.*  `Work.Whitney.doubleDetC f c p q` (in
  `Submission/Work/Whitney/DoubleDetC.lean`) is the signed determinant of a double point computed
  in **one** chart `c` — the form in which two co-located double points have directly comparable
  signs.  `Work.Whitney.exists_addDoublePoint_both_signs` supplies two glued maps `fp`, `fm` with
  the *same* inserted double point `(p', q')` and `doubleDetC fm c p' q' = - doubleDetC fp c p' q'`.
  The mechanism is `Work.Whitney.exists_reflection_det_neg`: an isometric linear `S` with
  `S (u,0) = (u,0)`, `S z = z`, `det S = -1`; replacing the tubular parametrisation `H` by `H ∘ S`
  preserves every hypothesis of the gluing (`S` is an isometry fixing the axis, and `S z = z` keeps
  the inserted image and the evaluation point of `DH` fixed) but multiplies the inserted
  determinant by `det S = -1`.

*(B') An obstruction to *applying* the gluing move, and its fix (found in session 5).*  The
gluing lemmas `Work.Whitney.exists_addDoublePoint` / `..._smooth` carry the hypothesis
`hsrc : ∀ y : M, ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) y‖ < 3 * R → y ∈ (chartAt ... x).source`.
This is **not provable** for `chartAt x`: `ChartedSpace` supplies only `atlas`, `chartAt`,
`mem_chart_source` and `chart_mem_atlas`, so the values of the chart function outside its source
("junk") are completely unconstrained, and nothing forces them to be large.  A gluing move can
therefore never be applied as stated.  The fix is to use a chart *with good junk*: for
`c₀ := chartAt (EuclideanSpace ℝ (Fin n)) x` and a fixed vector `v ≠ 0`, define

  `c.toFun y = if y ∈ c₀.source then c₀ y else (4 * R) • v`,  `c.source = c₀.source`,
  `c.target = c₀.target`, `c.invFun = c₀.invFun`.

Then `c` is an `OpenPartialHomeomorph` (the axioms only constrain `toFun` on the source), `c = c₀` on
`c.source`, `c.symm = c₀.symm` as functions, and `hsrc` holds for `c` by construction (`y ∉ c.source`
forces `‖c y‖ = 4R ≥ 3R`).  Two consequences: (i) the gluing lemma must be restated with an
arbitrary `c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))` in place of `chartAt ... x`,
carrying `x ∈ c.source` and `∀ u, c.symm u = (chartAt ... x).symm u` (the latter so that
`f ∘ c.symm` is the honest chart representation and `ContMDiffAt c y` follows from
`ContMDiffAt (chartAt ... x) y` by eventual equality); the existing proof should transplant verbatim
since it only uses the `OpenPartialHomeomorph` API plus the smoothness of the chart at `x`.
Delegating that restatement is the first task of the next session.  (ii) All uses of
`doubleDetC`/`doubleDet` in the endgame switch from `chartAt ... x` to this `c`.


**The endgame for compact `M`, `n ≥ 3`: insert + cancel, one double point at a time.**

Let `f : M → ℝ^{2n}` be a self-transverse immersion (`Work.Projection.exists_projection_transverse`
applied to `Work.Noncompact.exists_embedding_euclidean_weak`), with finitely many double points
(`Work.Embedding.finite_double_points_of_transverse`).  If `d = #doubleSet f / 2 ≥ 1` we reduce `d`
by one as follows.

1. Pick a double point `P = (p₁,p₂)`, and a *clean* point `x ∈ M` (a point whose image is not a
   double-point image) which is close to both `p₁` and `p₂` in a common chart.  Such an `x` exists:
   the two sheets through `w = f p₁ = f p₂` are transverse, so each of them covers a neighbourhood
   of `w`; a point `x` with `f x` in that neighbourhood but `f x ≠ w` and `f x` not the image of any
   double point lies on both sheets' `f`-preimages, i.e. `x` is close to `p₁` **and** close to `p₂`
   in `M` (this uses that `f` is injective near `x`, resp. near `p₁` and `p₂`, so that a preimage of
   `f x` close to `p₂` has to be `x` itself).  Working in `c := chartAt x` we get
   `p₁, p₂ ∈ c.source` with `‖c pᵢ‖ ≥ 2R` for a small `R` (so the ball of radius `R` around `x`
   misses the four preimages and is clean), while `R` is also small enough for the separation
   `hsep` of the gluing move.  (The *ratio* `‖c p₁‖/‖c p₂‖` is not controlled and is not needed;
   only `p₁, p₂ ∈ c.source` and `‖c p₁‖, ‖c p₂‖ ≥ 2R` are used.  The estimates are then:
   `‖f y - f pᵢ‖ ≥ σR - O(R²)` for `‖c y‖ < R`, with `σ` the minimal singular value of `Df(x)`, so
   `η` can be chosen positive and small, and `δ`, `L` small enough that `L δ < η`.)

2. Apply `Work.Whitney.exists_addDoublePoint_both_signs` at `x`, obtaining `fp`, `fm` with
   `doubleSet f± = doubleSet f ∪ {(p',q'), (q',p')}` and opposite values
   `B± := doubleDetC f± c p' q'`.  The existing double point `P` is untouched by the gluing (its
   preimages are outside the modification ball and `f± = f` there), so
   `A := doubleDetC fp c p₁ p₂ = doubleDetC fm c p₁ p₂`.
3. Exactly one of `A * B⁺`, `A * B⁻` is negative (they are opposites and nonzero).  For that
   choice, `P` and `P'` are co-located in the chart `c` with *opposite* local signs, which is
   precisely the hypothesis of the Whitney cancellation.
4. Cancelling the pair lowers `d` by one.

Iterating until `d = 0` and concluding with
`Work.Whitney.isEmbedding_of_injective_of_compactSpace` finishes the compact case.  **No separate
"motion of a double point" lemma is needed** — the co-location is achieved by *choosing* `x` close
to a preimage of `P`, and the ambient isotopies of `Work.Isotopy.*` are not needed for this step.
(An earlier revision of this docstring planned a motion lemma; that plan is obsolete.)

**What is still missing: the cancellation (Whitney trick), `n ≥ 3`.**

The statement to prove is: *let `f : M → ℝ^{2n}` be a smooth immersion (`n ≥ 3`), `p₁,p₂,q₁,q₂ ∈ M`
with `f p₁ = f p₂`, `f q₁ = f q₂`, all four preimages in the source of one chart `c`, both double
points transverse, the chart region containing no other double-point preimage, and*
`doubleDetC f c p₁ p₂ * doubleDetC f c q₁ q₂ < 0`.  *Then there is a smooth immersion `f'` with*
`doubleSet f' = doubleSet f ∖ {(p₁,p₂),(p₂,p₁),(q₁,q₂),(q₂,q₁)}`, *equal to `f` outside a small set.*

The classical construction (Whitney 1944; Persson's thesis, Lemma 4.12 / 4.13 / Theorem 4.14):

* choose arcs `C₁ ∋ p₁,q₁` and `C₂ ∋ p₂,q₂` in the chart region, disjoint apart from the double
  points, so that the images `B₁ = f(C₁)`, `B₂ = f(C₂)` form a simple closed curve `B ⊆ f(M)`;
* find an embedded 2-disc `D ⊂ ℝ^{2n}` with `∂D = B` and `int D ∩ f(M) = ∅` — this is where
  `n ≥ 3` is used (`2 + n < 2n`, so a generic disc avoids the `n`-dimensional image);
* modify `f` (only!) on a neighbourhood of the arc `C₂`, by pushing that sheet across `D`, so that
  the new image of `C₂` no longer meets `B₁`.  This is *not* an ambient isotopy of the whole target
  (a global homeomorphism can never separate the two sheets); it is the composition of the chart
  representation with a diffeomorphism supported near `D`, and `f` is changed only on the preimage
  of that support.

*Geometry of the push, and what not to try (established in session 5).*

* A "fibre-preserving" push of the form `θ_t(p,v) = (p, v + t ψ(p))` in a tubular neighbourhood of
  the *fixed* sheet, with `ψ(p) = σ(‖s(p)‖)(-s(p) - w)` and `s` the graph function of the moved
  sheet, **cannot work**.  The requirement is `s + ψ ≠ 0`, i.e. `(id + ψ) ≠ 0` where `ψ` is a
  compactly supported perturbation of the identity: in coordinates `u = s(p)` near a crossing this
  reads `u = -ψ(u)`; equivalently `id + ψ` would be a compactly supported perturbation of the
  identity that is nowhere zero, which is impossible since such a map is proper of degree `1`
  (if `0` were outside its image, the degree would be `0`).  Concretely, along any path from a
  crossing point out to the boundary of the support the quantities `‖ψ‖` (decreasing to `0`) and
  `‖u‖` cross.
* Consequently the moved sheet must **not** stay a graph over the fixed one: the push has to be a
  genuine diffeomorphism (indeed an isotopy) of a tubular neighbourhood, which moves the sheet in
  its *own normal direction*.  Equivalently: `θ` is an ambient isotopy of `ℝ^{2n}` supported near
  `D`, and one applies it to the sheet through `C₂` only (writing `f' = f` outside a neighbourhood
  of `C₂` and `f' = θ ∘ f` on it).  A *global* ambient isotopy can never separate the two sheets
  (it is a homeomorphism, so it preserves the double point set), which is why the modification must
  be applied to one sheet only.
* The push direction is any `w(x) ∈ ν_x D` transverse to `T_x S_B ∩ ν_x D` (`x ∈ β`): the latter
  has dimension `n - 1` inside the `(2n-2)`-dimensional `ν_x D`, so such a direction exists as soon
  as `n ≥ 2`.  The sheet is pushed in the direction `w` far enough to cross `D` and the fixed sheet;
  because `int D ∩ f(M) = ∅` the sweep passes through free space and creates no new intersections.
* Note that `D` is (to first order) *tangent* to `S_A` along `α` with inward direction normal to
  `S_A`, and likewise tangent to `S_B` along `β`; this is forced by `int D ∩ (S_A ∪ S_B) = ∅` and
  `S_A ∩ D = α`, `S_B ∩ D = β`.

*The statement delegated for this step.*  `Work.Whitney.cancel_double_points`
(`Submission/Work/Whitney/cancel_double_points.lean`) states the local heart cleanly: for `n ≥ 3`,
a smooth immersion `g : ℝⁿ → ℝ^{2n}` which is injective except for exactly two transverse double
points `(u₁,u₂)`, `(v₁,v₂)` of opposite sign (`doubleDetRep g u₁ u₂ * doubleDetRep g v₁ v₂ < 0`)
admits an injective immersion `g'` agreeing with `g` outside a large ball.  (A first version of
this statement with the agreement clause omitted was correctly rejected in review: without it the
conclusion is satisfied trivially by the linear inclusion.)


**`n = 1, 2`.**

* `n = 1`: `M` is a countable disjoint union of circles and lines; an explicit embedding of each
  component (circle of radius `1`, whole line) into `ℝ²` gives the result (and `ℝ² ⊂ ℝ²` trivially).
  Note `Work.Noncompact.exists_embedding_euclidean_weak` already gives an embedding into `ℝ³`, but
  the `2n = 2` case is better done directly.
* `n = 2`: the Whitney trick fails because a generic 2-disc meets the 2-dimensional image
  (`2 + 2 = 4`), and the classical proof uses the classification of surfaces (every surface embeds
  in `ℝ³`, and `ℝ³ ⊂ ℝ⁴`).  Mathlib has **no** classification of surfaces; this is a separate
  project.  A possible shortcut: every second-countable 2-manifold embeds in `ℝ³`, which itself
  needs the classification.  Deferred.

**Non-compact `M`.**

The classical argument (Persson, proof of Theorem 4.15) pushes the finitely many double points off
to infinity along disjoint properly embedded rays: for each double point take a curve `γᵢ` to
infinity, take disjoint small "tubes" `Uᵢ = S^{n-2} × [0,1] × [0,1)` around them, and use the
deformation `φ_t(p,r,s) = (p, r, [1-(1-δ)(1-r)t]s)` (made smooth), which is the identity on the
boundary of `Uᵢ`.  The result is again a proper immersion, hence — with no double points — an
embedding, and `Work.Embedding.isEmbedding_of_isProperMap_injective` gives `IsEmbedding`.  Note
that this needs *no* signs, but it does need the tubes to be disjoint and the deformation to keep
`f` an immersion; it is the second half of the work after the compact case.


### SESSION 6: the two preimages of a double point are *not* co-locatable (a flaw in the
### session-5 endgame plan), and what the sign bookkeeping really needs

The session-5 plan (still written above, under *The endgame for compact `M`, `n ≥ 3`*) proposed to
choose a *clean* point `x` which is **close to both** preimages `p₁, p₂` of the double point `P`
that is to be cancelled, so that both `p₁` and `p₂` lie in the chart at `x`, and to compute the
relative sign of `P` and of the newly inserted double point `Q` in that single chart (`doubleDetC`).
Adding the resulting new double point `P'` to `P` would then let `Work.Whitney.cancel_double_points`
remove the pair.

**That plan is broken**, and the reason is geometric, not formal:

* the two sheets through `w = f p₁ = f p₂` are *transverse*, so locally they meet **only** at `w`.
  Hence there is no point `x ≠ p₁, p₂` with `f x` on both sheets, and the argument "`f x` has one
  preimage near `p₁` and one near `p₂`, so `x` is close to both" is wrong: `f x` having two
  preimages would make `x` itself a double point, which transversality forbids near `w`;
* `p₁` and `p₂` are two points of `M` with `f p₁ = f p₂`; they are in general *far apart* (e.g. the
  two preimages of a crossing of a plane curve, or of a self-intersection of an immersed surface in
  `ℝ⁴`).  A chart is an open subset of `M` homeomorphic to `ℝⁿ`, so for a compact `M` (e.g. `T²`) a
  chart containing both `p₁` and `p₂` need not exist at all;
* adding a partner double point `Q` does not help: the gluing move
  (`Work.Whitney.exists_addDoublePoint_*`) creates a double point whose **two** preimages are both
  close to the insertion point, so after the insertion the four preimages are `p₁` (near the
  insertion point), `p₂` (far) and `q₁, q₂` (both near the insertion point).  Pairing `p₁` with a
  `q` gives a short arc inside one chart, but `p₂` has to be paired with the *other* `q`, and that
  arc is long.  So neither the "one chart for all four preimages" nor the "one chart per arc"
  configuration is available.

**What the cancellation really needs.**  The sign of a double point is not an intrinsic number: it
is the determinant of the two-sheet map `T_pM ⊕ T_qM → ℝ^{2n}`, which needs trivialisations of the
tangent spaces at both preimages.  Two double points can therefore only be compared *along the arcs
that pair their preimages* (the comparison is a product of the two determinants computed in
trivialisations that are consistent along those arcs).  The classical treatment (Whitney 1944;
Persson's thesis, Definition 4.8, Lemmas 4.12/4.13, Theorem 4.14) sidesteps this by fixing an
*orientation of `M`* when `M` is orientable and `n` is even, so that each double point has an
intrinsic sign; and by the following two facts in the remaining cases:

* **`n` odd**: relabelling the two preimages of a double point multiplies its sign by `(-1)ⁿ = -1`,
  so the *two pairings* of the four preimages give opposite comparisons.  Hence for `n` odd any two
  double points can be paired so as to have opposite signs -- no sign condition survives.
* **`M` non-orientable**: the comparison can be flipped by making the arc wind around an
  orientation-reversing loop, so again no sign condition survives.

This is exactly Persson's Theorem 4.14: a pair of double points can be removed when (i) `M`
orientable, `n` even and `#D > |I_f|`, or (ii) `M` non-orientable or `n` odd and `#D ≥ 2`; and
Whitney's proof of the strong embedding theorem then runs: use the *insertion* move
(`exists_addDoublePoint_*`, which changes the algebraic count `I_f` by `±1` and can be performed with
either sign) to arrange `I_f = 0`, then remove pairs until `#D = 0`.

**Formalisation options for the sign comparison** (none of them cheap; to be attacked in a later
session):

1. *Two charts, arcs inside them.*  `Work.Whitney.pairDet f c₁ c₂ a b` is the determinant of the
   two-sheet map with the first sheet read in `c₁` and the second in `c₂`.  If the arc from `p₁` to
   `q₁` lies in `c₁` and the arc from `p₂` to `q₂` lies in `c₂`, then
   `pairDet f c₁ c₂ p₁ p₂ * pairDet f c₁ c₂ q₁ q₂` *is* the geometric sign of the bigon, so the
   cancellation can take it as its hypothesis.  This is the cleanest statement, but as explained
   above it is not reachable in the endgame unless one can *drag a preimage* of a double point
   along a path (moving `q₂` next to `p₂`); that drag is itself a Whitney-style push supported near
   the path.
2. *Chart chain along the (long) arcs*: cover the arc by finitely many charts and compare through
   the transition determinants.  Faithful, but the transport bookkeeping is heavy.
3. *Orientation-based intrinsic signs*: formalise "`M` is oriented" (e.g. via an atlas whose
   transitions have positive Jacobian determinant, or a `StructureGroupoid` of positive-determinant
   local diffeos) and define the sign of a labelled double point via charts; this removes the arcs
   from the sign comparison entirely and is closest to the classical text.

**A second, unrelated formal gap found in session 6: `chartAt x` is not centred at `x`.**  Mathlib's
`ChartedSpace` gives only `x ∈ (chartAt x).source`; nothing forces `(chartAt x) x = 0`, so the ball
`{y | ‖(chartAt x) y‖ < r}` used by the gluing theorems is a ball around `(chartAt x)⁻¹ 0`, which may
be neither close to `x` nor a clean point.  Consequence: to insert a double point at a *chosen* clean
point `z` one needs the gluing move for an arbitrary smooth chart `c` (with `c z = 0`), not only for
`chartAt x`.  The files `Submission/Work/Whitney/PairDet.lean`, `exists_clean_ball.lean` and
`cancel_double_points_in_chart.lean` therefore take an arbitrary *chart-like*
`OpenPartialHomeomorph c` (`0 ∈ c.target`, `c` smooth on its source, `c.symm` smooth on its target)
instead of the `chartAt x` of the older statements.  A translated chart `c - c x` (same source, values
translated) turns the base point into `x` and is chart-like, so this interface gives full control over
where the insertion happens.

### SESSION 6, in the end: what is proved, and the endgame plan that works

**Proved this session** (all sorry-free, all imported above):

* `Work.Whitney.exists_addDoublePoint_chart_like` -- **the gluing move for an arbitrary
  chart-like `c`** (`0 ∈ c.target`, `c` smooth on its source, `c.symm` smooth on its target).  This
  is the form in which one can *choose the insertion point*: a translated chart
  `u ↦ (chartAt z) u - (chartAt z) z` is chart-like with `c z = 0`, so the gluing inserted at
  `c.symm 0` now happens at a chosen point `z`.
* `Work.Whitney.exists_addDoublePoint_chart_like` also returns the *located* information
  (`c p' = scaledPt n (√n) a`, `c q' = scaledPt n (√n) b`), and
  `Work.Whitney.exists_addDoublePoint_both_signs_chart_like`: two gluings at the *same* inserted
  double point `(p', q')` with *opposite* signs, i.e. the ability to choose the sign of an inserted
  double point.
* `Work.Whitney.exists_clean_point_and_chart`: a neighbourhood of any point contains a *clean*
  point `z` (no double point pair `(y,w)` has `f z = f y`), together with a chart-like map with
  `c z = 0` and `c` smooth both ways.  (`hclean0` of `exists_clean_ball`.)
* `Work.Whitney.exists_clean_ball`: around a chart-like `c` whose origin is clean, a
  junk-controlled chart `c'` and radii `R, η` with `f` injective on the `2R`-ball and the `R`-ball
  `η`-separated from everything outside the `2R`-ball (`hclean`, `hsep` of the gluing move).
* **`Work.Whitney.cancel_double_points_in_chart`** -- **the Whitney cancellation**, in the
  one-chart ("co-located") form: a smooth immersion (`n ≥ 3`) whose double point set consists of
  two transverse double points of opposite sign inside one chart can be modified inside that chart
  so that exactly those two double points disappear and no new one appears.  The geometric heart of
  the step `2n+1 → 2n`.
* **`Work.Whitney.cancel_double_points_oriented`** -- **the general Whitney cancellation**: two
  transverse double points of opposite sign (the sign being the *oriented-atlas* comparison below),
  joined by arcs inside a clean region `W` of a compact `M` (`n ≥ 3`), can be cancelled, keeping `f`
  fixed outside `W`.  This is the form the endgame uses: the arcs are arbitrary (long), the sign
  comparison is intrinsic because of the oriented atlas.
* `Work.Whitney.PairDet`: `pairDet f c₁ c₂ a b`, the two-chart signed determinant of a candidate
  double point, with `pairDet_self` (one chart = `doubleDetC`) and `pairDet_chartAt` (charts at the
  two points = intrinsic `doubleDet`).
* `Work.Whitney.IsOrientedAtlas` and `Work.Whitney.OppositeSign`: a cover of `M` by charts with
  pairwise positive Jacobian determinants ("an oriented atlas", i.e. a global orientation of `M`),
  and the induced *sign comparison* of two labelled double points; `Work.Whitney.oppositeSign_iff`
  proves that this comparison does not depend on which atlas charts are used at the four points.

**The endgame for compact `M`, `n ≥ 3`, that these make possible** (correcting the session-5
plan; see the session-6 discussion above for why co-location is impossible):

Let `f : M → ℝ^{2n}` be a self-transverse immersion of a compact `n`-manifold, `n ≥ 3`, and let
`A` be an oriented atlas of `M` (the orientable case).

1. *Insertion at a clean point.*  Using `exists_clean_point_and_chart` pick a clean point `z` close
   to a preimage `p₁` of an existing double point `P = (p₁, p₂)` and a chart-like `c` with
   `c z = 0`; using `exists_clean_ball` get `R, η`; choose the tubular parametrisation `H` and the
   cut-off model `β` (both already available: `Work.Whitney.exists_tubular_param_general_smooth`,
   `Work.Whitney.exists_bump_model_pair_smooth`) and apply
   `Work.Whitney.exists_addDoublePoint_both_signs_chart_like` to get `fp, fm` with the *same*
   inserted double point `Q = (p', q')` and `doubleDetC fm c p' q' = - doubleDetC fp c p' q'`.
   Since `A` covers `M`, the chart `c` may be taken from `A` (so the sign below is the intrinsic
   one).
2. *Choosing the right sign*: the inserted double point's sign relative to `A` is `±` a fixed
   number, so exactly one of `fp, fm` has `OppositeSign A … P … Q …`; the choice is decided by the
   concrete real-number inequality of `oppositeSign_iff`, i.e. by `by_cases`.
3. *Cancellation*: `Work.Whitney.cancel_double_points_oriented` (the general Whitney trick: the arcs
   joining `p₁` to `q₁` and `p₂` to `q₂`, the clean region `W` containing them, the disc in general
   position, and the sign condition `OppositeSign`), applied to that choice, deletes the four
   ordered pairs of `P` and `Q`, lowering the number of double points by one.
4. Iterate until the double point set is empty, then conclude with
   `Work.Whitney.isEmbedding_of_injective_of_compactSpace`.

The obstacle recorded in the session-6 notes above is thus resolved *for orientable `M`*: the sign
of a double point is intrinsic once an oriented atlas is fixed, so no co-location and no chart
chain is needed.  The remaining cases are (i) non-orientable `M` (Persson's Theorem 4.14(ii): the
comparison can be flipped by winding an arc around an orientation-reversing loop; alternatively one
may try to reduce to the orientable case via the orientation double cover), (ii) `n = 1, 2`, and
(iii) non-compact `M` (push the double points to infinity).

### A formalisation lesson (found by a colleague's `declare_false`)

`Work.Whitney.doubleDet f p q u v` must be evaluated at the *chart coordinates of the two points
themselves*, i.e. at `((chartAt p) p)` and `((chartAt q) q)` (compare
`Work.Whitney.doubleDet_ne_zero_iff`).  Writing `doubleDet f p q 0 0` is *wrong in general*: for the
trivial ChartedSpace on `ℝⁿ` (where `chartAt p = refl`, so `(chartAt p) p = p`), both blocks of
`doubleDet g p q 0 0` are the *same* derivative `fderiv ℝ g 0`, so the `coprod` kills the
antidiagonal and the determinant vanishes identically — no immersion can satisfy the clause.  Use
the coordinate-of-the-point form everywhere.

A second lesson from the same colleague: `chartAt x` is an `OpenPartialHomeomorph` whose underlying
function is *unconstrained outside its source* (only `x ∈ source`, `chartAt x ∈ atlas`, and the
transitions are constrained).  So a construction that reads the chart coordinate `(chartAt x) y` of
a point `y` need not be meaningful, and "the ball `{y | ‖(chartAt x) y‖ < r}`" can contain points
outside the chart source where the value is junk.  Statements about such constructions must either
restrict to `(chartAt x).source` explicitly or carry the hypothesis
`∀ y, ‖(chartAt x) y‖ < 3 * R → y ∈ (chartAt x).source` (which is satisfiable for a small `R` and
makes the junk values large, hence harmless).

### Third formalisation lesson: `ContDiff ℝ ⊤` is *analytic*, not smooth

In this Mathlib (`Mathlib/Analysis/Calculus/ContDiff/Defs.lean`), the order argument of `ContDiff`
has type `ℕ∞ω = WithTop ℕ∞`; `(⊤ : ℕ∞) : ℕ∞ω` is written `∞` and is `C^∞`, while
**`⊤ : ℕ∞ω` is written `ω` and means analyticity**.  Several statements in this chapter were
written with `ContDiff ℝ ⊤`; they must be read as *analyticity*.

* `Work.Whitney.model_immersion` is unaffected in practice: the model is a rational function, hence
  analytic, so the (stronger) statement is true.  Likewise for the other statements about the model.
* **`Work.Whitney.exists_tubular_param` must be restated with `ContDiff ℝ ∞`** (both in the
  hypothesis and in the conclusion): as written it assumes `φ` analytic and produces an analytic
  `H`, which our smooth-but-not-analytic chart representations do not satisfy.  The proof the
  colleague wrote (`exists_tubular_param_general`) uses only `ContDiff`-manipulations that are
  order-agnostic, so the `∞` version is cheap; the `EuclidModel`/`BumpModel` helper files contain
  the analogous `_infty` variants.
* **`Work.Whitney.exists_bump_model_pair` (in flight, `Whitney/exists_bump_model_pair*`) must be
  stated with `ContDiff ℝ ∞`**: with `⊤` = analyticity it is *false* — by the identity principle,
  an analytic `β` that agrees with the linear `inclModel` outside a ball is equal to it everywhere,
  so it has no double point.  A colleague proved the smooth version (`exists_bump_model_pair_smooth`)
  but the file was removed when they declared the `⊤` statement false; the helper files under
  `Submission/Work/Whitney/BumpModel/` (including the `_infty` ones) are theirs and are reusable.
* Likewise the gluing statement `exists_addDoublePoint` must use `ContDiff ℝ ∞` for `β` and `H`.

### Findings and design decisions (for future sessions)

* **The target's `M` is boundaryless** (`𝓡 n = modelWithCornersSelf`), so the projection
  machinery in its `𝓡 n` form applies to `M` itself.  Manifolds with boundary are only needed for
  the *compact pieces* of an exhaustion of a non-compact `M`.
* **Two routes for the boundary case** `Work.Boundary.exists_embedding_euclidean_of_compact_with_boundary`
  (compact smooth `n`-manifold with boundary ↪ `ℝ^{2n+1}`, currently delegated):
  1. *Doubling*: `W ⊔ W` modulo the identification of the two copies of `∂W` is a compact smooth
     `n`-manifold **without** boundary containing `W` as a neat submanifold; the already-proven
     `Work.Projection.exists_embedding_euclidean_of_compact_general` (or its `𝓡 n` version) then
     restricts.  This needs a construction of the double (quotient type, charts at boundary
     points, smoothness of the transition maps across the glued face).
  2. *Half-space analysis*: the bad sets of `Work.Projection.GeneralDefs` are defined with
     `fderivWithin ℝ _ (Set.range I)`, exactly matching the definition of `mfderiv`; the dimension
     bound then needs the *within*-derivative map `y ↦ fderivWithin ℝ g (Set.range I) y` to be
     locally Lipschitz on the half-space.  Useful Mathlib tools here:
     `ContDiffOn.continuousOn_fderivWithin` (`Mathlib/Analysis/Calculus/ContDiff/Defs.lean:912`),
     `ModelWithCorners.uniqueDiffOn` for `Set.range I`, and the interior/boundary lemmas in
     `Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean`
     (`IsBoundaryPoint`, `IsInteriorPoint`, `interior`, `boundary`, `isOpen_interior`,
     `interior_union_boundary_eq_univ`, `isInteriorPoint_iff_of_mem_atlas`,
     `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`).  Note that Mathlib's
     `writtenInExtChartAt` (which is how `mfderiv` is defined) may be a better chart representation
     for this route than `chartRepI`.
* **Strengthening available**: in the `..._general` branch the hypothesis `[I.Boundaryless]` can be
  weakened to `[BoundarylessManifold I M]` (`I` may have corners as long as no point of `M` is a
  boundary point); the chart targets then lie in `interior (range I)` and `fderivWithin _ (range I)`
  is `fderiv` there.
* **Tubular neighbourhoods**: `Work.Embedding.exists_unique_closest_point` — **proved** — is the
  metric form of the tubular neighbourhood theorem: a compact smooth submanifold of `ℝ^N` has
  positive reach, i.e. every point close enough to (the image of) `e` has a *unique* closest point
  in the image.  Its smooth strengthening is
  `Work.Embedding.exists_smooth_retraction` (currently delegated): the nearest-point projection is
  `C^∞` on a neighbourhood of the image and the displacement is orthogonal to the tangent space.
  These are the first steps towards both the collar/tube machinery used for gluing and the isotopy
  extension theorem.
* **Isotopy extension**:
  `Work.Isotopy.exists_smoothAmbientIsotopy_extending` (currently delegated) is the statement that
  a compactly supported smooth isotopy of a compact smoothly embedded submanifold of `ℝ^N` is
  induced by a smooth ambient isotopy.  It is the single most valuable missing tool: it is needed
  both for the telescoping gluing of the non-compact case and for the Whitney cancellation in the
  `2n+1 → 2n` step.  Its statement was reviewed three times and twice corrected (the support clause
  is vacuous if `U = univ` is allowed; the immersion hypothesis is indispensable — a cuspidal
  injective curve is a topological embedding but not an immersion; and the isotopy has to be
  stationary in time outside a compact interval, otherwise it may drift unboundedly although it is
  spatially compactly supported).  **Always have delegated statements reviewed: three of the
  statements written this session were initially wrong.**
* Other Mathlib facts that turned out to be useful: `CompactExhaustion`
  (`Mathlib/Topology/Compactness/SigmaCompact.lean`, with `choice`, `shiftr`, `find`,
  `mem_iff_find_le`) replaces a hand-rolled compact exhaustion;
  `SmoothPartitionOfUnity.exists_isSubordinate`;
  `Homeomorph.smulOfNeZero`, `Homeomorph.isEmbedding`, `Real.smoothTransition` (smooth step);
  `isClosedEmbedding_iff_continuous_injective_isClosedMap`, `IsProperMap.isClosed_range`.
* The file `Submission/Work/Isotopy/Smooth.lean` deliberately gives `SmoothAmbientIsotopy` only
  three fields (joint smoothness, slice embeddings, identity at `0`): deriving *slice* smoothness
  from joint smoothness requires commuting `(𝓘(ℝ,ℝ)).prod (𝓡 N)` with the self-model on
  `ℝ × ℝ^N`, which is a propositional (not definitional) equality of models.  The derived lemma
  is `SmoothAmbientIsotopy.contMDiff_apply`, whose proof uses `ContMDiff.prodMk` with the *manifold*
  product `(𝓘(ℝ,ℝ)).prod (𝓡 N)` as the target model.

### SESSION 7: the sign comparison, the clean region, and a key obstruction in the insertion

**New, proved (all sorry-free, imported above).**

* `Work.Whitney.pairDet_congr` (`SignCompare`) -- the two-chart signed determinant only depends on the
  values of `f` near the two points (this is how a modification far away leaves the sign of `P`
  untouched).
* `Work.Whitney.doubleDetC_transition` -- **the chart-change formula for the single-chart signed
  determinant**: `doubleDetC f c' p q = doubleDetC f c p q * (det T_p * det T_q)` with
  `T = D (c ∘ c'.symm)` evaluated at `c' p`, `c' q`.  The factor is independent of the map, which is
  what makes the sign of an inserted double point transportable to the charts of an oriented atlas.
* `Work.Whitney.oppositeSign_or_of_neg` -- **the sign choice**: if two candidate maps `fp`, `fm`
  agree with `f` near the preimages `p₁`, `p₂` of a transverse double point `P`, and their
  `doubleDetC`-values at an inserted double point `(p', q')`, read in one chart `c₃ ∈ A` of an
  oriented atlas, are opposite and nonzero, then exactly one of them makes `P` and `(p',q')` have
  opposite signs.  This decides the insertion by an explicit real inequality.
* `Work.Whitney.clean_region_conditions` (`CleanRegion`) -- if `W` meets the set
  `D = {y | ∃ z ≠ y, f z = f y}` of double-point preimages only in the four points, and the two
  double points are *simple* (their values have no third preimage), then `W` satisfies both
  hypotheses `hclean`, `hsep` of the cancellation.
* `Work.Whitney.exists_clean_data_shrink` -- the clean-ball data (injectivity on the `2S`-ball and
  separation `η` between the `S`-ball and the outside of the `2S`-ball) may be shrunk to any
  `R ≤ S`, with a fresh separation constant.
* **`Work.Whitney.exists_clean_region`** (`clean_region_of_arcs`) -- **the clean region of the
  cancellation is `W = M ∖ (D ∖ {p₁,p₂,q₁,q₂})`**: it is open, has compact closure, contains the four
  points, meets `D` exactly in them, and every other point of `W` has a unique preimage.  Hence every
  arc whose interior avoids `D` lies in `W`.  The only geometric input of the cancellation is thus
  the *existence of the two arcs*.
* `Work.Whitney.exists_chart_globally_smooth_symm` -- every chart-like map may be replaced, after
  shrinking its source, by one whose inverse is smooth *everywhere*; needed because the gluing move
  requires the chart representation `u ↦ f (c.symm u)` to be smooth on all of `ℝⁿ` and equal to
  `H (·, 0)` there.
* `Work.Whitney.exists_tubular_data_smooth` -- the tubular data `H : ℝⁿ × ℝⁿ → ℝ^{2n}` (smooth,
  `H (u,0) = f (c.symm u)`, injective on a ball with injective derivative) together with a Lipschitz
  constant `L` on that ball: exactly the `H, ρ, L` inputs of the gluing move.
* `Work.Whitney.exists_addDoublePoint_both_signs_located` -- the gluing move with the *located*
  conclusion `‖c p'‖ < R`, `‖c q'‖ < R`, so that the inserted preimages are in the `R`-ball, hence
  in the source of `c` and of every atlas chart covering that ball.  Without this the inserted points
  would be invisible to `doubleDetC`.

**Proved in the second half of session 7.**

* **`Work.Whitney.exists_addDoublePoint_oriented`** (`insert_double_point_oriented`) -- **the
  insertion of a transverse double point with a chosen sign**: from the clean chart `c`, the
  clean-ball data at radius `R`, a cut-off model with support radius `R` and deviation `δ`, the
  tubular data `H, ρ, L`, and a (transverse) pre-existing double point `P = (p₁,p₂)` whose two
  preimages are at `c`-distance `> R` (the two eventual conditions `hn₁`, `hn₂`), it produces an
  immersion `f'` with `doubleSet f' = doubleSet f ∪ {(p', q'), (q', p')}`, `‖c p'‖ < R`,
  `‖c q'‖ < R`, `f' = f` near `p₁` and `p₂`, and `OppositeSign A f' p₁ p₂ p' q'` for the oriented
  atlas `A`.  The proof: the located gluing move gives the two candidate maps `fp`, `fm` with
  opposite `doubleDetC` in the chart `c`; `doubleDetC_transition` transports the flip to a chart
  `c₃ ∈ A` (the transition factor is nonzero, hypothesis `htrans`, dischargeable by
  `Work.Whitney.fderiv_transition_det_ne_zero`); `oppositeSign_or_of_neg` then selects the variant.
* `Work.Whitney.exists_bump_model_pair_smooth_scaled` -- **the cut-off model with independent
  support radius `R` and deviation `δ`** (the fix for the obstruction below); proved by the fleet.
* `Work.Whitney.exists_addDoublePoint_both_signs_located` -- the gluing move with the located
  conclusion `‖c p'‖ < R`, `‖c q'‖ < R` (so that the inserted points can be read in the charts).
* `Work.Whitney.fderiv_transition_det_ne_zero` -- the transition factor `det D(c ∘ c'.symm)` is
  nonzero (the transition is a local diffeomorphism).
* `Work.Whitney.differentiableAt_comp_chart_globally_smooth`,
  `Work.Whitney.differentiableAt_transition_of_globally_smooth` -- the differentiability inputs of
  `doubleDetC_transition`.
* `Work.Whitney.EndgameAux`: `simple_of_inserted` (the inserted double point is simple),
  `simple_transported` (a simple pre-existing double point stays simple),
  `eventually_norm_lt_of_mem_source` (the eventual radius conditions at a point of the chart
  source), `ncard_doubleSet_insert` (`ncard` grows by two on insertion) and
  `ncard_doubleSet_drop_one` (`ncard` drops by two on cancellation) -- the bookkeeping of the
  endgame iteration.

**In flight at the end of the session**: `Work.Whitney.exists_disjoint_arcs_avoiding_finite` (two
disjoint arcs avoiding a finite set) -- the last missing geometric input of the compact `n ≥ 3`
endgame.

### SESSION 7, the obstruction: the cut-off model's deviation is tied to its support radius

The gluing move `Work.Whitney.exists_addDoublePoint_both_signs_chart_like` takes both the model's
support radius `R` and its deviation `δ` as parameters and needs

* `hβR : R ≤ ‖u‖ → β u = inclModel u`, * `hβδ : ‖β u - inclModel u‖ ≤ δ`, and
* `hδLη : L * δ < η`, where `η` is the separation between the images of the `R`-ball and of the
  outside of the `2R`-ball and `L` the Lipschitz constant of the tubular parametrisation.

Here `η ≥ σ R` where `σ` is the smallest singular value of the chart representation at the clean
point, while `L` is at least the Lipschitz constant of the chart representation, hence
`L ≳ σ_max ≥ σ`.  So the gluing needs `δ ≲ R·σ/L ≤ R`.  The existing model
`Work.Whitney.exists_bump_model_pair_smooth` cannot provide this: its construction
(`bumpPlus n χ ρ x = ρ • structMap n χ (ρ⁻¹ x)`) has support radius `4ρ` and deviation of order `ρ`,
i.e. `δ ≈ 2R`, so that `L δ ≳ 2 σ R > η` for *every* chart.  Concretely, for `f` the inclusion
`ℝⁿ → ℝ^{2n}` the hypotheses of the gluing move are unsatisfiable with that model.  The fix is
`Work.Whitney.exists_bump_model_pair_smooth_scaled`: the same `structMap` construction with a
cut-off whose plateau is a ball of radius `ε` and which decays like `ε/|x|`, giving deviation
`≲ ε·ρ` with support `≲ ρ`; i.e. an arbitrary ratio, as the gluing requires.

### SESSION 7, the plan for the insertion lemma (the next thing to write)

`exists_addDoublePoint_oriented` should take (all obtainable from the lemmas above):

* `f`, `hf`, `himm`;
* a chart-like `c` (with `0 ∈ c.target`, smooth on its source, globally smooth inverse) centred at a
  *clean* point `z = c.symm 0` (from `exists_clean_point_and_chart` +
  `exists_chart_globally_smooth_symm`);
* an explicit radius `R` with the clean conditions at radius `R` (from `exists_clean_ball` +
  `exists_clean_data_shrink`), plus `hsrc : ‖c y‖ < 3R → y ∈ c.source` and
  `Metric.ball 0 (3R) ⊆ c.target`;
* model data `β, a, b, δ` with support radius `R` and deviation `δ`
  (`exists_bump_model_pair_smooth_scaled`) with `L δ < η` and `2R + δ ≤ ρ`;
* tubular data `H, ρ, L` (`exists_tubular_data_smooth`);
* the double point data `f p₁ = f p₂`, `p₁ ≠ p₂`, atlas charts `c₁, c₂` containing them with
  `pairDet f c₁ c₂ p₁ p₂ ≠ 0`, and **the eventual radius conditions**
  `∀ᶠ y in 𝓝 p₁, R < ‖c y‖`, `∀ᶠ y in 𝓝 p₂, R < ‖c y‖`.  These two are the only non-obvious input:
  they say that the modification region is a neighbourhood of both preimages, which is what makes
  `pairDet f' c₁ c₂ p₁ p₂ = pairDet f c₁ c₂ p₁ p₂`.  They hold automatically when `p_i ∈ c.source`
  (continuity) and can be arranged otherwise through the *junk values* of `c` off its source: the
  `toFun` of an `OpenPartialHomeomorph` is unconstrained off its source, so one may set it to a fixed
  vector `ψ` with `‖ψ‖ > R` on a neighbourhood of `p_i` disjoint from `c.source`.

The conclusion should be: `∃ f' p' q', ContMDiff f' ∧ (∀ y, Injective (mfderiv f' y)) ∧
doubleSet f' = doubleSet f ∪ {(p',q'),(q',p')} ∧ f' =ᶠ[𝓝 p₁] f ∧ f' =ᶠ[𝓝 p₂] f ∧
OppositeSign A f' p₁ p₂ p' q'` (for the oriented atlas `A`).  For the last conjunct there are two
routes: (i) `doubleDetC_transition` transports the flip from the insertion chart `c` to a chart
`c₃ ∈ A`, which additionally needs the transition factor to be nonzero (local invertibility of
`c ∘ c₃.symm`); (ii) *enlarge* the oriented atlas by the insertion chart and prove
`IsOrientedAtlas (insert c A)` -- for a chart `c` that is a *translate* of a chart `c₀ ∈ A` all
transitions are translations, hence have determinant `1 > 0`, and positivity with the other charts of
`A` follows by factoring through `c₀`.  Route (ii) avoids the invertibility argument and lets
`oppositeSign_or_of_neg` be applied with `c₃ := c` (using the located conclusion `‖c p'‖ < R` to know
that `p', q' ∈ c.source`).

### SESSION 7, two further findings for the endgame

* **Triple points cannot be cancelled.**  If the value of `P = (p₁,p₂)` has a third preimage `z`,
  then no `W` can satisfy both `hclean` and `hsep`: `p₁ ∈ W` forces `z ∈ W` by `hsep`, and then the
  pair `(p₁, z)` violates `hclean`.  The endgame must therefore select a double point with exactly
  two preimages (or handle the "all double points are triple" case separately -- an open point).
* **The disconnected case must be reduced to the connected one.**  The preimages of `P` may lie in
  different components of `M`, in which case the two arcs do not exist.  For *compact* `M` this is
  handled by embedding the finitely many components separately (into bounded sets) and placing their
  images in disjoint regions of `ℝ^{2n}` by scaling and translating.

### Notes for future sessions

* `Work.Projection.exists_good_direction_general` and
  `Work.Projection.exists_embedding_euclidean_of_compact_general` extend the compact weak Whitney
  theorem to an arbitrary (boundaryless) finite-dimensional model `E`.
* A useful strengthening: everywhere in the `..._general` branch the hypothesis `[I.Boundaryless]`
  can be weakened to `[BoundarylessManifold I M]` (every point of `M` is an interior point); this
  covers open submanifolds of manifolds with corners and is what `isOpen_interior` /
  `isInteriorPoint_iff_of_mem_atlas` support.
* The file `orphan_exists_good_direction_general.lean.txt` in the workspace root is a leftover stub
  (statement + `sorry`, no proof) that had been created under `Submission/Work/Projection/`; it was
  moved out of the build because the path had to be re-requested.
* The `sorry` below is intentional: it marks exactly the two gaps described above.

### SESSION 8: the interfaces of the endgame, and the endgame itself

**New files (mine).**

* `Submission/Work/Whitney/InsertedDoublePoint.lean` -- the structure
  `Work.Whitney.InsertedDoublePoint f A p₁ p₂ f' p' q'`: everything the cancellation needs to know
  about the map `f'` obtained by gluing the model in (`contMDiff`, `injective_mfderiv`,
  `doubleSet f' = doubleSet f ∪ {(p',q'),(q',p')}`, `oppositeSign`, `finite_doubleSet`,
  `simple_new`, `simple_old`, `distinct`, `new_not_old`).

* `Submission/Work/Whitney/reduce_double_points_abstract.lean` -- the two *interfaces* and the
  reduction:
  * `Work.Whitney.SimpleDP f` -- every double point of `f` has exactly two preimages;
  * `Work.Whitney.TransDP A f` -- every double point of `f` is transverse, certified by two charts
    of `A` with nonvanishing `pairDet`;
  * `Work.Whitney.IsSmoothOrientedAtlas A` -- `IsOrientedAtlas A` **plus** the requirement that the
    charts of `A` are genuine smooth charts (both directions smooth).  This strengthening is
    necessary: `IsOrientedAtlas` may be witnessed by partial homeomorphisms that are not compatible
    with the smooth structure (e.g. `x ↦ x³` on `ℝ`), and then the `pairDet`-based sign statements
    are meaningless.  An earlier delegation of the insertion lemma was declared FALSE for exactly
    this reason;
  * `Work.Whitney.HasInsertion n M` -- the insertion step (instantiated by
    `Work.Whitney.exists_insertedDoublePoint`, delegated) *with* the preservation of both
    invariants;
  * `Work.Whitney.HasCancellation n M` -- Whitney's trick (`cancel_double_points_oriented`) with the
    extra clause that the modified map has the same `pairDet` off the clean region `W` (this is what
    makes the transversality of the *remaining* double points survive the modification; the proof
    uses that the push is the identity near the image of the frontier of the collar, so that
    `mfderiv f'' = mfderiv f'` at every point outside `W`, hence `f'' = f'` on a neighbourhood of
    every frontier point of the collar);
  * **`Work.Whitney.exists_reduce_double_points`** PROVED: a simple transverse double point can be
    removed together with an inserted partner of opposite sign, `(doubleSet f).ncard` drops by
    exactly `2`, and both invariants are preserved.  The proof is the assembly
    insert -> two disjoint arcs (`exists_disjoint_arcs_avoiding_finite`) -> clean region
    (`exists_clean_region`) -> Whitney cancellation, plus the invariant bookkeeping (simplicity
    transfers because `doubleSet f'' ⊆ doubleSet f'`; transversality transfers because the
    remaining preimages lie *outside* the clean region, which is proved from `SimpleDP f'` and the
    double point set equality).

* `Submission/Work/Whitney/endgame_abstract.lean` -- the iteration:
  `Work.Whitney.HasReduction` (the interface of the reduction step) and
  **`Work.Whitney.exists_embedding_of_reduce`** PROVED: strong induction on
  `(doubleSet f).ncard` shows that a smooth immersion `f : M → ℝ^{2n}` of a compact connected
  `n`-manifold (`n ≥ 3`) with finitely many *simple transverse* double points can be improved to a
  smooth embedding (`IsEmbedding`) with injective `mfderiv`; the base case is
  `Work.Whitney.isEmbedding_of_injective_of_compactSpace`.

* `Submission/Work/Whitney/projection_transverse_immersion.lean` -- PROVED:
  `Work.Whitney.exists_immersion_transverse_of_embedding`: the generic projection of a smooth
  embedding `e : M → ℝ^{2n+1}` is a smooth immersion whose double point set is **finite** (compact
  `M` + transversality, `finite_double_points_of_transverse`) and whose double points are
  **transverse** in the intrinsic (range) form.

**Landed later in session 8 (all sorry-free, all imported above).**

* `Work.Whitney.exists_insertedDoublePoint` (file `exists_insertedDoublePoint.lean`) -- the insertion
  step instantiated: it produces `InsertedDoublePoint f A p₁ p₂ f' p' q'` **and** preserves the two
  invariants `SimpleDP`, `TransDP`.  The earlier attempts at this path were declared FALSE for the
  reason recorded below (non-smooth charts in an "oriented atlas"); the delegated proof with
  `IsSmoothOrientedAtlas` succeeded.
* `Work.Whitney.pairDet_ne_zero_iff` (file `pairDet_ne_zero_iff.lean`) -- `pairDet f c₁ c₂ p q ≠ 0`
  iff the two tangent images span `ℝ^{2n}`; the bridge between the intrinsic transversality produced
  by the projection and the `pairDet` certificates of `TransDP`.
* `Work.Whitney.cancellation_of_pushData` (file `cancellation_of_pushData.lean`) -- given the
  target-side push data (`Work.Whitney.HasAmbientPushData`'s fields, unpacked) it produces the
  modified immersion with `doubleSet f' = doubleSet f \ {four pairs}` **and** with `pairDet`
  unchanged off `W` (the frontier argument of the push: `ψ` is the identity on a neighbourhood of
  `f '' frontier W₀`, so the cut-and-paste map agrees with `f` on a neighbourhood of every point
  outside `W`).
* `Work.Whitney.transDP_of_range`, `Work.Whitney.exists_embedding_of_compact_connected`
  (`assembly_compact.lean`) -- intrinsic transversality becomes `TransDP`, and the endgame is
  assembled: a compact connected `n`-manifold (`n ≥ 3`) carrying a smooth oriented atlas of smooth
  charts **and an immersion with finitely many simple transverse double points** admits a smooth
  embedding into `ℝ^{2n}` with injective derivative.
* `Work.Whitney.HasAmbientPush`, `Work.Whitney.hasCancellation_of_hasAmbientPush`,
  `Work.Whitney.hasInsertion_of`, `Work.Whitney.hasReduction_of` (`hasReduction.lean`) -- the three
  interfaces of the endgame instantiated: `HasReduction` follows from `HasInsertion` (proved) and
  `HasCancellation` (which follows from the *single* leftover geometric input `HasAmbientPush`, i.e.
  from `exists_ambient_push_data`).

* `Work.Whitney.exists_embedding_of_compact_connected_orientable`
  (`assembly_compact_full.lean`) -- **the compact, connected, orientable branch of the theorem,
  reduced to exactly three inputs**: the push construction (`Work.Whitney.HasAmbientPush`, i.e. the
  conclusion of `exists_ambient_push_data`), an oriented atlas of smooth charts on `M` (this is
  where orientability enters), and an immersion in general position (`hgen`, the genericity input
  delegated as `Work.Whitney.exists_simple_transverse_immersion`).  Everything else -- weak Whitney,
  generic projection, insertion, cancellation, invariant bookkeeping, iteration -- is proved.

**What remains for the compact, connected, orientable case `n ≥ 3`** (the branch the above targets):

1. ~~The insertion step preserving the invariants~~ -- PROVED
   (`Work.Whitney.exists_insertedDoublePoint`).
2. ~~The cancellation with the extra `pairDet` clause~~ -- PROVED modulo the push construction:
   `Work.Whitney.cancellation_of_pushData` plus the interface `Work.Whitney.HasAmbientPush`, which is
   exactly the conclusion of `Work.Whitney.exists_ambient_push_data` (the file whose dependency
   `Submission/Work/Whitney/local_push_cut_nontransverse_full.lean` is being finished right now).
3. ~~`Work.Whitney.pairDet_ne_zero_iff`~~ -- PROVED.
4. **Triple points.** `SimpleDP` of the projected immersion says that no value has three
   preimages.  This is a genuine *genericity* statement (a generic immersion of an `n`-manifold
   into `ℝ^{2n}` has no triple points, because the 3-fold locus has dimension `3n - 2·(2n) = -n`).
   The existing projection argument (`exists_projection_transverse`) excludes bad directions via
   Sard for the *double point* locus only; adding the 3-fold locus requires parametrising the
   collinear triples or a local argument that destroys triple points (e.g. pushing one of the three
   sheets), and is **not yet formalised**.  This is the main missing *geometric* input of the
   endgame after the push.
5. **Orientation.** `IsSmoothOrientedAtlas A` exists only if `M` is orientable.  For a
   *non-orientable* compact `M` the sign framework of this chapter (an oriented atlas, positive
   transition determinants) does not apply, and the classical argument uses instead the transport
   of a local orientation along the two arcs of the bigon (equivalently, the trivialisation of the
   normal bundle of the Whitney disc).  Formalising that is a separate project; the sign framework
   here (`OppositeSign`, `doubleDetC`, `pairDet`) would have to be re-based on a *framing of the
   bigon* rather than a global oriented atlas.  Note that `IsOrientedAtlas` is only ever used to
   make the *sign comparison* canonical; for non-orientable `M` one can also flip the sign of a
   double point by moving it around an orientation-reversing loop, which is the classical trick.

* `Work.Embedding.exists_embedding_of_components` (`Submission/Work/Embedding/exists_embedding_of_components.lean`)
  -- PROVED: the *disconnected* compact case reduces to the connected one.  For a compact smooth
  `n`-manifold (`n ≥ 1`), if every *compact connected open* subset `U` of `M` admits a smooth
  embedding `U → ℝ^{2n}` with injective derivative, then `M` does.  (Each component of `M` is
  clopen and compact; Mathlib's open-subset manifold structure
  (`TopologicalSpace.Opens.instChartedSpace`, `Opens.instIsManifold`, `contMDiff_subtype_val`)
  makes the components manifolds; the finitely many images are placed in disjoint balls and glued.)
  The remaining task for this branch is to *discharge* `hconn`: for a compact connected open `U`
  one must (i) restrict a smooth oriented atlas of `M` to `U` (not yet formalised) and (ii) apply
  `exists_embedding_of_compact_connected_orientable` to `U` (whose compactness, connectedness,
  second countability and manifold structure are inherited).

**Other branches of the target.**

* `n = 1`: **DONE** (session 9).  `Work.OneDim.exists_embedding_euclidean_two` is sorry-free
  (verified with `#print axioms`); its proof is the classification of connected 1-manifolds
  (`Work.OneDim.one_manifold_dichotomy`, `Work.OneDim.closing_diffeomorph_circle`) followed by the
  explicit disjoint-slot placement of lines and circles in `ℝ²`
  (`Work.OneDim.assembly_of_components`).  The target's proof now splits on `n = 1` and discharges
  that case with this theorem.
* `n = 2`: needs the classification of surfaces (absent from Mathlib) -- the Whitney trick itself
  provably fails at `n = 2` (the Whitney disc needs `2 + n < 2n`), so this is a separate project.
* non-compact `M`: see the SESSION 9 plan below (the *compression* mechanism).  The weak Whitney
  theorem for all second countable manifolds (`Work.Noncompact.*`) is already in place, as is
  `Work.Embedding.isEmbedding_of_isProperMap_injective`.

# SESSION 9

## New results of this session (all sorry-free, imported above)

* `Work.Whitney.exists_simple_transverse_immersion` (`Submission/Work/Whitney/exists_simple_transverse_immersion.lean`)
  -- **the genericity input of the endgame**: a compact smooth `n`-manifold (`n ≥ 3`) admits a
  smooth immersion into `ℝ^{2n}` with *finitely many*, *simple*, *transverse* double points (the
  3-fold locus has dimension `3n - 4n < 0`).
* `Work.Whitney.exists_isSmoothOrientedAtlas_restrict` -- a smooth oriented atlas restricts to an
  open submanifold (`A' = {c.subtypeRestr hU | c ∈ A}`); this discharges the hypothesis `hconn` of
  `Work.Embedding.exists_embedding_of_components`.
* **`Work.Whitney.exists_embedding_of_compact_of_orientedAtlas`**
  (`Submission/Work/Whitney/assembly_compact_orientable.lean`) -- **the *whole* compact orientable
  branch of the theorem, assembled end to end modulo ONE input**:
  `hpush : ∀ (U : Opens M) [CompactSpace U], HasAmbientPush n U` (the Whitney push).  Everything
  else -- general position, insertion, cancellation, invariants, iteration, the reduction to the
  connected case and the restriction of the atlas -- is proved.
* **The `n = 1` case of the target is proved**: `Work.OneDim.exists_embedding_euclidean_two` is
  sorry-free and is now used by the target's proof in the branch `n = 1` (the proof of
  `Submission.whitney_embedding` is `rcases eq_or_ne n 1` plus one remaining `sorry` for `n ≥ 2`).
* `Submission/Work/Whitney/ArcFraming.lean` -- the beginning of the **bigon-framing** framework
  needed for the *non-orientable* case: `Work.Whitney.IsSmoothChart`, `PosTransitionAt`,
  `IsArcChain` (a chain of smooth charts along an arc with positive transitions),
  `posTransitionAt_self`, `isArcChain_const`, and the predicate `Work.Whitney.OppositeType`
  (the sign comparison of two double points along a pair of arcs).  The two key lemmas are
  delegated: `Work.Whitney.exists_isArcChain` (a chain along any continuous arc exists, by covering
  the arc by charts and flipping each chart by a reflection) and
  `Work.Whitney.posTransitionAt_of_isArcChain` (**canonicity**: two chains along the *same* arc
  compare the endpoints' framings with the same sign -- the "transport along an arc is well defined
  up to positive transition" statement; note it genuinely needs `Continuous γ`, as the review
  caught).  Both of the following are now PROVED:
  `Work.Whitney.exists_isArcChain` and `Work.Whitney.exists_oppositeType_of_insertion`
  (the last one: the two insertion maps
  `exists_addDoublePoint_both_signs_chart_like` produce the *same* inserted pair with opposite
  `doubleDetC` in the insertion chart and agree with `f` near the pre-existing preimages, so
  exactly one of them has a negative *framed* comparison `Work.Whitney.OppositeType`).

## The three remaining branches, with the mechanism each needs

1. **Non-orientable compact (or general) `M`, `n ≥ 3`.**  `IsSmoothOrientedAtlas` cannot exist, so
   the sign comparison `Work.Whitney.OppositeSign` (a *global* oriented atlas) is unavailable and
   must be replaced by the *arc framing* `Work.Whitney.OppositeType`: each of the two bigon arcs is
   contractible, so a chain of positively related charts along it always exists (that is
   `Work.Whitney.exists_isArcChain`), and the comparison is canonical
   (`Work.Whitney.posTransitionAt_of_isArcChain`).  The *endgame* works with this notion and needs
   no canonicity across different choices of charts:  the insertion lemma
   (`Work.Whitney.exists_addDoublePoint_both_signs_chart_like`) provides two maps `fp`, `fm` with
   `doubleDetC fm c p' q' = - doubleDetC fp c p' q'` in the insertion chart `c` while both agree
   with `f` *near the pre-existing double point's two preimages*; taking `c₁ = c₃ = c` (the short arc
   lies in `c`) and any chain `c₂ → c₄ = c` along the long arc, the first factor
   `pairDet f c c₂ p₁ p₂` depends only on the *germ* of `f` at `p₁, p₂` (`Work.Whitney.pairDet_congr`)
   and is therefore the same for `fp` and `fm`, while the second factor is flipped.  So *exactly one*
   of the two insertions has a negative comparison.  What is needed to finish this branch:  (i) the
   two delegated lemmas;  (ii) restate the push interface `Work.Whitney.HasAmbientPush` with
   `OppositeType` in place of `OppositeSign A` (the push's *proof* uses the framing only to build
   the Whitney disc, so the change should be local);  (iii) re-derive the endgame interfaces
   (`HasInsertion`, `HasCancellation`, `HasReduction`) with `OppositeType`.

2. **Non-compact `M` (all `n ≥ 1`).**  The classical mechanism is a *compression of the domain*,
   which evades the parity/counting obstruction of the compact case because it is **not** a
   self-homeomorphism of `M`:  given a proper immersion `f : M → ℝ^{2n}` with isolated double
   points and a double point `f a = f b`, take an arc `γ` from `a` to infinity and a tubular
   neighbourhood `U ≅ S^{n-2} × [0,1] × [0,1)` of it, with `a` on the "spine" `{r = 0}` at
   parameter `s = 2δ`.  The map `φ (p,r,s) = (p, r, [1 - (1-δ)(1-r)] s)` (and the identity outside
   `U`) is an *injective, non-surjective* self-embedding of `M` with image `{s < δ + (1-δ) r}`; it
   fixes the boundary of `U`.  Then `f' = f ∘ φ` is again a proper immersion, and the double point
   `(a,b)` is **gone**:  `a` lies in the deleted shell `{s ≥ δ + (1-δ) r}` on the spine, so
   `a ∉ φ(M)`, while `b ∉ U` is unaffected; since `f a = f b` has exactly two preimages, the value
   is now attained at most once.  Doing this for *all* double points at once (disjoint tubes, one
   per double point, each starting at one of its preimages) removes all of them, and the resulting
   injective immersion is proper, hence an embedding.  Needed: a *proper* immersion `M → ℝ^{2n}`
   with isolated, simple, transverse double points (the general-position input for non-compact `M`;
   for compact `M` this is `exists_simple_transverse_immersion`), the existence of the tubes
   (tubular neighbourhood of a proper arc), and the bookkeeping above.

# SESSION 12: the transversality-carrying endgame, and a proper immersion into `ℝ^{2n}`

**The compact branch is now reduced to the *transverse* local push.**  The endgame interfaces
`Work.Whitney.HasPushNF`/`HasCancelNF` of SESSION 10 are *weaker* than the cut-form local push
`Work.Whitney.LocalPushNTrans`, which carries the transversality of the two double points as a
hypothesis.  `Submission/Work/Whitney/EndgameNFTrans.lean` (module
`Submission.Work.Whitney.EndgameNFTrans`, imported above) repeats the entire endgame with that
hypothesis carried along:

* `Work.Whitney.trans_of_transDP'` (**proved**) — the `TransDP'` certificate implies intrinsic
  transversality `range (mfderiv f p.1) ⊔ range (mfderiv f p.2) = ⊤` at every double point;
* `Work.Whitney.HasPushNFT`, `Work.Whitney.HasCancelNFT`, `Work.Whitney.HasReduceNFT` — the
  `Trans`-variants of the SESSION 10 interfaces;
* `Work.Whitney.hasPushNFT_of_localPushNTrans` (**proved**) — the push interface from
  `Work.Whitney.LocalPushNTrans` (via the delegated
  `Work.Whitney.hasAmbientPushData_of_localPushTrans`);
* `Work.Whitney.hasPushNFT_of_hasPushNF`, `Work.Whitney.hasCancelNFT_of_hasPushNFT` (**proved**);
* `Work.Whitney.exists_reduce_double_points_NFT` (**proved**) — the reduction step, with the two
  transversality hypotheses supplied from `TransDP'` of the *inserted* map;
* `Work.Whitney.hasReduceNFT_of`, `Work.Whitney.exists_embedding_of_reduce_NFT`,
  `Work.Whitney.exists_embedding_of_compact_connected_NFT`,
  `Work.Whitney.exists_embedding_of_compact_NFT` (**proved**).

Consequently the compact case for `n ≥ 3` is reduced to **`Work.Whitney.LocalPushNTrans n U`** for
every compact open `U` (equivalently to the cut-form push `Work.Whitney.exists_local_push_cut_full`
with the transversality hypothesis).  The plumbing into the target is checked: with
`h : ∀ (U : Opens M) [CompactSpace U], Work.Whitney.LocalPushNTrans n U`, the expression

  `Work.Whitney.exists_embedding_of_compact_NFT hn (fun U _ => hasPushNFT_of_localPushNTrans (h U))
     (fun U _ => Work.Whitney.hasInsertionNF (n := n) (by omega))`

has exactly the target's conclusion (verified in a scratch file; `Work.Whitney.hasInsertionNF`
needs only `2 ≤ n`).

**The non-compact branch: the general-position input is now available.**
`Work.Noncompact.exists_structured_proper_embedding_weak` (delegated this session, sorry-free) and
`Work.Projection.exists_projection_transverse_avoiding` (the general position theorem with the
freedom of avoiding a prescribed null set) give, in
`Submission/Work/Noncompact/proper_immersion_transverse.lean` (module
`Submission.Work.Noncompact.proper_immersion_transverse`, imported above):

* **`Work.Noncompact.exists_proper_immersion_transverse`** (**proved**, `1 ≤ n`, `M` Hausdorff,
  second countable, nonempty, *no compactness*): a smooth **proper** immersion
  `h : M → ℝ^{2n}` whose every double point is transverse.  Properness comes from the structural
  form `g = b - f • u₀` of the weak proper embedding (`b` bounded, `f` proper) plus the choice of
  the projection direction `u` with `projVec u u₀ ≠ 0`; the latter is forced by the null-set
  avoidance applied to `Z = {pairEquiv n (extract u₀)}` (if `projVec u u₀ = 0` then
  `u = extract u₀`).

Two further pieces of the non-compact chapter are in place (all proved, imported above):

* `Work.Noncompact.finite_preimages_and_discrete_doubleSet` — for a *proper* smooth immersion `h`
  in general position: every value has finitely many preimages, every double point is isolated in
  `doubleSet h`, and the double point preimages meet every compact set in a finite set (so the
  double point set is locally finite);
* `Work.Whitney.exists_simple_transverse_immersion_of_ge_one` — the general position input of the
  compact case with the hypothesis weakened from `3 ≤ n` to `1 ≤ n` (the `3 ≤ n` of the original
  statement was unused).  This is what the `n = 2` branch needs.

The remaining work for the non-compact case — the "push the double points to infinity" step — is
written up in **`Submission/Work/Noncompact/NOTES_noncompact_plan.md`**, together with two findings:
(i) `hn : 3 ≤ n` is *unused* in `Work.Whitney.local_push_manifold`, so the local push exists for
every `n ≥ 1`, which is relevant to the `n = 2` branch (the classification of closed surfaces
might be avoidable); (ii) a "smooth interpolation" of the non-cut push does *not* produce a cut
push (the intermediate values of the isotopy still have the crossing), which is why the cut form
needs the sheet-parameter-dependent amplitude of the fleet's box push.

# SESSION 12, continued: the `n = 2` branch may avoid the classification of closed surfaces

Three hypotheses that the fleet's machinery inherited from its origin are *unused*:

* `Work.Whitney.exists_simple_transverse_immersion` needs only `1 ≤ n` (proved as
  `Work.Whitney.exists_simple_transverse_immersion_of_ge_one`, imported above);
* `Work.Whitney.hasInsertionNF` is already stated with `2 ≤ n`;
* the `hn : 3 ≤ n` of `Work.Whitney.local_push_manifold` is used only to derive `1 ≤ n`, so the
  *non-cut* local push exists for every `n ≥ 1`.
If the cut-form box push (`Work.Whitney.LocalPushNTrans`) likewise needs no more than `2 ≤ n`
(its design constraints are dimension-independent), then the compact *surface* case follows from
the same endgame as `n ≥ 3` — the insertion, the general position and the (two-double-point)
cancellation all being available for `n = 2` — and the classical "classification of closed
surfaces" route, planned earlier for `n = 2`, can be dropped.  What is still missing for that
branch:

* a `2 ≤ n` version of the interface definitions and of the endgame plumbing (mechanical: the
  interfaces of `EndgameNF.lean`/`EndgameNFTrans.lean` begin with `∀ (hn : 3 ≤ n)`);
* `Work.Whitney.exists_disjoint_arcs_into_ball` (delegated this session, in flight): for a compact
  connected `n`-manifold (`2 ≤ n`) two disjoint arcs from `p₁`, `p₂` into a prescribed open
  neighbourhood of a point, avoiding a finite set — the surface case needs the (missing)
  path-connectedness of the complement of an arc in a surface, which is why its statement is
  `2 ≤ n` rather than `3 ≤ n`;
* the cut push for `n = 2`.

Also recorded in `Submission/Work/Noncompact/NOTES_noncompact_plan.md`: the strong clause
`ψ '' (f '' U₂) ∩ f '' univ = ∅` of `Work.Whitney.local_push_manifold` does **not** mean that a cut
push removes a single double point without creating one: the compensating double point sits in the
transition shell of the bump (outside the plateau `U₂`), which is exactly why the cut region of a
cut push must contain the whole support of `ψ` and why the double point count can only change by
`2` at a time.

# SESSION 11: the atlas-free endgame is stated; its two inputs are proved

The two inputs listed in SESSION 10 are now **proved** (delegated, both sorry-free and imported
above):

* `Work.Whitney.hasInsertionNF` (`Submission/Work/Whitney/hasInsertionNF.lean`) — the insertion step
  at the level of `Work.Whitney.HasInsertionNF` (atlas-free, sign-free);
* `Work.Whitney.hasPushNF_of_localPush` (`Submission/Work/Whitney/hasPushNF_of_localPush.lean`) —
  the push interface `Work.Whitney.HasPushNF` from the *local* push `Work.Whitney.LocalPushNF`.

Hence the compact case for `n ≥ 3`, **orientable or not**, is reduced to the single statement
`Work.Whitney.LocalPushNF n U` (for every compact open `U`), i.e. verbatim the cut-form local push
`Work.Whitney.exists_local_push_cut_full` whose *transverse* half is additionally available in a
fully proved form: see `Submission/Work/Whitney/NOTES_local_push_manifold_route.md` and the marked
placeholder `Work.Whitney.LocalPushNTrans` (`LocalPushNF` + the transversality hypothesis), which is
all the endgame needs (every map in the endgame has `Work.Whitney.TransDP'`, converted to
transversality by `Work.Whitney.pairDet_ne_zero_iff`).

# SESSION 10: the endgame needs NO orientations

`Submission/Work/Whitney/EndgameNF.lean` (module `Submission.Work.Whitney.EndgameNF`, imported
above) re-runs the whole endgame of the compact case **without any orientation input**:

* `Work.Whitney.TransDP'` -- every double point is transverse, certified by two *smooth* charts
  (`Work.Whitney.IsSmoothChart`, no atlas);
* `Work.Whitney.HasPushNF` -- the push (`Work.Whitney.HasAmbientPushData`, with the irrelevant
  `A`/`hA`/`hsign` hypotheses of `Work.Whitney.HasAmbientPush` dropped);
* `Work.Whitney.HasInsertionNF` -- the insertion step (atlas-free form of
  `Work.Whitney.InsertedDoublePoint`, no sign field);
* `Work.Whitney.HasCancelNF` -- the cancellation, atlas-free;
* `Work.Whitney.hasCancelNF_of_hasPushNF` (**proved**) -- the push gives the cancellation, directly
  from the already proved `Work.Whitney.cancellation_of_pushData` (whose hypotheses are
  orientation-free);
* `Work.Whitney.exists_reduce_double_points_NF` (**proved**) -- insertion + cancellation remove one
  double point and preserve `SimpleDP` and `TransDP'`;
* `Work.Whitney.hasReduceNF_of`, `Work.Whitney.exists_embedding_of_reduce_NF` (**proved**) -- the
  iteration;
* `Work.Whitney.transDP'_of_range` (**proved**) -- intrinsic transversality gives the `TransDP'`
  certificate, using `Work.Whitney.isSmoothChart_chartAt` (so the generic-position input
  `Work.Whitney.exists_simple_transverse_immersion` is usable directly);
* `Work.Whitney.exists_embedding_of_compact_connected_NF`, `Work.Whitney.exists_embedding_of_compact_NF`
  (**proved**) -- the compact case for `n ≥ 3`, **orientable or not**, modulo exactly two inputs:
  `Work.Whitney.HasPushNF` and `Work.Whitney.HasInsertionNF`.

**Why no orientation is needed** (the key finding of this session, visible in the existing code):
the Whitney move as constructed in this workspace is a *cut-and-paste* along a "finger/tongue"
(`Work.Whitney.ambient_push_data_full` + `Work.Whitney.cancellation_of_pushData`), not the classical
move across an embedded Whitney disc.  Its docstring records -- and `grep` confirms -- that the
bigon arcs `γ₁, γ₂`, the oriented atlas `A` and the sign hypothesis `hsign` are **never used**: the
geometric content is purely local at the two double points (the shadow-pair analysis of
`NOTES_shadow_pairs_obstruction.md` shows what the local push must satisfy, and it is
sign-independent).  Consequently:

* the "sign" chapters (`Work.Whitney.OrientedAtlas`, `PairDet`, `OppositeSign`, `OppositeType`,
  `ArcFraming`, `exists_isArcChain`, `exists_oppositeType_of_insertion`, ...) are **not needed** by
  the endgame; they remain in the tree as proved alternatives/documentation and as the classical
  formulation of the framing condition;
* the non-orientable `n ≥ 3` case is **not** a separate branch: it is covered by
  `Work.Whitney.exists_embedding_of_compact_NF`;
* the two remaining inputs for the compact case are
  1. `Work.Whitney.HasInsertionNF`, whose proof is `Work.Whitney.exists_insertedDoublePoint` with
     the atlas replaced by `chartAt` (delegated: `Submission/Work/Whitney/hasInsertionNF.lean`);
  2. `Work.Whitney.HasPushNF`, which follows from the *local* push `Work.Whitney.LocalPushNF`
     (verbatim the statement of `Work.Whitney.exists_local_push_cut_full`) via
     `Work.Whitney.hasPushNF_of_localPush` (delegated:
     `Submission/Work/Whitney/hasPushNF_of_localPush.lean`; the proof is
     `Work.Whitney.ambient_push_data_full`'s assembly with the unused `A`/`hsign` erased).
  The *entire* remaining mathematical content of the compact case is therefore the local Whitney
  push at one double point (`Submission/Work/Whitney/local_push_cut_transverse_full.lean`,
  `.../local_push_cut_nontransverse_full.lean`),
  whose proof is in progress elsewhere in the fleet.

The branch structure of the target is therefore now:

* `n = 1`: done (`Work.OneDim.exists_embedding_euclidean_two`).
* compact `n ≥ 3`: `Work.Whitney.exists_embedding_of_compact_NF`, modulo `HasInsertionNF` and
  `LocalPushNF` (no orientability hypothesis!).
* non-compact (any `n`): open; mechanism in item 2 below.
* compact `n = 2`: open; mechanism in item 3 below (the classification of closed surfaces).

3. **Compact surfaces (`n = 2`).**  The Whitney trick fails (`2 + n < 2n` needs `n ≥ 3`), and no
   cheap substitute is known to us: the classical proof embeds the sphere, the projective plane and
   the Klein bottle explicitly and uses the classification of closed surfaces (connected sums).
   This is a separate project.  Observe that the *non-compact* `n = 2` case is covered by (2), and
   that `n ≥ 3` covers every other dimension.

## SESSION 13: the non-compact case reduced to the *compression* of the domain

### The reduction (proved)

`Submission/Work/Noncompact/Compression.lean` (module `Submission.Work.Noncompact.Compression`),
sorry-free:

* `Work.Noncompact.HasCompression n M` -- the geometric interface: for every closed discrete set
  `B ⊆ M` (i.e. `∀ K, IsCompact K → (B ∩ K).Finite`) there is a smooth self-embedding `φ : M → M`
  with injective `mfderiv` such that `B ∩ closure (range φ) = ∅`.
* **`Work.Noncompact.exists_embedding_euclidean_of_compression`** -- for `n ≥ 2` and `M` T2,
  second countable, nonempty: `HasCompression n M` implies the existence of a smooth embedding
  `e : M → ℝ^{2n}` with injective `mfderiv`.

The proof takes the proper general-position immersion `h` of
`Work.Noncompact.exists_proper_immersion_transverse`, its finite fibres and locally finite double
point set (`Work.Noncompact.finite_preimages_and_discrete_doubleSet`), chooses one "kept" point per
value of `h` (so `B` = the other preimages is closed discrete), applies the compression to `B` and
shows:

* `h` is injective on `φ '' univ` (each double point pair loses one point);
* hence `h ∘ φ` is injective, smooth and an immersion;
* and `h ∘ φ` is an *embedding*: if `x` were a limit of an escaping sequence with images converging
  to `(h ∘ φ) x`, the limit `w` of the (compactly lying) `φ`-images satisfies `h w = h (φ x)` with
  `w ≠ φ x`, hence `w ∈ B` (the kept point of its fibre is `φ x`), contradicting
  `B ∩ closure (range φ) = ∅`.

### The remaining geometric input (delegated)

`Work.Noncompact.hasCompression` (`Submission/Work/Noncompact/hasCompression.lean`), for `M`
connected, non-compact, `n ≥ 2`: **the whole hard geometric content of the non-compact case**
(tubes to infinity through the closed discrete set, a transverse-coordinate-dependent shrink of
each tube).  The complete design -- including the two "reality checks" that a one-sided and a
bounded tube both fail, and that a shift not depending on the transverse coordinate is always
surjective -- is written up in `Submission/Work/Noncompact/NOTES_compression.md`; the interface
was reviewed and approved by two readers.

### Structure of the target's proof (state after this session)

* `n = 1`: done.
* `n ≥ 2`, `M` **connected**:
  * compact (needs `n ≥ 3`): the compact endgame modulo the local push;
  * non-compact (any `n ≥ 2`): `exists_embedding_euclidean_of_compression` +
    `hasCompression`;
  * compact `n = 2`: open (classification of closed surfaces, or a new idea).
* `n ≥ 2`, `M` **disconnected**: reduce to the connected components.
  * all components compact: `Work.Embedding.exists_embedding_of_components` (proved) does this.
  * general `M`: the countable version `Work.Embedding.exists_embedding_of_components_general`
    (delegated, `Submission/Work/Embedding/exists_embedding_of_components_general.lean`) glues the
    embeddings of the connected components into pairwise disjoint balls: the components of a
    manifold are open and clopen (and countable, since `M` is second countable), each is a
    connected open submanifold to which the connected case applies, and composing with a shrinking
    diffeomorphism of `R^{2n}` into a ball plus a translation places the images in disjoint balls,
    which makes the assembled map smooth, injective, an immersion and an embedding.  Hence the
    target's proof is: `n = 1` direct, otherwise reduce to the connected components and use the
    compact / non-compact connected cases there.

## SESSION 14: the architecture is complete; the compact push interface is corrected

### The full architecture typechecks

`_wire_full.lean` (scratch file at the workspace root, not part of the library) contains the whole
proof of the target with exactly three `sorry`s, and it **compiles**: `n = 1` direct, otherwise the
countable component reduction `Work.Embedding.exists_embedding_of_components_general`, and then for
each connected component `U`:

* `U` compact: `Work.Whitney.exists_embedding_of_compact_of_pushNFT hn (hpush U)` (the collar push
  interface, see below), or `..._of_localPush` for the local one;
* `U` non-compact: `Work.Noncompact.exists_embedding_euclidean_of_compression hn (hcomp U)`.

So the remaining content of the target is exactly: (a) the push interface for compact connected
pieces with `n ≥ 3`; (b) `Work.Noncompact.HasCompression` for non-compact connected pieces;
(c) compact `n = 2` (the classification of closed surfaces).

### The compact case packaged (new)

`Submission/Work/Whitney/compact_of_localPush.lean` (sorry-free, imported above):

* `Work.Whitney.exists_embedding_of_compact_of_pushNFT` -- the compact case from the **collar
  (bigon) push** `Work.Whitney.HasPushNFT`; **this is the interface to fund**;
* `Work.Whitney.exists_embedding_of_compact_of_localPush` -- the same from the local cut-form push
  `Work.Whitney.LocalPushNTrans`; kept for the record.

### The local cut-form push is (almost certainly) impossible

`Submission/Work/Whitney/NOTES_compact_route_obstruction.md` records the reason, which cost a
session and which redirects the compact branch:

* the cut clause of `LocalPushNTrans` forces the pushed `p₂`-sheet to avoid the `p₁`-sheet *inside
  the support* of `ψ` (the frontier clause plus the clopen argument forces `K ⊇ P₁`, `K ∩ P₂ = ∅`);
* the two sheet pieces inside a ball `B ⊇ support ψ` are complementary-dimensional disks with
  boundaries on `∂B` (hence fixed by `ψ`) meeting transversely exactly at the double point `q`,
  which *is* displaced; their relative intersection number in `(B, ∂B)` is `±1` and is invariant
  under ambient isotopies fixing `∂B`, so they can never be separated;
* hence `ψ` cannot exist, and the route
  `LocalPushNTrans → hasAmbientPushData_of_localPushTrans → cancellation` is blocked.  This is the
  classical reason why the Whitney move is *not* local at one double point: it is the Whitney disc
  (the bigon between the two double points) that makes room.  That is precisely the collar push
  `HasPushNFT`.

### The push interface is signed (new, SESSION 14 cont.)

Both readers of the FOLLOW-UP review agreed that the *sign-free* `HasPushNFT` is false: a same-type
pair of double points has total degree `±2` on the bounding sphere and cannot be disengaged, and
nothing in the clean-region/arc hypotheses forces opposite type (`NOTES_whitney_move_mechanism.md`
§1, `NOTES_push_map_requirements.md` req. 3, `NOTES_framing_for_push.md`).

Accordingly, `Submission/Work/Whitney/PushSigned.lean` (sorry-free, new) defines

* `Work.Whitney.HasPushSigned n M` -- `HasPushNFT` with the framing hypothesis
  `Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂` added; its conclusion is the ambient-diffeomorphism
  data `Work.Whitney.HasAmbientPushData`.

and the sound target for the compact branch is

* `Work.Whitney.hasPushSigned_holds` (delegated): `HasPushSigned n M`.

The endgame can supply the framing hypothesis: `Work.Whitney.exists_oppositeType_of_insertion`
(proved) makes the inserted partner opposite-typed, so the pairs the endgame cancels are always
opposite-typed -- the (still to be written) signed endgame is the plumbing that replaces the
sign-free `HasInsertionNF`/`HasPushNFT` route.

`Submission/Work/Whitney/CancelSigned.lean` (sorry-free, new) is the first segment of that signed
plumbing:

* `Work.Whitney.HasCancelSigned n M` -- `HasCancelNFT` with the framing hypothesis added;
* `Work.Whitney.hasCancelSigned_of_hasPushSigned` -- the signed push gives the signed cancellation,
  by the (orientation-free, proved) `Work.Whitney.cancellation_of_pushData`.

So the endgame's cancellation interface is now available on the sound, signed route.  What remains
of the plumbing (next segment) is the *signed insertion* interface: the endgame must obtain the
framing hypothesis for the arcs of its clean region from the insertion step, which is what
`Work.Whitney.exists_oppositeType_of_insertion` (proved) provides by choosing between the two
candidate inserted maps of `Work.Whitney.exists_addDoublePoint_both_signs_located`.

`Submission/Work/Whitney/InsertSigned.lean` (new) states that interface:
`Work.Whitney.HasInsertionSigned n M` -- the insertion produces *two* candidates `fp`, `fm` with the
same inserted pair `(p', q')`, both with the full gluing structure, such that for every pair of arcs
joining `p₁, p₂` to `p', q'` one of the two is `OppositeType` along those arcs.  Its discharge
(`Work.Whitney.hasInsertionSigned`, delegated, with the necessary `2 ≤ n`) is the next segment; the
readers of the review caught that the lower bound is required (the interface is false at `n = 0`).  Its discharge is now **proved**:
`Work.Whitney.hasInsertionSigned` (`Submission/Work/Whitney/hasInsertionSigned.lean`).

## SESSION 15: the signed endgame is assembled; the push and `n = 2` are handed out

### The signed endgame is now complete modulo the push alone

`Submission/Work/Whitney/EndgameSigned.lean` (module `Submission.Work.Whitney.EndgameSigned`,
sorry-free, imported above) is the signed analogue of `EndgameNFTrans`, built on the two proved
inputs `Work.Whitney.hasInsertionSigned` and `Work.Whitney.hasCancelSigned_of_hasPushSigned`:

* `Work.Whitney.hasReduceNFT_of_signed` -- `HasInsertionSigned → HasCancelSigned → HasReduceNFT`;
* `Work.Whitney.exists_embedding_of_compact_connected_signed` -- the compact connected branch
  (`n ≥ 3`, no orientability hypothesis) from `HasPushSigned`, `HasInsertionSigned` and a
  general-position immersion;
* `Work.Whitney.exists_embedding_of_compact_signed` -- the compact branch
  (`n ≥ 3`) from `HasPushSigned`/`HasInsertionSigned` on the compact open submanifolds.

The signed reduction step `Work.Whitney.exists_reduce_double_points_signed`
(`Submission/Work/Whitney/exists_reduce_double_points_signed.lean`, sorry-free, imported) is the
missing segment that was in flight: it chooses the two bigon arcs *before* the insertion candidate
(the finite set avoided is `doublePreimages f p' q'`, the same for both candidates
`Work.Whitney.HasInsertionSigned` produces) and then uses the framing alternative of
`HasInsertionSigned` to select the candidate the signed cancellation applies to.

So the compact `n ≥ 3` branch of the target is now reduced to the SINGLE input

  `Work.Whitney.HasPushSigned n M`   (compact `M`, `n ≥ 3`),

everything below it being proved and assembled.

### The push: two attempts are running, plus a design note

* `Submission/Work/Whitney/NOTES_CUT_PUSH_DESIGN_S15.md` -- the design.  Its two structural points
  are worth repeating: (i) the cut region `W₀` of the conclusion `HasAmbientPushData` need NOT be a
  collar of the arc -- two tiny balls around `p₂` and `q₂` are allowed, which *localises* the
  construction at the two double points (the arc data then enters only through the framing
  hypothesis); (ii) the frontier clause is the only difference from the PROVED
  `Work.Whitney.local_push_manifold`, and the framing hypothesis `OppositeType` is exactly what
  repairs it.
* child `Work.Whitney.hasPushSigned_holds` (the single statement) and the subproject
  `Submission/Work/Whitney/CutPush/` (the area, with the note above as its specification).

### `n = 2` (compact) handed out

The subproject `Submission/Work/DimensionTwo/` owns the missing theorem
`Work.DimensionTwo.exists_embedding_euclidean_four` (every compact surface embeds in `ℝ⁴`), with the
route described in the request (reduce to closed surfaces; classify them via the polygonal normal
form, reusing the architecture of the completed 1-dimensional classification
`Submission/Work/OneDim/`; or a handle-decomposition route).  Note that the *non-compact* `n = 2`
case needs nothing new: it is covered by the compression reduction below.

### The non-compact branch

`Work.Noncompact.exists_embedding_euclidean_of_compression` (proved) reduces the non-compact case
(for every `n ≥ 2`) to `Work.Noncompact.HasCompression`, whose proof chain
(`Submission/Work/Noncompact/CompressionTube/`, `.../Routing/`, `.../ProperLine/`) is being built by
another colleague's fleet; at the time of writing the two open obligations are the "two lanes inside
a canal" lemma (`CompressionTube/twoLanes_of_canal.lean`) and the plug-in point of
`CompressionTube/exists_compression_tube.lean`.  Nothing in `Submission.lean` imports that chain yet,
so the target's file stays green.

### THE ASSEMBLY IS VERIFIED (scratch files at the workspace root)

`_wire15d.lean` (not part of the library) contains the *whole proof of the target* with

* the `n = 1` case taken from `Work.OneDim.exists_embedding_euclidean_two`;
* the connected-component reduction `Work.Embedding.exists_embedding_of_components_general`;
* the compact `n ≥ 3` branch from `Work.Whitney.exists_embedding_of_compact_connected_signed`
  instantiated with `Work.Whitney.hasPushSigned_holds` (the delegated push),
  `Work.Whitney.hasInsertionSigned` and `Work.Whitney.exists_simple_transverse_immersion`;
* the non-compact branch from `Work.Noncompact.exists_embedding_euclidean_of_compression`
  instantiated with `Work.Noncompact.hasCompression n hn2 U hUc`;
* the compact `n = 2` branch left as a HYPOTHESIS `h2`;

and **it compiles** (`lake env lean _wire15d.lean`, rc = 0).  So all the typeclass/instance
bookkeeping of the final assembly is done and machine-checked; instantiating `h2` with the
`DimensionTwo` deliverable is the only remaining wiring step, and `_wire15c.lean` shows that the
transport from the `Fin 2` statement to the `Fin n` statement with `n = 2` is a one-line `subst`.
Consequently: **as soon as the three delegated inputs are sorry-free, the target is a copy of
`_wire15d.lean` with `h2` discharged by `_wire15c`.**

Axiom audit (`_ax15.lean`): every lemma of the assembled chain
(`Work.OneDim.exists_embedding_euclidean_two`,
`Work.Embedding.exists_embedding_of_components_general`,
`Work.Whitney.exists_embedding_of_compact_signed`, `..._connected_signed`,
`Work.Whitney.hasReduceNFT_of_signed`, `Work.Whitney.exists_reduce_double_points_signed`,
`Work.Whitney.hasInsertionSigned`, `Work.Whitney.hasCancelSigned_of_hasPushSigned`,
`Work.Noncompact.exists_embedding_euclidean_of_compression`,
`Work.Noncompact.exists_proper_immersion_transverse`,
`Work.Whitney.exists_simple_transverse_immersion`) depends only on
`propext, Classical.choice, Quot.sound` -- no hidden axioms anywhere in the development.

### State of the target's proof

* `n = 1`: done (`Work.OneDim.exists_embedding_euclidean_two`).
* `2 ≤ n`, per connected component `U` (via `Work.Embedding.exists_embedding_of_components_general`):
  * `U` compact, `n ≥ 3`: `Work.Whitney.exists_embedding_of_compact_signed` + `HasPushSigned`;
  * `U` compact, `n = 2`: the `DimensionTwo` subproject;
  * `U` non-compact, any `n ≥ 2`: `Work.Noncompact.exists_embedding_euclidean_of_compression` +
    `HasCompression`.

-/

open scoped Manifold ContDiff
open Topology

namespace Submission

/-- The compact 2-dimensional case: Work.Drive.N2.embedding_of_morse_movie (the level-separating movie
construction) fed with the proved Morse inputs. -/
theorem compact_two_embedding
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin 4), ContMDiff (𝓡 2) (𝓡 4) ∞ e ∧ Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 2) (𝓡 4) e x) := by
  obtain ⟨f, hf⟩ := Work.Drive.N2.exists_isMorseDistinct (M := M)
  exact Work.Drive.N2.embedding_of_morse_movie f hf
    (fun a b hcrit => Work.Drive.N2.hasLevelFlow_of_noCritical f hf.1 a b hcrit)
    Work.Drive.N2.morseLemma2

theorem whitney_embedding (n : ℕ) (_hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  classical
  rcases eq_or_ne n 1 with hn1 | hn1
  · subst hn1
    exact Work.OneDim.exists_embedding_euclidean_two
  · have hn2 : 2 ≤ n := by omega
    refine Work.Embedding.exists_embedding_of_components_general (n := n) (by omega) ?_
    intro U hUne
    haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUne
    have hne := hUne.nonempty
    haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
    by_cases hUc : CompactSpace U
    · haveI := hUc
      rcases eq_or_ne n 2 with hn22 | hn22
      · subst hn22
        exact compact_two_embedding (M := U)
      · have hn3 : 3 ≤ n := by omega
        exact Work.Drive.exists_embedding_of_compact_connected_smooth (n := n) hn3
          (Work.Drive.hasPushSignedSmooth_milnor (n := n) (M := U))
          (Work.Whitney.hasInsertionSigned (n := n) hn2)
          (Work.Whitney.exists_simple_transverse_immersion (n := n) hn3)
    · exact Work.Noncompact.exists_embedding_euclidean_of_compression (n := n) hn2
        (Work.Drive.hasCompression_drive n hn2 U hUc)

end Submission
