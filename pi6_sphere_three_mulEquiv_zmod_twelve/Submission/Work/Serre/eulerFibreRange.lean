import Mathlib

-- (The declarations this file needs (`Work.Serre.EulerFibreRange`,
-- `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, …) were moved
-- to the upstream module `Submission.Work.Serre.EulerFibreRoot`; importing *that* instead of
-- `Submission.Work.Serre.thomIsoCylFibreRange` removes the import edge that made the target of
-- `thomIsoCylFibreRange.lean` unprovable (build cycle).  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.)
import Submission.Work.Serre.ThomCylCellStepAltDef
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.GysinFibreRange
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.Serre.periodicity_of_serreFibration
import Submission.Work.Serre.exists_ratCup_iso_zero
import Submission.Work.StemsB.ModelThomStepRat
import Submission.Work.StemsB.CubePairHomology
import Submission.Work.Serre.cubePairRelHomology
import Submission.Work.RatHurewicz.SimplyConnectedBridge
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.cohMapIsoOfRatHomologyIso
import Submission.Work.Serre.pullbackFst_piMapN_bijective
import Submission.Work.Serre.serreK2
import Submission.Work.StemsB.Periodicity
import Submission.Work.Serre.fibreData_pullbackSnd
import Submission.Work.Serre.eulerClass_of_thomBdd
import Submission.Work.Serre.exists_cupWith_of_preimage
import Submission.Work.Serre.cwModelThomCase
import Submission.Work.Serre.thomCylBaseCase
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.ratFibreTransport

set_option synthInstance.maxHeartbeats 400000

/-!
# The Euler-class form of the Gysin theorem, in the range given by the fibre

The target `Work.Serre.EulerFibreRange` (`Submission/Work/Serre/thomIsoCylFibreRange.lean`) is the
*Euler class* form of Serre's Gysin/Thom theorem for a rational spherical fibration, in the range
given by the fibre:

> for a Serre fibration `p : E → B` with `E` rationally acyclic, `B` simply connected and the strict
> fibre `F = p⁻¹{b₀}` a rational `r`-sphere through degree `N`, there is `e ∈ H^{r+1}(B;ℚ)` with
> `x ↦ x ⌣ e : H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` for every `m` with `m + r + 1 ≤ N + 1`.

The *relative* (mapping-cylinder) form of the same statement is `Work.Serre.ThomIsoCylFibreRange`
(`Submission/Work/Serre/GysinFibreRange.lean`): there is a relative class
`U ∈ H^{r+1}(cyl p, E;ℚ)` whose *mixed* cup product with the pullback along the retraction is an
isomorphism in the range.  The implication in the other direction
(`EulerFibreRange → ThomIsoCylFibreRange`) is `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`.

This file proves the *reverse* implication, `ThomIsoCylFibreRange → EulerFibreRange`: given the
relative class `U`, the Euler class `e := (cylInr p)^*(relToAbs U)` makes the cup product an
isomorphism, because (by `Work.StemsB.mixedCup_relToAbs_R`, the naturality of the cup product and
the retraction identity `(cylInr p)^* ∘ (cylRetract p)^* = id`)

  `⌣ e = (cylInr p)^* ∘ relToAbs ∘ (⌣ U) ∘ (cylRetract p)^*`

is a composite of three isomorphisms (`isIso_cohMap_cylInr`, `isIso_relToAbs_succ` — the latter
needs the rational acyclicity of `E` — and the hypothesis on `U`).

## What remains for the target itself

The content of the target is therefore exactly the *relative* statement `ThomIsoCylFibreRange`,
i.e. the classical cell-by-cell Thom isomorphism for the disc-pair fibration of a spherical
fibration in the range given by the fibre.  Its two independent inputs are

* **the additive (`relativised Serre exact sequence`) statement** — for `n + r + 1 ≤ N + 1`,
  `H^{n+r+1}(cyl p, E;ℚ) ≅ H^n(B;ℚ)` (equivalently, by the long exact sequence of the pair and the
  acyclicity of `E`, the periodicity `H^n(B;ℚ) ≅ H^{n-r-1}(B;ℚ)`), the cell-by-cell computation of
  the *degenerate* (one-row) Serre spectral sequence of the disc-pair fibration — see
  `Work.Serre.discPairRelCohIso` below;
* **the class and its multiplicativity** — the `r+1`-class `U` of the disc pair exists cell-by-cell
  (the local input is `Work.StemsB.ModelThomRat` / `Work.StemsB.modelThomRatAll`, the Thom class of
  the trivial pair bundle over an arbitrary base; the obstruction to extending it over the
  `j`-skeleton vanishes for `j ≥ 2`, i.e. because `B` is simply connected and the model may be
  taken with no `1`-cells), and cupping with it is an isomorphism in the range (the cell-by-cell
  five-lemma chase, using the compatibility of the mixed cup product with the connecting maps:
  `Work.StemsB.mixedCup_relToAbs_R`, `Work.Cohomology.cupNaturalH`,
  `Work.StemsB.pairDelta_mixedCup_general_R`).
-/


/-!
## Recorded attack plan (session notes)

**PROVED in this file.** `eulerFibreRange_of_thomIsoCylFibreRange` : the relative
(mapping-cylinder) form of the Gysin theorem implies the Euler-class form.  Together with the
converse (`Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, already in the tree) this shows that
the target `EulerFibreRange` is *equivalent* to `Work.Serre.ThomIsoCylFibreRange`, and hence
(through `Work.Serre.serreE3b_of_thomCyl`) that `EulerFibreRange`, `ThomIsoCylFibreRange` and
`SerreE3b` all say the same thing: the Gysin/Thom theorem of a rational spherical fibration in the
range given by the fibre.

**Two independent inputs remain** (both factored out above):

* `DiscPairRelCohIso` (defined below): the *additive* half -- the cell-by-cell degeneration of the
  Serre spectral sequence of the disc-pair fibration `(cyl p, E) -> B`, whose fibre pair
  `(CF_b, F_b)` has relative rational cohomology concentrated in degree `r+1` through degree `N+1`.
  Because the first page is concentrated on a single line, all higher differentials vanish, so this
  is a *purely additive* statement (no cup products) -- the analogue, for the *disc pair*, of the
  workspace engine `Work.Serre.ratSerrePairComparison` (which handles the *sphere* pair, but only
  in the stable range `b + f` given by the *base's* connectivity).
* the *multiplicativity*: existence of the relative class `U` (the Thom class) and the fact that
  `cup U` is an isomorphism in the range.  The local input is `Work.StemsB.ModelThomRat` /
  `Work.StemsB.modelThomRatAll` (the Thom class of the *trivial* pair bundle over an arbitrary base,
  with its cup-product property -- proved); the global statement is the cell-by-cell five-lemma
  chase over a CW range model of `B`, using the compatibility of the mixed cup product with the
  connecting maps (`Work.StemsB.mixedCup_relToAbs_R`, `Work.Cohomology.cupNaturalH`,
  `Work.StemsB.pairDelta_mixedCup_general_R`).  Simple connectivity of `B` is used as
  *orientability*: the model may be taken with no `1`-cells, so there is no monodromy and the
  obstruction to extending `U` over the `j`-skeleton vanishes for `j >= 2`.


### The Thom-class extension over a range model without 1-cells (worked out)

Let `Gamma` be a range model of `B` built from a point by attaching cells of dimension `j >= 2`
(possible because `B` is simply connected: `pi_0 = pi_1 = 0`), with `g : Gamma -> B` the comparison
map, `q : E_Gamma -> Gamma` the pullback of `p`, and `(D_j, E_j)` the disc-pair bundle of `q` over
the `j`-skeleton (the bottom copy `E_j = q^{-1}(Gamma_j)`, the disc bundle
`D_j = cyl(q|_{E_j})`).

**Extension step.**  Given a Thom candidate `U_j` in `H^{r+1}(D_j, E_j)`, the obstruction to
lifting it to `U_{j+1}` in `H^{r+1}(D_{j+1}, E_{j+1})` lives (long exact sequence of the triple
`(D_{j+1}, D_j union E_{j+1}, E_{j+1})`, with the excision identification
`H^*(D_j union E_{j+1}, E_{j+1}) = H^*(D_j, E_j)`) in

    `H^{r+2}(D_{j+1}, D_j union E_{j+1})  =  direct sum over the (j+2)-cells of
       H^{r+2}(D^{j+2} x CF, boundary x CF union D^{j+2} x F)`

and, by the triviality of `q` over the cell (fibre-homotopy triviality over a disc, from the
homotopy lifting property), the summand is

    `H^{r+2-(j+2)}(CF, F) = reduced H^{r-j-1}(F)`,

which vanishes for every `j >= 2`: for `2 <= j <= r` because `0 < r+1-j < r` and `H_t(F;Q) = 0`
for such `t` (`hfib`), for `j = r+1` because `H^0_reduced(F;Q) = 0` (`hfib0` gives `F` path
connected), and for `j > r+1` because the degree is negative.  **So the extension is unobstructed
for every cell of dimension `>= 2`** — this is exactly where the two fibre hypotheses
(`hfib`, `hfib0`) are consumed by the *multiplicativity* half, and it is also why the model must be
taken with no 1-cells (`B` simply connected).

**Cell input.**  The class exists over one cell by `Work.StemsB.modelThomRatAll` (the Thom class of
the trivial pair bundle over an arbitrary base, with its cup-product property), transported along
the homeomorphism between the model cell `D^{j+2}` (`Work.RatHurewicz.cellDisk`) and the cube, and
along the fibre-homotopy trivialisation of `q` over the cell.  Multiplicativity over the cell is
the local model's `Function.Bijective` statement.

**Induction.**  Starting from the 0-skeleton (`Gamma_0` a point, where `U_0` is the generator of
`H^{r+1}(CF, F) = Q`, i.e. the fibre hypothesis `hgen` transported by `hfib`), the extension step
produces `U_j` for every `j`, hence `U` on `Gamma`.  The five-lemma chase (with the long exact
sequences of the pairs of skeleta on both sides, related by the mixed cup product and its
compatibility with the connecting maps, `Work.StemsB.pairDelta_mixedCup_general_R`) then identifies
`cup U` with the isomorphism produced on the base side, giving `ThomIsoCylFibreRange`, and the
reduction proved above gives the target.


**PROVED below: the cell-level input** `modelPairRelCohIso`
(`H^{n+r+1}(B × R^{r+1}, B × S^r; Q) ≅ H^n(B;Q)`), the group-level form of the proved model Thom
class `Work.StemsB.modelThomRatAll`.  This is the local input of the cell-by-cell construction over
the *trivial* pair, i.e. over one cell of the range model.

**Next pieces to hand out (in this order).**

1. *Suspension / relative Künneth for the cell pair.*  The extension step consumes the vanishing of
   `H^{r+2}` of the disc-pair bundle over a single cell relative to its boundary-and-sphere part,
   which is `H^(r+2-(j+2))(CF, F) = reduced H^(r-j-1)(F)`.  The needed statement is the
   pair-suspension `H^{m+j+2}(D^{j+2} × P, boundary × P ∪ D^{j+2} × Q) ≅ H^m(P,Q)` for *nice* pairs
   `(P,Q)` (cube/disc pairs — the pair of an *arbitrary* space fails, see
   `Submission/Work/Serre/TICFR_PLAN.md`).  The workspace's `Work.StemsB.CubePairCohomology`
   (`SerreCohomologyTargets.lean`) is this statement for cubes and is still an unproved `Prop`; the
   homological counterpart `Work.StemsB.cubePair_main`-style results and
   `Work.StemsB.serreSphere_collar_iso` are proved and are the model for it.
2. *The extension step.*  For a Serre fibration `q : E → attachCells n Y ι f` and a class over the
   old part `Y`, the obstruction to extending lives in `H^{r+2}(D_new, D_old ∪ E_new)`, which by
   (1) and additivity over the cells is a sum of `H^(r-j-1)`-reduced groups of the fibre, vanishing
   for every cell dimension `j + 2 ≥ 2`.  Stated over `Work.RatHurewicz.attachCells` /
   `attachIncl` / `cellMap`, with the old class in
   `RelCoh Q (r+1) (cyl (Pullback (attachIncl ..) q)) (range cylIncl)`.
3. *The five-lemma assembly* over a tower of such attachments (the range model of `B`), giving
   `ThomIsoCylFibreRange`, hence the target through the reduction proved above.

**Base case `k = 0` of the pair statement: PROVED below as `cubePairRelHomology_zero`.**  The pair
`(I^0 × P, I^0 × Q)` is the pair `(P,Q)` through the homeomorphism of pairs `cubeZeroHomeo P`
(`Prod.snd`, inverse `p ↦ (fun _ => 0, p)`); the proof is `Work.StemsB.cubeBdryK_zero` +
`Set.empty_union`, the `eqToIso (congrArg ...)` set transport (as in `Work.StemsB.cubePairZero_iso`),
`Work.StemsB.isIso_relChainsMapOf_homeomorph` and `HomologicalComplex.homologyMapIso`.

Two traps that cost time here, recorded so they are not re-hit:
* the lemma is about `Work.StemsB.relChainsMapOf (f) (A) (B) (hf)`, *not* about the same-named
  `Work.Cohomology.relChainsMapOf`, which instead takes the two `TopCat`s and a pair map explicitly;
* the `whnf` blow-up (deterministic, independent of `maxHeartbeats`) came from *unresolved implicit
  arguments* on `sphHomeoHom` and `relChainsMapOf`; pinning `X`, `Y` on both
  (`(X := TopCat.of (CubeP P 0)) (Y := TopCat.of P)`) removes it.  Also `asIso f` does *not* accept
  an instance as an extra positional argument (use `@asIso` with the full argument list if the
  instance must be given by hand).

**The `k → k+1` step (targets).**  `Work.StemsB.cubePair_main`'s induction runs
`Work.StemsB.cubePairStep_iso` (the Mayer–Vietoris step: built from `Work.Cohomology.relMVSmallIso`,
`Work.Cohomology.relMVδ` via `Work.StemsB.isIso_relMVδ_cube`, and
`Work.StemsB.relMVH₁_iso_slabMid`, all driven by `Work.Cohomology.relMV_shortExact X A U V`) followed
by `Work.StemsB.midRelIso` (the middle-slab identification along `Work.StemsB.midParam`) and then the
induction hypothesis.  The pair form of the statement needs **the same ingredients relativised to the
extra set `A := I^{n+1} × Q`**: because `relMV_shortExact` already carries the extra subset `A`, the
step should read

  `H_{m+1}(I^{n+1} × P , ∂I^{n+1} × P ∪ I^{n+1} × Q) ≅ H_m(slabMid , slabMidi ∪ slabMid × Q)`,

with `Q` riding along unchanged through `midRelIso`'s `midParam` step.  Sanity anchors: `Q = ∅`
reduces verbatim to the proved `Work.StemsB.cubePairStep_iso` / `Work.StemsB.midRelIso`, and the
`k = 0` floor is `cubePairRelHomology_zero`, proved above.  Beware the two set conventions:
`cubeBdryK Y k : Set (CubeP Y k)` (the `k`-cube's own boundary, used in `cubePair_main` and in the
base case above) versus `cubeBdry Y n : Set (CubeP Y (n+1))` (the shifted form used inside
`cubePairStep_iso`).

**Ingredient 1 of 3 for `k → k+1`: DONE.**  `relMVH₁_iso_slabMid_rel` (proved below) and its set
identity `slabMidi_union_second` (proved below) relativise `Work.StemsB.relMVH₁_iso_slabMid` to
the pair `(Y,Q)`.  The other two "ingredients" need **no relativisation at all**: `Work.Cohomology.relMVSmallIso`
(`relMVH₃ X A U V n ≅ (relChains X A).homology n`) and `Work.Cohomology.relMVδ` are already
stated for an *arbitrary* `A ⊆ X`.  What is cube-specific is only their *proof inputs*:
`Work.StemsB.isIso_relMVδ_cube` is obtained from
`Work.StemsB.isZero_relMVH₂_cube`, which comes from `Work.ThreeConnected.Excision.isZero_homology_biprod`
applied to `Work.StemsB.isZero_relSmallChains_slabA` / `..._slabB`, and from
`Work.ThreeConnected.Excision.relMV_iso_of_acyclic` — both of those Excision lemmas are generic.
**RETRACTION (important, and it un-kills the Mayer–Vietoris route).**  An earlier version of this
note claimed that the relative Mayer–Vietoris slab decomposition cannot be relativised to the second
pair `(Y,Q)`, on the strength of the `n = 0` computation `H_*([0,3/4) × Y , {0} × Y ∪ [0,3/4) × Q)`,
which I asserted to be `H_*(Y,Q)`.  **That computation was wrong**: the projection `[0,3/4) × Y → Y`
is a homotopy equivalence carrying the subspace `{0} × Y` onto *all* of `Y`, so the pair is
`(Y, Y ∪ ...) ≅ (Y,Y)` and the group **vanishes**.  The in-flight sibling file
`Submission/Work/Serre/cubePairRelHomology.lean` confirms this: with the *same* `slabA`/`slabB` cover it
proves the relativised vanishings `isZero_relChains_slabBigA` / `isZero_relChains_slabBigB` (for
`slabBigA = (Subtype.val) ⁻¹' (slabA ∩ (cubeBdry ∪ I^{n+1} × Q))`, exactly the set of that
computation) and is assembling `cubePairRelHomology` from them.  So the two proved lemmas above,
`slabMidi_union_second` and `relMVH₁_iso_slabMid_rel`, **are** on the critical path after all, and
`isZero_relSmallChains_slabA`/`_slabB` relativise as originally planned.  Read the sibling file before
re-deriving any of this.

**The LES-comparison route, with the exact API (checked, so the next pass starts here).**

* the two long exact sequences: the **triple** LES of `(I^k × P, ∂I^k × P ∪ I^k × Q, ∂I^k × P)` via
  `Work.Cohomology.Endgame.tripleShort (X) (A A') (h)` (or
  `Work.Cohomology.pd_triple.tripleShort`; `Work.Serre.RatTower.tripleShortR` is the ℚ-valued
  variant), and the **pair** LES via `Work.StemsB.relChainsR_exact₁/₂/₃ (X) (A) (n)`;
* identification 1 (no excision): the total term of the triple sequence is
  `H_{j+k}(I^k × P, ∂I^k × P ∪ I^k × Q)`, which *is* the left-hand side of `cubePairRelHomology` in
  the `relChains (CubeSpace P k) (cubeBdryK P k ∪ I^k × Q)` spelling — `cubeBdryK P k` and
  `∂I^k × P` are the same set (`Cube.boundary (Fin k)`);
* identification 2 (excision): `H_*(∂I^k × P ∪ I^k × Q, ∂I^k × P) ≅ H_*(I^k × Q, ∂I^k × Q)` — the
  set `∂I^k × Q = (∂I^k × P) ∩ (I^k × Q)`; the tool is
  `Work.Cohomology.excision_relChainsMap_isIso (X) (U A) (hU) (hA) ...` (or the small-chains
  excision `Work.Cohomology.relMVSmallIso`-machinery, which is what the cube development uses);
* the three remaining vertical maps are the **proved space case** `Work.StemsB.cubePair_iso` for
  `P`, the same for `Q` (after identification 2), and the target itself; the five lemma is
  `Work.Serre.RatTower.fiveLemmaTau2` for ℚ-valued short complexes (a ℤ-valued five lemma may have
  to be extracted from `Submission/Work/Serre/_e3a/stmt5.lean:fiveLemma_of_shortExact`).

**Five-lemma bookkeeping (checked, so the next pass does not re-grep).**  Mathlib has **no** five
lemma (`grep -rn five Mathlib/Algebra/Homology/` and `.../ShortComplex/` are both empty); what it has
is the short-exact-sequence homology machinery (`ShortComplex.homologyMap`,
`ShortComplex.ShortExact.δ`, and the `IsIso (homologyMap φ)` instances at
`Mathlib/Algebra/Homology/ShortComplex/Homology.lean:546–562`).  The workspace has a *proved*
ℚ-valued five lemma `Work.Serre.RatTower.fiveLemmaTau2` (isomorphisms in degrees `< N`, epi in
degree `N`) and an *unproved* ℚ statement
`Submission/Work/Serre/_e3a/stmt5.lean:fiveLemma_of_shortExact`.  **RESOLVED:** the ℤ-valued five lemma was delegated and is now
**proved**: `Work.Serre.fiveLemmaInt` in `Submission/Work/Serre/fiveLemmaInt.lean`
(import it; statement: isomorphism of the first and third columns in degrees `< N` plus epis in
degree `N` give isomorphism of the middle column in degrees `< N` and an epi in degree `N`).
So the comparison square of the `k → k+1` step can be run directly over **ℤ**, and the ℚ-valued
detour (`CubePairRelHomologyRat` below, plus the *proved* `Work.Serre.RatTower.fiveLemmaTau2`) is
no longer needed — it is kept only as a cross-check.

**DONE — both relativised small-chains vanishings are PROVED below**
(`isZero_relSmallChains_slabA_rel`, `isZero_relSmallChains_slabB_rel`).  Each is the `C`-generic
`Work.Cohomology.Endgame.relSmallChains_iso_relChains` composed with
`IsZero.of_iso (Work.Serre.isZero_relChains_slabBigA/B k Y Q m) ((… .mapIso e))` — note the *plain*
`mapIso e`, not its `.symm` (the reversed orientation is what failed earlier).  They import the
sibling's now-green `Submission.Work.Serre.cubePairRelHomology`, which also forced renaming my two
duplicates of its declarations to `cubeZeroHomeo'` / `cubePairRelHomology_zero'` (same namespace
`Work.Serre`).

**RETRACTED AGAIN (the "monotonicity" shortcut is invalid).**  An earlier note here claimed the two
relativised vanishings reduce to the proved `Work.StemsB.isZero_relChains_slabA` by monotonicity
(`A' ⊆ A ⟹ IsZero (H_m(X,A')) ⟹ IsZero (H_m(X,A))`).  **That implication is false**: the map
`relChains X A' → relChains X A` is degreewise surjective on chains, but a degreewise surjective
chain map need not be surjective on homology.  Review counterexample: `A' = {pt} ⊆ S¹ = A ⊆ D²`
gives `H_2(D²,{pt}) = 0 → H_2(D²,S¹) = ℤ`, not onto; likewise `(tripleShort X A' A h).g` has
`H_m`-surjectivity only under the missing hypothesis `IsZero ((tripleShort X A' A h).X₁.homology
(m-1))`.  So the sibling's `isZero_relChains_slabBigA/B` (the `pushSlabA`/`pairRestrict` homotopy
argument) **are** the content, not duplicates, and `isZero_of_isZero_of_surjective_int` above — true
as a general lemma — is not enough.  The `whnf` note for that file therefore stands as originally
written; ADDENDUM 1 of that note is retracted (ADDENDUM 2 corrects it).

**Spelling trap (cost a review round-trip):** in a *bare* statement (the harness's statement check
has no `open`s) the class name must be qualified — write `CategoryTheory.Limits.IsZero`, not
`IsZero`; the unqualified form fails with the misleading error "Function expected at".

**`Work.Serre.cubePairRelHomology` IS PROVED (sibling, green) — and it collides with two of my
declarations.**  `Submission/Work/Serre/cubePairRelHomology.lean` now builds (rc=0) and contains the
pair statement at line 558 plus its support (`cubeZeroHomeo`, `cubePairRelHomology_zero`,
`slabBigA`/`slabBigB`, `isZero_relChains_slabBigA`/`B`, `homA/B_mem_bdry_or`) — all in namespace
`Work.Serre`.  So the MV core of the pair Künneth is done.  Two consequences for this file:

1. **Name clashes:** my `cubeZeroHomeo` and `cubePairRelHomology_zero` are *the same statements* in
   the *same namespace* (`Work.Serre`), so `import Submission.Work.Serre.cubePairRelHomology` cannot
   be combined with them as-is.  Rename mine (e.g. suffix `'`) and drop the duplicate, or use the
   sibling's.  Everything else needed from that file (`isZero_relChains_slabBigA/B`, `slabBigA/B`) is
   available on import.
2. **The paste-ready relativisations** (`isZero_relSmallChains_slabA_rel`, `_slabB_rel`): with the
   import in place, each is the generic `relSmallChains_iso_relChains` plus
   `IsZero.of_iso (Work.Serre.isZero_relChains_slabBigA k Y Q m) ((… .mapIso e)).symm` — but the
   *direction* of the `IsZero.of_iso` argument must be checked against `slabBigA`'s definitional
   unfolding (a first attempt with `.symm` produced a type mismatch, so try the other orientation).

**Canonicity observation.**  Suppose `DiscPairRelCohIso` holds and some class
`V` in `H^{r+1}(cyl p, E;Q)` has `cup V` an isomorphism in the range.  By `DiscPairRelCohIso` at
`n = 0` the group `H^{r+1}(cyl p, E;Q)` is a one-dimensional `Q`-vector space (isomorphic to
`H^0(B;Q) = Q`), so the *canonically defined* class `U` -- the image of `1` under the inverse of
that isomorphism -- is a non-zero scalar multiple of `V`, hence `cup U` is an isomorphism in the
range too.  So the multiplicativity input only has to produce *some* class with the injectivity (or
surjectivity) property.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
## Session-9 status: the route to the target, and the state of the two inputs

**The route now taken for this file's target.**  `EulerFibreRange` is to be proved from the *CW-model
case* of the relative (Thom) statement plus a base-change (transfer) step:

* `Work.Serre.cwModelThomCase` (`Submission/Work/Serre/cwModelThomCase.lean`) — **DELEGATED**
  (both reviewers approved; not yet on disk).  It is `ThomIsoCylFibreRange` over the CW-model bases
  `(Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y`, for every `k`, with **no `RatAcyclic`
  hypothesis** on the total space: this is the *relative* statement, and acyclicity is needed only
  to pass from it to the Euler form.  Its proof is the cell-by-cell induction over the tower
  (`Work.Serre.CWModel.genStep`/`killStep`, cells of dimension `≥ 2`): base case `k = 0` (base is a
  point, the disc pair is the cone pair `(CX, X)` with `H̃^*(X)` known by `hvan`/`hgen`); induction
  step = the extension of the Thom class over the new cells (the obstruction is
  `⊕ H̃^{r+1-D}(F)`, vanishing for every cell dimension `D ≥ 2` by `hvan`/`hfib0`), the additive
  disc-pair cell computation (`Work.Serre.cubePairRelHomology`, `cubePairRelCohomology`,
  `Submission/Work/Serre/DiscPair/discCellStep`, `csr`-style excision/additivity over the cells),
  the *multiplicativity* over a cell (`Work.StemsB.modelThomRatAll`, transported along the
  cell/fibre geometry), and the five-lemma chase over the pairs of skeleta driven by
  `Work.StemsB.mixedCup_relToAbs_R`, `Work.StemsB.pairDelta_mixedCup_general_R`,
  `Work.Cohomology.cupNaturalH` and `Work.Serre.fiveLemmaInt`.

* `Work.Serre.cohMapIsoOfRatHomologyIso` (`Submission/Work/Serre/cohMapIsoOfRatHomologyIso.lean`) —
  **DELEGATED** (both reviewers approved; not yet on disk): a rational *homology* isomorphism (in one
  degree) induces a *cohomology* isomorphism (UCT naturality over `ℚ`; over `ℤ` it is false).  It is
  what turns `Work.Serre.serreK2` into `IsIso (Work.Thom.CohMap g ℚ k)` in the transfer below.

**The transfer to an arbitrary simply connected base** (the part of the assembly that belongs to this
file, not yet written — every ingredient is on disk):

1. `hB2 : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B b₀)` from `SimplyConnectedSpace B`.
2. `st := Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 (N+2)`, `Γ := st.Y`, `g := st.g`,
   `γ₀ := st.y₀` (`st.gbase : g γ₀ = b₀`); π-bijectivity at *every* base point of `Γ` from `st.bij`,
   `st.conn` and `Work.Serre.bijective_piMapN_of_joined` (the π₀ case as in
   `Work.Serre.CWModel.exists_model`); `SimplyConnectedSpace Γ` from that plus `hB2`.
3. `q := Work.StemsB.pullbackSnd p g : C(Work.StemsB.Pullback p g, Γ)`; `IsSerreFibration q` from
   `Work.StemsB.hasHLP_pullback` — the pattern is
   `Submission/Work/Serre/strictFibre_ratH_homotopyFibre.lean:211`.
4. Fibre data for `q` at `γ₀`: `Work.Serre.pbFibreHomeo`
   (`Submission/Work/Serre/E2dFibre.lean:51`) identifies `fibre (pullbackSnd p g) γ₀` with
   `fibre p b₀`; it transports `hfib0`, `hvan` and `hgen` to `q`.
5. Bounded acyclicity of `Work.StemsB.Pullback p g` in degrees `≤ N + 1`:
   `Work.Serre.pullbackFst_piMapN_bijective` (`Submission/Work/Serre/pullbackFst_piMapN_bijective.lean`)
   gives the π-isomorphism of `Work.StemsB.pullbackFst p g` with `E` in the range, `Work.Serre.serreK2`
   the rational homology isomorphism, and `RatAcyclic E` the vanishing.
6. Apply `cwModelThomCase` at `k = N + 2` to obtain `U`; then the Euler form over `Γ`: extract from
   the proof of `eulerFibreRange_of_thomIsoCylFibreRange` below the lemma
   `∃ e : Coh ℚ (r+1) Γ, ∀ m, m + r + 1 ≤ N + 1 → IsIso (cupWith Γ (r+1) e m)` from
   `(∀ k, 0 < k → k ≤ N + 1 → IsZero (Coh ℚ k (Pullback p g)))` (bounded acyclicity from step 5)
   and `U` — the same `hkey`/`mixedCup_relToAbs_R`/`cupNaturalH`/`cohMap_cylInr_cylRetract` argument,
   with `IsZero` in place of `RatAcyclic` (`isIso_relToAbs_succ` already takes the two vanishing
   hypotheses in the degrees `m + r` and `m + r + 1`).
7. Base change of the class: `e := (asIso (Work.Thom.CohMap g ℚ (r + 1))).inv e_Γ`, and the identity
   `cupWith (TopCat.of B) (r+1) e m = (CohMap g ℚ (m+r+1)).inv ∘ cupWith Γ (r+1) e_Γ m ∘ (CohMap g ℚ m)`
   by `Work.Cohomology.cupNaturalH` and `(CohMap g ℚ (r+1)) e = e_Γ`; then
   `IsIso (CohMap g ℚ m)`, `IsIso (CohMap g ℚ (m + r + 1))` from step 5 + `serreK2` +
   `cohMapIsoOfRatHomologyIso`.
-/

/-- **The Euler-class form follows from the relative (mapping-cylinder) form of the Gysin
theorem.**  The class is `e := (cylInr p)^*(relToAbs U)`, and `⌣ e` is the composite
`(cylInr p)^* ∘ relToAbs ∘ (⌣ U) ∘ (cylRetract p)^*` of three isomorphisms. -/
theorem eulerFibreRange_of_thomIsoCylFibreRange (h : ThomIsoCylFibreRange) : EulerFibreRange := by
  intro E B _ _ p b₀ r N hr hp hB hE hfib0 hfib hgen
  obtain ⟨U, hU⟩ := h E B p b₀ r N hr hp hB hE hfib0 hfib hgen
  refine ⟨(Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U), fun m hm => ?_⟩
  have hA : ∀ k : ℕ, 0 < k → IsZero (Work.Thom.Coh ℚ k ↥(Set.range (cylIncl p))) := by
    intro k hk
    obtain ⟨φ⟩ := cylHomeo p
    exact isZero_coh_of_homeo φ (isZero_coh_of_ratAcyclic hE hk)
  -- the key identity: `⌣ e` is the composite of the retraction pullback, the cup with `U`, the
  -- forgetful map and the pullback along `cylInr p`
  have hkey : (cupWith (TopCat.of B) (r + 1)
        ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) m) =
      ((Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom).comp
        (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom).comp
          (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U ∘ₗ
            (Work.Thom.CohMap (cylRetract p) ℚ m).hom)) := by
    ext x
    change Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of B)) m (r + 1) x
        ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) =
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom
          ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))
            ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U))
    rw [Work.StemsB.mixedCup_relToAbs_R ℚ (Set.range (cylIncl p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U]
    rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (cylInr p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x)
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)]
    rw [cohMap_cylInr_cylRetract p m x]
  have hbijF : Function.Bijective (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m
      (r + 1))).flip U ∘ₗ (Work.Thom.CohMap (cylRetract p) ℚ m).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (cylRetract p) ℚ m).hom))).mp (hU m hm)
  have hbijInr : Function.Bijective (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1)))).mp (isIso_cohMap_cylInr p (m + (r + 1)))
  have hbijRel : Function.Bijective
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1)))).mp
        (isIso_relToAbs_succ (Set.range (cylIncl p)) (m + r) (by omega)
          (hA (m + r) (by omega)) (hA (m + r + 1) (by omega)))
  have hbij : Function.Bijective (cupWith (TopCat.of B) (r + 1)
      ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) m) := by
    rw [hkey]
    exact hbijInr.comp (hbijRel.comp hbijF)
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1)
      ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) m))).mpr hbij


/-- **The local (cell-level) disc-pair input.**  Over the *trivial* pair bundle
`(B × ℝ^{r+1}, {p | p.2 ∈ S^r})` — the fibre pair of the disc-pair fibration over a single cell,
up to the fibre-homotopy triviality of the fibration over a disc — the relative rational cohomology
in degree `n + r + 1` is that of the base in degree `n`.

This is the group-level form of the model Thom class `Work.StemsB.ModelThomRat`: the Thom map
`x ↦ proj^*(x) ⌣ τ` is bijective (`Work.StemsB.modelThomRatAll`, proved for every rank), so it is
in particular an isomorphism of `ℚ`-modules.  It is the local input of the cell-by-cell
construction of the Thom class of a spherical fibration, and (by the long exact sequence of the
triple of skeleta) it is what makes the extension obstruction vanish over a cell of dimension `≥ 2`
for `j ≥ 2`. -/



theorem modelPairRelCohIso (B : Type) [TopologicalSpace B] (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℚ (n + r + 1) (B × EuclideanSpace ℝ (Fin (r + 1)))
        {p : B × EuclideanSpace ℝ (Fin (r + 1)) | p.2 ∈ Work.Thom.mSph (r + 1)} ≅
      Work.Thom.Coh ℚ n B) := by
  obtain ⟨τ, hτ⟩ := Work.StemsB.modelThomRatAll B (n := r + 1) (by omega)
  exact ⟨(LinearEquiv.ofBijective
      ((Work.Thom.mixedCupC ℚ {p : B × EuclideanSpace ℝ (Fin (r + 1)) |
          p.2 ∈ Work.Thom.mSph (r + 1)} n (r + 1)).flip τ ∘ₗ
        (Work.Thom.CohMap (Work.StemsB.projFstRat B (r + 1)) ℚ n).hom)
      (hτ n)).symm.toModuleIso⟩

/-- **The pair form of the relative homology of the cube pair** (the "cell suspension"): for the
cube pair `(I^k × P, ∂I^k × P)` cut down by a second pair `(P,Q)`, the `(j+k)`-th relative homology
is the `j`-th relative homology of `(P,Q)`:

  `H_{j+k}(I^k × P, ∂I^k × P ∪ I^k × Q; ℤ) ≅ H_j(P, Q; ℤ)`.

This is the statement the extension step of the cell-by-cell Thom construction consumes: over a
`(j+2)`-cell, the obstruction lives in `H^{r+2}` of the disc-pair bundle relative to its
boundary-and-sphere part, which is (up to the fibre-homotopy triviality over the cell)
`H^(r+2-(j+2))`-relative of the fibre pair.  Taking `k := m + 1` recovers the `SuspensionStep` form.

**Proof route.**  It follows from the *proved* space case `Work.StemsB.cubePair_main` (for the space
`P` and for the space `Q`) together with the long exact sequence of the pair of pairs
`(I^k × P, ∂I^k × P ∪ I^k × Q)`, the excision identification
`H_*(∂I^k × P ∪ I^k × Q, ∂I^k × Q) ≅ H_*(I^k × Q, ∂I^k × Q)` and the five lemma, comparing with the
long exact sequence of the pair `(P,Q)`.

**Induction available.**  The `k+1` step is the relativised version of the proved
`Work.StemsB.cubePairStep_iso` / `Work.StemsB.midRelIso`, driven by
`Work.StemsB.relMV_shortExact X A U V`, which already carries the extra subset `A` (so the
second pair `(P,Q)` rides along); the base case `k = 0` is `Work.StemsB.cubeBdryK_zero`
together with the homeomorphism of pairs `(I^0 × P, I^0 × Q) ≅ (P,Q)`; and the specialisation
`Q = ∅` is exactly the *proved* `Work.StemsB.cubePair_iso`.  Arbitrary pairs must *not* be used: the statement is false
for a general pair `(P,Q)` (see `Submission/Work/Serre/TICFR_PLAN.md`), so the cube/collar shape is
essential. -/
def CubePairRelHomology : Prop :=
  ∀ (k : ℕ) (P : Type) [TopologicalSpace P] (Q : Set P) (j : ℕ),
    Nonempty (((Work.Cohomology.relChains (Work.StemsB.CubeSpace P k)
        (Work.StemsB.cubeBdryK P k ∪ {p : Work.StemsB.CubeP P k | p.2 ∈ Q})).homology (j + k)) ≅
      ((Work.Cohomology.relChains (TopCat.of P) Q).homology j))





/-- The `0`-cube is a single point, so the projection `I^0 × P → P` onto the second factor is a
homeomorphism. -/
def cubeZeroHomeo' (P : Type) [TopologicalSpace P] : (Work.StemsB.CubeP P 0) ≃ₜ P where
  toFun := Prod.snd
  invFun := fun p => (fun _ => 0, p)
  left_inv := fun x => by
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  right_inv := fun p => rfl
  continuous_toFun := continuous_snd
  continuous_invFun := by fun_prop

/-- **Base case `k = 0` of the pair form of the relative homology of the cube pair**: the pair
`(I^0 × P, I^0 × Q)` *is* the pair `(P, Q)`, so the degree shift is trivial. -/
theorem cubePairRelHomology_zero' (P : Type) [TopologicalSpace P] (Q : Set P) (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (Work.StemsB.CubeSpace P 0)
        (Work.StemsB.cubeBdryK P 0 ∪ {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q})).homology (j + 0)) ≅
      ((Work.Cohomology.relChains (TopCat.of P) Q).homology j)) := by
  have hset : Work.StemsB.cubeBdryK P 0 ∪ {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q}
      = {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q} := by
    rw [Work.StemsB.cubeBdryK_zero]
    exact Set.empty_union _
  have hAB : ∀ x : Work.StemsB.CubeP P 0,
      x ∈ {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q} ↔ cubeZeroHomeo P x ∈ Q := fun x => Iff.rfl
  haveI hIso : IsIso (Work.StemsB.relChainsMapOf (X := TopCat.of (Work.StemsB.CubeP P 0)) (Y := TopCat.of P)
      (Work.StemsB.sphHomeoHom (X := TopCat.of (Work.StemsB.CubeP P 0)) (Y := TopCat.of P) (cubeZeroHomeo' P)) {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q} Q
      (Work.StemsB.homeoPairMem hAB)) :=
    Work.StemsB.isIso_relChainsMapOf_homeomorph (X := TopCat.of (Work.StemsB.CubeP P 0)) (Y := TopCat.of P)
      (cubeZeroHomeo' P) _ _ hAB
  have h2 : Work.Cohomology.relChains (Work.StemsB.CubeSpace P 0)
        (Work.StemsB.cubeBdryK P 0 ∪ {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q})
      ≅ Work.Cohomology.relChains (Work.StemsB.CubeSpace P 0)
        {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q} :=
    eqToIso (congrArg (fun s => Work.Cohomology.relChains (Work.StemsB.CubeSpace P 0) s) hset)
  have hiso : Work.Cohomology.relChains (Work.StemsB.CubeSpace P 0)
        {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q}
      ≅ Work.Cohomology.relChains (TopCat.of P) Q :=
    asIso (Work.StemsB.relChainsMapOf (X := TopCat.of (Work.StemsB.CubeP P 0)) (Y := TopCat.of P)
      (Work.StemsB.sphHomeoHom (X := TopCat.of (Work.StemsB.CubeP P 0)) (Y := TopCat.of P) (cubeZeroHomeo' P)) {p : Work.StemsB.CubeP P 0 | p.2 ∈ Q} Q
      (Work.StemsB.homeoPairMem hAB))
  exact ⟨HomologicalComplex.homologyMapIso (h2 ≪≫ hiso) (j + 0)⟩

/-- **The slab set identity with a second pair adjoined.**  Cutting the middle slab by the boundary
of the cube *and* by a second pair `(Y,Q)` on the parameter factor is the same as cutting it by the
boundary alone and then by `Q`: the set identity that relativises
`Work.StemsB.relMVH₁_iso_slabMid` to the pair `(Y,Q)`. -/
theorem slabMidi_union_second (Y : Type) [TopologicalSpace Y] (n : ℕ) (Q : Set Y) :
    (Subtype.val ⁻¹' (Work.StemsB.slabMid (Y := Y) n ∩
        (Work.StemsB.cubeBdry (Y := Y) n ∪ {p : Work.StemsB.CubeP Y (n + 1) | p.2 ∈ Q})))
      = Work.StemsB.slabMidi (Y := Y) n ∪
        {x : ↥(Work.StemsB.slabMid (Y := Y) n) | x.1.2 ∈ Q} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
    Work.StemsB.slabMidi]
  exact ⟨fun h => h.2.elim (fun hb => Or.inl ⟨h.1, hb⟩) Or.inr,
    fun h => h.elim (fun hb => ⟨hb.1, Or.inl hb.2⟩) (fun hc => ⟨x.2, Or.inr hc⟩)⟩

/-- **The relativised identification of the first term of the relative Mayer–Vietoris sequence with
the relative homology of the middle slab** (the *first* of the three ingredients of the
`k → k+1` step, with the second pair `(Y,Q)` adjoined): verbatim the proof of
`Work.StemsB.relMVH₁_iso_slabMid`, using the `C`-genericity of
`Work.Cohomology.Endgame.relSmallChains_iso_relChains`, together with the set identity
`slabMidi_union_second`. -/
theorem relMVH₁_iso_slabMid_rel (Y : Type) [TopologicalSpace Y] (n : ℕ) (m : ℕ) (Q : Set Y) :
    Nonempty (Work.Cohomology.relMVH₁ (Work.StemsB.CubeSpace (Y := Y) (n + 1))
        (Work.StemsB.cubeBdry (Y := Y) n ∪ {p : Work.StemsB.CubeP Y (n + 1) | p.2 ∈ Q})
        (Work.StemsB.slabA (Y := Y) n) (Work.StemsB.slabB (Y := Y) n) m ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabMid (Y := Y) n))
        (Work.StemsB.slabMidi (Y := Y) n ∪
          {x : ↥(Work.StemsB.slabMid (Y := Y) n) | x.1.2 ∈ Q})).homology m)) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := Work.StemsB.CubeSpace (Y := Y) (n + 1)) (Work.StemsB.slabA (Y := Y) n)
    (Work.StemsB.slabB (Y := Y) n) (Work.StemsB.slabMid (Y := Y) n)
    (Work.StemsB.slabMid (Y := Y) n ∩ (Work.StemsB.cubeBdry (Y := Y) n ∪
      {p : Work.StemsB.CubeP Y (n + 1) | p.2 ∈ Q}))
    (Set.inter_subset_left :
      Work.StemsB.slabMid (Y := Y) n ∩ (Work.StemsB.cubeBdry (Y := Y) n ∪
        {p : Work.StemsB.CubeP Y (n + 1) | p.2 ∈ Q}) ⊆ Work.StemsB.slabMid (Y := Y) n)
    (Or.inl (by intro x hx; exact hx.1))
  have h2 : Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabMid (Y := Y) n))
        (Subtype.val ⁻¹' (Work.StemsB.slabMid (Y := Y) n ∩
          (Work.StemsB.cubeBdry (Y := Y) n ∪ {p : Work.StemsB.CubeP Y (n + 1) | p.2 ∈ Q})))
      ≅ Work.Cohomology.relChains (TopCat.of ↥(Work.StemsB.slabMid (Y := Y) n))
        (Work.StemsB.slabMidi (Y := Y) n ∪
          {x : ↥(Work.StemsB.slabMid (Y := Y) n) | x.1.2 ∈ Q}) :=
    eqToIso (congrArg (fun s => Work.Cohomology.relChains
      (TopCat.of ↥(Work.StemsB.slabMid (Y := Y) n)) s) (slabMidi_union_second Y n Q))
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso
    (e ≪≫ h2)⟩

/-- **The `ℚ`-valued restatement of the pair form of the relative homology of the cube pair**
(route 1 for `CubePairRelHomorphism`): state and prove the pair Künneth over `ℚ`, feed the *proved*
five lemma `Work.Serre.RatTower.fiveLemmaTau2`, and recover the integral statement through
`Submission/Work/StemsB/RelChainsBaseChangeRat.lean`. -/
def CubePairRelHomologyRat : Prop :=
  ∀ (k : ℕ) (P : Type) [TopologicalSpace P] (Q : Set P) (j : ℕ),
    Nonempty (((Work.StemsB.relChainsR ℚ (Work.StemsB.CubeSpace P k)
        (Work.StemsB.cubeBdryK P k ∪ {p : Work.StemsB.CubeP P k | p.2 ∈ Q})).homology (j + k)) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homology j))


/-- **A surjection out of a zero `ℤ`-module has zero target** — the `ℤ`-coefficient instance of
`Work.Serre.isZero_of_isZero_of_surjective` (which is stated over `ℚ`), needed for the monotonicity
route to the relativised slab vanishings: it converts "the smaller relative group vanishes" plus the
surjectivity of `relChains X A' → relChains X A` (`A' ⊆ A`) into the vanishing of the larger one. -/
theorem isZero_of_isZero_of_surjective_int {X Y : ModuleCat ℤ} (hX : CategoryTheory.Limits.IsZero X)
    (f : X ⟶ Y) (hf : Function.Surjective f.hom) : CategoryTheory.Limits.IsZero Y := by
  have hzero : f = 0 := CategoryTheory.Limits.IsZero.eq_of_src hX f 0
  have hzero' : f.hom = 0 := by rw [hzero]; rfl
  haveI : Subsingleton (↥Y) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      rw [show f.hom x = 0 from by simp [hzero'], show f.hom y = 0 from by simp [hzero']]⟩
  exact ModuleCat.isZero_of_subsingleton Y


theorem isZero_relSmallChains_slabA_rel (Y : Type) [TopologicalSpace Y] (k : ℕ) (Q : Set Y)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := Work.StemsB.CubeSpace (Y := Y) (k + 1))
      (Work.StemsB.slabA (Y := Y) k) (Work.StemsB.slabB (Y := Y) k) (Work.StemsB.slabA (Y := Y) k)
      (Work.StemsB.slabA (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
        {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}))
      (Set.inter_subset_left :
        Work.StemsB.slabA (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
          {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}) ⊆ Work.StemsB.slabA (Y := Y) k)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := Work.StemsB.CubeSpace (Y := Y) (k + 1)) (Work.StemsB.slabA (Y := Y) k)
    (Work.StemsB.slabB (Y := Y) k) (Work.StemsB.slabA (Y := Y) k)
    (Work.StemsB.slabA (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
      {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}))
    (Set.inter_subset_left :
      Work.StemsB.slabA (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
        {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}) ⊆ Work.StemsB.slabA (Y := Y) k)
    (Or.inl subset_rfl)
  exact IsZero.of_iso (Work.Serre.isZero_relChains_slabBigA k Y Q m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

theorem isZero_relSmallChains_slabB_rel (Y : Type) [TopologicalSpace Y] (k : ℕ) (Q : Set Y)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relSmallChains (X := Work.StemsB.CubeSpace (Y := Y) (k + 1))
      (Work.StemsB.slabA (Y := Y) k) (Work.StemsB.slabB (Y := Y) k) (Work.StemsB.slabB (Y := Y) k)
      (Work.StemsB.slabB (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
        {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}))
      (Set.inter_subset_left :
        Work.StemsB.slabB (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
          {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}) ⊆ Work.StemsB.slabB (Y := Y) k)).homology m) := by
  obtain ⟨e⟩ := Work.Cohomology.Endgame.relSmallChains_iso_relChains
    (X := Work.StemsB.CubeSpace (Y := Y) (k + 1)) (Work.StemsB.slabA (Y := Y) k)
    (Work.StemsB.slabB (Y := Y) k) (Work.StemsB.slabB (Y := Y) k)
    (Work.StemsB.slabB (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
      {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}))
    (Set.inter_subset_left :
      Work.StemsB.slabB (Y := Y) k ∩ (Work.StemsB.cubeBdry (Y := Y) k ∪
        {p : Work.StemsB.CubeP Y (k + 1) | p.2 ∈ Q}) ⊆ Work.StemsB.slabB (Y := Y) k)
    (Or.inr subset_rfl)
  exact IsZero.of_iso (Work.Serre.isZero_relChains_slabBigB k Y Q m)
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso e)

/-- **The relativised second term of the relative Mayer–Vietoris sequence vanishes in every degree**
— `Work.StemsB.isZero_relMVH₂_cube` with the second pair `(Y,Q)` adjoined: the generic
`Work.ThreeConnected.Excision.isZero_homology_biprod` applied to the two relativised small-chains
vanishings above. -/
theorem isZero_relMVH₂_cube_rel (Y : Type) [TopologicalSpace Y] (n : ℕ) (Q : Set Y) :
    ∀ m : ℕ, IsZero (Work.Cohomology.relMVH₂ (Work.StemsB.CubeSpace (Y := Y) (n+1))
      (Work.StemsB.cubeBdry (Y := Y) n ∪ {p : Work.StemsB.CubeP Y (n+1) | p.2 ∈ Q})
      (Work.StemsB.slabA (Y := Y) n) (Work.StemsB.slabB (Y := Y) n) m) := fun m =>
  Work.ThreeConnected.Excision.isZero_homology_biprod
    (isZero_relSmallChains_slabA_rel Y n Q m) (isZero_relSmallChains_slabB_rel Y n Q m)

/-- **The additive (relativised Serre exact sequence) form of the Gysin theorem in the fibre
range**: the cohomology of the disc-pair bundle of `p` in degree `n + r + 1` is that of the base
in degree `n`, through degree `N + 1`.

This is the cell-by-cell computation of the *degenerate* Serre spectral sequence of the disc-pair
fibration `(cyl p, E) → B`: the fibre pair `(CF_b, F_b)` has relative rational cohomology
concentrated in degree `r + 1` through degree `N + 1`, so the first page of the spectral sequence is
the (shifted) cellular cochain complex of the base and all differentials vanish.  It is the
*additive* half of the Gysin theorem (no cup products), and it is the input that the
multiplicativity argument (cupping with the Thom class) consumes. -/
def DiscPairRelCohIso : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → RatAcyclic E →
      PathConnectedSpace (Work.StemsB.fibre p b₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∀ n : ℕ, n + r + 1 ≤ N + 1 → Nonempty
        (Work.Thom.RelCoh ℚ (n + r + 1) (cyl p) (Set.range (cylIncl p)) ≅
          Work.Thom.Coh ℚ n B)


/-!
## The CW-model case, and the transfer to an arbitrary simply connected base

The single remaining input of the target is the *relative* (Thom) form of the Gysin theorem over a
CW model of the base: the cell-by-cell induction needs a base whose cells all have dimension `≥ 2`
(so that there is no monodromy, which is the role of simple connectivity) and whose skeleta give a
filtration adapted to the disc-pair fibration.

`Work.Serre.CWModel.towerA` supplies exactly such a model `Γ` for a `(b-1)`-connected base `B`
(`b = 2` for a simply connected `B`), together with a map `g : Γ → B` which is a bijection on `π_i`
for every `i ≤ N` at every base point of `Γ`.  Transporting the fibration `p : E → B` along `g`
(pullback) and applying the CW-model case gives the Euler class on `Γ`; base-changing that class
back along `g` — legitimate because `g` is a rational (co)homology isomorphism in the range by
`Work.Serre.serreK2` and `Work.Serre.cohMapIsoOfRatHomologyIso` — gives the target.
-/

/-- **The CW-model case of the relative (Thom) form of the Gysin theorem.**  This is the statement
proved in `Submission/Work/Serre/cwModelThomCase.lean` (module
`Submission.Work.Serre.cwModelThomCase`), recorded here as a predicate so that the transfer below
can be stated and proved independently of it.  See that file for the mathematics: the tower
induction over the model bases `Work.Serre.CWModel.towerA B b₀ 2 _ hB2 k`, whose cells all have
dimension `≥ 2`. -/
def CWModelThomCase : Prop :=
  ∀ (B : Type) [TopologicalSpace B] (b₀ : B)
    (hB2 : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B b₀)) (N r : ℕ),
    1 ≤ r → ∀ k : ℕ, ∀ (X : Type) [TopologicalSpace X]
      (q : C(X, (CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y)),
      Work.StemsB.IsSerreFibration q →
      SimplyConnectedSpace (CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y →
      PathConnectedSpace (Work.StemsB.fibre q (CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → IsZero
        (ratH (TopCat.of (Work.StemsB.fibre q
          (CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q
        (CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∃ U : Work.Thom.RelCoh ℚ (r + 1) (cyl q) (Set.range (cylIncl q)),
        ∀ m : ℕ, m + r + 1 ≤ N + 1 →
          IsIso (ModuleCat.ofHom
            (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1))).flip U ∘ₗ
              (Work.Thom.CohMap (cylRetract q) ℚ m).hom))

/-- **The transfer: the CW-model case implies the Euler-class form of the Gysin theorem.**

Given the fibration `p : E → B` of the target (`B` simply connected, `E` rationally acyclic, strict
fibre a rational `r`-sphere through degree `N`), take the CW model `Γ := (towerA B b₀ 2 _ hB2
(N+2)).Y` of `B` with its comparison map `g` (`π_i`-bijective for `i ≤ N + 2` at every point).
The pullback `q := pullbackSnd p g` is a Serre fibration with the same fibre data, and the pullback
total space is rationally acyclic in degrees `≤ N + 1` (`pullbackFst` is a `π`-isomorphism below
`N + 2`, hence a rational homology isomorphism by `serreK2`).  The CW-model case produces the
relative Thom class over `Γ`, from which the bounded Euler extraction
(`Work.Serre.eulerClass_of_thomBdd`) gives an Euler class `e_Γ` on `Γ`, and
`Work.Serre.exists_cupWith_of_preimage` transports it back to `B` along the cohomology isomorphism
induced by `g`. -/
theorem eulerFibreRange_of_cwModelCase (h : CWModelThomCase) : EulerFibreRange := by
  intro E B _ _ p b₀ r N hr hp hB hE hfib0 hfib hgen
  haveI hscB : SimplyConnectedSpace B := hB
  by_cases hrN : r + 1 ≤ N + 1
  · -- the model base
    have hB2 : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B b₀) := by
      intro i hi
      interval_cases i
      · haveI : Subsingleton (ZerothHomotopy B) :=
          (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
        exact (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀)).injective.subsingleton
      · exact (HomotopyGroup.pi1EquivFundamentalGroup (X := B) (x := b₀)).injective.subsingleton
    let st : CWModel.StA B b₀ (2 - 2 + (N + 2)) :=
      CWModel.towerA B b₀ 2 (le_refl 2) hB2 (N + 2)
    haveI hconnY : PathConnectedSpace st.Y := st.conn
    -- `g` is a `π_i`-isomorphism at every base point, in the range
    have hg_bij : ∀ i : ℕ, i ≤ N + 2 → ∀ γ : st.Y, Function.Bijective (piMapN st.g i γ) := by
      intro i hi γ
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        haveI : Subsingleton (HomotopyGroup (Fin 0) st.Y γ) :=
          (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := γ)).injective.subsingleton
        haveI : Subsingleton (HomotopyGroup (Fin 0) B (st.g γ)) :=
          (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := st.g γ)).injective.subsingleton
        exact ⟨fun a b _ => Subsingleton.elim a b,
          fun y => ⟨default, Subsingleton.elim _ _⟩⟩
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        exact Work.Serre.bijective_piMapN_of_joined st.g
          (PathConnectedSpace.joined st.y₀ γ) (j + 1) (st.bij j (by omega))
    -- `Γ` is simply connected, and the pullback fibration is a Serre fibration
    have hscΓ : SimplyConnectedSpace st.Y := by
      refine Work.RatHurewicz.simplyConnectedSpace_of_subsingleton st.y₀ ?_ ?_
      · haveI : Subsingleton (ZerothHomotopy st.Y) :=
          (pathConnectedSpace_iff_zerothHomotopy.mp st.conn).2
        exact (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := st.y₀)).injective.subsingleton
      · have hπ1 : Subsingleton (HomotopyGroup (Fin 1) B (st.g st.y₀)) := by
          rw [st.gbase]; exact hB2 1 (by norm_num)
        haveI := hπ1
        exact ⟨fun a b => (st.bij 0 (by omega)).1 (Subsingleton.elim _ _)⟩
    have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p st.g) :=
      fun n => Work.StemsB.hasHLP_pullback p st.g (hp n)
    -- the fibre data of the pullback at `st.y₀`
    obtain ⟨hfib0', hvan', hgen'⟩ :=
      Work.Serre.fibreData_pullbackSnd p st.g st.y₀ st.gbase r N hfib0 hfib hgen
    haveI hne : Nonempty (Work.StemsB.Pullback p st.g) := by
      obtain ⟨e, he⟩ := hfib0.nonempty
      exact ⟨⟨(e, st.y₀), by show p e = st.g st.y₀; rw [he, st.gbase]⟩⟩
    -- rational acyclicity of the pullback total space, in the range
    have hacycH : ∀ k : ℕ, 0 < k → k ≤ N + 1 →
        IsZero (ratH (TopCat.of (Work.StemsB.Pullback p st.g)) k) := by
      intro k hk0 hkN
      have hbij : ∀ i : ℕ, i < N + 2 → ∀ x : Work.StemsB.Pullback p st.g,
          Function.Bijective (piMapN (Work.StemsB.pullbackFst p st.g) i x) :=
        Work.Serre.pullbackFst_piMapN_bijective p st.g hp (N + 2) hg_bij
      haveI : IsIso (ratHomologyMap (Work.StemsB.pullbackFst p st.g) k) :=
        Work.Serre.serreK2 (Work.StemsB.Pullback p st.g) E
          (Work.StemsB.pullbackFst p st.g) (N + 2) hbij k (by omega)
      exact IsZero.of_iso (Y := ratH (TopCat.of E) k) (Work.StemsB.isZero_ratH_of_ratAcyclic hE hk0)
        (asIso (ratHomologyMap (Work.StemsB.pullbackFst p st.g) k))
    have hXcoh : ∀ k : ℕ, 0 < k → k ≤ N + 1 →
        IsZero (Work.Thom.Coh ℚ k (Work.StemsB.Pullback p st.g)) := by
      intro k hk0 hkN
      exact Work.Serre.isZero_ratCoh_of_isZero_ratH (hacycH k hk0 hkN)
    -- the CW-model case, and the bounded Euler extraction
    have hU : ∃ U : Work.Thom.RelCoh ℚ (r + 1) (cyl (Work.StemsB.pullbackSnd p st.g))
        (Set.range (cylIncl (Work.StemsB.pullbackSnd p st.g))),
        ∀ m : ℕ, m + r + 1 ≤ N + 1 → IsIso (ModuleCat.ofHom
          (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd p st.g))) m
            (r + 1))).flip U ∘ₗ
            (Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd p st.g)) ℚ m).hom)) :=
      h B b₀ hB2 N r hr (N + 2) (Work.StemsB.Pullback p st.g)
        (Work.StemsB.pullbackSnd p st.g) hq hscΓ hfib0' hvan' hgen'
    obtain ⟨eΓ, heΓ⟩ := Work.Serre.eulerClass_of_thomBdd
      (Work.StemsB.pullbackSnd p st.g) r N hr hrN hXcoh hU
    -- base change back to `B`
    have hiso : ∀ k : ℕ, k ≤ N + 1 → IsIso (Work.Thom.CohMap st.g ℚ k) := by
      intro k hk
      haveI : IsIso (ratHomologyMap st.g k) :=
        Work.Serre.serreK2 st.Y B st.g (N + 3)
          (fun i hi γ => hg_bij i (by omega) γ) k (by omega)
      exact Work.Serre.cohMapIsoOfRatHomologyIso st.g k inferInstance
    exact Work.Serre.exists_cupWith_of_preimage st.g r N hr hiso eΓ heΓ
  · exact ⟨0, fun m hm => absurd hm (by omega)⟩


/-!
## An alternative (independent) cellular step, and the wiring for it

`Work.Serre.cwModelThomCase` (`Submission/Work/Serre/cwModelThomCase.lean`) is proved from two inputs
by its `Work.Serre.cwModelThomCase_of_pieces`: the base case `Work.Serre.thomCylBaseCase` (proved)
and one cellular step.  Should that cellular step be proved independently at
`Submission/Work/Serre/thomCylCellStepAlt.lean` (`Work.Serre.thomCylCellStepAlt`, an exact copy of
the statement), the following turns it into `CWModelThomCase` inside *this* file, so that the target
below no longer depends on the still-open `sorry` in `cwModelThomCase.lean`.
-/

/-! `Work.Serre.ThomCylCellStepAlt` is declared in the leaf module
`Submission/Work/Serre/ThomCylCellStepAltDef.lean` (imported above), so that the proof of the
cellular step in `Submission/Work/RatHurewicz/cellStepShell.lean` can name it without
importing this file (which would create the cycle
`eulerFibreRange → cwModelThomCase → cellStepShell → eulerFibreRange`). -/

/-- **The CW-model case from the independent cellular step.** -/
theorem cwModelThomCase_of_altCellStep (hcell : ThomCylCellStepAlt) : CWModelThomCase := by
  intro B _ b₀ hB2 N r hr k X _ q hq hsc hpc hvan hgen
  exact cwModelThomCase_of_pieces B b₀ hB2 N r hr
    (fun X' _ q' hq' hfib0' hvan' hgen' => thomCylBaseCase r N hr X' q' hq' hfib0' hvan' hgen')
    (fun D hD Γ _ hΓ ι f X' _ q' hq' hvan' hgen' hpc' IH =>
      hcell r N hr D hD hΓ ι f q' hq' hvan' hgen' hpc' IH)
    k X q hq hsc hpc hvan hgen

/-- **THE TARGET: the Euler-class form of the Gysin theorem in the fibre range.**

Proof: the transfer `Work.Serre.eulerFibreRange_of_cwModelCase` (proved above, axiom-clean) applied
to the CW-model case `Work.Serre.cwModelThomCase` (`Submission/Work/Serre/cwModelThomCase.lean`),
whose own proof is complete except for its single cellular step `Work.Serre.thomCylCellStep`.  The
predicate `Work.Serre.CWModelThomCase` above is *definitionally equal* to the type of
`Work.Serre.cwModelThomCase`, so this is the whole assembly. -/
theorem eulerFibreRange : Work.Serre.EulerFibreRange :=
  eulerFibreRange_of_cwModelCase cwModelThomCase

end

end Work.Serre
