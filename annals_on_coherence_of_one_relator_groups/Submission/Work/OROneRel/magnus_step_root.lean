/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus step for a root of a relator: `magnus_step_root`

This file contains the lemma `Work.OROneRel.magnus_step_root` -- the classical Magnus--Moldavanskii
step of the Karrass--Magnus--Solitar torsion theorem, with the root tracked up to conjugacy -- and
the elementary toolbox about the Magnus rewriting `magRew` that the step is built from.

## Status of the file (read this first)

**The file has NO `sorry` of its own any more.**  Everything is proved, including the residual: the
last open obligation is no longer a statement of this file but two statements of the `Z`-domain
(window) route, each carrying a `sorry` elsewhere:

* `Work.OROneRel.bandFreiheitssatz_of_windowData` (`Submission/Work/OROneRel/bandFreiheitssatz_of_windowData.lean`,
  the fleet's *active* Freiheitssatz line) -- given the window data of the minimal `Z`-domain,
  the **Freiheitssatz of the domain** `winRho x ∈ ⟪u ^ l⟫ → x ∈ ⟪winRoot ^ l⟫` (Linton,
  *One-relator hierarchies*, arXiv 2202.11324, Prop. 4.9 with the Magnus Freiheitssatz, Thm. 2.6).
  The *window data* itself is **proved** here: it is used through the namespaced copy
  `Work.OROneRel.NC.exists_window_support_data_cycred` (see §1 below);
* `Work.OROneRel.Low.windowSplitting_v2` (`Submission/Work/OROneRel/winSplittingLow.lean`) -- given
  the same window data, the case hypotheses of the residual and the Freiheitssatz, a weight-one deck
  element `τ` whose walk lies in the window, the generation plank `winVertex ⊔ ⟨mk τ⟩ = ⊤` and the
  injectivity of the canonical comparison map `hnnConjMap`: the graph-of-spaces splitting
  `G ≅ HNN(π₁D, π₁(D ∩ t⁻¹D), π₁(D ∩ tD), ψ)` (Linton, Prop. 4.3 with Prop. 2.2.19).  **That
  statement is *proved*** in `winSplittingLow.lean`, from the two halves
  `Work.OROneRel.Low.winRhoRange_cosetTree_window_v2` (the free-group coset-graph tree, (P-A)) and
  `Work.OROneRel.Low.winVertex_generation_exists_windowWalk_v2` (the generation, (P-B)) -- two
  statement stubs that are *verbatim copies* of the fleet's active lines
  `winRhoRange_cosetTree_window_v2` / `winVertex_generation_exists_windowWalk_v2`, relocated below
  this file by the module-cycle fix documented in
  `Submission/Work/OROneRel/NOTES_module_cycle_and_the_low_pathway.md` (the case predicates moved to
  `Submission/Work/OROneRel/magnusCaseDefs.lean`, so that the two halves no longer sit *above* this
  file).  The previous dependency `Work.OROneRel.magnus_residual_winSplitting` -- the same
  conclusion *without* the case hypotheses -- is no longer used: its un-strengthened halves are
  refuted for some window data, so the case hypotheses are the only shape in which the route is
  available (see `Submission/Work/OROneRel/magnus_residual_winTreeSplitting.lean`).

`magnus_step_root_no_eps_zero_residual` (below) is a *proof* from exactly those two: it derives
`Fintype α` from `hocc`, obtains the window data from
`NC.exists_window_support_data_cycred` and the Freiheitssatz from `bandFreiheitssatz_of_windowData`,
proves the aperiodicity `¬ IsProperPower (winRoot …)` (transport of a proper-power witness along the
telescoping identity `winRho_winRoot`) and the norm decrease (`winRootNormLt`, which needs the
traversed tree edge of the data), and assembles the `Z`-domain datum
(`magnusDomainDatum_of_hnnConjMap`) and the target
(`magnus_step_root_no_eps_zero_of_domainDatum`).  **Consequently this file closes as soon as those
two statements close**, with no further work here.  (`#print axioms Work.OROneRel.magnus_step_root`
gives `[propext, sorryAx, Classical.choice, Quot.sound]`; the `sorryAx` sources are
`bandFreiheitssatz_of_windowData` and, through `Low.windowSplitting_v2`, the two `Low/` stubs of
(P-A) and (P-B) -- verified in this session.)

### The two remaining gaps, and what was done about them

0. **A NEW sufficient condition for the splitting, the *pin*, and its limit (this session).**  The
   splitting `Function.Injective (hnnConjMap (winVertex …) (mk τ))` is *implied* by the concrete,
   gauge-level condition

   `hpin : ∀ j ∈ [lo,hi], Wt j * (Wt 1) ^ (-j) ∈ loopsInE c (winE c lo hi)`

   (`Work.pinAux.hnnConjMap_injective_of_pin` — **PROVED this session**, sorry-free, with the
   generation half as the separate theorem
   `Work.pinAux.loopsInE_sup_closure_Wt_one_eq_top` and the "Schreier basis of a window"
   `Work.pinAux.loopsInE_eq_closure_stbLoop`:
   `loopsInE c E = Subgroup.closure (stbLoop Wt c '' E)` — the window loop group is *generated* by
   the loop classes of the window edges).  The left inverse is constructed explicitly with the
   `τ`-coordinates; see `NOTES_pin_route_and_its_limit.md` for the construction and for the finding
   that **the pin forces the walk of `Wt 1` into the levels `{0,1}`, hence essentially requires a
   generator of weight `±1`** — i.e. the pin covers the *divisibility* cases of the Magnus step and
   cannot close this file's residual, whose hypothesis `hnd` excludes weight-`±1` letters.  The
   residual therefore still needs the graph-of-spaces step of Linton's Proposition 4.3, not the pin.

1. **The workspace-level `decor_replicate_true` clash is RESOLVED here.**  The window data of the
   minimal `Z`-domain is available sorry-free as `Work.OROneRel.exists_window_support_data_cycred`,
   and the Freiheitssatz is the fleet's active statement
   `Work.OROneRel.bandFreiheitssatz_of_windowData` (its reduction to the intersection hypothesis
   `hI`, `bandFreiheitssatz_of_windowData_of_intersection`, is proved in the same file).  But **no
   module used to be able to import both**: the closure of the first contains
   `Submission.Work.OROneRel.decor_wordOf_zpow_of` and that of the second contains
   `Submission.Work.OROneRel.twoLetter_cycle_decor`, and *both* declare
   `Work.OROneRel.decor_replicate_true` (a 2-argument and a 4-argument version), so Lean refused the
   second import.  That was the structural blocker of the whole general (non-two-letter) case.
   **Fix, done in this session:** the six modules `Submission/Work/OROneRel/*_nc.lean`
   (`decor_wordOf_zpow_of_nc`, `reach_unit_weight_nc`, `reach_winWindowData_two_nc`,
   `exists_winWindowData_nc`, `exists_winData_containing_one_nc`,
   `exists_window_support_data_cycred_nc`) are **namespaced copies** (`Work.OROneRel.NC`) of the
   window-data chain, in which `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true` and
   no longer clashes.  They contain no new mathematics, and they let the two halves be combined —
   `Submission/Work/OROneRel/tmp_nccombine` was the test that this now builds.  *(If the colleagues'
   originals change, refresh the copies.)*
2. **`winVertex_generation_of_htr` is *proved*** (`Submission/Work/OROneRel/winSplitNoPin.lean`,
   sorry-free): so the *generation* half of the splitting is available (from the containment of the
   walk of `τ ^ i` in the window), and the real content of the second gap is the **injectivity of the
   comparison map** (the consistency of the coedge labels / the graph-of-spaces splitting).  The
   *cycle-free* statements of it are `Work.OROneRel.magnus_residual_winSplitting` (used here),
   `Work.OROneRel.exists_tree_of_windowData` (the Bass–Serre tree, giving `hinj` through the proved
   `Work.OROneRel.hnnConjMap_injective_of_tree`) and the older
   `Work.OROneRel.winConsistencyResidual`; the newer `magnus_residual_winSplitting_v2` and
   `magnus_residual_winTreeSplitting` **do** import this file (for `FreeKernelCase` /
   `NielsenCountCase`) and therefore cannot be used here.


`magnus_step_root` itself is proved from the residual plus: the exponent-sum-zero case
`magnus_step_root_eps_zero` (inlined) and the case analysis inside
`magnus_step_root_no_eps_zero_main` -- a letter occurring once on one side only (`hnlo`); a letter
carrying a killing weight of value one (the weighted/divisibility step `magnusStepCase2_of_weight`);
the free-kernel case at `l = 1` (`magnusStepCase2_of_freeKernel`, wired in semantically inside the
support-normalised callback); the Nielsen count case (`magnusStepNielsenRoute`); the cyclic-reduction
transport; and the free-generator reduction `magnus_step_residual_of_support`.  The exponent-sum-zero
case rests on the classical Magnus--Moldavanskii rewriting
(`Submission.Work.OROneRel.mmStepData_of_expsum_zero`).

The long comment block above the residual records, for the record, which *elementary* routes to the
residual are dead and why (they were superseded by the two planks above, but the analysis is what
motivates them): the Nielsen/divisibility route (`a^4 b^7`, `a^6 b^14`, …), the `⊤`/weight-kernel
route (fails for non-fibered roots), and the meet-condition/telescoping recognition criteria (both
machine-checked FALSE).  A **SESSION NOTE** (immediately above the residual) carries the older
state: the count case is *not* automatic for `≥ 3` letters (counterexample `a^105 b^156 c^170`), the
two-letter Tietze/amalgam structure `⟨a,b | (a^p b^q)^l⟩ ≅ (ℤ ∗ ℤ/l) ∗_ℤ ℤ`, and the fact that the
vertex of any valid decomposition must have infinite index.
What the file *does* provide for that case, all sorry-free, is

* `magnus_step_root_of_eps_zero_image`: any automorphic image `ψ u` that is cyclically reduced,
  contains a letter `t` of vanishing exponent sum and has a strictly shorter Magnus rewriting gives
  the target for `u` -- the reusable interface for every future construction;
* `magnus_step_root_of_dvd`: the *divisibility* case `eps t u = c * eps y u`, given that the
  cost-free substitution `rightPow t q` (`q` supported on `{y}`, `q y = c`) preserves cyclic
  reducedness and the letter `t`;
* `magnus_step_root_of_dvd_large`: the packaged `|c| ≥ 2` case, taking the rotation witness as a
  hypothesis (that witness is FALSE in general -- see the comment above the gap);
* `magnus_step_root_no_eps_zero_of_letter_once`: the case in which some letter of `u` occurs on one
  side only, exactly once (`Submission.Work.OROneRel.magnus_step_root_of_letter_once`, proved by a
  colleague; the proof is the Tietze transformation `⟨α | u ^ l⟩ ≅ F(α ∖ {x}) ∗ ℤ/l`);
* the parametrised data layer `HasMagnusDataAt` with its transports `magnus_data_of_conj`,
  `magnus_data_of_aut`, `magnus_data_of_eps_zero_image`, which is what makes the various steps
  chainable (the norm bound must be carried by hand, since conjugating or applying an automorphism
  changes `relatorNorm`).

*Historical analysis (superseded by the reduction to the two planks above).*  What is *left* in `magnus_step_root_no_eps_zero` is therefore: roots `u` in which every letter occurs
at least twice, no two exponent sums divide each other in the cost-free way, and whose
letter-occurrence pattern makes the cost-free substitution lose the letter — for the rank-two
examples `u = a ^ 4 * b ^ 7` (no divisibility at all: `gcd 4 7 = 1` but the Nielsen route needs
`|c| = 4/7`) and `u = a ^ 6 * b ^ 14` (the divisibility is `2`, but the cost forces at least 25
non-`t` letters against a budget of 19), together with the run-length degeneracies above.  For these
the cyclic-cover / `Z`-domain construction of Masters and Linton (arXiv 2202.11324, §§4–5) is
required: one takes the `Z`-cover of the presentation complex induced by a weight `σ` with
`σ u = 0`, cuts out a minimal `Z`-domain, and obtains the HNN splitting of `π₁` over the fundamental
group of that domain, whose relator is a *rewriting* of `u` in the domain's free basis — a word of
length at most `|u| - 1` (the domain's spanning tree may be chosen to contain an edge of the lift of
`u`), giving the required strict decrease with the exponent `l` untouched.

## The statement

For `u : FreeGroup α` which is *not a proper power* and `1 ≤ l`, the one-relator group
`⟨α | u ^ l⟩` either has `relatorNorm u ≤ 1` (so that `u` is a single letter: the base case of the
induction), or it is an HNN extension of a presentation `⟨β | v ^ l⟩` with the *same* exponent `l`
and a strictly shorter root `v` (again not a proper power), and the class of `u` becomes conjugate
to the class of `v` in the base.  This is the inductive step of the proof of the
Karrass--Magnus--Solitar torsion theorem `Work.OROneRel.KMSTorsionAt` (see
`Submission/Work/OROneRel/kms_torsion_at.lean`, where the statement is consumed as
`HasMagnusStep`): the exponent `l` -- hence the order of the root -- survives the step, while the
root gets strictly shorter, so that strong induction on `relatorNorm` terminates.

## The toolbox

The combinatorial engine of the Magnus step is the *Magnus rewriting* `magRew t acc L`: the
`t`-letters of `L` are deleted and every other letter is decorated by the running exponent sum of
`t` before it.  If that exponent sum vanishes, the rewriting is compatible with concatenation and
hence with powers (`magRew_append`, `magRew_flatten_replicate_of_wordEps_eq_zero`), which is what
makes the exponent `l` -- and therefore the root -- survive the step.  This file records those
word-level facts together with their consequences for `relatorNorm (magnet u t)`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.magnus_step_root_of_conj_zpow
import Submission.Work.OROneRel.presentedGroup_pow_conj_iso
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.relatorNorm_pow_of_isCyclicallyReduced
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.rightPowDefs
import Submission.Work.OROneRel.rightPow_mulEquiv
import Submission.Work.OROneRel.nonTLetters_rightPow_le
import Submission.Work.OROneRel.sigma_rightPow
import Submission.Work.OROneRel.nonTLetters_lt_norm
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.eps_rightPow
import Submission.Work.OROneRel.magnus_step_root_of_letter_once
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.relatorNorm_of_zpow
import Submission.Work.OROneRel.presentedGroup_pow_one_iso_freeGroup
import Submission.Work.OROneRel.presentedGroup_map_injective_of_preimage
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.exists_cover_root_data
import Submission.Work.OROneRel.coverClass_injective
import Submission.Work.OROneRel.exists_covec_killing
import Submission.Work.OROneRel.coverLevelSet_ncard_two
import Submission.Work.OROneRel.not_isProperPower_coverRoot_of_count_one
-- the two-letter Tietze transformation `⟨a, b | (a ^ p * b ^ q) ^ l⟩ ≅ ⟨a, b, c | c ^ l, b ^ q c⁻¹ a ^ p⟩`
-- (proved by a colleague; it does not import this file).  `twoLetter_amalgam_tietze` carries the
-- element `a ^ p * b ^ q` to the *generator* `c` of the second presentation, which is why the
-- two-letter case of the residual can be attacked in that presentation (`hasMagnusStepAt_twoLetter_of_hnnData`).
import Submission.Work.OROneRel.twoLetter_amalgam_tietze
-- -- the two-letter block-word case (`a ^ p * b ^ q`, `gcd p q = 1`, every `l ≥ 1`) is DELEGATED to
-- -- `Submission/Work/OROneRel/magnusStepAt_blockWord.lean`; it rests on the colleague's
-- -- `Submission.Work.OROneRel.twoLetter_hnnData` (two-letter splitting) and on the relabelling
-- -- transport, neither of which is imported here (importing `twoLetter_hnnData` would pull in the
-- -- colleague's `magnus_step_root_no_eps_zero`, whose statement has the same *name* as the theorem
-- -- below, and the transport `hasMagnusStepAt_map_of_injective` is single-universe).  Import it and
-- -- delete this comment once it has landed.
-- the *weighted* Magnus--Moldavanskii step (a colleague's file; it does not import this one):
-- it subsumes the exponent-sum-zero case (`c = δ_t`, `cohom c u = eps t u = 0`) and the
-- divisibility case, and it is wired into `magnus_step_root_no_eps_zero` below, so that the
-- residual statement carries the sharp hypothesis "no letter `t` carries a killing weight `c`
-- with `c t = 1`".
import Submission.Work.OROneRel.magnusStepCase2_of_weight
-- the free-generator reduction of the residual (proved in a colleague's file; the reduction
-- `magnus_step_residual_of_support` derives the general residual from its "support-normalized"
-- form, in which every generator of the ambient type occurs in `u`):
import Submission.Work.OROneRel.magnus_step_residual_of_support
-- the *free-kernel* case of the residual (a colleague's file; it does not import this one): at
-- `l = 1`, a killing weight `c` whose kernel `ker (presentedCohom c u 1 hc)` is *free* makes
-- `⟨α | u ^ 1⟩` an HNN extension of that free vertex (the ℤ-quotient HNN structure
-- `hnnKernelForm_tracking`, which needs no Britton input because the kernel is normal), and the
-- l = 1 root tracking is automatic.  This removes every *fibered* instance from the residual --
-- in particular all torus relators `a ^ p * b ^ q` with `a ≠ b`, `2 ≤ p, q`, whose kernel is free
-- by `Work.OROneRel.isFreeGroup_ker_rescaledChi`.
import Submission.Work.OROneRel.magnusStepCase2_of_freeKernel
-- the *Nielsen count* route (a colleague's file; it does not import this one): the weighted Magnus
-- step at an *automorphic image* `ψ u`, in the sharp count form -- the norm of the new root is
-- bounded by the number of letters of `ψ u` different from the deleted letter `t`.  This is a case
-- of the residual which holds for *every* `l ≥ 1` and which covers the two-letter torus-type roots
-- `x ^ p y ^ q` of `Submission.Work.OROneRel.magnusStepNielsenTorusFamily` (the pairs with
-- `(p - 1)|m| + (m + q) < p + q` for the transvection `x ↦ x y ^ m`, e.g. `(2,3)`, `(2,5)`, `(3,4)`,
-- `(3,5)`, `(3,7)`, `(4,3)`, `(4,5)`, `(5,4)`), so that those instances leave the residual.
import Submission.Work.OROneRel.magnusStepNielsenRoute
-- ## The two planks the residual now rests on (a colleague's modules; none of them imports this one)
--
-- `Submission.Work.OROneRel.winSplitResidual` contains the *pin-free* residual of the `Z`-domain
-- (window) route to the splitting of `⟨α | u ^ l⟩` over the window vertex, split into the two
-- statements that the fleet is attacking:
--
--   * `Work.OROneRel.winFreiheitssatzResidual` — the existence of the *canonical* window data
--     (weight, band, tree-path gauge) together with the **Freiheitssatz of the domain**
--     (`winRho x ∈ ⟪u ^ l⟫ → x ∈ ⟪winRoot ^ l⟫`), i.e. Linton's `π₁`-injectivity of the minimal
--     `Z`-domain (`One-relator hierarchies`, arXiv 2202.11324, Prop. 4.9, via the Magnus
--     Freiheitssatz Thm. 2.6);
--   * `Work.OROneRel.winConsistencyResidual` — the consistency of the coedge labels and the
--     generation plank, i.e. Linton's graph-of-spaces splitting `G ≅ HNN(π₁D, π₁(D ∩ t⁻¹D),
--     π₁(D ∩ tD), ψ)` (Prop. 4.3, with Prop. 2.2.19).
--
-- Together with the *proved* `Work.OROneRel.magnusDomainDatum_of_consistencyData`,
-- `Work.OROneRel.winTheta_injective_of_freiheitssatz`, `Work.OROneRel.winRootNormLt` and the
-- aperiodicity of the window root, they produce the `Z`-domain datum, which
-- `Work.OROneRel.magnus_step_root_no_eps_zero_of_domainDatum` (in the colleague's module
-- `Submission.Work.OROneRel.magnus_step_root_no_eps_zero`) transports to the target.  The residual
-- below is therefore a *reduction to those two planks*: this file has no open obligation of its own
-- any more, and closing the two planks closes this file.
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winSplitResidual
import Submission.Work.OROneRel.winTheta_injective_of_freiheitssatz
import Submission.Work.OROneRel.winRootNormLt
import Submission.Work.OROneRel.magnus_step_root_no_eps_zero
-- **The two-letter block case, proved for every `l ≥ 1`** (a colleague's module, this session; it
-- does not import this file): `Work.OROneRel.magnusStepAt_blockWord` gives the target's second
-- disjunct for `u = a ^ p * b ^ q` (`a ≠ b`, `1 ≤ p, q`, `gcd p q = 1`) from the two-letter
-- `Z`-domain splitting `Work.OROneRel.twoLetter_hnnData`.
import Submission.Work.OROneRel.magnusStepAt_blockWord
-- **The window-data/Freiheitssatz combination — the one thing the workspace could not do before.**
-- The *proved* window data of the minimal `Z`-domain lives in
-- `Work.OROneRel.exists_window_support_data_cycred`, whose import closure contains
-- `Work.OROneRel.decor_replicate_true` (`Submission.Work.OROneRel.decor_wordOf_zpow_of`); the
-- Freiheitssatz lives (as the fleet's active statement `Work.OROneRel.bandFreiheitssatz_of_windowData`)
-- in a closure containing `Submission.Work.OROneRel.twoLetter_cycle_decor`, which declares
-- `Work.OROneRel.decor_replicate_true` as well.  Lean therefore refuses to import both.  The six
-- modules `Submission/Work/OROneRel/*_nc.lean` are **namespaced copies** (`Work.OROneRel.NC`) of the
-- window-data chain, in which `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true` and
-- no longer clashes; with them the two halves can finally be combined.
import Submission.Work.OROneRel.exists_window_support_data_cycred_nc
import Submission.Work.OROneRel.bandFreiheitssatz_of_windowData
-- **The splitting side of the residual.**  `Work.OROneRel.Low.windowSplitting_v2`
-- (`Submission/Work/OROneRel/winSplittingLow.lean`) is the pair form of the window splitting
-- (generation of `⟨α | u ^ l⟩` by the vertex together with a weight-one deck element `τ`, and
-- injectivity of the canonical comparison map `hnnConjMap`), *with the case hypotheses of this
-- residual in scope*, assembled below this file from the two halves of Linton's `Z`-domain
-- splitting.  Hence the `Z`-domain datum through `Work.OROneRel.magnusDomainDatum_of_hnnConjMap`.
--
-- The older statement `Work.OROneRel.magnus_residual_winSplitting` -- the same conclusion *without*
-- the case hypotheses -- is no longer used here: the case hypotheses are the only shape in which the
-- route through the free-group coset graph and the generation plank is available, and (see the
-- header of `Submission/Work/OROneRel/magnus_residual_winTreeSplitting.lean`) the un-strengthened
-- forms of the two halves are *false* for some window data.
import Submission.Work.OROneRel.winSplittingLow
import Submission.Work.OROneRel.winSplittingOfHnnConj
-- **The case predicates of the residual**, declared at the bottom of the hierarchy so that the
-- modules whose statements carry them as hypotheses can live *below* this file (see the header of
-- `Submission/Work/OROneRel/magnusCaseDefs.lean`).
import Submission.Work.OROneRel.magnusCaseDefs

-- ## The shape of the proof
--
-- `magnus_step_root` reduces `u` to its cyclically reduced conjugate
-- `w = cyclicReduction u` (using `exists_cyclicallyReduced_conjugate` and the transport lemmas
-- proved below), and then splits into three cases, each of which is proved by a colleague in
-- parallel:
--
--   * `Submission.Work.OROneRel.magnus_step_root_eps_zero`     (`w` has a letter with `eps = 0`):
--     the Magnus--Moldavanskii step with the exponent-sum-zero Magnus rewriting;
--   * `Submission.Work.OROneRel.magnus_step_root_no_eps_zero`  (no letter of `w` has `eps = 0`):
--     the remaining Magnus--Moldavanskii step;
--   * `Submission.Work.OROneRel.magnus_step_root_of_conj_zpow` (`relatorNorm w ≤ 1`, so that `u` is
--     conjugate to a generator): the decomposition of `ℤ/l ∗ F` as an HNN extension;
--
-- together with the cyclic-reduction transport
--
--   * `Submission.Work.OROneRel.presentedGroup_pow_conj_iso`   (`⟨α | u^l⟩ ≃* ⟨α | w^l⟩`).
--
-- The toolboxes used by those pieces -- the Magnus rewriting facts (`magRew_append`,
-- `magRew_flatten_replicate_of_wordEps_eq_zero`), the "root survives the power" statement
-- (`mk_magRew_pow`), the `magnet` norm bounds and the transport lemmas for the cyclic reduction --
-- are proved in this file above the assembly.

namespace Work.OROneRel

universe u

variable {α : Type u}

section MagnusToolbox

/-- The exponent sum of the empty word is `0`. -/
theorem wordEps_nil (t : α) : wordEps t ([] : List (α × Bool)) = 0 := by
  classical
  simp [wordEps]

/-- The exponent sum of a one-letter word is the signed contribution of that letter. -/
theorem wordEps_singleton [DecidableEq α] (t : α) (p : α × Bool) :
    wordEps t [p] = if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0 := by
  classical
  simp [wordEps]

/-- The exponent sum of a concatenation is the sum of the exponent sums. -/
theorem wordEps_append [DecidableEq α] (t : α) (L₁ L₂ : List (α × Bool)) :
    wordEps t (L₁ ++ L₂) = wordEps t L₁ + wordEps t L₂ := by
  classical
  simp [wordEps, List.map_append, List.sum_append]

/-- The exponent sum of a word, read off from the first letter. -/
theorem wordEps_cons [DecidableEq α] (t : α) (p : α × Bool) (L : List (α × Bool)) :
    wordEps t (p :: L) = (if p.1 = t then (if p.2 then (1 : ℤ) else -1) else 0) + wordEps t L := by
  rw [← List.singleton_append, wordEps_append, wordEps_singleton]

/-- The Magnus rewriting of the empty word is empty. -/
theorem magRew_nil (t : α) (acc : ℤ) : magRew t acc ([] : List (α × Bool)) = [] := by
  classical
  simp only [magRew]

/-- The Magnus rewriting, read off from the first letter: a `t`-letter is deleted (and the running
exponent sum updated), and any other letter is decorated by the running exponent sum before it. -/
theorem magRew_cons [DecidableEq α] (t : α) (acc : ℤ) (p : α × Bool) (L : List (α × Bool)) :
    magRew t acc (p :: L)
      = if h : p.1 = t then magRew t (acc + (if p.2 then (1 : ℤ) else -1)) L
        else ((⟨p.1, h⟩, acc), p.2) :: magRew t acc L := by
  classical
  simp only [magRew]
  split <;> rfl

/-- The Magnus rewriting is compatible with concatenation: the decoration of the second factor
starts at the accumulated exponent sum of the first one. -/
theorem magRew_append [DecidableEq α] (t : α) (L₁ L₂ : List (α × Bool)) (acc : ℤ) :
    magRew t acc (L₁ ++ L₂) = magRew t acc L₁ ++ magRew t (acc + wordEps t L₁) L₂ := by
  induction L₁ generalizing acc with
  | nil => simp [magRew_nil, wordEps_nil]
  | cons p L ih =>
    by_cases h : p.1 = t
    · have hδ : wordEps t (p :: L) = (if p.2 then (1 : ℤ) else -1) + wordEps t L := by
        rw [wordEps_cons, if_pos h]
      rw [List.cons_append, hδ, magRew_cons t acc p (L ++ L₂), dif_pos h,
        magRew_cons t acc p L, dif_pos h, ih (acc + (if p.2 then (1 : ℤ) else -1)),
        show acc + ((if p.2 then (1 : ℤ) else -1) + wordEps t L)
          = (acc + (if p.2 then (1 : ℤ) else -1)) + wordEps t L from by ring]
    · have hδ : wordEps t (p :: L) = 0 + wordEps t L := by
        rw [wordEps_cons, if_neg h]
      rw [List.cons_append, hδ, magRew_cons t acc p (L ++ L₂), dif_neg h,
        magRew_cons t acc p L, dif_neg h, ih acc, List.cons_append,
        show acc + (0 + wordEps t L) = acc + wordEps t L from by ring]

/-- The Magnus rewriting is never longer than the original word. -/
theorem magRew_length_le [DecidableEq α] (t : α) (acc : ℤ) (L : List (α × Bool)) :
    (magRew t acc L).length ≤ L.length := by
  induction L generalizing acc with
  | nil => simp [magRew_nil]
  | cons p L ih =>
    by_cases h : p.1 = t
    · rw [magRew_cons t acc p L, dif_pos h]
      exact le_trans (ih _) (Nat.le_succ _)
    · rw [magRew_cons t acc p L, dif_neg h]
      exact Nat.succ_le_succ (ih acc)

/-- The Magnus rewriting is strictly shorter than the original word as soon as the word contains a
letter equal to `t`. -/
theorem magRew_length_lt [DecidableEq α] (t : α) (acc : ℤ) (L : List (α × Bool))
    (h : ∃ b : Bool, (t, b) ∈ L) : (magRew t acc L).length < L.length := by
  induction L generalizing acc with
  | nil => exact absurd h (by simp)
  | cons p L ih =>
    by_cases hp : p.1 = t
    · rw [magRew_cons t acc p L, dif_pos hp, List.length_cons]
      exact Nat.lt_succ_of_le (magRew_length_le t _ L)
    · rw [magRew_cons t acc p L, dif_neg hp, List.length_cons, List.length_cons]
      obtain ⟨b, hb⟩ := h
      have hbL : (t, b) ∈ L := by
        rcases List.mem_cons.mp hb with h' | h'
        · exfalso
          have : p.1 = t := by rw [← h']
          exact hp this
        · exact h'
      exact Nat.succ_lt_succ (ih acc ⟨b, hbL⟩)

/-- `(L.replicate (n+1)).flatten = L ++ (L.replicate n).flatten`. -/
private theorem flatten_replicate_succ {β : Type*} (L : List β) (n : ℕ) :
    (List.replicate (n + 1) L).flatten = L ++ (List.replicate n L).flatten := by
  rw [List.replicate_succ, List.flatten_cons]

/-- If the exponent sum of `t` in `L` vanishes, the Magnus rewriting of a repetition of `L` is the
corresponding repetition of the rewriting: the decorations of the successive copies of `L` agree. -/
theorem magRew_flatten_replicate_of_wordEps_eq_zero [DecidableEq α] (t : α) (acc : ℤ)
    (L : List (α × Bool)) (hL : wordEps t L = 0) (n : ℕ) :
    magRew t acc (List.replicate n L).flatten
      = (List.replicate n (magRew t acc L)).flatten := by
  induction n generalizing acc with
  | zero => simp [magRew_nil]
  | succ n ih =>
    have hacc : acc + wordEps t L = acc := by rw [hL, add_zero]
    rw [flatten_replicate_succ, flatten_replicate_succ, magRew_append, hacc, ih]

/-- `FreeGroup.mk [] = 1`. -/
theorem mk_nil_eq_one [DecidableEq α] : FreeGroup.mk ([] : List (α × Bool)) = 1 := by
  rw [← FreeGroup.toWord_eq_nil_iff, FreeGroup.toWord_mk]
  simp

/-- The reduced word of a power of a cyclically reduced element is the concatenation of the copies:
no cancellation occurs at the joints. -/
theorem toWord_pow_of_isCyclicallyReduced [DecidableEq α] (u : FreeGroup α)
    (h : FreeGroup.IsCyclicallyReduced u.toWord) (l : ℕ) :
    (u ^ l).toWord = (List.replicate l u.toWord).flatten := by
  have key : u ^ l = FreeGroup.mk ((List.replicate l u.toWord).flatten) := by
    induction l with
    | zero => rw [pow_zero, List.replicate_zero, List.flatten_nil, mk_nil_eq_one]
    | succ l ih =>
      calc u ^ (l + 1) = u * u ^ l := pow_succ' u l
        _ = FreeGroup.mk u.toWord * FreeGroup.mk ((List.replicate l u.toWord).flatten) := by
              rw [ih, FreeGroup.mk_toWord]
        _ = FreeGroup.mk (u.toWord ++ (List.replicate l u.toWord).flatten) := FreeGroup.mul_mk
        _ = FreeGroup.mk ((List.replicate (l + 1) u.toWord).flatten) := by
              rw [List.replicate_succ, List.flatten_cons]
  rw [key, FreeGroup.toWord_mk,
    (FreeGroup.isReduced_iff_reduce_eq).mp (h.flatten_replicate l).isReduced]

-- `mk` of a repeated word is the corresponding power: this is `Work.OROneRel.mk_flatten_replicate`
-- from `Submission.Work.OROneRel.exists_common_power` (a colleague's file, now in the import cone),
-- with the two sides of the equation interchanged.

/-- **The root survives the power.**  For a cyclically reduced `u` whose exponent sum in the letter
`t` vanishes, the Magnus rewriting of the relator `u ^ l` is the `l`-th power of the Magnus
rewriting of `u`: the decorations of the successive copies of `u` agree, which is what keeps the
exponent `l` -- and hence the root -- intact in the Magnus step. -/
theorem mk_magRew_pow [DecidableEq α] (u : FreeGroup α) (t : α) (l : ℕ)
    (h : FreeGroup.IsCyclicallyReduced u.toWord) (he : wordEps t u.toWord = 0) :
    FreeGroup.mk (magRew t 0 (u ^ l).toWord) = (FreeGroup.mk (magRew t 0 u.toWord)) ^ l := by
  have h1 := toWord_pow_of_isCyclicallyReduced u h l
  have h2 := magRew_flatten_replicate_of_wordEps_eq_zero t 0 u.toWord he l
  rw [h1, h2, mk_flatten_replicate]

end MagnusToolbox

section MagnetNorm

/-- The relator length of the Magnus rewriting of `u` with respect to `t` is at most the relator
length of `u`. -/
theorem relatorNorm_magnet_le (u : FreeGroup α) (t : α) :
    relatorNorm (magnet u t) ≤ relatorNorm u := by
  classical
  have h1 : @FreeGroup.norm ({x : α // x ≠ t} × ℤ) (Classical.decEq _)
      (FreeGroup.mk (magRew t 0 u.toWord)) ≤ (magRew t 0 u.toWord).length :=
    @FreeGroup.norm_mk_le ({x : α // x ≠ t} × ℤ) (magRew t 0 u.toWord) (Classical.decEq _)
  have h2 : relatorNorm (magnet u t)
      = @FreeGroup.norm ({x : α // x ≠ t} × ℤ) (Classical.decEq _)
          (FreeGroup.mk (magRew t 0 u.toWord)) := rfl
  have h3 : (magRew t 0 u.toWord).length ≤ (u.toWord).length :=
    magRew_length_le t (0 : ℤ) u.toWord
  have h4 : (u.toWord).length = relatorNorm u := rfl
  omega

/-- A letter equal to `t` occurring in `u` makes the Magnus rewriting strictly shorter: the deleted
`t`-letters are not counted. -/
theorem relatorNorm_magnet_lt (u : FreeGroup α) (t : α) (ht : t ∈ relatorLetters u) :
    relatorNorm (magnet u t) < relatorNorm u := by
  classical
  obtain ⟨b, hb⟩ := ht
  have h1 : @FreeGroup.norm ({x : α // x ≠ t} × ℤ) (Classical.decEq _)
      (FreeGroup.mk (magRew t 0 u.toWord)) ≤ (magRew t 0 u.toWord).length :=
    @FreeGroup.norm_mk_le ({x : α // x ≠ t} × ℤ) (magRew t 0 u.toWord) (Classical.decEq _)
  have h2 : relatorNorm (magnet u t)
      = @FreeGroup.norm ({x : α // x ≠ t} × ℤ) (Classical.decEq _)
          (FreeGroup.mk (magRew t 0 u.toWord)) := rfl
  have h3 : (magRew t 0 u.toWord).length < (u.toWord).length :=
    magRew_length_lt t (0 : ℤ) u.toWord ⟨b, hb⟩
  have h4 : (u.toWord).length = relatorNorm u := rfl
  omega

end MagnetNorm

section NormOne

/-- A nontrivial element of relator length at most one is a power of a generator of exponent `±1`. -/
theorem exists_zpow_of_relatorNorm_le_one {r : FreeGroup α} (h : relatorNorm r ≤ 1)
    (hr : r ≠ 1) :
    ∃ (a : α) (k : ℤ), (k = 1 ∨ k = -1) ∧ r = FreeGroup.of a ^ k := by
  classical
  have hlen : r.toWord.length ≤ 1 := h
  have hne : r.toWord ≠ [] := fun h0 => hr (FreeGroup.toWord_eq_nil_iff.mp h0)
  have hpos : 0 < r.toWord.length := List.length_pos_iff.mpr hne
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp (by omega : r.toWord.length = 1)
  have hr' : r = FreeGroup.mk [p] := by rw [← FreeGroup.mk_toWord (x := r), hp]
  obtain ⟨a, b⟩ := p
  cases b
  · refine ⟨a, -1, Or.inr rfl, ?_⟩
    rw [hr', zpow_neg_one,
      show FreeGroup.of a = FreeGroup.mk [(a, true)] from rfl, FreeGroup.inv_mk]
    simp [FreeGroup.invRev]
  · refine ⟨a, 1, Or.inl rfl, ?_⟩
    rw [hr', zpow_one]
    rfl

end NormOne

section CyclicReduction

/-- Powers of a conjugate: `(c * w * c⁻¹) ^ k = c * w ^ k * c⁻¹`. -/
theorem conj_pow_eq (c w : FreeGroup α) (k : ℕ) :
    (c * w * c⁻¹) ^ k = c * w ^ k * c⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih]; group

/-- Being a proper power is invariant under conjugation. -/
theorem isProperPower_conj_iff (c w : FreeGroup α) :
    IsProperPower (c * w * c⁻¹) ↔ IsProperPower w := by
  constructor
  · rintro ⟨z, k, hk, hz⟩
    refine ⟨c⁻¹ * z * c, k, hk, ?_⟩
    have h2 : (c⁻¹ * z * c) ^ k = c⁻¹ * z ^ k * c := by
      simpa using conj_pow_eq c⁻¹ z k
    rw [h2, ← hz]
    group
  · rintro ⟨z, k, hk, hz⟩
    refine ⟨c * z * c⁻¹, k, hk, ?_⟩
    rw [hz, conj_pow_eq]

/-- The cyclic reduction of an element that is not a proper power is not a proper power. -/
theorem not_isProperPower_cyclicReduction {u : FreeGroup α} (hu : ¬ IsProperPower u) :
    ¬ IsProperPower (cyclicReduction u) := by
  intro h
  refine hu ?_
  have hc := cyclicConjugator_mul_cyclicReduction_mul_inv u
  rw [← hc]
  exact (isProperPower_conj_iff (cyclicConjugator u) (cyclicReduction u)).mpr h

/-- The cyclic reduction never increases the relator length. -/
theorem relatorNorm_cyclicReduction_le (u : FreeGroup α) :
    relatorNorm (cyclicReduction u) ≤ relatorNorm u := by
  classical
  have h1 : (cyclicReduction u).norm ≤ (FreeGroup.reduceCyclically u.toWord).length := by
    unfold cyclicReduction
    exact FreeGroup.norm_mk_le (L₁ := FreeGroup.reduceCyclically u.toWord)
  have h2 : (FreeGroup.reduceCyclically u.toWord).length ≤ (u.toWord).length := by
    have h := congrArg List.length
      (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically u.toWord)
    simp only [List.length_append, FreeGroup.invRev_length] at h
    omega
  simpa only [relatorNorm, FreeGroup.norm] using le_trans h1 h2

end CyclicReduction

-- ---------------------------------------------------------------------------------------------
-- The exponent-sum-zero case, proved in parallel by a colleague in
-- `Submission.Work.OROneRel.magnus_step_root_eps_zero` (which imports this module for
-- `magRew_flatten_replicate_of_wordEps_eq_zero`); it is reproduced here so that the assembly below
-- does not create an import cycle.
-- ---------------------------------------------------------------------------------------------

/-! ## 1. The Magnus rewriting of a power -/

/-- The Magnus rewriting of a power of a cyclically reduced word of exponent sum zero in `t` is the
concatenation of the copies of the rewriting. -/
theorem mmList_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) :
    mmList t (u ^ l) = (List.replicate l (mmList t u)).flatten := by
  classical
  have hh : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
    simpa only [IsCyclicallyReducedRelator] using hu
  have hred : FreeGroup.IsReduced (List.flatten (List.replicate l (FreeGroup.toWord u))) :=
    (hh.flatten_replicate l).1
  have hword : FreeGroup.toWord (u ^ l)
      = List.flatten (List.replicate l (FreeGroup.toWord u)) := by
    rw [FreeGroup.toWord_pow, hred.reduce_eq]
  have hw : wordEps t u.toWord = 0 := he
  rw [mmList, mmList, hword,
    magRew_flatten_replicate_of_wordEps_eq_zero t 0 u.toWord hw l,
    magRew_zero_eq_rewrite]

/-- The decorations of a generator `x ≠ t` occurring in the rewriting of `u ^ l` are the same as
those occurring in the rewriting of `u`. -/
theorem mmDecs_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmDecs t (u ^ l) x = mmDecs t u x := by
  classical
  ext k
  rw [mem_mmDecs_iff, mem_mmDecs_iff, mmList_pow t u hu he l]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨L', hL', hb'⟩ := List.mem_flatten.mp hb
    rw [List.eq_of_mem_replicate hL'] at hb'
    exact ⟨b, hb'⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, List.mem_flatten.mpr
      ⟨mmList t u, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩⟩

theorem mmLo_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmLo t (u ^ l) x = mmLo t u x := by
  classical
  rw [mmLo, mmLo, mmDecs_pow t u hu he l hl x]

theorem mmHi_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) (x : {x : α // x ≠ t}) :
    mmHi t (u ^ l) x = mmHi t u x := by
  classical
  rw [mmHi, mmHi, mmDecs_pow t u hu he l hl x]

/-- The interval closure of the decorations is the same for `u` and `u ^ l`. -/
theorem mmDecSet_pow (t : α) (u : FreeGroup α) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (l : ℕ) (hl : 1 ≤ l) :
    mmDecSet t (u ^ l) = mmDecSet t u := by
  ext p
  simp only [mmDecSet, Set.mem_ofPred_eq]
  rw [mmLo_pow t u hu he l hl p.1, mmHi_pow t u hu he l hl p.1]

/-! ## 2. The decorated alphabet of `u ^ l` and the root -/

/-- The transport of the decorated alphabet from `u` to `u ^ l` (the underlying decorated letters are
unchanged). -/
noncomputable def mmTransFun (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : IsCyclicallyReducedRelator u) (he : eps t u = 0) (hl : 1 ≤ l) :
    mmBeta t u → mmBeta t (u ^ l) :=
  fun e => ⟨e.1, (mmDecSet_pow t u hu he l hl).symm ▸ e.2⟩

/-- The Magnus rewriting of `u` with respect to `t`, viewed in the decorated alphabet of `u ^ l`. -/
noncomputable def rootW (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) : FreeGroup (mmBeta t (u ^ l)) :=
  FreeGroup.map (mmTransFun t u l hu he hl) (mmW t u)

theorem mmTransFun_val (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) (e : mmBeta t u) :
    ((mmTransFun t u l hu he hl e : mmBeta t (u ^ l)) : MMAlpha t) = (e : MMAlpha t) := rfl

/-- `rootW` as a word in the decorated alphabet. -/
theorem rootW_eq (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    rootW t u l hu he hl =
      FreeGroup.mk ((mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2))) := by
  rw [rootW, mmW, FreeGroup.map.mk]

/-- `FreeGroup.mk` of a repetition of a word is the corresponding power. -/
theorem mk_flatten_rep {β : Type*} (L : List (β × Bool)) (l : ℕ) :
    FreeGroup.mk ((List.replicate l L).flatten) = (FreeGroup.mk L) ^ l := by
  induction l with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero]; rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- The Magnus rewriting of `u ^ l` is the concatenation of the copies of the rewriting of `u`,
transported to the decorated alphabet of `u ^ l`. -/
theorem mmWL_pow_trans (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    mmWL t (u ^ l) =
      (List.replicate l ((mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2)))).flatten := by
  classical
  have hinner : (mmList t u).map (fun p => (mmBetaOf t (u ^ l) p.1, p.2))
      = (mmWL t u).map (fun q => (mmTransFun t u l hu he hl q.1, q.2)) := by
    rw [show mmWL t u = (mmList t u).map (fun p => (mmBetaOf t u p.1, p.2)) from by rw [mmWL]]
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hpm : p.1 ∈ mmDecSet t u := mmList_mem_decSet t u hp
    have hpm' : p.1 ∈ mmDecSet t (u ^ l) := (mmDecSet_pow t u hu he l hl).symm ▸ hpm
    simp only [Function.comp_apply]
    refine Prod.ext ?_ rfl
    refine Subtype.ext ?_
    rw [mmBetaOf_val t (u ^ l) hpm', mmTransFun_val, mmBetaOf_val t u hpm]
  calc mmWL t (u ^ l)
      = (mmList t (u ^ l)).map (fun p => (mmBetaOf t (u ^ l) p.1, p.2)) := by rw [mmWL]
    _ = (((List.replicate l (mmList t u)).flatten).map
            (fun p => (mmBetaOf t (u ^ l) p.1, p.2))) := by rw [mmList_pow t u hu he l]
    _ = ((List.replicate l (mmList t u)).map
            (List.map (fun p => (mmBetaOf t (u ^ l) p.1, p.2)))).flatten := by rw [List.map_flatten]
    _ = (List.replicate l ((mmList t u).map
            (fun p => (mmBetaOf t (u ^ l) p.1, p.2)))).flatten := by rw [List.map_replicate]
    _ = (List.replicate l ((mmWL t u).map
            (fun q => (mmTransFun t u l hu he hl q.1, q.2)))).flatten := by rw [hinner]

/-- **The `l`-th power of the root is the Magnus rewriting of `u ^ l`.** -/
theorem rootW_pow (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    rootW t u l hu he hl ^ l = mmW t (u ^ l) := by
  rw [rootW_eq, ← mk_flatten_rep ((mmWL t u).map
      (fun q => (mmTransFun t u l hu he hl q.1, q.2))) l, mmW, mmWL_pow_trans t u l hu he hl]

/-! ## 3. The root is again not a proper power and is shorter -/

/-- The expansion of a decorated letter `(x,k)`: the conjugate `t ^ k * x * t ^ (-k)`. -/
noncomputable def mmRhoFun (t : α) (p : MMAlpha t) : FreeGroup α :=
  FreeGroup.of t ^ p.2 * FreeGroup.of (p.1 : α) * FreeGroup.of t ^ (-p.2)

/-- `FreeGroup.lift` commutes with `FreeGroup.map`. -/
theorem lift_comp_map {γ δ M : Type*} [Group M] (f : δ → M) (g : γ → δ) :
    (FreeGroup.lift f).comp (FreeGroup.map g) = FreeGroup.lift (fun a => f (g a)) := by
  refine FreeGroup.ext_hom _ _ fun a => ?_
  rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]

/-- The value of `lift_comp_map` on an element. -/
theorem lift_map_apply {γ δ M : Type*} [Group M] (f : δ → M) (g : γ → δ) (w : FreeGroup γ) :
    FreeGroup.lift f (FreeGroup.map g w) = FreeGroup.lift (fun a => f (g a)) w :=
  congrArg (fun φ : FreeGroup γ →* M => φ w) (lift_comp_map f g)

/-- The expansion of the Magnus rewriting of `u` is `u` itself. -/
theorem lift_mmRho_mmW (t : α) (u : FreeGroup α) (he : eps t u = 0) :
    FreeGroup.lift (fun p : mmBeta t u => mmRhoFun t p.1) (mmW t u) = u := by
  classical
  have hcomp : FreeGroup.lift (fun p : mmBeta t u => mmRhoFun t p.1)
      = (rho t).comp (FreeGroup.map (fun p : mmBeta t u => (p.1 : MMAlpha t))) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
    rw [rho, FreeGroup.lift_apply_of]
    rfl
  rw [hcomp, MonoidHom.comp_apply, mmW_map_val]
  rw [show FreeGroup.mk (mmList t u) = magnet u t from rfl]
  exact rho_magnet u t he

/-- The expansion of the root `rootW` is `u`. -/
theorem lift_mmRho_rootW (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) :
    FreeGroup.lift (fun p : mmBeta t (u ^ l) => mmRhoFun t p.1) (rootW t u l hu he hl) = u := by
  rw [rootW, lift_map_apply]
  have : (fun p : mmBeta t u =>
        mmRhoFun t ((mmTransFun t u l hu he hl p : mmBeta t (u ^ l)) : MMAlpha t))
      = (fun p : mmBeta t u => mmRhoFun t (p : MMAlpha t)) := by
    funext p
    rw [mmTransFun_val]
  rw [this]
  exact lift_mmRho_mmW t u he

/-- The root is not a proper power. -/
theorem not_isProperPower_rootW (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : ¬ IsProperPower u) (hcyc : IsCyclicallyReducedRelator u) (he : eps t u = 0)
    (hl : 1 ≤ l) : ¬ IsProperPower (rootW t u l hcyc he hl) := by
  classical
  rintro ⟨z, k, hk, hzk⟩
  have h := lift_mmRho_rootW t u l hcyc he hl
  rw [hzk, map_pow] at h
  exact hu ⟨FreeGroup.lift (fun p : mmBeta t (u ^ l) => mmRhoFun t p.1) z, k, hk, h.symm⟩

/-- The root is strictly shorter than `u`. -/
theorem relatorNorm_rootW_lt (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) (ht : t ∈ relatorLetters u) :
    relatorNorm (rootW t u l hu he hl) < relatorNorm u := by
  classical
  have h1 : relatorNorm (rootW t u l hu he hl) ≤ (mmList t u).length := by
    rw [rootW_eq]
    refine le_trans FreeGroup.norm_mk_le ?_
    rw [List.length_map, show (mmWL t u).length = (mmList t u).length from by rw [mmWL, List.length_map]]
  have h2 : (mmList t u).length = (rewrite t u.toWord).length := by
    rw [mmList, magRew_zero_eq_rewrite]
  have h3 : (rewrite t u.toWord).length < u.toWord.length := by
    obtain ⟨b, hb⟩ : ∃ b : Bool, (t, b) ∈ u.toWord := ht
    cases b
    · exact rewrite_length_lt t (L := u.toWord) (Or.inr hb)
    · exact rewrite_length_lt t (L := u.toWord) (Or.inl hb)
  have h4 : u.toWord.length = relatorNorm u := rfl
  omega

/-! ## 4. The tracking of the root through the HNN step -/

section Tracking

variable {t : α} {r : FreeGroup α}

/-- The image of the Magnus rewriting in the HNN extension: it is the base element itself. -/
theorem mmTheta_lift_mmRho (hFw : FreiheitssatzAt (mmW t r))
    (hc : IsCyclicallyReducedRelator (mmW t r))
    (hA : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTA t r))
    (hB : (mmW t r) ∉ Subgroup.closure (FreeGroup.of '' mmTB t r))
    (w : FreeGroup (mmBeta t r)) :
    (FreeGroup.lift (mmThetaFun hFw hc hA hB))
        (FreeGroup.lift (fun p : mmBeta t r => mmRhoFun t p.1) w)
      = HNNExtension.of (PresentedGroup.mk ({mmW t r} : Set (FreeGroup (mmBeta t r))) w) := by
  have hcomp : (FreeGroup.lift (mmThetaFun hFw hc hA hB)).comp
        (FreeGroup.lift (fun p : mmBeta t r => mmRhoFun t p.1))
      = (HNNExtension.of).comp (PresentedGroup.mk ({mmW t r} : Set (FreeGroup (mmBeta t r)))) := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    set k : ℤ := (e : MMAlpha t).2 with hk
    set x : {a : α // a ≠ t} := (e : MMAlpha t).1 with hx
    have hkdec : ((x, k) : MMAlpha t) ∈ mmDecSet t r := e.2
    have hkx : mmLo t r x ≤ k := by simpa using hkdec.1
    have hkx2 : k ≤ mmHi t r x := by simpa using hkdec.2
    have hstep : ∀ s : ℕ, s < (k - mmLo t r x).toNat →
        ((x, mmLo t r x + (s : ℤ) + 1) : MMAlpha t) ∈ mmDecSet t r := by
      intro s hs
      have h2 : ((s : ℤ)) < ((k - mmLo t r x).toNat : ℤ) := by exact_mod_cast hs
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)] at h2
      show mmLo t r x ≤ mmLo t r x + (s : ℤ) + 1 ∧ mmLo t r x + (s : ℤ) + 1 ≤ mmHi t r x
      have hs0 : (0 : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
      constructor
      · omega
      · have h3 : mmLo t r x + (s : ℤ) + 1 ≤ k := by omega
        omega
    have hchain := mmChain (r := r) hFw hc hA hB x (mmLo t r x) (mmLo_mem_decSet t r x)
      ((k - mmLo t r x).toNat) hstep
    have hsum : mmLo t r x + ((((k - mmLo t r x).toNat : ℕ) : ℤ)) = k := by
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)]
      ring
    rw [hsum] at hchain
    set X : mmK t r hFw hc hA hB :=
      HNNExtension.of (PresentedGroup.of (mmBetaOf t r ((x, mmLo t r x) : MMAlpha t))) with hX
    rw [mmRhoFun, map_mul, map_mul, map_zpow, map_zpow]
    simp only [FreeGroup.lift_apply_of, mmThetaFun_t (r := r) hFw hc hA hB]
    rw [mmThetaFun_ne (r := r) hFw hc hA hB (y := (x : α)) x.2]
    rw [show (HNNExtension.t : mmK t r hFw hc hA hB) ^ k *
          ((HNNExtension.t : mmK t r hFw hc hA hB) ^ (-(mmLo t r x)) * X *
            (HNNExtension.t : mmK t r hFw hc hA hB) ^ (mmLo t r x)) *
          (HNNExtension.t : mmK t r hFw hc hA hB) ^ (-k)
        = (HNNExtension.t : mmK t r hFw hc hA hB) ^ (((k - mmLo t r x).toNat : ℕ) : ℤ) * X *
          (HNNExtension.t : mmK t r hFw hc hA hB) ^ (-(((k - mmLo t r x).toNat : ℕ) : ℤ)) from by
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - mmLo t r x)]
      group]
    rw [hchain]
    have heq : mmBetaOf t r ((x, k) : MMAlpha t) = e :=
      Subtype.ext (by rw [mmBetaOf_val t r hkdec])
    rw [heq]
    rfl
  exact congrArg (fun f : FreeGroup (mmBeta t r) →* mmK t r hFw hc hA hB => f w) hcomp

end Tracking

/-! ## 5. The Magnus step for the root, exponent-sum-zero case -/

/-- The defining relator set of the base one-relator group of the exponent-sum-zero Magnus step:
the `l`-th power of the transported Magnus rewriting `rootW t u l`. -/
abbrev mmRootRel (t : α) (u : FreeGroup α) (l : ℕ) (hu : IsCyclicallyReducedRelator u)
    (he : eps t u = 0) (hl : 1 ≤ l) : Set (FreeGroup (mmBeta t (u ^ l))) :=
  {(rootW t u l hu he hl) ^ l}

/-- **The nondegenerate alternative of `magnus_step_root`.**  The one-relator group `⟨α | u ^ l⟩`
is an HNN extension of a one-relator group `⟨β | v ^ l⟩` with the *same* exponent `l`, a strictly
shorter root `v` which is again not a proper power, and with the class of `u` conjugate to the class
of `v` in the base.  This is the second disjunct of the statement of `magnus_step_root`, named so
that the transport lemmas below have readable statements. -/
abbrev HasMagnusStepAt {α : Type u} (u : FreeGroup α) (l : ℕ) : Prop :=
  ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < relatorNorm u ∧
    ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
      ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
        e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹

/-- **Invariance of the step under conjugating the root.**  If `u` is conjugate to `w`, then the
HNN data of a Magnus step for `w` (with the norm bound measured against `u`, which is what is
needed in practice since conjugation need not preserve the relator length) transports to `u`: the
conjugating element `c` also conjugates the class of `u` onto the class of `w`, so it is simply
absorbed into the conjugating element of the root condition. -/
theorem magnus_step_root_of_conj {α : Type u} {u w : FreeGroup α} {l : ℕ}
    (hc : ∃ c : FreeGroup α, c * w * c⁻¹ = u)
    (h : ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({w ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ cc : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w) =
            cc * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * cc⁻¹) :
    HasMagnusStepAt u l := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_conj_iso u w c l hc
  obtain ⟨β, v, hpp, hlt, A, B, φ, e₂, cc, hcc⟩ := h
  refine ⟨β, v, hpp, hlt, A, B, φ, e₁.trans e₂,
    e₂ (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c) * cc, ?_⟩
  have h3 : PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u
      = PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c
        * PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w
        * (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c)⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv]
  rw [MulEquiv.trans_apply, he₁, h3, map_mul, map_mul, map_inv, hcc]
  group

theorem magnus_step_root_eps_zero_aux {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (t : α)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u)
    (he : Work.OROneRel.eps t u = 0) :
    ∃ (A B : Subgroup (PresentedGroup (mmRootRel t u l hcyc he hl)))
      (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup (mmRootRel t u l hcyc he hl)) A B φ),
        ∃ c : HNNExtension (PresentedGroup (mmRootRel t u l hcyc he hl)) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk (mmRootRel t u l hcyc he hl)
              (rootW t u l hcyc he hl)) * c⁻¹ := by
  classical
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hcycr : IsCyclicallyReducedRelator (u ^ l) := isCyclicallyReducedRelator_pow hcyc l
  have hepsr : eps t (u ^ l) = 0 := by
    have h1 : sigma t (u ^ l) = 1 := by
      rw [map_pow, (eps_eq_zero_iff_sigma_eq_one t u).mp he, one_pow]
    exact (eps_eq_zero_iff_sigma_eq_one t (u ^ l)).mpr h1
  have hnormu : 0 < relatorNorm u := by
    refine Nat.pos_of_ne_zero fun h0 => hu1 ?_
    have h2 : FreeGroup.norm u = 0 := h0
    exact FreeGroup.norm_eq_zero.mp h2
  have hrne : u ^ l ≠ 1 := by
    intro h
    have h1 : relatorNorm (u ^ l) = 0 := by
      rw [h]
      simp [relatorNorm, FreeGroup.norm]
    rw [relatorNorm_pow_of_isCyclicallyReduced u hcyc l] at h1
    rcases Nat.mul_eq_zero.mp h1 with h2 | h2
    · omega
    · omega
  have htr : t ∈ relatorLetters (u ^ l) := by
    have hh : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
      simpa only [IsCyclicallyReducedRelator] using hcyc
    have hred : FreeGroup.IsReduced (List.flatten (List.replicate l (FreeGroup.toWord u))) :=
      (hh.flatten_replicate l).1
    have hword : FreeGroup.toWord (u ^ l)
        = List.flatten (List.replicate l (FreeGroup.toWord u)) := by
      rw [FreeGroup.toWord_pow, hred.reduce_eq]
    rw [relatorLetters, hword]
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, List.mem_flatten.mpr
      ⟨FreeGroup.toWord u, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩⟩
  have hred : FreeGroup.IsReduced (mmWL t (u ^ l)) := mmWL_isReduced t (u ^ l) hcycr hepsr
  have hFw : FreiheitssatzAt (mmW t (u ^ l)) := freiheitssatz_at _
  have hc : IsCyclicallyReducedRelator (mmW t (u ^ l)) := mmW_isCyclicallyReduced hcycr hepsr
  have hA : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTA t (u ^ l)) :=
    mmW_notMem_closure_TA hrne htr hepsr hred
  have hB : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTB t (u ^ l)) :=
    mmW_notMem_closure_TB hrne htr hepsr hred
  have hrel : FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB) (u ^ l) = 1 :=
    mmThetaFun_relator (r := u ^ l) hepsr hFw hc hA hB
  let Θ : mmG (u ^ l) →* mmK t (u ^ l) hFw hc hA hB := mmTheta (r := u ^ l) hFw hc hA hB hrel
  let Ψ : mmK t (u ^ l) hFw hc hA hB →* mmG (u ^ l) := mmPsi (r := u ^ l) hepsr hFw hc hA hB
  have h1 : Ψ.comp Θ = MonoidHom.id _ := mmPsi_comp_mmTheta (r := u ^ l) hepsr hFw hc hA hB hrel
  have h2 : Θ.comp Ψ = MonoidHom.id _ := mmTheta_comp_mmPsi (r := u ^ l) hepsr hFw hc hA hB hrel
  let e : mmG (u ^ l) ≃* mmK t (u ^ l) hFw hc hA hB := MonoidHom.toMulEquiv Θ Ψ h1 h2
  have hcomp' : Θ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
      = FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact mmTheta_of (r := u ^ l) hFw hc hA hB hrel a
  have htrk : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
      = HNNExtension.of ((PresentedGroup.mk ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))))
          (rootW t u l hcyc he hl)) := by
    show Θ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) = _
    rw [← MonoidHom.comp_apply, hcomp']
    have hroot : (FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB)) u
        = (FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB))
            (FreeGroup.lift (fun p : mmBeta t (u ^ l) => mmRhoFun t p.1)
              (rootW t u l hcyc he hl)) := by
      congr 1
      exact (lift_mmRho_rootW t u l hcyc he hl).symm
    rw [hroot]
    exact mmTheta_lift_mmRho hFw hc hA hB (rootW t u l hcyc he hl)
  have key : ∃ (A B : Subgroup (PresentedGroup (mmRootRel t u l hcyc he hl)))
      (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup (mmRootRel t u l hcyc he hl)) A B φ),
      ∃ c : HNNExtension (PresentedGroup (mmRootRel t u l hcyc he hl)) A B φ,
        e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk (mmRootRel t u l hcyc he hl)
                (rootW t u l hcyc he hl)) * c⁻¹ := by
    rw [show mmRootRel t u l hcyc he hl
        = ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))) from by
      rw [mmRootRel, rootW_pow]]
    exact ⟨mmA t (u ^ l), mmB t (u ^ l), mmPhi (t := t) (r := u ^ l) hFw hc hA hB, e, 1, by
      rw [htrk, one_mul, inv_one, mul_one]⟩
  exact key

/-- **The Magnus step for a root, exponent-sum-zero case.** -/
theorem magnus_step_root_eps_zero {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (t : α)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (ht : t ∈ Work.OROneRel.relatorLetters u)
    (he : Work.OROneRel.eps t u = 0) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  obtain ⟨A, B, φ, e, c, hc⟩ := magnus_step_root_eps_zero_aux u l hl t hu hcyc ht he
  exact ⟨mmBeta t (u ^ l), rootW t u l hcyc he hl,
    not_isProperPower_rootW t u l hu hcyc he hl, relatorNorm_rootW_lt t u l hcyc he hl ht,
    A, B, φ, e, c, hc⟩

/-! ## Transporting the step along an automorphism, and the norm of the transported root -/

/-- The root `rootW t u l` is the Magnus rewriting of `u` written in the decorated alphabet of
`u ^ l`; its relator length is therefore at most the number of non-`t` letters of `u`. -/
theorem relatorNorm_rootW_le_nonTLetters {α : Type u} (u : FreeGroup α) (l : ℕ) (t : α)
    (hcyc : IsCyclicallyReducedRelator u) (he : eps t u = 0) (hl : 1 ≤ l) :
    relatorNorm (rootW t u l hcyc he hl) ≤ nonTLetters t u := by
  classical
  have h1 : relatorNorm (rootW t u l hcyc he hl) ≤ (mmList t u).length := by
    rw [rootW_eq]
    refine le_trans FreeGroup.norm_mk_le ?_
    rw [List.length_map, show (mmWL t u).length = (mmList t u).length from by
      rw [mmWL, List.length_map]]
  have h2 : (mmList t u).length = nonTLetters t u := by
    rw [mmList, magRew_zero_eq_rewrite,
      show (rewrite t u.toWord) = rewriteAux t 0 u.toWord from rfl, rewriteAux_length,
      nonTLetters, List.countP_eq_length_filter]
  exact h1.trans (le_of_eq h2)

/-- **Transport of a root presentation along an automorphism of the free group.**
An automorphism `ψ` of `F(α)` maps the normal closure of `u ^ l` onto the normal closure of
`(ψ u) ^ l`, hence induces an isomorphism of the two one-relator presentations which carries the
class of `u` to the class of `ψ u`. -/
theorem presentedGroup_pow_mulEquiv {α : Type u} (ψ : FreeGroup α ≃* FreeGroup α)
    (u : FreeGroup α) (l : ℕ) :
    ∃ e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        PresentedGroup ({(ψ u) ^ l} : Set (FreeGroup α)),
      e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
        PresentedGroup.mk ({(ψ u) ^ l} : Set (FreeGroup α)) (ψ u) := by
  have hmap : Subgroup.map (↑ψ) (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)))
      = Subgroup.normalClosure ({(ψ u) ^ l} : Set (FreeGroup α)) := by
    rw [Subgroup.map_normalClosure _ _ ψ.surjective]
    simp only [Set.image_singleton, map_pow]
    rfl
  refine ⟨QuotientGroup.congr _ _ ψ hmap, ?_⟩
  change (QuotientGroup.congr (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)))
      (Subgroup.normalClosure ({(ψ u) ^ l} : Set (FreeGroup α))) ψ hmap)
      (QuotientGroup.mk u) = QuotientGroup.mk (ψ u)
  rw [QuotientGroup.congr_mk]

/-- **The Magnus step for a root, reached through an automorphic image.**
If an automorphism `ψ` of `F(α)` carries the root `u` to a word `ψ u` that is cyclically reduced,
contains a letter `t` of vanishing exponent sum, and whose Magnus rewriting `rootW t (ψ u) l` is
strictly shorter than `u` itself, then the conclusion of `magnus_step_root` holds for `u`: the
HNN structure for `⟨α | (ψ u) ^ l⟩` transports back along `ψ`, and the root condition is preserved
because `ψ` carries the class of `u` to the class of `ψ u`. -/
theorem magnus_step_root_of_eps_zero_image {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (ψ : FreeGroup α ≃* FreeGroup α) (t : α)
    (hcyc : IsCyclicallyReducedRelator (ψ u))
    (hnp : ¬ IsProperPower (ψ u))
    (ht : t ∈ relatorLetters (ψ u))
    (he : eps t (ψ u) = 0)
    (hbound : relatorNorm (rootW t (ψ u) l hcyc he hl) < relatorNorm u) :
    HasMagnusStepAt u l := by
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_mulEquiv ψ u l
  obtain ⟨A, B, φ, e₂, c, hc⟩ := magnus_step_root_eps_zero_aux (ψ u) l hl t hnp hcyc ht he
  exact ⟨mmBeta t ((ψ u) ^ l), rootW t (ψ u) l hcyc he hl,
    not_isProperPower_rootW t (ψ u) l hnp hcyc he hl, hbound,
    A, B, φ, e₁.trans e₂, c, by rw [MulEquiv.trans_apply, he₁, hc]⟩

/-- **Transport of the Magnus step along an automorphism of the free group.**  The HNN data of a
step for the image `ψ u` (with the norm bound measured against `u` itself, since an automorphism
need not preserve the relator length) transports back along `ψ`. -/
theorem magnus_step_root_of_aut {α : Type u} {u : FreeGroup α} {l : ℕ}
    (ψ : FreeGroup α ≃* FreeGroup α)
    (h : ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({(ψ u) ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({(ψ u) ^ l} : Set (FreeGroup α)) (ψ u)) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹) :
    HasMagnusStepAt u l := by
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_mulEquiv ψ u l
  obtain ⟨β, v, hpp, hlt, A, B, φ, e₂, c, hc⟩ := h
  exact ⟨β, v, hpp, hlt, A, B, φ, e₁.trans e₂, c,
    by rw [MulEquiv.trans_apply, he₁, hc]⟩

/-! ## The divisibility case of the no-exponent-sum-zero case -/

/-- **The nondegenerate alternative of `magnus_step_root`, with the norm bound as a parameter.**
This is the "raw HNN data" of the second disjunct of `magnus_step_root`: the one-relator group
`⟨α | u ^ l⟩` is an HNN extension of `⟨β | v ^ l⟩` with the *same* exponent `l`, a root `v` which is
again not a proper power and — this is the parameter `R` — satisfies `relatorNorm v < R`, and with
the class of `u` conjugate to the class of `v`.  Keeping `R` free (instead of fixing
`R = relatorNorm u` as in `HasMagnusStepAt`) is what makes the transports chainable: the rotation,
the automorphism and the original root all have different relator norms, and the single norm bound
must be carried along by hand. -/
abbrev HasMagnusDataAt {α : Type u} (u : FreeGroup α) (l : ℕ) (R : ℕ) : Prop :=
  ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < R ∧
    ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
      ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
        e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹

/-- `HasMagnusStepAt` is the case `R = relatorNorm u` of the parametrised data. -/
theorem hasMagnusStepAt_iff (u : FreeGroup α) (l : ℕ) :
    HasMagnusStepAt u l ↔ HasMagnusDataAt u l (relatorNorm u) := Iff.rfl

/-- Transport of the raw HNN data along conjugating the root. -/
theorem magnus_data_of_conj {α : Type u} {u w : FreeGroup α} {l R : ℕ}
    (hc : ∃ c : FreeGroup α, c * w * c⁻¹ = u) (h : HasMagnusDataAt w l R) :
    HasMagnusDataAt u l R := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_conj_iso u w c l hc
  obtain ⟨β, v, hpp, hlt, A, B, φ, e₂, cc, hcc⟩ := h
  refine ⟨β, v, hpp, hlt, A, B, φ, e₁.trans e₂,
    e₂ (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c) * cc, ?_⟩
  have h3 : PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) u
      = PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c
        * PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w
        * (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) c)⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv]
  rw [MulEquiv.trans_apply, he₁, h3, map_mul, map_mul, map_inv, hcc]
  group

/-- Transport of the raw HNN data along an automorphism of the free group. -/
theorem magnus_data_of_aut {α : Type u} {u : FreeGroup α} {l R : ℕ}
    (ψ : FreeGroup α ≃* FreeGroup α) (h : HasMagnusDataAt (ψ u) l R) :
    HasMagnusDataAt u l R := by
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_mulEquiv ψ u l
  obtain ⟨β, v, hpp, hlt, A, B, φ, e₂, c, hc⟩ := h
  exact ⟨β, v, hpp, hlt, A, B, φ, e₁.trans e₂, c,
    by rw [MulEquiv.trans_apply, he₁, hc]⟩

/-- The exponent-sum-zero step as raw HNN data, through an automorphic image and with the norm bound
as a parameter. -/
theorem magnus_data_of_eps_zero_image {α : Type u} (w : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (ψ : FreeGroup α ≃* FreeGroup α) (t : α) (R : ℕ)
    (hcyc : IsCyclicallyReducedRelator (ψ w))
    (hnp : ¬ IsProperPower (ψ w))
    (ht : t ∈ relatorLetters (ψ w))
    (he : eps t (ψ w) = 0)
    (hR : relatorNorm (rootW t (ψ w) l hcyc he hl) < R) :
    HasMagnusDataAt w l R := by
  obtain ⟨e₁, he₁⟩ := presentedGroup_pow_mulEquiv ψ w l
  obtain ⟨A, B, φ, e₂, c, hc⟩ := magnus_step_root_eps_zero_aux (ψ w) l hl t hnp hcyc ht he
  exact ⟨mmBeta t ((ψ w) ^ l), rootW t (ψ w) l hcyc he hl,
    not_isProperPower_rootW t (ψ w) l hnp hcyc he hl, hR,
    A, B, φ, e₁.trans e₂, c, by rw [MulEquiv.trans_apply, he₁, hc]⟩

/-- The exponent sum is invariant under conjugation. -/
theorem eps_conj {α : Type u} (t : α) (r u : FreeGroup α) : eps t (r * u * r⁻¹) = eps t u := by
  have h1 : sigma t (r * u * r⁻¹) = sigma t u := by
    rw [map_mul, map_mul, map_inv, mul_comm ((sigma t) r) ((sigma t) u), mul_inv_cancel_right]
  rw [epsc_eq_toAdd_sigma, epsc_eq_toAdd_sigma, h1]

/-- The exponent sum in `t` after the single-letter cost-free substitution
`z ↦ z * t ^ (-(q z))` with `q` supported on `{y}`, `q y = c`. -/
theorem eps_rightPow_single {α : Type u} [DecidableEq α] (t y : α) (c : ℤ) (hyt : y ≠ t)
    (u : FreeGroup α) :
    eps t (rightPow t (fun z => if z = y then c else 0) u) = eps t u - c * eps y u := by
  have hs : ∀ z : α, z ∉ ({y} : Finset α) → (fun z : α => if z = y then c else 0) z = 0 := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    show (if z = y then c else 0) = 0
    rw [if_neg hz]
  have h1 := eps_rightPow t (fun z : α => if z = y then c else 0) {y} hs u
  rw [Finset.sum_singleton] at h1
  have hqy : (if y = y then c else 0) = c := by simp
  rw [h1, hqy]

theorem not_isProperPower_map_mulEquiv {α : Type u} (e : FreeGroup α ≃* FreeGroup α)
    {u : FreeGroup α} (hu : ¬ IsProperPower u) : ¬ IsProperPower (e u) := by
  rintro ⟨z, k, hk, hzk⟩
  refine hu ⟨e.symm z, k, hk, ?_⟩
  have h := congrArg e.symm hzk
  simpa using h

/-- The cost-free substitution `rightPow t q` as a `MulEquiv`, whose underlying function is
`rightPow t q` *definitionally* (unlike the existential form `rightPow_mulEquiv`). -/
noncomputable def rightPowEquiv {α : Type u} (t : α) (q : α → ℤ) (hq : q t = 0) :
    FreeGroup α ≃* FreeGroup α :=
  MulEquiv.ofBijective (rightPow t q) (by
    have h1 : Function.LeftInverse (rightPow t (-q)) (rightPow t q) := fun u => by
      rw [← MonoidHom.comp_apply, rightPow_neg_comp_rightPow t q hq]
      rfl
    have h2 : Function.LeftInverse (rightPow t q) (rightPow t (-q)) := fun u => by
      rw [← MonoidHom.comp_apply, rightPow_comp_rightPow_neg t q hq]
      rfl
    exact ⟨h1.injective, h2.surjective⟩)

/-- **The divisibility case of the no-exponent-sum-zero case.**  Let `u` be a root in which the two
distinct letters `t ≠ y` occur, with exponent sums satisfying `eps t u = c * eps y u` for some
integer `c`.  Then the cost-free substitution `Φ : z ↦ z * t ^ (-(q z))`, where `q` is supported on
`{y}` with `q y = c`, is an automorphism of `F(α)` (`rightPow_mulEquiv`, `rightPowEquiv`) which makes
the exponent sum in `t` vanish (`eps_rightPow`), while never increasing the number of non-`t` letters
(`nonTLetters_rightPow_le`).  Consequently, if the image `Φ u` is *cyclically reduced* and still
contains the letter `t`, the exponent-sum-zero Magnus step applies to `Φ u` with a root that is
strictly shorter than `u` itself, and the conclusion of `magnus_step_root` follows for `u`. -/
theorem magnus_step_root_of_dvd {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ IsProperPower u) (t y : α) (hyt : y ≠ t) (c : ℤ)
    (ht : t ∈ relatorLetters u)
    (hc : eps t u = c * eps y u)
    (hcyc' : IsCyclicallyReducedRelator (rightPow t (fun z => if z = y then c else 0) u))
    (ht' : t ∈ relatorLetters (rightPow t (fun z => if z = y then c else 0) u)) :
    HasMagnusStepAt u l := by
  classical
  set q : α → ℤ := fun z => if z = y then c else 0 with hq
  have hqt : q t = 0 := by
    simp only [hq]
    rw [if_neg (Ne.symm hyt)]
  -- the exponent sum in `t` vanishes on the image
  have heps : eps t (rightPow t q u) = 0 := by
    have hs : ∀ z : α, z ∉ ({y} : Finset α) → q z = 0 := by
      intro z hz
      rw [Finset.mem_singleton] at hz
      simp only [hq]
      rw [if_neg hz]
    have h1 := eps_rightPow t q {y} hs u
    rw [Finset.sum_singleton] at h1
    have hqy : q y = c := by simp only [hq]; simp
    rw [hqy, hc] at h1
    rw [h1]
    ring
  -- the automorphism and the transport of the hypotheses to its image
  refine magnus_step_root_of_eps_zero_image u l hl (rightPowEquiv t q hqt) t ?_ ?_ ?_ ?_ ?_
  · exact hcyc'
  · exact not_isProperPower_map_mulEquiv (rightPowEquiv t q hqt) hu
  · exact ht'
  · exact heps
  · refine lt_of_le_of_lt ?_ (nonTLetters_lt_norm u t ht)
    refine le_trans (relatorNorm_rootW_le_nonTLetters (rightPow t q u) l t hcyc' heps hl) ?_
    exact nonTLetters_rightPow_le t q u

/-- **The `|c| ≥ 2` divisibility case, given the rotation witness.**  If two distinct letters `t ≠ y`
of the root satisfy `eps t u = c * eps y u` and some rotation `w = r * u * r⁻¹` of `u` has the
cost-free image `Φ w` (`Φ : z ↦ z * t ^ (-(q z))`, `q` supported on `{y}`, `q y = c`) again
cyclically reduced and still containing `t`, with at most as many non-`t` letters as `u`, then the
conclusion of `magnus_step_root` holds for `u`.  The witness is the statement of
`Submission.Work.OROneRel.exists_rotation_rightPow_witness`; the route is: raw HNN data for `w` via
`magnus_data_of_eps_zero_image`, transported back along the rotation by `magnus_data_of_conj`, with
the single norm bound `relatorNorm (rootW t (Φ w) l …) ≤ nonTLetters t (Φ w) ≤ nonTLetters t u <
relatorNorm u` carried along by hand. -/
theorem magnus_step_root_of_dvd_large {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hu : ¬ IsProperPower u) (t y : α) (hyt : y ≠ t) (c : ℤ)
    (hcyc : IsCyclicallyReducedRelator u) (ht : t ∈ relatorLetters u)
    (hdvd : eps t u = c * eps y u)
    (hwit : ∃ (r w : FreeGroup α), w = r * u * r⁻¹ ∧ IsCyclicallyReducedRelator w ∧
      IsCyclicallyReducedRelator (rightPow t (fun z => if z = y then c else 0) w) ∧
      t ∈ relatorLetters (rightPow t (fun z => if z = y then c else 0) w) ∧
      nonTLetters t (rightPow t (fun z => if z = y then c else 0) w) ≤ nonTLetters t u) :
    HasMagnusStepAt u l := by
  classical
  obtain ⟨r, w, hw, _hcycw, hcycΦ, htΦ, hnorm⟩ := hwit
  have hqt : (fun z : α => if z = y then c else 0) t = 0 := by
    show (if t = y then c else 0) = 0
    rw [if_neg (Ne.symm hyt)]
  -- exponent sums of the rotation
  have hdvdw : eps t w = c * eps y w := by
    rw [hw, eps_conj t r u, eps_conj y r u, hdvd]
  -- the image `Φ w` has vanishing exponent sum in `t`
  have heps : eps t (rightPow t (fun z => if z = y then c else 0) w) = 0 := by
    rw [eps_rightPow_single t y c hyt w, hdvdw]
    ring
  -- the norm bound against the original root
  have hbound : relatorNorm
      (rootW t (rightPow t (fun z => if z = y then c else 0) w) l hcycΦ heps hl) < relatorNorm u :=
    lt_of_le_of_lt
      (le_trans (relatorNorm_rootW_le_nonTLetters _ l t hcycΦ heps hl) hnorm)
      (nonTLetters_lt_norm u t ht)
  -- the image is not a proper power
  have hu_w : ¬ IsProperPower w := by
    rw [hw, isProperPower_conj_iff r u]
    exact hu
  have hnp : ¬ IsProperPower (rightPow t (fun z => if z = y then c else 0) w) :=
    not_isProperPower_map_mulEquiv
      (rightPowEquiv t (fun z => if z = y then c else 0) hqt) hu_w
  -- the raw HNN data for `w`
  have hdata : HasMagnusDataAt w l (relatorNorm u) :=
    magnus_data_of_eps_zero_image w l hl
      (rightPowEquiv t (fun z => if z = y then c else 0) hqt) t (relatorNorm u)
      hcycΦ hnp htΦ heps hbound
  -- transport along the rotation
  exact (hasMagnusStepAt_iff u l).mpr
    (magnus_data_of_conj (⟨r⁻¹, by rw [hw]; group⟩ : ∃ s : FreeGroup α, s * w * s⁻¹ = u) hdata)

/-- **The no-exponent-sum-zero case when some letter of the root occurs on one side only, exactly
once.**  This is `Submission.Work.OROneRel.magnus_step_root_of_letter_once` (a colleague's file),
restated in the vocabulary of this file.  The proof there is elementary: if the letter `x` occurs
exactly once, with exponent `b`, and never with exponent `!b`, then splitting `toWord u` at that
occurrence and substituting `x ↦ P⁻¹ * u * Q⁻¹` is a Tietze transformation exhibiting
`⟨α | u ^ l⟩ ≅ F(α ∖ {x}) ∗ ℤ/l`, whose right-hand side is presented by a one-relator group whose
relator is the single letter `x ^ l` of length one — the step follows. -/
theorem magnus_step_root_no_eps_zero_of_letter_once {α : Type u} [DecidableEq α] (u : FreeGroup α)
    (l : ℕ) (hl : 1 ≤ l) (hu : ¬ IsProperPower u) (x : α) (b : Bool)
    (hb : (x, b) ∈ FreeGroup.toWord u)
    (hcyc : IsCyclicallyReducedRelator u)
    (hcount : (FreeGroup.toWord u).count (x, b) = 1 ∧
      (FreeGroup.toWord u).count (x, Bool.not b) = 0)
    (hn : 2 ≤ relatorNorm u) :
    HasMagnusStepAt u l :=
  magnus_step_root_of_letter_once u l hl x b hb hcyc hcount hn




-- ---------------------------------------------------------------------------------------------
-- THE REMAINING CASE: no letter of the root has vanishing exponent sum
-- ---------------------------------------------------------------------------------------------
--
-- `magnus_step_root_no_eps_zero` (below) is the only gap in the file.  Its statement is TRUE
-- (it is the tower-theoretic Magnus--Moldavanskii step with the root tracked, which is what the
-- coherence paper uses in the form of Masters' or Linton's hierarchy, arXiv 2202.11324, Theorem
-- 5.2), but the two *elementary* routes to it are exhausted, and the reader should not re-derive
-- the following analysis.
--
-- ## What is available now (all proved in this file, all sorry-free)
--
-- * `magnus_step_root_eps_zero_aux` : the exponent-sum-zero step in *explicit* form, with the base
--   `⟨mmBeta t (u ^ l) | mmRootRel t u l hcyc he hl⟩` and the root `rootW t u l hcyc he hl` named.
-- * `relatorNorm_rootW_le_nonTLetters` : `relatorNorm (rootW t u l …) ≤ nonTLetters t u`.
-- * `presentedGroup_pow_mulEquiv` : transport of a root presentation along an automorphism `ψ` of
--   `F(α)` (it carries the class of `u` to the class of `ψ u`).
-- * `HasMagnusStepAt u l` : the second disjunct of the target, named.
-- * `magnus_step_root_of_eps_zero_image` : **any** automorphic image `ψ u` that is cyclically
--   reduced, contains a letter `t` with `eps t (ψ u) = 0`, and whose Magnus rewriting is strictly
--   shorter than `u` gives the target for `u`.  This is the interface for every future construction.
-- * `magnus_step_root_of_aut` / `magnus_step_root_of_conj` : transport of the HNN data along an
--   automorphism, resp. along conjugating the root (with the norm bound measured against `u`).
-- * `magnus_step_root_of_dvd` : **the divisibility case is proved**: if two distinct letters
--   `t ≠ y` of `u` satisfy `eps t u = c * eps y u` and the cost-free substitution
--   `Φ = rightPow t q` (`q` supported on `{y}`, `q y = c`) has `Φ u` again cyclically reduced and
--   still containing `t`, then the target holds for `u`.  Its proof is the model for further cases:
--   `eps t (Φ u) = 0` (`eps_rightPow`), `nonTLetters t (Φ u) ≤ nonTLetters t u`
--   (`nonTLetters_rightPow_le`), hence `relatorNorm (rootW t (Φ u) l …) < relatorNorm u`.
--   The remaining obligation here is the *witness* (that `Φ u` is cyclically reduced and retains
--   `t`), a word-combinatorial statement which is **false** in degenerate cases: for
--   `u = t ^ 2 * y` (or `u = t ^ m * y`) and `c = m` one has `Φ u = t ^ m * y * t ^ (-m)`, a
--   conjugate of `y`, whose every cyclically reduced conjugate misses `t`.  Those degenerate cases
--   are exactly the ones in which a letter of `u` occurs exactly once, and are covered by
--   `Submission.Work.OROneRel.magnus_step_root_of_letter_once` (a colleague's file).
--
--   **The witness analysis for `|c| ≥ 2` (not yet formalised).**  Write `Φ = rightPow t q` with `q`
--   supported on `{y}`, `q y = c`.  Since `Φ(x)` begins with the same letter as `x` for `x ≠ y` and
--   `Φ(y) = y * t ^ (-c)` begins with `y`, the first letter of `Φ w` is the first letter of `w`
--   (unless `w` begins with `y⁻¹`, when it is `t`), and the last letter of `Φ w` is the last letter
--   of `w` (unless `w` ends with `y`, when it is `t ^ (-c)`, or with `y⁻¹`, when it is `y⁻¹`).
--   Consequently, for `|c| ≥ 2` the only way in which the cyclic word of `Φ w` can fail to be
--   reduced is that `w` begins with `y⁻¹` *and* ends with `t⁻¹`; and every letter `y` of `w`
--   contributes a nonzero power of `t` (a segment `y * t ^ (-c)` followed by `t ^ (± 1)` becomes
--   `y * t ^ (±1 - c)`, which is nontrivial exactly because `|c| ≥ 2`), so `Φ w` contains `t`.
--   Hence: *for `|c| ≥ 2` some rotation `w = r * u * r⁻¹` of `u`* has `Φ w` cyclically reduced and
--   containing `t*` — **this is FALSE as stated**: the analysis above only accounts for a *single*
--   following letter, and a run of `t`-letters of length exactly `|c|` cancels the inserted
--   `t ^ (-c)` completely.  Counterexample (found by a prover in this workspace): `u = y * t ^ 2`
--   (cyclically reduced, `both letters occurring once`), `c = 2`: for `w = y t ^ 2` one gets
--   `Φ w = y` (the t-run cancels), `t` is gone; the other two rotations `t ^ 2 * y` and `t * y * t`
--   give `t * y * t ^ (-1)`-shaped words whose first and last letters are inverse, so they are not
--   cyclically reduced at all, and for the rotations of `u⁻¹` again `t` is missing.  So the correct
--   hypothesis is a *run-length* one: no run of `t ^ (±1)` letters immediately following an
--   occurrence of `y` in the cyclic word of `u` may have length `|c|`.  (For `u = y * t ^ 2` this
--   fails, and indeed the route is then dead; that `u` is covered instead by the letter-once case,
--   its letter `y` occurring exactly once.)
--   This witness was requested as `Submission.Work.OROneRel.exists_rotation_rightPow_witness` and
--   came back FALSE for exactly this reason.  The assembly consuming it is
--   `magnus_step_root_of_dvd_large` below, which is proved and takes the witness as a hypothesis, so
--   it can be re-used verbatim once a correct run-length hypothesis is supplied.
--
--   **Assembly note for that route.**  The transports `magnus_step_root_of_aut` /
--   `magnus_step_root_of_conj` carry the norm bound `relatorNorm v < relatorNorm u` against *their
--   own* root `u`, so they cannot be chained: the rotation `w`, the automorphism `Φ` and the
--   original root `u` all have different relator norms.  The clean fix is to split the target's
--   second disjunct into its "raw HNN data" part (all of it except the norm bound) and a final
--   wrapper that adds `relatorNorm v < relatorNorm u`; the raw-data transports are then chained
--   (`w` → `Φ w` → `Φ u` → `u`, using `magnus_step_root_of_dvd`, the conjugation with `Φ r`, and
--   `rightPowEquiv`), and the single norm bound
--   `relatorNorm (rootW t (Φ w) l …) ≤ nonTLetters t (Φ w) ≤ nonTLetters t u < relatorNorm u` is
--   carried along by hand.  `relatorNorm_rootW_le_nonTLetters`, `nonTLetters_rightPow_le` and
--   `nonTLetters_lt_norm` supply exactly the three inequalities of that chain.
--
-- ## Route 1 (Nielsen transformation + the exponent-sum-zero Magnus step).  What is needed is an
-- automorphism `Φ` of `F(α)` and a letter `t` with `eps t (Φ u) = 0` and
-- `relatorNorm (mmW t (cyclicReduction (Φ u))) < n = relatorNorm u` (the last condition is what
-- the exponent-sum-zero step `magnus_step_root_eps_zero` consumes, through `EpsV2.relatorNorm_rootW_lt`).
-- For a block-structured `Φ` (each letter of `u` replaced by a block with `k_x` non-`t` letters)
-- the first condition reads `Σ_x eps x u · σ_t (Φ x) = 0` and the second is
-- `Σ_x occ_x u · k_x < n`, so that `k_x = 1` for `x ≠ t` and `k_t = 0` is the only "cost-free"
-- choice.  Automorphisms realising exactly that cost are (see `Submission.Work.OROneRel.rightPowDefs`)
-- `rightPow t q : y ↦ y * t ^ (-(q y))` for `q t = 0`; they give `σ_t (rightPow t q) = σ_t - Σ q_y σ_y`,
-- hence the first condition is solvable iff `gcd {eps x u : x ≠ t} ∣ eps t u`.  This divisibility
-- FAILS in general: already `u = a ^ 2 * b ^ 3` (exponent sums `2, 3`) admits no such `t`, so this
-- route needs a different construction in those cases (for `a ^ 2 * b ^ 3` a witness does exist --
-- it was found by brute force over `Aut(F 2)` -- namely a Nielsen transformation with
-- `(σ_b (Φ a), σ_b (Φ b)) = (3, -2)` and three non-`b` letters, so the divisibility obstruction is
-- not a counterexample to the statement, only to the cost-free family).
--
-- ## Route 1 is not merely difficult but impossible in the rank-two case.  For `u = a ^ 6 * b ^ 14`
-- (`n = 20`, all exponent sums `≠ 0`, `¬ IsProperPower u`, abelianisation `(6,14)` not unimodular so
-- the first disjunct of the next clause is unavailable) the conditions above force, for `t = a`,
-- `(σ_a (Φ a), σ_a (Φ b)) = ±(7,-3)` together with `7 δ + 3 β = ±1` for the `b`-exponents
-- `β = σ_b (Φ a)`, `δ = σ_b (Φ b)` (the determinant condition); hence `|β| ≥ 2`, `|δ| ≥ 1` and the
-- number of non-`a` letters of the reduced `Φ u = Φ a ^ 6 * Φ b ^ 14` is at least `6 |β| + 14 |δ|`
-- minus the block-boundary cancellations, which are bounded by the run lengths, giving `≥ 25 > 19`.
-- The symmetric computation for `t = b` gives the same bound.  So no Nielsen transformation can feed
-- the exponent-sum-zero step for `u = a ^ 6 * b ^ 14`: the *norm decrease* with respect to the
-- original relator genuinely needs the cyclic-cover/tower construction (a `Z`-domain in the
-- `(7,-3)`-cover, whose relator is the subword cut out between two visits of one sheet), not the
-- Magnus rewriting of a Nielsen transform.
--
-- An independent prover in this workspace reached the same conclusion by a search over Nielsen
-- images of `u = a ^ 4 * b ^ 7` (cyclically reduced, `¬ IsProperPower u`, `relatorNorm u = 11`,
-- exponent sums `4, 7`, both `≠ 0`): there is no `Φ ∈ Aut(F {a,b})` and no letter `t` with
-- `relatorNorm (mmW t (Φ u)) < 11`.  Their conclusion -- that the exponent-sum-zero Magnus step
-- cannot be reached by a Nielsen transformation in the no-zero-exponent-sum case -- is the same
-- obstruction recorded above, and they additionally observe that `mmStepData_of_pos_expsums` in this
-- workspace records the same for `r = a * b⁻¹` and `r = a ^ 2 * b`.
--
-- ## Route 2 (the Magnus/Putman substitution `Ψ`).  The workspace proves
-- `sigma_t_Psi : sigma t (Psi r t x r) = 1` and `nonTLetters_Psi_le : nonTLetters t (Psi r t x r) ≤ nonTLetters t r`
-- (`x ↦ x * t ^ (-σ_t r)`, `t ↦ t ^ (σ_x r)`, `x ≠ t`, all other generators fixed).  This yields a
-- letter `t` with `eps t (Ψ u) = 0` and `nonTLetters t (Ψ u) < n` -- exactly the two conditions of
-- Route 1 -- but `Ψ` is only INJECTIVE, never surjective (its abelianisation has determinant
-- `σ_x (u) ∉ {±1}`), so it induces no isomorphism `⟨α | u ^ l⟩ ≃* ⟨α | (Ψ u) ^ l⟩` and cannot be
-- used to transport an HNN structure back to `⟨α | u ^ l⟩`.  This is the precise reason why the
-- Freiheitssatz can be proved by this method while the Magnus step with the root tracked cannot.
--
-- ## What is available for the continuation.  `Submission.Work.OROneRel.rightPowDefs` (together with
-- `rightPow_mulEquiv`, `eps_rightPow`, `sigma_rightPow`, `nonTLetters_rightPow_le`) provides the
-- cost-free substitution automorphism `rightPow t q`; combined with the (proved, in this file)
-- case `magnus_step_root_eps_zero` it settles the case in which `gcd {eps x u : x ≠ t} ∣ eps t u`
-- for some `t ∈ relatorLetters u`.  The remaining cases -- of which `u = a ^ 2 * b ^ 3` and
-- `u = a ^ 6 * b ^ 14` are the smallest witnesses -- need the Masters/Linton cyclic-cover
-- construction.
--
-- ---------------------------------------------------------------------------------------------
-- ## Session notes (second refinement): why neither presentation-level route can work
-- ---------------------------------------------------------------------------------------------
--
-- **The "diagonalisation" illusion.**  One might hope to reduce the no-exponent-sum-zero case to the
-- exponent-sum-zero case by a change of generators: pick `c` with `cohom c u = 1` supported on
-- `{x, y}`, pick `τ = x ^ p * y ^ q` with `cohom c τ = 1` and `ζ = x ^ b * y ^ a` of weight `0`
-- (`a = c x`, `b = -c y`, so that `p * a - q * b = 1`, i.e. the pair `(τ, ζ)` has *unimodular*
-- abelianisation), and hope that `{τ, ζ}` is a basis of `F({x, y})`, in which case the weight
-- becomes `δ_τ`.  **This is false**: unimodular abelianisation only gives `[F : ⟨τ, ζ⟩] ≥ |det| = 1`,
-- and the index may be infinite.  For `u = a ^ 4 * b ^ 7` (weight `(7, -4)`, `τ = a ^ 3 * b ^ 5`,
-- `ζ = a ^ 4 * b ^ 7 = u`) the pair is *not* a basis -- otherwise `u` would be primitive and
-- `T(4, 7) = ⟨a, b | a ^ 4 * b ^ 7⟩ ≅ ⟨z, s | z⟩ = ℤ`, which is absurd (the abelianisation of the
-- lattice generated by `(3,5)` and `(4,7)` does not even contain `(4,7) = 3 * (3,5) - ... `; in
-- fact `⟨τ, ζ⟩` has infinite index).  So the case distinction is genuine: the "no zero exponent
-- sum" case is *not* a disguised zero case.
--
-- **The two maps of a presentation-level proof need incompatible gauges.**  With a weight `c` with
-- `cohom c u = 1` (so `u` is a closed walk in the `ℤ`-cover) and a gauge `W` (`W 0 = 1`), the
-- *deletion* of the letters of trivial loop class is justified by `gauge_truncation`
-- (`Submission.Work.OROneRel.gauge_truncation`): the product of the loop classes of the remaining
-- letters is still `u`.  Two further requirements appear:
--
--   * the HNN relation `t * of(y_e) * t⁻¹ = of(y_{e+1})` (for the symbol shift `e ↦ e + 1`) must
--     hold in `⟨α | u ^ l⟩` under the map `of(y_e) ↦ (loop class of e)`, `t ↦ τ`.  This is *false*
--     for the shape of gauge that makes deleting work, and *true* for the τ-equivariant gauge
--     `W m = τ ^ m` (where the loop class of `e = (x, i)` is `τ ^ i * x * τ ^ (-i - c x)`, which the
--     shift conjugates by `τ`).
--   * the inverse map `Φ : ⟨α | u ^ l⟩ → HNN` is built from *reference* symbols, one per letter
--     `x`; writing `Φ(x) = \hat W(i_x)⁻¹ * of(y_{(x,i_x)}) * \hat W(i_x + c x)` the telescoping of
--     `Φ(u)` over the walk forces `\hat W(m) = t ^ m * U` for a *fixed* `U`, i.e. `W m = τ ^ m * γ`:
--     again the τ-equivariant gauge.
--
-- But for the τ-equivariant gauge `W m = τ ^ m` *no* symbol has trivial loop class
-- (`τ ^ i * x * τ ^ (-i - c x) = 1` iff `x = τ ^ (c x)`, impossible since `τ` is longer than any
-- letter), so nothing may be deleted and the base relator has norm exactly `|u|`: no decrease.  With
-- the tree-path/first-arrival gauge (`gauge_walk_defs.walkGauge`) instead, the discovering (tree)
-- traversals have *literally trivial* loop class, so the deletion works and the base relator is the
-- deleted word `v` with `relatorNorm v ≤ |u| - (V - 1) < |u|` (`V ≥ 2` = number of levels visited),
-- and `Ψ(v) = u`; but then the τ-conjugation identity above fails.  Hence the isomorphism cannot be
-- produced by two explicit mutually inverse maps, and one needs the *structure theorem* (Bass--Serre
-- / the telescoping recognition theorem `Work.OROneRel.hnn_of_telescoping`), whose stability
-- hypothesis `H ⊓ t ^ m H t ^ (-m) = H ⊓ t H t ^ (-1)` is exactly the `Z`-stability of the domain
-- (Linton's theory) -- not automatic for a finite domain.
--
-- **Available now (all sorry-free, importable):**
--
--   * `Submission.Work.OROneRel.GaugeDefs`: `coverSrc`, `coverTgt`, `coverLetter`, `gaugeMap`,
--     `gauge_letter`, `gauge_decor` (telescoping), `gauge_decor_zero`;
--   * `Submission.Work.OROneRel.gauge_truncation`: `map_prod_eq_of_mk`, `filter_map_prod_eq`,
--     `gauge_truncation` (deleting the letters of trivial class preserves the product);
--   * `Submission.Work.OROneRel.gauge_walk_defs`: `running`, `lv`, `stepUpd`, `walkGauge` (the
--     first-arrival gauge), `exists_walk_gauge` (at most `N - (V - 1)` non-discovering steps);
--   * `Submission.Work.OROneRel.exists_covec_killing`: the weight `c` with `cohom c` surjective,
--     `cohom c u = 1` and `τ` of weight `1`;
--   * `Submission.Work.OROneRel.coverRootDefs`: `coverClass`, `coverBeta`, `coverRootList`,
--     `coverRoot`, `coverToClasses`, `coverLevelSet` -- the candidate base/root of the cover
--     decomposition;
--   * `Submission.Work.OROneRel.gauge_cover_vertices_ncard`,
--     `Submission.Work.OROneRel.list_new_positions_card`,
--     `Submission.Work.OROneRel.list_new_steps_card`,
--     `Submission.Work.OROneRel.running_ncard_two`,
--     `Submission.Work.OROneRel.gauge_levels_bound` (all proved): the combinatorial bookkeeping of
--     the first-arrival gauge;
--   * `Submission.Work.OROneRel.exists_coverRoot_norm` (proved): a gauge with
--     `relatorNorm (coverRoot W c u) < relatorNorm u` whenever `2 ≤ #levels` and `|u| ≠ 0`
--     -- the *strict norm decrease* of the candidate root;
--   * `Submission.Work.OROneRel.coverLevelSet_ncard_two` (proved): `2 ≤ #levels` for a weight `c`
--     that is non-zero on some letter of a non-trivial `u`;
--   * `Submission.Work.OROneRel.coverRoot_spec` (being proved): for such a gauge,
--     `coverToClasses (coverRoot) = u`, the norm decrease, and the induced map
--     `⟨β | (coverRoot) ^ l⟩ →* ⟨α | u ^ l⟩` carrying the class of `coverRoot` to the class of `u`
--     (the root tracking);
--   * `Submission.Work.OROneRel.hnn_of_telescoping` (being proved by a colleague) and the
--     Britton-normal-form statement `Submission.Work.OROneRel.telescoping_britton`.
--
-- **So the remaining gap is exactly the isomorphism** `⟨α | u ^ l⟩ ≃* HNN(⟨β | v ^ l⟩, A, B, φ)` with
-- `v = coverRoot W c u` (and the associated subgroups `A, B` realized by the shift of the cover),
-- together with the identification `⟨β | v ^ l⟩ ≅` the image of the cover class map.  By the
-- obstruction above this needs the Bass--Serre structure theorem for the `ℤ`-cover (Linton's
-- `Z`-domains, arXiv 2202.11324 §4), i.e. a finite domain `Z` with `Z ∩ t ^ m Z` (`m ≥ 1`)
-- `π₁`-stable, its one-relator presentation `⟨E \ T | v ^ l⟩`, and the graph-of-spaces splitting —
-- not the two explicit maps.
--
-- **The stability hypothesis of the recognition theorem is necessary.**  The tempting `hmono`-free
-- statement "`G = ⟨H, t⟩`, `φ̄ : G ↠ ℤ`, `φ̄(t) = 1`, `φ̄(H) = 0` imply
-- `G ≅ HNN(H, H ⊓ t⁻¹Ht, H ⊓ tHt⁻¹, conj_t)`" is **false**: take `G = F(a, b)`, `φ̄(a) = 1`,
-- `φ̄(b) = 0`, `t = a`, `H = ⟨b, a b a⁻¹⟩` (a proper free subgroup of rank 2).  Then all the stated
-- hypotheses hold, but the abelianisation of `HNN(H, A, B, conj_a)` is `ℤ³` (the relation
-- `t b t⁻¹ = a b a⁻¹` is abelianisation-trivial) while that of `F(a, b)` is `ℤ²`, so no isomorphism
-- exists.  Consistently, `H ⊓ t²Ht⁻² ≠ H ⊓ tHt⁻¹` here, so the real
-- `Work.OROneRel.hnn_of_telescoping` (with `hmono`) does not apply either: the `Z`-stability of the
-- domain is a genuine mathematical input, not a convenience.
--
-- **A correction to the norm bookkeeping.**  The count of "non-trivial symbols" must be taken *with
-- multiplicity*: `Set.ncard` of the set of decorated letters counts *distinct* symbols, which is
-- strictly weaker than the length of the filtered word (a closed walk necessarily revisits symbols;
-- e.g. `u = (a b a⁻¹ b⁻¹) ^ 2` with `c a = 1`, `c b = -1` revisits all four symbols).  The
-- statements `gauge_nontrivial_bound*` with `ncard` are therefore true but insufficient; the
-- statement needed for the norm decrease is about the *length* of the filtered list (or, as in
-- `exists_coverRoot_norm`, about `relatorNorm (coverRoot)` directly).
-- ---------------------------------------------------------------------------------------------
-- ## A gauge that is BOTH deleting and shift-equivariant (sharpening of the analysis above)
-- ---------------------------------------------------------------------------------------------
--
-- The comment above concludes that the two requirements on a gauge `W` — that some decorated letters
-- have trivial loop class (`W` "discovers" them, which is what produces the *strictly shorter* base
-- relator) and that the loop classes shift by *conjugation by the stable letter* under a shift of the
-- level — are incompatible, and that one therefore needs Linton's `Z`-domains.  That conclusion is
-- **too strong**, and the following explicit gauge repairs it in a genuine family of cases.
--
-- Setup.  Let `c : α → ℤ` be a weight with `c u = 0` (so that the walk of `u` in the `ℤ`-cover starts
-- and ends at level `0`) and let `t ∈ relatorLetters u` be a letter with `c t = 1`.  Take the gauge
--
--   `W m = t ^ m`   (`W 0 = 1`).
--
-- Writing `u = x₁ ⋯ xₙ` with running levels `i₀ = 0`, `i_j = i_{j-1} + c x_j` (so `iₙ = 0`), the loop
-- class of the `j`-th decorated letter is
--
--   `L_j = W i_{j-1} * x_j * (W i_j)⁻¹ = t ^ i_{j-1} * x_j * t ^ (-i_j)`,
--
-- and the *telescoping* identity (already proved in the workspace as `gauge_truncation` /
-- `GaugeDefs.gauge_decor`) gives
--
--   `L_1 * L_2 * ⋯ * L_n = t ^ i₀ * u * t ^ (-iₙ) = u`,
--
-- because `i₀ = iₙ = 0`.  Two things now hold simultaneously:
--
-- * **deletion.**  For a `t`-letter (`x_j = t`) we get `L_j = t ^ i_{j-1} * t * t ^ (-i_{j-1} - 1) = 1`,
--   since `c t = 1`.  So *every* occurrence of the letter `t` has trivial loop class and is deleted
--   from the base relator `v`, whose norm is therefore `n - occ_t u < n`.  This is the step that the
--   paragraph above ruled out: `τ ^ i * x * τ ^ (-i - c x) = 1` iff `x = τ ^ (c x)`, and this *does*
--   have a solution when `τ = t` is a **letter** of weight `±1` — namely `x = t`, `c x = ±1`.  The
--   earlier analysis had implicitly taken `τ` to be a non-letter word (which is the only shape in
--   which the first-arrival gauge of `gauge_walk_defs` is needed), and it is exactly there that the
--   deletion and the shift-equivariance conflict.
--
-- * **shift-equivariance.**  For the *same* gauge, conjugating a loop class by `t` shifts the level:
--   `t * L_j * t⁻¹ = t ^ i_{j-1} * x_j * t ^ (-i_j + 1 - 1)` is the loop class of the decorated
--   letter `(x_j, i_j)` shifted by one — i.e. the HNN relation
--   `t * of (y_e) * t⁻¹ = of (y_{e+1})` holds *on the nose*, with the shift of the `ℤ`-cover.
--   Consequently `G = ⟨H, t⟩` where `H = ⟨L_j : x_j ≠ t⟩`, and the *tracking* is automatic:
--   the class map `Ψ : F (β) → F (α)`, `p_j ↦ L_j`, sends the surviving word `v` (the word spelled by
--   the surviving decorated letters, `relatorNorm v = n - occ_t u`) to `u`, so
--   `⟨β | v ^ l⟩ → ⟨α | u ^ l⟩` is well defined and carries `mk v` to `mk u` — precisely the target's
--   root tracking.
--
-- So for every `u` for which such a pair `(t, c)` exists, the target is reduced to **two** explicit
-- obligations for the single concretely given subgroup `H`:
--
--   (i) injectivity of `⟨β | v ^ l⟩ → ⟨α | u ^ l⟩` (the `π₁`-injectivity / Freiheitssatz of the
--       domain), and
--   (ii) the `Z`-stability `H ⊓ t ^ m H t ^ (-m) = H ⊓ t H t ^ (-1)` for all `m ≥ 1`.
--
-- Both are statements about `H` alone, with no remaining gauge ambiguity; this is the sharpest form
-- of the gap that this file has reached, and it is the natural place for the cyclic-cover argument to
-- enter.  Note that the *existence* of `(t, c)` is a condition on the exponent-sum vector of `u`:
-- we need a vector of the kernel of `(eps ·)` with a coordinate `±1`.  This holds for
-- `u = a ^ 2 * b ^ 2 * a`, `u = a * b ^ 2 * a` (`c = (1, -1)`), `u = a ^ p * b ^ q` with `p = 1` or
-- `q = 1`, and for many others, but it **fails** for `u = a ^ 4 * b ^ 7` (kernel `ℤ * (7, -4)`) and
-- for exponent-sum vectors such as `(6, 10, 15)`; those cases are exactly the ones for which the
-- first-arrival gauge and hence the `Z`-domain theory proper is needed.
--
-- **The Nielsen cost floor for `u = a ^ 4 * b ^ 7` (confirms the earlier empirical finding).**  For
-- `u = a ^ p * b ^ q` and `t = b` the vanishing condition `σ_b (Φ u) = 0` reads
-- `(σ_b (Φ a), σ_b (Φ b)) = (q, -p) * k`, and the automorphism condition forces
-- `k * (p * x + q * y) = ±1` with `x = σ_a (Φ a)`, `y = σ_a (Φ b)`.  For `(p, q) = (4, 7)` this gives
-- `k = ±1` and `4 x + 7 y = ±1`, whose minimiser of `4 |x| + 7 |y|` is `(x, y) = (2, -1)`, so `Φ u`
-- has at least `4 * 2 + 7 * 1 = 15` non-`b` letters before any cancellation, against a budget of `11`.
-- Cancellations of non-`b` letters can occur only where a run of `a`'s of one sign in the block
-- `Φ a ^ 4 * Φ b ^ 7` meets a run of the opposite sign, i.e. essentially only at the single `Φ a | Φ b`
-- junction and possibly at the cyclic wrap: at most two cancelled pairs, that is four letters, leaving
-- at least `11 = n`.  The strict decrease `relatorNorm (mmW b (Φ u)) < n` therefore fails for every
-- Nielsen image, and symmetrically for `t = a` — no elementary Nielsen route can close these cases.
--
-- **A concrete witness that this family is not subsumed by the proved branches.**  For
-- `u = a ^ 2 * b ^ 3 * c ^ 5` the exponent-sum vector is `(2, 3, 5)`; no two of its entries divide
-- one another, so the divisibility branches `magnus_step_root_of_dvd` / `_large` do not apply, and no
-- letter occurs on one side only once, so the letter-once branch does not apply either.  But
-- `c = (1, 1, -1)` satisfies `2 * 1 + 3 * 1 + 5 * (-1) = 0` and `c a = 1`, so the construction above
-- applies with `t = a` and the base relator `v` has norm `10 - 2 = 8 < 10`.  (For `u = a ^ 4 * b ^ 7`
-- on the other hand the kernel of the exponent-sum functional is `ℤ * (7, -4)`, so no `c` with a
-- coordinate `±1` exists and the first-arrival gauge — hence the `Z`-domain theory proper — is needed.)
--
-- **Two worked instances of the construction.**  (a) `u = a * b ^ 2 * a`, weight `c = (1, -1)`,
-- `t = a`.  The walk `a b b a` has levels `0, 1, 0, -1`; the loop classes of the four decorated
-- letters are `1, a b, b a, 1`, so `β` has two symbols and `v` has norm `2 = n - 2`.  The map `Ψ`
-- sends `p q ↦ (a b)(b a) = a b ^ 2 a = u`, and in `G = ⟨a, b | a b ^ 2 a⟩` one has `b a = (a b)⁻¹`
-- (since `a b ^ 2 a = 1` gives `a b · b a = 1`), so `H = ⟨a b, b a⟩ = ⟨a b⟩ ≅ ℤ`; the substitution
-- `x = a b`, `t = a` is a Tietze transformation exhibiting `G ≅ ⟨t, x | t x t⁻¹ = x⁻¹⟩`, the Klein
-- bottle group, i.e. exactly `HNN (ℤ, ⊤, ⊤, inversion)` with `A = B = ⊤`.  Both obligations hold
-- here.  (This case is already covered by the divisibility branch `magnus_step_root_of_dvd`, since
-- `eps_a u = 2 = 1 * eps_b u`; it is recorded because it shows the construction produces the right
-- answer.)
--
-- (b) `u = a ^ 2 * b ^ 2 * a ^ 2`, weight `c = (1, -2)`, `t = a`.  The walk has levels
-- `0, 1, 2, 0, -2, -1, 0`; the loop classes are `1, 1, a ^ 2 * b, b * a ^ 2, 1, 1`, so the two
-- surviving symbols are `p ↦ a ^ 2 b` and `q ↦ b a ^ 2` and `v = p q` has norm `2 = n - 4`.  The
-- telescoping gives `Ψ v = a ^ 2 b ^ 2 a ^ 2 = u`, and modulo the relator `b a ^ 2 = (a ^ 2 b)⁻¹`, so
-- the vertex is again cyclic, generated by the image of `p`.
--
-- ---------------------------------------------------------------------------------------------
-- **The split of the gap.**  `magnus_step_root_no_eps_zero` below is proved from two pieces:
--
-- * the *letter-once* case (`magnus_step_root_no_eps_zero_of_letter_once`, a colleague's Tietze
--   argument, `⟨α | u ^ l⟩ ≅ F(α ∖ {x}) ∗ ℤ/l`), which covers every root in which some letter occurs
--   on one side only, exactly once — this includes all roots of norm `2` and `3` and, in the
--   rank-two case `u = a ^ p * b ^ q`, all cases in which a letter occurs once;
--
-- * the *residual* case `magnus_step_root_no_eps_zero_residual` below, in which in addition **no**
--   letter of `u` occurs on one side only exactly once.  This single statement is the whole gap of
--   this file: it is where the cyclic-cover (`Z`-domain) construction of Masters and Linton is
--   needed, and none of the elementary routes recorded in the two long comments above reaches it
--   (`u = a ^ 4 * b ^ 7` and `u = a * b * a⁻¹ * b * a * b⁻¹` are the smallest rank-two witnesses).
--   Its hypotheses are exactly those of `magnus_step_root_no_eps_zero` plus `hnlo`.
--
-- ---------------------------------------------------------------------------------------------
-- ## The gap in its sharpest form (fifth refinement)
-- ---------------------------------------------------------------------------------------------
--
-- **1. The norm bound is *presentation dependent*, so it is the easiest half.**  The target asks for
-- `relatorNorm v < relatorNorm u` where `v` is the root of *some* one-relator presentation
-- `⟨β | v ^ l⟩` of the candidate base.  Hence:
--
--   * if the base is *free* of any rank `r`, we are done for `l = 1` by taking `β = γ ⊕ Unit`,
--     `v = of (inr ())`, so that `⟨β | v ^ 1⟩ ≅ F γ` and `relatorNorm v = 1 < 2 ≤ relatorNorm u`;
--   * if the base is `ℤ / l ∗ F_k` (equivalently `⟨β | v ^ l⟩` for `v` a single generator) we are
--     done for *every* `l`, again with `relatorNorm v = 1`;
--   * in general it suffices to find a spanning tree `T` of the domain's `1`-skeleton that
--     *contains an edge of the lift of `u`*: the deleted root word then has norm `≤ |u| - 1`.  A
--     spanning tree may be chosen to contain any prescribed non-loop edge (any forest extends), so
--     the norm bound costs nothing.  What is *not* free is the presentation of the base: the vertex
--     group has to be recognised as one-relator (Linton, Prop. 4.9).
--
-- **2. The `A = B = ⊤` ("normal kernel") route is complete and Britton-free — but not general.**
-- `exists_hnn_top_of_normal_vertex` (proved, no Britton) gives, for *any* `K ◁ G` with
-- `G = ⟨K, t⟩` and `t ^ m ∉ K` for `m ≠ 0`,
-- `HNNExtension ↥K ⊤ ⊤ (conj_t) ≃* G`.  Applied with `K = ker φ̄` for a primitive weight `c` with
-- `c(u) = 0` and `c` not identically zero on the letters of `u` (so that `φ̄` is onto and
-- `G = ⟨α | u ^ l⟩ ↠ ℤ`), and `t` any element with `φ̄ t = 1`, this realises the target *provided* `↥K ≅ ⟨β | v ^ l⟩` with the root tracked.  Here the
-- tracking is *automatic*: `mk u ∈ K` (as `c(u) = 0`), and if `σ : ↥K ≃* ⟨β | v ^ l⟩` is the class
-- map of the cover then `σ (mk u) = mk v`, whence `c = 1` in the target.  This route is *not
-- general*: for a one-relator group which is *not* free-by-cyclic — e.g. the group of a non-fibered
-- knot, where `ker φ̄` is infinitely generated (only fibered knots have finitely generated
-- `ker (π₁ ∖ K → ℤ)`) — `ker φ̄` admits no one-relator presentation with `l = 1` at all.  So the
-- normal-kernel route covers a genuine family (fibered cases such as the torus knots `a ^ p b ^ q`,
-- where `K` is the fibre and `relatorNorm v = 1`), but the general case needs the splitting with
-- *proper* associated subgroups.
--
-- **3. The general route is Linton's one-relator tower, i.e. `hnn_of_telescoping` plus a `Z`-domain.**
-- Concretely, one needs a finite connected subcomplex `Z` of the `ℤ`-cover `Y → X` of the
-- presentation `2`-complex with (i) `ℤ · Z = Y`, (ii) `Z ∩ tZ ≠ ∅` connected, (iii)
-- `Z ∩ t ^ i Z ⊆ Z ∩ tZ ∩ … ∩ t ^ iZ` (`i > 0`).  Then, writing `H := π₁(Z) ≤ G` (the class map of
-- the domain, which is what `coverToClasses` computes), one has `G = ⟨H, t⟩`,
-- `H ∩ t ^ m H t ^ (-m) = H ∩ t H t ^ (-1)` for `m ≥ 1` (this is exactly (iii)), and
-- `H ≅ ⟨β | v ^ l⟩` where `v = coverRoot W c u` (`β = coverBeta W c u`), at which point
-- `hnn_of_telescoping` yields `G ≅ HNN(H, A, B, ψ)` with the correct root tracking.
-- Three inputs are needed, none of which is present:
--
--   (i) the *existence* of such a `Z` with `π₁(Z)` one-relator (Linton Prop. 4.6 + 4.9 + 4.11: a
--       minimal `Z`-domain of a `ℤ`-cover of a one-relator complex is a one-relator complex whose
--       complexity `(|λ| / deg λ, -χ)` strictly drops).  Conversely, the naive candidate — the
--       subcomplex spanned by the lift of `u` — need not have connected translate-intersections;
--   (ii) the *injectivity* of the class map `⟨β | v ^ l⟩ →* ⟨α | u ^ l⟩` (`coverToClasses`, which is
--       well defined by `gauge_truncation` and `exists_cover_root_data`), i.e. Linton's inductive
--       Freiheitssatz for the domain.  This is *not* implied by `freiheitssatz_at`: the loops of the
--       domain are generated by *conjugates* `W i * x * (W (i + c x))⁻¹` of the generators rather
--       than by generators, so the Magnus-subgroup Freiheitssatz does not apply.  For the
--       *letter-weight* gauge (`W m = t ^ m`, `c t = 1`) the class of a symbol `(x, i, +)` of
--       positive sign is `t ^ i * x * t ^ (-i - c x) = Φ (ρ (x, i))` — where
--       `ρ : F ((α ∖ {t}) × ℤ) →* F α`, `(x, i) ↦ t ^ i x t ^ (-i)`, is injective with image
--       `ker σ_t` (`rho_injective`), and `Φ = rightPow t c` (with `c t := 0`, so `Φ (x) = x t ^ (- c x)`)
--       is an *automorphism* (`rightPow_mulEquiv`) — so on the *positive* signs injectivity on
--       `F (β)` is immediate.  Careful: for a *negative* symbol `(x, i, -)` the class is
--       `t ^ i * x⁻¹ * t ^ (c x - i)` while `Φ (ρ (x, i)⁻¹) = t ^ (i + c x) * x⁻¹ * t ^ (-i)`; these
--       differ, and no homomorphism `Φ'` can realise both signs at once (`Φ' (x⁻¹)` is forced to be
--       `Φ' (x)⁻¹`), so the class map is *not* of the form (automorphism) ∘ ρ and needs its own
--       argument even at the level of free groups.  Above that, the content is the collapsing
--       statement `⟨⟨v ^ l⟩⟩_{F β} = (coverToClasses)⁻¹ ⟨⟨u ^ l⟩⟩_{F α}` (the surface form of the
--       statement that the domain's single relator generates the kernel); *this* is the crux, and it
--       is exactly why the earlier "two explicit maps" attempts failed;
--   (iii) the `¬ IsProperPower (coverRoot W c u)` condition.  A word of norm `≤ 1` is never a proper
--        power, so arranging `relatorNorm (coverRoot) ≤ 1` (i.e. a spanning tree that swallows
--        `|u| - 1` traversals of the lift) settles this too; that is possible whenever the traversed
--        edge set minus one edge is acyclic (e.g. whenever the walk visits `|u|` distinct levels).
--
-- **4. No shortcut exists even for the trefoil.**  `⟨a, b | a ^ 2 b ^ 3⟩ ≅ BS (2, 3) =
-- HNN (ℤ, 2ℤ, 3ℤ, x ^ 2 ↦ x ^ 3)`, but exhibiting that isomorphism already needs the Bass–Serre
-- structure theorem (the amalgam `ℤ ∗_{2ℤ ≅ 3ℤ} ℤ` has two vertex orbits, the HNN one), i.e. the
-- same machinery, and neither the divisibility, letter-once, exponent-sum-zero nor Nielsen branches
-- of this file reaches `u = a ^ 2 * b ^ 3` (`gcd {2, 3} = 1` divides neither exponent sum).
/-- **For `l = 1` the root tracking is automatic.**  The relator of `⟨α | u ^ 1⟩` is `u` itself, so
the class of `u` is trivial, and likewise the class of `v` in `⟨β | v ^ 1⟩`; the conjugacy condition
of the target therefore holds with `c = 1`.  Consequently, for `l = 1` the second disjunct of
`magnus_step_root` is exactly the statement that `⟨α | u⟩` is *some* HNN extension of a one-relator
group `⟨β | v⟩` with `¬ IsProperPower v` and `relatorNorm v < relatorNorm u`. -/
theorem hasMagnusStepAt_one_of_hnn {α : Type u} (u : FreeGroup α) {β : Type u} (v : FreeGroup β)
    (h1 : ¬ IsProperPower v) (h2 : relatorNorm v < relatorNorm u)
    {A B : Subgroup (PresentedGroup ({v ^ 1} : Set (FreeGroup β)))} {φ : A ≃* B}
    (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃*
      HNNExtension (PresentedGroup ({v ^ 1} : Set (FreeGroup β))) A B φ) :
    HasMagnusStepAt u 1 := by
  have hu1 : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u = 1 :=
    PresentedGroup.one_of_mem (by
      rw [Set.mem_singleton_iff]; exact (pow_one u).symm)
  have hv1 : PresentedGroup.mk ({v ^ 1} : Set (FreeGroup β)) v = 1 :=
    PresentedGroup.one_of_mem (by
      rw [Set.mem_singleton_iff]; exact (pow_one v).symm)
  refine ⟨β, v, h1, h2, A, B, φ, e, 1, ?_⟩
  rw [hu1, map_one, hv1, map_one]
  group

-- ---------------------------------------------------------------------------------------------
-- ## Session notes (this session): the recognition theorem has to be the *shrinking* one
-- ---------------------------------------------------------------------------------------------
--
-- **(a) The monotone ("stability") hypothesis of `Work.OROneRel.hnn_of_telescoping` is FALSE for the
-- domains of the `ℤ`-cover decomposition.**  The recognition theorem there assumes
-- `H ⊓ t ^ m H t ^ (-m) = H ⊓ t H t ^ (-1)` for all `m ≥ 1` (and, dually, with the opposite shift).
-- For the letter-weight gauge `W i = of t ^ i` (`c t = 1`) and `H` the subgroup generated by the
-- loop classes of the decorated letters of `u`, this fails.  Explicit instance (checked with a
-- Stallings-graph implementation of subgroup membership):
-- `α = {a, b, c}`, `t = a`, `c = (1, 1, -1)`, `u = a ^ 2 b ^ 3 c ^ 5` (a case of the residual below:
-- the exponent sums `2, 3, 5` are pairwise non-divisible, every letter occurs at least twice, and
-- `c a = 1`), and `H = ⟨rho b i, rho c j⟩` the loop classes of the *coedges of a window domain*
-- (levels `0 … M`, the `a`-edges as spanning tree).  Then
--   * `rho (b, 1) ∈ H` and `a * rho (b, 1) * a⁻¹ = rho (b, 2) ∈ H`, so `rho (b, 1) ∈ H ⊓ aHa⁻¹`;
--   * but `a ^ 2 * rho (b, 1) * a ^ (-2) = rho (b, -1) ∉ H`, so `rho (b, 1) ∉ H ⊓ a ^ 2 H a ^ (-2)`.
-- Hence the intersections *shrink* rather than stabilize, and `hnn_of_telescoping` cannot be the
-- tool.  This is not an artefact of the window: Linton's condition (2) for `Z`-domains
-- (`D ∩ t ^ i D ⊆ D ∩ tD ∩ … ∩ t ^ i D`) forces precisely this shrinking, and the corresponding
-- recognition statement is Proposition 4.3 of arXiv 2202.11324: `π₁X ≅ HNN(π₁D, π₁ (D ∩ t⁻¹D),
-- π₁ (D ∩ tD), ψ)` for a `Z`-domain `D` — a *graph-of-spaces* statement, proved by a homotopy
-- equivalence, not by a telescoping normal form.  Note the tension: the monotone hypothesis needs
-- `t H t⁻¹ = H`-like behaviour, which forces `H = ker φ̄` (the whole `ℤ`-cover group, which is not
-- one-relator), whereas one-relatorness of the vertex forces a finite domain, which makes the
-- intersections shrink.  So the two requirements are *mutually exclusive*, which is the real reason
-- that `hnn_of_telescoping` (however useful elsewhere) cannot close this gap.
--
-- **(b) The class map of the `ℤ`-cover is injective for the letter-weight gauge, but the naive
-- transfer to the one-relator presentations is FALSE.**  The statement "the loop classes of the
-- decorated letters form a free basis of the subgroup they generate" (with the two non-degeneracy
-- hypotheses: no letter `t`, and no edge of the cover used in both directions) is delegated as
-- `Submission.Work.OROneRel.coverClass_injective`; it was verified numerically on ~100 random
-- sign-mixed clash-free families.  It gives, for the letter-weight gauge, the *injectivity* of the
-- class map `FreeGroup β →* FreeGroup α`, but that does **not** give the injectivity of the induced
-- map `⟨β | v ^ l⟩ →* ⟨α | u ^ l⟩`: what is needed is the *preimage* statement
-- `ρ⁻¹ (normalClosure {ρ v}) = normalClosure {v}`, which does not follow from injectivity of `ρ`.
-- Counterexample: `ρ : F (a, b) → F (a, b)`, `a ↦ a`, `b ↦ b ^ 2` is injective (its image is the
-- rank-two subgroup `⟨a, b ^ 2⟩`), but every `ρ x` has even `b`-exponent, hence lies in
-- `normalClosure {b ^ 2}` (the kernel of `F (a, b) → ℤ/2`, `a ↦ 0`, `b ↦ 1`), while
-- `a ∉ normalClosure {b}`.  So the "Freiheitssatz for the domain" — the injectivity of
-- `π₁ (domain) → π₁ (cover)` — is a genuine third input.  (The transfer itself, i.e.
-- "injectivity of the class map *plus* the preimage statement imply that the vertex group really is
-- `⟨β | v ^ l⟩`", is a short isomorphism-theoretic argument, delegated as
-- `Submission.Work.OROneRel.presentedGroup_map_injective_of_preimage`; its statement isolates the
-- preimage statement `hpre` above as the *only* extra hypothesis.)
--
-- **(c) The clash phenomenon, and what `β` must be.**  The decorated letters of the walk can contain
-- two distinct elements with *inverse* loop classes: `((x, i), true)` (the edge `x` from level `i` to
-- `i + c x`, loop class `t ^ i * x * t ^ (-i - c x)`) and `((x, i), false)` (the same edge traversed
-- backwards, loop class `(t ^ i * x * t ^ (-i - c x))⁻¹`).  This happens exactly when the walk uses
-- an edge of the cover in both directions.  In that case the framework's `coverBeta` (decorated
-- letters of non-trivial loop class, with signs) has a redundant generator and `coverToClasses` is
-- not injective; the correct `β` is the set of *coedges of the domain* (one generator per undirected
-- edge, the direction being carried by the exponent in `v`), which is the bound `hclash` above.
-- The relator `v` then is the *reduced* coedge word of the walk, and the cancellations of the walk
-- are absorbed in the free group `FreeGroup β`.
--
-- **The remaining gap in its sharpest form.**  For the residual below it suffices to produce
-- (1) a `Z`-domain `D` of the `ℤ`-cover (windows `{0, …, M}` with all edges whose endpoints lie in
-- the window already satisfy Linton's conditions (1), (2), (3) for `M` large enough, with
-- `D ∩ t ^ i D` the window `{i, …, M}`), a spanning tree `T` of `D ^ (1)` and the coedge word `v`
-- of the lift of `u`, with `relatorNorm v < relatorNorm u` and `¬ IsProperPower v`;
-- (2) the graph-of-spaces splitting `π₁X ≅ HNN (π₁ D, π₁ (D ∩ t⁻¹D), π₁ (D ∩ tD), ψ)` (Linton
-- Proposition 4.3, via `Z ⊆ Y`, `ℤ · Z = Y` and the `π₁`-injectivity of the inclusions
-- `D ∩ tD → D, tD`);
-- (3) the injectivity of `π₁ D → π₁ X` (the Freiheitssatz for the domain, item (b));
-- (4) the tracking `mk u ↔ of (mk v)` up to conjugacy (from the telescoping identity
-- `gauge_truncation`).
-- **RESOLVED (this session): the import obstruction is gone.**  The clash was *not* between
-- `RhoRewrite` and `MagnusGenDefs` as such but came from the (unused) import
-- `Submission.Work.OROneRel.rho_injective`, the only import of *this* file pulling in `RhoRewrite`.
-- Removing that one import line (nothing in the file referred to it; the only name used from it was
-- `mk_append`, now inlined in `mk_flatten_rep`) and adding
--
--   `import Submission.Work.OROneRel.coverRootDefs`
--   `import Submission.Work.OROneRel.exists_cover_root_data`
--   `import Submission.Work.OROneRel.coverClass_injective`
--   `import Submission.Work.OROneRel.exists_covec_killing`
--   `import Submission.Work.OROneRel.coverLevelSet_ncard_two`
--
-- makes the *whole* cover vocabulary (`coverClass`, `coverBeta`, `coverRoot`, `coverToClasses`,
-- `exists_cover_root_data`, `gauge_truncation`, `coverClass_injective`, `exists_covec_killing`,
-- `coverLevelSet_ncard_two`) available in this file, *together with* the Freiheitssatz machinery
-- (`freiheitssatz_at`, `mmStepData_of_expsum_zero`).  So the residual can now be closed by an
-- argument written in the cover vocabulary, and files importing *this* file can use the cover
-- vocabulary too.  (Verified by `lake build`.)
--
-- **The recognition criterion: BOTH the ungraded and the graded forms are FALSE; the honest tool is
-- Britton-in-`G` (= the tree condition), and no finite list of "meet" conditions replaces it.**
-- The missing tool was supposed to be a criterion of the shape "`G = ⟨H, t⟩` plus intersection
-- conditions ⟹ `G ≅ HNN(H, A, B, conj_t)`" with `A = H ⊓ t⁻¹Ht`, `B = H ⊓ tHt⁻¹`.  *Three*
-- machine-checked refutations now exist in this workspace, and they show that the shape itself is
-- wrong.
-- (1) *Ungraded, `H = ⊤`*: with hypotheses `H ⊓ ⟨t ^ i H t ^ (-i) : i ≥ 1⟩ = B` and its mirror, the
-- statement instantiates with any finite `G` generated by `H` and `t` (whenever conjugation by `t`
-- acts trivially on `H` both sides are `H`), while every HNN extension is infinite —
-- machine-checked in `Submission/Work/OROneRel/hnn_iso_of_meet_conditions_false.lean`.  (Also
-- `G = ℤ`, `H = ⊤`, `t = 1`: `HNNExtension ℤ ⊤ ⊤ id ≅ ℤ × ℤ ≇ ℤ` while the conclusion forces a map
-- with `of 1 ↦ 1`, `t ↦ 1`.)
-- (2) *Graded*: adding a surjection `φbar : G →* Multiplicative ℤ` with `φbar|_H = 1` and `φbar t`
-- the generator excludes (1), and was delegated as
-- `Work.OROneRel.hnn_iso_of_meet_conditions_graded` — **refuted too**, machine-checked, in
-- `Submission/Work/OROneRel/graded_counterexample.lean` (+ `NOTES_hnn_iso_graded_false` and `NOTES_graded_counterexample`): take the
-- affine group `Aff = (⊕_ℤ ℤ) ⋊ ℤ` of the shift, `H = ℤ·δ₀`, `t = (0,1)`.  Then `H ⊔ ⟨t⟩ = ⊤`,
-- `φbar (f,k) = k`, and **both sides of both meet conditions are `⊥`** (each telescope generator is
-- some `δ_m` with `m ≠ 0`, hence vanishes at `0`), yet the conclusion would give
-- `Aff ≅ HNN(ℤδ₀, ⊥, ⊥) = ℤ ∗ ℤ`: the hypotheses cannot see the *mixed* products
-- `H · tHt⁻¹ = ⟨δ₀, δ₁⟩ ≅ ℤ²` (abelian in `Aff`, free in `ℤ ∗ ℤ`).  So the meeting conditions on the
-- *one-sided generated telescopes* fail to control the subgroup generated by `H` and one conjugate.
-- (3) The one-sided *single-conjugate* conditions are weaker still: `G = ℤ² ⋊_A ℤ`,
-- `A = [[1,1],[1,2]]`, `H = ⟨e₁⟩` satisfies `H ⊓ t^m H t^(-m) = ⊥` for all `m ≥ 1` and still fails.
-- The conclusion: a *sufficient* recognition theorem of this shape cannot exist (or needs
-- conditions on all *products*, which is Britton's lemma itself).  The honest tool is therefore the
-- Bass–Serre structure theorem for a loop quotient — "if `G` acts on a tree with one vertex orbit
-- (stabiliser `H`) and one edge orbit (stabiliser `A`), the quotient being a loop, then
-- `G ≅ HNN(H, A, B, φ)`" — which `Submission/Work/ORBassSerre/README.md` records as *not yet
-- formalised* (the HNN Bass–Serre tree itself is available: `Work.ORBassSerre.HNN.hnnGraph`,
-- a `SimpleGraph` on `HNNExtension G A B φ ⧸ ofE.range` with adjacency `{⟦h⟧, ⟦h * t⟧}`, proved to
-- be a tree by `hnnGraph_isTree`; that is the *forward* direction).  Equivalently (and this is the
-- useful shape): **prove directly, for the concrete `H`, `t` of the cover, that every `HNN`-reduced
-- word in `H`, `t` is nontrivial in `G`** — then `exists_reducedWord` (`ORBassSerre/HNN/Defs.lean`)
-- turns that into `G ≅ HNN`, with the tracking.  In the graded situation (`φ̄ : G → ℤ`, `φ̄|_H = 0`,
-- `φ̄ t = 1`) this "Britton for `G`" is exactly the statement that `T` (vertices `G/H`, edges
-- `{gH, gtH}`) is a *tree*, and the up-path description below reduces it to a statement about
-- products `h₁t ⋯ h_nt H`.
--
-- **The exact shape of the tree condition (up-path form).**  In the *graded* situation
-- (`φ̄ : G → ℤ`, `φ̄|_H = 0`, `φ̄ t = 1`, as in the application) the graph `T` (vertices `G/H`, edges
-- `{gH, gtH}`) has all edges raising the level by `1`, so *upward paths never close up and every
-- cycle contains a "top" vertex*: `T` is a tree **iff** no two *distinct* upward paths from any
-- vertex meet.  Upward paths from `H` are exactly the sequences `(h₁, …, h_n) ∈ H^n` with vertex
-- sequence `H, h₁t H, h₁th₂t H, …`; hence the tree condition is the purely algebraic statement
--
--   for all `n, n' ≥ 1` and all `h₁,…,h_n, h'₁,…,h'_{n'} ∈ H`:
--   `h₁ t ⋯ h_n t H = h'₁ t ⋯ h'_{n'} t H` implies the two paths agree.
--
-- Peeling this by induction on `n + n'` gives the conditions the criterion really needs, and shows
-- why the two simple intersection conditions cannot suffice:
-- * `n = n' = 1` uses exactly the one-block case (`h₁ t H = h'₁tH` ⟺ `h₁ ≡ h'₁ mod B`);
-- * `n = 2, n' = 0`: `h₁th₂t H = H` gives `h₂ = t⁻¹ h t⁻¹` with `h ∈ H`, so it needs a *two-sided*
--   condition — the set `{x ∈ H : ∃ h ∈ H, x = t⁻¹ht⁻¹}` must lie in `A` (well-typed form:
--   `{x ∈ H : t h x t ∈ H} ⊆ A`) — which is *not* a consequence of the one-sided subgroup
--   conditions, although it *is* a consequence of the tree condition;
-- * `n = 3, n' = 0` similarly gives `h₂ = t⁻¹ h₁⁻¹ t⁻¹ h t⁻¹`, i.e. a condition against elements of
--   `H t⁻¹H t⁻¹`-shape; in general `n`-block relations require the conditions against
--   `H t^{-1} H t^{-1} ⋯`-products, which is precisely Britton's lemma for `G`.
-- The single-conjugate counterexample `G = ℤ² ⋊_A ℤ` fails the `n = 2` case already
-- (`e₁ = t²e₁t^{-2}·t e₁⁻¹ t⁻¹`), which is why it is invisible to `H ⊓ t^mHt^{-m}`.
--
-- Items (2) and (3) are the missing chapter (the one-relator tower of arXiv 2202.11324 §4).
-- ---------------------------------------------------------------------------------------------
--
-- **THE PLAN (this session, in the cover vocabulary, now actually expressible in this file).**
-- With `coverRootDefs`/`exists_cover_root_data` imported, the residual reduces to *three* named
-- obligations plus bookkeeping.  Let `c : α → ℤ` have `cohom c u = 1`, `hV : 2 ≤
-- (coverLevelSet c u).ncard`, `hN : 0 < (decor c 0 (wordOf u)).length`, let `W`, `β := coverBeta W c u`,
-- `v := coverRoot W c u`, `ρ := coverToClasses W c u` and `Ψ : PresentedGroup {v ^ l} →*
-- PresentedGroup {u ^ l}` be the data of `Work.OROneRel.exists_cover_root_data` (so `W 0 = 1`,
-- `relatorNorm v < relatorNorm u`, `ρ v = u`, `Ψ (mk v) = mk u`), and let `τ : FreeGroup α` satisfy
-- `cohom c τ = 1` (`Work.OROneRel.exists_covec_killing`).  Put
--   * `H := Ψ.range ≤ G := PresentedGroup {u ^ l}`  (the vertex, `mk u ∈ H` because `Ψ (mk v) = mk u`),
--   * `t := PresentedGroup.mk {u ^ l} τ`  (the stable letter; `t ∉ H` since `t` has weight `1`),
--   * `φbar : G →* Multiplicative ℤ` the map induced by `c` on the presented group
--     (`φbar|_H = 1` because `Ψ` is `c`-weight-preserving, `φbar t = ofAdd 1`).
-- Then the obligations are:
--   (A) `Function.Injective Ψ` (equivalently, by
--       `Work.OROneRel.presentedGroup_map_injective_of_preimage`, the *preimage* statement
--       `∀ x, ρ x ∈ Subgroup.normalClosure {u ^ l} ↔ x ∈ Subgroup.normalClosure {v ^ l}`) —
--       the Freiheitssatz for the domain, i.e. the vertex really is `⟨β | v ^ l⟩`;
--   (B) **Britton for `(H, t)` in `G`**: every `HNN`-reduced word in `H`, `t` (with respect to
--       `A = H ⊓ t⁻¹Ht`, `B = H ⊓ tHt⁻¹`, `φ = conj_t`) is nontrivial in `G`; by
--       `Work.ORBassSerre.HNN.exists_reducedWord` this *is* the statement
--       `G ≅ HNNExtension ↥H A B φ` with `of ↦ subtype`, `t ↦ t`.  (Item (B) must NOT be replaced
--       by the meet conditions of `hnn_iso_of_meet_conditions_graded` — those are satisfied by the
--       affine counterexample `Submission/Work/OROneRel/graded_counterexample.lean` while the
--       conclusion fails; see the criterion paragraph above.  In the graded situation, (B) is the
--       assertion that the graph `T` — vertices `G/H`, edges `{gH, gtH}` — is a tree, i.e. that no
--       two distinct upward paths `(h₁, …, h_n)` meet; this is the `ℤ`-domain/graph-of-spaces
--       content of Linton Proposition 4.3.)
--   (C) `¬ IsProperPower v`.
-- Given (A) and (B), the isomorphism `presented-groups ≃* HNN` is obtained with the tracking by
-- `MulEquiv.ofInjective`/`hnnExtension_iso_of_baseMulEquiv` so that the base is literally
-- `PresentedGroup {v ^ l}`; the tracking is the bookkeeping `ρ v = u`, `Ψ (mk v) = mk u`.
-- The obligation (C) is the one that is *not* automatic: `coverRoot` is the word of the decorated
-- letters of non-trivial loop class, and nothing so far prevents it from being a proper power; it
-- should be attacked together with (B) (a *first-arrival/tree* gauge makes `v` as short as
-- `|u| - (V - 1)` with `V` the number of visited levels, and a short word in a *free* alphabet
-- `β` with `|β| ≫ |v|` is not a proper power for genericity reasons — but a proof needs the
-- specific gauge).  **The provable half of (C) is now isolated and delegated**: the exponent sum of
-- a `k`-th power is `k` times that of its root (`sigma t` is a homomorphism, and
-- `Work.OROneRel.transvectionNielsenData` already contains
-- `tvn_not_isProperPower_of_eps_eq_pm_one`), so `∃ x, eps x v = ±1` suffices; since `coverRootList`
-- emits every symbol with the constant exponent `true`, the exponent sum in a symbol is just its
-- number of occurrences, whence
--   `Work.OROneRel.not_isProperPower_coverRoot_of_count_one`
--   (`(coverRootList W c u).count (x, true) = 1 → ¬ IsProperPower (coverRoot W c u)`,
--   file `Submission/Work/OROneRel/not_isProperPower_coverRoot_of_count_one.lean`).
-- So (C) is reduced to choosing a gauge in which some decorated letter of non-trivial loop class
-- occurs exactly once — a combinatorial condition on `W` (`exists_cover_root_data` produces *some*
-- gauge, so the two requirements must be met simultaneously).
-- (A) and (B) are independent: (A) is a statement about `F (β) → F (α)` and the normal closure of
-- `u ^ l`, while (B) is the "π₁ of the intersection of the domain with its translates equals the
-- intersection of the π₁'s" statement of the `ℤ`-cover.  Both are instances of the same geometric
-- fact (the domain `→` cover immersion is `π₁`-injective), which is why the faithful account of the
-- gap is the one-relator tower (arXiv 2202.11324 §4) rather than two separate lemmas.
--
-- **A sufficient condition that avoids (B) entirely (the `⊤`-vertex route).**  `ker φbar ◁ G`, and
-- `exists_hnn_top_of_normal_vertex` gives `G ≅ HNN(ker φbar, ⊤, ⊤, conj_t)` — no intersection
-- argument needed, because the kernel is *normal*.  So the target follows as soon as the vertex
-- `ker φbar` is itself a one-relator group `⟨β | v ^ l⟩` with `relatorNorm v < relatorNorm u`:
-- * for `l = 1` this needs only that `ker φbar` be a *finitely generated free* group
--   (`magnusStepAt_one_of_free_vertex` finishes, with `v` a single generator); for `u = a ^ 4 * b ^ 7`
--   and `c = (7, -4)` this is Stallings' theorem that the commutator subgroup of a knot group is
--   free (finitely generated precisely when the knot is fibered — torus knots are), a genuine
--   classical theorem, so this route does not close the residual either, but it does cover
--   fibered cases without any Bass--Serre input;
-- * for `l ≥ 2` it needs `ker φbar ≅ ⟨β | v ^ l⟩` *plus* the tracking
--   `mk u ↔ of (mk v)` (which is automatic for `l = 1`, see `hasMagnusStepAt_one_of_hnn`).
-- This is the route to try first whenever `ker φbar` is (or is recognised as) one-relator; the tower
-- of (A)/(B) above is needed exactly for the cases where it is not.
-- ---------------------------------------------------------------------------------------------
--
-- **A reduction that the construction may assume.**  A generator `x ∉ relatorLetters u` is a free
-- factor: `Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported` gives
-- `⟨α | u ^ l⟩ ≅ ⟨{x}ᶜ | u ^ l⟩ ∗ ℤ`, and an HNN decomposition of the first factor extends to one of
-- the product with vertex `⟨β | v ^ l⟩ ∗ F_k ≅ ⟨β ⊔ k symbols | v ^ l⟩` (the relator `v` does not
-- involve the extra symbols).  So the construction below may assume `relatorLetters u = α`, hence
-- `α` finite; note that all the residual's hypotheses (`hbad`, `hnlo`, `hn`) are insensitive to
-- adding free generators, so this reduction does not change the case analysis.
-- ---------------------------------------------------------------------------------------------
--
-- **SESSION (the one that wired in the weighted step; read this before attacking the residual).**
--
-- (0) *The weighted Magnus--Moldavanskii step and the free-generator reduction are now part of the
-- case analysis.*  Importing `Submission.Work.OROneRel.magnusStepCase2_of_weight` (a colleague's
-- file; it does not import this one) and splitting `magnus_step_root_no_eps_zero` on
-- `∃ t ∈ relatorLetters u, ∃ c : α → ℤ, c t = 1 ∧ cohom c u = 1` shows that this case is *exactly*
-- the second disjunct of the target.  Hence the residual now *also* carries the hypothesis `hnd`,
-- i.e. "no letter carries a killing weight of value `1`" — equivalently, for no letter `t` does
-- `gcd {eps z u : z ≠ t}` divide `eps t u` (this is the divisibility condition).  Consequence: in
-- the residual, `|eps x u| ≥ 2` for every `x ∈ relatorLetters u` (if `|eps x u| = 1` then for any
-- other letter `t ≠ x` the gcd `gcd {eps z u : z ≠ t}` divides `eps x u = ±1`, hence is `1`, hence
-- divides `eps t u`, contradicting `hnd`).  Also the exponent-sum-zero case is the special case
-- `c = δ_t` (`cohom δ_t u = eps t u = 0`), so the inlined `magnus_step_root_eps_zero` machinery
-- below is subsumed by that import; it is kept because it is proved and self-contained.
--
-- (0') *The residual is stated in its `support-normalized` form.*  Using the (proved, imported)
-- `Submission.Work.OROneRel.magnus_step_residual_of_support` — which rests on
-- `Work.OROneRel.hasMagnusStepAt_map_of_injective`, the invariance of the Magnus step under an
-- injective relabelling of the generators — the residual carries the extra hypothesis
-- `hocc : ∀ x : α, x ∈ relatorLetters u`, i.e. *every* generator of the ambient type occurs in `u`.
-- Hence the residual may take `α = relatorLetters u` (so `α` is finite), which is what the
-- `ℤ`-cover/domain construction wants.  The free-generator case is therefore discharged.
-- (Still missing, and worth adding later: the two-letter *torus* words `a ^ p * b ^ q` with
-- `p, q ≥ 2` are not excluded by the residual; colleagues' files
-- (`Work.OROneRel.magnusStepDataOne_cpRelator`, `…_cpRelator_general`, `isFreeGroup_ker_rescaledChi`
-- + `magnusStepDataOne_of_freeKernel`) cover them, and wiring them in would remove the two-letter
-- instances from the residual.)
--
-- (0'') *Two new proved cases have been wired into the case split (both decided for the
-- support-normalized relator, so no transport of a case hypothesis is needed), and the residual now
-- carries their negations as hypotheses `hnfk` and `hnc`:*
--
-- * `FreeKernelCase u l` (`l = 1`, a killing weight whose kernel `ker (presentedCohom c u 1 hc)` is
--   free): `Work.OROneRel.magnusStepCase2_of_freeKernel` gives the target outright, over the free
--   vertex presented by the terminal relator `⟨Option γ | of none⟩`, with the trivial `l = 1`
--   tracking.  The HNN structure used is the `⊤`-route one (`hnnKernelForm_tracking`), which needs
--   no Britton input because the kernel of a weight map is *normal*.  This removes every *fibered*
--   instance, in particular all torus relators `a ^ p * b ^ q` (`Work.OROneRel.isFreeGroup_ker_rescaledChi`
--   proves the kernel of the rescaled character free for *all* `p, q ≥ 2`).
-- * `NielsenCountCase u` (an automorphic image `ψ u`, cyclically reduced, all exponent sums
--   non-zero, carrying a letter `t` with a killing weight `c` (`c t = 1`) whose decorated word with
--   the `t`-symbols deleted is shorter than `relatorNorm u`):
--   `Work.OROneRel.magnusStepData_of_count_image` gives the target for *every* `l ≥ 1`.  This covers
--   the two-letter torus roots `x ^ p y ^ q` for the pairs with `(p-1)|m| + (m+q) < p + q`
--   (`magnusStepNielsenTorusFamily`: `(2,3)`, `(2,5)`, `(3,4)`, `(3,5)`, `(3,7)`, `(4,3)`, `(4,5)`,
--   `(5,4)`), for all `l`.  The residual's negation of this case is strictly stronger than `hnd`.
--
-- What is *left* in the residual is therefore: `u` cyclically reduced, `¬IsProperPower`, `n ≥ 2`,
-- every letter occurring with non-zero exponent sum, no letter-once, **no fibered killing weight
-- (at `l = 1`)**, no letter carrying a killing weight of value `1`, no Nielsen-image count drop --
-- e.g. the two-letter roots `a ^ 4 b ^ 7`, `a ^ 3 b ^ 8`, `a ^ 2 b ^ 2` and the non-fibered knot
-- relators at *every* `l ≥ 1`.  For these the only remaining route is a *proper* (non-normal)
-- vertex, i.e. Britton, i.e. the graph-of-spaces splitting of the `ℤ`-cover with a `ℤ`-domain.
--
-- (1) *The `⊤`-route (the kernel of a weight map as the vertex) is NOT sufficient in general; do
-- not try to close the residual with it.*  For `α = {a, b}` the only primitive weight killing `u` is
-- (up to sign) `(eps b, -eps a)`, and the usual abelianisation argument
-- (`[G,G] ⊆ K ⊆ G`, `G^ab = ℤ ≅ G/K` ⟹ `K = [G,G]`) shows that the kernel `K` of the weight map is
-- the *commutator subgroup*.  For a non-fibered knot-group relator (`u = a ^ p b ^ q` is fibered, but
-- e.g. the 5_2 relator is not) `[G,G]` is *not finitely generated* (Stallings), hence not a
-- one-relator group, so no isomorphism `⟨β | v ^ l⟩ ≃* ker (presentedCohom …)` exists.  The vertex
-- of a valid Magnus step is therefore a *proper* subgroup of `K` (the fundamental group of a
-- finite *domain* in the `ℤ`-cover), exactly as Linton's tower theory requires.
-- (Corollary: the statement `ker (presentedCohom c u l hc) ≅ ⟨β | v ^ l⟩` in
-- `Submission.Work.OROneRel.magnusStepCase2` is false in general — its remaining `sorry` cannot be
-- discharged as stated.)
--
-- (2) *The `ℤ`-cover/gauge bookkeeping, in the sharpest form.*  Fix a primitive killing weight `c`
-- (`cohom c u = 1`) and `τ` with `cohom c τ = ofAdd 1`.  Let `E` be the set of edges of the level
-- graph (vertices `ℤ`, edges `(x, i) : i → i + c x`) and `T` a spanning tree.  Then
-- `ker (cohom c) = F(E ∖ T)` via the loop classes of the non-tree edges (Stallings graph theorem),
-- `u` corresponds to the word `v` of the *non-tree traversals* of its own walk, `|v| = n − #{tree
-- traversals}`, and the kernel `K` of the weight map on `⟨α | u ^ l⟩` is `F(E ∖ T)/N` where `N` is
-- the normal closure of the `σ`-orbit of `v ^ l`, `σ` being the automorphism of `ker (cohom c)`
-- induced by conjugation with `τ`.  The orbit elements are conjugates of the *shifted* words
-- `v_m = Π {(x_j, i_j + m) : (x_j, i_j) ∉ T}` (the conjugating words telescope along the walk), so
-- `N = ⟨⟨{v_m ^ l : m ∈ ℤ}⟩⟩`; this is a one-relator group only if the shifted words lie in
-- `⟨⟨v ^ l⟩⟩`, which is *false* in general.  Hence the norm decrease offered by the first-arrival
-- gauge does not by itself give the vertex — one also needs the "domain" (the extra gate edges) and
-- the graph-of-spaces splitting.
--
-- (3) *The recognition tool is available and is the right one.*  The Bass--Serre structure theorem
-- in the graph-of-groups form is formalized (`Submission.Work.ORBassSerre.Action.Structure`):
-- `TreeDatum` (a spanning-tree lift of a cocompact tree action without inversions),
-- `BSPresentation.rels`/`Gamma`/`Φ`, `BSReduction.Φ_injective` (given `IsTree V`),
-- `Phi_surjective.closure_lifts_top_aux`.  For a tree action with *one* vertex orbit and *one* edge
-- orbit, `Γ` is literally `HNNExtension (vgroup) (eGroup) (eGroup) φ` with the edge maps
-- `eGroupToSrc = inclusion` and `eGroupToTgt = conj (sElt)⁻¹` — and, because in the application the
-- HNN relation holds in `G` by construction, this *is* the HNN presentation of `G`.  So the whole
-- residual reduces to a single geometric input:
--
--     construct a `G`-action on a tree (a `Quiver` with involutive reverse) with one vertex orbit,
--     one edge orbit, vertex stabilizer a group presented as `⟨β | v ^ l⟩` with `relatorNorm v <
--     relatorNorm u` and `¬ IsProperPower v`, and with `mk u` equal to `of (mk v)` up to
--     conjugacy.
--
-- Equivalently (and this is the honest classical content): a finite *domain* `D` in the `ℤ`-cover
-- with `D ∩ t D` connected, so that the translates `t ^ k D` form a *line of pieces* and the dual
-- graph of the decomposition of the universal cover is the required tree; the vertex is `π₁ (D)`,
-- one-relator with the root of norm `< n`.  This is Linton, arXiv 2202.11324, Proposition 4.3
-- (with Theorem 2.6 for the `π₁`-injectivity of the gate inclusions).  Note that the *injectivity*
-- alone is not enough (with the walk-based coedge basis of `a ^ 4 b ^ 7` the vertex presentation is
-- even trivial, so injectivity is vacuous while the splitting is false) — the content is the
-- *splitting*, i.e. the tree.
-- ---------------------------------------------------------------------------------------------
-- The three case predicates `Work.OROneRel.FreeKernelCase`, `Work.OROneRel.NielsenCountCase` and
-- `Work.OROneRel.BlockWordCase` used below are declared in the *lower* module
-- `Submission/Work/OROneRel/magnusCaseDefs.lean` (imported at the top of this file), so that the
-- modules whose statements carry them as hypotheses can be placed *below* this file in the module
-- order.  See the header of that module for the reason.

-- ---------------------------------------------------------------------------------------------
--
-- **THE DOMAIN PICTURE, IN ITS SHARPEST FORM (this session's analysis; read before attacking).**
--
-- Everything that is *proved* about the residual goes through the `⊤`-route: for a killing weight
-- `c` (`cohom c u = 1`) and a deck element `τ` (`cohom c τ = 1`), the kernel `K = ker (presentedCohom c
-- u l hc)` is normal, `⟨α | u ^ l⟩ = ⟨K, mk τ⟩`, and (when `mk τ` has infinite order modulo `K`)
-- `⟨α | u ^ l⟩ ≅ HNNExtension ↥K ⊤ ⊤ (conj (mk τ))` -- with *no* Britton input at all
-- (`hnnKernelForm_tracking`, `exists_hnn_top_of_normal_vertex`).  So the residual reduces to
-- *identifying the vertex*: `K ≅ ⟨β | v ^ l⟩` in a way carrying the class of `u` to the class of the
-- root (`magnusStepCase2_of_kernelData`).  The two proved instances are exactly:
--   * `K` free and `l = 1` (the fibered case; `magnusStepCase2_of_freeKernel`, now wired in), and
--   * the Nielsen count route of the weighted step's *interval* gauge
--     (`magnusStepData_of_count_image`, now wired in).
--
-- (i) *The `⊤`-route cannot reach `l ≥ 2`.*  For `l ≥ 2` the class of `u` lies in `K` and has order
-- `l` in `⟨α | u ^ l⟩` (KMS, morally), so `K` is *not* free.  Moreover `K` is not of the form
-- `⟨β | v ^ l⟩` in general: the abelianisation of `⟨β | v ^ l⟩` with `β` an arbitrary type is
-- `(free abelian) ⊕ (cyclic)`, whereas for the first genuinely hard instance `u = a ^ 2 b ^ 2`,
-- `l = 2`, `c = (1,-1)`, the Reidemeister--Schreier presentation of `K = ker (presentedCohom c u 2 hc)`
-- for the transversal `{1, b}` is `⟨a, x = b a b⁻¹, y = b ^ 2 | (a ^ 2 y) ^ 2, x ^ 2 y x ^ 2 y⟩`, whose
-- abelianisation is `ℤ ⊕ ℤ/2 ⊕ ℤ/8` (Smith normal form of `⟨(4,0,2), (0,4,2)⟩`), which is *not* of
-- that form.  So the vertex of a valid Magnus step must be a *proper* (non-normal) subgroup of `K`,
-- and its construction is Britton, i.e. the graph-of-spaces splitting of the `ℤ`-cover.
--
-- (ii) *Where the domain comes from: the "band" of the walk.*  Let `c` be killing (`c u = 0`) with a
-- deck element `τ` (`c τ = 1`), and let `[lo, hi]` be the interval of levels visited by the walk of
-- `u` in the level graph (vertices `ℤ`, edge `(x,i) : i → i + c x`).  Then:
--   * the band `[lo,hi]` contains the walk, so it supports the lift of the 2-cell;
--   * (convention, machine-checked in `Submission/Work/OROneRel/band_one_lift.lean`: the symbol
--     `((x,j),b)` of `decor c 0 (wordOf u)` stands for the *edge* `(x,j)`, whose endpoints are `j` and
--     `j + c x`, for *both* signs `b` -- the stored level is the edge's source level, and a negative
--     letter traverses that edge backwards.  So "the walk is inside the band" is literally
--     `∀ p ∈ decor c 0 (wordOf u), lo ≤ p.1.2 ∧ lo ≤ p.1.2 + c p.1.1 ∧ p.1.2 ≤ hi ∧ p.1.2 + c p.1.1 ≤ hi`,
--     and a translate by `k` is inside iff the same holds with `p.1.2 + k`.  **PROVED**:
--     `Work.OROneRel.band_one_lift` (module `Submission.Work.OROneRel.band_one_lift`) produces
--     `lo < hi` with the walk inside and *no* non-zero translate inside -- the band of the walk is
--     minimal, hence supports exactly one lift of the `2`-cell);
--   * a lift `t ^ k (u) ⊆ [lo,hi]` forces `k = 0`, since the walked levels exactly exhaust `[lo,hi]`
--     -- so the band supports *exactly one* lift of the relator `u ^ l`, i.e. the 2-complex band is a
--     *one-relator* complex;
--   * the intersection `[lo,hi] ∩ [lo+1,hi+1] = [lo+1,hi]` is non-empty and connected, so the
--     translates form a *line of pieces* and the graph-of-spaces (Bass--Serre) theorem would give
--     `⟨α | u ^ l⟩ ≅ HNNExtension (π₁ Z) (π₁(Z ∩ t⁻¹Z)) (π₁(Z ∩ tZ)) (conj t)`;
--   * taking the domain's spanning tree to contain every traversal of the walk except one makes the
--     vertex's relator word a *single letter* `x ^ {±l}`, so the vertex is `⟨β | x ^ l⟩` with
--     `relatorNorm x = 1 < n` and `¬ IsProperPower x` -- precisely the target's norm bound (a free
--     vertex when `l = 1`, the group `F_k ∗ ℤ/l` when `l ≥ 2`);
--   * the *tracking* is the telescoping identity: the class of the closed walk `u` in `π₁ Z` is
--     `∏_j g_{j-1} (loop class) g_{j-1}⁻¹` with `g_j` the tree path to the `j`-th vertex; with a single
--     non-tree traversal this is `g x ^ {±1} g⁻¹`, i.e. conjugate to the vertex root -- and in the HNN
--     group `of (mk v)` for `v = x` is exactly that class.  (For `l = 1` both classes are trivial.)
--   The only missing ingredients are exactly Linton's: (a) `D ∩ t D → D, t D` is `π₁`-injective
--   (a Freiheitssatz for the domain), and (b) the graph-of-spaces splitting (Britton).
--
-- (iii) *Ablation: a general `τ`-gauge (no letter of weight `1`) gives no norm decrease at all.*  With
-- the gauge `W(i) = τ ^ i` the symbols are `ρ(x,i) = τ ^ i x τ ^ (-i - c x)`; for a *reduced* word the
-- decorated symbol word is already reduced (two consecutive symbols can only cancel if they are
-- inverses of the same edge, i.e. if the word contains `x x⁻¹`), so nothing is deleted and the
-- rewriting has norm exactly `n`.  Deletion -- hence the norm drop -- needs a *letter* `t` with
-- `c t = 1` (then `ρ(t,i) = 1`).  What remains for a general killing weight is only the *tree* form of
-- the decrease (the domain's spanning tree, as in (ii)).
-- ---------------------------------------------------------------------------------------------
--

/-- **The count case with `ψ = id` subsumes the weighted (divisibility) case.**  If a letter `t` of
`u` carries a killing weight of value one (`c t = 1`, `cohom c u = 1`), then the decorated word of `u`
with the `t`-symbols deleted is *strictly* shorter than `u` (`wvListAux_length_lt`: the deleted
`t`-letters are at least one), so all components of `NielsenCountCase u` hold with `ψ = id`.
Consequently `¬ NielsenCountCase u` implies the residual's hypothesis `hnd` (the two are not
independent), and the weighted Magnus step `magnusStepCase2_of_weight` is a special case of
`NielsenCountCase`. -/
theorem nielsenCountCase_of_weight_witness {α : Type u} [DecidableEq α] (u : FreeGroup α)
    (hu : ¬ IsProperPower u) (hcyc : IsCyclicallyReducedRelator u)
    (hn : 2 ≤ relatorNorm u)
    (hbad : ∀ x : α, x ∈ relatorLetters u → eps x u ≠ 0)
    (t : α) (c : α → ℤ) (ht : t ∈ relatorLetters u) (hct : c t = 1)
    (hcu : cohom c u = 1) :
    NielsenCountCase u := by
  classical
  refine ⟨MulEquiv.refl (FreeGroup α), t, c, hu, hcyc, hn, hbad, ht, hct, hcu, ?_⟩
  have hb : ∃ b : Bool, (t, b) ∈ wordOf u := by
    rw [relatorLetters] at ht
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, hb⟩
  have hlt : (wvListAux c t 0 (wordOf u)).length < (wordOf u).length :=
    wvListAux_length_lt c t 0 (wordOf u) hb
  have hlen : (wordOf u).length = relatorNorm u := rfl
  simpa only [MulEquiv.refl_apply, hlen] using hlt

/-- **The two-letter case reduces to an HNN decomposition of the Tietze presentation.**  For
`u = a ^ p * b ^ q` (`a = FreeGroup.of 0`, `b = FreeGroup.of 1`), the Tietze transformation
`twoLetter_amalgam_tietze` identifies `⟨a, b | (a ^ p b ^ q) ^ l⟩` with
`⟨a, b, c | c ^ l, b ^ q c⁻¹ a ^ p⟩`, carrying `a ^ p b ^ q` to the *generator* `c`.  Consequently,
any HNN decomposition of the second presentation whose vertex `⟨β | v ^ l⟩` has the generator `c`
tracked (`e (mk c)` conjugate to `of (mk v)`) transports to the target's second disjunct for `u`,
provided `relatorNorm v < relatorNorm u`.  This is the clean way to attack the residual's two-letter
instances, where the tracking element is a *generator* of the vertex presentation. -/
theorem hasMagnusStepAt_twoLetter_of_hnnData (p q l : ℕ)
    (h : ∃ (β : Type) (v : FreeGroup β)
        (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β))))
        (φ : A ≃* B)
        (e : PresentedGroup ({FreeGroup.of (2 : Fin 3) ^ l,
            FreeGroup.of (1 : Fin 3) ^ q * (FreeGroup.of (2 : Fin 3))⁻¹ *
              FreeGroup.of (0 : Fin 3) ^ p} : Set (FreeGroup (Fin 3))) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ¬ IsProperPower v ∧
        relatorNorm v <
          relatorNorm (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) ∧
        ∃ c' : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk _ (FreeGroup.of (2 : Fin 3))) =
            c' * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c'⁻¹) :
    HasMagnusStepAt (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) l := by
  obtain ⟨β, v, A, B, φ, e, hpp, hnorm, c', htr⟩ := h
  obtain ⟨eT, heT⟩ := twoLetter_amalgam_tietze p q l
  exact ⟨β, v, hpp, hnorm, A, B, φ, eT.trans e, c', by
    rw [MulEquiv.trans_apply, heT]
    exact htr⟩

-- **The block-word case of the two-letter Magnus step** (DELEGATED, see
-- `Submission/Work/OROneRel/magnusStepAt_blockWord.lean`).  For distinct letters `a b` of `α` and
-- `p q l` with `1 ≤ p`, `1 ≤ q`, `1 ≤ l` and `gcd p q = 1`, the group `⟨α | (a ^ p * b ^ q) ^ l⟩`
-- satisfies the target's second disjunct.  The mathematical content is the colleague's
-- `Work.OROneRel.twoLetter_hnnData` (the two-letter splitting, in the Tietze presentation
-- `⟨a, b, c | c ^ l, b^q c⁻¹ a^p⟩`, via `hasMagnusStepAt_twoLetter_of_hnnData` above); the work is
-- the transport along the injective relabelling `0 ↦ a`, `1 ↦ b` of `Fin 2` into `α`.
--
-- The transport `hasMagnusStepAt_map_of_injective` is stated with a *single* universe (`{σ α :
-- Type u}`), so it cannot be applied to `σ = Fin 2` (`Type 0`) and `α : Type u`; the delegated
-- module states the conclusion directly at `α : Type u` (so that it is definitionally the second
-- disjunct of the target) and carries out the universe bookkeeping itself.
--
-- Together with the *other* two-letter cases (a letter occurring once on one side only, the
-- divisibility case, and the free kernel at `l = 1`) this removes a further family from the
-- residual: what is left there has `≥ 3` occurring letters, or two occurring letters in a pattern
-- that is not `a ^ p * b ^ q`.

-- ## SESSION NOTE (the count case does *not* cover all `≥ 3`-letter relators; the two-letter amalgam)
--
-- The residual below carries `hnc : ¬ NielsenCountCase u`.  This note records the findings.
--
-- **(1) `NielsenCountCase u` is *not* automatic for relators with `≥ 3` occurring letters.**  A
-- delegation of the corresponding statement (`OROneRel/nielsenCountCase_of_three_letters`: `≥ 3`
-- occurring letters + the residual's hypotheses `⟹ NielsenCountCase u`) was **declared FALSE** by its
-- prover, with the concrete instance `u = a ^ 105 * b ^ 156 * c ^ 170` (`α = Fin 3`): it satisfies
-- every hypothesis --
--   * `x = a`, `y = b`, `z = c` occur; the reduced word `a^105 b^156 c^170` is cyclically reduced and
--     not a proper power (`relatorNorm u = 431` is prime, so `u = v ^ k`, `k ≥ 2`, forces `|v| = 1`);
--   * `eps a = 105`, `eps b = 156`, `eps c = 170`, all non-zero;
--   * `hnd`: `gcd(156,170) = 2 ∤ 105`, `gcd(105,170) = 5 ∤ 156`, `gcd(105,156) = 3 ∤ 170`;
-- -- and the *single transvection* witnesses are provably excluded: for `ψ(s) = s · j ^{±1}` the only
-- available `t` is `s` (for `t = j` the divisibility is `gcd(eps s u, …) ∣ eps j u`, which `hnd`
-- refutes; for the third letter likewise), and on a block word the count forces `|k| = 1` with the
-- inserted letter the inverse of the neighbouring block, so the six possible conditions are
--   `gcd(|156-105|,170) = 17 ∣ 105` (FALSE), `gcd(|170-105|,156) = 13 ∣ 105` (FALSE),
--   `gcd(|170-156|,105) = 7 ∣ 156` (FALSE), and the three with the roles of `t` exchanged:
--   `17 ∣ 156` (FALSE), `13 ∣ 170` (FALSE), `7 ∣ 170` (FALSE).
-- So neither (Q″) of `NOTES_magnus_step_root_no_eps_zero.md` nor any single transvection covers
-- `a ^ 105 b ^ 156 c ^ 170`, and the *residual's `≥ 3`-letter instances are genuine* (small cases such
-- as `a^6 b^10 c^15`, `a^6 b^14 c^21`, `a^14 b^35 c^10` *are* covered -- by `ψ(a) = a b ^{-1}`, whose
-- divisibility `gcd(156,170) ∣ 105`-type condition holds there because the pairwise gcds are large and
-- the differences small -- but this behaviour does *not* persist).  What *is* provable in general,
-- and is the only part of the recipe that survives, is the **count formula**
--
--     `(wvListAux c s 0 (wordOf (ψ u))).length = n - 2 * (#cancellations)`,
--
-- for a transvection `ψ : s ↦ s · i^{±1}` (`n = relatorNorm u`, one inserted symbol per `s`-letter,
-- one cancellation per `s` whose successor is the matching `i^{±1}`), which is the *norm bookkeeping*
-- that remains usable whatever the arithmetic; the obstruction is the divisibility, not the count.
--
-- **(2) The two-letter relators are the wall, and they have a concrete structure.**  For the *block*
-- word `u = a ^ p * b ^ q` with `gcd p q = 1` the walk of `u` in the `ℤ`-cover (weight `a ↦ q`,
-- `b ↦ -p`) is a **simple cycle**: the decorated word has `Nodup` and its source levels number
-- `p + q` (`Work.OROneRel.twoLetter_cycle_decor`, proved by a colleague) -- the levels are
-- `0, q, …, (p-1)q, pq, p(q-1), …, p`.  Consequences, both recorded here because they are what a
-- future attack must use:
--
--   * *(the closing traversal is the only non-discovering one)* under the first-arrival gauge the
--     first `p+q-1` traversals of the walk are discovering, so their loop class is `1`
--     (`walkGauge_triv`) and they are **not** in `coverBetaEdge`; hence the walk's coedge word
--     `coedgeRoot (uGauge c u) c u` is a *single letter* and `relatorNorm` of it is `1`
--     (delegated as `Submission.Work.OROneRel.coedgeRoot_twoLetter_eq_one`);
--   * *(that vertex is too small)* with `β` of *cardinality one* the vertex `⟨β | x ^ l⟩` is the
--     cyclic group `ℤ/l`, and an HNN over `ℤ/l` is either `(ℤ/l) ∗ ℤ` (for `A = ⊥`), or
--     `ℤ/l ⊕ ℤ`, or the dihedral group `⟨x, t | x^l, t x t^{-1} x⟩` -- all of them virtually
--     abelian (or free), whereas `G = ⟨a,b | (a^p b^q)^l⟩` contains the amalgam vertex
--     `⟨a, c | c^l⟩ = ℤ ∗ ℤ/l` of the Tietze decomposition.  So the vertex of a valid decomposition
--     of the block word must have `|β| ≥ 2`, and the natural candidate is the *domain's* coedge set
--     (the window band `D` has `|E| - |V| + 1` coedges; for `a ^ 3 b ^ 8`, `D = [0,24]`, that is
--     `39 - 25 + 1 = 15`, giving `⟨β | x ^ l⟩ = ℤ/l ∗ F_14` with root `x` of norm `1` and the walk's
--     word a single root symbol).
--
-- For `u = a ^ p * b ^ q` the count case is also *provably* unavailable: for a reduced
-- `w = ψ(a)^p ψ(b)^q` one
-- has `#{non-a letters of w} ≥ |b-exponent of w| = |p w_b + q v_b|`, whence `t = a` forces
-- `Q ∣ P` with `P = p w_a + q v_a`, `Q = p w_b + q v_b`, `det = w_a v_b - w_b v_a = ±1`, and the cases
-- `|v_b| ≤ 1`, `|w_b| ≤ 1` that the count budget allows are all incompatible with `P/Q ∈ ℤ` (this is
-- a finite check over `(p,q) = (3,8), (4,7), (5,7), (5,8), (4,9)`, confirmed by an exhaustive search
-- over `ψ` with `|ψ(a)|, |ψ(b)| ≤ 5` and over the *block* forms `a ^{p_1} b ^{s_1} a ^{p_2} …`).
-- So the two-letter residual instances are genuinely residual.
--
-- On the other hand the two-letter group itself has a *Tietze* structure, obtained by adding the
-- generator `z := a ^ p * b ^ q` (so that `b ^ q = z a^{-p}`):  **delegated as
-- `Submission.Work.OROneRel.twoLetter_amalgam_tietze`** (reviewed, `looks correct as stated`), whose
-- statement is
--
--     `∃ e : ⟨a, b | (a ^ p * b ^ q) ^ l⟩ ≃* ⟨a, b, z | z ^ l, b ^ q * z^{-1} * a ^ p⟩`,
--         `e (mk (a ^ p * b ^ q)) = mk z`
--
-- (the right-hand presentation is the *same* group: its second relator gives `z = b ^ q * a ^ p`, which
-- is the conjugate `b ^ q (a ^ p b ^ q) b^{-q}` of `a ^ p b ^ q`, so `z ^ l = 1` says exactly
-- `(a ^ p b ^ q) ^ l = 1`).  In the right-hand presentation `z` is a *generator*, i.e. the residue of
-- `a ^ p * b ^ q` is the image of a generator whose only relation is `z ^ l` -- which is precisely the
-- *tracking* the target asks for.  Reading the two relations as an amalgam:
--
--     `≅ (⟨a, z | z ^ l⟩)  ∗_{⟨z a^{-p}⟩ ≅ ⟨b ^ q⟩}  (⟨b | ⟩)  =  (ℤ ∗ ℤ/l) ∗_{ℤ} ℤ`
--
-- an amalgam of `ℤ ∗ ℤ/l` with `ℤ` over `ℤ` (no Freiheitssatz needed: `z a^{-p}` has infinite order
-- and is not a proper power in `ℤ ∗ ℤ/l`).  In particular a *valid vertex group* for the target is
-- available in the two-letter case: `ℤ ∗ ℤ/l` is
-- `⟨z, a | z ^ l⟩`, i.e. `⟨β | v ^ l⟩` with `relatorNorm v = 1 < p + q` and `¬ IsProperPower v`.
-- What is missing is again only the *splitting*: the amalgam has *two* vertex orbits while the
-- target needs an HNN (one), and the comparison map of `hnnConjSplit` over `H = ℤ ∗ ℤ/l` with stable
-- letter `b` is surjective but its edge group `H ⊓ b^{-1} H b` is strictly larger than `⟨c⟩` - the
-- abelianisation forces `A ^ab` to be the *full* free part of `H ^ab` (rank `|β| - 1 = 1`, cf.
-- `rank π(R) = |β| - |α| + 1` and `torsion(V ^ab / A) ≅ ℤ/(l * gcd p q)`, which forces `d_v = 1` and
-- `A ^ab` onto the free factor; for `(p,q) = (3,8)`, `l = 2` this needs an element of class
-- `(-1, 1)`, e.g. `a^{-1} z`).  So even the two-letter case needs an injectivity statement for a
-- *proper* edge subgroup, i.e. the same geometric input as the general case.
--
-- *The vertex of the two-letter case has infinite index, and the obvious candidates are excluded.*
-- In `HNN (V, A, B, φ)` the stable letter has infinite order modulo `V`: the relation
-- `t a t^{-1} = φ a` has total `t`-exponent sum `1 - 1 = 0`, so `t ↦ 1`, `V ↦ 0` is a
-- homomorphism `HNN → ℤ` trivial on `V` and nontrivial on `t`.  Hence any vertex of a valid
-- decomposition must be a subgroup of `⟨α | u ^ l⟩` of *infinite* index, and in fact inside the
-- weight kernel `ker χ`.  This rules out the tempting candidates: for `u = a ^ p b ^ q`, `l = 2`,
-- `q` even, the subgroup `H = ⟨a, b²⟩` *does* have the right vertex shape -- `q = 8` gives
-- `H = ⟨a, b' | ((b')⁴ a³)²⟩` with `v = (b')⁴ a³`, `relatorNorm v = 5 < 11`, `¬ IsProperPower v`,
-- and the root tracks, since `a³ b⁸ = b⁸ (a³ b⁸) b^{-8} = b⁸ a³` is conjugate to `b⁸ a³ = v` -- but
-- the comparison map `HNN (↥H, H, H, conj_b) → G` sends `t² ↦ b² ∈ H` while `t² ≠ b²` in the HNN
-- (`b²` is a base element and `t` has infinite order modulo the base by the homomorphism above), so
-- it is not injective.  So the vertex is not one of the "block" subgroups `⟨a, b ^ k⟩`, and its
-- construction is the geometric input referred to above.
--
-- *The two-letter route as it now stands (session 13).*  The pieces that are available are
--
--   * `hasMagnusStepAt_twoLetter_of_hnnData` (this file, proved): the target for the block word
--     `a ^ p * b ^ q` follows from the HNN data of the *Tietze presentation*
--     `⟨a, b, c | c ^ l, b^q c⁻¹ a^p⟩` with the generator `c` tracked (the Tietze iso is
--     `twoLetter_amalgam_tietze`, and `c` *is* the residue of `a ^ p * b ^ q` there);
--   * `twoLetter_cycle_decor` (colleague, proved): the walk of the block word is a simple cycle --
--     `p + q` distinct levels, every edge traversed at most once;
--   * `coedgeRoot_twoLetter_eq_one` (colleague, proved): consequently the *walk's* coedge word is a
--     single letter, of norm `1`, not a proper power;
--   * `twoLetter_hnnData` (colleague, **in flight**): the missing geometric input, i.e. the HNN data
--     for the Tietze presentation of the block word.
--
-- The candidate HNN data, from the `ℤ`-cover picture, is: `β` = the *domain's* coedges (all edges of
-- a window band that are not in a spanning tree of its `1`-skeleton: for `a ^ 3 b ^ 8`, the band
-- `[0,24]` has `25` vertices and `39` edges, hence `15` coedges), `v = x` the single *non-tree*
-- traversal of the walk (`relatorNorm v = 1`, `¬ IsProperPower v`, tracking by telescoping), and
-- `A = π₁(D ⊓ t⁻¹D)`, `B = π₁(D ⊓ tD)`, `φ` the shift.  (Do *not* use the walk's own coedge set as
-- `β`: `coedgeRoot_twoLetter_eq_one` computes its root as a single letter, so that vertex is the
-- cyclic group `ℤ/l`, which cannot be the vertex of a valid decomposition -- see above.)
--
-- **(3) `NielsenCountCase` subsumes the weighted (divisibility) case, with `ψ = id`.**  If
-- `∃ t c, t ∈ relatorLetters u ∧ c t = 1 ∧ cohom c u = 1` then the count
-- `(wvListAux c t 0 (wordOf u)).length = relatorNorm u - #(t-letters) < relatorNorm u` outright, so
-- with `ψ = id` all eight components of `NielsenCountCase u` hold; consequently
-- `¬ NielsenCountCase u` implies the residual's `hnd` hypothesis (the two are not independent).
-- This is proved below, as `nielsenCountCase_of_weight_witness`.
--
-- **(4) Status of the wall (session 12).**  The fleet's reduction of the residual to a *single*
-- statement is now complete on the generation side: `Work.OROneRel.closure_shift_classes_insert_top`
-- (proved) gives `⟨α | u ^ l⟩ = ⟨mk τ, mk (loop class of e) : e ∈ D⟩` for any weight `c` with
-- `cohom c u = 1`, any `τ` of weight one and any set `D` of edges meeting every edge orbit.  So with
-- `H = ⟨the loop classes of the domain's edges⟩` the hypotheses of `hnnConjSplit.hnnConjMap_bijective`
-- are met, and the *only* remaining input for the residual is
-- `Function.Injective (hnnConjMap H τ)`, which the fleet's `NOTES` (SESSION 10 §1, §6) identifies
-- with Linton's graph-of-spaces splitting (`Z`-domain + the graph-of-spaces theorem).  Everything
-- *elementary* about the residual is by now either proved or refuted; what remains is that geometric
-- input, in one of the two shapes recorded above (a `G`-tree with one vertex and one edge orbit, or
-- Britton for the line of pieces `t ^ k D`).
--
-- **(5) The two modules that will close this file.**  Two colleagues' modules prove statements that
-- *directly* discharge parts of this file; whenever one of them lands, importing it here and
-- replacing the corresponding `sorry` is a one-line change:
--
--   * `Submission.Work.OROneRel.magnus_step_root_no_eps_zero` aims at stating and proving
--     `magnus_step_root_no_eps_zero` *verbatim* (same hypotheses, same conclusion), assembled inside
--     that module from the single injectivity input.  It still contains a `sorry`, so it may be
--     imported here only once it is complete -- at which point this file's
--     `magnus_step_root_no_eps_zero` can be replaced by it outright;
--   * `Submission.Work.OROneRel.twoLetter_amalgam_tietze` (proved) is the Tietze step
--     `⟨a, b | (a^p b^q)^l⟩ ≅ ⟨a, b, c | c^l, b^q c⁻¹ a^p⟩` carrying `a^p b^q` to the generator `c`;
--     a transport of the target's HNN data along it is the clean way to attack the two-letter case.
-- ---------------------------------------------------------------------------------------------
--

theorem magnus_step_root_no_eps_zero_residual {α : Type u} [DecidableEq α] (u : FreeGroup α)
    (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (hnd : ∀ (t : α) (c : α → ℤ), t ∈ Work.OROneRel.relatorLetters u → c t = 1 →
      Work.OROneRel.cohom c u ≠ 1)
    (hnlo : ∀ (x : α) (b : Bool), (FreeGroup.toWord u).count (x, b) = 1 →
      (FreeGroup.toWord u).count (x, Bool.not b) ≠ 0)
    (hocc : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u)
    (hnfk : ¬ FreeKernelCase u l)
    (hnc : ¬ NielsenCountCase u) :
    HasMagnusStepAt u l := by
  classical
  -- ## `α` is finite
  -- every generator occurs in the word of `u` (`hocc`), so the set of occurring generators is
  -- finite and `Fintype α` is available (this is what the window/Freiheitssatz plank needs).
  let L : List (α × Bool) := @FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) u
  let s : Finset α := L.toFinset.image Prod.fst
  have hmem : ∀ a : α, a ∈ s := by
    intro a
    obtain ⟨b, hb⟩ := hocc a
    exact Finset.mem_image.mpr ⟨(a, b), List.mem_toFinset.mpr hb, rfl⟩
  have hU : (Set.univ : Set α).Finite := (Finset.finite_toSet s).subset (fun a _ => hmem a)
  haveI : Finite α := Finite.of_finite_univ hU
  letI : Fintype α := Fintype.ofFinite α
  -- ## The window data of the minimal `Z`-domain (PROVED, sorry-free)
  -- `Work.OROneRel.NC.exists_window_support_data_cycred` is the namespaced copy of the colleague's
  -- `Work.OROneRel.exists_window_support_data_cycred`: it produces the band `[lo,hi]` of the walk,
  -- the killing weight `c`, the tree-path gauge `Wt` (deck element of weight one), and the
  -- cyclic reducedness of the root.  The copy is needed because the original module pulls
  -- `Work.OROneRel.decor_replicate_true`, which clashes with the declaration of the same name in
  -- `Submission.Work.OROneRel.twoLetter_cycle_decor` -- a module in the import closure of the
  -- Freiheitssatz used below.  See the header of
  -- `Submission/Work/OROneRel/exists_window_support_data_cycred_nc.lean`.
  obtain ⟨c, lo, hi, Wt, hcu, hW0, hcoh, hlo1, hhi1, hwin, hone, htree, hcov, hlast, _hcycred⟩ :=
    NC.exists_window_support_data_cycred u l hl hu hcyc hn hbad
  -- ## The Freiheitssatz of the domain (the fleet's active statement)
  -- Linton's `π₁`-injectivity of the minimal `Z`-domain: `winRho x ∈ ⟪u ^ l⟫ → x ∈ ⟪winRoot ^ l⟫`.
  -- `Work.OROneRel.bandFreiheitssatz_of_windowData` is the statement the fleet is actively proving
  -- (its reduction to the intersection hypothesis `hI`,
  -- `bandFreiheitssatz_of_windowData_of_intersection`, is proved in the same file).  This is the
  -- *only* place in this file that rests on a `sorry` from the Freiheitssatz side.
  have hA : ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))) :=
    bandFreiheitssatz_of_windowData u l hl hu hcyc hn hbad hcu hW0 hcoh hwin hone htree hcov hlast
  -- ## The root data of the vertex presentation `⟨winBeta | winRoot ^ l⟩`
  -- aperiodicity: a proper-power witness for `winRoot` would transport to one for `u` along the
  -- telescoping identity `winRho (winRoot) = u`.
  have hppv : ¬ IsProperPower (winRoot Wt c lo hi u) := by
    rintro ⟨w, k, hk, hwk⟩
    exact hu ⟨winRho Wt c lo hi w, k, hk, by
      rw [← winRho_winRoot Wt hW0 hcu lo hi hwin, hwk, map_pow]⟩
  -- the strict norm decrease: the gauge walks through at least one tree edge *of the walk*, which
  -- is deleted from the root.
  have hnorm : relatorNorm (winRoot Wt c lo hi u) < relatorNorm u :=
    winRootNormLt Wt lo hi hcyc hwin hlast
  -- ## The splitting: generation + the injectivity of the comparison map (the fleet's *tree* route)
  -- `Work.OROneRel.Low.windowSplitting_v2` (in `Submission/Work/OROneRel/winSplittingLow.lean`, a
  -- module *below* this one) produces a weight-one deck element `τ` whose walk lies in the window,
  -- the generation plank `winVertex ⊔ ⟨mk τ⟩ = ⊤` and the injectivity of the canonical comparison
  -- map `hnnConjMap (winVertex …) (mk τ)`.  It is assembled from the two halves of the `Z`-domain
  -- splitting -- the free-group coset-graph tree
  -- (`Work.OROneRel.Low.winRhoRange_cosetTree_window_v2`) and the generation
  -- (`Work.OROneRel.Low.winVertex_generation_exists_windowWalk_v2`), both carrying the *case
  -- hypotheses* of this residual in scope below -- through the proved
  -- `Work.OROneRel.Low.magnus_residual_winTreeSplitting_of_freeTree` and the proved
  -- `Work.OROneRel.exists_split_of_cosetTree`, i.e. Linton's Prop. 4.3/2.2.19 (the graph-of-spaces
  -- splitting of the `Z`-domain).  This is the one remaining `sorry` on the splitting side of this
  -- file.
  obtain ⟨τ, hτ, _hwalk, hgen, hinj⟩ :=
    Low.windowSplitting_v2 u l hl hu hcyc hn hbad hnd hnlo hocc hnfk hnc
      hcu hW0 hcoh hwin hone htree hcov hlast hlo1 hhi1 hA
  -- ## The `Z`-domain datum, and the transport to the target
  -- `Work.OROneRel.magnusDomainDatum_of_hnnConjMap` packages the datum from the Freiheitssatz `hA`
  -- (which identifies the vertex `winVertex` with the one-relator presentation `⟨β | v ^ l⟩`) and
  -- the splitting data; the target is then `magnus_step_root_no_eps_zero_of_domainDatum`.
  exact magnus_step_root_no_eps_zero_of_domainDatum u l
    (magnusDomainDatum_of_hnnConjMap hcu hW0 hwin hτ hppv hnorm hA hinj hgen)

theorem magnus_step_root_no_eps_zero_main {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  by_cases h : ∃ (x : α) (b : Bool), (FreeGroup.toWord u).count (x, b) = 1 ∧
      (FreeGroup.toWord u).count (x, Bool.not b) = 0
  · obtain ⟨x, b, h1, h2⟩ := h
    exact magnus_step_root_no_eps_zero_of_letter_once u l hl hu x b
      (by rw [← List.count_pos_iff]; omega) hcyc ⟨h1, h2⟩ hn
  · push_neg at h
    -- the *weighted* Magnus--Moldavanskii step: a letter `t` of `u` carrying a killing weight `c`
    -- with `c t = 1` is the second case of the no-exponent-sum-zero step.
    by_cases hw : ∃ (t : α) (c : α → ℤ), t ∈ Work.OROneRel.relatorLetters u ∧ c t = 1 ∧
        Work.OROneRel.cohom c u = 1
    · exact magnusStepCase2_of_weight u l hl hu hcyc hn hbad hw
    · push_neg at hw
      -- The residual is invoked in its *support-normalized* form: the free-generator case is
      -- discharged by the (proved) reduction `magnus_step_residual_of_support`, which derives the
      -- general residual from the form in which every generator of the ambient type occurs in `u`.
      -- the *two-letter block* case `u = a ^ p * b ^ q` (`a ≠ b`, `1 ≤ p, q`, `gcd p q = 1`) is
      -- *fully proved*, for every `l ≥ 1`, by `magnusStepAt_blockWord` -- no residual plank is
      -- needed for these instances (they are the ones for which every elementary route is provably
      -- dead), so they are peeled off before the residual.
      by_cases hbw : BlockWordCase u
      · obtain ⟨a, b, p, q, hab, hp, hq, hcop, rfl⟩ := hbw
        exact magnusStepAt_blockWord a b hab p q l hp hq hl hcop
      · refine magnus_step_residual_of_support
          (fun {σ} _inst u' l' hl' hu' hcyc' hn' hocc' hbad' hnd' hnlo' =>
            by
              -- the *free-kernel* case (`l = 1`, a killing weight with free kernel) is proved by
              -- `magnusStepCase2_of_freeKernel`; it is decided separately for the
              -- support-normalized relator, so that no transport of the case hypothesis is needed.
              by_cases hfk : FreeKernelCase u' l'
              · obtain ⟨hl1, c, hc, hτ, γ, hγ⟩ := hfk
                subst hl1
                exact magnusStepCase2_of_freeKernel u' hn' hc hτ ⟨γ, hγ⟩
              · -- the *Nielsen count* case, again decided for the support-normalized relator
                by_cases hnc : NielsenCountCase u'
                · obtain ⟨ψ, t, c, hpp, hcycψ, hnψ, hbadψ, ht, hct, hcu, hcount⟩ := hnc
                  exact magnusStepData_of_count_image u' l' hl' hu' hcyc' hn' hbad' ψ t c
                    hpp hcycψ hnψ hbadψ ht hct hcu hcount
                · exact magnus_step_root_no_eps_zero_residual u' l' hl' hu' hcyc' hn' hbad' hnd'
                    hnlo' hocc' hfk hnc)
          u l hl hu hcyc hn hbad hw h

theorem magnus_step_root {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u) :
    Work.OROneRel.relatorNorm u ≤ 1 ∨
      ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
        Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
        ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
          (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
            HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
          ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
            e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
              c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  by_cases h1 : relatorNorm u ≤ 1
  · exact Or.inl h1
  right
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hconj : cyclicConjugator u * cyclicReduction u * (cyclicConjugator u)⁻¹ = u :=
    cyclicConjugator_mul_cyclicReduction_mul_inv u
  have hcyc : IsCyclicallyReducedRelator (cyclicReduction u) :=
    isCyclicallyReducedRelator_cyclicReduction u
  have hnp : ¬ IsProperPower (cyclicReduction u) := not_isProperPower_cyclicReduction hu
  have hnorm : relatorNorm (cyclicReduction u) ≤ relatorNorm u := relatorNorm_cyclicReduction_le u
  have hn2 : 2 ≤ relatorNorm u := by omega
  obtain ⟨e1, he1⟩ := presentedGroup_pow_conj_iso u (cyclicReduction u) (cyclicConjugator u) l hconj
  by_cases hw1 : relatorNorm (cyclicReduction u) ≤ 1
  · obtain ⟨a, k, hk, hwk⟩ :=
      exists_zpow_of_relatorNorm_le_one hw1 (cyclicReduction_ne_one hu1)
    have hu' : u = cyclicConjugator u * FreeGroup.of a ^ k * (cyclicConjugator u)⁻¹ := by
      calc u = cyclicConjugator u * cyclicReduction u * (cyclicConjugator u)⁻¹ := hconj.symm
        _ = cyclicConjugator u * FreeGroup.of a ^ k * (cyclicConjugator u)⁻¹ := by rw [hwk]
    obtain ⟨β, v, hnpv, hlt, A, B, φ, e, c, htr⟩ :=
      magnus_step_root_of_conj_zpow u l hl a k hk (cyclicConjugator u) hu' hn2
    exact ⟨β, v, hnpv, hlt, A, B, φ, e, c, htr⟩
  · by_cases hcase : ∃ t : α, t ∈ relatorLetters (cyclicReduction u) ∧
        eps t (cyclicReduction u) = 0
    · obtain ⟨t, ht, he⟩ := hcase
      obtain ⟨β, v, hnpv, hlt, A, B, φ, e2, c2, htr⟩ :=
        magnus_step_root_eps_zero (cyclicReduction u) l hl t hnp hcyc ht he
      refine ⟨β, v, hnpv, lt_of_lt_of_le hlt hnorm, A, B, φ, e1.trans e2,
        e2 (PresentedGroup.mk ({cyclicReduction u ^ l} : Set (FreeGroup α))
          (cyclicConjugator u)) * c2, ?_⟩
      rw [MulEquiv.trans_apply, he1]
      have hmul := congrArg (PresentedGroup.mk ({cyclicReduction u ^ l} : Set (FreeGroup α)))
        hconj.symm
      rw [hmul]
      simp only [map_mul, map_inv]
      rw [htr]
      group
    · push_neg at hcase
      obtain ⟨β, v, hnpv, hlt, A, B, φ, e2, c2, htr⟩ :=
        magnus_step_root_no_eps_zero_main (cyclicReduction u) l hl hnp hcyc (by omega) hcase
      refine ⟨β, v, hnpv, lt_of_lt_of_le hlt hnorm, A, B, φ, e1.trans e2,
        e2 (PresentedGroup.mk ({cyclicReduction u ^ l} : Set (FreeGroup α))
          (cyclicConjugator u)) * c2, ?_⟩
      rw [MulEquiv.trans_apply, he1]
      have hmul := congrArg (PresentedGroup.mk ({cyclicReduction u ^ l} : Set (FreeGroup α)))
        hconj.symm
      rw [hmul]
      simp only [map_mul, map_inv]
      rw [htr]
      group

/-! ## Tools for the free-vertex route

The target's norm bound is *presentation dependent*, so it is automatic whenever the vertex group of
the splitting can be presented with a *short* root.  In particular a **free** vertex group of any
rank `r` can be presented as `⟨β | v ^ 1⟩` with `relatorNorm v = 1 < relatorNorm u` (take
`β = γ ⊕ Unit`, `v = of (Sum.inr ())`), and a vertex group `ℤ / l ∗ F_k` can be presented as
`⟨β | v ^ l⟩` with `relatorNorm v = 1` for *every* `l`.  The first ingredient is the Tietze fact
that `⟨β | x ^ 1⟩` is the free group on the remaining generators. -/

/-! ## The `l = 1` free-vertex assembly

The target's second disjunct is *presentation dependent*: it only asks for a one-relator presentation
`⟨β | v ^ l⟩` of the vertex group with `relatorNorm v < relatorNorm u`.  For `l = 1` a **free** vertex
group of any rank is therefore free to use: it can be presented as `⟨β | v ^ 1⟩` with `v` a single
generator and `relatorNorm v = 1`.  Consequently, for `l = 1` the Magnus step follows as soon as
`⟨α | u⟩` is an HNN extension of *some* free group with *some* associated subgroups (this is the
shape in which the `Z`-cover/Magnus tower produces the splitting).  The root tracking is automatic
for `l = 1` (both classes are trivial, `hasMagnusStepAt_one_of_hnn`). -/

/-- **The `l = 1` free-vertex assembly.**  If `⟨α | u⟩` is an HNN extension of a free group (any
rank, any associated subgroups, any identification), then the Magnus step is available at `u` with
`l = 1`, since the free vertex is presentable as `⟨β | v ^ 1⟩` with `relatorNorm v = 1 < 2 ≤
relatorNorm u`. -/
theorem magnusStepAt_one_of_free_vertex {α : Type u} (u : FreeGroup α)
    (hn : 2 ≤ relatorNorm u) {γ : Type u} {A B : Subgroup (FreeGroup γ)} {φ : A ≃* B}
    (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃*
      HNNExtension (FreeGroup γ) A B φ) :
    HasMagnusStepAt u 1 := by
  classical
  -- the free vertex `F γ` presented as `⟨β | v ^ 1⟩` with `β = γ ⊕ Unit`, `v = of (Sum.inr ())`
  obtain ⟨σ₀⟩ := presentedGroup_pow_one_iso_freeGroup (Sum.inr () : γ ⊕ Unit)
  let eγ : {a : γ ⊕ Unit // a ≠ Sum.inr ()} ≃ γ :=
    { toFun := fun a => match a with
        | ⟨Sum.inl y, _⟩ => y
        | ⟨Sum.inr u, h⟩ => (h (congrArg Sum.inr (Subsingleton.elim u ()))).elim
      invFun := fun y => ⟨Sum.inl y, fun h => by cases h⟩
      left_inv := by
        intro a
        obtain ⟨ab, ha⟩ := a
        cases ab with
        | inl y => simp
        | inr u => exact absurd (congrArg Sum.inr (Subsingleton.elim u ())) ha
      right_inv := fun y => rfl }
  let σ : PresentedGroup ({FreeGroup.of (Sum.inr () : γ ⊕ Unit) ^ (1 : ℕ)} :
      Set (FreeGroup (γ ⊕ Unit))) ≃* FreeGroup γ :=
    σ₀.trans (FreeGroup.freeGroupCongr eγ)
  obtain ⟨A', B', φ', E, -, -, -, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv σ.symm A B φ
  refine ⟨γ ⊕ Unit, FreeGroup.of (Sum.inr ()), not_isProperPower_of (Sum.inr ()), ?_,
    A', B', φ', e.trans E, 1, ?_⟩
  · have h1 : relatorNorm (FreeGroup.of (Sum.inr () : γ ⊕ Unit)) = 1 := by
      rw [show FreeGroup.of (Sum.inr () : γ ⊕ Unit) = FreeGroup.of (Sum.inr ()) ^ (1 : ℤ) from
        (zpow_one _).symm, relatorNorm_of_zpow]
      norm_num
    omega
  · have hu1 : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u = 1 :=
      PresentedGroup.one_of_mem (by rw [Set.mem_singleton_iff]; exact (pow_one u).symm)
    have hv1 : PresentedGroup.mk ({FreeGroup.of (Sum.inr () : γ ⊕ Unit) ^ (1 : ℕ)} :
        Set (FreeGroup (γ ⊕ Unit))) (FreeGroup.of (Sum.inr ())) = 1 :=
      PresentedGroup.one_of_mem (by rw [Set.mem_singleton_iff, pow_one])
    rw [hu1, map_one, hv1, map_one]
    group

end Work.OROneRel
