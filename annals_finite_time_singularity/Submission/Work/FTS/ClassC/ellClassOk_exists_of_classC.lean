/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.ellClassOk_exists_of_classC` — the historical audit, and the level-`7` corollary

> **Current state (2026-10-10).** The name `ellClassOk_exists_of_classC` is declared by
> `Submission.Work.FTS.ClassC.A2` (the unconditional level-`8` statement), which this module
> imports.  The file below is the *historical audit* of the earlier route and now ends with the
> **proved** level-`7` corollary `ellClassOk_exists_of_classC_of_decay`.  This module contains
> no `sorry`.

## What the (historical) requested statement is

```
∃ α₀ > 0, ∀ α ∈ (0,α₀], ∀ g, ClassC α g → (decay of g) → (decay of F_*(g)) →
  ∃ Ψ, EllExist.EllClassOk 7 α g Ψ
```

with `EllClassOk 7 α g Ψ = IsBslSol α g Ψ ∧ SmoothOpen Ψ ∧
EllWeakPos α 7 (orthSource g) (shiftSing α g Ψ)`.

## What the audit establishes (and what was missing)

The bulk of this file records the session's audit of the node `PhiStar.bslOp_sol_exists` and of
the honesty frontier; it is kept because it documents *why* the class was raised to level `8`
(lead ruling 2026-10-08 09:50) and why the level-`7` route with the two decay hypotheses was
abandoned.  The mathematics of the audit is unchanged; only the conclusion differs (the level-`8`
statement of `A2` is now the live one).

Everything in the chain from the class `ClassC` to the **elliptic existence node** was already
proved and axiom-clean in the workspace
(`classC_ellInputs`, `tendsto_orthSource_atTop_of`, `Fstar_orthSource_zero`,
`FstarDivOpen.fstar_div_integrable_of_smoothOpen`, `HasDerivAt_L12_of_Fstar_facts`,
`Gsing_contDiffOn_ode_of_Fstar_facts`, `gsing_tendsto_atTop_zero_of_classC`,
`EllExist.ellClassOk_of_bslOp_node`):

* `SmoothOpen (orthSource g)`, `HkMem α 7 (orthSource g)` — `classC_ellInputs` (`reg`, `mem`,
  `fsm`, and `α ≤ 1`);
* the decay of `orthSource g` — `tendsto_orthSource_atTop_of` (the two decay hypotheses);
* `IntegrableOn (F_*(g)(r)/r) (Ioi 0)` — `fstar_div_integrable_of_smoothOpen` (`reg`, `mem`);
* the three `Gsing α g` facts — `HasDerivAt_L12_of_Fstar_facts`,
  `Gsing_contDiffOn_ode_of_Fstar_facts`, `gsing_tendsto_atTop_zero_of_classC`;
* `Fstar (orthSource g) ≡ 0` — `Fstar_orthSource_zero`.

The `node` hypothesis of `ellClassOk_of_bslOp_node 7` — an honest weak solution of
`bslOp α Ψ' = orthSource g` — is the **only** missing ingredient, and it is exactly
`Work.FTS.PhiStar.bslOp_sol_exists` at `k = 7` for the source `orthSource g`:

```
∃ Ψ', EllWeakPos α 7 (orthSource g) Ψ' ∧ IsBslSol α (orthSource g) Ψ'.
```

That node is **unproved** in the workspace: `Submission/Work/FTS/PhiStar/bslOp_sol_exists.lean`
is `:= by sorry` (and the build warns "declaration uses sorry"), so
`Work.FTS.EllExist.ellClassOk_exists_of_inputs` and every statement resting on it carry
`sorryAx`.  Its content is Elgindi §7 (existence for (PolarBSL)) **plus** the finiteness
(honesty) half of Proposition `prop:H2`/`prop:Hk` (`HkMem` of `z²∂_zzΨ`, `∂_θθΨ`), i.e. the two
inputs that `Submission/Work/FTS/PhiStar/NOTES_bslOp_sol_exists.md` records as "an in-one-go
proof is out of reach".  Concretely the workspace is missing:

* the modal weak-solution existence: `Work.FTS.H2.ModalSol.weakSolExists_slice` and
  `Work.EllipticEst.ModalSolution.weakSolExists_slice` do **not** build (10+ errors), and the
  copy consumed by the assembled existence (`Deleg.weakSolExists_slice_fts`) is a bare `sorry`;
* the interior-regularity input: `Deleg.bslOp_interiorSmoothQ0_fts` fails through
  `Deleg.outerCutExists_fts` (Mathlib-API drift), so `Deleg.bslSolExistence_fts` (the assembled
  *existence* of a smooth solution) does not build either;
* the honesty of the solution's second-order quantities, which is the *finiteness* half of
  `prop:Hk`; the workspace's honest estimates (`TT.EllWeak0`, `TT.EllEstUnif k`) all *assume*
  that honesty (`EllWeakPos`), and even the level-`2` estimate `remov.EllEstUnif_two` still
  contains a `sorry`.  (The project's own audit records that the weighted-`ℋ` route was put
  off-route: `Submission/Work/FTS/STARPKG_T2_LEAD.md` §4, `NOTES_PhiStar.md` §3.)

## Contents (state after the de-duplication of 2026-10-10)

* The name `ellClassOk_exists_of_classC` is **not** declared here any more: it denotes
  `A2`'s level-`8` statement (`Submission.Work.FTS.ClassC.A2`), which this module now imports.
  `A2` is the authoritative, unconditional version (`∃ α₀ > 0, ∀ α ≤ α₀, ∀ g, ClassC α g →
  ∃ Ψ, EllClassOk 8 α g Ψ`) and is what the downstream `EllSol` chain consumes.
* `ellClassOk_exists_of_classC_of_decay` — the original level-`7` request **verbatim**, i.e.
  with its two extra decay hypotheses; it is now **proved** here from `A2` by
  `ellClassOk_mono` (8 ⟶ 7), so this module's file carries **no `sorry`**.
* `EllNode7`, `ellClassOk_exists_of_classC_of_node` and `fstar_eq_zero_of_cmode_zero` are kept
  unchanged: the node-conditional form documents the historical route and is used nowhere else.
* (History: the lead's ruling of 2026-10-08 09:50 raised the class to `mem8`/`tr7` and the
  existence node to level `8`.  Before this session both this module and `A2` declared
  `ellClassOk_exists_of_classC`, so they could not be imported together; the duplicate is now
  retired and the two modules *are* co-importable.)

The whole remaining gap of the requested statement is the *node*; for the level-`7` variant that
gap is exactly the honesty of the three second-order slots of the solution, the subject of
`NOTES_node_honesty_frontier.md`.

See `NOTES_ellClassOk_exists_of_classC.md` in this directory for the full audit.

## Session addendum (the crux, and the exact remaining gap)

This session's audit of the node is `NOTES_node_crux.md` in this directory — **read it before
attacking the node**.  Its conclusions:

* every *hypothesis* of `EllNode7` is already discharged for `ClassC` sources (see §0 of the
  note), so the lemma's whole gap is the *conclusion* of the node: the **honesty** (finiteness)
  of the three second-order slots `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ` of the solution;
* that honesty is *not* a bookkeeping consequence of the class (`EllipticEst/propHkWeakOpenFts`
  records two refutations: the weak class admits boundary-singular solutions, and no naive
  approximation of the source has a uniform `ℋ^k` bound), but it is *true* for honest data — the
  honest slots of the solution reproduce the source's marginal rate (note §3);
* the routes, in order of promise: (1) domain-truncated energy identity + monotone convergence
  (**unexplored**, and independent of both refutations), (2) operator regularisation
  `bslOp + εA` + weak compactness, (3) the modal truncation route of `EllExist/Honesty/*`
  (blocked on the uniform bound), (4) the finite-mode/compactly-supported base case.

The brick proved in this file (`fstar_eq_zero_of_cmode_zero`) is the converse of
`Series.eFam_zero_moment` and is what a finite-mode presentation of a source (route 4, and any
`psiTrunc`-based statement) needs in order to *produce* the solvability condition
`F_*F ≡ 0` from its zeroth mode coefficient.

## Session addendum (honest-modal route: what works and what does not)

`NOTES_uniformity_projection.md` (same directory) records the outcome of a session spent on the
`PhiStar/NOTES_bslOp_sol_exists.md` §4.2 route to the honesty of `Ψ = Σ_m a_m e_m`, namely the
eigen-truncation `F_N = Σ_{m≤N} cmode m F·e_m` plus Fatou.  Two negative results:

* the `cos θ dθ`-orthogonal projection onto the first `N+1` modes is **not** uniformly bounded on
  `L²(sin(2θ)^{-σ}dθ)`: numerically `‖P_N‖ ≈ N^{σ/2}` (≈ `N^{0.49}` for `σ = η = 0.99`), so
  `sup_N ‖F_N‖_{ℋ^k}` does not follow from the projection;
* even with a bounded projection it would fail for the honest class, because the mode coefficients
  of a `ClassC` source (endpoint vanishing only `o(sin(2θ)^{α/20})`) decay like `m^{-1-α/20}`,
  far slower than the `m^{-i-3/2}` that the truncated sources need.

The bricks proved in that session (all `sorry`-free, in this directory):

* `SliceIbp.lean` — the vocabulary `lift1`, `LzeroS` (= `-∂_θθ + ∂_θ(tan θ·) - 6` on a slice),
  `LzeroSIter`, `SliceBdry` (the Wronskian boundary datum `cos θ(f' e_m - f e_m') → 0`), and
  `LzeroS_eFam`/`lam_ne_zero`;
* `slice_ibp_eFam.lean` (+ `slice_ibp_generic`, `hasDerivAt_wronskian_LzeroS`) — the one-step
  self-adjointness identity `∫ f e_m cos = λ_m^{-1} ∫ (LzeroS f) e_m cos`;
* `slice_moment_iterate.lean` — its `K`-fold iterate;
* `sliceBdry_of_endpoint_vanish.lean` — the `BdryTraces`-type endpoint vanishing gives `SliceBdry`;
* `gram_eFam_rpow.lean` — the exact form of the weighted Gram entry,
  `∫ e_m e_n sin(2θ)^{-σ} = 2^{-σ-1}∫_0^1 v^a(1-v)^a h_m h_n dv`, `a = (1-σ)/2`,
  `h_m(v) = gC(2m+1)(√v)/√v` (the Jacobi frame in which the uniformity question above is decided);
* `ellWeakPos_psiTrunc_of_cmode.lean` — the honest-truncation interface: per-mode coefficient data
  ⇒ `EllWeakPos α k F_N Ψ_N`.

## Session addendum (the moment conjunct `F_*(Ψ) ≡ 0` of the node)

The elliptic existence node (`EllNode7` below) has, besides the existence and the honesty, a
**moment conjunct**: `F_*(Ψ) ≡ 0` (`F_*(f)(z) = ∫_θ f(z,θ) sinθcos²θ dθ`).  That conjunct is now
*proved* modulo explicit, named hypotheses, in this directory — see
`NOTES_moment_conjunct.md` for the full account:

* `euler_ode_unique.lean` — `euler_ode_eq_zero_of_decay_of_bdd`,
  `euler_ode_eq_zero_of_decay_of_zsq`: the classical rigidity for
  `α²z²u'' + α(5+α)zu' = 0` (decay at `+∞` + a `z = 0` bound ⟹ `u ≡ 0`);
* `Fstar_bslOp_moment.lean` — the moment identity
  `F_*(bslOp α Ψ) z = -(α²z²)·F_*(∂_zzΨ)z - α(5+α)z·F_*(∂_zΨ)z`;
* `Fstar_chain_pz.lean` — the chain rule `F_*f(z) - F_*f(s) = ∫_s^z F_*(∂_zf)`;
* `euler_weak_eq_zero_of_decay.lean` — the integrated rigidity;
* `Fstar_eq_zero_of_bslOp.lean` — **`Fstar_eq_zero_of_bslOp`**, the assembly: for a solution of
  `bslOp α Ψ = F` with `F_*F ≡ 0` and the honest memberships of `z²∂_zzΨ`, `D_zΨ`, `Ψ`, `∂_zΨ`
  (plus the closed-`θ`-interval `C²` regularity of the slices, `u → 0` at `+∞` and
  `z²u → 0` at `0`), the moment `F_*Ψ` vanishes identically.

## Session addendum (the level-`0` modal estimate for the honesty)

The honesty input of the node (`HkMem α 7` of `z²∂_zzΨ`, `∂_θθΨ`, `z∂_z∂_θθΨ`) is attacked
through its level-`0` entry point.  The session's product is the level-`0` estimate for the
*finite mode sums* of the modal solution, `Ψ_N = Σ_{m≤N} a_m e_m`:

  `HkSq α 0 Ψ_N ≤ 9(∫_θ σ)·(Σ_{m≤N}(m+1)‖a_m w‖)²`   (`ModeSumZ.HkSq_zero_modeSum_le`),

together with the per-mode input `μ_m‖a_m w‖ ≤ ‖c_m w‖`
(`ModeEnergyCS.modeWeightedEnergy_norm`, `μ_m = λ_m − 3α² − 3α(5+α)/2`), the angular quadratic-form
bound `angGram_modeSum`, the radial finite-sum Minkowski `weighted_l2_modeSum`, and the
Bessel/Plancherel bound `bessel_cmode` on the source.  See `NOTES_mode_sum_level0.md` for the
route, the corrected convergence criterion (`Σ_m m^{-3}`, *not* `Σ_m G'_{mm}/λ_m`), and the
precise reason why the two negative results of `NOTES_uniformity_projection.md` do **not** apply.

The same route gives the *pure `z`-slots* at every level; the **mixed slots** (`D_θ^i`, `i ≥ 1`,
weight `sin(2θ)^{-γ}` with `γ > 1`) remain out of reach of a modal argument (the relevant
diagonal is `≍ m^{2i+2}`), so they need the operator/σ-Gram route — see §4 of the note.

## Session addendum (the level-`0` honest estimate — COMPLETE)

The level-`0` entry point of that route is now closed: the modal solution `Ψ = psiSeries α F` has
finite `σ`-weighted `L²`-mass, controlled by the source,

  `∫⁻_z ∫⁻_θ ofReal (Ψ² w² σ) ≤ ofReal (72 · (∫θ σ) · HkSq α 0 F)`   (`0 < α ≤ 1/4`),

proved as `Work.FTS.ClassC.lintegral_psiSeries_le_concrete`
(`Submission/Work/FTS/ClassC/level0_psiSeries_concrete.lean`, `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]`), from the per-mode bounds
`μ_m‖a_m w‖ ≤ ‖√(eNorm_m)·c_m w‖`, the angular/radial mode-sum bounds, Bessel's inequality
integrated in `z` (`bessel_z.lean`) and Fatou in the truncation index.  This is an `ENNReal`
(lintegral) statement, hence not junk-vacuous.  The per-mode hypotheses are *not* derivable from
the honest class alone (they encode the fine `z`-rate of the mode coefficients); see
`NOTES_level0_complete.md` for the brick table, the caveats, and the route to the pure-`z` slots
(the radial operator is `α²D_z² + 5αD_z`, a polynomial in `D_z = z∂_z`, hence commutes with
`D_z`).

## Session addendum (the honest level-`0` layer is now COMPLETE and `sorry`-free)

This session repaired the honest level-`0` layer of `prop:H2` end to end.  All of it lives in
`Submission/Work/FTS/ClassC/HonW2Fix/`, with the proofs and the consumption rules in
`HonW2Fix/NOTES_HonW2Fix.md`; nothing in this file's statements changed and `EllNode7` remains the
single gap.

**Closed here, all axiom-clean** (`#print axioms = [propext, Classical.choice, Quot.sound]`), each
by *citing an already-proved sibling* rather than by new analysis:

* `Honest.I1LowerHonest` — the `I₁` lower bound of Step 2 — is `Final.honI1Lower_of_mixedHon`
  applied with its two extra hypotheses discharged by `Hon.memMix1`, `Hon.memMix2` (`Hon` has
  carried them since the last `EllWeakPos` extension).  Consequently `Honest.step2Angular`
  (Step 2) and `Honest.step3Angle` (Step 3) become `sorry`-free; with the already-clean
  `Honest.step1FirstOrder`, the level-`0` *estimates* of `prop:H2` are complete.
* `Honest.HonW2PthBoundYc` (`w²`-weighted first-order bound on `∂_θΨ`, `C = 14`) — its stand-in
  `YcEnergyStandIn` is *verbatim* `Honest.Step1G.EnergyG`, which is proved; hence
  `Honest.HonPsiRhoBnd` (`‖Ψ‖_ρ ≤ C‖F‖_ρ`), whose own `honW2PthBoundInput` is exactly that bound.
* `Honest.sliceSecondSqLe` (the 1-D `L²(σ)` coercivity of `Lzero1`) — from
  `Final.slot20A_secondDeriv_bochner` + `Final.slot20A_lintPassage` plus the null-set comparison
  `Ioo 0 (π/2) =ᵐ Icc 0 (π/2)`.
* `Honest.Trunc.deriv_phiWsq`, `Honest.Trunc.deriv_deriv_phiWsqSq` — verbatim re-exports of
  `ClassC.HonestCut.ThetaOpen.derivPhiWsq` / `derivDerivPhiWsqSq`, already proved.

**A false leaf found and repaired.**  `Honest.Trunc.PerThetaRadialIbp` (the per-`θ` radial
integration by parts used by the `RadialIbpHon`/`HonW2EnergyYc` chain) is **FALSE as stated**: it
omits the boundary term `(1/2)G'(0⁺)f(0⁺)²` at `z = 0⁺` (`G = φ w² z²`), which
`hsupp : ∀ z ≤ 0, φ z = 0` does not kill (take `φ ≈ z³` and `Ψ z θ = e^{-z}g(θ)`).  Explicit
counterexample, the corrected statement (add `h0 : ∃ r > 0, ∀ z ∈ [0,r), φ z = 0`, satisfied by
the intended cut `Work.FTS.EllipticEst.cut n`), and the propagation obligation are in
`HonW2Fix/NOTES_HonW2Fix.md` §3; the corrected lemma is being proved as
`Work.FTS.ClassC.HonW2Fix.PerThetaRadialIbp_fix`.

**Two stale-API build breaks** still make parts of the wider honest cone unreachable by `import`:
`Honest/HonThetaZeroLimitAeYc.lean:78` (`TT.EllWeakPos` gained a fourth honesty field; append
`h.memMix2`) and `Honest/Trunc/HonRadialJointIntegrable.lean:47` (a `linarith` missing
`le_max_right r 0`).  Neither is in this file's cone.

**What remains for the node.**  Level `0` is no longer the bottleneck: the gap is the *raise*
`0 → 7` and the level-`0` *finiteness* for the modal solution, i.e. `ClassC/HonestCut/`, whose open
modules are `H2W.AeMixedAeMem`, `AeColl.limitBound`, `AeColl.pairChain`, `AeI1Fts.I1WMOuter`,
`AeI1Fts.Upsi_A_integrable`, `AeI1Fts.radial_identity`, `H2W.ShiftC.psiLzeroBox`,
`RPFresh.MixedAGN_finite`.

## Session addendum (the honesty frontier of the node, sharpened)

Full write-up: `NOTES_node_honesty_frontier.md` (same directory).  Summary:

* The node's honesty is *exactly* the rectangle of level-`0` honesties
  `∀ j m ≤ 9, HkMem α 0 (DzIter j (pthIter m Ψ))` plus the trivial-slave identities:
  **`Work.FTS.ClassC.HkMem_seven_slots_of_plain_family`** (proved, axiom-clean,
  `Submission/Work/FTS/ClassC/HkMem_seven_slots_of_plain_family.lean`) turns
  `∀ j m, j ≤ 9 → m ≤ 9 → HkMem α 0 (DzIter j (pthIter m Ψ))` into the three `HkMem α 7`
  conclusions of `TT.EllWeakPos` (via `HkMem_of_plain_slots`, `z²∂_z² = D_z² - D_z`, and the
  `∂_θ`–`D_z` commutation).  The rectangle is tight (the largest index reached is exactly 9).
* The mixed part of the `ℋ^k`-integrand needs only **vanishing** angular weights:
  **`Work.FTS.ClassC.mixedSlot_vanishing_weight_domination`** (proved, axiom-clean): the
  un-weakened form of the landed `plainSlot_domination`,
  `(D_z^j D_θ^i f · Wt)² ≤ C Σ_{1≤r≤i} (D_z^j ∂_θ^r f)² w² sin(2θ)^{2r-γ}`.
* **`Work.FTS.ClassC.HkMem_of_pure_and_vanishing`** (proved, axiom-clean) is the corresponding
  reduction: `f ∈ ℋ^k` follows from the σ-weighted pure-`z` slots `D_z^i f` (`i ≤ k`) together
  with the plain angular slots `D_z^j ∂_θ^r f` against the *vanishing* weight
  `w² sin(2θ)^{2r-γ}` only.  Hence the σ-weight `sin(2θ)^{-η}` is needed only for the pure-`z`
  slots, i.e. for θ-orders ≤ 2 — every θ-order ≥ 3 requirement is a vanishing-weight statement.
  The node-level instance of this sharpening is
  **`Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family`** (proved, axiom-clean): the three
  `HkMem α 7` conclusions of `TT.EllWeakPos` follow from the σ-slots `∀ l ≤ 9, m ≤ 2,
  HkMem α 0 (DzIter l (pthIter m Ψ))` together with the *vanishing*-weight angular slots
  `∫∫(DzIter l (pthIter t Ψ))² w² sin(2θ)^{2t-4-γ} < ∞` for `3 ≤ t ≤ 9`, `l ≤ 9`.
  A *sufficient* route to that hypothesis is landed too
  (**`Work.FTS.ClassC.vig_integrableOn_of_slice_majorant`**): a pointwise-in-θ majorant
  `|DzIter l (pthIter t Ψ) z θ · w z| ≤ g z` with `g ∈ L²(Iz)` gives both conjuncts of `hV`
  (the angular weight `sin(2θ)^{2t-4-γ}` is integrable at the endpoints, so only *local
  boundedness* of the slices is needed) — the shape the tree's Agmon-type slice bounds produce.
* Consequently the remaining chapter is the *vanishing-weight* angular slots
  `∫∫(D_z^l ∂_θ^t Ψ)² w² sin(2θ)^{2t-4-γ} < ∞` for `3 ≤ t ≤ 9` (`l ≤ 9`), the θ-orders ≤ 2
  coming from the box route.  See §2.1/§4 of the notes for the exact index ranges.
* **Negative result (recorded so it is not re-attempted):** the mode / `psiSeries` lane *cannot*
  produce the angular orders `m ≥ 3`.  The only available mode bound is the triangle inequality in
  `m`, where `sup_θ |∂_θ^m e_m| ≍ m^{2m+2}` against the polynomial coefficient decay
  `a_m = O(m^{-2q-3})` (`q ≤ 3` from `HkMem α 7 F`), so it diverges like `m^{4m}`.  The truth at
  `m ≥ 3` is a *cancellation* statement, i.e. the energy method.  Likewise the plain-`∂_θ`
  induction, the slice-coercivity-at-`D_θ^m` idea (the top term cancels between the two sides; no
  strict gap, ratio `→ 1` on the eigenfunctions), and iterated Hardy all fail for the same reason.
* The structural input the truncated step needs is `Lzero (D_θ^m Ψ) = Σ_{k≤m+2} c_{m,k}(θ) ∂_θ^k Ψ`
  with **bounded** `c` and top coefficient `c_{m,m+2} = -(sin 2θ)^m` (the landed
  `AeMom.Lzero_DthIter_one` is `m = 1`), which is exactly the `sin`-bookkeeping under which the
  weights above are the natural ones.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.classC_ellInputs
import Submission.Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.sum_bmode_eFam_eq
import Submission.Work.FTS.ClassC.A4
import Submission.Work.FTS.ClassC.A2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval BigOperators

namespace Work.FTS.ClassC

open MeasureTheory

/-! ## The `m = 0` coefficient of the source *is* the angular moment

`Series.eFam_zero_moment` proves `F_*F z = 0 → cmode 0 F z = 0`.  The converse is what a
*finite-mode* presentation of a source needs (it is how such a source produces the solvability
condition `F_*F ≡ 0` of `(PolarBSL)`), and it is unconditional: the Bochner integral is a total
function, so the chain only uses pointwise rewrites and the null-set comparison `Icc`/`Ioc`.
-/

/-- **The converse of `Series.eFam_zero_moment`.**  If the zeroth mode coefficient of the source
vanishes, then so does the angular moment `F_*F`. -/
theorem fstar_eq_zero_of_cmode_zero (F : ℝ → ℝ → ℝ) (z : ℝ)
    (h : Work.FTS.PhiStar.Series.cmode 0 F z = 0) : Work.Elliptic.Fstar F z = 0 := by
  have hpoint : ∀ θ : ℝ,
      F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ
        = 3 * (F z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [Work.FTS.PhiStar.Series.eFam_zero_apply]
    simp only [Work.Elliptic.sinCos2]
    ring
  have hN : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      (Work.FTS.PhiStar.Gegenbauer.eFam 0 θ) ^ 2 * Real.cos θ) ≠ 0 := by
    rw [← Work.FTS.PhiStar.Series.iota_eq_interval]
    exact ne_of_gt (Work.FTS.PhiStar.Series.eFam_norm_pos 0)
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
      = 3 * Work.Elliptic.Fstar F z := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpoint θ)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp only [Work.Elliptic.Fstar, Work.Spaces.Iθ]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
  have hmul : Work.FTS.PhiStar.Series.cmode 0 F z *
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Work.FTS.PhiStar.Gegenbauer.eFam 0 θ) ^ 2 * Real.cos θ)
      = 3 * Work.Elliptic.Fstar F z := by
    rw [Work.FTS.PhiStar.Series.cmode, div_mul_cancel₀ _ hN, hnum]
  rw [h, zero_mul] at hmul
  linarith

/-- **The elliptic existence node** (`Work.FTS.PhiStar.bslOp_sol_exists` at `k = 7`), as the
hypothesis under which the requested statement is provable: for every source `F` with vanishing
angular moment, `C^∞` on the open quadrant, honestly in `ℋ⁷` and decaying in `z`, there is a
solution of `bslOp α Ψ' = F` in the weak class `EllWeakPos α 7 F`. -/
def EllNode7 : Prop :=
  ∀ (α : ℝ) (F : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 7 F →
    (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
    ∃ Ψ' : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.TT.EllWeakPos α 7 F Ψ' ∧ Work.Elliptic.IsBslSol α F Ψ'

/-- **The requested statement, from the elliptic existence node.**  The class `ClassC` supplies
every input of the level-`7` existence node for the orthogonalised source `orthSource g`; the
assembly is `Work.FTS.EllExist.ellClassOk_of_bslOp_node 7`.

This is the exact form in which the requested lemma is available in the current workspace: the
only gap between it and the requested statement is `EllNode7`, whose proof is
`Work.FTS.PhiStar.bslOp_sol_exists` (a `sorry` in the workspace) plus the ClassC input adapters
already proved. -/
theorem ellClassOk_exists_of_classC_of_node (hNode : EllNode7) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g →
      (∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0)) →
      Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0) →
      ∃ Ψ : Work.FTS.Galerkin.Fn, Work.FTS.EllExist.EllClassOk 7 α g Ψ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 g hg hdec hFdec
  have hα1 : α ≤ 1 := by linarith
  -- the two class inputs for the orthogonalised source
  obtain ⟨hSm, hHk⟩ := Work.FTS.ClassC.classC_ellInputs (g := g) hα hα1 hg hFdec
  -- its decay
  have hDec : ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Elliptic.orthSource g z θ) Filter.atTop (nhds 0) :=
    Work.FTS.EllExist.tendsto_orthSource_atTop_of hdec hFdec
  -- the three `Gsing α g` facts
  have hFint : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hg.reg hg.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hg.fsm hFint
  obtain ⟨hGsm, hGode⟩ :=
    Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts α g hα hg.fsm hFint hL12
  -- the assembly
  exact Work.FTS.EllExist.ellClassOk_of_bslOp_node 7
    (hNode α (Work.Elliptic.orthSource g) hα hα4 hSm hHk
      (fun z _ => Work.FTS.EllExist.Fstar_orthSource_zero g z) hDec)
    hGsm hGode
    (Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC hα hg.reg hg.mem)

/-- **The repaired elliptic existence node at level `8`** (lead install 2026-10-11,
`cbc/fts_phistar_REVIEW.md`): the statement of `Work.FTS.PhiStar.bslOp_sol_exists_pp 8`.
`EllNode7` above (= the original node at `k = 7`) is false; the repair assumes two more orders
of the source, `HkMem α 10 F`, and concludes `EllWeakPos α 8`.  The ClassCHon route's target is
`ClassCHon.EllNode8pp_holds : EllNode8pp` (`ClassCHon/EllNode8pp.lean`). -/
def EllNode8pp : Prop :=
  ∀ (α : ℝ) (F : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 10 F →
    (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
    ∃ Ψ' : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.TT.EllWeakPos α 8 F Ψ' ∧ Work.Elliptic.IsBslSol α F Ψ'

/-- **A2 from the repaired node** (`EllNode8pp`): every `ClassC` profile has a stream function
in `EllClassOk 8`.  Same assembly as `A2`, with the node as a hypothesis. -/
theorem ellClassOk_exists_of_classC_of_node8pp (hNode : EllNode8pp) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g →
      ∃ Ψ : Work.FTS.Galerkin.Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 g hg
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hSm, hHk, hDec, hFsm, hFint⟩ := Work.FTS.ClassC.classC_ellInputs_full hα hα1 hg
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  obtain ⟨hGsm, hGode⟩ :=
    Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts α g hα hFsm hFint hL12
  exact Work.FTS.EllExist.ellClassOk_of_bslOp_node 8
    (hNode α (Work.Elliptic.orthSource g) hα hα4 hSm hHk
      (fun z _ => Work.FTS.EllExist.Fstar_orthSource_zero g z) hDec)
    hGsm hGode
    (Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC hα hg.reg hg.mem)

/-- **The original level-`7` request, verbatim** — with its two extra decay hypotheses.

Before the de-duplication of 2026-10-10 this was the (unproved) declaration
`ellClassOk_exists_of_classC`; that name is now `A2`'s level-`8` statement, which this module
imports.  Here the level-`7` form is *derived* from it by monotonicity `ellClassOk_mono`
(`EllClassOk 8 α g Ψ → EllClassOk 7 α g Ψ`), so the two decay hypotheses are simply discarded.
In particular this module contains no `sorry`. -/
theorem ellClassOk_exists_of_classC_of_decay :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g →
      (∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0)) →
      Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0) →
      ∃ Ψ : Work.FTS.Galerkin.Fn, Work.FTS.EllExist.EllClassOk 7 α g Ψ := by
  obtain ⟨α₀, hα₀, hmain⟩ := Work.FTS.ClassC.ellClassOk_exists_of_classC
  exact ⟨α₀, hα₀, fun α hα hαα₀ g hg _ _ =>
    (hmain α hα hαα₀ g hg).imp fun Ψ hΨ =>
      Work.FTS.ClassC.ellClassOk_mono (by norm_num : 7 ≤ 8) hΨ⟩

end Work.FTS.ClassC
