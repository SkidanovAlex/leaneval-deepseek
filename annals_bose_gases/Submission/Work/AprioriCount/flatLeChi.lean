import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.AprioriCount.Defs
import Submission.Work.BoseFixB1S.kinFormB_ge_gapColumn_smooth
import Submission.Work.BoseFixR.BoxWordLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.flatLeChi` — the "flat part is visible" interface

The target is `Work.AprioriCount.FlatLeChi` (statement frozen, see below): for every low box
state, the flat count `cS1` is dominated by the χ-mass `chiCount`, with a **fixed** constant.

**Verdict and reduction** (see `FINDING_flatLeChi.md` for the full analysis): the statement is
*true*, but it is **not** an elementary interface: it is equivalent — up to the additive
diluteness gain `X³ = (μa³)^{3/323}` — to the a-priori count window `n ≤ C μ ℓ³`
(`NodeB1B` / `LowStateCountCapB1` / `BoseFixB1B.lowCountBound`), i.e. to FS
`thm:aprioriHLambda`, the chapter's standing central residual.  Concretely:

* the count window **implies** the target in two lines (`cS1 ≤ n·‖Φ‖²` plus the Θ-term of
  `IsLowB` together with the chemical-mass bound `M₁ ≤ K₀·chiCount`, giving
  `chiCount ≥ μℓ³(1−j)/(4chiSup)`);
* every route from the *proved* corpus pieces (the window-free sharp chain
  `Work.BoseBox.q3potChainNoWin`, the gap column, the exact `q0`-value identity
  `Submission.BoseGases.q0word_w2_mass_sub`, the Cauchy–Schwarz pairing bound
  `Work.SmallBoxA0.q4PairWord_cs_bound`) loses **exactly** the factor `X³`; the only missing
  input is the *sharp kinetic budget* `kinFormB ≲ 4π(a v)μ²ℓ³·j`, which is what the window /
  the Bogoliubov port supply.

The helper lemmas below are the ones this file can contribute on its own; the delegated brick
`Submission.Work.AprioriCount.fibMass_le_chiCount` supplies the chemical-mass bound.

**SESSION 4 UPDATE (the current, sharpest reduction).**  `Submission.Work.AprioriCount.flatLeChiResiduals`
reduces the target to FS's **two** residuals, with every intermediate step proved and axiom-clean:

    FlatLeChi v h R  ⟸  Work.BoseFixB1B.FlatBranchMaxFree v h R  +  Work.BoseFixB1B.TrimLowMax v h
                        (`flatLeChi_of_flatBranchMaxFree_and_trim`),

via `AprioriUnif` (`flatLeChi_of_aprioriUnif`, using only its `n₊`-window conjunct).  The two
spellings `flatLeChi_of_flatBranchLowMax_and_trim` (frozen `c₁ = 1/4`) and
`flatLeChi_of_flatBranchMaxFree_and_crudeLower` (`TrimLowMax ⟸ CrudeLower`) are recorded there too.
See `FINDING_flatLeChi_session4.md` for why `CrudeLower` (unrestricted pointwise) must **not** be
used as the crude spelling: it is false (the `τ → 0` corner family, session 3 §15).

**SESSION 5 UPDATE (the Dyson gate).**  `Submission.Work.AprioriCount.flatDyson` reduces the node to
a **single, Dyson-flavoured** pair-rigidity residual:

    FlatLeChi v h R   ⟸   Work.AprioriCount.FlatDyson v h R
                          (`Work.AprioriCount.flatLeChi_of_flatDyson`),

where `FlatDyson` is the **flat-count Dyson bound** `c·(a v)·(cS1 ℓ Φ)² ≤ (kinFormB + pairPartB)·ℓ³·‖Φ‖²`
on low states (`2 ≤ n`).  The proof uses *only* proved lemmas and is *arithmetic*: lowness pins the
χ-mass from below (`lowStateChiCountGe`) and `k+p` from above (`boxBudget` + the chemical-mass law),
and `FlatDyson` turns the flat count into `k+p`, so the two pins meet.  No count window, no
`FlatBranchMaxFree`, no `TrimLowMax`, no `ChiDysonBound` is used — the whole content of the node
moves into `FlatDyson`.

The same file also proves:
* `Work.AprioriCount.flatDyson_of_crudeDyson` — the crude Dyson bound `(E)` (the hypothesis of the
  PROVED `dysonChiBound_of_crudeDyson`) implies `FlatDyson`, via `cS1 ≤ n‖Φ‖²`;
* `Work.AprioriCount.flatDyson_of_flatLeChi_chiDyson` — the converse given the corpus's χ-side
  `ChiDysonBound`, so modulo `ChiDysonBound` the node and `FlatDyson` are *equivalent*;
* **`Work.AprioriCount.countWindow_of_crudeDyson`** — the chapter's a-priori **count window**
  (FS `thm:aprioriHLambda`) from the **single** residual `(E)` = `Work.AprioriCount.CrudeDyson`,
  composing `dysonChiBound_of_crudeDyson` + `chemMassLeChiMass_holds` + the gate above +
  `cubeCountWindow_of_inputs`.  Nothing from the `thm:smallbox` chapter is used.

In other words the chapter's central node is now, on disk, `(E) ⟹ count window` — and my node is
the flat-side half of that implication.

**SESSION 6 UPDATE (the mean-field identity and the condensed count window).**
`Submission.Work.AprioriCount.condensedWindow` (`FINDING_flatLeChi_session6.md`) proves

* `Work.AprioriCount.eight_pi_a_le_integral_v` — **`8π(a v) ≤ ∫v`**, which together with the
  corpus's box identities `W_g = ℓ³∫g₀ = 8π(a v)ℓ³`, `W_v = ℓ³∫v` gives the *mean-field identity*
  `(μW_g)²/(2W_v) ≤ 4π(a v)μ²ℓ³ = Λ₀` (equality iff `∫v = 8πa`, the weak-potential endpoint).
  This is why the crude budget's slack is *exactly* `Λ₀·j` and why the corner/correlation-hole
  families cannot violate this node: the pair term is quadratic in the χ-visible count while the
  chemical gain (`M₁`) is linear, so `μM₁ − 𝔓 ≤ Λ₀`;
* **`Work.AprioriCount.countWindow_boxConstant`** — the chapter's a-priori count cap
  (FS `thm:aprioriHLambda`) in the **exactly condensed** class (`boxQInd` vanishing in every slot):
  `(n : ℝ) ≤ 2·μ·ℓ³ + 1` on low states.  The *whole* difficulty of the general count window is
  therefore in the correlated/hole part (the pair marginal below the product of the marginals),
  which is paid only by the kinetic row.

Two helper bricks are delegated (reviewed, `wLoc_box_integral_eq`, `wLoc_box_integrable`) to
discharge the two kernel hypotheses carried by `countWindow_boxConstant`.  This session does **not**
change this file's statement or its residual set (the four gates above are unchanged).

**SESSION 7 UPDATE (the weakest gate, and the flat-count reading of the node).**
`Submission.Work.AprioriCount.flatCountWindow` (`FINDING_flatCountWindow.md`) adds two gates, both
proved and axiom-clean:

* **`Work.AprioriCount.flatLeChi_of_flatWindow`** — the node from the **flat**-count cap alone:

      FlatWindow v h R  :=  cS1 ℓ Φ ≤ C·μℓ³·‖Φ‖²   on low states
      ⟹  FlatLeChi v h R   (κ = c₁(a v)/(4C), the χ-mass floor `lowStateChiCountGe`),

  i.e. the node bounds the *flat* (slice-mean) count only, and the excited count may be arbitrarily
  large — `FlatWindow` is **strictly weaker than every other gate on this file's list**
  (`cS1 ≤ n‖Φ‖²`);
* **`Work.AprioriCount.flatWindow_of_weakMF`** — `WeakMF` (the crude mean-field pair bound with a
  *free* kinetic coefficient and the bare coupling `∫v`, equivalent to the corpus's `CrudeDyson`
  `(E)`) **implies `FlatWindow`** by elementary arithmetic alone (`boxBudget` +
  `fibMass_le_chiCount` + `visCount_le_chiSup_mul` + the `J`-window + `μℓ³ ≥ 1`), hence
  **`Work.AprioriCount.flatLeChi_of_weakMF` : `WeakMF ⟹ FlatLeChi`**.  That route uses neither
  `FlatDyson`, `ChiDysonBound`, nor the per-box chapter.

`Submission.Work.AprioriCount.visibilityGate` records the **cleanest form of the residual** (the
"no-hiding" statement of `FINDING_flatCountWindow.md` §0bis and §2(d)):

      ChiVisibility v h R  :=  c·n·‖Φ‖² ≤ chiCount ℓ Φ   on low states
      ⟹  ExcitedLeChi ⟹ FlatLeChi   (`flatLeChi_of_chiVisibility`),

with the converse `ExcitedLeChi ⟹ ChiVisibility` — i.e. the node's whole analytic content is
*"the mass of a low state cannot hide where `χ` is small"*, the quantitative form of FS's Appendix
step (P-d).  The count cap implies it (`chiVisibility_of_countCap`), so it is not a strengthening.

**SESSION 9 UPDATE (the localised branch is trivial; the decisive input is the state-level
mean-field sharpness).**  `Submission.Work.AprioriCount.visibilityLocalised`
(`FINDING_flatLeChi_session9.md`) proves, sorry-free and axiom-clean,

* `Work.AprioriCount.two_mul_chiCount_ge_of_plateau` and
  `Work.AprioriCount.mul_chiCount_ge_of_ballLocalised` — the **ball-localised branch of
  `ChiVisibility`**, by the *pointwise* bound `Σᵢχ_ℓ(xᵢ) ≥ n/2` on the support: no kinetic input,
  no budget, no lowness.  Hence the localisation-to-kinetic lane
  (`kinFormB_ge_clusterKin` + `mul_chiCount_ge_of_kin`) cannot contribute to `ChiVisibility` — where
  its hypotheses hold the conclusion is trivial, and where the conclusion is non-trivial (`χ` small
  on the localising ball) they fail.

`FINDING_flatLeChi_session9.md` also records two traps (in this Mathlib `ContDiff ℝ ⊤` is
*analytic*, not smooth — `slotGrad_windowed_ge`, `dysonKinRow`, `kinFormB_ge_clusterKin` are
inapplicable resp. vacuous as stated; and the whole box word is `χ`-windowed, so corner mass pays
only the *gap* word) and re-derives the node's mechanism with constants: lowness (the LHY payment)
forces the `χ`-visible mass into `n_vis ∈ [0.83, 2.4]·μℓ³` and the sharp budget forces the hidden
mass to `n_hid ≤ 400μℓ³(μa³)^{0.435}`, after which the node's arithmetic closes with a *fixed* `κ`.
The decisive missing input is therefore the state-level mean-field sharpness
`μM₁ − pairPartB ≤ 4π(a v)μ²ℓ³(1+o(1))‖Φ‖²` (session 6's mean-field identity at the state level),
not the crude Dyson bound `(E)`.

**SESSION 12 UPDATE (the audited chain, and the χ²-ledger's cap).**  See
`FINDING_flatLeChi_session12.md`.  Every arrow of the chain

    FlatLeChi ⟸ CountWindow ⟸ CountWindowUnifAllJ ⟸ AprioriUnif
              ⟸ CollectedUnifCube (+ `SlidingBCube`) ⟸ CubePerBox

is a **proved, axiom-clean** corpus theorem
(`flatLeChi_of_countWindow`, `lowStateCountCap_of_countWindowUnif`,
`countWindowUnif_of_aprioriUnif`, `aprioriUnifOfCollectedUnifCube`, `SlidingBCube_holds`,
`collectedUnifCube_of_cubePerBox`); the **single** gap of the node is therefore the dense band arm
`Work.BoseB1Cube.CubeBandArmDensePos`, the one `sorry` of `cubePerBox_holds.lean`.  Note also that
the node consumes **only the second conjunct** of `AprioriUnif` (the `n₊`-window), and that — by
`isLowB_mono`, `IsLowB (J) ⟹ IsLowB (J')` for `J ≤ J'` — the `J`-uniform spellings are
*equivalent* to the `J`-indexed ones at any fixed `J₀ ≥ lhyC`, so no separate `J`-uniformity
obligation exists.

New machinery landed with this session (for the χ²-currency route of
`FINDING_dysonChiSqSplit.md`): `AprioriCount/chiSqSplitDefs.lean` (`chiSqClump`, `chiSqHole`),
the delegated exact partition `chiSqMass_split`, and the cap
**`Work.AprioriCount.chiSqMass_le_cap`** — the χ²-mass paid by the Dyson row, the packing term and
the pair row, with the **δ-term** `δ·chiSup·barePairSum` as the single uncontrolled term.  That
δ-term is exactly the ball/cube mismatch (the corpus's `chi` is `chiBump`, a *ball* bump with
`rOut = 1/2`, so the cube's corner shell has `χ_ℓ ≡ 0`); it vanishes identically at a
**cube-supported plateau bump** (`Work.BoseFixB1B.chiCubeBump`), which is the fleet's repair in
flight.

**SESSION 15 UPDATE (the exact χ-decomposition, the optimal band, and the χ²-window gate).**
Three new proved, axiom-clean modules sharpen the node's *own* side; the frontier is unchanged.

1. `AprioriCount/chiQmassDefs.lean` + the delegated `chiQmassDecomp` and `chiQmassCross` give the
   **exact** decomposition of the χ-mass (since `Φ = PᵢΦ + QᵢΦ` *pointwise* and `PᵢΦ` is constant
   in the `i`-th coordinate),

       chiCount ℓ Φ = aChi ℓ · cS1 ℓ Φ + chiQmass ℓ Φ + 2·chiCross ℓ Φ ,
       |chiCross ℓ Φ| ≤ √(aChi ℓ · cS1 ℓ Φ · chiQmass ℓ Φ) ,

   with `aChi ℓ` the mean of `χ_ℓ` over the cube and `chiQmass` the χ-mass of the excited part.
   Hence (`flatLeChiChiQWindow.lean`, `chiCount_ge_sqrt`)

       (√(aChi ℓ · cS1 ℓ Φ) − √(chiQmass ℓ Φ))²  ≤  chiCount ℓ Φ .

   The bound is **attained** — a state whose support avoids the window has `chiQmass = aChi·cS1`,
   `chiCross = −aChi·cS1`, `chiCount = 0` — so it is the sharpest elementary statement about the
   node, and it shows that the node fails exactly when the *excited* χ-mass is of the size of the
   flat one.
2. `AprioriCount/bandOptimal.lean` gives the **optimal band threshold**: the admissible `(T, κ)`
   region is `κ + C·T/(1−T) ≤ A/2` (`cS1_le_chiCount_of_bandAt`,
   `cS1_le_chiCount_of_band_kappa`), i.e. `T → A/(2C + A)` as `κ → 0` — a factor `2` above session
   14's frozen `A/(4C + A)`; the `∃`-form is `flatLeChi_bandOptimal`
   (`T₀ = min(1/8, 3A/(8C + 3A))`, `κ = A/8`).
3. `AprioriCount/flatLeChiChiQWindow.lean` proves the **strictly weaker gate**
   **`ChiQWindow ⟹ FlatLeChi`** (`flatLeChi_of_chiQWindow`), where `ChiQWindow` is the a-priori
   *excited-χ window* `chiQmass ≤ CQ·μℓ³·normB` on low states.  Since
   `chiQmass ≤ chiSup·cnPlus` (`chiQmass_le_chiSup_mul_cnPlus`) and `chiSup ∈ [1.38, 3.91]`, this is
   strictly weaker than the session-2 gate `NPlusWindow`
   (`nPlusWindow_imp_chiQWindow` records the implication) — the excited part may carry a large
   *count* while its χ-mass stays small, and it is the χ-mass that the engine actually needs.  The
   pure-real dichotomy is `AprioriCount/chiQWindowArith.lean` (`chiQWindow_arith`); the threading of
   `Adm`/`IsLowB` and the low-state χ-floor are the proved chain of `flatLeChiOfNPlus.lean`.

**SESSION 16 UPDATE (the gate chain audited; two recorded residuals corrected).**  See
`FINDING_flatLeChi_session16.md`.

1. **Audit.**  `AprioriCount/_axFlat16.lean` checks `#print axioms` for every bridge of session 15
   §5: all of them are clean (`[propext, Classical.choice, Quot.sound]`).  The node is exactly one
   frontier atom away and no bridge has decayed.
2. **Session 15's `PairLowerChiSq` (coefficient `16π`) is FALSE.**  At the corpus bump
   `∫χ² = 1` (so `chiSqMass/N = n` on the flat state, `⟨χ²⟩ = 1`), and the stated row fails at
   `n = 2μℓ³`.  The correct χ²-currency coefficient is `8π`; the `16π` of the *proved*
   `fibMass_le_chiSq` is the slack of the crude `wScaled ≤ 2g₀`.  Hence `MI` cannot be obtained
   from the proved `fibMass_le_chiSq` plus any pair bound — it is a word/potential row and must be
   attacked directly.
3. **Session 4's lead (L4) is a non-issue**: `BoxState.contDiff : ContDiff ℝ ∞` makes every
   `BoxState` continuous, so `fibSum_le`'s `hΦc` is discharged by `Φ.contDiff.continuous`.
4. **The `hband` route, from FS's text.**  FS's crude bound `H_B(4μ) ≥ −Cμ²a∫χ_B² − Cμa` is
   `thm:smallbox` with the positive quadratic dropped (hence `n`-independent), and FS apply it only
   on `I ⊆ goodSet` (where `λ₁(u) ≥ μ^{-1/3}`), integrating the χ-smallness over `u`.  The corpus's
   `hband` asks it on the *outer sliver*; the χ-smallness route there is a two-input ledger
   (pointwise `χ_{B(u)} ≤ bandS` plus a sliver count bound), not free of a count bound.

**New PROVED rows available to this node's consumers.**

* `Work.AprioriCount.fibreMass_le_chiSq_sharp` (`AprioriCount/fibreMassSharp.lean`):
  `μM₁ ≤ 8π(a v)μ(1 + 2C₂(R/ℓ)²)(chiSqMass + (C₁R/ℓ)chiCount)` — the corpus's `fibMass_le_chiSq`
  (`16π(a v)`) with the *unsharp* denominator floor `1/2` replaced by the sharp
  `1/(1 + 2C₂(R/ℓ)²)`; the general-`θ` kernel rows are in `AprioriCount/potBrSharp.lean`
  (`abs_kRat_le_of_lower`, `abs_wScaled_le_of_lower`, `potBr_le_of_lower`), and
  `exists_conv_floor_gt_half` shows the floor is *strictly* improvable (`3/4` on a ball).
* `Work.AprioriCount.regime_sideAt_ge_bundle` / `_adm` (`AprioriCount/regimeSharp.lean`): the
  standing dilute regime `R ≤ ℓ·chiR0` holds with `chiR0` replaced by `min chiR0 r` for **any**
  prescribed `r > 0` (the proof only needs `Work.BoseBox.sideAt_large`).  Hence
  `potBrLeChiSq_threeQuarters` (`32π(a v)/3` instead of `16π(a v)`), `potBrLeChiSq_eps`
  (`8π(a v)(1+ε)` — both coefficients sharp up to `ε`) and `chemMass_le_chiMass_sharp`
  (`M₁ ≤ 8π(a v)(1+ε)(chiSup+ε)chiCount`, no lowness, no `J`): the corpus's chemical-mass constants
  `16π(a v)chiSup²` are improvable by `≈ 2chiSup ≈ 7.8`.
* `Work.AprioriCount.sbPot_ge_a0Main_add_boxA2` and `Work.AprioriCount.integral_potWordU_eq`
  (`AprioriCount/sbPotRow.lean`): FS `lm:appinteractionestimate` is *already* a row for the
  **potential** word `sbPot = qLHSwordB`; and `∫_u sbPot = −μM₁ + pairPartB` via
  `qLHSwordB_integral_u` + `qLHSword_eq_potWordU_integral`.  So `MI` ⟺ a `u`-integral row of the
  corpus's explicit per-box quantities.
* ★ **THE LEAD** (`FINDING_flatLeChi_session16.md` §6bis): the same telescoping turns the
  *pointwise* PROVED `sbWord_ge_a0Main_add_boxA2` (+ the PROVED prescribed-`ε` port) into
  `UIntSharp` — the parent of `NPlusWindow`, hence of this node — **without consuming the open
  `PerBoxF`/`Up.flatFreeResidual` chain of the other chapter**.  The only remaining content is the
  `u`-integral of the explicit localised quantities (`a0MainLocBox`'s quadratic in `ρ(u)`,
  the counts `Q(u)`, `ρ(u)`), for which `Work.SmallBoxSliding.Telescope`'s `nBox_integral_u` /
  `boxInd_integral_u` family is available.
-/

/-
**SESSION 17 UPDATE (the exponent bookkeeping, and two pruned routes).**  See
`FINDING_flatLeChi_session17.md` (and the module `AprioriCount/potWordSharp.lean`).

1. **The gate chain's two allowances are not interchangeable.**  `MeanFieldSharp`/`SB` carry the
   exponent `(μ(a v)³)^{1/4}`, while `UIntSharp` and the whole-box potential row
   `μM₁ − pairPartB ≤ 4π(a v)μ²ℓ³(1 + C·K_B³√(μ(a v)³))‖Φ‖²` carry
   `K_B³√(μ(a v)³) = (μ(a v)³)^{287/646}` — a **smaller** allowance.  Hence the whole-box row
   *implies* both `MI` and `UIntSharp` (it is a common strengthening, **not** a new weaker gate),
   while `MI` does not imply it; and `MI` and `UIntSharp` (different functionals) are
   **incomparable**.  The arithmetic fact is proved in `AprioriCount/potWordSharp.lean`
   (`Work.AprioriCount.KB_cube_mul_sqrt_le_rpow_quarter`).
2. **⛔ The χ²-ledger cannot reach `MI`** — and the obstruction is *structural*, not a constant
   race (this sharpens session 16 §1, whose argument was a single-state computation with the
   unsharp `16π` row): with the *sharp* fibre row (`8π(a v)(1+2C₂(R/ℓ)²)`) any pair row
   `P ≥ 8π(a v)μ(X+…)` leaves the term `8π(a v)μ·2C₂(R/ℓ)²·(X + …)` **uncancelled**, and
   `X + … ≲ chiSup·n‖Φ‖²` is unbounded in `n`; shrinking `R/ℓ` shrinks the admissible `μ`'s but
   never bounds `n`.  So `MI` must be a word/potential row at the whole box.
3. **⛔ Session 16 §6bis is wrong**: `Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2` (and the PROVED
   port) require the **a.e. box-support** `∀ᵐ x, Φ x ≠ 0 → ∀ i, x i ∈ dlBox ℓ d u`, which fails for
   *every* `u` for a `BoxState` spread over `abox n ℓ`; the row therefore cannot be integrated over
   `u`, and the route needs the cube chapter's localisation/arity step.  Only the *telescoping*
   `∫_u sbPot = qLHSword = −μM₁ + pairPartB` is unconditional.
4. **⛔ No energy-row + fibre-row combination can give `MI`.**  The χ-**count**-currency companion of
   item 2: with the sharp fibre row and *any* row of the grid/`Y²` type
   `P ≥ B·Y²/N − C(a v)Y − …`, `MI` becomes the quadratic `B y² − Ay + Λ₀(1+…) ≥ 0` in `y = Y/N`,
   whose bad interval collapses (scaling match `B = 4π(a v)(2chiSup−1)/ℓ³`) to exactly
   `y ∈ (μℓ³/(2chiSup−1), μℓ³)` — i.e. **precisely the mean-field count band in which every low
   state lives**.  So `MI` is an equality at the flat extremal state and no such row can be uniform.
   `MI` must be FS `lm:appinteractionestimate` itself, as a word/potential row at the whole box.
-/

/-
**SESSION 18 UPDATE (the residual localised; a scale-free ratio gate; the band half is free).**
See `FINDING_flatLeChi_session18.md`, and the two modules
`AprioriCount/flatLeChiResidual18.lean` and `AprioriCount/flatLeChiRatio18.lean` (both PROVED,
`sorry`-free, axiom-clean).

1. **The residual, localised.**  `AprioriCount/flatLeChiResidual18.lean` composes the two
   *unconditional* halves of the node — the band row (`flatLeChi_bandUncond`, re-exported as
   `bandRow_exists`) and the small-count row (`flatLeChi_smallCount`) — into the Probs `GapCap`
   (the count cap solely above the band threshold; **no** `0 < normB` hypothesis is needed, since
   the gap inequality itself forces `normB > 0` via Parseval) and `ExcitedGate`, with

       `flatLeChi_of_gapCap` / `flatLeChi_of_excitedGate`  :  gate ⟹ `FlatLeChi`,
       `exists_gapCap_of_countWindow` / `excitedGate_of_countWindow` :  `CountWindow ⟹` gate.

   So a counterexample must be a low state with **`K·μ·ℓ³ < n`** *and* **`T₀·n·‖Φ‖² < cnPlus ℓ Φ`**,
   for **every** fixed `K > 0` — the quantitative form of session 13 §1 / session 17 §3bis.

2. **A scale-free ratio gate.**  `AprioriCount/flatLeChiRatio18.lean` supplies the
   *complementary* side of session 15's sharp `√`-engine (`chiCount_ge_sqrt`):
   `cS1_le_chiCount_of_chiQAbove : θ ≥ 1 ∧ θ·(aChi ℓ·cS1) ≤ chiQmass ⟹ (√θ−1)²·aChi ℓ·cS1 ≤ chiCount`
   (unconditionally true, for *every* state).  With the `θ ≤ 1` sibling
   `cS1_le_chiCount_of_chiQBand`, the node follows from the **ratio** gate

       `RatioGate v h R` :  every low state has  `chiQmass ≤ θ₁·aChi ℓ·cS1`  **or**
                             `θ₂·aChi ℓ·cS1 ≤ chiQmass`   (`0 < θ₁ < 1 < θ₂`),

   proved as `flatLeChi_of_ratioGate` (the thresholds are uniform in `ℓ` because
   `chiScaleMeanLower` gives `aChi ℓ ≥ c_χ > 0`).  This statement carries **no `μ`, no `ℓ`, no
   particle count and no `n₊`-window**: it is a pure *ratio* between the excited and the flat
   χ-mass of a single state.  On the band the ratio is `≲ 1/4`, so the band theorem is the *upper*
   side of the gate; what is left is the bounded window
   `θ₁·aChi ℓ·cS1 ≤ chiQmass ≤ θ₂·aChi ℓ·cS1`, i.e. the near-critical configurations of the
   engine — attained (with `chiQmass = aChi ℓ·cS1` and `chiCount = 0`) by the corner family, which
   lowness excludes through `M₁ = 0` there.  ⚠ **Caveat**: `RatioGate` is a *sufficient* condition
   (its thresholds are existentially quantified, so the window may be taken narrow); the corner
   family shows that the engine `chiCount_ge_sqrt` cannot be sharpened, so the *only* remaining
   freedom is whether the low class misses that critical set.  The unconditionally true content is
   the row `cS1_le_chiCount_of_chiQAbove`.

**SESSION 19 UPDATE (the node from FS's *whole-box* interaction row; the ledger is now exact).**
`Submission.Work.AprioriCount.fsBoxRow` reduces the node to a **single** whole-box residual in FS's
own currency, `Work.AprioriCount.FsBoxRow`:

    P₀·(a v)·(μℓ³‖Φ‖² − cS1 ℓ Φ)²/(ℓ³‖Φ‖²) − D·(a v)·μ²ℓ³‖Φ‖² − C·(a v)·μ·cS1 ℓ Φ ≤ wordB
      (low states, ‖Φ‖² > 0, with P₀ > 0, D ≥ P₀ + 4π, C ≥ 0),

i.e. FS's `A₀ + A₂ − Ca(μ + n₀|B|⁻¹)n₊` bound for the box word — with a *linear* error `C·a·μ·cS1`,
FS's **self-energy slot** `D·a·μ²ℓ³‖Φ‖²`, and no `F`-term, no sliding-box localisation, no
`u`-integration, no cube/ball window comparison.  The chain is `flatLeChi_of_fsBoxRow`:

* `fsRow_arith` (PROVED): `FsBoxRow` + lowness ⟹ `s² ≤ (2 + C/P₀)·μℓ³‖Φ‖²·s + (D/P₀)·(μℓ³‖Φ‖²)²`,
  hence `cS1 ≤ (3 + C/P₀ + D/P₀)·μℓ³‖Φ‖²` — a **fixed** constant;
* `fsBoxRow_imp_flatWindow` (PROVED): hence `FlatWindow` (the flat count cap), and then the PROVED
  `flatLeChi_of_flatWindow` gives the node.

⚠ **The self-energy slot is not cosmetic.**  At `cS1 = 0` the corpus's proved `q0word`-quadratic
carries *no slack* (its `4πaμ²ℓ³` slot cancels the square exactly), while lowness is *strictly*
negative there; so any row of the pure shape `P₀a(μℓ³‖Φ‖² − cS1)²/(ℓ³‖Φ‖²) − ⋯ ≤ wordB` is FALSE at
a low state with zero condensate count (a symmetrised `ψ⊗ψ` with `∫_{acube}ψ = 0` has `cS1 = 0`).
The `−D·aμ²ℓ³‖Φ‖²` slot (with `D ≥ P₀ + 4π`) restores the consistency with lowness at `cS1 = 0` that
FS's own `A₀` has (`A₀(n₀=0) = −2πaℓ³(μ − 1/ℓ³)²`).  The error was caught by the review gate on the
delegated `fsBoxRow_holds`; the definition was repaired.

Why this is the honest residual: the corpus's *proved* `q0word`-identity plus `cS2 ≥ cS1² − cS1`
already supplies the mean-field quadratic in the flat count (`q0word_ge_flatDeviation`), so the only
thing missing is the *reduced* `q`-rows `q₁+q₂+q₃+q₄` (FS's Cauchy–Schwarz absorption of `Q₃+Q₄`
together with the Bogoliubov bound on `A₂`).  So this is the whole-box form of FS
`lm:appinteractionestimate` + `lm:appbogolubov`, and it is **strictly weaker** than `CrudeDyson`/`(E)`
(which carries the unwindowed `n(n−1)` and is equivalent to the sharp count window).  A strictly
weaker spelling — keep the proved `q0word` quadratic, with its self-energy slot, and ask only
`k + q₁+q₂+q₃+q₄ ≥ −(D − 4π)·a·μ²ℓ³‖Φ‖² − C·a·μ·cS1` — is on disk as `Work.AprioriCount.QRow`
(`flatLeChi_of_qRow`); its flat cap is the fixed constant `4 + C/(4π) + D/(4π)`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pair part of the box word is nonnegative** for `0 ≤ v`: the localised pair kernel
`wLoc ℓ v 0 x y = χ_ℓ(x)·wScaled ℓ v (x−y)·χ_ℓ(y)` is pointwise nonnegative (a product of three
nonnegative factors).  Needed to pass from `IsLowB` (`wordB ≤ ℓ³Θ‖Φ‖²`, `Θ < 0`) to the
chemical-mass inequality `μM₁ ≥ 4πμ²(a v)ℓ³(1−j)‖Φ‖²`. -/
theorem pairPartB_nonneg {v : E3 → ℝ} (hv : 0 ≤ v) {ℓ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} :
    0 ≤ Work.BoseKinLoc.pairPartB n v ℓ Φ := by
  rw [Work.BoseKinLoc.pairPartB]
  refine MeasureTheory.setIntegral_nonneg (Submission.BoseGases.abox_measurable n ℓ) ?_
  intro x _
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg ?_)
  intro ij _
  rw [Submission.BoseGases.wLoc]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · simpa [Submission.BoseGases.chiU] using Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • x ij.1.1)
  · exact Submission.BoseGases.wScaled_nonneg hv (x ij.1.1 - x ij.1.2)
  · simpa [Submission.BoseGases.chiU] using Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • x ij.1.2)

/-- **The χ-mass is homogeneous of degree `2`** — the scaling needed to apply the corpus's
normalised (`∫Φ² = 1`) lemmas to `Φ/√I`. -/
theorem chiCount_smul {n : ℕ} (ℓ c : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    chiCount ℓ (c • Φ) = c ^ 2 * chiCount ℓ Φ := by
  rw [chiCount, chiCount]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        (c * Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i))
      = ∫ x in Submission.BoseGases.abox n ℓ,
        c ^ 2 * (Φ x ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i)) from by
    refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ) fun x _ => by ring]
  exact MeasureTheory.integral_const_mul _ _

/-- **The χ-mass is nonnegative.** -/
theorem chiCount_nonneg {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ chiCount ℓ Φ := by
  rw [chiCount]
  exact MeasureTheory.integral_nonneg fun x => by
    have hnn : 0 ≤ ∑ i : Fin n, Submission.BoseGases.chiScale ℓ (x i) :=
      Finset.sum_nonneg fun i _ => by
        simpa [Submission.BoseGases.chiScale] using Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • x i)
    exact mul_nonneg (sq_nonneg _) hnn

/-! **SESSION 11 UPDATE (the Dyson half of the χ²-ledger, PROVED).**
`Submission.Work.AprioriCount.dysonChiSqSplit` (`FINDING_dysonChiSqSplit.md`) proves the χ²-currency
form of Dyson's lemma: the χ²-mass of the particles whose nearest neighbour is farther than the
support radius `R` of `v` is paid by the proved sharp-weight Dyson row plus the *packing* term,

    ∫_{abox} Φ²·Σᵢ χ_ℓ(xᵢ)²·1_{R < nnDist xᵢ}
      ≤ (R'³−R³)·(Dyson row RHS)/(3a) + chiSup²·m³·‖Φ‖²      (`ℓ√3 ≤ mR'`),

both declarations axiom-clean (`card_nnDist_gt_le`, `dysonChiSqHole_le`).  At the natural choice
`R' = γμ^{-1/3}` the packing term is a *fixed* multiple of `μℓ³‖Φ‖²` and the annulus term a fixed
multiple of `chiCount` (via the budget `kin + 𝔓 ≤ μM₁ ≤ K₀·chiCount`), so the Dyson ledger caps the
χ²-mass of the **holed** particles; the only remaining term is the χ²-mass of the **clumped**
particles (`nnDist ≤ R`), i.e. exactly the *pair half* of FS `lm:appinteractionestimate` (delegated
as `Work.AprioriCount.clumpedMass_le_pair_add_delta`).  This is the first proved half of the ledger
in the currency the χ-count/χ²-count bridge (`chiCount² ≤ nN·chiSqMass`) actually consumes, and it
does not use any of the `thm:smallbox` vocabulary. -/

/-- **The a-priori count window** at FS's sliding parameters, as a *hypothesis* Prop (the
quantifier shape of `Work.BoseFixB1S.LowStateCountCapB1`): there are `C, ε₀ > 0` such that every
low box state at an admissible chemical potential has at most `C μ ℓ³` particles.  This is the
chapter's standing central residual (FS `thm:aprioriHLambda`). -/
def CountWindow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ {J μ : ℝ}, Work.BoseBoxFix.Adm v ε₀ μ → Work.UBB.lhyC ≤ J →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))},
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
            Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ) →
              (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3

theorem flatLeChi {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.AprioriCount.FlatLeChi v h R := by sorry

end Work.AprioriCount
