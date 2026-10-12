import ChallengeDeps
import Submission.Work.BoseFixB1.windowBridge_holds
import Submission.Work.BoseFixB1B.aprioriFromSliding
import Submission.Work.BoseFixB2.DvApriori.exists_window_factor_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowCountBound` — FS `thm:aprioribounds`, the count bound

FS's remark after `thm:aprioribounds` (`final_v2.tex`, proof of Theorem
`thm:aprioribounds`): *"Due to our assumptions they, in particular, imply that
`n ≤ C μ ℓ³`"* — i.e. the two a-priori windows `eq:apriorinn+` force the particle
number of a low state to be bounded by a constant times the expected one.

The present statement is that consequence at FS's own parameters
(`ℓ = sideAt μ (a v)`, `K_B = (paramsAt μ (a v)).KB`), in the frozen vocabulary of
`Submission/Work/BoseBoxFix/Defs.lean` (`Adm`, `IsLowB`, `normB`,
`Work.BoseKinLoc.BoxState`), for a fixed `J ≥ lhyC` (with FS's low-state
hypothesis `J ≤ K_B³` carried as a hypothesis of the quantified statement).

## Route

* the a-priori bounds `Work.BoseFixB1.AprioriHLambdaIneq` (FS `eq:aprioriRn+`,
  proved from the Appendix `SmallBoxes`: the sliding localisation `SlidingB` +
  the per-small-box bound `smallBoxCollectedC_holds`);
* `Work.BoseFixB1.windowBridge_holds` (FS `thm:aprioriHLambda` step 4): a low
  box state with `0 < ‖Φ‖²` satisfies `|n − μℓ³| ≤ C·nWindow` with
  `nWindow = μℓ³·K_B^{3/2}K_ℓ(μa³)^{1/4}`;
## Status of the route (read before changing this file)

> **⚠ THE PROOF BELOW IS *VACUOUS* — read `Submission/Work/BoseFixB1B/FINDING_lowCountBound_session8.md`.**
> `Work.BoseFixB1B.aprioriHLambdaIneq_from_slidingB` consumes the corpus's
> `Work.BoseFixB1.smallBoxCollectedC_holds`, whose cone contains (i) `sorryAx` and (ii) the
> **FALSE** statement `Work.BoseFixB1.PerBoxF` *without* a low-state restriction (its provider is
> required for *all* states; three independent refutations of its flat branch via the
> Jastrow/correlation-hole family, `Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`).
> So the proof below is not usable.
>
> The **corrected, non-vacuous** chain for this very statement is on disk:
>
> * `Submission/Work/BoseFixB1B/lowProviderDefs.lean` — `PerBoxFLow`, `OffGoodCrudeLow`,
>   `CollectedLow`, `AprioriHLambdaIneqLow` (the low-state / positive-norm class);
> * `Submission/Work/BoseFixB1B/perBoxIntegratedLow.lean`,
>   `Submission/Work/BoseFixB1B/trimInteriorOfPerBoxFLow.lean` — the `IsLowB`-restricted copies of
>   the corpus's integrated per-box node and of the `eq:badset` trim;
> * `Submission/Work/BoseFixB1B/lowProviderChain.lean` — `collectedLow_of_providers`,
>   `aprioriHLambdaIneqLow_of_collected`, `lowCountBound_of_windowBridge`;
> * `Submission/Work/BoseFixB1B/lowProviderResidual.lean` — `perBoxFLow_of_branches` and
>   `aprioriHLambdaIneqLow_of_residual`.
>
> The corrected residual is exactly the FLAT branch for low states
> (`Work.BoseFixB1B.flatBranchLowB`, i.e. `FlatBranchLow`) plus FS `eq:badset` off the good set,
> together with the delegated window step `Work.BoseFixB1B.windowBridgeLow`.

## Session 10 — read `FINDING_lowCountBound_session10.md`

Two results that change how this node should be attacked (statement of the theorem below
untouched; the body is unchanged from session 8, hence still `sorryAx`-tainted):

* this node needs the good-set provider `PerBoxF` only at a **free** `c₁` — `collectedLow_of_providers`
  existentially quantifies `c₁` and `arith_absorb` never mentions it (the `c₁·W·∫Φ²ψ` credit is
  dropped, soundly).  So aim at `Work.BoseFixB1S.PerBoxFlatFree`, *not* at the sharp `c₁ = 1/4`
  of `Work.BoseFixB1B.flatBranchLowB`;
* the fleet's `PerBoxFlatResJensen` (the `BoseFixB1S` flat-branch residual,
  `perBoxMeanFieldB1.lean`) is **FALSE**: its MAN3/Jensen Cauchy–Schwarz correction
  `2√(Kw·M_w·(n−1)²QS/(2V²))` is not payable by the slack for states with `n ≫ μV`
  (constant ratio `≳ 2/(1+ω̄) ≥ 4/3`, and `≫ 1` for the pointwise `Kw` the corpus's
  `mfManifestLowerV2B1` requires).  See the FINDING §2, §5–§7 for the ratio computation and the
  numerics; the pairing `A₂` must be kept in the supply (FS's `eq:Q3+Q4CS`), i.e. the crux is the
  *operator*-form `boxCrossJoint`, not a scalar manifest.

## Session 11 — read `FINDING_lowCountBound_session11.md`

Two things changed the picture:

* the sharpest residual pair is now `{ FlatBranchFree , FlatArmBand }`
  (`Work.BoseFixB1B.lowCountBound_of_freeFlatArmBand`,
  `Submission/Work/BoseFixB1B/lowCountResidualSharp.lean`, axiom-clean); `FlatArmBand` is
  strictly weaker than `ArmCondensed` (the PROVED `bandCondensedArm_of_flatArm` assembles the
  latter from the former, `bandExcitedArm` being PROVED with `C = 0`);
* **both** arms of that pair reduce to the *same* filed statement: FS `lm:appbogolubov` at the
  sliding box in the sharpened `(n+1)·(flat count)` mass form, i.e.
  `Work.BoseFixB1.lm_appbogolubov_localisedB` (`Submission/Work/BoseFixB1/…`), whose entire
  leftover is the in-proof goal `hβ : 0 ≤ β(Ψ)` at line 531.  So the node's remaining
  *mathematical* content is one question (the joint `A₁`-shift/zero-point per-mode bound); see the
  FINDING §§2–4 for the exact shape and the recommended first step
  (`Work.BoseFixB1.boxSimpleA2TwoWindowC`, whose last missing ingredient is now PROVED).

The session-9 wiring blocker is still in place (the `Work.BoseFixB1S.normB_nonneg` shadowing and
the duplicated `Work.BoseFixB1S.sbKin_nonneg`); see the FINDING §6.

## Session 12 — read `FINDING_lowCountBound_session12.md`

The node is now **attached to the fleet's live sector frontier**, machine-checked and axiom-clean
(`Submission/Work/BoseFixB1B/sectorFrontier.lean`):

    Work.BoseFixB1B.lowCountBound  ⟸  { ∃ ε₀ c₁ C, PerBoxFLow v h R J c₁ C ε₀ ,  one band arm }

The first half is supplied by `Work.BoseFixB1.PerSectorSmooth` (via `perBoxFLow_of_perSectorSmooth`),
by its low-state-restricted spelling `Work.BoseFixB1B.PerSectorSmoothLow` (via
`perBoxFLow_of_perSectorSmoothLow`), and by the two *named* frontier atoms
`perSectorSmoothLowDens` / `perSectorSmoothHighDens` (via
`lowCountBound_of_coreEx_flatArmBand` / `…_armCondensed`, which consume exactly those two files'
`∃`-form conclusions); the second half is `FlatArmBand` / `ArmCondensed` /
`ArmCondensedDecoupled` (`lowCountBound_of_perSectorSmoothLow_{flatArmBand, armCondensed,
decoupled}`).  So the node is two applications away from the two frontier files, and the
session-8…11 wrapper stack (`flatBranchLowB`, `trimInteriorOfPerBoxFLow`, `lowProvider*`) is
bypassed.  On a sector the count identity `Σᵢ(Pᵢ+Qᵢ) = k·Id` holds
(`boxFlat_add_boxQCount_sectorPiece`), which makes the scalarised credit exact — this is why the
sector route avoids the session-11 `hβ ≥ 0` obstruction, and why the corpus's sector-level rung-4
payment `Work.BoseFixB1.SectorAux.a0A2QPayNormB1Good` is axiom-clean (verified).  The band half
cannot come from the frontier (the frontier is stated on `goodSet`, the band lies outside it); the
`4μ` is *not* the obstruction (`armCondensed_of_decoupled` handles it).  See the FINDING §§1–9.

## Session 9 — read `FINDING_lowCountBound_session9.md`

The band half of that residual is now the corpus's **central** residual, and the corrected chain is
*machine-checked axiom-clean*:

    `Work.BoseFixB1B.lowCountBound`  ⟸  { `FlatBranchLow` , `Work.BoseFixR.SlabCondensedHalf` }

is `Work.BoseFixB1B.lowCountBound_of_flatSlabCondensed` (`Submission/Work/BoseFixB1B/bandFromSlab.lean`:
the adapter from the corpus's central residual, over `bandFromCondensed.lean`'s axiom-clean assembly
`offGoodCrudeLow_of_arm`); the `#print axioms` of `Work.BoseFixB1B.lowCountBound_of_flatArm` (the
same chain with the two residuals as hypotheses) is `[propext, Classical.choice, Quot.sound]`.  An
equivalent formulation using FS's own `μ ↦ 4μ` mechanism is
`Work.BoseFixB1B.lowCountBound_of_flatDecoupled` (`decoupledBand.lean`, also axiom-clean).

**Why this body is NOT (yet) wired to that chain.**  Wiring it requires importing
`Submission.Work.BoseFixB1B.bandFromSlab` and `Submission.Work.BoseFixB1B.flatBranchLowB` here.
`flatBranchLowB`'s import cone contains `Submission.Work.BoseFixB1S.sectorPassageB1`, which declares
`Work.BoseFixB1S.normB_nonneg`; that declaration *shadows* the unqualified `normB_nonneg` used in
`Submission.Work.BoseFixB1S.trimInteriorB1` (and, by the same mechanism,
`aprioriUnif_of_collectedUnif`), so importing it here breaks two sibling files whose cones reach
this one (`trimInteriorB1` is imported by `Work.BoseFixB1.smallBoxCollected_holds`).  Until their
owners rename that declaration — and the equally fragile `Work.BoseFixB1S.sbKin_nonneg`, declared
both in `perBoxCrudeLowerB1.lean` and in `BandPerBoxCrudeB1.lean` — the body below is left as
session 8 left it.  To wire it, add the two imports above and replace the body by

    exact lowCountBound_of_flatSlabCondensed h hv hv1 hvrad hR hv_supp hav hJ
      (flatBranchLowB v h hv hv1 hvrad hR hv_supp hav hJ)

* `Work.BoseFixB1.windowBridge_holds` (FS `thm:aprioriHLambda` step 4) is *proved*
  and `sorry`-free; the arithmetic below is mine.
* `Work.BoseFixB1.aprioriHLambdaIneq_holds` (FS `eq:aprioriRn+`) is proved modulo the
  chapter's one open analytic input `Work.BoseFixB1.SlidingB` (FS `eq:BSsliding2` /
  Bratteli--Solovej Thm 3.10): the file `slidingB_holds.lean` still ends in `sorry`, and
  via `slidingB_of_kineticHalf` + `potentialHalf_holds` it reduces to
  `Work.BoseFixB1.KineticHalf`, whose design and remaining pieces are in
  `Submission/Work/BoseFixB1/ONE_BODY_KINETIC_HALF_DESIGN_S2.md` (pieces (P), (G) and the
  assembly; the `ε₀` arithmetic is the proved `oneBodyKineticHalfArith.exists_eps₀_criteria`).
  This lemma therefore becomes `sorry`-free exactly when that input lands; no other gap.

* the arithmetic: the window factor `K_B^{3/2}K_ℓ(μa³)^{1/4} = (μa³)^{281/1292}`
  tends to `0`, so for `ε₀` small it is at most `1/2`
  (`Work.BoseFixB2.DvApriori.exists_window_factor_le`), whence
  `|n − μℓ³| ≤ (C/2)μℓ³`, i.e. `n ≤ (1 + C/2)μℓ³`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `ℓ = sideAt μ a = K_ℓ(μa)^{-1/2}` is positive (the elementary form of
`Work.BoseFixB1.adm_ell_pos`, without the `Adm` bundle). -/
lemma sideAt_pos' {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) : 0 < Work.BoseBox.sideAt μ a :=
  Work.BoseBox.boxSide_pos hμ ha (by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity))

/-- **The window factor is a small perturbation.**  At FS's parameters the window
factor `K_B^{3/2}K_ℓ(μa³)^{1/4}` is `(μa³)^{281/1292}`, so it is `≤ 1/2` on a
diluteness window; consequently `nWindow ≤ μℓ³/2`. -/
lemma nWindow_le_half_mu_side_cube {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
          (_root_.BoseGases.a v)
        ≤ (1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
  obtain ⟨εF, hεF, hF⟩ :=
    Work.BoseFixB2.DvApriori.exists_window_factor_le v hav (C₁ := 1) (by norm_num)
  refine ⟨εF, hεF, fun μ hμ ht => ?_⟩
  -- `nWindow` in terms of `sideAt` and the window factor
  have hnw : Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
      = μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)) := by
    rw [Work.BoseFixB1.nWindow_eq]
    ring
  rw [hnw]
  have hfac : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ) ≤ 1 / 2 := by
    simpa using hF μ hμ ht
  have h0 : 0 ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    mul_nonneg hμ.le (pow_nonneg (sideAt_pos' hμ hav).le 3)
  calc μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ))
      ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hfac h0
    _ = (1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by ring

theorem lowCountBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
  -- FS `eq:aprioriRn+` and the particle window of FS `thm:aprioriHLambda`
  have hA : Work.BoseFixB1.AprioriHLambdaIneq v h J :=
    Work.BoseFixB1B.aprioriHLambdaIneq_from_slidingB h hv hv1 hvrad hR hv_supp hav hJ
  obtain ⟨Cw, εw, hCw0, hεw, hW⟩ :=
    Work.BoseFixB1.windowBridge_holds h hv hv1 hvrad hR hv_supp hav hJ hA
  -- the window factor is `≤ 1/2` on the diluteness window
  obtain ⟨εF, hεF, hF⟩ := nWindow_le_half_mu_side_cube (v := v) hav
  refine ⟨min εw (min εF 1), 1 + Cw / 2,
    lt_min hεw (lt_min hεF one_pos), by linarith, ?_⟩
  intro μ hAdm hJK n Φ hpos hlow
  have hμ : 0 < μ := hAdm.1
  have hε1 : min εw (min εF 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hεw' : min εw (min εF 1) ≤ εw := min_le_left _ _
  have hεF' : min εw (min εF 1) ≤ εF := le_trans (min_le_right _ _) (min_le_left _ _)
  have hAdmW : Work.BoseBoxFix.Adm v εw μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 hεw', hAdm.2.2⟩
  have hwin := hW μ hAdmW hJK n Φ hpos hlow
  have hfac : Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
      ≤ (1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
    hF μ hμ (le_trans hAdm.2.1 hεF')
  have hCw : 0 ≤ Cw := hCw0
  -- `|n − μℓ³| ≤ (Cw/2)μℓ³`
  have hb2 : Cw * Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
      ≤ Cw * ((1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) :=
    mul_le_mul_of_nonneg_left hfac hCw
  have hb3 : Cw * ((1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3))
      = (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by ring
  have hmain : |(n : ℝ) - μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3|
      ≤ (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
    le_trans hwin (le_trans hb2 (le_of_eq hb3))
  -- conclude `n ≤ (1 + Cw/2)·μℓ³`
  have hβ : 0 ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    mul_nonneg hμ.le (pow_nonneg (sideAt_pos' hμ hav).le 3)
  have hn : (n : ℝ)
      ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        + (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
    have := (abs_le.mp hmain).2
    linarith
  calc (n : ℝ)
      ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        + (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := hn
    _ = (1 + Cw / 2) * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by ring

end Work.BoseFixB1B
