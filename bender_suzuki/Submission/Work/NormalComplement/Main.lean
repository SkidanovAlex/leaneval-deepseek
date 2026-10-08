/-
# Area `NormalComplement` — Theorem D of Peterfalvi I Chapter III

The main theorem of the area: **Théorème D** (Peterfalvi I Ch. III, p.172), i.e.
`Submission.Blueprint.ThmDProp`: in the situation (B0)–(B2), for every strongly embedded `H`
there is an involution `t ∉ H` such that `D = H ∩ H^t` has a normal complement `Q` in `H`.

## The shape of the delivered theorem

`ThmDProp` is assembled in `Submission.Work.NormalComplement.thmD_of_sections_v3` from

* `hFT : FeitThompsonProp` — the project's standing hypothesis (odd order ⟹ solvable);
* `TransferProp` — Ch. III §1 Lemma 1, proved as `Work.NormalComplement.pcontrol_transfer`;
* `StrategyProp` — the Strategy of §1, proved from `Work.NormalComplement.pResidual_strategy`;
* `PrimesOfAbelianizationProp` — the elementary input of §2, proved as
  `Work.NormalComplement.primes_of_abelianization`;
* `Section2Prop'` — Ch. III §2 Prop. 1 (`SectionsV3.lean`), proved as
  `Work.NormalComplement.section2_prop1_v3`;
* `Section2CorollaryProp` — the Corollary of §2 Prop. 1, proved as
  `Work.NormalComplement.section2Corollary_v3`;
* `Section3Prop` — §3, proved as `Work.NormalComplement.section3Prop_of` (App. VI = `appVI`,
  App. VII = `appVIIProp`, §3 Prop. 2 = `section3_prop2`, §1 Lemma 2 Corollary = `controlCorollary`);
* `Section45Prop` — Ch. III §4–§5, proved as `Work.NormalComplement.section45Prop_of`
  (`exists_setup45` → `sec4_lemma1ab` → `exists_setup5_nokinv` → `sec5_final_clean`).

All of these are proved in this directory, `sorry`-free and axiom-clean; the only hypotheses of the
delivered `normalComplement` are the blueprint's `Prop`s (`FeitThompsonProp` and the area `Prop`s,
among them `ChIIFourP3SubnormalProp` and `BenderModelFacts2Prop`).

`BenderPrelimProp` (Ch. I §2 Prop. 2(b), the Ch. I input that no area `Prop` exposes) is proved as
`Work.NormalComplement.bender_prelim`; the Ch. I/II inputs App. III and App. V are
`Work.NormalComplement.appIII` and `Work.NormalComplement.appV`.

## The `KInvariantUnderD` input is not needed

An earlier version of this assembly carried `KInvariantUnderD H t` (`K = J(D,t)` is a subgroup of
`D`) as an input, through `KInvariantUnderD`-taking versions of §2 Prop. 1.  Following the lead's
ruling (`NOTES_LEAD_bs_appxgap.md`) that input is *gone*: `Section2Prop'` (`SectionsV3.lean`) is
Ch. III §2 Prop. 1 with the case split of the proof made after conjugating the `p`-subgroup into
`V = C_D(t)`, where no `D`-conjugation of `K` occurs; the normaliser conditions are transported
back by `normalizerCond_conj`.  The files `AppXReduce.lean`, `AppXProp`, `AppXGap` and
`InvolutionsCommuteProp` are superseded and are not inputs (see `NOTES_APPX_CONCLUSION.md` for the
analysis that prompted the ruling).
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.SectionsV3
import Submission.Work.NormalComplement.thmD_of_sections_v3
import Submission.Work.NormalComplement.pcontrol_transfer
import Submission.Work.NormalComplement.pResidual_strategy
import Submission.Work.NormalComplement.primes_of_abelianization
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.section2_prop1_v3
import Submission.Work.NormalComplement.section2Corollary_v3
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.section3Prop_of
import Submission.Work.NormalComplement.appV
import Submission.Work.NormalComplement.appVIIProp
import Submission.Work.NormalComplement.appVI
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.controlCorollary
import Submission.Work.NormalComplement.chISixCor1Prop
import Submission.Work.NormalComplement.burnsideClassProp
import Submission.Work.NormalComplement.section45Prop_of

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## The discharged inputs of the interface -/

/-- Ch. III §1 Lemma 1 (transfer), discharged: `TransferProp` from
`Work.NormalComplement.pcontrol_transfer`. -/
theorem transferProp : TransferProp := by
  intro G _ _ p _ E W y h hE h1 hord hy' _
  exact pcontrol_transfer h hE h1 hord hy'

/-- The Strategy of Ch. III §1 (p.175), discharged from `pResidual_strategy`. -/
theorem strategyProp : StrategyProp := by
  intro G _ _ p _ E W D H y hEW hED hE hWH hHn hWD hyW hy
  exact pResidual_strategy hEW hED hE hWH hHn hWD hyW hy

/-- The elementary input of Ch. III §2, discharged. -/
theorem primesOfAbelianization : PrimesOfAbelianizationProp := primes_of_abelianization

/-- The Ch. I §2 Prop. 2(b) input of Chapter III, discharged. -/
theorem benderPrelim : BenderPrelimProp := bender_prelim

/-- App. VI (pp. 213–215), discharged.  (`AppVIProp` quantifies over an index type in an arbitrary
universe; we pin it to universe `0`, the project's convention.) -/
theorem appVIProp : AppVIProp.{0} := by
  intro W _ _ I _ _ K hI hreg hcent
  exact appVI hI hreg hcent

/-- App. III (pp. 206–207), discharged from `appIII`. -/
theorem appIIIProp (hBrSz : BrauerSuzukiProp) (hFT : FeitThompsonProp) : AppIIIProp :=
  appIII hBrSz hFT

/-- The Corollary of §2 Prop. 1 (p.176), discharged from `section2Corollary_v3`. -/
theorem section2CorollaryProp (hFT : FeitThompsonProp) (hTrans : TransferProp)
    (hS2 : Section2Prop') (hBP : BenderPrelimProp) (hC4 : ChIIFourProp) :
    Section2CorollaryProp :=
  section2Corollary_v3 hFT hTrans hS2 hBP hC4

-- §3 Prop. 2 (p.178) is `Submission.Work.NormalComplement.section3_prop2`, whose hypotheses are
-- `AppVIProp` (`appVIProp` above), `HeringProp`, `Section2CorollaryProp` (`section2CorollaryProp`
-- above), `BenderPrelimProp` and `ChIIFourProp`.

/-! ## Theorem D -/

/-- **Theorem D** (Peterfalvi I Ch. III, p.172), assembled from the blueprint's `Prop`s.  The area
`Prop`s `hA, hC, hC4, hHer, hTF, hBrSz, hMod` are consumed inside `Section2Prop'`, `Section3Prop`
and `Section45Prop`; `hP3` (`ChIIFourP3SubnormalProp`) and `hMF2` (`BenderModelFacts2Prop`) are the
two blueprint `Prop`s added for this area. -/
theorem normalComplement (hFT : FeitThompsonProp) (hA : ThmAProp) (hC : ThmCProp)
    (hC4 : ChIIFourProp) (hHer : HeringProp) (hTF : ThompsonFrobeniusProp)
    (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp) (hP3 : ChIIFourP3SubnormalProp)
    (hMF2 : BenderModelFacts2Prop) : ThmDProp := by
  have hBP : BenderPrelimProp := benderPrelim
  have hTrans : TransferProp := transferProp
  have hStrat : StrategyProp := strategyProp
  -- Ch. III §2 Prop. 1, without any `KInvariantUnderD` input.
  have hS2 : Section2Prop' := section2_prop1_v3 hFT hBP hC4 hP3
  -- the Corollary of §2 Prop. 1.
  have hS2c : Section2CorollaryProp := section2Corollary_v3 hFT hTrans hS2 hBP hC4
  -- Ch. III §3.
  have hS3 : Section3Prop :=
    section3Prop_of hFT hC4 hMod appV appVIIProp hS2c
      (section3_prop2 appVIProp hHer hS2c hBP hC4 : Section3Prop2)
  -- Ch. III §4–§5 (the glue of `section45Prop_of` derives its own `Section2Prop'`).
  have hS45 : Section45Prop :=
    section45Prop_of hFT hA hC hC4 hMod hP3 appV (appIIIProp hBrSz hFT) appVIIProp hMF2
      (chISixCor1Prop hA hBP) burnsideClassProp controlCorollary hBP hTrans hStrat
      (Section2Prop_of_Section2Prop' hS2)
  exact thmD_of_sections_v3 hFT hTrans hStrat primesOfAbelianization hS2 hS3 hS45

end Work.NormalComplement
