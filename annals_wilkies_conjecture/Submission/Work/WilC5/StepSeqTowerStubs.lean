import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.StepSeqLogDominated
import Submission.Work.WilC5.EmbeddingTowerGlue
import Submission.Work.WilC5.DclExtRedAlign_probe
import Submission.Work.WilC5.StepSeqCutOverB
import Submission.Work.WilC5.LogPreservingExp
import Submission.Work.WilC5.StepSeqLogPresCut
import Submission.Work.WilC5.StepSeqCutBig
import Submission.Work.WilC5.StepSeqTowerExists
import Submission.Work.WilC5.StepSeqVLeLog

/-! Temporary stub module for `Work.WilC5.StepSeqTower`: the statements of the pieces of vdDMM
Lemma 4.4 that colleagues are proving in parallel, copied verbatim from the review requests.  When
those modules land this file is deleted and its import replaced by `import`s of the real files (the
declaration names are identical, so nothing else changes).

-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-! ## 0. TEMPORARY STUBS

The five lemmas below are being proved by colleagues in parallel; their statements are copied
verbatim from the review requests.  When those modules land, this block is replaced by the
corresponding imports (the names are identical, so nothing else changes). -/

