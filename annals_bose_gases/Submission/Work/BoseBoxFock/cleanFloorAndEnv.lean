import ChallengeDeps
import Submission.Work.BoseBoxFock.Clean.Floor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/cleanFloorAndEnv.lean`

The two environment inputs of the box ↔ model bridge, delivered as a single
`∧`-statement:

* the **environment bundle** `EnvFactsAt`, uniformly in the honest mode data
  (`Work.BoseBoxFock.envFacts_uniform`, delivered here as `Clean.envFacts_uniform`);
* the **model floor** (FS `thm:Kafz`, node BF4) at the honest model
  (`Work.BoseBoxFock.model_kafz`, delivered here as `Clean.model_kafz`).

## The "clean" in the name

The two original modules `Submission/Work/BoseBoxFock/envFacts_uniform.lean` and
`Submission/Work/BoseBoxFock/model_kafz.lean` (and their statements) are correct, but their
**import cones are currently unloadable**: they reach
`Submission.Work.BoseFixR.HonestEnvParity` → `RB5FSFixAux` and
`Submission.Work.BoseBoxFock.sum_hatChiSq_sq_le` → `Submission.Work.BoseFixR.FarKernelRowsB`
→ `Submission.Work.BoseGateFS.GateHonest`, and those two modules no longer compile after the
interface change `F9` (`CloseCond` → `CloseCondFS`): their sources fail to typecheck
(one-line `CloseCond`/`CloseCondFS` mismatches) and their `.olean`s are gone, so *every* module
above them in the import order fails to load.

This file therefore delivers the same two statements from a rebuilt, self-contained copy of
that (sub)cone, living in `Submission/Work/BoseBoxFock/Clean/`:

* `Clean/Parity.lean` — `HonestEnvParity` (`RB5FSFixAux` is unused by its proof);
* `Clean/EnvFacts2.lean` — `honestEnvFam_*`, `cHCF_nonneg` (the six environment facts);
* `Clean/ChiSq.lean` — `unitCell_chiSq_cos`, `BesselUnitCell`, `sum_hatChiSq_sq_le`;
* `Clean/Bessel.lean` — `honestEnvBesselCorrected` (`§1`–`§8` of `honestEnvBessel.lean`);
* `Clean/EnvFactsNumeric.lean` — the regime lemmas and `envFacts_uniform`;
* `Clean/Floor.lean` — `model_kafz`.

Each of these is a verbatim copy of the corresponding declaration with the broken imports
replaced by its clean counterpart, so the two conjuncts below are proved exactly as the
originals were.  No new mathematics is claimed here; the point of the lemma is that the
two statements *are available* in a cone that compiles.
-/

namespace Work.BoseBoxFock

theorem cleanFloorAndEnv (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) :
    (∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
        Work.BoseBoxFix.Adm v ε₀ μ → Work.BoseBoxFock.EnvFactsAt v h fc fu HM μ C) ∧
    (∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
        Work.BoseBoxFix.Adm v ε₀ μ → ∀ (n : ℕ),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          ∀ Ψ : Work.BoseB4.RealFock (HM μ).m, Ψ ≠ 0 →
            Work.BoseBoxFock.ExcWindow (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
              (BoseGases.a v) μ) n Ψ →
            ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFS ρ.1)
                - Work.BoseFixR.errKafz v R μ C) * Work.BoseB4.bomb (HM μ).m Ψ Ψ
              ≤ Work.BoseB4.bomb (HM μ).m Ψ (Work.BoseBoxFock.H2ndHon v h fc fu HM μ Ψ)) :=
  ⟨Clean.envFacts_uniform v h hv hv1 hvrad hR hv_supp hav fc fu,
   Clean.model_kafz v h hv hv1 hvrad hR hv_supp hav fc fu⟩

end Work.BoseBoxFock
