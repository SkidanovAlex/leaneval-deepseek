import Mathlib
import Submission.CDTPlan.InterfacesK

/-! Bridge module: re-exports the orchestrator blueprint `Submission.CDTPlan.InterfacesK`
(where `HauptFacts`, `PsiCFacts`, `phiC`, `psiC`, `hauptH`, `PhiLift` live) inside the
`Submission/Work` subtree, so that `Submission/Work/...` lemmas can list it in `depends_on`. -/
