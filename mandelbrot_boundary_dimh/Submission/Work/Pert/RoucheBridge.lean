import Mathlib
import Submission.Unif.Commons.Analysis.Complex.rouche_simple_zero

/-!
# Bridge: re-export the Rouché lemma

`Commons.Analysis.Complex.rouche_simple_zero` lives outside `Submission/Work/`, so it cannot be
named in a `depends_on` list of a lemma delegated under `Submission/Work/`.  This file imports it
so that PERT lemmas can depend on `Work/Pert/RoucheBridge`.
-/
