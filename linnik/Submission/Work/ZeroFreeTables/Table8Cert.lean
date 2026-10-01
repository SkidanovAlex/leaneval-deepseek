/-
# ZeroFreeTables — Table8Cert.lean

The rational certificate for the thirteen entries of HB Table 8 that `rows15`
uses (with the targets equal to `rows15`'s `λ₀`-entries, i.e. the printed values
lowered by `1/1000`).  Each row is a list of four rational literals and
`cond913`/`p913` are rational expressions, so both conjuncts are decided by
kernel arithmetic; the witnesses were found by exact rational search (`dev/t8h.py`)
using HB's polynomial `P₃(X) = X + X² + (2/3)X³`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

theorem Table8Cert : ∀ r ∈ Work.ZeroFreeTables.t8certRows,
    Work.ZeroFreeTables.cond913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) ∧
    Work.ZeroFreeTables.p913 r.2.1 r.2.2.1 r.2.2.2 (Work.ZeroFreeTables.Kaff r.2.1) < 0 := by
  intro r hr
  fin_cases hr <;>
    (constructor <;> norm_num [cond913, p913, Kaff, P3R, psi13, Kond])

end Work.ZeroFreeTables
