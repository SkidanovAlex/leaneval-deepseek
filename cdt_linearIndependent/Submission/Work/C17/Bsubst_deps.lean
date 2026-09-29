/-
# Shared imports for the `Bsubst_poly_growth` development (area C17)

Aggregator module: it only re-exports the workspace modules in which the
pure functions `B₁,…,B₇`, the symmetrisation data (`sympY`, `sympPhi`,
`sympW`), the x-side series (`Lps`, `Li2ps`, `Jps`, `g`) and the ODEs of
`B₂, B₄, B₅` live, so that delegated lemmas can name them in `depends_on`.
-/
import Submission.CDTPlan.Interfaces
import Submission.CDT.SympH
import Submission.Work.C7.xdefs
import Submission.Work.Pure.b4_rel
import Submission.Work.Pure.b5_rel
