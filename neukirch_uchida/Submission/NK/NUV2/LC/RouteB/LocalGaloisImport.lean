import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NeukirchUchida.Local.LocalGalois

/-!
# Import wrapper: local Galois theory of completions

Re-exports the local Galois/decomposition theory of completions of number fields
(`Submission.NeukirchUchida.Local.LocalGalois`) together with the `Algebra` instance on the
completion of an extension.  Delegated lemmas needing this theory must list this module in
`depends_on` (the harness resolves `depends_on` relative to `Submission/Work/`).
-/
