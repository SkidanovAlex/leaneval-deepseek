/-
# Area 4 / HB (11.9) — collected `Commons` dependencies for the `Phi`-contour lemmas

Wrapper module so that the delegated pieces under `Work/LinnikAreas/Density4/` can pull in the
`Commons` API (Gamma vertical bounds, the character-`L` bound on `Re s ≥ 1`, and the vertical
contour shift) with a single `depends_on` entry.
-/
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
