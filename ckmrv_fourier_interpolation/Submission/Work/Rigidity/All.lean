/-
# The CKMRV rigidity chapter: entry point

Import this module to obtain the area developed under `Submission/Work/Rigidity/`:

* `Work.Rigidity.Basic` : the vocabulary of the chapter.  `InStrip`, `StripDecay`
  (`o(e^{−2πc Im τ})` along the strip), `SlashEigen` (`f ∣[k] S = ε·f`), `AnnT2`
  (`(T − I)² f = 0`), and the single-function statement `SingleRigidity k ε c`; plus the
  transfer lemmas from functions of `ℂ` to functions on `ℍ`.

* `Work.Rigidity.Reduction` : the eigenfunction reduction.  For `(i/τ)^k = τ^{−k}` and even
  `k`, the single-function statements `SingleRigidity k (±1) c` imply
  `Work.FE.HomogeneousRigidity n c` with `n = 2k`; the generic form
  `homogeneousRigidity_of_eigen` carries an extra class `P` of functions along, so that the
  same proof serves the `𝒫`-free and the paper-faithful variants.

* `Work.Rigidity.Diff` : the first difference `fstDiff f τ = f(τ+1) − f(τ)`; periodicity of
  the first difference *is* `AnnT2`, and `fstDiff` inherits the strip decay.  This is the
  splitting `f = u + τ·v` used in every proof of `lem:noPsolutions`.

* `Work.Rigidity.ModerateGrowth` : the paper-faithful statements
  `SingleRigidityP k ε c` (with `f ∈ 𝒫 = Work.Kernels.InP`) and `HomogeneousRigidityP n c`,
  together with the corrected reduction `homogeneousRigidityP_of_singleRigidityP`.

* `Work.Rigidity.Counterexample` : **the two `InP`-free statements are false.**  An explicit
  nonzero `f` with `(T − I)² f = 0`, `f ∣[k] S = −f` and the strip decay exists at both
  weights (`verification/verify_ce.py` checks the `q`-expansions in exact arithmetic), and
  `not_homogeneousRigidity_of_singleCounterexample` turns any such `f` into a refutation of
  `Work.FE.HomogeneousRigidity 2k c` by taking `g = g̃ = f/2`.

The directory `_abandoned_dir/` holds, with a `.lean.bak` suffix so that `lake` ignores them,
the abandoned routes through the `𝒫`-free statements (they contain `sorry`); they are kept only
as a record and must not be re-opened.

Consequently `Work.FE.HomogeneousRigidity 8 0` and `Work.FE.HomogeneousRigidity 24 1` — the
targets originally requested — cannot be proved, and the corrected targets are
`Work.Rigidity.HomogeneousRigidityP 8 0` and `Work.Rigidity.HomogeneousRigidityP 24 1`,
whose four inputs `SingleRigidityP 4 (±1) 0`, `SingleRigidityP 12 (±1) 1` are the actual
content of CKMRV `lem:noPsolutions`.

* `Work.Rigidity.AnnPlusWeightFourP`, `Work.Rigidity.AnnMinusWeightFourP` : the two weight-`4`
  corrected statements (proved).
* `Work.Rigidity.InP_of_dirichletExpansion` : `Work.Kernels.InP` for a Dirichlet expansion
  `Σ aₙ e^{2πinτ} + 2πiτ Σ bₙ e^{2πinτ}` with polynomially bounded coefficients — the missing
  side condition for the Section 8 pairs.
* `Work.Rigidity.Assembly` : `Work.Rigidity.homogeneousRigidityP_eight : HomogeneousRigidityP 8 0`,
  the corrected `E₈` and Leech theorems
  (`homogeneousRigidityP_eight : HomogeneousRigidityP 8 0`,
  `homogeneousRigidityP_twentyfour : HomogeneousRigidityP 24 1`).
-/
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.Reduction
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.Counterexample
import Submission.Work.Rigidity.Assembly
import Submission.Work.Rigidity.AnnPlusWeightFourP
import Submission.Work.Rigidity.AnnMinusWeightFourP
import Submission.Work.Rigidity.AnnPlusWeightTwelveP
import Submission.Work.Rigidity.AnnMinusWeightTwelveP
import Submission.Work.Rigidity.InP_of_dirichletExpansion
