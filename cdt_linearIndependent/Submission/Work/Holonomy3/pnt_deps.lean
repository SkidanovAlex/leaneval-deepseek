import Submission.CDTPlan.Interfaces
import Submission.Commons.NumberTheory.Chebyshev.tendsto_log_lcmUpto_div_id

/-!
# Dependency bridge for the Chebyshev/prime-number-theorem input to the lcm-cap estimate

This module only re-exports, for the pieces of `Work.Holonomy3` that measure the logarithm of
`lcmUpto`, the two modules they need:

* `Submission.CDTPlan.Interfaces`, which defines `lcmUpto`, `rowSum`, `tauFlat`;
* `Commons.NumberTheory.Chebyshev.tendsto_log_lcmUpto_div_id`, the Chebyshev/PNT input
  `log [1,…,N] / N → 1` (`Chebyshev.psi_eq_log_lcmUpto` identifies `log lcmUpto N` with `ψ N`).
-/
