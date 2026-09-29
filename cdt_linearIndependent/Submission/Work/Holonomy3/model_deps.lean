import Mathlib
import Submission.CDT.IntegratedLcm
import Submission.CDT.ModelRiemann
import Submission.CDT.Lcm2Bound
import Submission.CDTPlan.Interfaces
import Submission.Commons.NumberTheory.Chebyshev.theta_sub_theta_eq
import Submission.Commons.NumberTheory.Chebyshev.theta_rel_error
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_band_sub_id_isLittleO

/-!
# Imports for the `τ♯` window-sum estimate

A single import hub for the lemmas used in `Work.Holonomy3.sum_Lge_le_integral`: the model
function of Lemma `lcm-2` and its Riemann-sum material (`Submission.CDT.ModelRiemann`,
`Submission.CDT.IntegratedLcm`), the uniform form of Lemma `lcm-2` (`Submission.CDT.Lcm2Bound`),
the paper's integrated lcm cost (`Submission.CDTPlan.Interfaces`), and the prime number theorem
for `θ`.
-/
