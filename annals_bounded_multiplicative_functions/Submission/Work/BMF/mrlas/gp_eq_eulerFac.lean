import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.LSeries_exp_Wsup_defs
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex

/-- The local Euler factor `gp f p s = Σ_e f(p^e) p^{-es}` defined from the L-series terms
agrees with `eulerFac f p s = Σ_e f(p^e) (p^{-s})^e`. -/
theorem gp_eq_eulerFac (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    Work.BMF.gp f p s = Work.BMF.eulerFac f p s := by
  rw [Work.BMF.gp, Work.BMF.eulerFac]
  exact tsum_congr fun e => by
    rw [term_primePow f hp s e, u_eq_cpow hp.ne_zero s]

end Work.BMF.mrlas
