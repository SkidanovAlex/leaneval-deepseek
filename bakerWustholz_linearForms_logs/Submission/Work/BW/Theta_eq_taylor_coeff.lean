import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `Θ(z;k,l,m) = (1/m!) (d/dz)^m Δ(z;k)^l`, where the right-hand side is read as the `m`-th
Taylor coefficient of `Δ(X;k)^l` at `z`.

`Theta` is `aeval z (hasseDeriv m (deltaPoly k ^ l))`; pushing `aeval` past the Hasse derivative
(`Polynomial.aeval_def`, `Polynomial.eval₂_eq_eval_map`, `Polynomial.hasseDeriv_map`) turns it into
`eval z (hasseDeriv m ((deltaPoly k ^ l).map (algebraMap ℚ ℂ)))`, and `Polynomial.taylor_coeff`
identifies that with the `m`-th Taylor coefficient. -/
theorem Theta_eq_taylor_coeff (z : ℂ) (k l m : ℕ) :
    Theta z k l m
      = (Polynomial.taylor z ((deltaPoly k ^ l).map (algebraMap ℚ ℂ))).coeff m := by
  rw [Theta, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Polynomial.hasseDeriv_map,
    Polynomial.taylor_coeff]

end Work.BW
