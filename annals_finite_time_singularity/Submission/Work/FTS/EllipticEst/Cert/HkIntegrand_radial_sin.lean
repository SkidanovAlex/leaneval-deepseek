/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ^k`-integrand of a separated function `R(z)·sin 2θ`

Identifies the general definition `Work.Spaces.HkIntegrand α k (fun z θ => R z * sin 2θ)`
with the separated form `HkExp α k R` of `Cert/Defs.lean`.  The two ingredients are

* `DzIter_fstarSin_eq` / `mixed_fstarSin_eq` (module `OpenQAux`): `D_z` resp. the mixed
  `D_z^j D_θ^i` act as `radIter R j z` resp. `radIter R j z · sinProf i θ`;
* `FstarHkOpen.zTerm_eq_on` / `FstarHkOpen.mixedTerm_eq_on` (module `OpenQAng`): the two
  kinds of summand evaluate, on `Iθ`, to `Ψ² w² sin(2θ)^{2-η}` resp.
  `Ψ² w² (sinProf i θ)² sin(2θ)^{-γ}`.

Both identities hold only on `Iθ` (they use `sin(2θ) ≥ 0`), which is why the hypothesis
`hθ : θ ∈ Iθ` is needed.  The statement is purely definitional otherwise.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

theorem HkIntegrand_radial_sin (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
      = Work.FTS.EllipticEst.Cert.HkExp α k R z θ := by
  rw [Work.Spaces.HkIntegrand, HkExp]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.EllipticEst.DzIter_fstarSin_eq]
    exact Work.FTS.EllipticEst.FstarHkOpen.zTerm_eq_on (Work.FTS.EllipticEst.radIter R i z)
      z θ hθ
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, Work.FTS.EllipticEst.mixed_fstarSin_eq]
      exact Work.FTS.EllipticEst.FstarHkOpen.mixedTerm_eq_on α
        (Work.FTS.EllipticEst.radIter R j z) z (Work.FTS.EllipticEst.sinProf i) θ hθ
    · rw [if_neg hc, if_neg hc]

end Work.FTS.EllipticEst.Cert
