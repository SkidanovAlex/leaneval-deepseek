import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.eta_mul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.e23A_mul_aSq` — the monomial identity for `a²·e23A`

The error bracket `e23A E = E0 E · (η K_L³ K_ℓ^{3/2} (μa³)^{1/4})` with
`E0 E = μ²aℓ³` (`Work.BoseB7AK.Defs`).  At FS's §10 parameter point
(`Work.BoseB7.FSParamsView E`) every factor is a monomial in `X = (μa³)^{1/323}`:

* `μ²a³ℓ³ = (μa³)(μℓ³) = X^{323}·X^{-166} = X^{157}`
  (the second factor is `Work.BoseB7.mue_val`),
* `η = X^{1236}` (`eta_eq`), `K_L³ = X^{-63/2}` (`KL_val`),
  `K_ℓ^{3/2} = X^{-9/4}` (`Kl_val`), `(μa³)^{1/4} = X^{323/4}` (`dil_val`),

so

`a²·e23A E = a²·E0 E·(…) = μ²a³ℓ³ · η K_L³ K_ℓ^{3/2}(μa³)^{1/4} = X^{1440}`.

The exponent is exact: `157 + 1236 - 63/2 - 9/4 + 323/4 = 1440`.

## Contents

* `mu_sq_aSq_cube_ell_cube` — `μ²a³ℓ³ = X^{157}`.
* `e23A_mul_aSq` — the requested identity.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7 Work.BoseBox

/-- `μ²a³ℓ³ = (μa³)(μℓ³) = X^{323}·X^{-166} = X^{157}` at the parameter point
`t = μa³`. -/
lemma mu_sq_aSq_cube_ell_cube {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.FSParamsView E) :
    E.mu ^ 2 * E.aScat ^ 3 * E.ell ^ 3 = fsXp h.t 157 := by
  have hma : E.mu * E.aScat ^ 3 = fsXp h.t 323 := by
    rw [h.mu_eq]; exact delta_eq_fsXp h.t_pos.le
  calc E.mu ^ 2 * E.aScat ^ 3 * E.ell ^ 3
      = (E.mu * E.aScat ^ 3) * (E.mu * E.ell ^ 3) := by ring
    _ = fsXp h.t 323 * fsXp h.t (-166) := by rw [hma, mue_val E h]
    _ = fsXp h.t 157 := by rw [fsXp_mul h.t_pos]; congr 1; norm_num

theorem e23A_mul_aSq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    E.aScat ^ 2 * Work.BoseC3QAll.e23A E = Work.BoseBox.fsXp hv.t 1440 := by
  have hE0 : E.aScat ^ 2 * E0 E = fsXp hv.t 157 := by
    rw [E0, ← mu_sq_aSq_cube_ell_cube E hv]; ring
  calc E.aScat ^ 2 * e23A E
      = (E.aScat ^ 2 * E0 E) *
          (eta E * E.KL ^ 3 * E.Kl ^ ((3 : ℝ) / 2) * dil E (1 / 4)) := by
        rw [e23A]; ring
    _ = fsXp hv.t 157 * (fsXp hv.t 1236 * (fsXp hv.t (-(21 / 2))) ^ 3 *
          (fsXp hv.t (-(3 / 2))) ^ ((3 : ℝ) / 2) * fsXp hv.t (323 * (1 / 4))) := by
        rw [hE0, eta_eq E hv, KL_val E hv, Kl_val E hv, dil_val E hv (1 / 4)]
    _ = fsXp hv.t 1440 := by
        rw [fsXp_pow hv.t_pos.le (-(21 / 2)) 3, fsXp_rpow hv.t_pos.le (-(3 / 2)) (3 / 2)]
        simp only [fsXp_mul hv.t_pos]
        congr 1
        norm_num

end Work.BoseC3QAll
