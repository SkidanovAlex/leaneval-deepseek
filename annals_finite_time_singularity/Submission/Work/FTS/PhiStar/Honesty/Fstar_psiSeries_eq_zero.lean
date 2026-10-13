import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero_corrected
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero` — the moment conjunct `F_*(Ψ) ≡ 0`

`EllWeakPos α k F Ψ` (and every consumer in the `MixHon`/`Ae` chain) needs the angular moment
`F_*(Ψ) z = ∫_θ Ψ z θ · sinθcos²θ dθ` of the modal solution to vanish, i.e.

  `F_*(psiSeries α F) z = 0` for `z > 0`, from the source's moment `F_*(F) ≡ 0` on `z > 0`.

## The hypothesis `0 < z` is necessary (a review-gate catch)

The statement *without* the hypothesis `0 < z` is **FALSE**: `F_*(psiSeries α F) z` reduces
(`Fstar_psiSeries_eq_tsum`, `eFam_orthogonal`) to `acoeff α 0 F z · 3∫_0^{π/2} sin²θcos³θ dθ`,
and `acoeff α 0 F z = radGreen α 0 (cmode 0 F) z` integrates `cmode 0 F` — a multiple of `F_*(F)`
— over `(z, ∞)`; for `z < 0` that interval contains the negative half-line, about which the
source hypothesis says nothing.  A machine-checked witness is
`Work.FTS.PhiStar.Honesty.Fstar_psiSeries_counterexample`
(`Submission/Work/FTS/PhiStar/Honesty/Fstar_psiSeries_counterexample.lean`, `sorry`-free):
`α = 1`, `z = -1`, `F(t,θ) = 1_{(-1,-1/2)}(t)·(3 sinθcosθ)`.

With `0 < z` — exactly the form in which the node's hypothesis is stated
(`bslOp_sol_exists`: `(∀ z, 0 < z → F_*(F) z = 0)`) — the statement is true, and it is proved
below from the honest forms collected in `Fstar_psiSeries_eq_zero_corrected.lean`
(`Fstar_psiSeries_eq_zero_of_pos`, and the all-`z` variants
`…_of_moment_all`, `…_of_left_support` for sources vanishing on `z ≤ 0`).
-/

namespace Work.FTS.PhiStar.Honesty

/-- **The angular moment of the modal series vanishes at every `z > 0`**, from the vanishing of
the source's moment on the positive half-line (`acoeff α 0 F z = 0`, since the Green function
`radGreen α 0` only sees `z' > 0` when `z > 0`) and the weighted summability of the coefficients
(the zeroth-slot `hcoef` of the honesty capstones). -/
theorem Fstar_psiSeries_eq_zero {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  Fstar_psiSeries_eq_zero_of_pos hz hsum hF

end Work.FTS.PhiStar.Honesty
