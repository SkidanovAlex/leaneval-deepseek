/-
# `Work.FTS.PhiStar.Series.ResolventSetup` — the per-mode resolvent identity

`Work.FTS.PhiStar.Radial.radGreen_solves` says that `R_m := radGreen α m c` solves the mode-`m`
Euler equation

  `-α²z²R_m'' - α(5+α)zR_m' + λ_m R_m = c`     (`z > 0`),

which rearranged is the *resolvent identity*

  `λ_m R_m = c + A R_m`,   `A a := α²z²a'' + α(5+α)za'`.

This is the algebraic seed of the resummation used for the proof of
`Work.FTS.PhiStar.Series.psiSeries_solves_rem`: iterating it `J` times gives

  `R_m = Σ_{i<J} (A^i c)/λ_m^{i+1} + (A^J R_m)/λ_m^J`,

whose front terms are the *explicit* functions `A^i c = α^i · phiAj (i+1) α` paired with the
resummed angular functions `Ψ_{i+1}` (see `Series/NOTES_psiSeries_solves_rem.md` §3–§4).

Also recorded here: the `AngModel` form of the vanishing of the `m = 0` mode coefficient.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- **The per-mode resolvent identity**: `λ_m · radGreen α m c z = c z + A (radGreen α m c) z`,
where `A a := α²z²a'' + α(5+α)za'`. -/
theorem radGreen_resolvent (α : ℝ) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hα : 0 < α) (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 *
            deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
  have h := Work.FTS.PhiStar.Radial.radGreen_solves hα m hc h0 h0' hinf z hz
  have h' : Work.FTS.PhiStar.Radial.lamR m
        * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + (α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          + α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) := by
    linarith [h]
  exact h'

/-- The `m = 0` mode coefficient of `psiSeries` for the remainder source vanishes under
`AngModel α ψ`: the source moment `Fstar (RemSource α ψ)` is `α² phiA α z ·∫ψ·sinCos2`. -/
theorem acoeff_RemSource_zero_of_angModel (α : ℝ) (ψ : ℝ → ℝ)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ z, 0 < z → acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z = 0 := by
  refine acoeff_zero_of_fstar α (Work.FTS.PhiStar.RemSource α ψ) (fun t _ => ?_)
  rw [Fstar_RemSource, hψ.moment, mul_zero]

end Work.FTS.PhiStar.Series
