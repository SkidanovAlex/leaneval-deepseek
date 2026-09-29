import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.evp_add_mul
import Submission.Work.CPull.powerSeries_hasDerivAt
import Submission.Work.CPull.evp_B2_ode
import Submission.Work.B5pull.powser_deriv
import Submission.Work.B5pull.series_ode
import Submission.Work.B5pull.b5_coeff_rec_c
import Submission.Work.Pure.b5_rel
import Submission.Work.Pure.b4_B2_ode

/-!
# The analytic ODEs of the pullbacks `evp B₂` and `evp B₅` on the disc of radius `4`

`Submission.CDTPlan.B2`, `Submission.CDTPlan.B5` are the pure series of the paper
(Calegari--Dimitrov--Tang, arXiv:2408.15403), and `Work.Pure.b4_B2_ode`, `Work.Pure.b5_rel` are
the *formal* differential relations

`X·(4 - X)·B₂' = (2 - X)·B₂ + X²`,
`2·X·(4 - X)·B₅' = (4 - X)·B₅ - 2·B₂ + 4·X`.

Here we transfer them to the analytic functions `y ↦ evp B₂ y = Σ cₙ yⁿ` and
`y ↦ evp B₅ y` on the true disc of convergence `‖y‖ < 4`:

* the coefficient bound hypothesis `h2`/`h5` gives, by the term-by-term differentiation lemma
  `Work.CPull.powerSeries_hasDerivAt`, the summability of the coefficient series (and of the
  derivative series) and the identity `deriv (evp f) y = Σ (n+1) cₙ₊₁ yⁿ`;
* the coefficient recurrence extracted from the formal relation together with the
  series-to-ODE lemma `Work.B5pull.series_ode` gives the analytic equation.

The `B₂` half is nothing but the third component of `Work.CPull.evp_B2_ode`, which already
performs exactly this transfer; the `B₅` half is assembled here from the recurrence
`Work.B5pull.b5_coeff_rec_c` (coefficient-wise form of `Work.Pure.b5_rel`) and the general
lemma `Work.B5pull.series_ode`.
-/

namespace Work.B5pull

theorem evp_ode {C2 C5 : ℝ} (hC2 : 0 < C2) (hC5 : 0 < C5)
    (h2 : ∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ C2 * (1 / 4 : ℝ) ^ n)
    (h5 : ∀ n : ℕ, ‖((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)‖ ≤ C5 * (1 / 4 : ℝ) ^ n) :
    (∀ y : ℂ, ‖y‖ < 4 → y * (4 - y) * deriv (fun z : ℂ => Work.CPull.evp Submission.CDTPlan.B2 z) y
        = (2 - y) * Work.CPull.evp Submission.CDTPlan.B2 y + y ^ 2) ∧
    (∀ y : ℂ, ‖y‖ < 4 → 2 * y * (4 - y) * deriv (fun z : ℂ => Work.CPull.evp Submission.CDTPlan.B5 z) y
        = (4 - y) * Work.CPull.evp Submission.CDTPlan.B5 y
          - 2 * Work.CPull.evp Submission.CDTPlan.B2 y + 4 * y) := by
  constructor
  · -- The `B₂` equation: the disc `‖y‖ < 4` is `Metric.ball 0 4`.
    intro y hy
    exact Work.CPull.evp_B2_ode.2.2 y (by rwa [Metric.mem_ball, dist_zero_right])
  · -- The `B₅` equation: summability of the coefficient series from the bound `h5`/`h2`,
    -- the recurrence from the formal relation, then `series_ode`.
    intro y hy
    have hB5 := Work.CPull.powerSeries_hasDerivAt
      (fun n => ((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)) C5 hC5 h5
    have hB2 := Work.CPull.powerSeries_hasDerivAt
      (fun n => ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)) C2 hC2 h2
    exact series_ode _ _ y (fun n => b5_coeff_rec_c n) (hB5.1 y hy) (hB5.2.1 y hy)
      (hB5.2.2.1 y hy) (hB2.1 y hy) (hB5.2.2.2 y hy).deriv

end Work.B5pull
