import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.Q4x_eval_xs
import Submission.Work.C17.Pfun_hasSum
import Submission.Work.C17.logP_not_holomorphic_at_xs
import Submission.Work.C17.beukersEta_irrational
import Submission.Work.C17.logP_local_structure
import Submission.Work.C17g.pringsheim

namespace Work.C17

/-- The local (ACL-a) structure of the unlikely series `Pfun` at its cusp `x_s`, in the
normalisation used by the C17 assembly: for `a, b` admissible, and a relation
`r_a η_a + r_b η_b + r_ab η_a η_b = r₀` with `r_ab ≠ 0`, there are `δ > 0` with `2δ ≤ x_s` and
`2δ ≤ 1 − x_s`, `κ ≠ 0`, a solution `y₁` of `M` holomorphic and non-vanishing on `ball x_s δ`,
and `hh` holomorphic on `ball x_s δ`, with `Pfun = κ·y₁·log(x_s − ·) + hh` on
`ball x_s δ ∩ ball 0 x_s`. -/
theorem acl_a_local (a b : ℚ) (hA : Work.C17.AdmQ a b) (ra rb rab r0 : ℤ) (hrab : rab ≠ 0)
    (hrel : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ)
        + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
      = (r0 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ ≤ Work.C17.xs a b ∧ 2 * δ ≤ 1 - Work.C17.xs a b ∧
      ∃ (κ : ℂ) (y1 hh : ℂ → ℂ), κ ≠ 0 ∧ y1 ((Work.C17.xs a b : ℝ) : ℂ) ≠ 0 ∧
        DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ) ∧
        DifferentiableOn ℂ hh (Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ) ∧
        (∀ z ∈ Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ,
          (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
            + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
            + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0) ∧
        (∀ z ∈ Metric.ball ((Work.C17.xs a b : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xs a b),
          Work.C17.Pfun a b ra rb rab r0 z
            = κ * y1 z * Complex.log (((Work.C17.xs a b : ℝ) : ℂ) - z) + hh z) := by

  obtain ⟨ha, hab, _hgap, m, n, _ham, _hbn⟩ := hA
  have hb : 3 ≤ b := by linarith
  -- the four analytic inputs of `logP_local_structure`, derived from `AdmQ` + the relation
  have hQ4 : (Q4x a b).eval₂ (algebraMap ℚ ℂ) ((xs a b : ℝ) : ℂ) = 0 :=
    Q4x_eval_xs a b ha hb hab
  have hconv : ∀ z : ℂ, ‖z‖ < xs a b →
      HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
        (Pfun a b ra rb rab r0 z) :=
    Pfun_hasSum a b ha hb hab ra rb rab r0 hrel
  have heta : Irrational (Submission.CDT.beukersEta (b : ℝ)) :=
    beukersEta_irrational_rat b (by linarith)
  have hprings : ∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) → ∀ (R : ℝ), 0 < R →
      (∀ r : ℝ, 0 ≤ r → r < R → Summable fun n => f n * r ^ n) →
      ∀ (g : ℂ → ℂ) (δ : ℝ), 0 < δ → DifferentiableOn ℂ g (Metric.ball (R : ℂ) δ) →
      (∀ z ∈ Metric.ball (R : ℂ) δ ∩ Metric.ball (0 : ℂ) R,
        HasSum (fun n => (f n : ℂ) * z ^ n) (g z)) →
      ∃ ρ : ℝ, R < ρ ∧ Summable fun n => f n * ρ ^ n :=
    fun f hf R hR hsum g δ hδ hg hfg =>
      Work.C17g.pringsheim f hf R hR hsum g δ hδ hg hfg
  have hnot : ¬ ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧
      DifferentiableOn ℂ g (Metric.ball ((xs a b : ℝ) : ℂ) δ) ∧
      ∀ z ∈ Metric.ball ((xs a b : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b),
        g z = Pfun a b ra rb rab r0 z := by
    rintro ⟨g, δ, hδ, hg, hcont⟩
    exact logP_not_holomorphic_at_xs a b ha hb hab ra rb rab r0 hrab hrel heta hprings
      hδ g hg hcont
  obtain ⟨δ₀, hδ₀, κ, y1, hh, hκ, hy1s, hy1d, hhd, hode, heq⟩ :=
    logP_local_structure a b ha hb hab ra rb rab r0 hQ4 hconv hnot
  -- the radius is shrunk so that `2δ ≤ x_s` and `2δ ≤ 1 − x_s`
  obtain ⟨hxs_pos, hxs_sq_lt_one⟩ := xs_pos_and_sq_lt_one a b ha hb hab
  have hxs_lt_one : xs a b < 1 := by nlinarith
  set δ : ℝ := min δ₀ (min (xs a b / 2) ((1 - xs a b) / 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hδ₀ (lt_min (by linarith) (by linarith))
  have hδle : δ ≤ δ₀ := by rw [hδdef]; exact min_le_left _ _
  have hδsub : δ ≤ min (xs a b / 2) ((1 - xs a b) / 2) := by
    rw [hδdef]; exact min_le_right _ _
  have hδ2 : 2 * δ ≤ xs a b := by
    have := le_trans hδsub (min_le_left (xs a b / 2) ((1 - xs a b) / 2)); linarith
  have hδ3 : 2 * δ ≤ 1 - xs a b := by
    have := le_trans hδsub (min_le_right (xs a b / 2) ((1 - xs a b) / 2)); linarith
  refine ⟨δ, hδpos, hδ2, hδ3, κ, y1, hh, hκ, hy1s, ?_, ?_, ?_, ?_⟩
  · exact hy1d.mono (Metric.ball_subset_ball hδle)
  · exact hhd.mono (Metric.ball_subset_ball hδle)
  · intro z hz
    exact hode z (Metric.ball_subset_ball hδle hz)
  · intro z hz
    exact heq z ⟨Metric.ball_subset_ball hδle hz.1, hz.2⟩


end Work.C17
