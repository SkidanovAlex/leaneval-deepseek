import Mathlib
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2Lead.polarCurve_rows
import Submission.Work.Drive.N2Lead.saddlePacket

/-!
# The marked curve of the saddle packet and the rows `packetCurves` consumes

`Work.Drive.N2Lead.polarCurve_rows` proves the four rows (smoothness, `1`-periodicity, injectivity
modulo one period, nonvanishing velocity) of the polar curve `C₀ t = cE3 (r (Θ t) * exp (i Θ t))`.
`Work.Drive.N2Lead.packetCurves` additionally needs the *norm* bound `‖C₀ t‖ ≤ R` (with `19 < R`
false — the bound is used against the parked circles, so `R < 19`).

This file provides `saddleMarkedCurve`, the conjunction of the five rows in the exact shape of the
hypotheses of `packetCurves`, and its twisted variant `saddleMarkedCurveTwist` (the Möbius case
`twistY a' 1 ∘ C₀`, an isometry, so the norm bound is unchanged).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The planar inclusion `cE3 : ℂ → ℝ³` is an isometry onto the plane `{z = 0}`. -/
lemma norm_cE3_marked (z : ℂ) : ‖Work.Drive.N2.cE3 z‖ = ‖z‖ := by
  have h2 : ‖Work.Drive.N2.cE3 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
    simp only [Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_one,
      Work.Drive.N2.cE3_apply_two, Real.norm_eq_abs, sq_abs]
    ring
  nlinarith [norm_nonneg (Work.Drive.N2.cE3 z), norm_nonneg z]

/-- The polar curve `t ↦ cE3 (r (Θ t) * exp (i Θ t))` of the packet, with all five rows. -/
theorem saddleMarkedCurve {r Θ : ℝ → ℝ} {R : ℝ}
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) ∧
      (∀ t : ℝ, r (Θ (t + 1)) * Complex.exp (((Θ (t + 1) : ℝ) : ℂ) * Complex.I)
        = r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) ∧
      (∀ s t : ℝ, r (Θ s) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
          = r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) → ∃ k : ℤ, s = t + k) ∧
      (∀ t : ℝ, deriv (fun u : ℝ =>
        Work.Drive.N2.cE3 (r (Θ u) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))) t ≠ 0) ∧
      (∀ t : ℝ, ‖Work.Drive.N2.cE3
        (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))‖ ≤ R) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    Work.Drive.N2Lead.polarCurve_rows hr hrpos hrper hΘ hΘmono hΘderiv hΘper
  refine ⟨h1, h2, h3, h4, fun t => ?_⟩
  have hn : ‖r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ = r (Θ t) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [Complex.norm_of_nonneg (le_of_lt (hrpos (Θ t)))]
  rw [norm_cE3_marked, hn]
  exact hrR (Θ t)

end

end Work.Drive.N2Lead
