import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.conv3chi_dev_quadratic
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **`L¹`-bound for the FS §4 kernel `W₁`.**

`W₁ = wScaled ℓ (g0 v h) = g₀/(χ⋆χ)(·/ℓ)` with `g₀ = v(1−ω)`, and in the dilute
regime `R ≤ ℓ·chiR0` the renormalisation factor `(χ⋆χ)(·/ℓ)` is bounded below by
`1/2` on the support `ball 0 R` of `g₀`, so `|W₁| ≤ 2|g₀|` and

    ∫|W₁| ≤ 2∫|g₀| = 2∫g₀ = 16π·(a v)

(the mass identity `∫g₀ = 8π(a v)` being the definition of the scattering length,
`ScatKernelChosen.g0_integral`).  The constant `16π` is the
`wScaled_g0_abs_integral_le` one; the point of the statement below is that
`R ≤ ℓ·chiR0` (with `R > 0`, `chiR0 > 0`) already forces `ℓ > 0`, so no
positivity hypothesis on `ℓ` is needed. -/
theorem W1fun_L1_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ x| ≤ C * BoseGases.a v := by
  refine ⟨16 * Real.pi, by positivity, fun ℓ hRℓ => ?_⟩
  -- `R ≤ ℓ·chiR0` with `R > 0` and `chiR0 > 0` forces `ℓ > 0`
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ : 0 < ℓ := by
    have hpos : 0 < ℓ * Submission.BoseGases.chiR0 := lt_of_lt_of_le hR hRℓ
    nlinarith [hpos, hchi]
  have hbound := Submission.BoseGases.wScaled_g0_abs_integral_le (v := v) (R := R) (ℓ := ℓ)
    hR hv hvrad hv_supp h hℓ hRℓ
  simpa [Work.BoseFixR.W1fun] using hbound

end Work.BoseBoxFock
