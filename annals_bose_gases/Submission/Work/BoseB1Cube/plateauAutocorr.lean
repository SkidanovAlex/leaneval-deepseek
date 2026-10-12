import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.pairMassB_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseB1Cube

/-! # The autocorrelation of the sliding cutoff is the rescaled self-convolution of the bump

`Work.BoseFixB1.autocorr ℓ d u z = ∫_x χ_B(x)·χ_B(x − z)` with
`χ_B = Submission.BoseGases.chiSmallB M ℓ d u`.  The hypothesis `hχ` says that on the plateau
of the two-factor cutoff the `ℓ`-scale factor `χ(x/ℓ)` equals its sup `chiSupAbs`
(equivalently `chiScale ℓ = chiSupAbs` pointwise), so that `χ_B` is *exactly* the
`(ℓd)`-rescaled cosine bump.  The autocorrelation is then, after the substitution
`x = (ℓd)·(y + u)`, the self-convolution of the bump at the rescaled shift:

    ∫_x χ_B(x)χ_B(x − z) = chiSupAbs² · (ℓd)³ · ∫_y χ_M(y)·χ_M(y − (ℓd)⁻¹·z)
                          = chiSupAbs² · (ℓd)³ · conv3Small M ((ℓd)⁻¹ • z) .

The last step uses the evenness of `χ_M` to swap the argument of the second factor. -/

theorem plateauAutocorr {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hχ : ∀ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.chiSmallB M ℓ d u x
          = Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.autocorr (M := M) ℓ d u z
      = Submission.BoseGases.chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • z) := by
  have hc : (0:ℝ) < ℓ * d := mul_pos hℓ hd
  set w : EuclideanSpace ℝ (Fin 3) := (ℓ * d)⁻¹ • z with hw
  set G : EuclideanSpace ℝ (Fin 3) → ℝ := fun y =>
    Submission.BoseGases.chiSmall M y * Submission.BoseGases.chiSmall M (y - w) with hG
  -- the integrand of the autocorrelation, rewritten by `hχ`
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u (x - z)
        = Submission.BoseGases.chiSupAbs ^ 2 * G ((ℓ * d)⁻¹ • x - u) := by
    intro x
    rw [hχ x, hχ (x - z), hG]
    have harg : (ℓ * d)⁻¹ • (x - z) - u = ((ℓ * d)⁻¹ • x - u) - w := by
      rw [hw, smul_sub]; abel
    rw [harg]
    ring
  -- the self-convolution form: evenness of `χ_M` puts the shift on the right
  have hGint : (∫ y : EuclideanSpace ℝ (Fin 3), G y)
      = Submission.BoseGases.conv3Small M w := by
    rw [hG, Submission.BoseGases.conv3Small]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [show y - w = -(w - y) by abel, ← Submission.BoseGases.chiSmall_even hM (w - y)]
  -- the substitution `x = (ℓd)·(s + u)`
  have hmain : (∫ x : EuclideanSpace ℝ (Fin 3), G ((ℓ * d)⁻¹ • x - u))
      = (ℓ * d) ^ 3 * Submission.BoseGases.conv3Small M w := by
    rw [Submission.BoseGases.integral_comp_smul_right
      (fun x : EuclideanSpace ℝ (Fin 3) => G ((ℓ * d)⁻¹ • x - u)) hc]
    have hsimp : ∀ s : EuclideanSpace ℝ (Fin 3),
        G ((ℓ * d)⁻¹ • ((ℓ * d) • s) - u) = G (s - u) := by
      intro s
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    simp only [hsimp]
    rw [MeasureTheory.integral_sub_right_eq_self G u, hGint]
  rw [Work.BoseFixB1.autocorr_apply]
  simp only [hpoint]
  rw [MeasureTheory.integral_const_mul, hmain]
  ring

end Work.BoseB1Cube
