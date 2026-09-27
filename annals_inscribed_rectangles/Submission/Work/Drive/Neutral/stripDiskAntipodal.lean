import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataChord_spec

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- `Circle.exp` is periodic with period `2 * π`. -/
lemma circle_exp_add_two_pi (t : ℝ) : Circle.exp (t + 2 * Real.pi) = Circle.exp t := by
  rw [Circle.exp_eq_exp]
  exact ⟨1, by push_cast; ring⟩

/-- `exp (θ + 3π/2) = exp (θ - π/2)` on the circle. -/
lemma circle_exp_three_pi_div_two (θ : ℝ) :
    Circle.exp (θ + Real.pi + Real.pi / 2) = Circle.exp (θ - Real.pi / 2) := by
  rw [show θ + Real.pi + Real.pi / 2 = (θ - Real.pi / 2) + 2 * Real.pi by ring]
  exact circle_exp_add_two_pi _

/-- The argument of a nonzero complex number is a continuous argument. -/
lemma exp_arg_eq_div_norm (x : ℂ) (hx : x ≠ 0) :
    (Circle.exp (Complex.arg x) : ℂ) = x / (‖x‖ : ℂ) := by
  rw [← toCirc_eq_exp_arg x hx, toCirc_coe]

/-- Shifting the argument by `π` gives an argument of `-x`. -/
lemma exp_arg_add_pi_eq_div_norm (x : ℂ) (hx : x ≠ 0) :
    (Circle.exp (Complex.arg x + Real.pi) : ℂ) = (-x) / (‖-x‖ : ℂ) := by
  rw [Circle.exp_add, Circle.coe_mul, exp_arg_eq_div_norm x hx, Circle.coe_exp,
    Complex.exp_pi_mul_I, norm_neg, mul_neg_one, neg_div]

lemma sClamp_half_pi : sClamp (Real.pi / 2) = Real.pi / 2 := by
  rw [sClamp_eq_self (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)])]

/-- At the opening `π/2` the two chord endpoints of the antipodal parameter are exchanged:
this is the pointwise core of `stripDiskAntipodal`. -/
lemma curvePtAt_half_pi_eq (γ : Circle → ℝ × ℝ) (x : ℂ) (hx : x ≠ 0) :
    curvePtAt γ x (Real.pi / 2) = symmC (curve γ (Complex.arg x + Real.pi / 2)) ∧
      curvePtAt γ x (-(Real.pi / 2)) = symmC (curve γ (Complex.arg x - Real.pi / 2)) ∧
      curvePtAt γ (-x) (Real.pi / 2) = symmC (curve γ (Complex.arg x - Real.pi / 2)) ∧
      curvePtAt γ (-x) (-(Real.pi / 2)) = symmC (curve γ (Complex.arg x + Real.pi / 2)) := by
  have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [curvePtAt_eq_exp γ x hx (exp_arg_eq_div_norm x hx) (Real.pi / 2), sClamp_half_pi]
  · rw [curvePtAt_eq_exp γ x hx (exp_arg_eq_div_norm x hx) (-(Real.pi / 2)), sClamp_odd,
      sClamp_half_pi]
    congr 1
  · rw [curvePtAt_eq_exp γ (-x) hx' (exp_arg_add_pi_eq_div_norm x hx) (Real.pi / 2),
      sClamp_half_pi]
    congr 1
    exact congrArg γ (circle_exp_three_pi_div_two _)
  · rw [curvePtAt_eq_exp γ (-x) hx' (exp_arg_add_pi_eq_div_norm x hx) (-(Real.pi / 2)),
      sClamp_odd, sClamp_half_pi]
    congr 1
    rw [show (Complex.arg x + Real.pi) + -(Real.pi / 2) = Complex.arg x + Real.pi / 2 by ring]

theorem stripDiskAntipodal (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    (∀ x : ℂ, x ≠ 0 →
        Work.Drive.Neutral.dataChord γ (-x) (Real.pi / 2) = -Work.Drive.Neutral.dataChord γ x (Real.pi / 2)) ∧
      (∀ x : ℂ, x ≠ 0 →
        Work.Drive.Neutral.dataMid γ (-x) (Real.pi / 2) = Work.Drive.Neutral.dataMid γ x (Real.pi / 2)) ∧
      (∀ x : ℂ, x ≠ 0 →
        Work.Drive.Neutral.dchW γ (-x, Real.pi / 2) = -Work.Drive.Neutral.dchW γ (x, Real.pi / 2)) := by
  have hchord : ∀ x : ℂ, x ≠ 0 →
      dataChord γ (-x) (Real.pi / 2) = -dataChord γ x (Real.pi / 2) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := curvePtAt_half_pi_eq γ x hx
    have hL : dataChord γ (-x) (Real.pi / 2)
        = symmC (curve γ (Complex.arg x - Real.pi / 2))
          - symmC (curve γ (Complex.arg x + Real.pi / 2)) := by
      rw [dataChord, endPlus, endMinus, h3, h4]
    have hR : dataChord γ x (Real.pi / 2)
        = symmC (curve γ (Complex.arg x + Real.pi / 2))
          - symmC (curve γ (Complex.arg x - Real.pi / 2)) := by
      rw [dataChord, endPlus, endMinus, h1, h2]
    rw [hL, hR]; ring
  have hmid : ∀ x : ℂ, x ≠ 0 →
      dataMid γ (-x) (Real.pi / 2) = dataMid γ x (Real.pi / 2) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := curvePtAt_half_pi_eq γ x hx
    have hL : dataMid γ (-x) (Real.pi / 2)
        = (symmC (curve γ (Complex.arg x - Real.pi / 2))
            + symmC (curve γ (Complex.arg x + Real.pi / 2))) / 2 := by
      rw [dataMid, endPlus, endMinus, h3, h4]
    have hR : dataMid γ x (Real.pi / 2)
        = (symmC (curve γ (Complex.arg x + Real.pi / 2))
            + symmC (curve γ (Complex.arg x - Real.pi / 2))) / 2 := by
      rw [dataMid, endPlus, endMinus, h1, h2]
    rw [hL, hR]; ring
  have hW : ∀ x : ℂ, x ≠ 0 →
      dchW γ (-x, Real.pi / 2) = -dchW γ (x, Real.pi / 2) := by
    intro x hx
    have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
    have hA : (Real.pi / 2) • dchW γ (-x, Real.pi / 2) = -dataChord γ x (Real.pi / 2) := by
      rw [dchW_smul γ hγ hx' (Real.pi / 2), hchord x hx]
    have hB : (Real.pi / 2) • (-(dchW γ (x, Real.pi / 2))) = -dataChord γ x (Real.pi / 2) := by
      rw [smul_neg, dchW_smul γ hγ hx (Real.pi / 2)]
    have hkey : (Real.pi / 2) • dchW γ (-x, Real.pi / 2)
        = (Real.pi / 2) • (-(dchW γ (x, Real.pi / 2))) := by rw [hA, hB]
    exact smul_right_injective ℂ (by positivity : (Real.pi / 2 : ℝ) ≠ 0) hkey
  exact ⟨hchord, hmid, hW⟩

end

end Work.Drive.Neutral
