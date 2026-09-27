import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs

namespace Work.Mostow.gapA

theorem tubeSubsetTb (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (η₁ R : ℝ) (hη₁ : 0 < η₁)
    (hR : 2 * Real.arsinh (Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ))) < η₁) :
    {u : Submission.Mostow.E 3 | Work.Mostow.distGeod a b u ≤ R} ⊆ Work.Mostow.Tb b₀ η₁ := by
  intro u hu v hv
  have hu' : Work.Mostow.distGeod a b u ≤ R := hu
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hsin : 0 ≤ Real.sin (Real.pi / (M : ℝ)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · rw [div_le_iff₀ hMpos]; nlinarith [Real.pi_pos, hM1]
  have hdisp : Submission.Mostow.hdist v (b₀ • v) =
      2 * Real.arsinh (Real.sinh (Work.Mostow.distGeod a b v) * Real.sin (Real.pi / (M : ℝ))) := by
    have h := hrot.2 v
    rwa [show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) from by ring] at h
  rw [hdisp]
  have hvh : Work.Mostow.distGeod a b v ≤ R + 1 := by
    have h := distGeod_abs_sub_le a b hI ha hb hab u v
    have h1 : Work.Mostow.distGeod a b v - Work.Mostow.distGeod a b u ≤ Submission.Mostow.hdist u v := by
      have h2 := le_abs_self (Work.Mostow.distGeod a b v - Work.Mostow.distGeod a b u)
      rw [abs_sub_comm] at h2
      exact le_trans h2 h
    linarith [hv, hu']
  have hsinh_le : Real.sinh (Work.Mostow.distGeod a b v) ≤ Real.sinh (R + 1) :=
    Real.sinh_le_sinh.mpr hvh
  have hprod : Real.sinh (Work.Mostow.distGeod a b v) * Real.sin (Real.pi / (M : ℝ))
      ≤ Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ)) :=
    mul_le_mul_of_nonneg_right hsinh_le hsin
  have hars : Real.arsinh (Real.sinh (Work.Mostow.distGeod a b v) * Real.sin (Real.pi / (M : ℝ)))
      ≤ Real.arsinh (Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ))) :=
    Real.arsinh_le_arsinh.mpr hprod
  linarith [hR]

end Work.Mostow.gapA
