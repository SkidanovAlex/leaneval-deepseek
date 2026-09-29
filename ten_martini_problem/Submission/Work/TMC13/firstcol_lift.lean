import Mathlib
import Submission.Work.TMC13.Defs

namespace Work.TMC13

open Work.TMComp.RotBasics

theorem firstcol_lift {A : Matrix (Fin 2) (Fin 2) ℝ} {r η : ℝ} (hr : 0 < r)
    (h00 : A 0 0 = r * Real.cos (2 * Real.pi * η))
    (h10 : A 1 0 = r * Real.sin (2 * Real.pi * η)) :
    Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc 0) /
      (↑‖Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc 0)‖ : ℂ) =
        Work.TMComp.RotBasics.vc (2 * η) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hvc0 : vc (0 : ℝ) = 1 := by
    refine Complex.ext ?_ ?_ <;> simp [vc]
  have hsmul : smul A (vc 0) =
      ⟨r * Real.cos (2 * Real.pi * η), r * Real.sin (2 * Real.pi * η)⟩ := by
    rw [hvc0]
    refine Complex.ext ?_ ?_
    · simp [smul, h00]
    · simp [smul, h10]
  have hnorm : ‖smul A (vc 0)‖ = r := by
    rw [hsmul]
    have h : ‖(⟨r * Real.cos (2 * Real.pi * η), r * Real.sin (2 * Real.pi * η)⟩ : ℂ)‖ ^ 2
        = r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * η)]
    nlinarith [norm_nonneg (⟨r * Real.cos (2 * Real.pi * η),
      r * Real.sin (2 * Real.pi * η)⟩ : ℂ), hr]
  rw [hnorm, hsmul]
  have hvc2 : vc (2 * η) = ⟨Real.cos (2 * Real.pi * η), Real.sin (2 * Real.pi * η)⟩ := by
    refine Complex.ext ?_ ?_ <;> simp [vc, show Real.pi * (2 * η) = 2 * Real.pi * η by ring]
  rw [hvc2]
  rw [div_eq_iff (by exact_mod_cast hrne : (↑r : ℂ) ≠ 0)]
  refine Complex.ext ?_ ?_ <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

end Work.TMC13
