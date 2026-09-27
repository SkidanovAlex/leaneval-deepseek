import Mathlib
import Submission.Work.Configuration

open Manifold
open scoped Manifold ContDiff

namespace Work.Drive

open Submission.Collision (dirC)
open Submission.Configuration

/-- The doubled direction is insensitive to reversing the vector (the direction of a line, not of an
oriented vector): `dirC (-p) = dirC p`. -/
theorem dirC_neg (p : ℝ × ℝ) : dirC (-p) = dirC p := by
  unfold dirC
  by_cases hp : (⟨p.1, p.2⟩ : ℂ) = 0
  · have hp' : p = 0 :=
      Prod.ext (by simpa using congrArg Complex.re hp) (by simpa using congrArg Complex.im hp)
    simp [hp']
  · have hneg : (⟨(-p).1, (-p).2⟩ : ℂ) = -(⟨p.1, p.2⟩ : ℂ) := by
      apply Complex.ext <;> simp
    rw [hneg]
    have key : Complex.arg (-(⟨p.1, p.2⟩ : ℂ)) = Complex.arg (⟨p.1, p.2⟩ : ℂ) + Real.pi ∨
        Complex.arg (-(⟨p.1, p.2⟩ : ℂ)) = Complex.arg (⟨p.1, p.2⟩ : ℂ) - Real.pi := by
      rcases lt_trichotomy (⟨p.1, p.2⟩ : ℂ).im 0 with hlt | heq | hgt
      · exact Or.inl (Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inl hlt))
      · rcases lt_trichotomy (⟨p.1, p.2⟩ : ℂ).re 0 with hre | hre | hre
        · exact Or.inr (Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨heq, hre⟩))
        · exfalso
          have hp1 : p.1 = 0 := by simpa using hre
          have hp2 : p.2 = 0 := by simpa using heq
          exact hp (by apply Complex.ext <;> simp [hp1, hp2])
        · exact Or.inl (Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨heq, hre⟩))
      · exact Or.inr (Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inl hgt))
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
      AddCircle.coe_eq_zero_iff (1 : ℝ) |>.mpr ⟨1, by simp⟩
    rcases key with h | h
    · rw [h, add_div, div_self Real.pi_ne_zero, AddCircle.coe_add, hone, add_zero]
    · rw [h, sub_div, div_self Real.pi_ne_zero, AddCircle.coe_sub, hone, sub_zero]

/-- The doubled direction is insensitive to a nonzero real scaling. -/
theorem dirC_smul_ne {c : ℝ} (hc : c ≠ 0) (p : ℝ × ℝ) : dirC (c • p) = dirC p := by
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · have hkey : c • p = (-c) • (-p) := by
      ext <;> simp
    rw [hkey, dirC_smul_pos (by linarith) (-p), dirC_neg]
  · exact absurd heq hc
  · exact dirC_smul_pos hgt p

/-- `0` is always a collision angle: any chord, compared with the reversed chord, gives a coincidence
of midpoints and lengths with the *same* doubled direction. -/
theorem zero_mem_GoodC (γ : Circle → ℝ × ℝ) : (0 : UnitAddCircle) ∈ GoodC γ := by
  refine ⟨1, Circle.exp Real.pi, 1, Circle.exp Real.pi, ?_, ?_, ?_⟩
  · exact fun h => Circle.exp_pi_ne_one h.symm
  · exact fun h => Circle.exp_pi_ne_one h.symm
  · simp [muOrd, actC]

end Work.Drive
