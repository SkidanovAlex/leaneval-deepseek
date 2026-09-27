import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.depthPlus3
import Submission.Work.Mostow.sinh_le_mul_cosh

/-!
# Auxiliary estimates for `rotData3`
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Work.Mostow
open Matrix

noncomputable section

lemma cosh_le_cosh_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.cosh x ≤ Real.cosh 1 := by
  rw [Real.cosh_le_cosh, abs_of_nonneg h0, abs_one]
  exact h1

/-- `sinh x ≤ x * cosh 1` for `0 ≤ x ≤ 1`. -/
lemma sinh_le_mul_cosh_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.sinh x ≤ x * Real.cosh 1 := by
  have h := Work.Mostow.sinh_le_mul_cosh x h0
  have h2 : Real.cosh x ≤ Real.cosh 1 := cosh_le_cosh_one h0 h1
  nlinarith [h, h2, h0]

/-- The inequality `sinh (distGeod a b z) * sin (θ/2) ≤ η/2` for an `η`-near-identity rotation. -/
theorem ineq_of_rotation (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (a b z : Submission.Mostow.E 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (θ η : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hη : 0 < η) (hη2 : η ≤ 1)
    (hrot : Work.Mostow.IsRotationAbout g a b θ) (hne : Submission.Mostow.NearIdAt g z η) :
    Real.sinh (distGeod a b z) * Real.sin (θ / 2) ≤ η / 2 := by
  have hS : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hdz : 0 ≤ distGeod a b z := distGeod_nonneg a b ha hb hab z
  have hsh : 0 ≤ Real.sinh (distGeod a b z) := Real.sinh_nonneg_iff.mpr hdz
  have key : ∀ u : Submission.Mostow.E 3, hdist z u ≤ 1 →
      Real.sinh (distGeod a b u) * Real.sin (θ / 2) < Real.sinh (η / 2) := by
    intro u hzu
    have h1 : hdist u (g • u) < η := hne u hzu
    rw [hrot.2 u] at h1
    have h2 : Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (θ / 2)) < η / 2 := by
      linarith
    have h3 : Real.sinh (Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (θ / 2)))
        < Real.sinh (η / 2) := Real.sinh_lt_sinh.mpr h2
    rwa [Real.sinh_arsinh] at h3
  obtain ⟨u, hzu, hdu⟩ := exists_distGeod_addOne 3 (by norm_num) a b ha hb hab z
  have hu := key u hzu
  have hstep : Real.sinh (distGeod a b z) * Real.cosh 1 ≤ Real.sinh (distGeod a b z + 1) := by
    rw [Real.sinh_add]
    have hc : 0 < Real.cosh (distGeod a b z) := Real.cosh_pos _
    have hs : 0 ≤ Real.sinh 1 := Real.sinh_nonneg_iff.mpr (by norm_num)
    nlinarith [hc, hs, hsh]
  have hmono : Real.sinh (distGeod a b z) * Real.cosh 1 * Real.sin (θ / 2)
      ≤ Real.sinh (distGeod a b u) * Real.sin (θ / 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hS
    exact le_trans hstep (Real.sinh_le_sinh.mpr hdu)
  have hmain : Real.sinh (distGeod a b z) * Real.sin (θ / 2) * Real.cosh 1 < Real.sinh (η / 2) := by
    have h := lt_of_le_of_lt hmono hu
    have h3 : Real.sinh (distGeod a b z) * Real.cosh 1 * Real.sin (θ / 2)
        = Real.sinh (distGeod a b z) * Real.sin (θ / 2) * Real.cosh 1 := by ring
    rwa [h3] at h
  have hfinal : Real.sinh (η / 2) ≤ η / 2 * Real.cosh 1 := by
    have h := sinh_le_mul_cosh_one (by linarith : (0:ℝ) ≤ η / 2) (by linarith : η / 2 ≤ 1)
    linarith
  have hc1 : 0 < Real.cosh 1 := Real.cosh_pos 1
  have h2 : Real.sinh (distGeod a b z) * Real.sin (θ / 2) * Real.cosh 1 < η / 2 * Real.cosh 1 :=
    lt_of_lt_of_le hmain hfinal
  exact le_of_lt (lt_of_mul_lt_mul_right h2 (le_of_lt hc1))

/-- In the "acute" range `2m ≤ M`, `sin (π/M) ≤ sin (π m/M)`. -/
lemma sin_pi_div_le_acute (M m : ℕ) (hM : 2 ≤ M) (hm0 : 0 < m) (h2m : 2 * m ≤ M) :
    Real.sin (Real.pi / (M : ℝ)) ≤ Real.sin (Real.pi * (m : ℝ) / (M : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h2mr : 2 * (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2m
  have hpi := Real.pi_pos
  have hle1 : Real.pi / (M : ℝ) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) hMr
  have hle2 : Real.pi * (m : ℝ) / (M : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hMpos]
    have h := mul_le_mul_of_nonneg_left h2mr (le_of_lt hpi)
    nlinarith [h]
  have hle3 : Real.pi / (M : ℝ) ≤ Real.pi * (m : ℝ) / (M : ℝ) := by
    rw [div_le_div_iff_of_pos_right hMpos]
    have h : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt hpi)
    nlinarith [h']
  have hp1 : (0:ℝ) < Real.pi / (M : ℝ) := div_pos hpi hMpos
  have hp2 : (0:ℝ) < Real.pi * (m : ℝ) / (M : ℝ) := div_pos (mul_pos hpi hmr) hMpos
  have h1 : Real.pi / (M : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hle1⟩
  have h2 : Real.pi * (m : ℝ) / (M : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hle2⟩
  exact Real.strictMonoOn_sin.monotoneOn h1 h2 hle3

/-- `sin (π/M) ≤ sin (π*m/M)` for `1 ≤ m ≤ M-1`. -/
theorem sin_pi_div_le (M m : ℕ) (hM : 2 ≤ M) (hm0 : 0 < m) (hmM : m < M) :
    Real.sin (Real.pi / (M : ℝ)) ≤ Real.sin (Real.pi * (m : ℝ) / (M : ℝ)) := by
  by_cases h2m : 2 * m ≤ M
  · exact sin_pi_div_le_acute M m hM hm0 h2m
  · push_neg at h2m
    have h1 : 0 < M - m := by omega
    have h2 : 2 * (M - m) ≤ M := by omega
    have h4 := sin_pi_div_le_acute M (M - m) hM h1 h2
    have h5 : Real.pi * ((M - m : ℕ) : ℝ) / (M : ℝ)
        = Real.pi - Real.pi * (m : ℝ) / (M : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hmM)]
      field_simp
      try ring
    rw [h5, Real.sin_pi_sub] at h4
    exact h4

end

end Work.Mostow.gapA
