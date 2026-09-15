import Submission.FUP.LocalizeZplane
import Submission.Commons.Analysis.Complex.weyl_dbar
import Submission.Commons.Analysis.Complex.abs_re_log_div_le
import Submission.Commons.Analysis.Measure.integral_strip_eq_iterated
import Submission.Commons.Analysis.Fourier.strip_integral_entire_le

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The sum over cells of the per-cell z-plane estimate

Assembles `cell_zplane` over the cells of the `2ℤ^d` lattice: the sup-norms `S_n` of the
per-cell functions are controlled by the strip integral of the entire extension `F` via the
mean value inequality and the bounded multiplicity of the lattice balls.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The centre of the cell of the `2ℤ^d`-lattice with index `n`. -/
noncomputable def cellCentre {d : ℕ} (γ : Fin d → ℝ) (n : Fin d → ℤ) : Fin d → ℝ :=
  fun i => 2 * (n i : ℝ) + γ i + 1

lemma csSup_image_eq_of_isMaxOn {α : Type*} {s : Set α} {g : α → ℝ} {x0 : α}
    (hx0 : x0 ∈ s) (hmax : ∀ x ∈ s, g x ≤ g x0) : sSup (g '' s) = g x0 := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨g x0, x0, hx0, rfl⟩ ?_
    rintro y ⟨x, hx, rfl⟩
    exact hmax x hx
  · exact le_csSup ⟨g x0, by rintro y ⟨x, hx, rfl⟩; exact hmax x hx⟩ ⟨x0, hx0, rfl⟩

lemma phiLens_one_pos {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < phiLens q ε 1 := by
  rw [phiLens]
  have h1 : (1:ℝ) < (1 + (1-ε) * 1) / (1 - (1-ε) * 1) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 - (1-ε)*1)]
    linarith
  have h2 : 0 < Real.log ((1 + (1-ε) * 1) / (1 - (1-ε) * 1)) := Real.log_pos h1
  positivity

/-- The real part of the lens map on the closed unit disk. -/
lemma abs_re_lensMap_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : |(lensMap q ε w).re| ≤ phiLens q ε 1 := by
  have hr0 : (0:ℝ) ≤ 1 - ε := by linarith
  have hr1 : (1 - ε) < 1 := by linarith
  have hnorm : ‖((1 - ε : ℝ) : ℂ) * w‖ ≤ 1 - ε := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    calc (1 - ε) * ‖w‖ ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left hw hr0
      _ = 1 - ε := by ring
  have h := Commons.Analysis.Complex.abs_re_log_div_le hr0 hr1 hnorm
  have hc : (0:ℝ) ≤ 2*q/Real.pi := by positivity
  simp only [lensMap, stripMap] at h ⊢
  have hre : (((2 * q / Real.pi : ℝ) : ℂ) * Complex.log
        ((1 + ((1 - ε : ℝ) : ℂ) * w) / (1 - ((1 - ε : ℝ) : ℂ) * w))).re
      = (2*q/Real.pi) * (Complex.log
        ((1 + ((1 - ε : ℝ) : ℂ) * w) / (1 - ((1 - ε : ℝ) : ℂ) * w))).re := by
    rw [Complex.mul_re]
    simp
  rw [hre, abs_mul, abs_of_nonneg hc]
  calc (2*q/Real.pi) * |(Complex.log ((1 + ((1 - ε : ℝ) : ℂ) * w)
        / (1 - ((1 - ε : ℝ) : ℂ) * w))).re|
      ≤ (2*q/Real.pi) * Real.log ((1 + (1 - ε)) / (1 - (1 - ε))) :=
        mul_le_mul_of_nonneg_left h hc
    _ = phiLens q ε 1 := by rw [phiLens]; ring_nf

/-- The imaginary part of the lens map on the closed unit disk. -/
lemma im_lensMap_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : |(lensMap q ε w).im| ≤ q := by
  have hr0 : (0:ℝ) ≤ 1 - ε := by linarith
  have hnorm : ‖((1 - ε : ℝ) : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    have h1 : (1 - ε) * ‖w‖ ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left hw hr0
    linarith
  have hmem : ((1 - ε : ℝ) : ℂ) * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]; exact hnorm
  have h := Commons.Analysis.Complex.strip_map_mapsTo q hq hmem
  simp only [Set.mem_ofPred_eq, abs_lt] at h
  have h2 : lensMap q ε w = stripMap q (((1 - ε : ℝ) : ℂ) * w) := rfl
  rw [h2]
  have hcast : ((2 * q / Real.pi : ℝ) : ℂ) = 2 * (q : ℂ) / (Real.pi : ℂ) := by push_cast; ring
  simp only [stripMap, hcast]
  rw [abs_le]
  exact ⟨le_of_lt h.1, le_of_lt h.2⟩

end Submission.FUP
