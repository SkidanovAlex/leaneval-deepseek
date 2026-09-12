import Mathlib
import Submission.PolyaShell
import Submission.StarGeom

/-!
# Above-the-tip (corridor) cells of the E2b deformation

The E2b contour deformation parts the annulus between the big circle and the
hedgehog `star S` into cells.  `Submission.StarGeom`/`Submission.Fold` treat
the *gap cells*: angular ranges `[c, d]` containing no spike direction are
star-free for every radial range.  The complementary *spike-corridor cells*
have an angular range containing a spike direction `θ` but a radial range
`[xmin, xmax]` that starts *above* the tips of all spikes pointing into
`[c, d]`: then the exp-image of the w-rectangle still avoids the hedgehog
(every point of a spike pointing into `[c, d]` has modulus `≤` its endpoint
norm `< exp xmin ≤ ‖exp w‖`), so the same rectangle-Cauchy identity applies.

This module proves
1. the geometric fact `expRect_avoids_star_tip` (exp-image of the rectangle
   avoids `star S` under the above-the-tip hypothesis), and
2. the analytic cell identity `tip_cell_boundary_integral_eq_zero` (the
   pulled-back boundary integral over such a rectangle vanishes for every
   `h` holomorphic off the hedgehog).

Both mirror the gap-cell statements in `Submission.StarGeom` and
`Submission.PolyaShell`, with the "no direction in range" hypothesis replaced
by "every spike pointing into the range is shorter than the inner radius".
-/

noncomputable section

open scoped Complex Real Interval
open Complex

namespace Submission.TipCell

open Submission.XTransfer

/-- **Above-the-tip single-cell geometry.**  If every spike endpoint `z²`,
`z⁴` (`z ∈ S`) whose argument points into the closed angular range
`[ymin, ymax] ⊆ (-π, π]` has norm strictly below the inner radius `exp xmin`
of the w-rectangle `[[xmin,xmax]] ×ℂ [[ymin,ymax]]`, then the exp-image of
that rectangle avoids the hedgehog. -/
lemma expRect_avoids_star_tip {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {xmin xmax ymin ymax : ℝ} (hx : xmin ≤ xmax) (hy : ymin < ymax)
    (hyl : -π < ymin) (hyu : ymax ≤ π)
    (htip : ∀ z ∈ S,
      (Complex.arg (z ^ 2) ∈ Set.Icc ymin ymax → ‖z ^ 2‖ < Real.exp xmin) ∧
      (Complex.arg (z ^ 4) ∈ Set.Icc ymin ymax → ‖z ^ 4‖ < Real.exp xmin)) :
    ∀ w ∈ ([[xmin, xmax]] ×ℂ [[ymin, ymax]]), Complex.exp w ∉ star S := by
  intro w hw hws
  have hwim : w.im ∈ Set.Icc ymin ymax := by
    have hwim0 := (Complex.mem_reProdIm.mp hw).2
    simpa [Set.uIcc_of_le (le_of_lt hy)] using hwim0
  have hwre : w.re ∈ Set.Icc xmin xmax := by
    have hwre0 := (Complex.mem_reProdIm.mp hw).1
    simpa [Set.uIcc_of_le hx] using hwre0
  have hylw : -π < w.im := lt_of_lt_of_le hyl hwim.1
  have hyuw : w.im ≤ π := le_trans hwim.2 hyu
  have hargw : Complex.arg (Complex.exp w) = w.im := StarGeom.arg_exp_eq_im hylw hyuw
  have hexp0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hexpnorm : Real.exp xmin ≤ ‖Complex.exp w‖ := by
    have hre_ge : xmin ≤ w.re := hwre.1
    have hexpmono : Real.exp xmin ≤ Real.exp w.re := Real.exp_le_exp.mpr hre_ge
    rw [Complex.norm_exp]
    exact hexpmono
  have hstar : ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) := by
    change ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) at hws
    exact hws
  rcases hstar with ⟨z, hz, hseg⟩
  have hz0 : z ≠ 0 := hS0 z hz
  rcases hseg with h2 | h4
  · -- exp w on the segment [0, z²]
    have harg2 : Complex.arg (z ^ 2) = w.im := by
      calc
        Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
          (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
        _ = w.im := hargw
    have hsmall : ‖z ^ 2‖ < Real.exp xmin := (htip z hz).1 (by
      rw [harg2]
      exact hwim)
    have hnorm_le : ‖Complex.exp w‖ ≤ ‖z ^ 2‖ := by
      rcases (mem_segment_zero_iff (z ^ 2) (Complex.exp w)).mp h2 with ⟨t, ht01, htX⟩
      calc
        ‖Complex.exp w‖ = ‖t • (z ^ 2)‖ := by rw [htX]
        _ = t * ‖z ^ 2‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
        _ ≤ ‖z ^ 2‖ := by
          exact mul_le_of_le_one_left (norm_nonneg (z ^ 2)) ht01.2
    linarith
  · -- exp w on the segment [0, z⁴]
    have harg4 : Complex.arg (z ^ 4) = w.im := by
      calc
        Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
          (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
        _ = w.im := hargw
    have hsmall : ‖z ^ 4‖ < Real.exp xmin := (htip z hz).2 (by
      rw [harg4]
      exact hwim)
    have hnorm_le : ‖Complex.exp w‖ ≤ ‖z ^ 4‖ := by
      rcases (mem_segment_zero_iff (z ^ 4) (Complex.exp w)).mp h4 with ⟨t, ht01, htX⟩
      calc
        ‖Complex.exp w‖ = ‖t • (z ^ 4)‖ := by rw [htX]
        _ = t * ‖z ^ 4‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
        _ ≤ ‖z ^ 4‖ := by
          exact mul_le_of_le_one_left (norm_nonneg (z ^ 4)) ht01.2
    linarith

/-- **Above-the-tip cell Cauchy.**  If `h` is holomorphic off the hedgehog
and every spike endpoint pointing into the closed angular range `[c, d] ⊆
(-π, π]` is shorter than the inner radius `e^a` of the cell (so the
exp-image of the w-rectangle `[[a,b]] ×ℂ [[c,d]]` avoids the hedgehog), then
the boundary integral of the pulled-back 1-form `h(exp w)·exp w·dw` over the
rectangle vanishes. -/
lemma tip_cell_boundary_integral_eq_zero {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (a b : ℝ) (hab : a ≤ b) {c d : ℝ} (hc : c < d) (hcl : -π < c) (hdu : d ≤ π)
    (htip : ∀ z ∈ S,
      (Complex.arg (z ^ 2) ∈ Set.Icc c d → ‖z ^ 2‖ < Real.exp a) ∧
      (Complex.arg (z ^ 4) ∈ Set.Icc c d → ‖z ^ 4‖ < Real.exp a)) :
    (∫ x : ℝ in a..b, h (Complex.exp (x + c * Complex.I)) * Complex.exp (x + c * Complex.I)) -
      (∫ x : ℝ in a..b, h (Complex.exp (x + d * Complex.I)) * Complex.exp (x + d * Complex.I)) +
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (b + y * Complex.I)) * Complex.exp (b + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (a + y * Complex.I)) * Complex.exp (a + y * Complex.I)) = 0 := by
  apply PolyaShell.sector_cauchy_of_star_compl hh a b c d
  intro w hw
  have hne : Complex.exp w ∉ Submission.XTransfer.star S :=
    expRect_avoids_star_tip (S := S) hS0 hab hc hcl hdu htip w hw
  simpa using hne

end Submission.TipCell

end
