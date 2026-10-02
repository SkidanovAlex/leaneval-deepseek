/-
# `Work.FQC.Ell` — the MNS twist `ℓ_t` of the Écalle cylinder

The map `ell t w = w + i·t·saw (Re w)` is MNS's piecewise-affine twist of the Écalle cylinder
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.4).  The full API is

* `Work.FQC.saw_add_one`, `Work.FQC.saw_add_half` (modules `saw_add_one`, `saw_add_half`);
* `Work.FQC.ell_add_one`, `Work.FQC.ell_comm_I`, `Work.FQC.ell_homeo`,
  `Work.FQC.ell_beltrami`, `Work.FQC.ell_beltrami_conj`;
* in this file: `ell_re`, `ell_im`, the special values of `saw`, and `ell_quarter`.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_add_one
import Submission.Work.FQC.saw_add_half
import Submission.Work.FQC.ell_add_one
import Submission.Work.FQC.ell_comm_I
import Submission.Work.FQC.ell_homeo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem ell_re (t : ℝ) (w : ℂ) : (ell t w).re = w.re := by
  simp only [ell, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem ell_im (t : ℝ) (w : ℂ) : (ell t w).im = w.im + t * saw w.re := by
  simp only [ell, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem saw_quarter : saw (1 / 4) = 1 / 2 := by
  have h : Int.fract ((1 : ℝ) / 4 + 1 / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num, Int.fract_eq_self]
    norm_num
  rw [saw_apply, h]
  norm_num

theorem saw_three_quarter : saw (3 / 4) = -(1 / 2) := by
  have h : Int.fract ((3 : ℝ) / 4 + 1 / 4) = 0 := by
    rw [show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Int.fract_one]
  rw [saw_apply, h]
  norm_num

theorem saw_zero : saw 0 = 0 := by
  have h : Int.fract ((0 : ℝ) + 1 / 4) = 1 / 4 := by
    rw [show (0 : ℝ) + 1 / 4 = 1 / 4 by norm_num, Int.fract_eq_self]
    norm_num
  rw [saw_apply, h]
  norm_num

/-- `ℓ_t` moves the point of phase `1/4` and height `h` to height `h + t/2`: this is the
computation underlying the height shift. -/
theorem ell_quarter (t h : ℝ) :
    ell t ((1 / 4 : ℝ) + (h : ℂ) * Complex.I) =
      (1 / 4 : ℝ) + ((h + t / 2 : ℝ) : ℂ) * Complex.I := by
  have hre : (((1 / 4 : ℝ) : ℂ) + (h : ℂ) * Complex.I).re = 1 / 4 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  apply Complex.ext
  · simp only [ell_re, hre, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [ell_im, hre, saw_quarter, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

end Work.FQC

end
