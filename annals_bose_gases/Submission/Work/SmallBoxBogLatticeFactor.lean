import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.Work.SmallBoxBogolubovLayer
import Submission.Work.SmallBoxL2Modes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-260 part 8 — the `(1+C·c0·(av))`-factor: the refined pointwise
lattice weight bound

FS lm:appbogolubov's `|p| > 2c` reduction replaces the weighted-kinetic
symbol `[r−c]₊⁻²` by the Newtonian `r⁻²`-value up to the factor
`(1 + C·(dsℓ)⁻¹/r)` (eq:refinedaprioribog's `(1+C(dsℓ)⁻¹a)`-prefactor after
the `|p| ≥ a⁻¹`-split).  This module certifies the elementary pointwise
leaf in the box-lattice variables (`r := π‖k‖/s` the mode eigenvalue):

  * **`inv_sub_sq_le`** — `(r−c)⁻² ≤ r⁻²·(1 + 6c/r)` for `r ≥ 2c > 0`
    (the universal constant `6` is the sharp simple choice: the equivalent
    `1 ≤ (1−t)²(1+Ct)` on `t := c/r ≤ 1/2` needs `C ≥ 6`);
  * **`boxModeCoeff_le_newtonian_refined`** — the box-mode form
    `boxModeCoeff s c k ≤ (s²/(π²‖k‖²))·(1 + 6cs/(π‖k‖))` for
    `π‖k‖/s ≥ 2c` (`inv_sub_sq_le` + `boxModeCoeff_eq_fsKinCoeff_inv` +
    `fsKinCoeff_of_lt`);
  * **`inv_sub_sq_factor`** — the collapsed `(1+C·c0·(av))`-prefactor
    `(r−c)⁻² ≤ r⁻²·(1+6ca)` for `r ≥ max(2c, a⁻¹)`
    (`6c/r ≤ 6ca` from `r ≥ a⁻¹`).

The `|p| < a⁻¹`-part of the split (where `1 ≤ r·a` fails) is where the
log/`c0³`-bracket terms emerge (over the continuum, with `Ŵ₁`-boundedness);
that is the next certified piece.  This module keeps the factor clean and
leaves the per-mode Fock2Mode instantiation for after the bracket leaves.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma inv_sub_sq_le {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    (r - c)⁻¹ ^ 2 ≤ r⁻¹ ^ 2 * (1 + 6 * c / r) := by
  have hc0 : 0 < r := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hr
  have hrc : 0 < r - c := by nlinarith
  have hrcne : r - c ≠ 0 := ne_of_gt hrc
  have hrne : r ≠ 0 := ne_of_gt hc0
  have h1 : 0 ≤ r - 2 * c := by linarith
  have h2 : 0 ≤ 4 * r - 3 * c := by nlinarith
  field_simp [hrcne, hrne]
  have hfac : 0 ≤ c * (r - 2 * c) * (4 * r - 3 * c) :=
    mul_nonneg (mul_nonneg hc.le h1) h2
  nlinarith

lemma boxModeCoeff_le_newtonian_refined {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (k : Fin 3 → ℕ) (hk : 2 * c * s ≤ Real.pi * boxModeNorm k) :
    boxModeCoeff s c k ≤ (s ^ 2 / (Real.pi ^ 2 * boxModeNorm k ^ 2))
        * (1 + 6 * c * s / (Real.pi * boxModeNorm k)) := by
  let r : ℝ := Real.pi * boxModeNorm k / s
  have hcs : 0 < 2 * c * s := by positivity
  have hpiN : 0 < Real.pi * boxModeNorm k := lt_of_lt_of_le hcs hk
  have hkn : 0 < boxModeNorm k := pos_of_mul_pos_right hpiN (le_of_lt Real.pi_pos)
  have hr2c : 2 * c ≤ r := by dsimp [r]; exact (le_div_iff₀ hs).mpr hk
  have hpt := inv_sub_sq_le (c := c) (r := r) hc hr2c
  have hrgt : c < r := by nlinarith [hr2c]
  have hcoeff : boxModeCoeff s c k = (r - c)⁻¹ ^ 2 := by
    calc
      boxModeCoeff s c k = (fsKinCoeff c r)⁻¹ := by
            simpa [r] using (boxModeCoeff_eq_fsKinCoeff_inv s c k)
      _ = ((r - c) ^ 2)⁻¹ := by
            have hfs : fsKinCoeff c r = (r - c) ^ 2 := fsKinCoeff_of_lt (le_of_lt hc) hrgt
            rw [hfs]
      _ = (r - c)⁻¹ ^ 2 := by exact (inv_pow (r - c) 2).symm
  calc
    boxModeCoeff s c k = (r - c)⁻¹ ^ 2 := hcoeff
    _ ≤ r⁻¹ ^ 2 * (1 + 6 * c / r) := hpt
    _ = (s ^ 2 / (Real.pi ^ 2 * boxModeNorm k ^ 2))
          * (1 + 6 * c * s / (Real.pi * boxModeNorm k)) := by
          dsimp [r]
          field_simp [ne_of_gt hs, ne_of_gt hkn, Real.pi_ne_zero]

lemma inv_sub_sq_factor {c a r : ℝ} (hc : 0 < c) (ha : 0 < a) (hrc : 2 * c ≤ r)
    (hra : a⁻¹ ≤ r) :
    (r - c)⁻¹ ^ 2 ≤ r⁻¹ ^ 2 * (1 + 6 * c * a) := by
  have hc0 : 0 < r := by nlinarith [hrc, hc]
  have hpt := inv_sub_sq_le hc hrc
  have han : a ≠ 0 := ne_of_gt ha
  have h1le : 1 ≤ a * r := by
    have hmul := (mul_le_mul_iff_of_pos_left (a := a) ha).2 hra
    simpa [mul_inv_cancel₀ han] using hmul
  have hr_inv : r⁻¹ ≤ a := by
    have hrn : r ≠ 0 := ne_of_gt hc0
    exact (mul_le_mul_iff_of_pos_right hc0).mp (by
      simpa [inv_mul_cancel₀ hrn] using h1le)
  have hdiv : 6 * c / r ≤ 6 * c * a := by
    calc
      6 * c / r = (6 * c) * r⁻¹ := by ring
      _ ≤ (6 * c) * a := mul_le_mul_of_nonneg_left hr_inv (by positivity)
  calc
    (r - c)⁻¹ ^ 2 ≤ r⁻¹ ^ 2 * (1 + 6 * c / r) := hpt
    _ ≤ r⁻¹ ^ 2 * (1 + 6 * c * a) := by
          exact mul_le_mul_of_nonneg_left (by nlinarith [hdiv]) (sq_nonneg (r⁻¹))

end BoseGases
end Submission

