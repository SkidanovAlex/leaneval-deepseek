import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory

/-- Auxiliary computation: the product of `1` (over the first `i` coordinates) and `ρ` (over the
remaining ones) equals `ρ ^ (n - i)`. -/
private lemma prod_ite_scaleLast {n i : ℕ} {ρ : ℝ} :
    ∏ j : Fin n, (if (j : ℕ) < i then (1 : ℝ) else ρ) = ρ ^ (n - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    rcases lt_or_ge n i with h | h
    · have h1 : n - i = 0 := by omega
      have h2 : n + 1 - i = 0 := by omega
      rw [h1, h2, if_pos h]
      simp
    · have h2 : n + 1 - i = n - i + 1 := by omega
      rw [h2, if_neg (by omega), pow_succ]

/-- The matrix of `scaleLast i ρ` in the standard basis is the diagonal matrix with entries
`1` on the first `i` coordinates and `ρ` on the remaining ones. -/
private lemma toMatrix'_scaleLast {n i : ℕ} (ρ : ℝ) :
    LinearMap.toMatrix' (Work.BW.scaleLast (d := n) i ρ)
      = Matrix.diagonal (fun j : Fin n => if (j : ℕ) < i then (1 : ℝ) else ρ) := by
  ext a b
  rw [LinearMap.toMatrix'_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : (a : ℕ) < i
    · rw [Work.BW.scaleLast_apply_lt i ρ (Pi.single a 1) ha, if_pos rfl, if_pos ha,
        Pi.single_eq_same]
    · rw [Work.BW.scaleLast_apply_not i ρ (Pi.single a 1) ha, if_pos rfl, if_neg ha,
        Pi.single_eq_same]
      ring
  · rw [if_neg hab]
    by_cases ha : (a : ℕ) < i
    · rw [Work.BW.scaleLast_apply_lt i ρ (Pi.single b 1) ha,
        Pi.single_eq_of_ne hab]
    · rw [Work.BW.scaleLast_apply_not i ρ (Pi.single b 1) ha,
        Pi.single_eq_of_ne hab]
      ring

/-- The determinant of `scaleLast i ρ` is `ρ ^ (n - i)`. -/
private lemma det_scaleLast {n i : ℕ} (ρ : ℝ) :
    LinearMap.det (Work.BW.scaleLast (d := n) i ρ) = ρ ^ (n - i) := by
  rw [← LinearMap.det_toMatrix' (f := Work.BW.scaleLast (d := n) i ρ), toMatrix'_scaleLast,
    Matrix.det_diagonal, prod_ite_scaleLast]

/-- Multiplying the last `n - i` coordinates by `ρ > 0` multiplies the volume by `ρ ^ (n - i)`. -/
theorem volume_scaleLast {n i : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (S : Set (Fin n → ℝ)) :
    MeasureTheory.volume.real (Work.BW.scaleLast i ρ '' S) =
      ρ ^ (n - i) * MeasureTheory.volume.real S := by
  have hdet : LinearMap.det (Work.BW.scaleLast (d := n) i ρ) = ρ ^ (n - i) := det_scaleLast ρ
  have hnn : (0 : ℝ) ≤ ρ ^ (n - i) := pow_nonneg hρ.le _
  have key : (MeasureTheory.volume (Work.BW.scaleLast (d := n) i ρ '' S)).toReal
      = ρ ^ (n - i) * (MeasureTheory.volume S).toReal := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, hdet, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg hnn]
  simpa only [MeasureTheory.Measure.real_def] using key

end Work.BW.Minkowski2
