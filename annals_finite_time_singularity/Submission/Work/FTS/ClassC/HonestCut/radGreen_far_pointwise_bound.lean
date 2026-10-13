/-
# `Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound`

The far-field (`z ≥ 1`) *pointwise* bounds for the mode-`m` radial Green function
`Work.FTS.PhiStar.Radial.radGreen α m c`:

  `|radGreen α m c z| ≤ C / z`  and  `|z · ∂_z radGreen α m c z| ≤ C / z`.

Both are assembled from the existing landing bricks:

* `Work.FTS.ClassC.rgA_growth`: `|rgA z| ≤ CA · z^{rgQ-1}` for `z ≥ 1`, i.e. the decaying branch
  `rgG1 z = z^{-rgQ}·rgA z` satisfies `|rgG1 z| ≤ CA / z`;
* `Work.FTS.ClassC.rgB_far_bound`: `z^{rgP}·|rgB z| ≤ C2 / z`, i.e. the growing branch
  `rgG2 z = z^{rgP}·rgB z` satisfies `|rgG2 z| ≤ C2 / z`;
* `Work.FTS.ClassC.radGreen_eq_rgG`: `radGreen z = rgK·(rgG1 z + rgG2 z)`;
* `Work.FTS.ClassC.radGreen_deriv1_form`: `z·∂_z radGreen z = rgK·(rgP·rgG2 z − rgQ·rgG1 z)`.

The constant is `C = max (rgK·(CA+C2)) (rgK·(rgP·C2 + rgQ·CA))`.

(The hypothesis `h0'` — integrability of the *tail* integrand near `0` — is not needed: only the
forward primitive near `0` (`h0`) enters `rgA_growth`, and `rgB_far_bound` uses the decay of `c`
together with `hinf`.)
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.rgA_growth
import Submission.Work.FTS.ClassC.rgB_far_bound
import Submission.Work.FTS.ClassC.radGreen_deriv1_form
import Submission.Work.FTS.ClassC.radGreen_far_limits
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

open Work.FTS.EllExist (rgK rgP rgQ rgA rgB rgG1 rgG2)

/-- `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_abs_add_aux (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

theorem radGreen_far_pointwise_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ C / z
      ∧ |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z| ≤ C / z := by
  obtain ⟨CA, hCA0, hAb⟩ := Work.FTS.ClassC.rgA_growth hα hα4 m hcont hdec h0
  obtain ⟨C2, hC20, hBb⟩ := Work.FTS.ClassC.rgB_far_bound hα hα4 m hdec hinf
  have hKpos : 0 < rgK α m := Work.FTS.EllExist.rgK_pos hα m
  have hK0 : 0 ≤ rgK α m := hKpos.le
  have hq0 : 0 ≤ rgQ α m := (Work.FTS.EllExist.rgQ_pos hα m).le
  have hp0 : 0 ≤ rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- ## the two branches in `C/z` form
  have hG1le : ∀ z : ℝ, 1 ≤ z → |rgG1 α m c z| ≤ CA / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hcomb : z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1) = z ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    simp only [Work.FTS.EllExist.rgG1]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    calc z ^ (-(rgQ α m)) * |rgA α m c z|
        ≤ z ^ (-(rgQ α m)) * (CA * z ^ (rgQ α m - 1)) :=
          mul_le_mul_of_nonneg_left (hAb z hz1) (Real.rpow_nonneg hz0.le _)
      _ = CA * (z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1)) := by ring
      _ = CA / z := by rw [hcomb, Real.rpow_neg_one, div_eq_mul_inv]
  have hG2le : ∀ z : ℝ, 1 ≤ z → |rgG2 α m c z| ≤ C2 / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    simp only [Work.FTS.EllExist.rgG2]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    exact hBb z hz1
  -- ## the pointwise bounds for `radGreen` and `z·∂_z radGreen`
  have hBnd_rad : ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ (rgK α m * (CA + C2)) / z := by
    intro z hz1
    rw [Work.FTS.ClassC.radGreen_eq_rgG α m c z, abs_mul, abs_of_nonneg hK0]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ ≤ rgK α m * (CA / z + C2 / z) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hG1le z hz1) (hG2le z hz1)) hK0
      _ = (rgK α m * (CA + C2)) / z := by ring
  have hBnd_zd : ∀ z : ℝ, 1 ≤ z →
      |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hd := Work.FTS.ClassC.radGreen_deriv1_form hα m hcont h0 hinf z hz0
    rw [hd, abs_mul, abs_of_nonneg hK0]
    have e1 : |rgP α m * rgG2 α m c z| = rgP α m * |rgG2 α m c z| := by
      rw [abs_mul, abs_of_nonneg hp0]
    have e2 : |rgQ α m * rgG1 α m c z| = rgQ α m * |rgG1 α m c z| := by
      rw [abs_mul, abs_of_nonneg hq0]
    calc rgK α m * |rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z|
        ≤ rgK α m * (|rgP α m * rgG2 α m c z| + |rgQ α m * rgG1 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_abs_add_aux _ _) hK0
      _ = rgK α m * (rgP α m * |rgG2 α m c z| + rgQ α m * |rgG1 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (rgP α m * (C2 / z) + rgQ α m * (CA / z)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hG2le z hz1) hp0)
              (mul_le_mul_of_nonneg_left (hG1le z hz1) hq0)) hK0
      _ = (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by ring
  -- ## assembly with the maximum of the two constants
  refine ⟨max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)),
    le_trans (mul_nonneg hK0 (by linarith)) (le_max_left _ _), fun z hz1 => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
  refine ⟨?_, ?_⟩
  · calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ (rgK α m * (CA + C2)) / z := hBnd_rad z hz1
      _ ≤ max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z :=
          div_le_div_of_nonneg_right (le_max_left _ _) hz0.le
  · calc |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := hBnd_zd z hz1
      _ ≤ max (rgK α m * (CA + C2)) (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z :=
          div_le_div_of_nonneg_right (le_max_right _ _) hz0.le

end Work.FTS.ClassC.HonestCut
