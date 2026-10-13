/-
# `Work.FTS.ClassC.radGreen_far_limits`

The far-field (`z → ∞`) decay of the mode-`m` radial Green function
`Work.FTS.PhiStar.Radial.radGreen α m c` of `Radial/Defs.lean`:

  `z · (radGreen z)² → 0`  and  `z · radGreen z · (z · ∂_z radGreen z) → 0`,

for `0 < α ≤ 1/4`, a source `c` continuous on `(0,∞)` with `|c t| ≤ K/t` for `t ≥ 1` and the
three integrability conditions of `Radial/radGreen_solves`.

These are exactly the two inputs of `Work.FTS.ClassC.flux_radGreen_atTop` (the boundary term of
the per-mode weighted energy identity vanishes at `+∞`).

## The argument

Write (`Work.FTS.EllExist.RadGreenDefs`)

  `radGreen α m c z = rgK·(rgG1 z + rgG2 z)`,
  `rgG1 z = z^{-rgQ} · rgA z`,  `rgA z = ∫₀^z c t^{rgQ-1} dt`,
  `rgG2 z = z^{rgP} · rgB z`,   `rgB z = ∫_z^∞ c t^{-rgP-1} dt`,
  `rgQ = (2m+5)/α ≥ 20`,  `rgP = 2m/α ≥ 0`.

With only `|c t| ≤ K/t` on `[1,∞)`:

* `rgA` **grows**: `|rgA z| ≤ CA·z^{rgQ-1}` for `z ≥ 1` (`FTS/ClassC/rgA_growth`), so
  `|rgG1 z| ≤ CA/z` and `z|rgG1 z| ≤ CA`;
* `rgB` **decays**: `z^{rgP}|rgB z| ≤ C2/z` (`FTS/ClassC/rgB_far_bound`), so `|rgG2 z| ≤ C2/z`
  and `z|rgG2 z| ≤ C2`;

hence `|radGreen z| ≤ rgK(CA+C2)/z` (decaying like `1/z`) while `|z·radGreen z| ≤ rgK(CA+C2)` is
bounded.  For the derivative, `Work.FTS.ClassC.radGreen_deriv1_form` gives

  `z·∂_z radGreen z = rgK·(rgP·rgG2 z − rgQ·rgG1 z)`,

whose modulus is `≤ rgK(rgP·C2 + rgQ·CA)/z → 0`.  The two products in the statement are then a
bounded factor times a factor tending to `0`.  (The `hderiv` hypothesis is not needed: it is a
consequence of the other ones.)
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassC.radGreen_deriv1_form
import Submission.Work.FTS.ClassC.rgA_growth
import Submission.Work.FTS.ClassC.rgB_far_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

open Work.FTS.EllExist (rgK rgP rgQ rgA rgB rgG1 rgG2)

/-- `radGreen` written with the two indicial branches `rgG1`, `rgG2` of
`Work.FTS.EllExist.RadGreenDefs`. -/
theorem radGreen_eq_rgG (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
  rw [Work.FTS.EllExist.radGreen_eq]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]

/-- `C / z → 0` at `+∞`. -/
private theorem tendsto_const_div_atTop (C : ℝ) :
    Tendsto (fun z : ℝ => C / z) atTop (nhds 0) :=
  Filter.Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (nhds C))
    (tendsto_id : Tendsto (fun z : ℝ => z) atTop atTop)

/-- `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_abs_add' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

theorem radGreen_far_limits {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z) :
    Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2)
        Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z)
          * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) Filter.atTop (nhds 0) := by
  obtain ⟨CA, hCA0, hAb⟩ := rgA_growth hα hα4 m hcont hdec h0
  obtain ⟨C2, hC20, hBb⟩ := rgB_far_bound hα hα4 m hdec hinf
  have hKpos : 0 < rgK α m := Work.FTS.EllExist.rgK_pos hα m
  have hK0 : 0 ≤ rgK α m := hKpos.le
  have hq0 : 0 ≤ rgQ α m := (Work.FTS.EllExist.rgQ_pos hα m).le
  have hp0 : 0 ≤ rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  have hCAD : 0 ≤ CA + C2 := by linarith
  -- ## (i) the two branches, in the normalised form
  have hG1le : ∀ z : ℝ, 1 ≤ z → |rgG1 α m c z| ≤ CA / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hA := hAb z hz1
    have hcomb : z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1) = z ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    simp only [Work.FTS.EllExist.rgG1]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    calc z ^ (-(rgQ α m)) * |rgA α m c z|
        ≤ z ^ (-(rgQ α m)) * (CA * z ^ (rgQ α m - 1)) :=
          mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz0.le _)
      _ = CA * (z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1)) := by ring
      _ = CA / z := by rw [hcomb, Real.rpow_neg_one, div_eq_mul_inv]
  have hG2le : ∀ z : ℝ, 1 ≤ z → |rgG2 α m c z| ≤ C2 / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hB := hBb z hz1
    simp only [Work.FTS.EllExist.rgG2]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    exact hB
  have hzG1le : ∀ z : ℝ, 1 ≤ z → z * |rgG1 α m c z| ≤ CA := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    calc z * |rgG1 α m c z| ≤ z * (CA / z) := mul_le_mul_of_nonneg_left (hG1le z hz1) hz0.le
      _ = CA := by field_simp
  have hzG2le : ∀ z : ℝ, 1 ≤ z → z * |rgG2 α m c z| ≤ C2 := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    calc z * |rgG2 α m c z| ≤ z * (C2 / z) := mul_le_mul_of_nonneg_left (hG2le z hz1) hz0.le
      _ = C2 := by field_simp
  -- ## (ii) the pointwise bounds for `radGreen`, `z·radGreen` and `z·∂_z radGreen`
  have hBnd_rad : ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ (rgK α m * (CA + C2)) / z := by
    intro z hz1
    rw [radGreen_eq_rgG α m c z, abs_mul, abs_of_nonneg hK0]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ ≤ rgK α m * (CA / z + C2 / z) :=
          mul_le_mul_of_nonneg_left (add_le_add (hG1le z hz1) (hG2le z hz1)) hK0
      _ = (rgK α m * (CA + C2)) / z := by ring
  have hBnd_zrad : ∀ z : ℝ, 1 ≤ z →
      |z * Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ rgK α m * (CA + C2) := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    rw [radGreen_eq_rgG α m c z]
    rw [show z * (rgK α m * (rgG1 α m c z + rgG2 α m c z))
        = rgK α m * (z * rgG1 α m c z + z * rgG2 α m c z) from by ring,
      abs_mul, abs_of_nonneg hK0]
    have e1 : |z * rgG1 α m c z| = z * |rgG1 α m c z| := by rw [abs_mul, abs_of_pos hz0]
    have e2 : |z * rgG2 α m c z| = z * |rgG2 α m c z| := by rw [abs_mul, abs_of_pos hz0]
    calc rgK α m * |z * rgG1 α m c z + z * rgG2 α m c z|
        ≤ rgK α m * (|z * rgG1 α m c z| + |z * rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ = rgK α m * (z * |rgG1 α m c z| + z * |rgG2 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (CA + C2) :=
          mul_le_mul_of_nonneg_left (add_le_add (hzG1le z hz1) (hzG2le z hz1)) hK0
  have hBnd_zd : ∀ z : ℝ, 1 ≤ z →
      |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hd := radGreen_deriv1_form hα m hcont h0 hinf z hz0
    rw [hd, abs_mul, abs_of_nonneg hK0]
    have e1 : |rgP α m * rgG2 α m c z| = rgP α m * |rgG2 α m c z| := by
      rw [abs_mul, abs_of_nonneg hp0]
    have e2 : |rgQ α m * rgG1 α m c z| = rgQ α m * |rgG1 α m c z| := by
      rw [abs_mul, abs_of_nonneg hq0]
    calc rgK α m * |rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z|
        ≤ rgK α m * (|rgP α m * rgG2 α m c z| + |rgQ α m * rgG1 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_abs_add' _ _) hK0
      _ = rgK α m * (rgP α m * |rgG2 α m c z| + rgQ α m * |rgG1 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (rgP α m * (C2 / z) + rgQ α m * (CA / z)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hG2le z hz1) hp0)
              (mul_le_mul_of_nonneg_left (hG1le z hz1) hq0)) hK0
      _ = (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by ring
  -- ## (iii) the two limits
  have hBnn : 0 ≤ rgK α m * (CA + C2) := mul_nonneg hK0 hCAD
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm'
      (a := fun z : ℝ => ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2))) / z) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
      calc ‖z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2‖
          = |z * Work.FTS.PhiStar.Radial.radGreen α m c z|
              * |Work.FTS.PhiStar.Radial.radGreen α m c z| := by
            rw [Real.norm_eq_abs,
              show z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
                = (z * Work.FTS.PhiStar.Radial.radGreen α m c z)
                    * Work.FTS.PhiStar.Radial.radGreen α m c z from by ring,
              abs_mul]
        _ ≤ (rgK α m * (CA + C2)) * ((rgK α m * (CA + C2)) / z) :=
            mul_le_mul (hBnd_zrad z hz1) (hBnd_rad z hz1) (abs_nonneg _) hBnn
        _ = ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2))) / z := by ring
    · simpa using tendsto_const_div_atTop ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2)))
  · refine squeeze_zero_norm'
      (a := fun z : ℝ =>
        ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA))) / z) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
      calc ‖z * Work.FTS.PhiStar.Radial.radGreen α m c z
              * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)‖
          = |z * Work.FTS.PhiStar.Radial.radGreen α m c z|
              * |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ (rgK α m * (CA + C2))
              * ((rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z) :=
            mul_le_mul (hBnd_zrad z hz1) (hBnd_zd z hz1) (abs_nonneg _) hBnn
        _ = ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA))) / z := by
            ring
    · simpa using tendsto_const_div_atTop
        ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA)))

end Work.FTS.ClassC
