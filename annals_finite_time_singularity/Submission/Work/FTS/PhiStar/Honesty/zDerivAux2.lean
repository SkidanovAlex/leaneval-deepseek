import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.zDerivAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Real

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

variable {α : ℝ} {m : ℕ} {c : ℝ → ℝ}

/-! ### the a.e. derivative identity for `z * deriv radGreen` -/

/-! ### the a.e. derivative identity for `z * deriv radGreen` -/

theorem zg_ae_zderiv_radGreen (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ᵐ z ∂volume, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.EllExist.rgK α m * (Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z
            - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgG1 α m c z) := by
  have hA := zg_ae_hasDerivAt_rgA hα hα4 hm hc hnear hfar
  have hB := zg_ae_hasDerivAt_rgB hα hα4 hm hc hnear hfar
  filter_upwards [hA, hB] with z hzA hzB hz
  have hzA' : HasDerivAt (Work.FTS.EllExist.rgA α m c) (Work.FTS.EllExist.rgF1 α m c z) z := hzA hz
  have hzB' : HasDerivAt (Work.FTS.EllExist.rgB α m c) (-(Work.FTS.EllExist.rgF2 α m c z)) z :=
    hzB hz
  have hd1 : HasDerivAt (fun y : ℝ => y ^ (-(Work.FTS.EllExist.rgQ α m)))
      (-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := -(Work.FTS.EllExist.rgQ α m)) (Or.inl (ne_of_gt hz))
  have hd2 : HasDerivAt (fun y : ℝ => y ^ (Work.FTS.EllExist.rgP α m))
      (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := Work.FTS.EllExist.rgP α m) (Or.inl (ne_of_gt hz))
  have hG1 : HasDerivAt (Work.FTS.EllExist.rgG1 α m c)
      ((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
        * Work.FTS.EllExist.rgA α m c z
        + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z) z :=
    hd1.mul hzA'
  have hG2 : HasDerivAt (Work.FTS.EllExist.rgG2 α m c)
      (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
        * Work.FTS.EllExist.rgB α m c z
        + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z))) z :=
    hd2.mul hzB'
  have hR : HasDerivAt (fun y : ℝ => Work.FTS.EllExist.rgK α m *
      (Work.FTS.EllExist.rgG1 α m c y + Work.FTS.EllExist.rgG2 α m c y))
      (Work.FTS.EllExist.rgK α m *
        (((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
            * Work.FTS.EllExist.rgA α m c z
            + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
          + (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z
              + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z))))) z :=
    (hG1.add hG2).const_mul (Work.FTS.EllExist.rgK α m)
  have hfun : (fun y : ℝ => Work.FTS.EllExist.rgK α m *
      (Work.FTS.EllExist.rgG1 α m c y + Work.FTS.EllExist.rgG2 α m c y))
      = Work.FTS.PhiStar.Radial.radGreen α m c := by
    funext y
    rw [Work.FTS.EllExist.radGreen_eq]
    simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]
  have hRd : HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (Work.FTS.EllExist.rgK α m *
        (((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
            * Work.FTS.EllExist.rgA α m c z
            + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
          + (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z
              + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z))))) z :=
    hR.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)
  rw [hRd.deriv]
  -- rpow arithmetic
  have hA1 : z * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1)
      = z ^ (-(Work.FTS.EllExist.rgQ α m)) := by
    have h := Real.rpow_add hz (1 : ℝ) (-(Work.FTS.EllExist.rgQ α m) - 1)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (-(Work.FTS.EllExist.rgQ α m) - 1)
      = -(Work.FTS.EllExist.rgQ α m) from by ring] at h
    exact h.symm
  have hA2 : z * z ^ (-(Work.FTS.EllExist.rgQ α m)) = z ^ (1 - Work.FTS.EllExist.rgQ α m) := by
    have h := Real.rpow_add hz (1 : ℝ) (-(Work.FTS.EllExist.rgQ α m))
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (-(Work.FTS.EllExist.rgQ α m)) = 1 - Work.FTS.EllExist.rgQ α m from by ring] at h
    exact h.symm
  have hA3 : z ^ (1 - Work.FTS.EllExist.rgQ α m) * z ^ (Work.FTS.EllExist.rgQ α m - 1) = 1 := by
    have h := Real.rpow_add hz (1 - Work.FTS.EllExist.rgQ α m) (Work.FTS.EllExist.rgQ α m - 1)
    rw [show (1 - Work.FTS.EllExist.rgQ α m) + (Work.FTS.EllExist.rgQ α m - 1) = 0 from by ring,
      Real.rpow_zero] at h
    exact h.symm
  have hB1 : z * z ^ (Work.FTS.EllExist.rgP α m - 1) = z ^ (Work.FTS.EllExist.rgP α m) := by
    have h := Real.rpow_add hz (1 : ℝ) (Work.FTS.EllExist.rgP α m - 1)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (Work.FTS.EllExist.rgP α m - 1) = Work.FTS.EllExist.rgP α m from by ring] at h
    exact h.symm
  have hB2 : z * z ^ (Work.FTS.EllExist.rgP α m) = z ^ (Work.FTS.EllExist.rgP α m + 1) := by
    have h := Real.rpow_add hz (1 : ℝ) (Work.FTS.EllExist.rgP α m)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + Work.FTS.EllExist.rgP α m = Work.FTS.EllExist.rgP α m + 1 from by ring] at h
    exact h.symm
  have hB3 : z ^ (Work.FTS.EllExist.rgP α m + 1) * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) = 1 := by
    have h := Real.rpow_add hz (Work.FTS.EllExist.rgP α m + 1) (-(Work.FTS.EllExist.rgP α m) - 1)
    rw [show (Work.FTS.EllExist.rgP α m + 1) + (-(Work.FTS.EllExist.rgP α m) - 1) = 0 from by ring,
      Real.rpow_zero] at h
    exact h.symm
  have hcf1 : z ^ (1 - Work.FTS.EllExist.rgQ α m) * Work.FTS.EllExist.rgF1 α m c z = c z := by
    simp only [Work.FTS.EllExist.rgF1]
    rw [show z ^ (1 - Work.FTS.EllExist.rgQ α m) * (c z * z ^ (Work.FTS.EllExist.rgQ α m - 1))
        = c z * (z ^ (1 - Work.FTS.EllExist.rgQ α m) * z ^ (Work.FTS.EllExist.rgQ α m - 1))
        from by ring, hA3, mul_one]
  have hcf2 : z ^ (Work.FTS.EllExist.rgP α m + 1) * Work.FTS.EllExist.rgF2 α m c z = c z := by
    simp only [Work.FTS.EllExist.rgF2]
    rw [show z ^ (Work.FTS.EllExist.rgP α m + 1) * (c z * z ^ (-(Work.FTS.EllExist.rgP α m) - 1))
        = c z * (z ^ (Work.FTS.EllExist.rgP α m + 1) * z ^ (-(Work.FTS.EllExist.rgP α m) - 1))
        from by ring, hB3, mul_one]
  have hD1 : z *
      ((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
          * Work.FTS.EllExist.rgA α m c z
          + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
      = -(Work.FTS.EllExist.rgQ α m) * Work.FTS.EllExist.rgG1 α m c z + c z := by
    have e1 : z * ((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
        * Work.FTS.EllExist.rgA α m c z)
        = -(Work.FTS.EllExist.rgQ α m)
          * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z) := by
      rw [← hA1]; ring
    have e2 : z * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z) = c z := by
      rw [show z * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
          = (z * z ^ (-(Work.FTS.EllExist.rgQ α m))) * Work.FTS.EllExist.rgF1 α m c z from by ring,
        hA2, hcf1]
    rw [mul_add, e1, e2, show Work.FTS.EllExist.rgG1 α m c z
      = z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z from rfl]
  have hD2 : z *
      (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
          * Work.FTS.EllExist.rgB α m c z
          + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z)))
      = Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z - c z := by
    have e3 : z * (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
        * Work.FTS.EllExist.rgB α m c z)
        = Work.FTS.EllExist.rgP α m
          * (z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z) := by
      rw [← hB1]; ring
    have e4 : z * (z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z))) = -(c z) := by
      rw [show z * (z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z)))
          = -((z * z ^ (Work.FTS.EllExist.rgP α m)) * Work.FTS.EllExist.rgF2 α m c z) from by ring,
        hB2, hcf2]
    rw [mul_add, e3, e4, show Work.FTS.EllExist.rgG2 α m c z
      = z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z from rfl]
    ring
  have key : z *
      (((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
          * Work.FTS.EllExist.rgA α m c z
          + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
        + (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
            * Work.FTS.EllExist.rgB α m c z
            + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z))))
      = Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z
        - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgG1 α m c z := by
    rw [mul_add, hD1, hD2]
    ring
  rw [show z * (Work.FTS.EllExist.rgK α m *
        (((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
            * Work.FTS.EllExist.rgA α m c z
            + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
          + (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z
              + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z)))))
      = Work.FTS.EllExist.rgK α m * (z *
        (((-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1))
            * Work.FTS.EllExist.rgA α m c z
            + z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgF1 α m c z)
          + (Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z
              + z ^ (Work.FTS.EllExist.rgP α m) * (-(Work.FTS.EllExist.rgF2 α m c z)))))
      from by ring]
  rw [key]

end Work.FTS.PhiStar.Honesty
