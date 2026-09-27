import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.fermiW_chart
import Submission.Work.Mostow.stab_eq_blk

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- Real-variable core: if `sinh (D/2)^2 ≤ X^2 + Y^2` with `D, X, Y ≥ 0`, then
`D ≤ 2 * arsinh X + 2 * arsinh Y`.  Indeed `sinh (D/2) ≤ √(X²+Y²) ≤ X + Y`,
and `X + Y ≤ sinh (arsinh X + arsinh Y)` because `sinh` is superadditive on `[0,∞)`. -/
private lemma le_two_arsinh_add {D X Y : ℝ} (hD : 0 ≤ D) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : Real.sinh (D / 2) ^ 2 ≤ X ^ 2 + Y ^ 2) :
    D ≤ 2 * Real.arsinh X + 2 * Real.arsinh Y := by
  have hS0 : 0 ≤ Real.sinh (D / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have h1 : Real.sinh (D / 2) ≤ Real.sqrt (X ^ 2 + Y ^ 2) := by
    rw [← Real.sqrt_sq hS0]
    exact Real.sqrt_le_sqrt h
  have h2 : Real.sqrt (X ^ 2 + Y ^ 2) ≤ X + Y := by
    calc Real.sqrt (X ^ 2 + Y ^ 2) ≤ Real.sqrt ((X + Y) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hX, hY])
      _ = X + Y := Real.sqrt_sq (by linarith)
  have h3 : X + Y ≤ Real.sinh (Real.arsinh X + Real.arsinh Y) := by
    rw [Real.sinh_add, Real.sinh_arsinh, Real.sinh_arsinh]
    have hcx : 1 ≤ Real.cosh (Real.arsinh X) := Real.one_le_cosh _
    have hcy : 1 ≤ Real.cosh (Real.arsinh Y) := Real.one_le_cosh _
    nlinarith [hX, hY, hcx, hcy]
  have h4 : Real.sinh (D / 2) ≤ Real.sinh (Real.arsinh X + Real.arsinh Y) :=
    le_trans (le_trans h1 h2) h3
  have h5 : D / 2 ≤ Real.arsinh X + Real.arsinh Y := Real.sinh_le_sinh.mp h4
  linarith

theorem geeDisplacement (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (hc : c ∈ Submission.Mostow.SetStabStd 1 m)
    (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdispt : Submission.Mostow.hdist v (Submission.Mostow.resStd 1 m c • v) ≤ a)
    (hdispn : ‖(Submission.Mostow.nrmStd 1 m c) W - W‖ ≤ b) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W) (c • Submission.Mostow.fermiW 1 m v W)
      ≤ 2 * Real.arsinh (Real.sqrt (1 + ‖W‖ ^ 2) * Real.sinh (a / 2)) + 2 * Real.arsinh (b / 2) := by
  set h : PO 1 1 := resStd 1 m c with hh
  set R : E m ≃ₗᵢ[ℝ] E m := nrmStd 1 m c with hR
  have hcblk : c = blk 1 m h R := by
    rw [hh, hR]
    exact stab_eq_blk 1 m hA1 hI1 hA hI c hc
  have hdisp : Real.sinh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (c • Submission.Mostow.fermiW 1 m v W) / 2) ^ 2
      = (1 + ‖W‖ ^ 2) * Real.sinh (Submission.Mostow.hdist v (h • v) / 2) ^ 2
        + ‖R W - W‖ ^ 2 / 4 := by
    rw [hcblk]
    exact disp_fermiW m hA1 hI1 hA hI h R v W
  have hX0 : 0 ≤ Real.sqrt (1 + ‖W‖ ^ 2) * Real.sinh (a / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr (by linarith))
  have hY0 : 0 ≤ b / 2 := by linarith
  have hsq : Real.sinh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (c • Submission.Mostow.fermiW 1 m v W) / 2) ^ 2
      ≤ (Real.sqrt (1 + ‖W‖ ^ 2) * Real.sinh (a / 2)) ^ 2 + (b / 2) ^ 2 := by
    rw [hdisp, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + ‖W‖ ^ 2)]
    have hsdsq : Real.sinh (Submission.Mostow.hdist v (h • v) / 2) ^ 2
        ≤ Real.sinh (a / 2) ^ 2 := by
      have hsd : Real.sinh (Submission.Mostow.hdist v (h • v) / 2) ≤ Real.sinh (a / 2) :=
        Real.sinh_le_sinh.mpr (by linarith [hdispt])
      have h1 : 0 ≤ Real.sinh (Submission.Mostow.hdist v (h • v) / 2) :=
        Real.sinh_nonneg_iff.mpr (by linarith [nib_hdist_nonneg v (h • v)])
      have h2 : 0 ≤ Real.sinh (a / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
      nlinarith [hsd, h1, h2]
    have hbsq : (‖R W - W‖ / 2) ^ 2 ≤ (b / 2) ^ 2 :=
      by nlinarith [hdispn, norm_nonneg (R W - W), hb]
    have hmul := mul_le_mul_of_nonneg_left hsdsq (by positivity : (0 : ℝ) ≤ 1 + ‖W‖ ^ 2)
    have hbb : ‖R W - W‖ ^ 2 / 4 = (‖R W - W‖ / 2) ^ 2 := by ring
    rw [hbb]
    linarith
  have hDnn : 0 ≤ Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
      (c • Submission.Mostow.fermiW 1 m v W) := nib_hdist_nonneg _ _
  exact le_two_arsinh_add hDnn hX0 hY0 hsq

end Work.Mostow
