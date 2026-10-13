import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.ClassCHon.HcoefSplit.radGreen_split_le_gen
import Submission.Work.FTS.ClassCHon.CmpSupp.cmode_facts
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.ClassCHon.Zpz.cmode_Dz
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_Dz
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.Honesty.Dzu_cmode_eqOn
import Submission.Work.FTS.PhiStar.Honesty.Dzu_radGreen_comm
import Submission.Work.FTS.PhiStar.Honesty.radGreen_supp_weight_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set

/-! ## A locality fact for the radial Green function -/

/-- `radGreen` only sees the values of the source on the open half-line `(0,∞)`: for `z > 0`
both integrals range over positive arguments only. -/
theorem radGreen_congr_Ioi {α : ℝ} (m : ℕ) {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m f z
      = Work.FTS.PhiStar.Radial.radGreen α m g z := by
  intro z hz
  have h1 : (∫ t in (0 : ℝ)..z, f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = (∫ t in (0 : ℝ)..z, g t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h ht.1])
  have h2 : (∫ t in Set.Ioi z, f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = (∫ t in Set.Ioi z, g t * t ^ (-(2 * (m : ℝ) / α) - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [h (lt_trans hz ht)])
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-! ## The assembly -/

theorem acoeff_DzIter_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (l N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter l (fun z' _ => Work.FTS.PhiStar.Series.acoeff α j G z') z 0|
        ≤ C * ((j : ℝ) + 1) ^ (-(N : ℝ))
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  -- the two uniform constants
  obtain ⟨CB, hCBpos, hCB⟩ := radGreen_supp_weight_le (α := α) hα ha hab
  obtain ⟨Cd, hCd0, hCd⟩ := cmode_decay_of_cptQ (G := G) hG l N
  have hGsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry G) :=
    contDiff_infty.mpr (fun n => hG.smooth n)
  refine ⟨CB * max Cd 1, by positivity, fun j hj z hz => ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  set M : ℝ := max Cd 1 * ((j : ℝ) + 1) ^ (-(N : ℝ)) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.rpow_nonneg hjpos.le _)
  -- the source is the `j`-th angular mode of `D_z^l G`, which decays rapidly in `j`
  have hdec : ∀ t : ℝ, |Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t| ≤ M := by
    intro t
    have h1 : |Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t|
        ≤ Cd / ((j : ℝ) + 1) ^ N := hCd j hj t
    have h2 : Cd / ((j : ℝ) + 1) ^ N = Cd * ((j : ℝ) + 1) ^ (-(N : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_neg hjpos.le, Real.rpow_natCast]
    rw [h2] at h1
    rw [hM]
    exact h1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hjpos.le _))
  have hsupF : ∀ t : ℝ, t ∉ Set.Icc a b →
      Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t = 0 := by
    intro t ht
    have hFsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.DzIter l G z θ = 0 :=
      fun z θ hz' => DzIter_eq_zero_of_z_not_mem
        (fun z θ h => by
          by_contra hmem
          exact h (hsupp z θ hmem)) l hz'
    have hFsm : ContDiff ℝ Work.Stability.smoothOrder
        (Function.uncurry (Work.Spaces.DzIter l G)) :=
      contDiff_infty.mpr (fun n => DzIter_contDiff_of_forall_end hG.smooth l n)
    exact (Work.FTS.ClassCHon.CmpSupp.cmode_facts (F := Work.Spaces.DzIter l G) ha hFsm hFsupp).2.1 j t ht
  -- the mode coefficient of `G` is smooth on `(0,∞)` and supported in `[a,b]`
  have hcfG :=
    Work.FTS.ClassCHon.CmpSupp.cmode_facts (F := G) ha hGsm hsupp
  have hcd : ContDiffOn ℝ (l + 1 : ℕ)
      (fun t => Work.FTS.PhiStar.Series.cmode j G t) (Set.Ioi 0) :=
    hcfG.1 j (l + 1)
  have hsupG : ∀ t : ℝ, t ∉ Set.Icc a b → Work.FTS.PhiStar.Series.cmode j G t = 0 :=
    hcfG.2.1 j
  have hcomm1 : Work.FTS.EllExist.Honesty.Dzu l
        (Work.FTS.PhiStar.Radial.radGreen α j
          (fun t => Work.FTS.PhiStar.Series.cmode j G t)) z
      = Work.FTS.PhiStar.Radial.radGreen α j
        (Work.FTS.EllExist.Honesty.Dzu l (fun t => Work.FTS.PhiStar.Series.cmode j G t)) z :=
    Dzu_radGreen_comm (α := α) hα j l ha hab hcd hsupG z hz
  -- and `D_z` commutes with the mode coefficient
  have hcomm2 : Work.FTS.EllExist.Honesty.Dzu l
        (fun t => Work.FTS.PhiStar.Series.cmode j G t) z
      = Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) z :=
    Dzu_cmode_eqOn hG l j hz
  have hrg : Work.FTS.PhiStar.Radial.radGreen α j
        (Work.FTS.EllExist.Honesty.Dzu l (fun t => Work.FTS.PhiStar.Series.cmode j G t)) z
      = Work.FTS.PhiStar.Radial.radGreen α j
        (fun t => Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t) z :=
    radGreen_congr_Ioi j (fun t ht => Dzu_cmode_eqOn hG l j ht) z hz
  have hbound : |Work.FTS.PhiStar.Radial.radGreen α j
        (fun t => Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t) z|
      ≤ CB * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
    hCB M hM0 hsupF hdec j hj z hz
  calc |Work.Spaces.DzIter l (fun z' _ => Work.FTS.PhiStar.Series.acoeff α j G z') z 0|
      = |Work.FTS.EllExist.Honesty.Dzu l (Work.FTS.PhiStar.Series.acoeff α j G) z| := by
        rw [Work.FTS.EllExist.Honesty.DzIter_zOnly]
    _ = |Work.FTS.EllExist.Honesty.Dzu l (Work.FTS.PhiStar.Radial.radGreen α j
          (fun t => Work.FTS.PhiStar.Series.cmode j G t)) z| := by
        rw [show Work.FTS.PhiStar.Series.acoeff α j G
            = Work.FTS.PhiStar.Radial.radGreen α j
              (fun t => Work.FTS.PhiStar.Series.cmode j G t) from rfl]
    _ = |Work.FTS.PhiStar.Radial.radGreen α j
          (Work.FTS.EllExist.Honesty.Dzu l (fun t => Work.FTS.PhiStar.Series.cmode j G t)) z| := by
        rw [hcomm1]
    _ = |Work.FTS.PhiStar.Radial.radGreen α j
          (fun t => Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter l G) t) z| := by
        rw [hrg]
    _ ≤ CB * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := hbound
    _ = CB * max Cd 1 * ((j : ℝ) + 1) ^ (-(N : ℝ))
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
        rw [hM]; ring

end Work.FTS.PhiStar.Honesty
