import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- **Hölder with exponents `p = 4`, `q = 4/3`.**  On a set of finite measure, the `L¹` norm of
`f` is controlled by the `L⁴` norm times `(volume s)^{3/4}`. -/
theorem integral_abs_le_L4_mul_vol {s : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : MeasureTheory.volume s < ⊤)
    (hf : MeasureTheory.MemLp f 4 (MeasureTheory.volume.restrict s)) :
    ∫ x in s, |f x| ≤ (MeasureTheory.volume s).toReal ^ (3 / 4 : ℝ)
      * (∫ x in s, |f x| ^ 4) ^ (1 / 4 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf' : MemLp f (ENNReal.ofReal (4 : ℝ)) (MeasureTheory.volume.restrict s) := by
    simpa using hf
  -- `s` has finite measure, so the constant function `1` lies in `L^{4/3}` on it
  have hg : MemLp (fun _ : ℝ × ℝ => (1 : ℝ)) (ENNReal.ofReal (4 / 3))
      (MeasureTheory.volume.restrict s) := by
    rw [memLp_const_iff (p := ENNReal.ofReal (4 / 3)) (c := (1 : ℝ))
      (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) ENNReal.ofReal_ne_top]
    right
    rw [Measure.restrict_apply_univ]
    exact hs
  have hmain := integral_mul_norm_le_Lp_mul_Lq (μ := MeasureTheory.volume.restrict s)
    (f := f) (g := fun _ : ℝ × ℝ => (1 : ℝ)) hpq hf' hg
  -- the two `L^p` factors simplify to the two quantities in the statement
  have hA : ∫ a, ‖f a‖ ^ (4 : ℝ) ∂(MeasureTheory.volume.restrict s)
      = ∫ x in s, |f x| ^ 4 := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.rpow_ofNat]
  have hB : ∫ a, ‖(1 : ℝ)‖ ^ ((4 : ℝ) / 3) ∂(MeasureTheory.volume.restrict s)
      = (MeasureTheory.volume s).toReal := by
    simp [Measure.real_def]
  rw [hA, hB] at hmain
  calc ∫ x in s, |f x|
      = ∫ a, ‖f a‖ * ‖(1 : ℝ)‖ ∂(MeasureTheory.volume.restrict s) := by
        simp [Real.norm_eq_abs]
    _ ≤ _ := hmain
    _ = (MeasureTheory.volume s).toReal ^ (3 / 4 : ℝ)
          * (∫ x in s, |f x| ^ 4) ^ (1 / 4 : ℝ) := by
        rw [show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num, mul_comm]

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
