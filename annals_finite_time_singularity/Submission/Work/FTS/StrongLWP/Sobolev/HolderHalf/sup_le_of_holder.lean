import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- **Averaging core of the `C^{1/2}` sup bound.**  Let `s` be a measurable set of volume `4`
all of whose points are at distance at most `1` from `p` (think of the open unit square centred
at `p`, which in the product metric on `ℝ × ℝ` has volume `4` and diameter `2`).  If `v` obeys
the Hölder-`1/2` bound with constant `P ≥ 0`, then on account of the pointwise estimate
`|v p| ≤ |v p - v z| + |v z| ≤ P + |v z|` (`z ∈ s`) and Cauchy–Schwarz on `s`,
`|v p| ≤ P + (1/2) √(∫_s v²)`. -/
theorem abs_le_of_holder_on_set {v : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} {p : ℝ × ℝ} {P : ℝ}
    (hP : 0 ≤ P) (hM : ∀ z z' : ℝ × ℝ, |v z - v z'| ≤ P * Real.sqrt (dist z z'))
    (hs : MeasurableSet s) (hvol : volume s = ENNReal.ofReal 4)
    (hdiam : ∀ z ∈ s, dist z p ≤ 1)
    (hint2 : IntegrableOn (fun z => (v z) ^ 2) s)
    (hint1 : IntegrableOn (fun z => |v z|) s) :
    |v p| ≤ P + Real.sqrt (∫ z in s, (v z) ^ 2) / 2 := by
  have hvolreal : volume.real s = 4 := by
    change (volume s).toReal = 4
    rw [hvol, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  -- the pointwise bound `|v p| ≤ P + |v z|` on `s`
  have hpt : ∀ z ∈ s, |v p| ≤ P + |v z| := by
    intro z hz
    have h1 : |v p - v z| ≤ P := by
      have h3 : Real.sqrt (dist p z) ≤ 1 := by
        rw [Real.sqrt_le_one, dist_comm]
        exact hdiam z hz
      calc |v p - v z| ≤ P * Real.sqrt (dist p z) := hM p z
        _ ≤ P * 1 := mul_le_mul_of_nonneg_left h3 hP
        _ = P := mul_one P
    rw [show v p = (v p - v z) + v z from by ring]
    exact (abs_add_le _ _).trans (add_le_add h1 le_rfl)
  have hIntP : Integrable (fun z : ℝ × ℝ => P + |v z|) (volume.restrict s) :=
    (integrable_const P).add hint1
  have hIntc : Integrable (fun _ : ℝ × ℝ => |v p|) (volume.restrict s) :=
    integrable_const (|v p|)
  have hmono : (∫ z in s, |v p|) ≤ ∫ z in s, (P + |v z|) :=
    MeasureTheory.setIntegral_mono_on hIntc hIntP hs (fun z hz => hpt z hz)
  have hL : (∫ z in s, |v p|) = 4 * |v p| := by
    rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
  have hR : (∫ z in s, (P + |v z|)) = 4 * P + ∫ z in s, |v z| := by
    have h1 := MeasureTheory.integral_add (f := fun _ : ℝ × ℝ => P)
      (g := fun z : ℝ × ℝ => |v z|) (integrable_const P) hint1
    rw [h1]
    have h2 : (∫ z in s, (P : ℝ)) = 4 * P := by
      rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
    rw [h2]
  -- Cauchy–Schwarz on `s`
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict s)
    (f := fun z : ℝ × ℝ => |v z|) (g := fun _ : ℝ × ℝ => (1 : ℝ))
    hint1.aestronglyMeasurable aestronglyMeasurable_const
    (hint2.congr (Filter.Eventually.of_forall fun z => (sq_abs (v z)).symm))
    (by
      have h1 : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (volume.restrict s) :=
        integrable_const (1 : ℝ)
      simpa only [one_pow] using h1)
  have hL2 : (∫ z in s, |v z| ^ 2) = ∫ z in s, (v z) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs (v z))
  have hone : (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s)) = 4 := by
    have h1 : (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s))
        = ∫ _z : ℝ × ℝ, (1 : ℝ) ∂(volume.restrict s) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => one_pow 2)
    rw [h1, MeasureTheory.integral_const]
    change ((volume.restrict s) Set.univ).toReal * 1 = 4
    rw [Measure.restrict_apply_univ, hvol,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hCS : (∫ z in s, |v z|) ≤ 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
    have h1 : |∫ z : ℝ × ℝ, |v z| * 1 ∂(volume.restrict s)| = ∫ z in s, |v z| := by
      rw [show (fun z : ℝ × ℝ => |v z| * 1) = fun z => |v z| from by funext z; rw [mul_one]]
      exact abs_of_nonneg (MeasureTheory.integral_nonneg
        (f := fun z : ℝ × ℝ => |v z|) fun z => abs_nonneg (v z))
    calc (∫ z in s, |v z|) = |∫ z : ℝ × ℝ, |v z| * 1 ∂(volume.restrict s)| := h1.symm
      _ ≤ Real.sqrt (∫ z : ℝ × ℝ, |v z| ^ 2 ∂(volume.restrict s))
            * Real.sqrt (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s)) := hcs
      _ = 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
          rw [hL2, hone, show Real.sqrt 4 = 2 by norm_num]
          ring
  have h4 : 4 * |v p| ≤ 4 * P + 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
    calc 4 * |v p| = ∫ z in s, |v p| := hL.symm
      _ ≤ ∫ z in s, (P + |v z|) := hmono
      _ = 4 * P + ∫ z in s, |v z| := hR
      _ ≤ 4 * P + 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by linarith
  linarith

theorem sup_le_of_holder {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (P : ℝ) (hP : 0 ≤ P) (hM : ∀ z z' : ℝ × ℝ, |v z - v z'| ≤ P * Real.sqrt (dist z z')) :
    ∀ p : ℝ × ℝ, |v p| ≤ P + Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) / 2 := by
  intro p
  have hcont : Continuous v := hv.continuous
  set s : Set (ℝ × ℝ) :=
    Set.Ioo (p.1 - 1) (p.1 + 1) ×ˢ Set.Ioo (p.2 - 1) (p.2 + 1) with hsdef
  have hsm : MeasurableSet s := by
    rw [hsdef]
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hvol : volume s = ENNReal.ofReal 4 := by
    rw [hsdef, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      show p.1 + 1 - (p.1 - 1) = 2 by ring, show p.2 + 1 - (p.2 - 1) = 2 by ring,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hdiam : ∀ z ∈ s, dist z p ≤ 1 := by
    intro z hz
    rw [hsdef] at hz
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (le_of_lt (abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩))
      (le_of_lt (abs_lt.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩))
  have hIntv : Integrable v volume := hcont.integrable_of_hasCompactSupport hc
  have hInt1 : Integrable (fun z : ℝ × ℝ => |v z|) volume := hIntv.abs
  have hInt2 : Integrable (fun z : ℝ × ℝ => (v z) ^ 2) volume := by
    have hsupp : HasCompactSupport (fun z : ℝ × ℝ => (v z) ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact (hcont.pow 2).integrable_of_hasCompactSupport hsupp
  have hbound := abs_le_of_holder_on_set (v := v) (s := s) (p := p) (P := P) hP hM hsm hvol
    hdiam hInt2.restrict hInt1.restrict
  have hmonoJ : (∫ z in s, (v z) ^ 2) ≤ ∫ z : ℝ × ℝ, (v z) ^ 2 :=
    MeasureTheory.setIntegral_le_integral hInt2 (Filter.Eventually.of_forall fun z => sq_nonneg _)
  calc |v p| ≤ P + Real.sqrt (∫ z in s, (v z) ^ 2) / 2 := hbound
    _ ≤ P + Real.sqrt (∫ z : ℝ × ℝ, (v z) ^ 2) / 2 := by
        linarith [Real.sqrt_le_sqrt hmonoJ]

end Work.FTS.StrongLWP.Sobolev.HolderHalf
