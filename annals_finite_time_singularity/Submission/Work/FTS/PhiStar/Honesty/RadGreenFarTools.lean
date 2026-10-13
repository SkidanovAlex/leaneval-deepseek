/-
# Shared measure-theoretic tools for the far-field `radGreen` estimates

Elementary tools used by both `RadGreenFarField` (the `G2` half) and `RadGreenFarG1` (the `G1`
half) of the far-field weighted `L²`-integrability of `radGreen`: the weighted AM–GM, the bound
`w² ≤ 16` on `(1,∞)`, the "uniform interval bounds give integrability" criterion on `(1,∞)`, and
the energy identity `(z A²)' = (1 + 2s)·A² + 2 d·A` for a solution of `z A' = s·A + d`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.FarAux.Basic
import Submission.Work.FTS.PhiStar.Honesty.IoiTool

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G2 G1f)
open Work.FTS.PhiStar.RadialWAux (radP radQ)

/-! ### Elementary tools -/
/-- Weighted AM–GM: `2|XY| ≤ l·X² + (1/l)·Y²` for `l > 0`. -/
theorem radFar_two_mul_abs_mul_le_inv {l X Y : ℝ} (hl : 0 < l) :
    2 * |X * Y| ≤ l * X ^ 2 + (1 / l) * Y ^ 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq (l * |X|) (|Y|)
  have h' : (l * |X|) ^ 2 + |Y| ^ 2 = l ^ 2 * X ^ 2 + Y ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]
  have h3 : 2 * (|X| * |Y|) * l ≤ l ^ 2 * X ^ 2 + Y ^ 2 := by
    have h'' : 2 * (l * |X|) * |Y| = 2 * (|X| * |Y|) * l := by ring
    linarith [h, h']
  have h5' : (1 / l) * Y ^ 2 * l = Y ^ 2 := by
    rw [one_div, mul_assoc, mul_comm (Y ^ 2) l, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hl),
      one_mul]
  have h5 : (l * X ^ 2 + (1 / l) * Y ^ 2) * l = l ^ 2 * X ^ 2 + Y ^ 2 := by
    rw [add_mul, h5']
    ring
  have h4 : 2 * (|X| * |Y|) * l ≤ (l * X ^ 2 + (1 / l) * Y ^ 2) * l := by
    rw [h5]
    exact h3
  exact le_of_mul_le_mul_right h4 hl

/-- Weighted AM–GM with two prescribed coefficients: `2|XY| ≤ l·X² + m·Y²` when `l > 0`,
`m > 0` and `l·m = 1`. -/
theorem radFar_amgm {l m X Y : ℝ} (hl : 0 < l) (hm : 0 < m) (hlm : l * m = 1) :
    2 * |X * Y| ≤ l * X ^ 2 + m * Y ^ 2 := by
  have h := radFar_two_mul_abs_mul_le_inv hl (X := X) (Y := Y)
  have h1l : 1 / l = m := by
    rw [div_eq_iff (ne_of_gt hl), mul_comm]
    exact hlm.symm
  rwa [h1l] at h



/-- Measurability of `z ↦ w z ^ 2` on `(1,∞)`. -/
theorem radFar_aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 1)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine (ContinuousOn.div ?_ ?_ ?_).pow 2
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · exact (continuous_id.pow 2).continuousOn
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.mp hz)))

/-- The weight on `(1,∞)` is bounded by `16`. -/
theorem radFar_ae_norm_w_sq_le :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 1)),
      ‖(fun z : ℝ => (Work.Spaces.w z) ^ 2) z‖ ≤ 16 := by
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine ae_of_all _ fun z hz => ?_
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have h0 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg h0]
  exact Work.FTS.EllExist.Honesty.w_sq_le_sixteen_of_one_le hz1

/-- Multiplying an integrable function on `(1,∞)` by the bounded weight `w²` keeps it integrable. -/
theorem radFar_integrableOn_mul_w_sq {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => g z * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) :=
  (Integrable.bdd_mul hg radFar_aestronglyMeasurable_w_sq radFar_ae_norm_w_sq_le).congr
    (ae_of_all _ fun z => by ring)

/-- **Uniform interval bounds on `(1,∞)` give integrability**: for a nonnegative continuous `f` on
`(0,∞)` with `∫_1^y f ≤ T` for every `y > 1`, the function `f` is integrable on `(1,∞)`. -/
theorem radFar_integrableOn_Ioi_one_of_sq_interval_bound {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hfnn : ∀ z : ℝ, 0 ≤ f z)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hb : ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, f z) ≤ T) :
    MeasureTheory.IntegrableOn f (Set.Ioi 1) := by
  refine (integrableOn_Ioi_one_of_interval_bounds (f := f) (T := T) ?_ ?_ ?_).1
  · intro z hz
    exact hfnn z
  · intro i
    have hsub : Set.Icc (1 : ℝ) ((i : ℝ) + 1) ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      have hz1 : (1 : ℝ) ≤ z := hz.1
      show (0 : ℝ) < z
      linarith
    exact ((hcont.mono hsub).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  · intro i
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hempty : Set.Ioc (1 : ℝ) (((0 : ℕ) : ℝ) + 1) = ∅ := by
        rw [Set.Ioc_eq_empty_iff]
        norm_num
      rw [hempty]
      rw [MeasureTheory.setIntegral_empty]
      exact hT
    · have hpos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast h0
      have hle : (1 : ℝ) < (i : ℝ) + 1 := by linarith
      rw [← intervalIntegral.integral_of_le hle.le]
      exact hb _ hle

/-- The energy identity for a solution of `z A' = s·A + d`: `(z·A²)' = (1 + 2s)·A² + 2d·A`. -/
theorem radFar_hasDerivAt_mul_sq {A : ℝ → ℝ} {s : ℝ} {d : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt A ((s * A z + d z) / z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (A y) ^ 2)
      ((1 + 2 * s) * (A z) ^ 2 + 2 * d z * A z) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hd := h z hz
  have hprod : HasDerivAt (fun y : ℝ => y * (A y) ^ 2)
      (1 * (A z) ^ 2 + z * (2 * (A z) * ((s * A z + d z) / z))) z := by
    have hh := (hasDerivAt_id z).mul (hd.pow 2)
    have hfun : (fun y : ℝ => y * (A y) ^ 2) = (id * A ^ 2 : ℝ → ℝ) := by
      funext y
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    refine (hh.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv ?_
    simp only [Pi.pow_apply, id_eq]
    ring
  refine hprod.congr_deriv ?_
  field_simp
  ring

end Work.FTS.PhiStar.Honesty
