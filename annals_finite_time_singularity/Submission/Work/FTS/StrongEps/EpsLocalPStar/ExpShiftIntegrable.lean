import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Set

/-- The map `y ↦ z * exp (-y)` is a `C¹` diffeomorphism from `ℝ` onto `(0,∞)`; it carries
`Icc (-ε) ε` onto the compact positive interval `Icc (z * exp (-ε)) (z * exp ε)`.  Hence a
function which is integrable on every compact interval of positive reals has an integrable
pull-back under this exponential substitution. -/
theorem ExpShiftIntegrable {h : ℝ → ℝ} {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn h (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun x : ℝ => h (z * Real.exp (-x))) (Set.Icc (-ε) ε) := by
  have hz0 : z ≠ 0 := hz.ne'
  -- The positive interval which is the image of `Icc (-ε) ε`.
  set a : ℝ := z * Real.exp (-ε) with ha_def
  set b : ℝ := z * Real.exp ε with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have hb : 0 < b := by rw [hb_def]; positivity
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz.le
  have hloga : Real.log a = Real.log z - ε := by
    rw [ha_def, Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlogb : Real.log b = Real.log z + ε := by
    rw [hb_def, Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
  -- The inverse substitution `φ y = log z - log y`, which maps `Icc a b` onto `Icc (-ε) ε`.
  set φ : ℝ → ℝ := fun y => Real.log z - Real.log y with hφ
  have hderiv : ∀ y ∈ Set.Icc a b, HasDerivWithinAt φ (-(y⁻¹)) (Set.Icc a b) y := by
    intro y hy
    have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have hd : HasDerivAt (fun t : ℝ => Real.log z - Real.log t) (0 - y⁻¹) y :=
      (hasDerivAt_const y (Real.log z)).sub (Real.hasDerivAt_log hy0)
    simpa [hφ] using hd.hasDerivWithinAt
  have hinj : Set.InjOn φ (Set.Icc a b) := by
    intro y hy y' hy' heq
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hy0' : 0 < y' := lt_of_lt_of_le ha hy'.1
    have hlog : Real.log y = Real.log y' := by
      have h' := heq
      simp only [hφ] at h'
      linarith
    exact Real.log_injOn_pos hy0 hy0' hlog
  have himg : φ '' Set.Icc a b = Set.Icc (-ε) ε := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_Icc] at hy
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      have h1 : Real.log y ≤ Real.log z + ε := by
        rw [← hlogb]; exact Real.log_le_log hy0 hy.2
      have h2 : Real.log z - ε ≤ Real.log y := by
        rw [← hloga]; exact Real.log_le_log ha hy.1
      simp only [hφ, Set.mem_Icc]
      constructor <;> linarith
    · intro ht
      simp only [Set.mem_Icc] at ht
      refine ⟨z * Real.exp (-t), ?_, ?_⟩
      · simp only [ha_def, hb_def, Set.mem_Icc]
        constructor
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hz.le
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.1])) hz.le
      · simp only [hφ]
        rw [Real.log_mul hz0 (Real.exp_ne_zero _), Real.log_exp]
        ring
  -- Change of variables: integrability on `φ '' Icc a b` is equivalent to integrability of
  -- `|φ'| • (h ∘ φ)` on `Icc a b`.
  have key := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Icc a b) (f := φ) (f' := fun y => -(y⁻¹)) measurableSet_Icc hderiv hinj
    (fun x => h (z * Real.exp (-x)))
  rw [himg] at key
  rw [key]
  -- On `Icc a b` the factor `|φ' y| = y⁻¹` is bounded, and `h ∘ φ = h` there.
  have hcont : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro y hy; exact (lt_of_lt_of_le ha hy.1).ne'
  have h2 : MeasureTheory.IntegrableOn (fun y : ℝ => y⁻¹ * h y) (Set.Icc a b) :=
    MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcont (hint a b ha hab)
      isCompact_Icc measurableSet_Icc Subset.rfl
  rw [MeasureTheory.integrableOn_congr_fun
    (f := fun y : ℝ => |(-(y⁻¹))| • h (z * Real.exp (-(Real.log z - Real.log y))))
    (g := fun y : ℝ => y⁻¹ * h y) _ measurableSet_Icc]
  · exact h2
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hexp : z * Real.exp (-(Real.log z - Real.log y)) = y := by
      rw [show -(Real.log z - Real.log y) = Real.log y - Real.log z by ring]
      rw [Real.exp_sub, Real.exp_log hy0, Real.exp_log hz]
      field_simp
    have habs : |(-(y⁻¹))| = y⁻¹ := by
      rw [abs_neg, abs_of_pos (inv_pos.mpr hy0)]
    show |(-(y⁻¹))| • h (z * Real.exp (-(Real.log z - Real.log y))) = y⁻¹ * h y
    rw [hexp, habs, smul_eq_mul]

end Work.FTS.StrongEps.EpsLocalPStar
