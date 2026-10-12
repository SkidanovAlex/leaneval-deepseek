import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Trunc

open MeasureTheory Filter
open scoped Topology ContDiff

/-- The scaling factor `n + 1`. -/
noncomputable def cutoffScale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The `n`-th cutoff function `t ↦ (n + 1) * sin (t / (n + 1))`. -/
noncomputable def cutoffPsi (n : ℕ) (t : ℝ) : ℝ :=
  cutoffScale n * Real.sin (t * (cutoffScale n)⁻¹)

lemma cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  unfold cutoffScale; positivity

lemma cutoffScale_ne_zero (n : ℕ) : cutoffScale n ≠ 0 := (cutoffScale_pos n).ne'

lemma cutoffPsi_contDiff (n : ℕ) : ContDiff ℝ ⊤ (cutoffPsi n) := by
  unfold cutoffPsi
  have h : ContDiff ℝ ⊤ (fun t : ℝ => Real.sin (t * (cutoffScale n)⁻¹)) :=
    (Real.contDiff_sin (n := ⊤)).comp (contDiff_id.mul contDiff_const)
  exact ContDiff.const_smul (cutoffScale n) h

lemma cutoffPsi_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (cutoffPsi n) (Real.cos (t * (cutoffScale n)⁻¹)) t := by
  unfold cutoffPsi
  have h1 : HasDerivAt (fun y : ℝ => y * (cutoffScale n)⁻¹) ((cutoffScale n)⁻¹) t := by
    simpa using (hasDerivAt_id t).mul_const ((cutoffScale n)⁻¹)
  have h2 : HasDerivAt (fun y : ℝ => Real.sin (y * (cutoffScale n)⁻¹))
      (Real.cos (t * (cutoffScale n)⁻¹) * (cutoffScale n)⁻¹) t := by
    have hsin : HasDerivAt Real.sin (Real.cos (t * (cutoffScale n)⁻¹))
        (t * (cutoffScale n)⁻¹) :=
      Real.hasDerivAt_sin _
    exact hsin.comp t h1
  have h3 := h2.const_mul (cutoffScale n)
  have h4 : cutoffScale n * (Real.cos (t * (cutoffScale n)⁻¹) * (cutoffScale n)⁻¹)
      = Real.cos (t * (cutoffScale n)⁻¹) := by
    calc cutoffScale n * (Real.cos (t * (cutoffScale n)⁻¹) * (cutoffScale n)⁻¹)
        = Real.cos (t * (cutoffScale n)⁻¹) * (cutoffScale n * (cutoffScale n)⁻¹) := by ring
      _ = Real.cos (t * (cutoffScale n)⁻¹) * 1 := by
            rw [mul_inv_cancel₀ (cutoffScale_ne_zero n)]
      _ = Real.cos (t * (cutoffScale n)⁻¹) := by ring
  rwa [h4] at h3

lemma cutoffPsi_deriv_le (n : ℕ) (t : ℝ) : |deriv (cutoffPsi n) t| ≤ 1 := by
  rw [(cutoffPsi_hasDerivAt n t).deriv]
  exact Real.abs_cos_le_one _

lemma cutoffPsi_zero (n : ℕ) : cutoffPsi n 0 = 0 := by
  simp [cutoffPsi]

lemma cutoffPsi_abs_le (n : ℕ) (t : ℝ) : |cutoffPsi n t| ≤ |t| := by
  have hc : 0 < cutoffScale n := cutoffScale_pos n
  rw [cutoffPsi, abs_mul, abs_of_pos hc]
  calc cutoffScale n * |Real.sin (t * (cutoffScale n)⁻¹)|
      ≤ cutoffScale n * |t * (cutoffScale n)⁻¹| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hc.le
    _ = cutoffScale n * (|t| * (cutoffScale n)⁻¹) := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    _ = |t| := by field_simp

lemma cutoffPsi_abs_le_succ (n : ℕ) (t : ℝ) : |cutoffPsi n t| ≤ (n : ℝ) + 1 := by
  rw [cutoffPsi, abs_mul, abs_of_pos (cutoffScale_pos n), cutoffScale]
  calc ((n : ℝ) + 1) * |Real.sin (t * ((n : ℝ) + 1)⁻¹)| ≤ ((n : ℝ) + 1) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = (n : ℝ) + 1 := by ring

lemma cutoffPsi_lipschitz (n : ℕ) : LipschitzWith 1 (cutoffPsi n) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (cutoffPsi_hasDerivAt n x).differentiableAt) (fun x => ?_)
  have h := cutoffPsi_deriv_le n x
  rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
  simpa using h

/-- The algebraic identity underlying the pointwise convergence:
`t * slope sin 0 (t / c) = c * sin (t / c)`. -/
lemma cutoffPsi_mul_slope (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    t * slope Real.sin 0 (t * (cutoffScale n)⁻¹) = cutoffPsi n t := by
  rw [cutoffPsi, slope_def_field, Real.sin_zero, sub_zero]
  simp only [sub_zero]
  field_simp [ht]

lemma cutoffPsi_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => cutoffPsi n t) atTop (nhds t) := by
  by_cases ht : t = 0
  · subst ht
    simp [cutoffPsi]
  · -- `slope sin 0 → 1` at `0`, and `t * (n + 1)⁻¹ → 0` while staying nonzero.
    have hslope : Tendsto (slope Real.sin 0) (𝓝[≠] (0 : ℝ)) (nhds 1) := by
      simpa using (Real.hasDerivAt_sin 0).tendsto_slope
    have hcast : Tendsto (cutoffScale) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      have h' : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
        simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
      exact h'
    have hinv : Tendsto (fun n : ℕ => (cutoffScale n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hdiv : Tendsto (fun n : ℕ => t * (cutoffScale n)⁻¹) atTop (nhds 0) := by
      simpa using hinv.const_mul t
    have hw : Tendsto (fun n : ℕ => t * (cutoffScale n)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hdiv, by
        filter_upwards with n
        exact mul_ne_zero ht (inv_ne_zero (cutoffScale_ne_zero n))⟩
    have hcomp : Tendsto (fun n : ℕ => slope Real.sin 0 (t * (cutoffScale n)⁻¹))
        atTop (nhds 1) :=
      hslope.comp hw
    have hmul : Tendsto (fun n : ℕ => t * slope Real.sin 0 (t * (cutoffScale n)⁻¹))
        atTop (nhds t) := by
      simpa using hcomp.const_mul t
    refine Filter.Tendsto.congr' ?_ hmul
    filter_upwards with n
    exact cutoffPsi_mul_slope n t ht

theorem smooth_cutoff_family_bounded :
    ∃ ψ : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ⊤ (ψ n)) ∧
      (∀ n t, |deriv (ψ n) t| ≤ 1) ∧
      (∀ n, ψ n 0 = 0) ∧
      (∀ n t, |ψ n t| ≤ |t|) ∧
      (∀ n, LipschitzWith 1 (ψ n)) ∧
      (∀ n t, |ψ n t| ≤ (n : ℝ) + 1) ∧
      (∀ t, Filter.Tendsto (fun n => ψ n t) Filter.atTop (nhds t)) := by
  exact ⟨cutoffPsi, fun n => cutoffPsi_contDiff n, fun n t => cutoffPsi_deriv_le n t,
    fun n => cutoffPsi_zero n, fun n t => cutoffPsi_abs_le n t, fun n => cutoffPsi_lipschitz n,
    fun n t => cutoffPsi_abs_le_succ n t, fun t => cutoffPsi_tendsto t⟩

end Work.BoseSym.Trunc
