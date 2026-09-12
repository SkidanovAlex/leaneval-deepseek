import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.LMAux
import Submission.F_tower
import Submission.F_chernoff

/-!
Real-valued MGF and frozen-row probability bound (child task).

Proves `Xn_mgf_real_le` (real-valued MGF bound for the frozen-coordinate
walk) and `row_frozen_prob_le` (probability that a row is frozen after T
steps is at most the Gaussian tail bound).
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- Measurability of the MGF integrand of the walk increment. -/
lemma meas_Xn_mgf {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (t : ℝ) :
    Measurable (fun ω : Omega n T => Real.exp (t * vin (Xn n T δ γ x0 v c ω T - x0) w)) := by
  have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω T) :=
    measurable_Xn (n := n) (ι := ι) (T := T) (t := T) (le_refl T) δ γ x0 v c
  have hsub : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω T - x0) := hX.sub measurable_const
  have hvin : Measurable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω T - x0) w) :=
    (measurable_vin n w).comp hsub
  have hprod : Measurable (fun ω : Omega n T => t * vin (Xn n T δ γ x0 v c ω T - x0) w) :=
    hvin.const_mul t
  exact Real.continuous_exp.measurable.comp hprod

/-- The MGF integrand of the walk increment is integrable (for every real `t`). -/
lemma Xn_mgf_integrable {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (t : ℝ) :
    Integrable (fun ω : Omega n T => Real.exp (t * vin (Xn n T δ γ x0 v c ω T - x0) w)) (mu n T) := by
  have hmeas : AEStronglyMeasurable (fun ω : Omega n T =>
      Real.exp (t * vin (Xn n T δ γ x0 v c ω T - x0) w)) (mu n T) :=
    (meas_Xn_mgf n T δ γ x0 v c w t).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[mu n T] (fun ω : Omega n T =>
      Real.exp (t * vin (Xn n T δ γ x0 v c ω T - x0) w)) :=
    ae_of_all (mu n T) (fun ω => (Real.exp_pos _).le)
  rw [← (lintegral_ofReal_ne_top_iff_integrable (f := fun ω : Omega n T =>
      Real.exp (t * vin (Xn n T δ γ x0 v c ω T - x0) w)) hmeas hnn)]
  have hlin := tower_lin (n := n) (T := T) (δ := δ) (γ := γ) (x0 := x0) (v := v) (c := c)
    (w := w) (lam := t)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin

/-- Real MGF bound for the frozen-coordinate walk. -/
lemma Xn_mgf_real_le {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ) :
    (∫ ω : Omega n T, Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w) ∂(mu n T)) ≤
      Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * (T : ℝ) / 2) := by
  have hmeas : AEStronglyMeasurable (fun ω : Omega n T =>
      Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w)) (mu n T) :=
    (meas_Xn_mgf n T δ γ x0 v c w lam).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[mu n T] (fun ω : Omega n T =>
      Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w)) :=
    ae_of_all (mu n T) (fun ω => (Real.exp_pos _).le)
  have hEq : (∫ ω : Omega n T, Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w) ∂(mu n T))
      = ENNReal.toReal (∫⁻ ω : Omega n T, ENNReal.ofReal
          (Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w)) ∂(mu n T)) :=
    integral_eq_lintegral_of_nonneg_ae hnn hmeas
  have hlin := tower_lin (n := n) (T := T) (δ := δ) (γ := γ) (x0 := x0) (v := v) (c := c)
    (w := w) (lam := lam)
  calc
    (∫ ω : Omega n T, Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w) ∂(mu n T))
        = ENNReal.toReal (∫⁻ ω : Omega n T, ENNReal.ofReal
            (Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w)) ∂(mu n T)) := hEq
    _ ≤ Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * (T : ℝ) / 2) := by
        refine ENNReal.toReal_le_of_le_ofReal ?_ hlin
        exact (Real.exp_pos _).le

/-- Probability that row j is frozen after T steps. -/
lemma row_frozen_prob_le {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hT1 : 1 ≤ T) {j : ι} (hvj : ‖v j‖ ≠ 0) (hcj : δ ≤ c j) :
    (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} ≤
      2 * Real.exp (-(c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ))) := by
  let Z : Omega n T → ℝ := fun ω => vin (Xn n T δ γ x0 v c ω T - x0) (v j)
  let a : ℝ := (c j - δ) * ‖v j‖
  let σsq : ℝ := γ ^ 2 * ‖v j‖ ^ 2 * (T : ℝ)
  have hZmeas : Measurable Z := by
    have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω T) :=
      measurable_Xn (n := n) (ι := ι) (T := T) (t := T) (le_refl T) δ γ x0 v c
    have hsub : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω T - x0) := hX.sub measurable_const
    have hvin : Measurable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω T - x0) (v j)) :=
      (measurable_vin n (v j)).comp hsub
    simpa [Z] using hvin
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (sub_nonneg.mpr hcj) (norm_nonneg _)
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hT1)
  have hσsq : 0 < σsq := by
    dsimp [σsq]
    exact mul_pos (mul_pos (sq_pos_of_ne_zero hγ.ne') (sq_pos_of_ne_zero hvj)) hTpos
  have hint : ∀ t : ℝ, Integrable (fun ω : Omega n T => Real.exp (t * Z ω)) (mu n T) := by
    intro t
    simpa [Z] using Xn_mgf_integrable (n := n) (T := T) (δ := δ) (γ := γ) (x0 := x0) (v := v)
      (c := c) (w := v j) t
  have hmgf : ∀ t : ℝ, (∫ ω : Omega n T, Real.exp (t * Z ω) ∂(mu n T)) ≤
      Real.exp (t ^ 2 * σsq / 2) := by
    intro t
    have hb := Xn_mgf_real_le (n := n) (T := T) (δ := δ) (γ := γ) (x0 := x0) (v := v)
      (c := c) (w := v j) (lam := t)
    calc
      (∫ ω : Omega n T, Real.exp (t * Z ω) ∂(mu n T))
          ≤ Real.exp (t ^ 2 * γ ^ 2 * ‖v j‖ ^ 2 * (T : ℝ) / 2) := by
              simpa [Z] using hb
      _ = Real.exp (t ^ 2 * σsq / 2) := by
              congr 1
              dsimp [σsq]
              ring
  have hmain : (mu n T).real {ω : Omega n T | a ≤ |Z ω|} ≤
      2 * Real.exp (-(a ^ 2) / (2 * σsq)) :=
    prob_abs_ge_le_of_mgf (μ := mu n T) (Z := Z) hZmeas σsq hσsq hint hmgf a ha0
  have hset : {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} =
      {ω : Omega n T | a ≤ |Z ω|} := by
    ext ω
    simp [Z, a, frozenRows]
  calc
    (mu n T).real {ω : Omega n T | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)}
        ≤ 2 * Real.exp (-(a ^ 2) / (2 * σsq)) := by
            rw [hset]
            exact hmain
    _ = 2 * Real.exp (-(c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ))) := by
            congr 2
            rw [show -(a ^ 2) / (2 * σsq) = -(c j - δ) ^ 2 / (2 * γ ^ 2 * (T : ℝ)) by
              dsimp [a, σsq]
              field_simp [hγ.ne', hvj, hTpos.ne']]

end Discrepancy

end Submission
