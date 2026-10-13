import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.Coercivity

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

theorem hasSum_setIntegral_tsum {I : Set ℝ} {a : ℕ → ℝ → ℝ} {C s : ℝ} (hC : 0 < C) (hs : 0 < s)
    (hIm : MeasurableSet I) (hI : volume I ≠ ⊤)
    (hcont : ∀ k, ContinuousOn (a k) I)
    (hbd : ∀ k θ, θ ∈ I → |a k θ| ≤ C / s ^ k)
    {u : ℝ} (hu : |u| < s) :
    HasSum (fun k => (∫ θ in I, a k θ) * u ^ k) (∫ θ in I, ∑' k, a k θ * u ^ k) := by
  set r : ℝ := |u| / s with hrdef
  have hr_nonneg : 0 ≤ r := by rw [hrdef]; positivity
  have hr_lt_one : r < 1 := by rw [hrdef, div_lt_one hs]; exact hu
  have hsum_r : Summable (fun n => r ^ n) :=
    summable_geometric_of_abs_lt_one (by rw [abs_of_nonneg hr_nonneg]; exact hr_lt_one)
  let bound : ℕ → ℝ → ℝ := fun n _ => C * r ^ n
  have hbound_summable : ∀ θ, Summable (fun n => bound n θ) := fun θ => hsum_r.mul_left C
  have hfin : IsFiniteMeasure (volume.restrict I) := by
    rw [isFiniteMeasure_iff, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_top_iff_ne_top.mpr hI
  have hbound_integrable : Integrable (fun θ => ∑' n, bound n θ) (volume.restrict I) := by
    have hthis : (fun θ => ∑' n, bound n θ) = fun _ => ∑' n, C * r ^ n := by
      funext θ; rfl
    rw [hthis]
    exact integrable_const _
  have hmeas : ∀ n, AEStronglyMeasurable (fun θ => a n θ * u ^ n) (volume.restrict I) :=
    fun n => ((hcont n).aestronglyMeasurable hIm).mul_const (u ^ n)
  have hbd' : ∀ n, ∀ᵐ θ ∂(volume.restrict I), ‖(fun θ => a n θ * u ^ n) θ‖ ≤ bound n θ := by
    intro n
    filter_upwards [ae_restrict_mem hIm] with θ hθ
    simp only [bound]
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |a n θ| * |u| ^ n ≤ (C / s ^ n) * |u| ^ n :=
          mul_le_mul_of_nonneg_right (hbd n θ hθ) (by positivity)
      _ = C * r ^ n := by rw [hrdef, div_pow]; ring
  have hsummable_ae : ∀ᵐ θ ∂(volume.restrict I), Summable (fun n => bound n θ) :=
    Filter.Eventually.of_forall hbound_summable
  have hlim : ∀ᵐ θ ∂(volume.restrict I),
      HasSum (fun n => a n θ * u ^ n) (∑' n, a n θ * u ^ n) := by
    filter_upwards [ae_restrict_mem hIm] with θ hθ
    apply Summable.hasSum
    apply Summable.of_norm_bounded (g := fun n => C * r ^ n) (hsum_r.mul_left C)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |a n θ| * |u| ^ n ≤ (C / s ^ n) * |u| ^ n :=
          mul_le_mul_of_nonneg_right (hbd n θ hθ) (by positivity)
      _ = C * r ^ n := by rw [hrdef, div_pow]; ring
  have h := hasSum_integral_of_dominated_convergence (F := fun n θ => a n θ * u ^ n)
      (f := fun θ => ∑' n, a n θ * u ^ n) bound hmeas hbd' hsummable_ae hbound_integrable hlim
  simpa only [integral_mul_const] using h

end Work.Coercivity
