import Mathlib
import Submission.Commons.Analysis.Trace.trace_adjoint_comp_le_norm_mul
import Submission.Commons.Analysis.Trace.sqrt_trace_adjoint_comp_le_trace_of_nonneg
import Submission.Commons.Analysis.Trace.trace_sub_sqrt_mono

namespace Commons.Analysis.Trace

open scoped InnerProductSpace

/-! ## Elementary scalar lemmas -/

/-- If `S ≥ 0`, `T ≥ 0` and `(b + S)^2 ≤ S * T`, then `b ≤ √S * √T - S`. -/
theorem le_sqrt_mul_sqrt_sub {b S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (h : (b + S) ^ 2 ≤ S * T) : b ≤ Real.sqrt S * Real.sqrt T - S := by
  have hST : 0 ≤ S * T := mul_nonneg hS hT
  rcases le_or_gt 0 (b + S) with hbs | hbs
  · have h1 : b + S ≤ Real.sqrt (S * T) := (Real.le_sqrt hbs hST).mpr h
    rw [Real.sqrt_mul hS T] at h1
    linarith
  · have h1 : 0 ≤ Real.sqrt S * Real.sqrt T :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith

/-- Scalar core of the tangent inequality for `x ↦ x - √(2 + x²)`. -/
theorem sqrt_add_div_le_sqrt {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hT : 0 ≤ 2 + (a + 2 * b + c)) (hb : b ^ 2 ≤ a * c) :
    Real.sqrt (2 + a) + b / Real.sqrt (2 + a) ≤ Real.sqrt (2 + (a + 2 * b + c)) := by
  have hSpos : 0 < 2 + a := by linarith
  have hSc : b ^ 2 ≤ (2 + a) * c := by
    have h1 : a * c ≤ (2 + a) * c := mul_le_mul_of_nonneg_right (by linarith) hc
    linarith
  have hST : (b + (2 + a)) ^ 2 ≤ (2 + a) * (2 + (a + 2 * b + c)) := by
    nlinarith [hSc]
  have key : b ≤ Real.sqrt (2 + a) * Real.sqrt (2 + (a + 2 * b + c)) - (2 + a) :=
    le_sqrt_mul_sqrt_sub hSpos.le hT hST
  have hsSpos : 0 < Real.sqrt (2 + a) := Real.sqrt_pos_of_pos hSpos
  have key' : b / Real.sqrt (2 + a) ≤ Real.sqrt (2 + (a + 2 * b + c)) - Real.sqrt (2 + a) := by
    rw [div_le_iff₀ hsSpos]
    nlinarith [key, Real.sq_sqrt hSpos.le]
  linarith [key']

/-! ## Main tangent inequality -/

theorem trace_sub_sqrt_tangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N D : E →L[ℝ] E} (hN : N.IsSymmetric) (hD : D.IsSymmetric) : (LinearMap.trace ℝ E (N + D).toLinearMap - Real.sqrt (2 + LinearMap.trace ℝ E ((N + D).toLinearMap ∘ₗ (N + D).toLinearMap))) - (LinearMap.trace ℝ E N.toLinearMap - Real.sqrt (2 + LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))) ≤ LinearMap.trace ℝ E D.toLinearMap - LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap) / Real.sqrt (2 + LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)) := by
  classical
  have hNDsym : (N + D).IsSymmetric := by
    rw [ContinuousLinearMap.toLinearMap_add]
    exact LinearMap.IsSymmetric.add hN hD
  -- nonnegativity of the quadratic traces
  have ha_nn : 0 ≤ LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap) :=
    trace_comp_sq_nonneg hN
  have hc_nn : 0 ≤ LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap) :=
    trace_comp_sq_nonneg hD
  -- trace of the sum
  have hsum : LinearMap.trace ℝ E (N + D).toLinearMap
      = LinearMap.trace ℝ E N.toLinearMap + LinearMap.trace ℝ E D.toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_add, map_add]
  -- expansion of the quadratic trace
  have hsq : LinearMap.trace ℝ E ((N + D).toLinearMap ∘ₗ (N + D).toLinearMap)
      = LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)
        + 2 * LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)
        + LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap) :=
    trace_comp_sq_add N D
  -- T ≥ 0
  have hT_nn : 0 ≤ 2 + (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)
        + 2 * LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)
        + LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap)) := by
    have hq := trace_comp_sq_nonneg hNDsym
    rw [hsq] at hq
    linarith
  -- Cauchy–Schwarz one sided
  have hb_le : LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap) ≤
      Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
        * Real.sqrt (LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap)) :=
    trace_comp_le_sqrt_mul_sqrt hN hD
  have hmb_le : -(LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)) ≤
      Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
        * Real.sqrt (LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap)) := by
    have hsym : (-N).IsSymmetric := by
      have := LinearMap.IsSymmetric.smul (c := (-1 : ℝ)) (by simp) hN
      simpa using this
    have h := trace_comp_le_sqrt_mul_sqrt (A := -N) (B := D) hsym hD
    have h1 : LinearMap.trace ℝ E ((-N).toLinearMap ∘ₗ D.toLinearMap)
        = -(LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)) := by
      rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.neg_comp, map_neg]
    have h2 : LinearMap.trace ℝ E ((-N).toLinearMap ∘ₗ (-N).toLinearMap)
        = LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap) := by
      rw [ContinuousLinearMap.toLinearMap_neg, LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
    rw [h1, h2] at h
    exact h
  -- b² ≤ a c
  have hb_sq : (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)) ^ 2 ≤
      LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)
        * LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap) := by
    set p := Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
        * Real.sqrt (LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap)) with hp
    have hp_nn : 0 ≤ p := by rw [hp]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have habs : |LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)| ≤ p := by
      rw [hp]
      exact abs_le.mpr ⟨by linarith [hmb_le], hb_le⟩
    have hp2 : p ^ 2 = LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)
        * LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap) := by
      rw [hp, mul_pow, Real.sq_sqrt ha_nn, Real.sq_sqrt hc_nn]
    have h2 : (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap)) ^ 2 ≤ p ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hp_nn]
      exact habs
    rwa [hp2] at h2
  -- scalar reduction
  have hkey := sqrt_add_div_le_sqrt
    (a := LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
    (b := LinearMap.trace ℝ E (N.toLinearMap ∘ₗ D.toLinearMap))
    (c := LinearMap.trace ℝ E (D.toLinearMap ∘ₗ D.toLinearMap)) ha_nn hc_nn hT_nn hb_sq
  rw [hsum, hsq]
  linarith [hkey]

end Commons.Analysis.Trace
