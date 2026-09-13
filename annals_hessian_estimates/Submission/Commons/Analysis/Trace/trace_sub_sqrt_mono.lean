import Mathlib
import Submission.Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq
import Submission.Commons.Analysis.Trace.sqrt_trace_adjoint_comp_le_trace_of_nonneg
import Submission.Commons.Analysis.Trace.trace_adjoint_comp_le_norm_mul

namespace Commons.Analysis.Trace

open scoped InnerProductSpace

/-! ## Scalar lemma -/

theorem sqrt_two_add_sq_sub_le {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t)
    (hxy : x - y ≤ t) : Real.sqrt (2 + x ^ 2) - Real.sqrt (2 + y ^ 2) ≤ t := by
  rcases le_or_gt y x with hyx | hyx
  · have hx2 : (0:ℝ) < 2 + x ^ 2 := by positivity
    have hy2 : (0:ℝ) < 2 + y ^ 2 := by positivity
    have hx_le : x ≤ Real.sqrt (2 + x ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
    have hy_le : y ≤ Real.sqrt (2 + y ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
    have hAB : Real.sqrt (2 + x ^ 2) - Real.sqrt (2 + y ^ 2)
        = (x ^ 2 - y ^ 2) / (Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2)) := by
      rw [eq_div_iff (by positivity)]
      have h1 : Real.sqrt (2 + x ^ 2) * Real.sqrt (2 + x ^ 2) = 2 + x ^ 2 := by
        rw [← pow_two]; exact Real.sq_sqrt hx2.le
      have h2 : Real.sqrt (2 + y ^ 2) * Real.sqrt (2 + y ^ 2) = 2 + y ^ 2 := by
        rw [← pow_two]; exact Real.sq_sqrt hy2.le
      nlinarith [h1, h2]
    have hsum_pos : (0:ℝ) < Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2) := by positivity
    have hle_sum : x + y ≤ Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2) := by linarith
    have hxy_nonneg : 0 ≤ x - y := by linarith
    calc
      Real.sqrt (2 + x ^ 2) - Real.sqrt (2 + y ^ 2)
          = (x ^ 2 - y ^ 2) / (Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2)) := hAB
      _ = ((x - y) * (x + y)) / (Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2)) := by ring_nf
      _ ≤ ((x - y) * (Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2)))
            / (Real.sqrt (2 + x ^ 2) + Real.sqrt (2 + y ^ 2)) := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle_sum hxy_nonneg)
            hsum_pos.le
      _ = x - y := by rw [mul_div_cancel_right₀ _ hsum_pos.ne']
      _ ≤ t := hxy
  · have hle : Real.sqrt (2 + x ^ 2) ≤ Real.sqrt (2 + y ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hyx, hx, hy]
    linarith

/-! ## Trace helpers -/

theorem trace_comp_sq_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hA : A.IsSymmetric) :
    0 ≤ LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap) := by
  rw [Commons.Analysis.Sigma2.trace_sq_eq_sum_eigenvalues_sq hA]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem trace_comp_sq_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A B : E →L[ℝ] E) :
    LinearMap.trace ℝ E ((A + B).toLinearMap ∘ₗ (A + B).toLinearMap)
      = LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap)
        + 2 * LinearMap.trace ℝ E (A.toLinearMap ∘ₗ B.toLinearMap)
        + LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap) := by
  rw [show ((A + B).toLinearMap ∘ₗ (A + B).toLinearMap)
      = A.toLinearMap ∘ₗ A.toLinearMap + A.toLinearMap ∘ₗ B.toLinearMap
        + B.toLinearMap ∘ₗ A.toLinearMap + B.toLinearMap ∘ₗ B.toLinearMap from by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, ContinuousLinearMap.toLinearMap_add,
      map_add]
    abel]
  simp only [map_add, LinearMap.trace_comp_comm' (A.toLinearMap) (B.toLinearMap)]
  ring

theorem trace_comp_le_sqrt_mul_sqrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    LinearMap.trace ℝ E (A.toLinearMap ∘ₗ B.toLinearMap)
      ≤ Real.sqrt (LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap))
        * Real.sqrt (LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap)) := by
  have h := Commons.Analysis.Trace.trace_adjoint_comp_le_norm_mul (T := A) (S := B)
  rw [LinearMap.IsSymmetric.adjoint_eq hA, LinearMap.IsSymmetric.adjoint_eq hB] at h
  exact h

theorem sqrt_trace_sq_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    Real.sqrt (LinearMap.trace ℝ E ((A + B).toLinearMap ∘ₗ (A + B).toLinearMap))
      ≤ Real.sqrt (LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap))
        + Real.sqrt (LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap)) := by
  have hAA := trace_comp_sq_nonneg hA
  have hBB := trace_comp_sq_nonneg hB
  have hcs := trace_comp_le_sqrt_mul_sqrt hA hB
  have hmain : LinearMap.trace ℝ E ((A + B).toLinearMap ∘ₗ (A + B).toLinearMap)
      ≤ (Real.sqrt (LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap))
          + Real.sqrt (LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap))) ^ 2 := by
    rw [trace_comp_sq_add]
    nlinarith [hcs, Real.sq_sqrt hAA, Real.sq_sqrt hBB]
  calc
    Real.sqrt (LinearMap.trace ℝ E ((A + B).toLinearMap ∘ₗ (A + B).toLinearMap))
        ≤ Real.sqrt ((Real.sqrt (LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap))
            + Real.sqrt (LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap))) ^ 2) :=
          Real.sqrt_le_sqrt hmain
    _ = Real.sqrt (LinearMap.trace ℝ E (A.toLinearMap ∘ₗ A.toLinearMap))
        + Real.sqrt (LinearMap.trace ℝ E (B.toLinearMap ∘ₗ B.toLinearMap)) :=
          Real.sqrt_sq (by positivity)


open scoped InnerProductSpace in
theorem trace_sub_sqrt_mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {M N : E →L[ℝ] E} (hM : M.IsSymmetric) (hN : N.IsSymmetric)
    (h : ∀ v : E, ⟪M v, v⟫_ℝ ≤ ⟪N v, v⟫_ℝ) :
    LinearMap.trace ℝ E (M.toLinearMap)
        - Real.sqrt (2 + LinearMap.trace ℝ E (M.toLinearMap.adjoint ∘ₗ M))
      ≤ LinearMap.trace ℝ E (N.toLinearMap)
        - Real.sqrt (2 + LinearMap.trace ℝ E (N.toLinearMap.adjoint ∘ₗ N)) := by
  have hD_sym : (N - M).IsSymmetric := hN.sub hM
  have hD_pos : ∀ v : E, 0 ≤ ⟪(N - M) v, v⟫_ℝ := by
    intro v
    have hv := h v
    rw [sub_apply, inner_sub_left]
    linarith
  have hMtr := Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq hM
  have hNtr := Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq hN
  have hDtr' := Commons.Analysis.Sigma2.trace_adjoint_sq_eq_trace_sq hD_sym
  have htN : 0 ≤ LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap) := trace_comp_sq_nonneg hN
  have htM : 0 ≤ LinearMap.trace ℝ E (M.toLinearMap ∘ₗ M.toLinearMap) := trace_comp_sq_nonneg hM
  have hMD : M + (N - M) = N := by abel
  have htri : Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
      ≤ Real.sqrt (LinearMap.trace ℝ E (M.toLinearMap ∘ₗ M.toLinearMap))
        + Real.sqrt (LinearMap.trace ℝ E ((N - M).toLinearMap ∘ₗ (N - M).toLinearMap)) := by
    have hh := sqrt_trace_sq_add_le hM hD_sym
    rwa [hMD] at hh
  have hw : Real.sqrt (LinearMap.trace ℝ E ((N - M).toLinearMap ∘ₗ (N - M).toLinearMap))
      ≤ LinearMap.trace ℝ E (N - M).toLinearMap := by
    have h1 := Commons.Analysis.Trace.sqrt_trace_adjoint_comp_le_trace_of_nonneg hD_sym hD_pos
    rwa [hDtr'] at h1
  have hDnonneg : 0 ≤ LinearMap.trace ℝ E (N - M).toLinearMap :=
    le_trans (Real.sqrt_nonneg _) hw
  have hDtr : LinearMap.trace ℝ E (N - M).toLinearMap
      = LinearMap.trace ℝ E N.toLinearMap - LinearMap.trace ℝ E M.toLinearMap := by
    rw [show (N - M).toLinearMap = N.toLinearMap - M.toLinearMap from by ext x; simp]
    rw [map_sub]
  have hxy : Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap))
      - Real.sqrt (LinearMap.trace ℝ E (M.toLinearMap ∘ₗ M.toLinearMap))
      ≤ LinearMap.trace ℝ E (N - M).toLinearMap := by linarith [htri, hw]
  have hkey := sqrt_two_add_sq_sub_le
      (x := Real.sqrt (LinearMap.trace ℝ E (N.toLinearMap ∘ₗ N.toLinearMap)))
      (y := Real.sqrt (LinearMap.trace ℝ E (M.toLinearMap ∘ₗ M.toLinearMap)))
      (t := LinearMap.trace ℝ E (N - M).toLinearMap)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hDnonneg hxy
  rw [Real.sq_sqrt htN, Real.sq_sqrt htM] at hkey
  rw [hMtr, hNtr]
  linarith [hkey, hDtr]

end Commons.Analysis.Trace
