import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE5.Flat.strictFDeriv_eaEval
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE2.VcbTopology
import Submission.Work.WilE2.sard_square
import Submission.Work.WilE2.avoid_null

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Topology Filter

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-! ## The positive set of one EA function on the cube, and its basic geometry.

Support module for `Work.WilE2.posComps_finite`. -/

/-- The positive set of `eaEval c Q` inside the cube `[-1,1]^k`. -/
def posSet {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) : Set (Fin k → ℝ) :=
  cubeC k ∩ {x | 0 < eaEval c Q x}

@[simp] theorem mem_posSet {k r : ℕ} {c : EAChain k r} {Q : EAPoly k r} {x : Fin k → ℝ} :
    x ∈ posSet c Q ↔ x ∈ cubeC k ∧ 0 < eaEval c Q x := Iff.rfl

theorem isOpen_eaEval_pos {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    IsOpen {x : Fin k → ℝ | 0 < eaEval c Q x} :=
  isOpen_lt continuous_const (Work.WilE5.Flat.continuous_eaEval c Q)

/-- The frontier of the cube is the union of its faces. -/
theorem frontier_cubeC_eq (K : ℕ) :
    frontier (cubeC K) = {x : Fin K → ℝ | x ∈ cubeC K ∧ ∃ i, |x i| = 1} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    refine ⟨(isClosed_cubeC K).closure_subset (frontier_subset_closure hx), ?_⟩
    obtain ⟨j, hj | hj⟩ := frontier_cubeC_subset hx
    · exact ⟨j, by rw [hj]; norm_num⟩
    · exact ⟨j, by rw [hj]; norm_num⟩
  · rintro x ⟨hxC, j, hj⟩
    refine ⟨?_, ?_⟩
    · rw [(isClosed_cubeC K).closure_eq]; exact hxC
    · intro hmem
      rw [interior_cubeC] at hmem
      have hlt := hmem j
      rw [hj] at hlt
      norm_num at hlt

/-- A point of the cube is either interior or lies on a face. -/
theorem cubeC_mem_interior_or_face {K : ℕ} {x : Fin K → ℝ} (hx : x ∈ cubeC K) :
    x ∈ interior (cubeC K) ∨ ∃ i, |x i| = 1 := by
  by_cases h : x ∈ interior (cubeC K)
  · exact Or.inl h
  · refine Or.inr ?_
    have hx' := (mem_frontier_iff_notMem_interior hx).mpr h
    exact (frontier_cubeC_eq K ▸ hx').2

/-- An island (a component of the positive set avoiding the frontier of the cube) is contained in
the interior of the cube. -/
theorem island_subset_interior {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x₀ : Fin k → ℝ} (hfr : Disjoint (connectedComponentIn (posSet c Q) x₀) (frontier (cubeC k))) :
    connectedComponentIn (posSet c Q) x₀ ⊆ interior (cubeC k) := by
  intro y hy
  have hyc : y ∈ cubeC k := (connectedComponentIn_subset _ _ hy).1
  rcases cubeC_mem_interior_or_face hyc with h | ⟨i, hi⟩
  · exact h
  · exfalso
    refine Set.disjoint_left.mp hfr hy ?_
    rw [frontier_cubeC_eq]
    exact ⟨hyc, i, hi⟩

/-! ## The linear perturbation -/

/-- The linear functional `x ↦ ∑ i, u i * x i`, as a continuous linear map. -/
def linCLM {k : ℕ} (u : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, u i • ContinuousLinearMap.proj i

theorem linCLM_apply {k : ℕ} (u : Fin k → ℝ) (x : Fin k → ℝ) :
    linCLM u x = ∑ i, u i * x i := by
  simp only [linCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem linCLM_abs_le {k : ℕ} (u : Fin k → ℝ) {x : Fin k → ℝ} (hx : x ∈ cubeC k) :
    |linCLM u x| ≤ ∑ i, |u i| := by
  rw [linCLM_apply]
  calc |∑ i, u i * x i| ≤ ∑ i, |u i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |x i| := by simp only [abs_mul]
    _ ≤ ∑ i, |u i| * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by simpa using hx i) (abs_nonneg _)
    _ = ∑ i, |u i| := by simp

theorem linCLM_le_sum_abs {k : ℕ} (u : Fin k → ℝ) {x : Fin k → ℝ} (hx : x ∈ cubeC k) :
    linCLM u x ≤ ∑ i, |u i| := (le_abs_self _).trans (linCLM_abs_le u hx)

/-! ## The derivative of the gradient map, and Sard genericity -/

/-- The Fréchet derivative of `eaEval c Q` evaluated at `v`, in coordinates. -/
theorem eaEvalD_apply {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x v : Fin k → ℝ) :
    Work.WilE5.Calc.eaEvalD c Q x v = ∑ i, eaEval c (eaD c i Q) x * v i := by
  simp only [Work.WilE5.Calc.eaEvalD, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The derivative of the gradient map, applied to a vector, is the matrix-vector product
with the Hessian matrix. -/
theorem pi_eaEvalD_apply_eq {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x v : Fin k → ℝ) :
    (ContinuousLinearMap.pi fun i => Work.WilE5.Calc.eaEvalD c (eaD c i Q) x) v
      = Matrix.mulVec (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) x) v := by
  funext i
  show Work.WilE5.Calc.eaEvalD c (eaD c i Q) x v
      = Matrix.mulVec (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) x) v i
  rw [eaEvalD_apply, Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.of_apply]

/-- The derivative of the gradient map, as a linear map, is the matrix-vector map of the
Hessian matrix. -/
theorem pi_eaEvalD_eq_toLin {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    ((ContinuousLinearMap.pi fun i => Work.WilE5.Calc.eaEvalD c (eaD c i Q) x) :
        (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = Matrix.toLin' (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) x) := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply]
  exact pi_eaEvalD_apply_eq c Q x v

/-- The determinant of a continuous linear map agrees with the determinant of any matrix
representing it. -/
theorem clm_det_eq_matrix_det {k : ℕ} (T : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ))
    (M : Matrix (Fin k) (Fin k) ℝ)
    (h : (T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) = Matrix.toLin' M) : T.det = M.det := by
  change LinearMap.det ((T : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ))) = M.det
  rw [h, LinearMap.det_toLin']

/-- **Sard for the gradient map.**  For every `ε > 0` there is `u` with all coordinate absolute
values `< ε` such that every solution of `∇Q = -u` is a *nondegenerate* critical point. -/
theorem posComps_good_perturbation {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ u : Fin k → ℝ, (∀ i, |u i| < ε) ∧ ∀ x : Fin k → ℝ,
      (∀ i, eaEval c (eaD c i Q) x = - u i) →
      (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) x).det ≠ 0 := by
  classical
  have hF' : ∀ x : Fin k → ℝ,
      HasFDerivAt (fun y : Fin k → ℝ => fun i => eaEval c (eaD c i Q) y)
        (ContinuousLinearMap.pi fun i => Work.WilE5.Calc.eaEvalD c (eaD c i Q) x) x :=
    fun x => hasFDerivAt_pi.mpr (fun i => Work.WilE5.Calc.hasFDerivAt_eaEval c (eaD c i Q) x)
  have hnull := Work.WilE2.sard_square
    (fun y : Fin k → ℝ => fun i => eaEval c (eaD c i Q) y)
    (fun y => ContinuousLinearMap.pi fun i => Work.WilE5.Calc.eaEvalD c (eaD c i Q) y) hF'
  obtain ⟨y, hy, hybad⟩ := Work.WilE2.avoid_null hnull 0 hε
  refine ⟨-y, ?_, ?_⟩
  · intro i
    have h1 : |y i| ≤ dist y 0 := by
      have h := dist_le_pi_dist y (0 : Fin k → ℝ) i
      simpa [Real.dist_eq] using h
    have h2 : |y i| < ε := lt_of_le_of_lt h1 hy
    simpa only [Pi.neg_apply, abs_neg] using h2
  · intro x hx
    have hFx : (fun y : Fin k → ℝ => fun i => eaEval c (eaD c i Q) y) x = y := by
      funext i
      have h := hx i
      simp only [Pi.neg_apply, neg_neg] at h
      exact h
    have hcrit : ¬ ((ContinuousLinearMap.pi fun i =>
        Work.WilE5.Calc.eaEvalD c (eaD c i Q) x).det = 0) := by
      intro h0
      exact hybad ⟨x, h0, hFx⟩
    have hdet := clm_det_eq_matrix_det
      (ContinuousLinearMap.pi fun i => Work.WilE5.Calc.eaEvalD c (eaD c i Q) x)
      (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) x)
      (pi_eaEvalD_eq_toLin c Q x)
    rw [hdet] at hcrit
    exact hcrit

end Work.WilE2
