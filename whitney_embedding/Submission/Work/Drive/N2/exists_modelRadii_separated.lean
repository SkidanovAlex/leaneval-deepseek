import Mathlib
import Submission.Work.Drive.N2.modelOrbitMono
import Submission.Work.Drive.N2.modelBall

namespace Work.Drive.N2

/-- Coordinate-wise square bound for the Euclidean space `ℝ²`. -/
private lemma sq_coord_le_norm_sq (v : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    (v k) ^ 2 ≤ ‖v‖ ^ 2 := by
  have h : |v k| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := 2) v k
  exact sq_le_sq' (by linarith [neg_abs_le (v k), h]) (by linarith [le_abs_self (v k), h])

theorem exists_modelRadii_separated {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {ι : Type*} [Fintype ι] (f : M → ℝ) (x : ι → M)
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ι → ℝ)
    (hsrc : ∀ i, x i ∈ (φ i).source) (hcen : ∀ i, φ i (x i) = 0)
    (hval : ∀ i y, y ∈ (φ i).source →
      f y = f (x i) + Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) y)
    {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j : ι, i ≠ j → 2 * η < |f (x i) - f (x j)|) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i) ∧
      (∀ i, x i ∈ Work.Drive.N2.modelBall (φ i) (r i)) ∧
      ∀ i j : ι, i ≠ j → ∀ y : M,
        y ∈ Work.Drive.N2.modelBall (φ i) (r i) →
        f y ∉ Set.Ioo (f (x j) - η) (f (x j) + η) := by
  -- The quadratic normal form is small wherever the chart norm is small.
  have key : ∀ (i : ι) (v : EuclideanSpace ℝ (Fin 2)),
      |s₁ i * (v 0) ^ 2 + s₂ i * (v 1) ^ 2| ≤ (|s₁ i| + |s₂ i|) * ‖v‖ ^ 2 := by
    intro i v
    calc |s₁ i * (v 0) ^ 2 + s₂ i * (v 1) ^ 2|
        ≤ |s₁ i * (v 0) ^ 2| + |s₂ i * (v 1) ^ 2| := abs_add_le _ _
      _ = |s₁ i| * (v 0) ^ 2 + |s₂ i| * (v 1) ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (v 0)),
              abs_of_nonneg (sq_nonneg (v 1))]
      _ ≤ |s₁ i| * ‖v‖ ^ 2 + |s₂ i| * ‖v‖ ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left (sq_coord_le_norm_sq v 0) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (sq_coord_le_norm_sq v 1) (abs_nonneg _))
      _ = (|s₁ i| + |s₂ i|) * ‖v‖ ^ 2 := by ring
  set rr : ι → ℝ := fun i => Real.sqrt (η / (|s₁ i| + |s₂ i| + 1)) with hrr
  have hrpos : ∀ i, 0 < rr i := by
    intro i
    simp only [hrr]
    exact Real.sqrt_pos.2 (div_pos hη (by positivity))
  have hrsq : ∀ i, (rr i) ^ 2 = η / (|s₁ i| + |s₂ i| + 1) := by
    intro i
    simp only [hrr]
    exact Real.sq_sqrt (le_of_lt (div_pos hη (by positivity)))
  have hrle : ∀ i, (|s₁ i| + |s₂ i|) * (rr i) ^ 2 < η := by
    intro i
    have hc : (0 : ℝ) < |s₁ i| + |s₂ i| + 1 := by positivity
    have h1 : (|s₁ i| + |s₂ i|) / (|s₁ i| + |s₂ i| + 1) < 1 := by
      rw [div_lt_one hc]; linarith
    calc (|s₁ i| + |s₂ i|) * (rr i) ^ 2
        = η * ((|s₁ i| + |s₂ i|) / (|s₁ i| + |s₂ i| + 1)) := by
          rw [hrsq i]; ring
      _ < η * 1 := mul_lt_mul_of_pos_left h1 hη
      _ = η := by ring
  refine ⟨rr, hrpos, ?_, ?_⟩
  · intro i
    refine ⟨hsrc i, ?_⟩
    rw [hcen i]
    simpa using hrpos i
  · intro i j hij y hy
    have hy1 : y ∈ (φ i).source := hy.1
    have hy2 : ‖φ i y‖ < rr i := hy.2
    have hQ : chartQ (φ i) (s₁ i) (s₂ i) y = f y - f (x i) := by
      rw [hval i y hy1]; ring
    have hclose : |f y - f (x i)| < η := by
      rw [← hQ]
      simp only [chartQ]
      refine lt_of_le_of_lt (key i (φ i y)) ?_
      have h3 : ‖φ i y‖ ^ 2 < (rr i) ^ 2 := by
        nlinarith [norm_nonneg (φ i y), hy2, le_of_lt (hrpos i)]
      calc (|s₁ i| + |s₂ i|) * ‖φ i y‖ ^ 2
          ≤ (|s₁ i| + |s₂ i|) * (rr i) ^ 2 :=
            mul_le_mul_of_nonneg_left (le_of_lt h3) (by positivity)
        _ < η := hrle i
    intro hmem
    rw [Set.mem_Ioo] at hmem
    have hmem' : |f y - f (x j)| < η := by
      rw [abs_lt]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have hclose' : |f (x i) - f y| < η := by
      rwa [abs_sub_comm] at hclose
    have htri : |f (x i) - f (x j)| ≤ |f (x i) - f y| + |f y - f (x j)| :=
      abs_sub_le _ _ _
    linarith [hdist i j hij, htri, hclose', hmem']

end Work.Drive.N2
