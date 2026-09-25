import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.calderon_zygmund_decomposition_1d

namespace Commons.Analysis.CalderonZygmund

open MeasureTheory Set
open scoped ENNReal Interval

theorem calderon_zygmund_decomposition_1d_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : MeasureTheory.Integrable f) (α : ℝ) (hα : 0 < α) :
    ∃ (A c : ℕ → ℝ) (g : ℝ → E) (b : ℕ → ℝ → E),
      (∀ j, A j ≤ c j) ∧
      (∀ j k, j ≠ k → Disjoint (Set.Ioo (A j) (c j)) (Set.Ioo (A k) (c k))) ∧
      (∀ j, α * (c j - A j) ≤ ∫ x in (A j)..(c j), ‖f x‖) ∧
      (∀ j, ∫ x in (A j)..(c j), ‖f x‖ ≤ 2 * α * (c j - A j)) ∧
      (∀ j, ∀ x, b j x = if x ∈ Set.Ioo (A j) (c j)
          then f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) else 0) ∧
      (∀ x, x ∉ ⋃ j, Set.Ioo (A j) (c j) → g x = f x) ∧
      (∀ j, ∀ x ∈ Set.Ioo (A j) (c j),
          g x = (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t)) ∧
      (∀ᵐ x ∂MeasureTheory.volume, x ∉ ⋃ j, Set.Ioo (A j) (c j) → ‖f x‖ ≤ α) ∧
      (∀ᵐ x ∂MeasureTheory.volume, ‖g x‖ ≤ 2 * α) ∧
      (MeasureTheory.volume (⋃ j, Set.Ioo (A j) (c j))
          ≤ ENNReal.ofReal (α⁻¹ * ∫ x, ‖f x‖)) ∧
      (∀ᵐ x ∂MeasureTheory.volume, f x = g x + ∑' j, b j x) := by
  classical
  have hfn : MeasureTheory.Integrable (fun x : ℝ => ‖f x‖) := hf.norm
  obtain ⟨A, c, g₀, b₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    calderon_zygmund_decomposition_1d (fun x : ℝ => ‖f x‖) hfn α hα
  have h3' : ∀ j, α * (c j - A j) ≤ ∫ x in (A j)..(c j), ‖f x‖ := by
    intro j; simpa using h3 j
  have h4' : ∀ j, ∫ x in (A j)..(c j), ‖f x‖ ≤ 2 * α * (c j - A j) := by
    intro j; simpa using h4 j
  let b : ℕ → ℝ → E := fun j x =>
    if x ∈ Set.Ioo (A j) (c j)
      then f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) else 0
  let g : ℝ → E := fun x => f x - ∑' j, b j x
  have hb_def : ∀ j, ∀ x, b j x = if x ∈ Set.Ioo (A j) (c j)
      then f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) else 0 := fun j x => rfl
  have h6' : ∀ x, x ∉ ⋃ j, Set.Ioo (A j) (c j) → g x = f x := by
    intro x hx
    have hbj : ∀ j, b j x = 0 := by
      intro j
      simp only [b]
      rw [if_neg]
      intro hmem
      exact hx (Set.mem_iUnion.mpr ⟨j, hmem⟩)
    have hz : (∑' j, b j x) = 0 := by rw [tsum_congr hbj, tsum_zero]
    simp only [g]
    rw [hz, sub_zero]
  have h7' : ∀ j, ∀ x ∈ Set.Ioo (A j) (c j),
      g x = (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) := by
    intro j x hx
    have hbj : b j x = f x - (c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t) := by
      simp only [b]; rw [if_pos hx]
    have hbj' : ∀ j', j' ≠ j → b j' x = 0 := by
      intro j' hj'
      have hdisj := h2 j j' (Ne.symm hj')
      have hmem : x ∉ Set.Ioo (A j') (c j') := fun hmem => (Set.disjoint_left.mp hdisj hx) hmem
      simp only [b]; rw [if_neg hmem]
    have htsum : (∑' j', b j' x) = b j x := tsum_eq_single j hbj'
    simp only [g]
    rw [htsum, hbj]
    abel
  have h8' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∉ ⋃ j, Set.Ioo (A j) (c j) → ‖f x‖ ≤ α := by
    filter_upwards [h8] with x hx
    intro hxU
    have h1' : |‖f x‖| ≤ α := hx hxU
    rwa [abs_of_nonneg (norm_nonneg _)] at h1'
  have h9' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ 2 * α := by
    filter_upwards [h8] with x hx
    by_cases hU : x ∈ ⋃ j, Set.Ioo (A j) (c j)
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
      rw [h7' j x hj]
      have hpos : 0 < c j - A j := sub_pos.mpr (lt_trans hj.1 hj.2)
      have hfin : ‖∫ t in (A j)..(c j), f t‖ ≤ ∫ t in (A j)..(c j), ‖f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (h1 j)
      calc ‖(c j - A j)⁻¹ • (∫ t in (A j)..(c j), f t)‖
          = |(c j - A j)⁻¹| * ‖∫ t in (A j)..(c j), f t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = (c j - A j)⁻¹ * ‖∫ t in (A j)..(c j), f t‖ := by rw [abs_inv, abs_of_pos hpos]
        _ ≤ (c j - A j)⁻¹ * (∫ t in (A j)..(c j), ‖f t‖) :=
            mul_le_mul_of_nonneg_left hfin (le_of_lt (inv_pos.mpr hpos))
        _ ≤ (c j - A j)⁻¹ * (2 * α * (c j - A j)) :=
            mul_le_mul_of_nonneg_left (h4' j) (le_of_lt (inv_pos.mpr hpos))
        _ = 2 * α := by
            rw [mul_comm (2 * α) (c j - A j), ← mul_assoc,
              inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    · rw [h6' x hU]
      have hfx : ‖f x‖ ≤ α := by
        have h1' : |‖f x‖| ≤ α := hx hU
        rwa [abs_of_nonneg (norm_nonneg _)] at h1'
      linarith
  have h10' : MeasureTheory.volume (⋃ j, Set.Ioo (A j) (c j))
      ≤ ENNReal.ofReal (α⁻¹ * ∫ x, ‖f x‖) := by
    simpa using h10
  have h11' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      f x = g x + ∑' j, b j x := by
    filter_upwards with x
    simp only [g]
    rw [sub_add_cancel]
  exact ⟨A, c, g, b, h1, h2, h3', h4', hb_def, h6', h7', h8', h9', h10', h11'⟩

end Commons.Analysis.CalderonZygmund
