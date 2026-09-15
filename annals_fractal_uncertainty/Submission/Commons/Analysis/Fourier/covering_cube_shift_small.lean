import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators

/-- One-dimensional covering by unit half-width intervals centred at even integers.
If `(a+1)/2 ≤ N` then the intervals `[2k-1, 2k+1]` with `-N ≤ k ≤ N` cover `[-a,a]`; moreover
`|2k| ≤ a+1` and `|y - 2k| ≤ 1`. -/
private lemma int_cover_floor (N : ℤ) (a y : ℝ) (hN : (a + 1) / 2 ≤ (N : ℝ))
    (hy : -a ≤ y ∧ y ≤ a) :
    -N ≤ ⌊(y + 1) / 2⌋ ∧ ⌊(y + 1) / 2⌋ ≤ N ∧
      |2 * ((⌊(y + 1) / 2⌋ : ℤ) : ℝ)| ≤ a + 1 ∧
      |y - 2 * ((⌊(y + 1) / 2⌋ : ℤ) : ℝ)| ≤ 1 := by
  have hfl := Int.floor_le ((y + 1) / 2)
  have hlt := Int.lt_floor_add_one ((y + 1) / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Int.cast_le (R := ℝ)).mp
    push_cast
    linarith
  · have key : (((⌊(y + 1) / 2⌋ : ℤ)) : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast key
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- The windows `2m + [-1,1]^d` with `|2 mᵢ| ≤ α₁+1` cover the cube `[-α₁,α₁]^d` in the
integral sense, and the index set is exactly the one allowed by the damping hypothesis
(`|ηᵢ| ≤ α₁+1`). -/
theorem covering_cube_shift_small (d : ℕ) {α₁ : ℝ} (hα₁ : 1 ≤ α₁) :
    ∃ (s : Finset (Fin d → ℤ)), (∀ m ∈ s, ∀ i : Fin d, |2 * (m i : ℝ)| ≤ α₁ + 1) ∧
      ∀ (G : EuclideanSpace ℝ (Fin d) → ℂ),
        MeasureTheory.MemLp G 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) →
        MeasureTheory.integral (MeasureTheory.volume.restrict
            {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -α₁ ≤ x i ∧ x i ≤ α₁})
            (fun x => ‖G x‖ ^ 2)
          ≤ ∑ m ∈ s, MeasureTheory.integral (MeasureTheory.volume.restrict
              {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1})
              (fun x => ‖G x‖ ^ 2) := by
  classical
  let N : ℤ := ⌈α₁⌉
  let s : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d =>
      (Finset.Icc (-N) N).filter (fun k : ℤ => |2 * (k : ℝ)| ≤ α₁ + 1))
  have hN : (α₁ + 1) / 2 ≤ (N : ℝ) := by
    have h1 : (α₁ + 1) / 2 ≤ α₁ := by linarith
    have h2 : α₁ ≤ (N : ℝ) := by simp only [N]; exact Int.le_ceil α₁
    linarith
  refine ⟨s, ?_, ?_⟩
  · intro m hm i
    rw [Fintype.mem_piFinset] at hm
    exact (Finset.mem_filter.mp (hm i)).2
  · intro G hG
    set f : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ‖G x‖ ^ 2 with hfdef
    have hf_int : Integrable f volume := by
      rw [hfdef]
      exact (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
    have hcover : {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -α₁ ≤ x i ∧ x i ≤ α₁}
        ⊆ ⋃ m ∈ s, {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1} := by
      intro x hx
      simp only [Set.mem_iUnion]
      refine ⟨fun i => ⌊(x i + 1) / 2⌋, ?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_filter]
        obtain ⟨h1, h2, h3, -⟩ := int_cover_floor N α₁ (x i) hN ⟨(hx i).1, (hx i).2⟩
        exact ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, h3⟩
      · intro i
        obtain ⟨-, -, -, h4⟩ := int_cover_floor N α₁ (x i) hN ⟨(hx i).1, (hx i).2⟩
        exact h4
    have hle : (volume.restrict {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -α₁ ≤ x i ∧ x i ≤ α₁})
        ≤ ∑ m ∈ s, volume.restrict
            {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1} := by
      rw [Measure.le_iff]
      intro E hE
      rw [Measure.restrict_apply hE, Measure.finsetSum_apply]
      simp only [Measure.restrict_apply hE]
      calc volume (E ∩ {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, -α₁ ≤ x i ∧ x i ≤ α₁})
          ≤ volume (⋃ m ∈ s, (E ∩ {x : EuclideanSpace ℝ (Fin d) |
              ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1})) := by
            apply measure_mono
            intro x hx
            obtain ⟨hxE, hxC⟩ := hx
            have hxs := hcover hxC
            simp only [Set.mem_iUnion] at hxs ⊢
            obtain ⟨m, hm, hxm⟩ := hxs
            exact ⟨m, hm, hxE, hxm⟩
        _ ≤ ∑ m ∈ s, volume (E ∩ {x : EuclideanSpace ℝ (Fin d) |
              ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1}) :=
            measure_biUnion_finset_le s _
    have hf_intν : Integrable f (∑ m ∈ s, volume.restrict
        {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1}) :=
      (integrable_finsetSum_measure).2
        (fun m _ => hf_int.mono_measure Measure.restrict_le_self)
    have h1 := integral_mono_measure hle
      (Filter.Eventually.of_forall (fun x => by rw [hfdef]; exact sq_nonneg (‖G x‖))) hf_intν
    have h2 := integral_finsetSum_measure (μ := fun m => volume.restrict
        {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1})
      (s := s) (f := f) (fun m _ => hf_int.mono_measure Measure.restrict_le_self)
    exact h1.trans_eq h2

end Commons.Analysis.Fourier