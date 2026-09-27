import Mathlib
import Submission.Work.Whitney.isClosed_setOf_norm_le
import Submission.Work.Whitney.exists_clean_ball

/-!
# Shrinking the clean-ball data to the radius of the inserted model

`Work.Whitney.exists_clean_ball` produces, around a clean point, a chart `c'`, a radius `S` and a
separation constant `η` with

* `f` injective on the `2S`-ball,
* `η ≤ ‖f y - f z‖` for `‖c' y‖ ≤ S` and `2S ≤ ‖c' z‖`,
* every point of the `3S`-ball lies in the source.

The insertion move `Work.Whitney.exists_addDoublePoint_chart_like` however prescribes the *model's*
support radius `R ≤ S`: the neighbourhood modified by the model has radius `R`, and its hypotheses
are the two clean conditions at radius `R` (with a fresh separation constant `η'`).  This file
derives them from the radius-`S` data, for every `R ≤ S`: the injectivity at radius `R` follows from
injectivity on the `2S`-ball together with the separation at level `S`, and the separation at radius
`R` is the positive minimum of `‖f y - f z‖` over the compact pair of sets
`{‖c y‖ ≤ R}` and `{2R ≤ ‖c z‖}`, whose values are pairwise distinct by the same two inputs.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **The clean data at a smaller radius.** -/
theorem exists_clean_data_shrink {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (S η : ℝ) (hS : 0 < S) (hη : 0 < η)
    (hsrc : ∀ y : M, ‖c y‖ ≤ 3 * S → y ∈ c.source)
    (hball : Metric.ball 0 (3 * S) ⊆ c.target)
    (hinj : ∀ y z : M, ‖c y‖ ≤ 2 * S → ‖c z‖ ≤ 2 * S → f y = f z → y = z)
    (hsep : ∀ y z : M, ‖c y‖ ≤ S → 2 * S ≤ ‖c z‖ → η ≤ ‖f y - f z‖)
    (R : ℝ) (hR : 0 < R) (hRS : R ≤ S) :
    ∃ η' : ℝ, 0 < η' ∧
      (∀ y : M, ‖c y‖ < R → ∀ z : M, f y = f z → z = y) ∧
      (∀ y z : M, ‖c y‖ < R → 2 * R ≤ ‖c z‖ → f y ≠ f z → η' ≤ ‖f y - f z‖) := by
  have h2R3S : 2 * R ≤ 3 * S := by linarith
  have hKclosed : IsClosed {y : M | ‖c y‖ ≤ R} :=
    isClosed_setOf_norm_le c (R := S) (r := R) (by linarith) (fun y hy => hsrc y (le_of_lt hy)) hball
  have hopen : IsOpen {z : M | ‖c z‖ < 2 * R} := by
    have hset : {z : M | ‖c z‖ < 2 * R} = c.symm '' (Metric.ball 0 (2 * R) ∩ c.target) := by
      ext z
      constructor
      · intro hz
        have hz' : ‖c z‖ < 2 * R := hz
        have hz3 : ‖c z‖ < 3 * S := by linarith
        have hzs : z ∈ c.source := hsrc z (le_of_lt hz3)
        refine ⟨c z, ⟨?_, c.map_source hzs⟩, c.left_inv hzs⟩
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hz
      · rintro ⟨u, ⟨hu, hut⟩, rfl⟩
        show ‖c (c.symm u)‖ < 2 * R
        rw [c.right_inv hut]
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    rw [hset]
    refine c.symm.isOpen_image_of_subset_source (Metric.isOpen_ball.inter c.open_target)
      Set.inter_subset_right
  have hZclosed : IsClosed {z : M | 2 * R ≤ ‖c z‖} := by
    have hset : {z : M | 2 * R ≤ ‖c z‖} = {z : M | ‖c z‖ < 2 * R}ᶜ := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [hset]; exact hopen.isClosed_compl
  have hdisj : ∀ y ∈ {y : M | ‖c y‖ ≤ R}, ∀ z ∈ {z : M | 2 * R ≤ ‖c z‖}, f y ≠ f z := by
    rintro y hy z hz hfyz
    have hy' : ‖c y‖ ≤ R := hy
    have hz' : 2 * R ≤ ‖c z‖ := hz
    by_cases hz2S : ‖c z‖ < 2 * S
    · have hy2S : ‖c y‖ ≤ 2 * S := by linarith
      have hzy : z = y := (hinj y z hy2S (le_of_lt hz2S) hfyz).symm
      rw [hzy] at hz'
      linarith
    · have hz2S' : 2 * S ≤ ‖c z‖ := le_of_not_gt hz2S
      have h1 : η ≤ ‖f y - f z‖ := hsep y z (by linarith) hz2S'
      rw [hfyz, sub_self, norm_zero] at h1
      linarith
  obtain ⟨η', hη'pos, hη'⟩ := exists_pos_le_norm_sub hf hKclosed hZclosed hdisj
  refine ⟨η', hη'pos, ?_, ?_⟩
  · intro y hyR z hyz
    by_cases hz2R : ‖c z‖ < 2 * R
    · have hRS2 : R ≤ 2 * S := by linarith
      have h2RS : 2 * R ≤ 2 * S := by linarith
      exact (hinj y z (le_trans (le_of_lt hyR) hRS2) (le_trans (le_of_lt hz2R) h2RS) hyz).symm
    · exact absurd hyz (hdisj y (le_of_lt hyR) z (le_of_not_gt hz2R))
  · intro y z hyR hz2R hne
    exact hη' y (le_of_lt hyR) z hz2R

end Work.Whitney
