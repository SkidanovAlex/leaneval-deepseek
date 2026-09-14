import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.InnerProduct

/-- Given at least two distinct points `p i` in a real inner product space, there is a point
`p i₀` and a nonzero direction `δ` such that `p i₀` is strictly separated from all the other
points: `⟪p i₀ - p j, δ⟫ > 0` for every `j ≠ i₀`. Concretely, a point of maximal norm works,
with `δ = p i₀`. -/
theorem exists_inner_pos_extreme {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → E)
    (hinj : Function.Injective p) (h2 : 2 ≤ Fintype.card ι) :
    ∃ i₀ : ι, ∃ δ : E, δ ≠ 0 ∧ ∀ j : ι, j ≠ i₀ → 0 < inner ℝ (p i₀ - p j) δ := by
  -- Choose a point of maximal norm.
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => ‖p i‖) Finset.univ_nonempty
  refine ⟨i₀, p i₀, ?_, ?_⟩
  · -- The chosen point is nonzero.
    intro hzero
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) i₀
    have hjle : ‖p j‖ ≤ ‖p i₀‖ := hi₀ j (Finset.mem_univ j)
    rw [hzero, norm_zero] at hjle
    have hnorm : ‖p j‖ = 0 := le_antisymm hjle (norm_nonneg _)
    have hpj : p j = 0 := by rwa [norm_eq_zero] at hnorm
    exact hj (hinj (by rw [hpj, hzero]))
  · -- Strict separation.
    intro j hj
    by_contra hle
    rw [not_lt] at hle
    -- `hle : ⟪p i₀ - p j, p i₀⟫ ≤ 0` implies `⟪p j, p i₀⟫ ≥ ‖p i₀‖²`.
    have hle' : ‖p i₀‖ ^ 2 ≤ inner ℝ (p j) (p i₀) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at hle
      linarith
    have hjle : ‖p j‖ ≤ ‖p i₀‖ := hi₀ j (Finset.mem_univ j)
    have hjle_sq : ‖p j‖ ^ 2 ≤ ‖p i₀‖ ^ 2 := by
      nlinarith [hjle, norm_nonneg (p j), norm_nonneg (p i₀)]
    have hkey : ‖p i₀ - p j‖ ^ 2 ≤ ‖p j‖ ^ 2 - ‖p i₀‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm]
      linarith
    have hzero : ‖p i₀ - p j‖ ^ 2 = 0 := by nlinarith [hkey, hjle_sq]
    have hpij : p i₀ = p j := by
      have h1 : ‖p i₀ - p j‖ = 0 := sq_eq_zero_iff.mp hzero
      exact sub_eq_zero.mp (norm_eq_zero.mp h1)
    exact hj (hinj hpij).symm

end Commons.Analysis.InnerProduct