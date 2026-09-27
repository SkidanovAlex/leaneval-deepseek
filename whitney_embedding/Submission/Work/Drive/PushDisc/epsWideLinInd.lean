import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens

/-!
# A continuous family that is linearly independent on `[-1,1]` is so on a wider interval

`Work.Drive.PushDisc.epsWideLinInd`: if `γ : ℝ → Fin (2 + k + k) → Mdl k` is continuous and the
family `γ x` is linearly independent for every `x ∈ [-1, 1]`, then there is `ε > 0` such that
`γ x` is linearly independent for every `x` with `|x| ≤ 1 + ε`.

The mathematical content is the *openness of linear independence*: for a **finite** family of
vectors in a complete normed space, `{f : ι → E | LinearIndependent 𝕜 f}` is open
(Mathlib's `isOpen_setOfPred_linearIndependent`, whose proof is quantitative: an independent family
has a uniform injectivity modulus `K` of the linear combination map, and any family within `1/K`
of it in sup-norm is still independent).  Composing with the continuous path `γ` and applying
compactness of `[-1, 1]` (`IsCompact.exists_thickening_subset_open`) produces a uniform thickening;
the elementary one-dimensional computation `mem_thickening_Icc_of_abs_le` converts the thickening
radius `δ` into the interval bound `|x| ≤ 1 + δ/2`.
-/

namespace Work.Drive.PushDisc

open Set Metric

/-- Every real number with `|x| ≤ 1 + δ/2` lies in the open `δ`-thickening of `[-1, 1]`: the foot
of the perpendicular is the clamp `max (-1) (min 1 x)`. -/
theorem mem_thickening_Icc_of_abs_le (δ : ℝ) (hδ : 0 < δ) {x : ℝ} (hx : |x| ≤ 1 + δ / 2) :
    x ∈ thickening δ (Icc (-1 : ℝ) 1) := by
  rw [mem_thickening_iff]
  refine ⟨max (-1) (min 1 x), ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, ?_⟩
  rw [Real.dist_eq]
  have hx' := abs_le.mp hx
  have key : |x - max (-1) (min 1 x)| ≤ δ / 2 := by
    rcases le_or_gt x 1 with h1 | h1
    · rw [min_eq_right h1]
      rcases le_or_gt (-1 : ℝ) x with h2 | h2
      · rw [max_eq_right h2, sub_self, abs_zero]; linarith
      · rw [max_eq_left (le_of_lt h2), abs_of_neg (by linarith)]; linarith
    · rw [min_eq_left (le_of_lt h1), max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
        abs_of_pos (by linarith)]
      linarith
  linarith

theorem epsWideLinInd {k : ℕ} (γ : ℝ → Fin (2 + k + k) → Work.Drive.Whitney.Mdl k)
    (hγ : Continuous γ)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ (γ x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| ≤ 1 + ε → LinearIndependent ℝ (γ x) := by
  have hopen : IsOpen {x : ℝ | LinearIndependent ℝ (γ x)} :=
    isOpen_setOfPred_linearIndependent.preimage hγ
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_thickening_subset_open hopen h
  exact ⟨δ / 2, half_pos hδpos,
    fun x hx => hδsub (mem_thickening_Icc_of_abs_le δ hδpos hx)⟩

end Work.Drive.PushDisc
