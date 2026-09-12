import Mathlib
import Submission.Conjugates
import Submission.XTransfer

/-!
# Bounds for the star over the conjugates

For a nonzero algebraic integer `α` with conjugate set `S := conjugateValues α`
and house `H := NumberField.house α`, the star `star S` (over `{z², z⁴}`)
lies in the closed ball of radius `H⁴` around the origin:

    ∀ X ∈ star S, ‖X‖ ≤ H⁴

Indeed every conjugate `z ∈ S` satisfies `‖z‖ ≤ H`
(`Submission.Conjugates.norm_conj_le_house`), so the tips `z²`, `z⁴` have
norm `≤ H² ≤ H⁴` and `≤ H⁴` respectively (using `1 ≤ H`, from
`one_le_house_of_isIntegral_ne_zero`), and points on the segment
`[0, z^k]` have norm `≤ ‖z^k‖`.

This is the geometric input ("spikes of length at most `house⁴`") used later
with Dubinin's hedgehog bound to obtain `τ(star S) < 1` under
`house < 2^(1/(4 d'))`.

You may add helper lemmas.  Do NOT change the statements below.  No sorries
may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.StarBounds

open Submission.Conjugates
open Submission.XTransfer

/-- Points on a segment from `0` to `c` have norm at most `‖c‖`. -/
lemma norm_le_of_mem_segment_zero {c : ℂ} {X : ℂ} (hX : X ∈ segment ℝ 0 c) :
    ‖X‖ ≤ ‖c‖ := by
  rcases (Submission.XTransfer.mem_segment_zero_iff c X).1 hX with ⟨t, ht, hXt⟩
  have ht0 : 0 ≤ t := ht.1
  calc
    ‖X‖ = ‖t • c‖ := by rw [hXt]
    _ = t * ‖c‖ := by rw [norm_smul]; simp [abs_of_nonneg ht0]
    _ ≤ ‖c‖ := by
      have hnorm0 : 0 ≤ ‖c‖ := norm_nonneg c
      nlinarith [ht.2]

/-- If a conjugate `z` has norm at most `H`, then so does any power `z ^ n`. -/
lemma norm_pow_le_of_norm_le {z : ℂ} {H : ℝ} (h : ‖z‖ ≤ H) (n : ℕ) :
    ‖z ^ n‖ ≤ H ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) h n

/-- Every element of the star `star (conjugateValues α)` has norm at most
`(house α) ^ 4`. -/
theorem star_subset_closedBall_house {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    (star (conjugateValues α)) ⊆ Metric.closedBall (0 : ℂ) ((NumberField.house α) ^ 4) := by
  classical
  let H := NumberField.house α
  have hH : 1 ≤ H := by
    simpa [H] using (one_le_house_of_isIntegral_ne_zero hα hα0)
  intro X hX
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  change ‖X‖ ≤ H ^ 4
  rcases hX with ⟨z, hz, hXseg⟩
  have hzH : ‖z‖ ≤ H := by
    rcases Finset.mem_image.mp hz with ⟨σ, _hσ, hzσ⟩
    simpa [H, hzσ] using (norm_conj_le_house α σ)
  rcases hXseg with hX2 | hX4
  · have hseg : ‖X‖ ≤ ‖z ^ 2‖ := norm_le_of_mem_segment_zero hX2
    have hz2 : ‖z ^ 2‖ ≤ H ^ 2 := norm_pow_le_of_norm_le hzH 2
    have h2le4 : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by decide : (2 : ℕ) ≤ 4)
    exact le_trans (le_trans hseg hz2) h2le4
  · have hseg : ‖X‖ ≤ ‖z ^ 4‖ := norm_le_of_mem_segment_zero hX4
    have hz4 : ‖z ^ 4‖ ≤ H ^ 4 := norm_pow_le_of_norm_le hzH 4
    exact le_trans hseg hz4

end Submission.StarBounds

end
