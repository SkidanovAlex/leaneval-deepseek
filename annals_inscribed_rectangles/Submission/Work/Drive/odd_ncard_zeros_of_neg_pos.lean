import Mathlib
import Submission.Work.Drive.ncard_zeros_mod_four_eq_two
import Submission.Work.Surf.signChangeAt_of_hasDerivAt

/-!
# The parity of the number of zeros between a negative and a positive value

If `f : ℝ → ℝ` is differentiable on `[0,1]`, has `f 0 < 0 < f 1`, and its zeros on `[0,1]` are
finite and simple (the derivative does not vanish at them), then the number of zeros of `f` in
`[0,1)` is odd.

This is the one-dimensional parity statement behind the oddness inputs of Hugelmeyer's Lemma 2.  The
analytic content is already available in the workspace:

* `Work.Drive.odd_ncard_zeros_of_opposite_signs` — a continuous function on an interval whose
  endpoint values have opposite signs and whose zeros are all sign changes has an odd number of
  zeros;
* `Work.Surf.signChangeAt_of_hasDerivAt` — a zero with non-vanishing derivative is a sign change.

The only remaining steps are: differentiability on `[0,1]` gives continuity; `deriv f t ≠ 0` at the
zeros turns them into sign changes; and since `f 1 > 0` there is no zero at the right endpoint, so
the zeros of `[0,1]` are exactly the zeros of `[0,1)`.
-/

namespace Work.Drive

/-- **Parity of the number of zeros from a negative to a positive value.** -/
theorem odd_ncard_zeros_of_neg_pos {f : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (deriv f x) x)
    (h0 : f 0 < 0) (h1 : 0 < f 1)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ f t = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = 0 → deriv f t ≠ 0) :
    Odd ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ f t = 0}).ncard := by
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hsc : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = 0 → SignChangeAt f t :=
    fun t ht hft => Work.Surf.signChangeAt_of_hasDerivAt (hder t ht) (hreg t ht hft) hft
  have hodd : Odd ({t ∈ Set.Icc (0:ℝ) 1 | f t = 0} : Set ℝ).ncard :=
    odd_ncard_zeros_of_opposite_signs zero_le_one hcont hfin hsc
      (ne_of_lt h0) (ne_of_gt h1) (Or.inl ⟨h0, h1⟩)
  have hset : ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ f t = 0} : Set ℝ)
      = {t ∈ Set.Icc (0:ℝ) 1 | f t = 0} := by
    ext t
    simp only [Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨ht0, ht1⟩, htz⟩
      exact ⟨⟨ht0, le_of_lt ht1⟩, htz⟩
    · rintro ⟨⟨ht0, ht1⟩, htz⟩
      refine ⟨⟨ht0, ?_⟩, htz⟩
      rcases lt_or_eq_of_le ht1 with hlt | heq
      · exact hlt
      · exact absurd (heq ▸ htz) (ne_of_gt h1)
  rw [hset]
  exact hodd

end Work.Drive
