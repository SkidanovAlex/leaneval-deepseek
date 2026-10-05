import Mathlib
import Submission.Work.RPCore.Flow.fderiv_bounded_of_periodic_on_slab
import Submission.Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab

/-!
# A global `C⁰`/`C¹` bound for a periodic function supported in a slab

If `f : PS → ℝ` is `C¹`, `2π`-periodic in the angle `q₂` and vanishes outside the slab
`{|q₁| + |p₁| + |p₂| ≤ R}`, then both `|f|` and `‖fderiv ℝ f‖` are globally bounded by a single
constant `M ≥ 0`.

The two halves are supplied by the library:

* `bounded_of_periodic_of_eq_on_slab` (with the constant `0`, `B = 0`) bounds `|f|`;
* `fderiv_bounded_of_periodic_on_slab` bounds `‖fderiv ℝ f‖`,

and we take `M` to be the maximum of the two constants.
-/

open scoped Topology

namespace Work.RPCore.Chain

theorem bounds_of_periodic_slab (f : Work.RPV.PS → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : ∀ x, f (Work.RPV.Tk 1 x) = f x) (R : ℝ)
    (hsupp : ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → f x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |f x| ≤ M) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ M) := by
  -- Bound on `‖fderiv ℝ f‖`.
  obtain ⟨M₁, hM₁₀, hM₁⟩ :=
    Work.RPCore.Flow.fderiv_bounded_of_periodic_on_slab f hf hper R hsupp
  -- Bound on `|f|`, obtained from the same compactness statement applied to `f` itself
  -- (viewed as a function of `(t, x)` constant in `t`, with slab constant `0`).
  obtain ⟨M₂, hM₂₀, hM₂⟩ :=
    Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab (V := ℝ)
      (fun z : ℝ × Work.RPV.PS => f z.2) (hf.continuous.comp continuous_snd)
      (fun z => hper z.2)
      (fun z hz => hsupp z.2 (le_of_lt hz)) 0
  refine ⟨max M₁ M₂, le_max_of_le_left hM₁₀, ?_, ?_⟩
  · intro x
    have h := hM₂ (0, x) (by simp)
    simpa using le_trans h (le_max_right M₁ M₂)
  · intro x
    exact le_trans (hM₁ x) (le_max_left M₁ M₂)

end Work.RPCore.Chain
