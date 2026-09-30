import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for `Work.BMF.SD.tk_bad_weight`

The Turán--Kubilius / Markov argument bounding the reciprocal-prime weight of the "bad"
primes (those for which the correlation of the dilated phase is small) uses

* `tkw_disc`, the discrepancy of `f` on the multiples of `p` with the phase `φ` inserted, and
* `tkw_bad`, the exceptional set of primes at a fixed left endpoint `y`.

These are made public here so that the two independent pieces of the argument
(the per-`y` weight bound, and the "small discrepancy gives a large correlation") can be
proved in separate modules and assembled in `Work.BMF.SD.tk_bad_weight`.
-/

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF

/-- The "discrepancy of `f` on the multiples of `p`" with the phase `φ` inserted. -/
noncomputable def tkw_disc (f : ℕ → ℂ) (φ : Polynomial ℝ) (p : ℕ) (x H : ℝ) : ℂ :=
  (∑ m ∈ natIcc (x / p) ((x + H) / p),
      f (p * m) * eC (-(Polynomial.eval ((p * m : ℕ) : ℝ) φ)))
    - (1 / p) * (∑ n ∈ natIcc x (x + H), f n * eC (-(Polynomial.eval (n : ℝ) φ)))

/-- The exceptional set of primes at a fixed `y`: either `p` is small, or the discrepancy of
`f` on the multiples of `p` is large. -/
def tkw_bad (c₀ H : ℝ) (f : ℕ → ℂ) (φ : Polynomial ℝ) (y : ℝ) (p : ℕ) : Prop :=
  ((p : ℝ) < 64 / c₀) ∨
    ((c₀ / 4) ^ 2 * H ^ 2 < (p : ℝ) ^ 2 * ‖tkw_disc f φ p y H‖ ^ 2)

/-- `tkw_bad` is a union of two conditions, so filtering by it is a union of filters. -/
lemma tkw_bad_filter (c₀ H : ℝ) (f : ℕ → ℂ) (φ : Polynomial ℝ) (y : ℝ) (S : Finset ℕ) :
    S.filter (fun (p : ℕ) => tkw_bad c₀ H f φ y p) =
      (S.filter (fun (p : ℕ) => (p : ℝ) < 64 / c₀)) ∪
        (S.filter (fun (p : ℕ) =>
          (c₀ / 4) ^ 2 * H ^ 2 < (p : ℝ) ^ 2 * ‖tkw_disc f φ p y H‖ ^ 2)) := by
  rw [← Finset.filter_or]
  exact Finset.filter_congr (fun x _ => Iff.rfl)

/-- Union bound for sums of nonnegative terms. -/
lemma tkw_sum_union_le (s t : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ x ∈ t, 0 ≤ g x) :
    ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  have h1 : ∑ x ∈ (s ∪ t) \ s, g x + ∑ x ∈ s, g x = ∑ x ∈ s ∪ t, g x :=
    Finset.sum_sdiff (Finset.subset_union_left : s ⊆ s ∪ t)
  have h2 : (s ∪ t) \ s = t \ s := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have h3 : ∑ x ∈ t \ s, g x ≤ ∑ x ∈ t, g x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun x hx _ => hg x hx)
  calc ∑ x ∈ s ∪ t, g x = ∑ x ∈ t \ s, g x + ∑ x ∈ s, g x := by rw [← h1, h2]
    _ ≤ ∑ x ∈ t, g x + ∑ x ∈ s, g x := by linarith
    _ = ∑ x ∈ s, g x + ∑ x ∈ t, g x := by ring

end Work.BMF.SD
