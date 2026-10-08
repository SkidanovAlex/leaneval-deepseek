import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `cfInner` of two integral combinations of a "diagonal" pair of families

If `F, F' : ι → M → ℂ` satisfy `⟨F x, F' y⟩ = δ_{x y}` (diagonal `1`, off-diagonal `0`), then the
character inner product of any two integral combinations `∑ c x • F x` and `∑ d y • F' y` is
`∑ c x * d x`.  This is the index-set (rather than Finset/`Orthonormal`) form of
`Work.Coherence.cfInner_eq_sum_coeff_mul` used in the coherence argument.
-/

noncomputable section

open Classical

namespace Work.Coherence

theorem cfInner_span_eq {M : Type*} [Fintype M] {ι : Type*} [Fintype ι]
    (c d : ι → ℤ) (F F' : ι → M → ℂ)
    (hdiag : ∀ x, cfInner (F x) (F' x) = 1)
    (hoff : ∀ x y, x ≠ y → cfInner (F x) (F' y) = 0) :
    cfInner (∑ x : ι, (c x : ℂ) • F x) (∑ y : ι, (d y : ℂ) • F' y)
      = ∑ x : ι, (c x : ℂ) * (d x : ℂ) := by
  have h1 : cfInner (∑ x : ι, (c x : ℂ) • F x) (∑ y : ι, (d y : ℂ) • F' y)
      = ∑ x : ι, cfInner ((c x : ℂ) • F x) (∑ y : ι, (d y : ℂ) • F' y) := by
    simpa using cfInner_sum_left (Finset.univ) (fun x => (c x : ℂ) • F x)
      (∑ y : ι, (d y : ℂ) • F' y)
  rw [h1]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [cfInner_smul_left]
  congr 1
  rw [cfInner_sum_right]
  simp only [cfInner_smul_right]
  rw [Finset.sum_eq_single x]
  · rw [hdiag x, mul_one]
    simp
  · intro y _ hy
    rw [hoff x y (fun hxy => hy hxy.symm), mul_zero]
  · intro hx; exact absurd (Finset.mem_univ x) hx

end Work.Coherence
