import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A single finite-place contribution `log⁺(v x)` is at most the full logarithmic height
`logHeight₁ x`: the height is the sum of all `log⁺` contributions (finite places and, with
multiplicity, infinite places), each of them nonnegative. -/
theorem logHeight_one_le_of_finite {K : Type*} [Field K] [NumberField K] (x : K)
    (v : NumberField.FinitePlace K) : (v x).posLog ≤ Height.logHeight₁ x := by
  classical
  rw [NumberField.logHeight₁_eq]
  -- The infinite-place part is a sum of nonnegative terms.
  have hinf : 0 ≤ ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * (w x).posLog :=
    Finset.sum_nonneg fun w _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  -- It remains to compare the single finite-place term with the finite-place sum.
  suffices hfin : (v x).posLog ≤ ∑ᶠ w : NumberField.FinitePlace K, (w x).posLog by linarith
  by_cases hx : x = 0
  · subst hx
    simp
  · -- `log⁺ (w x)` has finite support, being contained in the finite support of `w x - 1`.
    have hsupp : Function.HasFiniteSupport (fun w : NumberField.FinitePlace K => (w x).posLog) := by
      refine Set.Finite.subset (NumberField.FinitePlace.hasFiniteMulSupport hx) ?_
      intro w hw
      simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
      intro h
      exact hw (by rw [h]; simp)
    -- The function supported only at `v` is finitely supported.
    have hsingle : Function.HasFiniteSupport
        (fun w : NumberField.FinitePlace K => if w = v then (v x).posLog else 0) := by
      rw [Function.HasFiniteSupport]
      refine (Set.finite_singleton v).subset ?_
      intro w hw
      rw [Set.mem_singleton_iff]
      by_contra h
      exact hw (by simp [h])
    have hle : (fun w : NumberField.FinitePlace K => if w = v then (v x).posLog else 0)
        ≤ (fun w : NumberField.FinitePlace K => (w x).posLog) := by
      intro w
      change (if w = v then (v x).posLog else 0) ≤ (w x).posLog
      by_cases h : w = v
      · subst h; simp
      · have : (if w = v then (v x).posLog else 0) = 0 := by simp [h]
        rw [this]; exact Real.posLog_nonneg
    calc (v x).posLog
        = ∑ᶠ w : NumberField.FinitePlace K, (if w = v then (v x).posLog else 0) := by
          rw [finsum_eq_single
            (fun w : NumberField.FinitePlace K => if w = v then (v x).posLog else 0) v
            (fun w hw => by simp [hw])]
          simp
      _ ≤ ∑ᶠ w : NumberField.FinitePlace K, (w x).posLog := finsum_le_finsum hsingle hsupp hle

end Work.BW
