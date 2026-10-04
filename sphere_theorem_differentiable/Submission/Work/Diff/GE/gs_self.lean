import Mathlib
import Submission.Work.Diff.GE.frame_family_defs
import Submission.Work.Diff.L.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gram–Schmidt of an orthonormal family is the family itself

The Gram–Schmidt recursion `gs b κ` of `Submission/Work/Diff/GE/frame_family_defs.lean` is, at
`s = t`, applied to the family `κ = onFrame (G t) x`, which is *already* orthonormal for the form
`b = frameB G x t = (G t).inner x`.  This file records the two elementary facts that make the
statement `frameFamily G t x t = onFrame (G t) x` immediate:

* `gsU_self_of_isON`: the pre-normalisation vector of an orthonormal family is the vector itself;
* `gs_eq_self_of_isON`: hence Gram–Schmidt returns the family unchanged.

Both are pure algebra (no positivity, no completeness), and are used to evaluate the frame and its
derivatives at `s = t`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If `κ` is `b`-orthogonal (in the sense that `b (κ i) (κ j) = 0` for `j < i`), then the
pre-normalisation vector of the Gram–Schmidt recursion is `κ i` itself. -/
theorem gsU_self_of_isON {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (h : ∀ i j : Fin n, j.val < i.val → b (κ i) (κ j) = 0) (i : Fin n) :
    gsU b κ κ i = κ i := by
  rw [gsU]
  have : (∑ j : Fin n, if j.val < i.val then b (κ i) (κ j) • κ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < i.val
    · rw [if_pos hj, h i j hj, zero_smul]
    · rw [if_neg hj]
  rw [this, sub_zero]

/-- **Gram–Schmidt of an orthonormal family is the family itself**: if `b (κ i) (κ j) = δᵢⱼ`, then
`gs b κ = κ`. -/
theorem gs_eq_self_of_isON {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (h : ∀ i j : Fin n, b (κ i) (κ j) = if i = j then 1 else 0) :
    gs b κ = κ := by
  have key : ∀ m : ℕ, ∀ i : Fin n, i.val < m → gs b κ i = κ i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · rw [gs_apply]
        have hcong := gsU_congr (b := b) (κ := κ) (E := gs b κ) (E' := κ) (i := i)
          (fun j hj => ih j (by rw [← heq]; exact hj))
        rw [hcong,
          gsU_self_of_isON b κ
            (fun a c hac => by
              have hne : a ≠ c := fun hh => absurd (hh ▸ hac) (Nat.lt_irrefl _)
              rw [h a c, if_neg hne])]
        rw [h i i, if_pos rfl]
        simp
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

end Generic

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Gram–Schmidt family starts at `onFrame (G t) x`**: at `s = t` the metric `G t` makes
`onFrame (G t) x` orthonormal, so the Gram–Schmidt process returns it unchanged. -/
theorem frameFamily_at_t (G : ℝ → SMet I M) (t : ℝ) (x : M) :
    frameFamily G t x t = onFrame (G t) x :=
  gs_eq_self_of_isON (frameB G x t) (onFrame (G t) x)
    (fun i j => (Work.Diff.L.onFrame_isONFrame (G t) x) i j)

/-- The pre-normalisation vector of the Gram–Schmidt family at `s = t` is `onFrame (G t) x i`. -/
theorem frameU_at_t (G : ℝ → SMet I M) (t : ℝ) (x : M) (i : Fin (Module.finrank ℝ E)) :
    frameU G t x t i = onFrame (G t) x i := by
  rw [frameU, frameFamily_at_t]
  exact gsU_self_of_isON (frameB G x t) (onFrame (G t) x)
    (fun a c hac => by
      have hne : a ≠ c := fun hh => absurd (hh ▸ hac) (Nat.lt_irrefl _)
      have h1 : (G t).inner x (onFrame (G t) x a) (onFrame (G t) x c) = if a = c then 1 else 0 :=
        Work.Diff.L.onFrame_isONFrame (G t) x a c
      show (G t).inner x (onFrame (G t) x a) (onFrame (G t) x c) = 0
      rw [h1, if_neg hne])
    i

end Manifold

end Work.Diff.GE
