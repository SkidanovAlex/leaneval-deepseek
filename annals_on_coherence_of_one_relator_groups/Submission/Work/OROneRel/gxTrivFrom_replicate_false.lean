/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `x₀`-chain of downward steps starting at level `v`

`gxTrivFrom c D i L` says that every traversed edge of the word `L`, read from the level `i`
(`decor c i L`), has trivial loop class under the gauge `D`
(`coverClassAt D c (coverEdge p) = 1`).

The word `List.replicate n (x₀, false)` is the walk that takes `n` *downward* steps through the
`x₀`-edge of the `ℤ`-cover, i.e. it goes from level `v` down to `v - n * c x₀`, and the decorated
letters are read at the levels `v - c x₀`, `v - 2 * c x₀`, …, `v - n * c x₀`:

`decor c v (List.replicate n (x₀, false))`
  `= ((x₀, v - c x₀), false) :: ((x₀, v - 2 * c x₀), false) :: ⋯ :: ((x₀, v - n * c x₀), false)`.

The hypothesis `h` says precisely that consecutive gauges are related by a *right* multiplication by
`x₀`, `D (v - m * c x₀) = D (v - (m + 1) * c x₀) * of x₀`, so that the loop class of the `m`-th
traversed edge,

`coverClassAt D c (x₀, v - (m+1) * c x₀) = D (v - (m+1) * c x₀) * of x₀ * (D (v - m * c x₀))⁻¹`,

collapses to `1`.  The proof is a plain induction on `n`, the induction hypothesis being applied at
the shifted base level `v - c x₀` to the tail of the decorated list (the hypothesis is re-indexed by
`m ↦ m + 1`, which is exactly the content of the arithmetic step).
-/

import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

namespace Work.OROneRel

theorem gxTrivFrom_replicate_false {α : Type*} [DecidableEq α] (c : α → ℤ) (D : ℤ → FreeGroup α)
    (x₀ : α) (v : ℤ) (n : ℕ)
    (h : ∀ m : ℕ, m < n →
      D (v - (m : ℤ) * c x₀) = D (v - ((m : ℤ) + 1) * c x₀) * FreeGroup.of x₀) :
    Work.OROneRel.gxTrivFrom c D v (List.replicate n (x₀, false)) := by
  induction n generalizing v with
  | zero =>
      intro p hp
      simp only [List.replicate_zero, decor, List.not_mem_nil] at hp
  | succ n ih =>
      intro p hp
      rw [List.replicate_succ, decor.eq_3, List.mem_cons] at hp
      rcases hp with rfl | hp
      · -- the head traversal: the edge `(x₀, v - c x₀)`, with `D v = D (v - c x₀) * of x₀`
        rw [coverEdge, coverClassAt, gaugeMap_of]
        rw [show (v - c x₀) + c x₀ = v from by ring]
        have h0 : D v = D (v - c x₀) * FreeGroup.of x₀ := by
          have hh := h 0 (by omega)
          simpa using hh
        rw [← h0]
        exact mul_inv_cancel _
      · -- the tail: the same statement read from the shifted base level `v - c x₀`
        have h' : ∀ m : ℕ, m < n →
            D ((v - c x₀) - (m : ℤ) * c x₀) =
              D ((v - c x₀) - ((m : ℤ) + 1) * c x₀) * FreeGroup.of x₀ := by
          intro m hm
          have key := h (m + 1) (by omega)
          have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
          rw [hcast] at key
          rw [show (v - c x₀) - (m : ℤ) * c x₀ = v - ((m : ℤ) + 1) * c x₀ from by ring,
              show (v - c x₀) - ((m : ℤ) + 1) * c x₀
                = v - (((m : ℤ) + 1) + 1) * c x₀ from by ring]
          exact key
        exact ih (v - c x₀) h' p hp

end Work.OROneRel
