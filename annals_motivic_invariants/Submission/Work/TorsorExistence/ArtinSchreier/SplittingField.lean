/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence.ArtinSchreier
-/
import Mathlib
import Submission.Work.TorsorExistence.ArtinSchreier.Basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The root field of an Artin–Schreier polynomial is its splitting field

If `𝕜` has characteristic `5`, `L/𝕜` is a field extension, `α ∈ L` satisfies `α ^ 5 - α = a` and
`L = 𝕜(α)`, then `L` is a splitting field of `X ^ 5 - X - a` over `𝕜`: the roots of that
polynomial in `L` are exactly `α, α + 1, …, α + 4`.
-/

set_option autoImplicit false

universe u

open Polynomial

namespace Work.TorsorExistence.ArtinSchreier

/-- **The root field of an Artin–Schreier polynomial is its splitting field.**  If `L = 𝕜(α)` and
`α ^ 5 - α = a`, then `L` is a splitting field of `X ^ 5 - X - a` over `𝕜`. -/
theorem isSplittingField_adjoin_of_pow_five_sub_self {𝕜 L : Type u} [Field 𝕜] [CharP 𝕜 5]
    [Field L] [Algebra 𝕜 L] (a : 𝕜) {α : L} (hα : α ^ 5 - α = algebraMap 𝕜 L a)
    (hgen : Algebra.adjoin 𝕜 ({α} : Set L) = ⊤) :
    IsSplittingField 𝕜 L (X ^ 5 - X - C a : 𝕜[X]) := by
  have h5L : (5 : L) = 0 := by
    have h := congrArg (algebraMap 𝕜 L) (CharP.cast_eq_zero 𝕜 5)
    simp only [map_zero] at h
    rw [map_natCast] at h
    exact h
  have hp0 : (X ^ 5 - X - C a : 𝕜[X]) ≠ 0 := by
    intro h
    have h2 : (X ^ 5 - X - C a : 𝕜[X]).natDegree = 5 := by
      have hh : (X ^ 5 - X - C a : 𝕜[X]) = (X ^ 5 - C a) - X := by ring
      rw [hh, natDegree_sub_eq_left_of_natDegree_lt]
      · exact natDegree_X_pow_sub_C
      · rw [natDegree_X, natDegree_X_pow_sub_C]; norm_num
    rw [h] at h2; simp at h2
  refine ⟨?_, ?_⟩
  · rw [show (X ^ 5 - X - C a : 𝕜[X]).map (algebraMap 𝕜 L)
        = X ^ 5 - X - C (algebraMap 𝕜 L a) from by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]]
    rw [← hα, ← prod_range_five_shift (R := L) h5L α]
    exact Splits.prod (fun i _ => Splits.X_sub_C _)
  · rw [eq_top_iff, ← hgen]
    apply Algebra.adjoin_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [mem_rootSet_of_ne hp0]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hα, sub_self]

end Work.TorsorExistence.ArtinSchreier
