import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.Minkowski2.mem_latOf_one
import Submission.Work.BW.Minkowski2.smulSet_unitBall_eq
import Submission.Work.BW.Minkowski2.succSetL_notMem_of_nonpos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open Matrix
open scoped Pointwise

/-- The lattice `ℤⁿ`, realised as `Work.BW.latOf 1` (the `ℤ`-span of the standard basis vectors
of `ℝⁿ`), coincides with the set of integer vectors.  Pointwise form: `mem_latOf_one`. -/
private lemma latOf_one_coe {n : ℕ} :
    ((Work.BW.latOf (1 : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ))
      = {x : Fin n → ℝ | ∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)} :=
  Set.ext fun x => mem_latOf_one x

/-- The `Pointwise` form (the one occurring in `Work.BW.succMinBody`) of
`Work.BW.Minkowski2.smulSet_unitBall_eq`: the dilation by `t > 0` of the unit ball
`{y | F y ≤ 1}` of an absolutely homogeneous function `F` is the ball `{x | F x ≤ t}`. -/
private lemma smul_unitBall_eq {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {t : ℝ}
    (ht : 0 < t) : t • {y : Fin n → ℝ | F y ≤ 1} = {x : Fin n → ℝ | F x ≤ t} :=
  (Work.BW.smulSet_eq t {y : Fin n → ℝ | F y ≤ 1}).symm.trans (smulSet_unitBall_eq F hF ht)

/-- The successive minima of the lattice `ℤⁿ` with respect to the unit ball `{y | F y ≤ 1}` of a
lattice norm `F` (`Work.BW.IsLatticeNorm`, so `F` is nonnegative, absolutely homogeneous, vanishes
only at `0` and has finite sublevel sets on `ℤⁿ`) coincide with `Work.BW.succMinL F`, the infimum of
the levels `t` for which the lattice points of `F`-norm `≤ t` span a subspace of dimension `≥ j`.

Indeed `{x | F x ≤ t} = t • {y | F y ≤ 1}` for `t > 0` by homogeneity, and for `1 ≤ j` a level
`t ≤ 0` never qualifies (only `0` has `F`-norm `≤ t`, so the span is trivial), which is exactly why
the extra condition `0 < λ` in `Work.BW.succMinBody` is harmless. -/
theorem succMinL_eq_succMinBody {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    {j : ℕ} (hj : 1 ≤ j) :
    Work.BW.succMinL F j =
      Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin n) (Fin n) ℤ))
        {y : Fin n → ℝ | F y ≤ 1} j := by
  unfold Work.BW.succMinL Work.BW.succMinBody
  have hset : ∀ {t : ℝ}, 0 < t →
      ((Work.BW.latOf (1 : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ))
        ∩ (t • {y : Fin n → ℝ | F y ≤ 1})
      = {x : Fin n → ℝ | (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t} := by
    intro t ht
    rw [latOf_one_coe, smul_unitBall_eq F hF ht]
    ext x
    simp
  congr 1
  ext t
  constructor
  · intro ht
    change j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
      (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ F x ≤ t}) at ht
    have htpos : 0 < t := by
      by_contra h
      exact succSetL_notMem_of_nonpos F hF hj (not_lt.mp h) ht
    refine ⟨htpos, ?_⟩
    rw [hset htpos]
    exact ht
  · rintro ⟨htpos, ht⟩
    rw [hset htpos] at ht
    exact ht

end Work.BW.Minkowski2
