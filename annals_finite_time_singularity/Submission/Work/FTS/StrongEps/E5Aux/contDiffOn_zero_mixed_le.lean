/-
Copyright: work module for the Elgindi finite-time singularity project.

# Finite-order smoothness of the slots `D_zⁱD_θ^j` (arbitrary order)

`Work.FTS.StrongEps.E5Aux.contDiffOn_zero_mixed` (in `iterSmooth.lean`) covers the case
`n = 2`: every slot `D_zⁱD_θ^j` with `i + j ≤ 2` of a function that is only `C²` on the
open quadrant is continuous there.  This file removes the restriction on the order:

* `contDiffOn_DthIter_sub` / `contDiffOn_DzIter_sub`: applying `D_θ` (resp. `D_z`) `i`
  times to a function of class `C^m` on `Q0` costs exactly `i` orders of
  differentiability, i.e. the iterate is `C^{m - i}` (for `i ≤ m`);
* `contDiffOn_zero_mixed_le`: consequently every slot `D_z^j D_θ^i` with `j + i ≤ n` of a
  function of class `C^n` on `Q0` is *continuous* on `Q0`.

The proofs are inductions on the number of iterates, using the one-step lemmas
`contDiffOn_uncurry_Dth_succ` / `contDiffOn_uncurry_Dz_succ` of `iterSmooth.lean` and the
arithmetic of the `ℕ∞ω`-valued differentiability order (handled through the `ℕ`-valued
statements `(m - i : ℕ) : ℕ∞ω` and `Nat.cast_add`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E5Aux.iterSmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- `D_θ^i` costs `i` orders of differentiability: the `i`-fold `θ`-iterate of a function
of class `C^m` on `Q0` is of class `C^{m-i}` (with the natural-valued order `m - i`). -/
theorem contDiffOn_DthIter_sub {m : ℕ} {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ∀ i : ℕ, i ≤ m →
      ContDiffOn ℝ ((m - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DthIter i G))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
      intro hi
      have hih : ContDiffOn ℝ ((m - i : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 :=
        ih (by omega)
      have hsub : m - i = (m - (i + 1)) + 1 := by omega
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_uncurry_Dth_succ
        (n := ((m - (i + 1) : ℕ) : ℕ∞ω)) Work.FTS.EllipticEst.isOpen_Q0
        (by simpa [hsub, Nat.cast_add, Nat.cast_one] using hih)

/-- `D_z^j` costs `j` orders of differentiability: the `j`-fold `z`-iterate of a function
of class `C^m` on `Q0` is of class `C^{m-j}` (with the natural-valued order `m - j`). -/
theorem contDiffOn_DzIter_sub {m : ℕ} {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ∀ j : ℕ, j ≤ m →
      ContDiffOn ℝ ((m - j : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DzIter j G))
        Work.FTS.EllipticEst.Q0 := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
      intro hj
      have hih : ContDiffOn ℝ ((m - j : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DzIter j G)) Work.FTS.EllipticEst.Q0 :=
        ih (by omega)
      have hsub : m - j = (m - (j + 1)) + 1 := by omega
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_uncurry_Dz_succ
        (n := ((m - (j + 1) : ℕ) : ℕ∞ω)) Work.FTS.EllipticEst.isOpen_Q0
        (by simpa [hsub, Nat.cast_add, Nat.cast_one] using hih)

/-- Every slot `D_z^j D_θ^i` with `j + i ≤ n` of a function of class `C^n` on `Q0` is
continuous there (the finite-order counterpart of `contDiffOn_zero_mixed`). -/
theorem contDiffOn_zero_mixed_le {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) Work.FTS.EllipticEst.Q0) {j i : ℕ}
    (hji : j + i ≤ n) :
    ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 := by
  have hDth : ContDiffOn ℝ ((n - i : ℕ) : ℕ∞ω)
      (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_DthIter_sub (m := n) h i (by omega)
  have hjn : j ≤ n - i := by omega
  have hDz := contDiffOn_DzIter_sub (m := n - i) hDth j hjn
  have hmi : (n - i) - j = n - (j + i) := by omega
  rw [show ((((n - i) - j : ℕ)) : ℕ∞ω) = ((n - (j + i) : ℕ) : ℕ∞ω) from by rw [hmi]] at hDz
  have h0 : (0 : ℕ∞ω) ≤ ((n - (j + i) : ℕ) : ℕ∞ω) := by positivity
  simpa [Work.Spaces.mixed] using hDz.of_le h0

end Work.FTS.StrongEps.E5Aux
