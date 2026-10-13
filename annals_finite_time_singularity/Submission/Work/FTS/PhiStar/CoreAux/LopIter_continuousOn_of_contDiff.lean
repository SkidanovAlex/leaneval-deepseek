/-
# Continuity of the iterated angular operator `Lop^[i] = (sin(2θ) ∂_θ)^i`

`Work.Spaces.Lop u = fun θ => sin (2 θ) * deriv u θ` is the action of the angular operator
`D_θ = sin(2θ) ∂_θ` on a one-dimensional slice, and `Work.FTS.EllipticEst.LopIter i u` is its
`i`-th iterate.  This file proves that on the closed angular interval
`Iθ = [0, π/2]` these iterates of a `C^m` datum are continuous as long as `i ≤ m`.

The quantitative statement proved first is the exact regularity bookkeeping: one application of
`Lop` consumes exactly one order of differentiability,

`ContDiff ℝ (p + i) u  →  ContDiff ℝ p (Lop^[i] u)`,

which is an induction on `i` using `ContDiff.deriv'` (a `C^{n+1}` function has a `C^n`
derivative) and the fact that the factor `θ ↦ sin (2θ)` is smooth.  Note that the order
arguments are natural numbers cast into `ℕ∞ω = WithTop ℕ∞`, so that the induction never has to
manipulate truncated subtraction in `WithTop`; the subtraction `m - i` in the application is
performed in `ℕ` before the cast.

As an immediate corollary, `LopIter i c` is continuous (hence continuous on `Iθ`) whenever
`c` is `C^m` with `i ≤ m`; this is the requested
`Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff`.

Both proofs are `sorry`-free and use only `propext`, `Classical.choice` and `Quot.sound`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

/-- **The regularity bookkeeping of the iterated angular operator.**  If `u` is of class `C^{p+i}`
on `ℝ` then `Lop^[i] u` is of class `C^p`: each iteration `Lop u = sin(2·) · u'` costs exactly
one order of differentiability. -/
theorem Lop_iter_contDiff (i p : ℕ) (u : ℝ → ℝ) (h : ContDiff ℝ (p + i : ℕ) u) :
    ContDiff ℝ (p : ℕ) (Work.Spaces.Lop^[i] u) := by
  induction i generalizing p with
  | zero => simpa using h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    -- `h` has order `p + (i+1)`; rewrite it as `(p+1) + i` to apply the induction hypothesis
    -- with the shifted `p + 1`.
    have h' : ContDiff ℝ (p + 1 + i : ℕ) u := (show p + (i + 1) = p + 1 + i by omega) ▸ h
    have hd : ContDiff ℝ (p + 1 : ℕ) (Work.Spaces.Lop^[i] u) := ih (p + 1) h'
    have hdp : ContDiff ℝ (p : ℕ) (deriv (Work.Spaces.Lop^[i] u)) := ContDiff.deriv' hd
    have hsin : ContDiff ℝ (p : ℕ) (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    change ContDiff ℝ (p : ℕ)
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[i] u) θ)
    exact hsin.mul hdp

theorem LopIter_continuousOn_of_contDiff (m : ℕ) (c : ℝ → ℝ) (hc : ContDiff ℝ (m : ℕ∞) c) : ∀ i ≤ m, ContinuousOn (Work.FTS.EllipticEst.LopIter i c) Work.Spaces.Iθ := by
  intro i hi
  -- Regard `hc` as a `C^m` hypothesis with `m` cast from `ℕ`, and split `m = (m - i) + i`.
  have hci : ContDiff ℝ (m : ℕ) c := hc
  have h' : ContDiff ℝ ((m - i) + i : ℕ) c := by
    rw [Nat.sub_add_cancel hi]; exact hci
  have hcd : ContDiff ℝ (m - i : ℕ) (Work.Spaces.Lop^[i] c) := Lop_iter_contDiff i (m - i) c h'
  change ContinuousOn (Work.Spaces.Lop^[i] c) Work.Spaces.Iθ
  exact hcd.continuous.continuousOn

end Work.FTS.PhiStar.CoreAux
