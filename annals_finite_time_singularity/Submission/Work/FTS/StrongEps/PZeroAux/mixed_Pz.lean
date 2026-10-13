/-
# The mixed derivative of the projection `P₀`

The projection of `Submission/Work/FTS/StrongEps/PZero.lean` is

  `Pz f = f − (L₁₂ f 0 / pzNorm) • bump`,   i.e.   `Pz f z θ = f z θ − c * bump z θ`

with `c = L₁₂ f 0 / pzNorm`.  Since `D_z^j D_θ^i` is a linear combination of the partial
derivatives `∂_z^a∂_θ^b` with `θ`-only coefficients, it is linear on the open quadrant `Q0`
where the data are `C^∞`:

  `D_z^j D_θ^i (Pz f) = D_z^j D_θ^i f − c · D_z^j D_θ^i bump`   on `Q0`.

This module proves exactly that, as

  `Work.FTS.StrongEps.PZeroAux.mixed_Pz`.

Route: rewrite `Pz f` pointwise as `f + (−c)*bump` (`Pz_apply`), apply the additivity of
`mixed` on the open quadrant for `SmoothOpen` data
(`Work.FTS.EllipticEst.SmoothOpen.mixed_add`, whose second argument is `SmoothOpen` because
`bump` is, `smoothOpen_bump`), and use the *unconditional* scalar homogeneity of the iterated
operators `DzIter_const_mul` / `DthIter_const_mul` for the correction term.

(Note: `open scoped Real` is needed for the `π` of the statement's `Set.Ioo 0 (π / 2)` to
denote `Real.pi` — that is the same set as the `Q0`/`SmoothOpen` quadrant below.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.mixed_const_mul
import Submission.Work.FTS.StrongEps.mixed_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.PZeroAux

/-- **The mixed derivative of the projection `P₀`.**  On the open quadrant the iterated
operator `D_z^j D_θ^i` is linear, so it acts on `Pz f = f − (L₁₂ f 0 / pzNorm) • bump`
by the two terms of the definition. -/
theorem mixed_Pz {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Pz f) z θ
      = Work.Spaces.mixed j i f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
  -- the scalar of the correction
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hc
  -- the pointwise form of the projection
  have hPz : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, ← hc]
    ring
  -- the correction profile `(−c)·bump` is smooth on the open quadrant
  have hgsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) := by
    have hfun : Function.uncurry (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ)
        = fun p : ℝ × ℝ => (-c) * Function.uncurry Work.FTS.StrongEps.bump p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
    exact (contDiffOn_const (c := (-c)) (s := Work.FTS.EllipticEst.Q0)).mul
      Work.FTS.StrongEps.smoothOpen_bump
  -- unconditional scalar homogeneity of the correction term
  have hmul : Work.Spaces.mixed j i (fun z' θ' => (-c) * Work.FTS.StrongEps.bump z' θ') z θ
      = (-c) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
    simp only [Work.Spaces.mixed, DthIter_const_mul (-c) Work.FTS.StrongEps.bump i,
      DzIter_const_mul (-c) (Work.Spaces.DthIter i Work.FTS.StrongEps.bump) j]
  calc Work.Spaces.mixed j i (Work.FTS.StrongEps.Pz f) z θ
      = Work.Spaces.mixed j i
          (fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ) z θ := by rw [hPz]
    _ = Work.Spaces.mixed j i f z θ
          + Work.Spaces.mixed j i (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.mixed_add hsm hgsm j i z θ hz hθ.1 hθ.2
    _ = Work.Spaces.mixed j i f z θ
          + (-c) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by rw [hmul]
    _ = Work.Spaces.mixed j i f z θ
          - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
        rw [hc]; ring

end Work.FTS.StrongEps.PZeroAux
