import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.tower3Arr_deriv_time_of_target

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the chart tower `tower3Arr`

`Work.Diff.EXT.ConnCov.tower3Arr G x₀ t A m v i j l` is the chart recursion of a `(0,3)`-array
`A` with respect to the *fixed* background connection `cGam (G 0)`: level `0` is the base `A`,
and every level is the chart derivative of the previous level in the direction `v 0`, corrected
by the four Christoffel contractions of the coordinate frame.  The parameter `t` is phantom:
`tower3Arr G x₀ s A m v i j l` depends on `s` only through the base `A`.

Hence, for a family `s ↦ A s` of base arrays, the time derivative of the tower of the family is the
tower of the pointwise time derivative `∂_s A`:

`∂_s (tower3Arr G x₀ s (A s) m v i j l y) = tower3Arr G x₀ t (∂_s A) m v i j l y`   at `s = t`.

**This is the statement of the present file.**  The hypothesis `hy : y ∈ (extChartAt I x₀).target`
is essential (and is part of the requested statement): the recursion multiplies by the coefficient
functions `y' ↦ cGam (G 0) x₀ (pt x₀ y') k i j`, which are smooth exactly on the chart target —
they involve the inverse chart `pt x₀ = (extChartAt I x₀).symm`, whose values outside the target are
arbitrary junk data of the `ChartedSpace` structure.  Off the target these coefficients need not
even be continuous, the tower levels need not be differentiable, and `fderiv` defaults to `0` there,
so the claimed identity genuinely fails (see the docstring of
`Submission/Work/Diff/EXT/ConnCov/tower3Arr_deriv_time_of_target.lean` for the explicit
counterexample).

The substantive proof — the induction on the level, whose step differentiates the chart recursion in
`s` and commutes `∂_s` with `fderiv_y` by Clairaut's theorem (the joint smoothness of the levels,
`C²` suffices, coming from `hy` and the joint smoothness of `A`) — is carried out in the modules

* `Submission.Work.Diff.EXT.ConnCov.tower3Arr_jointSmooth` (joint smoothness of every level of the
  tower, by an induction whose only analytic input is that the slice derivative of a jointly `C^∞`
  function is jointly `C^∞`); and
* `Submission.Work.Diff.EXT.ConnCov.tower3Arr_deriv_time_of_target` (the derivative statement, with
  the joint smoothness of the levels as an explicit hypothesis `J`, discharged there by the former).

The present file exposes that result under the requested name.
-/

namespace Work.Diff.EXT.ConnCov

theorem tower3Arr_deriv_time
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (A : ℝ → E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hsm : ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => A p.1 p.2 i j l) (t, y)) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      HasDerivAt (fun s : ℝ =>
          Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ s (A s) m v i j l y)
        (Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ t
          (fun y' i j' l => deriv (fun s : ℝ => A s y' i j' l) t) m v i j l y) t :=
  tower3Arr_deriv_time_of_target (I := I) (M := M) G x₀ hy A hsm

/-- **The time derivative of the reaction tower**: the specialisation of
`tower3Arr_deriv_time` to the base family `s ↦ aCompArr G x₀ s` (the chart array of the connection
difference `aComp`).  Since `reactArr G x₀ t = ∂_s (aCompArr G x₀ s)` *by definition*, the time
derivative of the `∇^{G 0}`-chart tower of the connection difference is the tower of the reaction
array `reactArr`.

This is the form in which the statement is consumed by the chart bound
`Work.Diff.EXT.ConnCov.dAOfTower_chart_bound`: for a fixed level `m` and direction tuple `v` it
identifies `∂_t (∇^{G 0}{}^m aComp)(y)` with `(∇^{G 0}{}^m ∂_t aComp)(y)`, i.e. with the chart tower
of `reactArr` — the object whose jet bounds are proven in `Work.Diff.EXT.ConnCov.reactJetsKit`. -/
theorem tower3Arr_aCompArr_deriv_time
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (hsm : ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l) (t, y)) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      HasDerivAt (fun s : ℝ =>
          Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ s
            (aCompArr (I := I) (M := M) G x₀ s) m v i j l y)
        (Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ t
          (reactArr (I := I) (M := M) G x₀ t) m v i j l y) t := by
  intro m v i j l
  -- `aCompArr G x₀ s` and `reactArr G x₀ t` are *definitionally* the base family
  -- `s ↦ (aComp G x₀ s)` and its pointwise time derivative, so the statement is the
  -- instance of `tower3Arr_deriv_time` at that base family.
  exact tower3Arr_deriv_time (I := I) (M := M) G x₀ (t := t) (y := y) hy
    (A := fun s y' i j l => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ s y' i j l) hsm m v i j l

end Work.Diff.EXT.ConnCov
