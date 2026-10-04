import Mathlib
import Submission.Work.Diff.C.geoCrux.Port.Defs
import Submission.Work.Diff.C.JacobiUniqAux
import Submission.Work.Diff.C.isJacobiAt_add

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniqueness of a Jacobi field from its data at one time (two-centre form)

This file proves `Work.Diff.C.geoCrux.Port.TwoCentre.jacobi_uniq`, i.e. the closed `Prop`
`Work.Diff.C.geoCrux.Port.JacobiUniqCoreProp`: two Jacobi fields `J`, `Z` along the same `C^∞` curve with
nowhere vanishing velocity which have the same value **and** the same covariant derivative at one
time `t₀` are equal everywhere.

## Route

The Jacobi equation is a *linear* second-order ODE along `γ`, so the space of Jacobi fields is a
vector space and the data `(J t₀, ∇_{γ'}J(t₀))` determine the field.  Concretely:

1. **Linear structure** (`Work.Diff.C.isJacobiAt_add`, proved in
   `Submission/Work/Diff/C/isJacobiAt_add.lean`) — the sum of two germ-local Jacobi fields is a
   germ-local Jacobi field.  The proof there needs `cov.torsion = 0` (it transfers the chart data of
   one field into the chart of the other).
2. **Closure under negation** (`isJacobiAt_neg_field`, *this file*) — this one needs no chart
   transfer at all: the chart data of `-Z` in the very chart that gives the data of `Z` is obtained
   by negating the field coordinates (the chart Jacobi equation and the Christoffel terms are linear
   in the field).
3. **Closure under subtraction** (`isJacobiAt_sub_field`, *this file*) — `J - Z = J + (-Z)`, from 1
   and 2.
4. **Propagation** (`Work.Diff.C.eq_of_dual_zero`, proved in `Submission/Work/Diff/C/JacobiUniqAux.lean`)
   — a *single* Jacobi field with a double zero at one time vanishes identically.  The proof is the
   standard connectedness argument: the set of times near which the field vanishes is open (clear)
   and closed (interior-point uniqueness for the first-order linear Jacobi system), and nonempty.
   `Work.Diff.C.covAlong_sub` (same file) is the linearity of `covAlong` needed to see that
   `∇_{γ'}(J - Z)(t₀) = 0` when `J` and `Z` have the same covariant derivative at `t₀`.

The whole content is therefore in steps 2–3 (this file) plus the two proved library pieces.
Nothing beyond `propext`, `Classical.choice`, `Quot.sound` is used.

⚠ Note for maintainers: the *same* mathematical argument is also written in
`Submission/Work/Diff/C/geoCrux/SharpCore.lean` and `Submission/Work/Diff/C/geoCrux/jacobi_uniq.lean`
(targeting the `Prop` `Work.Diff.C.geoCrux.JacobiUniqProp`), where the helpers are named
`Work.Diff.C.geoCrux.chartCovDeriv_neg_aux`, `Work.Diff.C.geoCrux.isJacobiAt_neg_aux`,
`Work.Diff.C.geoCrux.isJacobiAt_sub_aux`.  Those two files *both* declare those names, so no module
may import both of them.  The helpers below are deliberately in the namespace
`Work.Diff.C.geoCrux.TwoCentre`, so that this module can be imported alongside either of them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter
open Submission.Geodesic
open Submission.Jacobi
open Submission.JacobiVec
open Submission.Rauch
open Submission.ChartConnection
open Submission.RauchGlobal
open Submission.JacobiGlobal

namespace Work.Diff.C.geoCrux.Port.TwoCentre

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- `chartCovDeriv` is **additively negative** in the field.  (Unconditional: the Christoffel term
is linear in the field and `deriv` of a negated function is the negated derivative.) -/
lemma chartCovDeriv_neg_field {x₀ : M} (u w y : ℝ → E) (s : ℝ) :
    chartCovDeriv cov x₀ u w (-y) s = -(chartCovDeriv cov x₀ u w y s) := by
  have hd : deriv (-y) s = -deriv y s := deriv.neg
  simp only [chartCovDeriv, hd, Pi.neg_apply, map_neg, neg_add]

/-- **`IsJacobiAt` is closed under negation of the field.**  The chart data for `-Z` is the chart
data for `Z` with the field coordinates negated (in the *same* chart, so no chart transfer and no
hypothesis on the connection is needed). -/
lemma isJacobiAt_neg_field {γ : ℝ → M} {Z : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hZ : IsJacobiAt cov γ Z t) :
    IsJacobiAt cov γ (-Z) t := by
  obtain ⟨x₀, u, w, y, hTgt, huD, hγeq, hyF, hunit, hyd, hzd, hjac⟩ := hZ
  have hfe : chartCovDeriv cov x₀ u w (-y)
      = -chartCovDeriv cov x₀ u w y := by
    funext σ
    exact chartCovDeriv_neg_field u w y σ
  refine ⟨x₀, u, w, -y, hTgt, huD, hγeq, ?_, hunit, ?_, ?_, ?_⟩
  · filter_upwards [hyF] with s hs
    simp only [Pi.neg_apply, frameVector_neg, hs]
  · filter_upwards [hyd] with s hs
    rw [deriv.neg]
    exact hs.neg
  · filter_upwards [hzd] with s hs
    rw [hfe, deriv.neg]
    exact hs.neg
  · filter_upwards [hjac, hTgt] with s hj htg
    have hp : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) htg
    have hneg : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w (-y)) s
        = -(chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) := by
      rw [hfe, chartCovDeriv_neg_field u w (chartCovDeriv cov x₀ u w y) s]
    have hcurv : chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) ((-y) s) (w s)
        = -(chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s)) := by
      rw [Pi.neg_apply, ← neg_one_smul ℝ (y s),
        chartCurv_smul_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u s)) hp (-1) (y s) (w s),
        neg_one_smul]
    rw [hneg, hcurv, ← neg_add, hj, neg_zero]

/-- **`IsJacobiAt` is closed under subtraction of fields** (germ form, at one time). -/
lemma isJacobiAt_sub_field (htor : cov.torsion = 0) {γ : ℝ → M}
    {J Z : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : IsJacobiAt cov γ J t) (hZ : IsJacobiAt cov γ Z t) :
    IsJacobiAt cov γ (fun s : ℝ ↦ J s - Z s) t := by
  have h := isJacobiAt_add (cov := cov) htor hJ (isJacobiAt_neg_field (cov := cov) hZ)
  have hfun : (fun s : ℝ ↦ J s - Z s) = (fun s : ℝ ↦ J s + (-Z) s) := by
    funext s
    rw [sub_eq_add_neg, Pi.neg_apply]
  rw [hfun]
  exact h

end

/-- **Uniqueness of a Jacobi field with prescribed data at one time.**  The difference `J - Z` is a
Jacobi field (germ form `isJacobiAt_sub_field`), and it has a double zero at `t₀`: the same value
(`hv`) and the same covariant derivative (`covAlong_sub` + `hd`).  So `Work.Diff.C.eq_of_dual_zero`
makes it vanish identically. -/
theorem jacobi_uniq : Work.Diff.C.geoCrux.Port.JacobiUniqCoreProp := by
  intro E hE1 hE2 hE3 hE4 H hH I M hM1 hM2 hM3 hMM hRB hIC hBd hNt hCS
    cov hCov htor γ hγ hne J Z hJ hZ t₀ hv hd t
  have hW : ∀ s : ℝ, IsJacobiAt cov γ (fun r : ℝ ↦ J r - Z r) s :=
    fun s ↦ isJacobiAt_sub_field (cov := cov) htor (hJ s) (hZ s)
  have h0 : (fun r : ℝ ↦ J r - Z r) t₀ = 0 := by
    show J t₀ - Z t₀ = 0
    rw [hv, sub_self]
  have hd0 : covAlong cov (fun r : ℝ ↦ J r - Z r) t₀ = 0 := by
    rw [covAlong_sub (cov := cov) htor hγ hJ hZ t₀, hd, sub_self]
  have hzero := eq_of_dual_zero (cov := cov) htor hγ hne hW h0 hd0 t
  have hz : J t - Z t = 0 := hzero
  exact sub_eq_zero.mp hz

end Work.Diff.C.geoCrux.Port.TwoCentre
