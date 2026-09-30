import Mathlib
import Submission.Work.Final.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.LCSmooth

/-- Multiplying a `C^n` map into `E4` by a constant is `C^n`.

Mathlib's `ContMDiffOn.const_smul` would give this from the instance
`ContMDiffConstSMul Work.Space.I4 n ℝ Work.Space.E4`, which is not registered (the class is
stated for a general action `Γ` on a manifold `M`, and the scalar action of `ℝ` on its own model
space is not covered by any instance).  The map `x ↦ c • x` is a continuous linear map, so we
compose with it directly. -/
private lemma contMDiffOn_const_smul_E4 {M : Type*} [TopologicalSpace M]
    [ChartedSpace Work.Space.E4 M] {n : ℕ∞ω} {s : Set M}
    (c : ℝ) {f : M → Work.Space.E4}
    (hf : ContMDiffOn Work.Space.I4 Work.Space.I4 n f s) :
    ContMDiffOn Work.Space.I4 Work.Space.I4 n (fun q => c • f q) s := by
  have h1 : ContMDiffOn Work.Space.I4 Work.Space.I4 n
      (fun x : Work.Space.E4 => c • x) Set.univ :=
    ((c • (1 : Work.Space.E4 →L[ℝ] Work.Space.E4)).contMDiffOn (s := Set.univ)).congr
      (fun x _ => by simp)
  exact (h1.comp hf (fun _ _ => Set.mem_univ _)).congr (fun q _ => rfl)

/-- **The chart Christoffel symbol has `C^∞` coefficients.**  On a charted Riemannian manifold
(`Work.Final.ChartedRiem`: a manifold charted on `E4` with a `C^∞` Riemannian metric) with a
`C^∞` connection (`Work.Final.ChartedRiemConn`, e.g. the Levi-Civita connection
`Work.LCSmooth.chartedRiemConn`), the chart Christoffel symbol
`Submission.ChartCurv.chrB C.cov x₀ · a b` — the coordinate vector of `∇_{σ_b} σ_a` in the chart
at `x₀` — is `C^∞` on the source of that chart.

This is the "smooth coefficients" statement behind the Koszul route to the smoothness of the
Levi-Civita connection: the Koszul identity in charts says `g(chrB, ·) = ½ (∂g + ∂g − ∂g)`, so
`chrB = ½ g⁻¹(∂g + ∂g − ∂g)` is as smooth as the metric and its inverse.

Proof route: on the chart source, `chrB C.cov x₀ q a b` is the finite linear combination
`∑ᵢ ∑ⱼ ((coord i) a * (coord j) b) • gammaEntry C.cov x₀ i j q` of Christoffel entries
(`Submission.ChartCurv.chrB_eq_sum_gammaEntry`), and each `gammaEntry C.cov x₀ i j` is `C^∞` on
the chart source (`Submission.ChartCurv.contMDiffOn_gammaEntry`, from
`contMDiffOn_cov_apply` and the tangent-bundle trivialisation, using `C.smooth`).  Assemble with
`Finset` sums, `ContMDiffOn.const_smul`, `ContMDiffOn.congr` (and `Work.Final.smoothGrade`, which
is definitionally the `∞` of `ContMDiffOn`). -/
theorem contMDiffOn_chrB {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace Work.Space.E4 M] [Work.Final.ChartedRiem M]
    [C : Work.Final.ChartedRiemConn M] (x₀ : M) (a b : Work.Space.E4) :
    ContMDiffOn Work.Space.I4 Work.Space.I4 Work.Final.smoothGrade
      (fun q : M ↦ Submission.ChartCurv.chrB C.cov x₀ q a b)
      (chartAt Work.Space.E4 x₀).source := by
  classical
  have hsum : ContMDiffOn Work.Space.I4 Work.Space.I4 Work.Final.smoothGrade
      (fun q : M => ∑ i, ∑ j, (((Module.finBasis ℝ Work.Space.E4).coord i) a *
        ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
        Submission.ChartCurv.gammaEntry C.cov x₀ i j q)
      (chartAt Work.Space.E4 x₀).source := by
    refine contMDiffOn_finsetSum (t := Finset.univ) (f := fun i q => ∑ j,
      (((Module.finBasis ℝ Work.Space.E4).coord i) a *
        ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
        Submission.ChartCurv.gammaEntry C.cov x₀ i j q) ?_
    intro i _
    refine contMDiffOn_finsetSum (t := Finset.univ) (f := fun j q =>
      (((Module.finBasis ℝ Work.Space.E4).coord i) a *
        ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
        Submission.ChartCurv.gammaEntry C.cov x₀ i j q) ?_
    intro j _
    exact contMDiffOn_const_smul_E4 _
      (Submission.ChartCurv.contMDiffOn_gammaEntry (cov := C.cov) x₀ i j)
  refine ContMDiffOn.congr hsum ?_
  intro q hq
  rw [Submission.ChartCurv.chrB_eq_sum_gammaEntry (cov := C.cov) x₀ q a b hq]

end Work.LCSmooth
