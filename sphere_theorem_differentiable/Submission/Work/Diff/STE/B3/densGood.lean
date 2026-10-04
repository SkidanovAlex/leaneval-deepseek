import Mathlib
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.STE.deTurck.posDef_gmat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: `DensGood`, i.e. positivity and smoothness of the chart volume density

For the Layer B3 data `D` (see `B3/Data.lean`) the *volume density* of the chart at `x₀ i` is

`D.dens i z = √det (chartMatFun g₀ (x₀ i) (flatToE x₀ i z))`,

`√det` of the Gram matrix of the coordinate frame at the point with flat coordinate `z`.  The
predicate `D.DensGood i` (see `B3/CompSmooth.lean`) asks that, as a function of the flat
coordinate `z` ranging over the chart target, this density is *strictly positive* and `C^∞`.

Both halves are elementary `√det`-facts about the chart matrix, which the workspace already
provides in usable form:

* positivity is the positive definiteness of the Gram matrix of a Riemannian metric in a frame
  (`Work.Diff.STE.deTurck.posDef_gmat`), whose determinant is positive
  (`Matrix.PosDef.det_pos`); the coordinate frame of a chart is a basis, so its Gram matrix is
  positive definite.
* smoothness is `√` of a smooth function that is non-zero (`Real.contDiffAt_sqrt`) composed with
  the determinant (`Matrix.det`, a polynomial in the entries) of the chart matrix, which is
  `C^∞` in the flat coordinate (`Work.Diff.EXT.kz_contDiffAt_chartMatFun`).

This file is the missing ingredient of `B3Data.DensGood`: `B3/CompSmooth.lean` takes
`DensGood i` as a hypothesis when it proves smoothness of the localised components
`R i h a b = ψ i · √dens i · mat i h a b`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/-- **The determinant is a smooth function of the entries of a matrix.**  The determinant is the
polynomial `∑_σ sign σ · ∏_i A (σ i) i` in the entries (`Matrix.det_apply'`), and polynomials are
smooth. -/
lemma contDiff_det_of {n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  rw [funext (fun A => Matrix.det_apply' (Matrix.of A))]
  simp only [Matrix.of_apply]
  refine ContDiff.sum (𝕜 := ℝ) (E := Fin n → Fin n → ℝ) (s := Finset.univ)
    (f := fun (σ : Equiv.Perm (Fin n)) (A : Fin n → Fin n → ℝ) =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i) (fun σ _ => ?_)
  refine ContDiff.mul contDiff_const ?_
  exact contDiff_prod (𝕜 := ℝ) (E := Fin n → Fin n → ℝ) (t := Finset.univ)
    (f := fun (i : Fin n) (A : Fin n → Fin n → ℝ) => A (σ i) i) (fun i _ => by fun_prop)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

theorem densGood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    D.DensGood i := by
  intro z hz
  -- The point of `M` whose flat coordinate is `z`, lying in the chart at `x₀ i`.
  have hsymm : (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)
      ∈ (chartAt H (D.x₀ i)).source := by
    rw [← extChartAt_source (I := I) (D.x₀ i)]
    exact PartialEquiv.map_target (extChartAt I (D.x₀ i)) hz
  -- The chart matrix is the Gram matrix of the coordinate frame, hence positive definite.
  have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
      ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)))).PosDef :=
    Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hsymm
  have hdetpos : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z))).det := by
    have := hpd.det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z))
        = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z) from rfl] at this
  refine ⟨?_, ?_⟩
  · -- positivity of the density
    simpa only [Work.Diff.STE.B3Data.dens] using Real.sqrt_pos.mpr hdetpos
  · -- smoothness of the density in the flat coordinate
    have hflat : ContDiffAt ℝ (⊤ : ℕ∞) (flatToE (I := I) (D.x₀ i)) z :=
      (contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt
    have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i))
        (flatToE (I := I) (D.x₀ i) z) :=
      Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ (D.x₀ i) hz
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z)) z :=
      hchart.comp z hflat
    have hdet : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det) z :=
      (contDiff_det_of (n := Module.finrank ℝ E)).contDiffAt.comp z hcomp
    have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z => Real.sqrt ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z))).det)) z :=
      (Real.contDiffAt_sqrt (ne_of_gt hdetpos)).comp z hdet
    exact hsqrt

end Work.Diff.STE.B3
