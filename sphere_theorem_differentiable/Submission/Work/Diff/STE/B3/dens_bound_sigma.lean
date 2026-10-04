import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.EXT.continuousAt_chartMatFun_centre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: uniform two-sided bounds for the chart volume density on the `σ`-ball

`D.dens i z = √det (chartMatFun g₀ (x₀ i) (flatToE (x₀ i) z))` is the volume density of the chart
at `x₀ i`, expressed in the flat coordinates `z` centred at the chart centre.  The lemma proved
here,

`∃ c C, 0 < c ∧ 0 < C ∧ ∀ i z, ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C`,

is the uniform (in the chart `i` and in `z`) two-sided bound which is needed whenever the
`g₀`-norm of a localised component has to be compared with the flat `L²`-norm of its
representative: on the closed flat ball of radius `D.σ i` the chart is genuine and the density is
comparable to `1`.

The proof is compactness.  For a fixed chart `i`:

* the closed flat ball `Kᵢ = {z | ‖z‖ ≤ D.σ i}` is compact;
* every `z ∈ Kᵢ` has `flatToE (x₀ i) z` in the chart target, because `‖z‖ ≤ D.σ i ≤ 2 * D.σ i` and
  `D.htarget`;
* on the target the entries of the chart matrix are continuous
  (`Work.Diff.STE.B3.chartMatFun_continuousAt_target` below, which is the `I.Boundaryless`-free
  version of `Work.Diff.EXT.continuousAt_chartMatFun_centre`), so `D.dens i` is continuous on
  `Kᵢ` (as `√` of `det` of the chart matrix, along the affine map `flatToE`);
* the determinant of the chart matrix is positive at every point of the target, because the chart
  matrix is the Gram matrix of a Riemannian metric in the coordinate frame
  (`Work.Diff.STE.deTurck.posDef_gmat`); hence the density is strictly positive there.

So `D.dens i` attains a minimum `mᵢ > 0` and a maximum `Mᵢ` on `Kᵢ`, and the finitely many pairs
`(mᵢ, Mᵢ)` are combined by a minimum/maximum over `Finset.univ` (an induction on the finset, which
also disposes of the empty index type).

Note that all of this is done **without** `I.Boundaryless`: the target statement does not assume
it, and neither does the argument — the only continuity input is
`continuousAt_extChartAt_symm''`, which is unconditional.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ### `flatToE` is smooth (version without `I.Boundaryless`) -/

/-- The affine identification of the flat coordinates with the model space `E` is `C^∞`.  This is
`Work.Diff.STE.contDiff_flatToE`, restated without the unused `I.Boundaryless` hypothesis. -/
lemma flatToE_contDiff (x₀ : M) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatToE (I := I) x₀) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) :=
    contDiff_const.add contDiff_id
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun.symm w) :=
    (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) :
        (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap.contDiff
  exact h2.comp h1

/-! ### Continuity of the chart matrix on the chart target -/

/-- **The entries of the chart matrix of a smooth metric are continuous at every point of the chart
target.**  This is the local version of `Work.Diff.EXT.continuousAt_chartMatFun_centre`; the proof
is the same, with `continuousAt_extChartAt_symm''` (which is unconditional) in place of
`continuousAt_extChartAt_symm` at the chart centre. -/
lemma chartMatFun_continuousAt_target (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun y' : E => Work.Diff.EXT.chartMatFun g x₀ y' i j) y := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hY : CMDiffAt ∞ (T% (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q
      (Work.Diff.EXT.bB (E := E) i))) ((extChartAt I x₀).symm y) :=
    Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Work.Diff.EXT.bB (E := E) i) hp
  have hZ : CMDiffAt ∞ (T% (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q
      (Work.Diff.EXT.bB (E := E) j))) ((extChartAt I x₀).symm y) :=
    Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Work.Diff.EXT.bB (E := E) j) hp
  have hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m))
      ((extChartAt I x₀).symm y) :=
    g.contMDiff _
  have hmain : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m
        (g.inner m (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j))))
      univ ((extChartAt I x₀).symm y) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : M => m)
      (v := fun m : M => Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
      (w := fun m : M => Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j))
      (ψ := fun m : M => g.inner m) (s := univ) (x := (extChartAt I x₀).symm y) hψ hY hZ
  have hsec : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun m : M => g.inner m
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j)))
      univ ((extChartAt I x₀).symm y) := by
    have := (contMDiffWithinAt_section (IB := I) (F := ℝ) (E := Bundle.Trivial M ℝ)
      (s := fun m : M => g.inner m
        (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j)))
      (a := univ) (x₀ := (extChartAt I x₀).symm y) (n := ∞)).mp hmain
    simpa using this
  have hcont : ContinuousAt (fun m : M => g.inner m
      (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) i))
      (Submission.Geodesic.frameVector (I := I) x₀ m (Work.Diff.EXT.bB (E := E) j)))
      ((extChartAt I x₀).symm y) :=
    (continuousWithinAt_univ _ _).1 hsec.continuousWithinAt
  have hcomp := hcont.comp (continuousAt_extChartAt_symm'' hy)
  simpa only [Function.comp_def, Work.Diff.EXT.chartMatFun] using hcomp

/-! ### Positivity and continuity of the density on the chart target -/

/-- **The volume density is strictly positive at every point of the chart target.**  The chart
matrix is the Gram matrix of the coordinate frame, hence positive definite
(`Work.Diff.STE.deTurck.posDef_gmat`), so its determinant is positive, and so is its square root. -/
lemma dens_pos_of_mem_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    0 < D.dens i z := by
  have hsrc : (extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z)
      ∈ (chartAt H (D.x₀ i)).source := by
    have h1 := (extChartAt I (D.x₀ i)).map_target hz
    rwa [extChartAt_source] at h1
  have hpd := Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hsrc
  have hdet : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z))).det := by
    have h := hpd.det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i)
          ((extChartAt I (D.x₀ i)).symm (flatToE (I := I) (D.x₀ i) z))
        = Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
          (flatToE (I := I) (D.x₀ i) z) from rfl] at h
  simpa only [Work.Diff.STE.B3Data.dens] using Real.sqrt_pos.mpr hdet

/-- **The volume density is continuous at every point of the chart target**: it is `√` (continuous
everywhere) of `det` (a polynomial) of the chart matrix (continuous by
`chartMatFun_continuousAt_target`) composed with the affine map `flatToE`. -/
lemma dens_continuousAt_of_mem_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContinuousAt (D.dens i) z := by
  have hflat : ContinuousAt (fun z' : Fin (Module.finrank ℝ E) → ℝ =>
      flatToE (I := I) (D.x₀ i) z') z :=
    (flatToE_contDiff (I := I) (M := M) (D.x₀ i)).continuous.continuousAt
  have hmat : ContinuousAt (fun z' : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.EXT.chartMatFun g₀ (D.x₀ i) (flatToE (I := I) (D.x₀ i) z')) z := by
    rw [continuousAt_pi]
    intro a
    rw [continuousAt_pi]
    intro b
    exact (chartMatFun_continuousAt_target (I := I) g₀ (D.x₀ i) hz a b).comp hflat
  have hdet : ContinuousAt (fun w : Work.Diff.EXT.MatE (E := E) => (Matrix.of w).det)
      (Work.Diff.EXT.chartMatFun g₀ (D.x₀ i) (flatToE (I := I) (D.x₀ i) z)) :=
    (Work.Diff.STE.B3.contDiff_det_of (n := Module.finrank ℝ E)).continuous.continuousAt
  have hdet2 : ContinuousAt (fun w : Work.Diff.EXT.MatE (E := E) =>
      Real.sqrt ((Matrix.of w).det))
      (Work.Diff.EXT.chartMatFun g₀ (D.x₀ i) (flatToE (I := I) (D.x₀ i) z)) :=
    Real.continuous_sqrt.continuousAt.comp hdet
  have hcomp := ContinuousAt.comp
    (f := fun z' : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.EXT.chartMatFun g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z'))
    (x := z)
    (g := fun w : Work.Diff.EXT.MatE (E := E) => Real.sqrt ((Matrix.of w).det)) hdet2 hmat
  change ContinuousAt (fun z' : Fin (Module.finrank ℝ E) → ℝ =>
    Real.sqrt (Matrix.det (Matrix.of (Work.Diff.EXT.chartMatFun g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z'))))) z
  simpa only [Function.comp_def] using hcomp

/-! ### The per-chart bound -/

/-- **Two-sided bound for the density of a single chart on its `σ`-ball.**  The closed flat ball
of radius `D.σ i` is compact, the density is continuous and strictly positive on it (its flat
coordinate lies in the chart target by `D.htarget`), so the density attains a positive minimum and
a maximum there. -/
lemma dens_bound_chart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ D.σ i → m ≤ D.dens i z ∧ D.dens i z ≤ M := by
  have hmem : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) ↔ ‖z‖ ≤ D.σ i := by
    intro z
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) :=
    isCompact_closedBall _ _
  have hKne : (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)).Nonempty :=
    ⟨0, by rw [hmem]; simpa using le_of_lt (D.hσ i)⟩
  have htgt : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i),
      flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target := by
    intro z hz
    refine D.htarget i z ?_
    have h1 : ‖z‖ ≤ D.σ i := (hmem z).mp hz
    have h2 : 0 < D.σ i := D.hσ i
    linarith
  have hcont : ContinuousOn (D.dens i)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)) :=
    fun z hz => (dens_continuousAt_of_mem_target D i (htgt z hz)).continuousWithinAt
  obtain ⟨zmin, hzmin, hmin⟩ := hKc.exists_isMinOn hKne hcont
  obtain ⟨zmax, hzmax, hmax⟩ := hKc.exists_isMaxOn hKne hcont
  exact ⟨D.dens i zmin, D.dens i zmax, dens_pos_of_mem_target D i (htgt zmin hzmin),
    hmin hzmax, fun z hz => ⟨hmin ((hmem z).mpr hz), hmax ((hmem z).mpr hz)⟩⟩

/-! ### The bound on a finite set of charts -/

/-- **Uniform two-sided bound for the density of the charts in a finite set.**  Induction on the
finset: the empty set is trivial, and the insert step takes the minimum of the two lower bounds
and the maximum of the two upper bounds. -/
lemma dens_bound_finset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (s : Finset ι₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ i ∈ s, ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 1, one_pos, one_pos, by simp⟩
  | insert a s ha ih =>
      obtain ⟨c, C, hc, hC, hb⟩ := ih
      obtain ⟨m, M, hm, hmM, hb'⟩ := dens_bound_chart D a
      refine ⟨min c m, max C M, lt_min hc hm, lt_max_of_lt_left hC, fun i hi z hz => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact ⟨le_trans (min_le_right _ _) (hb' z hz).1,
          le_trans (hb' z hz).2 (le_max_right _ _)⟩
      · exact ⟨le_trans (min_le_left _ _) (hb i hi' z hz).1,
          le_trans (hb i hi' z hz).2 (le_max_left _ _)⟩

/-- **Uniform two-sided bounds for the chart volume densities on the `σ`-balls.**  For the Layer B3
data `D` there are constants `0 < c ≤ C` with

`c ≤ D.dens i z ≤ C` for every chart `i` and every flat coordinate `z` with `‖z‖ ≤ D.σ i`.

This is the compactness argument: on the closed flat ball of radius `σ i` the chart is genuine, the
chart matrix is continuous and positive definite, hence `√det` is continuous and strictly positive
there, so it attains a positive minimum and a maximum; since the index type is finite, the finitely
many constants can be combined. -/
theorem dens_bound_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C := by
  obtain ⟨c, C, hc, hC, hb⟩ := dens_bound_finset D Finset.univ
  exact ⟨c, C, hc, hC, fun i z hz => hb i (Finset.mem_univ i) z hz⟩

end Work.Diff.STE.B3
