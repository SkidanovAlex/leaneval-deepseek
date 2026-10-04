import Mathlib
import Submission.Work.Diff.STE.D.transMap_interior_contDiffAt
import Submission.Work.Diff.STE.D.dens_interior_contDiffAt
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: smoothness of the variable-coefficient array of the localised components

This file proves `Work.Diff.STE.B3.VarCoef.coeff_contDiff`:  the coefficient

`z ↦ θ z * ρ z * (D.ζ i (D.pt l z))⁻¹ * (√(D.dens i (coord_i (D.pt l z))))⁻¹
        * (⟪e_l a, e_i c⟫ * ⟪e_l b, e_i d⟫)`

is `C^∞` on the flat coordinates, provided the cut-off `ρ` has its topological support in the set
where the normalised weight `ζ i` does not vanish and the flat coordinate lies in the *interior* of
the chart target of the chart `l`.

## Route

The function is a product of the (globally smooth) cut-offs `θ`, `ρ` with the pull-back along
`z ↦ D.pt l z` of a function on the manifold,

`H p = (ζ i p)⁻¹ * (√√(det (gmat g₀ (x₀ i) p)))⁻¹ * (⟪e_l a, e_i c⟫ p * ⟪e_l b, e_i d⟫ p)`,

and `H` is `C^∞` at every point of the chart source of `x₀ i` at which `ζ i ≠ 0`:

* `p ↦ gmat g₀ (x₀ i) p` is the Gram matrix of the coordinate frame, a smooth function of `p`
  (`Work.Diff.STE.B3.contMDiffAt_gmat_coeff'`, which needs **no** boundary or Hausdorff hypothesis),
  its determinant is positive (`Work.Diff.STE.deTurck.posDef_gmat`), and `√√` is smooth where the
  determinant does not vanish;
* the normalised weight `ζ i` is smooth and non-zero;
* the two pairings are smooth by `Work.EXT.ONF.pairing`.

No smoothness of `p ↦ D.dens i (coord_i p)` at a *boundary* point of the chart target is needed:
`D.dens i (coord_i p) = √det (gmat g₀ (x₀ i) p)` on the whole chart source
(`dens_coord_eq_gmat`), and the right hand side is smooth there.

Since `z ↦ D.pt l z` is smooth (`Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior`) at every point
whose flat coordinate lies in the *interior* of the chart target of `l`, the pull-back of `H` is
smooth on the support of `ρ`, and the product with `ρ` (which vanishes on an open neighbourhood of
every point outside `tsupport ρ`) is smooth everywhere.
-/

noncomputable section

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Function

namespace Work.Diff.STE.B3.VarCoef

/-! ## Elementary calculus -/

/-- The fourth root of the determinant of the chart matrix is smooth as a function of the matrix,
on the set where the determinant is positive. -/
theorem contDiffAt_sqrtSqrt_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A₀ : Work.Diff.EXT.MatE (E := E)) (hA : 0 < (Matrix.of A₀).det) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Work.Diff.EXT.MatE (E := E) =>
        Real.sqrt (Real.sqrt ((Matrix.of A).det))) A₀ := by
  have hdet : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Work.Diff.EXT.MatE (E := E) => (Matrix.of A).det) A₀ :=
    (Work.Diff.STE.B3.contDiff_det_of (n := Module.finrank ℝ E)).contDiffAt
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.sqrt x) ((Matrix.of A₀).det) :=
    Real.contDiffAt_sqrt (ne_of_gt hA)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.sqrt x)
      (Real.sqrt ((Matrix.of A₀).det)) :=
    Real.contDiffAt_sqrt (Real.sqrt_pos.mpr hA).ne'
  exact h2.comp A₀ (h1.comp A₀ hdet)

/-! ## The density, as a function on the manifold -/

/-- The chart volume density of the chart `i`, read as a function of the *point* of `M` rather than
of the flat coordinate: `√√det` of the Gram matrix of the coordinate frame at `p`.

On the chart source this is `√(D.dens i (coord_i p))` (`dens_coord_eq_gmat`), and — unlike
`D.dens i ∘ coord_i` — it is smooth at every point of the chart source, including boundary points
of the chart target, because it is the Gram matrix of a smooth frame that is being measured. -/
noncomputable def densGram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (p : M) : ℝ :=
  Real.sqrt (Real.sqrt (Matrix.det (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p))))

/-- The Gram matrix of the coordinate frame of the chart `i` is a smooth function of the point. -/
theorem gmat_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (chartAt H (D.x₀ i)).source) :
    ContMDiffAt I (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun q : M => Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) q) p := by
  refine contMDiffAt_pi_space.mpr (fun a => ?_)
  refine contMDiffAt_pi_space.mpr (fun b => ?_)
  exact Work.Diff.STE.B3.contMDiffAt_gmat_coeff' (I := I) g₀ (D.x₀ i) hp a b

/-- The pointwise density `densGram` is `C^∞` at every point of the chart source. -/
theorem densGram_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (chartAt H (D.x₀ i)).source) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (densGram (I := I) (g₀ := g₀) D i) p := by
  have hmat := gmat_contMDiffAt (I := I) (g₀ := g₀) D i hp
  have hdetpos : 0 < (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p)).det :=
    (Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hp).det_pos
  have hcd := contDiffAt_sqrtSqrt_det (E := E)
    (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p) hdetpos
  have hcm : ContMDiffAt (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E)))
      (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun A : Work.Diff.EXT.MatE (E := E) => Real.sqrt (Real.sqrt ((Matrix.of A).det)))
      (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p) :=
    contMDiffAt_iff_contDiffAt.mpr hcd
  exact hcm.comp p hmat

/-- The pointwise density `densGram` is strictly positive on the chart source. -/
theorem densGram_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (chartAt H (D.x₀ i)).source) :
    0 < densGram (I := I) (g₀ := g₀) D i p := by
  rw [densGram]
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr
    ((Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ i) hp).det_pos))

/-- **The dictionary between the flat density and the pointwise density**:  on the chart source, the
volume density of the chart `i` at the flat coordinate `coord_i p` is `√det` of the Gram matrix of
the coordinate frame at `p`. -/
theorem dens_coord_eq_gmat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) {p : M}
    (hp : p ∈ (extChartAt I (D.x₀ i)).source) :
    D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
      = Real.sqrt (Matrix.det (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p))) := by
  have harg : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p) := by abel
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) p) = (extChartAt I (D.x₀ i)) p := by
    simp only [Work.Diff.STE.flatToE, Work.Diff.STE.coord]
    rw [harg, LinearEquiv.symm_apply_apply]
  have hmat : Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
        ((extChartAt I (D.x₀ i)) p))
      = Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ i) p) := by
    ext a b
    simp only [Matrix.of_apply, Work.Diff.EXT.chartMatFun, Work.Diff.EXT.gmat,
      Work.Diff.EXT.fvec, Work.Diff.EXT.bB]
    rw [(extChartAt I (D.x₀ i)).left_inv hp]
  rw [Work.Diff.STE.B3Data.dens, hflat, hmat]

/-! ## The pointwise coefficient -/

/-- The variable-coefficient factor of the localised component of chart `l` with frame index `i`,
as a function of the point of `M`. -/
noncomputable def coeffM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) (p : M) : ℝ :=
  (D.ζ i p)⁻¹ * (densGram (I := I) (g₀ := g₀) D i p)⁻¹ *
    (g₀.inner p (D.e l a p) (D.e i c p) * g₀.inner p (D.e l b p) (D.e i d p))

/-- `coeffM` is `C^∞` at every point of the chart source at which the weight `ζ i` does not
vanish. -/
theorem coeffM_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H (D.x₀ i)).source) (hζ : D.ζ i p ≠ 0) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (coeffM (I := I) (g₀ := g₀) D l i a b c d) p := by
  have h1 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun q => (D.ζ i q)⁻¹) p :=
    ((D.hζsm i).contMDiffAt).inv₀ hζ
  have h2 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun q => (densGram (I := I) (g₀ := g₀) D i q)⁻¹) p :=
    (densGram_contMDiffAt (I := I) (g₀ := g₀) D i hp).inv₀
      (ne_of_gt (densGram_pos (I := I) (g₀ := g₀) D i hp))
  have h3 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun q => g₀.inner q (D.e l a q) (D.e i c q)) p :=
    Work.EXT.ONF.pairing g₀ p ((D.hesm l a).contMDiffAt) ((D.hesm i c).contMDiffAt)
  have h4 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun q => g₀.inner q (D.e l b q) (D.e i d q)) p :=
    Work.EXT.ONF.pairing g₀ p ((D.hesm l b).contMDiffAt) ((D.hesm i d).contMDiffAt)
  exact (h1.mul h2).mul (h3.mul h4)

/-! ## The target -/

theorem coeff_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (θ ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (i : ι₀) (c d : Fin (Module.finrank ℝ E))
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hsupp : tsupport ρ ⊆ {z : Fin (Module.finrank ℝ E) → ℝ | D.ζ i (D.pt l z) ≠ 0} ∩
      {z : Fin (Module.finrank ℝ E) → ℝ | Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => θ z * ρ z
      * (D.ζ i (D.pt l z))⁻¹
      * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z))))⁻¹
      * (g₀.inner (D.pt l z) (D.e l a (D.pt l z)) (D.e i c (D.pt l z))
        * g₀.inner (D.pt l z) (D.e l b (D.pt l z)) (D.e i d (D.pt l z)))) := by
  classical
  refine contDiff_iff_contDiffAt.mpr (fun z => ?_)
  by_cases hz : z ∈ tsupport ρ
  · -- the point lies in the support of `ρ`: the whole coefficient is smooth there
    have hzζ : D.ζ i (D.pt l z) ≠ 0 := (hsupp hz).1
    have hzint : Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
        ∈ interior ((extChartAt I (D.x₀ l)).target) := (hsupp hz).2
    have hp : D.pt l z ∈ (chartAt H (D.x₀ i)).source := by
      have h := (D.hζsupp i (D.pt l z) hzζ).1
      rwa [extChartAt_source] at h
    have hpt : ContMDiffAt (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ)) I
        (⊤ : ℕ∞) (D.pt l) z :=
      Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D l z hzint
    have hH : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
        (coeffM (I := I) (g₀ := g₀) D l i a b c d) (D.pt l z) :=
      coeffM_contMDiffAt (I := I) (g₀ := g₀) D l i a b c d hp hzζ
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => coeffM (I := I) (g₀ := g₀) D l i a b c d (D.pt l w)) z :=
      contMDiffAt_iff_contDiffAt.mp (hH.comp z hpt)
    have hmain : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => θ w * ρ w * coeffM (I := I) (g₀ := g₀) D l i a b c d (D.pt l w)) z :=
      (hθ.contDiffAt.mul hρ.contDiffAt).mul hcomp
    refine hmain.congr_of_eventuallyEq ?_
    have hcontζ : ContinuousAt (fun w => D.ζ i (D.pt l w)) z :=
      ((D.hζsm i).continuous.continuousAt).comp hpt.continuousAt
    filter_upwards [hcontζ.eventually_ne hzζ] with w hw
    have hsrc : D.pt l w ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i (D.pt l w) hw).1
    have hdens := dens_coord_eq_gmat (I := I) (g₀ := g₀) D i hsrc
    simp only [coeffM, densGram, hdens]
    ring
  · -- outside the support of `ρ` the function vanishes on a neighbourhood
    have hρ0 : ρ =ᶠ[nhds z] (fun _ : Fin (Module.finrank ℝ E) → ℝ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hz] with w hw
      by_contra h
      exact hw (subset_closure h)
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (by
      filter_upwards [hρ0] with w hw
      rw [hw]
      ring)

end Work.Diff.STE.B3.VarCoef
