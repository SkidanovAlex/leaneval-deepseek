import Mathlib
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior
import Submission.Work.Diff.STE.D.transMap_interior_contDiffAt
import Submission.Work.Diff.STE.D.dens_interior_contDiffAt
import Submission.Work.Diff.STE.B3.BPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `goodSet` is open and the cross-chart data is smooth — **without `[T2Space M]`**

`Submission/Work/Diff/STE/D/R_Rstar_expansion2.lean` proves `IsOpen goodSet`, the smoothness of
`tMapFun` on `goodSet` and the smoothness of `coeffFun` on `goodSet`, but only under the extra
instance `[T2Space M]` (carried as a section variable of that file).  None of the *ingredients*
need `M` to be Hausdorff: `pt` is smooth on the interior of the chart target
(`pt_contMDiffAt_of_mem_interior`, already stated without `[T2Space M]`), `flatToE` is affine,
`extChartAt` is continuous on its source (`continuousAt_extChartAt'`), `coord` composed with `pt`
is smooth (`transMap_interior_contDiffAt`), `dens` is smooth on the interior of the target
(`dens_interior_contDiffAt`) and the metric pairing of smooth fields is smooth
(`Work.EXT.ONF.pairing`).  This file repeats the three proofs verbatim in the `T2`-free setting,
so that the Layer-B3 chain can be assembled without assuming the manifold is Hausdorff.
-/

namespace Work.Diff.STE.B3

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

set_option linter.unusedSectionVars false

section Geometry

/-- **The flat `i`-coordinate of a point of the chart-`i` source is the chart-`i` image** —
without `[T2Space M]` (the copy in `R_Rstar_expansion2` carries that instance). -/
theorem noT2_flatToE_coord (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    {p : M} (_hp : p ∈ (extChartAt I (D.x₀ i)).source) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ i) (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
      = (extChartAt I (D.x₀ i)) p := by
  have harg : (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i))
      + ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p)
        - (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)))
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) p) := by abel
  simp only [Work.Diff.STE.flatToE, Work.Diff.STE.coord]
  rw [harg, LinearEquiv.symm_apply_apply]

/-- **`goodSet` is open**, without `[T2Space M]`. -/
theorem noT2_isOpen_goodSet
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  have hpt : ContinuousAt (D.pt j) z :=
    (Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz1).continuousAt
  have hflat : ContinuousAt (Work.Diff.STE.flatToE (I := I) (D.x₀ j)) z :=
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous.continuousAt
  have h1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
      interior ((extChartAt I (D.x₀ j)).target) ∈ 𝓝 z :=
    hflat.preimage_mem_nhds (isOpen_interior.mem_nhds hz1)
  have h2 : D.pt j ⁻¹' (extChartAt I (D.x₀ i)).source ∈ 𝓝 z :=
    hpt.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) (D.x₀ i)).mem_nhds hz2)
  have h3 : (fun w => (extChartAt I (D.x₀ i)) (D.pt j w)) ⁻¹'
      interior ((extChartAt I (D.x₀ i)).target) ∈ 𝓝 z :=
    ((continuousAt_extChartAt' (I := I) hz2).comp hpt).preimage_mem_nhds
      (isOpen_interior.mem_nhds hz3)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  intro w hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

end Geometry

section Smoothness

/-- **The transition map is `C^∞` at every point of `goodSet`**, without `[T2Space M]`. -/
theorem noT2_tMapFun_contDiffAt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z := by
  show ContDiffAt ℝ (⊤ : ℕ∞)
    (fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z
  exact Work.Diff.STE.D.transMap_interior_contDiffAt (I := I) D i j z hz.1 hz.2.1

/-- **`tMapFun` is `C^∞` on `goodSet`**, without `[T2Space M]`. -/
theorem noT2_tMapFun_contDiffOn
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :=
  fun _ hz => (noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hz).contDiffWithinAt

/-- `ζ i ∘ pt j` is `C^∞` at every point of `goodSet`, without `[T2Space M]`. -/
theorem noT2_contDiffAt_zeta_pt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  exact contMDiffAt_iff_contDiffAt.mp (((D.hζsm i).contMDiffAt).comp z hpt)

/-- The localised weight `ψ j` is `C^∞` at every point of `goodSet`, without `[T2Space M]`. -/
theorem noT2_contDiffAt_psi
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.psi j) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  have hζ : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ j (D.pt j w)) z :=
    contMDiffAt_iff_contDiffAt.mp (((D.hζsm j).contMDiffAt).comp z hpt)
  show ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.χ j w * D.ζ j (D.pt j w)) z
  simpa only [Pi.mul_apply] using (D.hχsm j).contDiffAt.mul hζ

/-- The metric pairing of two smooth fields, composed with `pt j`, is `C^∞` at a point of
`goodSet` — without `[T2Space M]`. -/
theorem noT2_contDiffAt_pairing_pt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) (k : ι₀)
    (c' d' : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e k c' (D.pt j w)) (D.e i d' (D.pt j w))) z := by
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  have hpair := Work.EXT.ONF.pairing g₀ (D.pt j z)
    ((D.hesm k c').contMDiffAt) ((D.hesm i d').contMDiffAt)
  exact contMDiffAt_iff_contDiffAt.mp (hpair.comp z hpt)

/-- **The coefficient is `C^∞` at every point of `goodSet`**, without `[T2Space M]`. -/
theorem noT2_coeffFun_contDiffAt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (c d : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) z := by
  have hpsi : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi j) z :=
    noT2_contDiffAt_psi (I := I) (M := M) D i j hz
  have hdj : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens j) z :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D j z hz.1
  have hdjpos : D.dens j z ≠ 0 :=
    (Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D j (interior_subset hz.1)).ne'
  have hsj : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Real.sqrt (D.dens j w)) z :=
    (Real.contDiffAt_sqrt hdjpos).comp z hdj
  have hzi : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z :=
    noT2_contDiffAt_zeta_pt (I := I) (M := M) D i j hz
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) z :=
    noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hz
  have hchi : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))) z :=
    (D.hχsm i).contDiffAt.comp z hT
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      = (extChartAt I (D.x₀ i)) (D.pt j z) :=
    noT2_flatToE_coord (I := I) (M := M) D i hz.2.1
  have hdi : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D i _ (by rw [hflat]; exact hz.2.2)
  have hdipos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
      (by rw [hflat]; exact interior_subset hz.2.2)
  have hsi : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.sqrt (D.dens i y))
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) :=
    (Real.contDiffAt_sqrt hdipos.ne').comp _ hdi
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
        (D.pt j w))))⁻¹) z := by
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
          (D.pt j w)))) z :=
      ContDiffAt.comp (x := z)
        (f := fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w)) hsi hT
    exact hcomp.inv (Real.sqrt_pos.mpr hdipos).ne'
  have hpair1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j a (D.pt j w)) (D.e i c (D.pt j w))) z :=
    noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j a c hz
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j b (D.pt j w)) (D.e i d (D.pt j w))) z :=
    noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j b d hz
  have hK : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => D.ζ i (D.pt j w) * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w))))⁻¹) z :=
    (hzi.mul hchi).mul hinv
  show ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) z
  exact (((hpsi.mul hsj).mul hK).mul hpair1).mul hpair2

/-- **`coeffFun` is `C^∞` on `goodSet`**, without `[T2Space M]`. -/
theorem noT2_coeffFun_contDiffOn
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :=
  fun _ hz => (noT2_coeffFun_contDiffAt (I := I) (M := M) D i j a b c d hz).contDiffWithinAt

end Smoothness

end

theorem goodSet_smooth_noT2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
    (∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)
        (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)) :=
  ⟨noT2_isOpen_goodSet (I := I) (M := M) D i j,
   noT2_tMapFun_contDiffOn (I := I) (M := M) D i j,
   fun a b c d => noT2_coeffFun_contDiffOn (I := I) (M := M) D i j a b c d⟩

end Work.Diff.STE.B3
