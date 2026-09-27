import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.cofactor_restrict_surjective
import Submission.Work.Drive.cofactorVec_mem_ker

/-!
# A common direction of the two chains with a prescribed non-zero coordinate

Let `M` be a smooth `4`-manifold, `D : ℝ² → M`, `N : ℝ³ → M` smooth, `y ∈ ℝ⁵` a point of the chart
region at `p` with `D (sqPart y) = N (cbPart y)`, and suppose the charted difference map
`chartDiff p D N` is a submersion at `y` (`hsurj`) whose restriction to the coordinate hyperplane
`{v | v i = 0}` is still onto (`hface`).

This file proves that there are then `σ : ℝ²`, `τ : ℝ³` with
`mfderiv D (sqPart y) σ = mfderiv N (cbPart y) τ` — a **common direction** of the two derivatives,
i.e. a direction in which the two chains are tangent — whose block vector `mkPart σ τ` has non-zero
`i`-th coordinate, so that the corresponding direction is transverse to the `i`-th face.

## Proof

The charted difference map factors through the linear map `(σ, τ) ↦ mfderiv D σ − mfderiv N τ`:

* `chartDiff_fderiv_mkPart` gives, at `y`,
  `fderiv ℝ (chartDiff p D N) y (mkPart σ τ) =
     T₁ (mfderiv D σ) − T₂ (mfderiv N τ)`, where `T₁`, `T₂` are the two change-of-coordinates maps;
* since `D (sqPart y) = N (cbPart y)`, the maps `T₁` and `T₂` coincide (`tangentCoordChange_congr`)
  and are invertible (`tangentCoordChange_injective`), so the kernel direction of the charted
  difference map is *exactly* the image under `mkPart` of the common directions.

The `i`-th component of the kernel direction is computed by the cofactor vector:
`cofactorVec (fderiv ℝ (chartDiff p D N) y)` spans the kernel (`cofactorVec_mem_ker`) and its `i`-th
component is non-zero precisely when the restriction of the derivative to the `i`-th face is onto
(`surjective_domRestrict_iff_cofactorVec_ne_zero`, applied to `hsurj` and `hface`).  Splitting that
kernel direction into its two blocks with `mkPart (sqPart ·) (cbPart ·) = ·` produces the required
`σ` and `τ`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

/-- The two block projections jointly invert `mkPart`: the blocks of `x` reassemble to `x`. -/
private theorem mkPart_sqPart_cbPart_aux (x : Amb 4) : mkPart (sqPart x) (cbPart x) = x := by
  ext k
  revert k
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun k => mkPart (sqPart x) (cbPart x) k = x k) ?_ ?_
  · intro i
    show mkPart (sqPart x) (cbPart x) (sqIdx i) = x (sqIdx i)
    rw [mkPart_sqIdx, ← sqPartCLM_eq_sqPart x, sqPartCLM_apply]
  · intro j
    show mkPart (sqPart x) (cbPart x) (cbIdx j) = x (cbIdx j)
    rw [mkPart_cbIdx, ← cbPartCLM_eq_cbPart x, cbPartCLM_apply]

theorem exists_sigma_tau_of_faceSurjective {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    {y : Work.Drive.Amb 4} (hy : y ∈ Work.Drive.chartRegion p D N)
    (heq : D (Work.Drive.sqPart y) = N (Work.Drive.cbPart y))
    {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (Work.Drive.chartDiff p D N) y))
    (hface : Function.Surjective (fun v : {v : Work.Drive.Amb 4 // v i = 0} =>
      fderiv ℝ (Work.Drive.chartDiff p D N) y v.1)) :
    ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D (Work.Drive.sqPart y) σ
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) N (Work.Drive.cbPart y) τ ∧
      Work.Drive.mkPart σ τ i ≠ 0 := by
  -- The derivative of the charted difference map at `y`.
  set Φ : Work.Drive.Amb 4 →L[ℝ] Work.Drive.Tgt 4 :=
    fderiv ℝ (Work.Drive.chartDiff p D N) y with hΦ
  -- A kernel direction: the cofactor vector.
  set v : Work.Drive.Amb 4 := Work.Drive.cofactorVec Φ with hv
  have hker : Φ v = 0 := Work.Drive.cofactorVec_mem_ker Φ
  -- Its `i`-th coordinate is non-zero by the face hypothesis.
  have hne : v i ≠ 0 :=
    (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero Φ hsurj i).mp hface
  have hv' : fderiv ℝ (Work.Drive.chartDiff p D N) y v = 0 := by
    rw [← hΦ]; exact hker
  refine ⟨Work.Drive.sqPart v, Work.Drive.cbPart v, ?_, ?_⟩
  · -- The blocks of the kernel direction give a common direction of the two derivatives.
    have hB := Work.Drive.chartDiff_fderiv_mkPart p D N hD hN hy
      (Work.Drive.sqPart v) (Work.Drive.cbPart v)
    have h0 : fderiv ℝ (Work.Drive.chartDiff p D N) y
        (Work.Drive.mkPart (Work.Drive.sqPart v) (Work.Drive.cbPart v)) = 0 := by
      rw [mkPart_sqPart_cbPart_aux v]; exact hv'
    have hEq : (tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p (D (Work.Drive.sqPart y)))
          ((mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart y)) (Work.Drive.sqPart v))
        = (tangentCoordChange (𝓡 4) (N (Work.Drive.cbPart y)) p (N (Work.Drive.cbPart y)))
          ((mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart y)) (Work.Drive.cbPart v)) := by
      rw [hB] at h0
      exact sub_eq_zero.mp h0
    -- The two change-of-coordinates maps agree because the base points do.
    have hT12 : tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p (D (Work.Drive.sqPart y))
        = tangentCoordChange (𝓡 4) (N (Work.Drive.cbPart y)) p (N (Work.Drive.cbPart y)) :=
      Work.Drive.tangentCoordChange_congr heq
    -- ... and are injective, so they can be cancelled.
    have hinj : Function.Injective
        (tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p (D (Work.Drive.sqPart y))) := by
      refine Work.Drive.tangentCoordChange_injective ?_
      refine ⟨mem_extChartAt_source (I := 𝓡 4) _, ?_⟩
      rw [extChartAt_source]
      exact hy.1
    refine hinj ?_
    rw [← hT12] at hEq
    exact hEq
  · -- The `i`-th coordinate is the one of the kernel direction.
    rw [mkPart_sqPart_cbPart_aux v]
    exact hne

end Work.Drive
