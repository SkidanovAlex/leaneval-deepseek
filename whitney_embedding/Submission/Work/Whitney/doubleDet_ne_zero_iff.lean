import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.LocalModel
import Submission.Work.Projection.mfderiv_chartAt_decomp

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- The range of a composite of continuous linear maps is the image of the range of the second
under the first: the continuous linear version of `LinearMap.range_comp`. -/
lemma range_comp_clm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A ∘L B).range = Submodule.map (A : F →ₗ[𝕜] G) B.range := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨B y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- **The range of the manifold derivative is the range of the derivative of the chart
representation.**  For a smooth `f : M → ℝ^{2n}` and a point `p`, the range of `mfderiv f p` equals
the range of the Fréchet derivative at the chart coordinate `(chartAt p) p` of the chart
representation `Work.Whitney.chartRepM f p`.  This is `Work.Projection.mfderiv_chartAt_decomp`
together with the fact that the derivative of a chart is surjective. -/
lemma range_mfderiv_eq_range_fderiv_chartRep {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (p : M) :
    (mfderiv (𝓡 n) (𝓡 (2 * n)) f p).range
      = (fderiv ℝ (chartRepM f p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)).range := by
  have : IsManifold (𝓡 n) 1 M := IsManifold.of_le (m := 1) (n := ∞) (by simp)
  have hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := mem_chart_source _ _
  rw [Work.Projection.mfderiv_chartAt_decomp f hf p p hp]
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) p
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
  have hB : B.range = ⊤ := (mdifferentiable_chart (I := 𝓡 n) p).range_mfderiv_eq_top hp
  change (A ∘L B).range = (fderiv ℝ (chartRepM f p) _).range
  rw [range_comp_clm, hB, Submodule.map_top]
  rfl

/-- The signed determinant of a double point vanishes exactly when the two tangent images are complementary, i.e. exactly when the double point is transverse.  (`Work.Whitney.doubleDet f p q u v` is defined in `Submission/Work/Whitney/DoublePoint.lean` as the determinant of the two-sheets map through the block identification `Work.Projection.pairEquiv n`, and `Work.Projection.mfderiv_chartAt_decomp` relates `mfderiv f p` to `fderiv ℝ (chartRepM f p) ⋯`.) -/
theorem doubleDet_ne_zero_iff {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (p q : M) :
    Work.Whitney.doubleDet f p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) ≠ 0 ↔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f q).range = ⊤ := by
  -- the two derivatives of the chart representations
  set Ap : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (chartRepM f p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) with hAp
  set Aq : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (chartRepM f q) ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) with hAq
  -- the "two sheets" map and the endomorphism whose determinant is `doubleDet`
  set L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := Ap.coprod Aq with hL
  set Φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ((Work.Projection.pairEquiv n).toLinearMap).comp L.toLinearMap with hΦ
  have hdet : Work.Whitney.doubleDet f p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)
      ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) = LinearMap.det Φ := rfl
  rw [hdet]
  -- a finite-dimensional endomorphism has nonzero determinant exactly when it is injective
  have hdetiff : (LinearMap.det Φ ≠ 0) ↔ Function.Injective ⇑Φ := by
    rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  rw [hdetiff]
  -- `Φ` is `pairEquiv ∘ L`, so it is injective exactly when `L` is
  have hinjiff : Function.Injective ⇑Φ ↔ Function.Injective ⇑(L.toLinearMap) := by
    constructor
    · intro h x y hxy
      apply h
      simp only [hΦ, LinearMap.comp_apply, hxy]
    · intro h x y hxy
      apply h
      have := congrArg (⇑((Work.Projection.pairEquiv n).symm)) hxy
      simpa only [hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        using this
  -- the range of `L` is the supremum of the two tangent images
  have hLrange : L.toLinearMap.range = Ap.range ⊔ Aq.range := by
    rw [hL, ContinuousLinearMap.coe_coprod, LinearMap.range_coprod]
  -- `L` is a map between spaces of the same dimension `2n`, so injective = surjective
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  have hiff : Function.Injective ⇑Φ ↔ Ap.range ⊔ Aq.range = ⊤ := by
    rw [hinjiff, ← hLrange, LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
  -- replace the ranges of the chart derivatives by the ranges of the manifold derivatives
  have hfp : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p).range = Ap.range := by
    rw [hAp]; exact range_mfderiv_eq_range_fderiv_chartRep f hf p
  have hfq : (mfderiv (𝓡 n) (𝓡 (2 * n)) f q).range = Aq.range := by
    rw [hAq]; exact range_mfderiv_eq_range_fderiv_chartRep f hf q
  rw [hfp, hfq]
  exact hiff

end Work.Whitney
