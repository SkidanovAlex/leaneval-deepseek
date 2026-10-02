import Mathlib
import Submission.Work.PTGeometric.OrientationWiring
import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.PTGeometric.Lvl.Manifold
import Submission.Work.ThomBordism.CofAtlas.newTransition_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem levelSet_positiveAtlas_of_coframing
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (hMdet : ∀ (x y : M),
      x ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M →
      y ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M →
      ∀ z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).target ∩
          (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm ⁻¹'
            (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y).source,
        z 0 > 0 →
        (0 : ℝ) < LinearMap.det
          ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
            (extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y)
              ((extChartAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) x).symm w)) z)
            : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin ((8 + k) + 1))))
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPgr : ∀ x, P x ∈ Work.PTGeometric.Gr n k)
    (v : M → EuclideanSpace ℝ (Fin n))
    (hvsm : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ENat) : WithTop ENat) v)
    (hPv : ∀ x, P x (v x) = v x)
    (W : Set M) (hWcl : IsClosed W) (hW : W = {x : M | v x = 0})
    (hlink : ∀ x ∈ W, Set.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) v x) = {z | P x z = z})
    (L : Work.PTGeometric.LocalLevelData k M W)
    (hcof : ∃ (m : ℕ) (U : Fin m → Set M)
        (ℓ : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
        (e : Fin m → M → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      (∀ j, IsOpen (U j)) ∧ (∀ x ∈ W, ∃ j, x ∈ U j) ∧
      (∀ j y, y ∈ U j → ∀ c : EuclideanSpace ℝ (Fin k), ℓ j (e j y c) = c ∧ P y (e j y c) = e j y c) ∧
      (∀ j y, y ∈ U j → Function.Injective (e j y)) ∧
      (∀ j j' y, y ∈ U j → y ∈ U j' →
        0 < LinearMap.det ((ℓ j').comp (e j y)
          : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))))
    : ∃ (I : ChartedSpace (EuclideanHalfSpace 9) ↥W), letI := I;
        ((modelWithCornersEuclideanHalfSpace 9).boundary ↥W =
          {x : ↥W | (x : M) ∈
            (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M}) ∧
        ∃ (_hm : IsManifold (modelWithCornersEuclideanHalfSpace 9)
            ((⊤ : ENat) : WithTop ENat) ↥W), letI := _hm;
          (letI : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 ↥W :=
            IsManifold.of_le (n := ((⊤ : ENat) : WithTop ENat))
              (I := modelWithCornersEuclideanHalfSpace 9) (by simp);
           Work.PTGeometric.HasPositiveAtlas (k := k) W) := by
  obtain ⟨m, U, ℓ, e, hUopen, hUcov, hℓe, heinj, hpos⟩ := hcof
  let D : CofAtlas.Cof k n M :=
    { hMdet := hMdet, P := P, hPgr := hPgr, v := v, hvsm := hvsm, hPv := hPv,
      W := W, hWcl := hWcl, hW := hW, hlink := hlink, L := L,
      m := m, U := U, ℓ := ℓ, e := e, hUopen := hUopen, hUcov := hUcov,
      hℓe := hℓe, heinj := heinj, hpos := hpos }
  refine ⟨CofAtlas.newChartedSpace D, ?_, ⟨CofAtlas.newIsManifold D, ?_⟩⟩
  · exact CofAtlas.newBoundary D
  · exact CofAtlas.newTransition_det_pos D

end Work.ThomBordism
