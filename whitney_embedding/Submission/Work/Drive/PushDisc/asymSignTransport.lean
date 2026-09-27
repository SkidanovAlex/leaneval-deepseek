import Submission.Work.Drive.PushDisc.asymSignDefs
import Submission.Work.Drive.Whitney.splitEuclideanSpace

/-!
# `Work.Drive.PushDisc.asymSignTransport`: the transport step of the sign derivation

`Work.Whitney.pairDet` computes the crossing sign as the determinant of an endomorphism of
`E^n × E^n` (with `n = k + 1`) obtained by pairing the two charts' jets through
`Work.Projection.pairEquiv`.  When the two jets are those of the *model* charts, they factor through
the same linear map `T = fderiv ℝ Θ (f p)` (the `pairEquiv`-side), and the determinant splits as

    det (pairEquiv ∘ T ∘ (A coprod B)) = det (pairEquiv ∘ T ∘ pairZ'⁻¹) * det (pairZ' ∘ (A coprod B))

where `pairZ'` is the pairing of the model space `Mdl k = ℝ × ℝ × E^k × E^k` with the two blocks of
`k + 1` coordinates that `pairEquiv` splits into.  The second factor is computed by
`Work.Drive.PushDisc.det_pairZ_inc_coprod_graph` (it equals `yx`), and the first factor is the same
for both crossings up to the *constant* `det (pairEquiv ∘ T ∘ pairZ'⁻¹)`, whose two values have the
same sign by `Work.Drive.PushDisc.det_fderiv_mul_pos`.
-/

namespace Work.Drive.PushDisc

/-- The chosen splitting `ℝ × E^k ≃ E^{k+1}` (`Work.Drive.Whitney.splitEuclideanSpace`). -/
noncomputable def splitE (k : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (Work.Drive.Whitney.splitEuclideanSpace k).choose.toLinearEquiv

/-- The pairing of the model space with the two blocks of `k + 1` coordinates that `pairEquiv`
splits into: `(x, y, u, v) ↦ ((x,u), (y,v))` with `ℝ × E^k` read as `E^{k+1}`. -/
noncomputable def pairZ' (k : ℕ) : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ]
    (EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin (k + 1))) :=
  (pairZ k).trans ((splitE k).prodCongr (splitE k))

/-- **The transport step.**  Factoring the composite through the pairing `pairZ'`. -/
theorem det_pairEquiv_transport {k : ℕ}
    (T : Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (A B : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k) :
    LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
        (T.comp (A.coprod B))) =
      LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
          (T.comp (pairZ' k).symm.toLinearMap)) *
        LinearMap.det ((pairZ' k).toLinearMap.comp (A.coprod B)) := by
  have hcomp : T.comp (A.coprod B) =
      (T.comp (pairZ' k).symm.toLinearMap).comp
        ((pairZ' k).toLinearMap.comp (A.coprod B)) := by
    rw [LinearMap.comp_assoc]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hcomp, ← LinearMap.comp_assoc, LinearMap.det_comp]

end Work.Drive.PushDisc
