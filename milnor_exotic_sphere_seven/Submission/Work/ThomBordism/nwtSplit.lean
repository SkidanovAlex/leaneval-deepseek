import Mathlib
import Submission.Work.ThomBordism.nwtComplement
import Submission.Work.ThomBordism.PontryaginThom.SplittingData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The splitting `TV ⊕ ν ≅ ε^{8+k}` for the orthonormal normal bundle

`Work.ThomBordism.PontryaginThom.nonempty_bundleIso_splitting` assembles the splitting of the
trivial bundle along the frame of an immersion from a `ComplementData` and the frame data.  This
file applies it to the *orthonormal* complement data `orthComplementData E ND` of the normal bundle
and the frame `frame E.e i x` of the immersion `E`, using:

* `nwtKerComplP` — the kernel of the projection is the plane of the frame;
* `nwtComplI_complP` — the insertion composed with the projection is `orthInj` of the frame;
* `range_coeffMap_frame_agree` — the plane does not depend on the chart;
* `frame_A_compat`, `frame_Ainv_compat` — the frame is compatible with the tangent bundle.
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom
open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The splitting of the tangent bundle along the orthonormal normal bundle**:
`TV ⊕ ν ≅ ε^{8+k}` with `ν = (orthComplementData E ND).toRealBundle`. -/
theorem nonempty_bundleIso_tangent_sum_orthComplementData
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Nonempty (BundleIso
      ((Work.TangentClasses.tangentBundle (𝓡 8) V.pt).sum
        (orthComplementData E ND).toRealBundle)
      (RealBundle.trivial V.pt (Euc (8 + k)) Unit)) := by
  classical
  have hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 E.e := E.smooth.of_le (by simp)
  have hLI : ∀ (i : atlas (Euc 8) V.pt) (x : V.pt), x ∈ i.1.source →
      LinearIndependent ℝ (frame E.e i x) :=
    fun i x hx => frame_linearIndependent E.e hf E.injective_mfderiv i hx
  refine nonempty_bundleIso_splitting (Work.TangentClasses.tangentBundle (𝓡 8) V.pt)
    (orthComplementData E ND)
    (fun i x => frame E.e i x)
    (fun i x => LinearMap.toContinuousLinearMap (frameCoords (frame E.e i x)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact continuousOn_frame E.e hf i
  · intro i
    exact continuousOn_frameCoordsCLM (fun x => frame E.e i x) (i.1.source)
      (continuousOn_frame E.e hf i) (fun x hx => hLI i x hx)
  · intro j i x hj hi
    rw [show (orthComplementData E ND).P j x = complP E ND j x from rfl]
    rw [nwtKerComplP E ND j hj]
    exact range_coeffMap_frame_agree E.e hf (coverChart j) i
      (ND.baseSet_sub j.1 j.2 x hj) hi
  · intro i x _ v
    show frameCoords (frame E.e i x) (coeffMap (frame E.e i x) v) = v
    exact frameCoords_coeffMap (frame E.e i x) (hLI i x (by assumption)) v
  · intro i j x hi hj u
    change coeffMap (frame E.e i x) (frameCoords (frame E.e i x) u)
      = u - complI E ND j x (complP E ND j x u)
    rw [show coeffMap (frame E.e i x) (frameCoords (frame E.e i x) u)
        = orthProj (frame E.e i x) u from
      coeffMap_frameCoords (frame E.e i x) (hLI i x hi) u]
    rw [nwtComplI_complP E ND j hj u]
    rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply, sub_sub_cancel]
    exact congrArg (fun L => L u)
      (orthProj_eq_of_range_coeffMap (frame E.e i x) (frame E.e (coverChart j) x)
        (hLI i x hi) (hLI (coverChart j) x (ND.baseSet_sub j.1 j.2 x hj))
        (range_coeffMap_frame_agree E.e hf i (coverChart j) hi
          (ND.baseSet_sub j.1 j.2 x hj)))
  · intro i j x hi hj u
    change complI E ND i x (complP E ND i x u) = complI E ND j x (complP E ND j x u)
    rw [nwtComplI_complP E ND i hi u, nwtComplI_complP E ND j hj u]
    congr 1
    rw [orthInj, orthInj, orthProj_eq_of_range_coeffMap
      (frame E.e (coverChart i) x) (frame E.e (coverChart j) x)
      (hLI (coverChart i) x (ND.baseSet_sub i.1 i.2 x hi))
      (hLI (coverChart j) x (ND.baseSet_sub j.1 j.2 x hj))
      (range_coeffMap_frame_agree E.e hf (coverChart i) (coverChart j)
        (ND.baseSet_sub i.1 i.2 x hi) (ND.baseSet_sub j.1 j.2 x hj))]
  · intro i x hx v
    exact frame_A_compat E.e hf i hx v
  · intro i x hx u
    exact frame_Ainv_compat E.e hf E.injective_mfderiv i hx u

end

end Work.ThomBordism
