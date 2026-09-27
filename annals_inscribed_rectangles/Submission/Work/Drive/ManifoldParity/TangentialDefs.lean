import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.InterSetDefs

/-!
# Definitions for the tangential field on the intersection set

The gauge-corrected local difference maps used in `Work.Drive.ManifoldParity.exists_tangential_field`.

* `triv p` is the tangent-bundle trivialization at `p`;
* `symmLField D p x` is its `symmL`, i.e. the inverse chart derivative `B_p` as a function of
  `D (sqPart x)`, typed as a continuous linear map `ℝ⁴ →L ℝ⁴` (via the definitional equality
  `TangentSpace (𝓡 4) y = ℝ⁴`);
* `gcorr D N p x = B_p (chartDiff p D N x)` is the local piece corrected so that its derivative at a
  meeting point is the chart-independent difference of the two manifold derivatives.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology Bundle
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The tangent-bundle trivialization at `p`. -/
abbrev triv (p : M) : Bundle.Trivialization (EuclideanSpace ℝ (Fin 4))
    (Bundle.TotalSpace.proj : Bundle.TotalSpace (EuclideanSpace ℝ (Fin 4)) (TangentSpace (𝓡 4)) → M) :=
  trivializationAt (EuclideanSpace ℝ (Fin 4)) (TangentSpace (𝓡 4)) p

/-- `B_p`: the inverse chart derivative of the tangent-bundle trivialization at `p`, as a function of
the base point `D (sqPart x)`. -/
def symmLField (D : EuclideanSpace ℝ (Fin 2) → M) (p : M) :
    Amb 4 → (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :=
  fun x => show EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) from
    (triv p).symmL ℝ (D (sqPart x))

/-- The gauge-corrected local difference map: the charted difference `chartDiff p D N` corrected by
the inverse chart derivative `B_p`, so that its derivative at a meeting point is the chart-independent
difference of the two manifold derivatives. -/
def gcorr (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) (p : M) :
    Amb 4 → Tgt 4 :=
  fun x => symmLField D p x ((chartDiff p D N) x)

/-- `mfderiv D (sqPart x)`, retyped as a continuous linear map into `Tgt 4 = ℝ⁴` (through the
definitional equality `TangentSpace (𝓡 4) y = ℝ⁴`). -/
def mdD (D : EuclideanSpace ℝ (Fin 2) → M) (x : Amb 4) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] Tgt 4 :=
  show EuclideanSpace ℝ (Fin 2) →L[ℝ] Tgt 4 from mfderiv (𝓡 2) (𝓡 4) D (sqPart x)

/-- `mfderiv N (cbPart x)`, retyped as a continuous linear map into `Tgt 4 = ℝ⁴`. -/
def mdN (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] Tgt 4 :=
  show EuclideanSpace ℝ (Fin 3) →L[ℝ] Tgt 4 from mfderiv (𝓡 3) (𝓡 4) N (cbPart x)

/-- `Lfun D N x` is the *chart independent* difference of the two manifold derivatives: it sends
`v : ℝ⁵` to `mfderiv D (sqPart x) (sqPartCLM v) - mfderiv N (cbPart x) (cbPartCLM v)`.  The tangency
condition of `exists_tangential_field` is `V x ∈ ker (Lfun D N x)`. -/
def Lfun (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (x : Amb 4) : Amb 4 →L[ℝ] Tgt 4 :=
  (mdD D x).comp sqPartCLM - (mdN N x).comp cbPartCLM

theorem LfunA_apply (D : EuclideanSpace ℝ (Fin 2) → M) (x : Amb 4)
    (v : Amb 4) :
    mdD D x (sqPartCLM v) = mfderiv (𝓡 2) (𝓡 4) D (sqPart x) (sqPartCLM v) := rfl

theorem mfderivD_apply (D : EuclideanSpace ℝ (Fin 2) → M) (x : Amb 4)
    (σ : EuclideanSpace ℝ (Fin 2)) :
    mdD D x σ = mfderiv (𝓡 2) (𝓡 4) D (sqPart x) σ := rfl

theorem mfderivN_apply (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4)
    (τ : EuclideanSpace ℝ (Fin 3)) :
    mdN N x τ = mfderiv (𝓡 3) (𝓡 4) N (cbPart x) τ := rfl

theorem Lfun_apply (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (x v : Amb 4) :
    Lfun D N x v = (show Tgt 4 from mfderiv (𝓡 2) (𝓡 4) D (sqPart x) (sqPartCLM v)) -
      (show Tgt 4 from mfderiv (𝓡 3) (𝓡 4) N (cbPart x) (cbPartCLM v)) := rfl

theorem Lfun_mkPart (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4) (σ : EuclideanSpace ℝ (Fin 2))
    (τ : EuclideanSpace ℝ (Fin 3)) :
    Lfun D N x (mkPart σ τ) = mdD D x σ - mdN N x τ := by
  rw [Lfun, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, sqPartCLM_mkPart, cbPartCLM_mkPart]

end

end Work.Drive
