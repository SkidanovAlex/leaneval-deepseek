import Mathlib
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Definitions for the isomorphism-invariance of the tautological quotient

This module only contains definitions used by `Work.Thom.tautQuotientCore_iso` and by the lemmas
delegated for it.  For a bundle isomorphism `f : BundleIso Z Z'` of two complex bundles of rank
`m + 1` over `B`:

* `Work.Thom.BundleIso.clm f b` is the fibrewise linear map of `f` at `b`, as a *continuous*
  linear map `ℂ^{m+1} →L[ℂ] ℂ^{m+1}` (possible because the fibre is finite dimensional);
* `Work.Thom.gaugeFwd f` / `Work.Thom.gaugeBwd f` are the induced fibrewise maps of the
  tautological quotients, `Q_Z → φ^*(Q_{Z'})` and back, where
  `φ = Work.Thom.punctHomeo Z Z' f`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}

/-- The fibre vector of the total space point of a punctured total space, typed as the model
fibre `ℂ^{m+1}` (rather than as a `Fiber`). -/
def fibre {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    (p : ↥(zeroComplement (realification Z))) : EuclideanSpace ℂ (Fin (m+1)) :=
  (p : (realification Z).TotalSpace).2

/-- The `i`-chart coordinate of the tautological section at `p`. -/
def zCoord {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    (i : ι) (p : ↥(zeroComplement (realification Z))) : EuclideanSpace ℂ (Fin (m+1)) :=
  (Z.localTriv i (p : (realification Z).TotalSpace)).2

/-- The base point of the point `Φ p` of the punctured total space of `Z'`. -/
def phiBase {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) : B :=
  ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
    (realification Z').TotalSpace).proj

/-- The `i'`-chart coordinate of the tautological section at `Φ p`. -/
def phiCoord {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (f : BundleIso Z Z') (i' : ι') (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin (m+1)) :=
  (Z'.localTriv i' ((punctHomeo Z Z' f p : ↥(zeroComplement (realification Z'))) :
    (realification Z').TotalSpace)).2

/-- **The fibrewise map of a bundle isomorphism, as a continuous linear map.**  The fibre is
`ℂ^{m+1}`, finite dimensional over the complete field `ℂ`, so a linear map is automatically
continuous. -/
def BundleIso.clm {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'} (f : BundleIso Z Z') (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)) :=
  let g : EuclideanSpace ℂ (Fin (m+1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m+1)) := f.hom b
  LinearMap.toContinuousLinearMap (𝕜 := ℂ) g

theorem BundleIso.clm_apply {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'} (f : BundleIso Z Z') (b : B)
    (v : EuclideanSpace ℂ (Fin (m+1))) : f.clm b v = f.hom b v := by
  show (f.clm b) v = (f.hom b) v
  rw [BundleIso.clm]
  rfl

/-- **The forward fibrewise map of the tautological quotient** induced by a bundle isomorphism
`f : Z ≅ Z'`.  In the preferred charts at `p` and `φ p` it sends the class of the tautological
section of `Z` at `p` to the class of the tautological section of `Z'` at `φ p`. -/
def gaugeFwd {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (quoCLM (tqCoord Z' (punctHomeo Z Z' f p))
      (f.clm ((p : (realification Z).TotalSpace).1) (fibre p))).comp
    ((f.clm ((p : (realification Z).TotalSpace).1)).comp (fillCLM (tqCoord Z p)))

/-- **The backward fibrewise map** of the tautological quotients, the inverse of
`Work.Thom.gaugeFwd`. -/
def gaugeBwd {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι'}
    (f : BundleIso Z Z') (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (quoCLM (tqCoord Z p) (fibre p)).comp
    ((f.symm.clm ((p : (realification Z).TotalSpace).1)).comp
      (fillCLM (tqCoord Z' (punctHomeo Z Z' f p))))

end

end Work.Thom
