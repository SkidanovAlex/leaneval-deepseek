import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Transporting a real bundle along an equivalence of the fibres

The gluing model of `Work.TangentClasses` (`RealBundle B F ι = VectorBundleCore ℝ B F ι`) has the
fibre `F` as a parameter, and the chapter uses two conventions for the normal bundle of an
immersion:

* the **coordinate fibre** `Fin k → ℝ`, in which the complement bundle of a family of planes is
  constructed (`ComplementBundle.lean`) and in which the splitting `TV ⊕ ν ≅ ε^{8+k}` is proved
  (`Splitting.lean`);
* the **euclidean-space fibre** `Euc k = EuclideanSpace ℝ (Fin k)`, in which the sibling Grassmann
  chapter presents the tautological bundle
  `Grassmann.tautologicalBundle k m : RealBundle (OG k m) (Amb k) (ChartIdx k m)`.

The two are related by the canonical linear isometry `EuclideanSpace.equiv (Fin k) ℝ`, and this file
provides the transport of a bundle along *any* continuous linear equivalence `e : F ≃L[ℝ] F'` of the
fibres: `bundleMapEquiv Z e`, with the same cover, index map and base sets, and transition
functions `mapEquivCoordChange` conjugated by `e`:

`(bundleMapEquiv Z e).coordChange i j x = e ∘ Z.coordChange i j x ∘ e.symm`

(`bundleMapEquivCoordChange_apply`: `bundleMapEquivCoordChange Z e i j x v = e (Z.coordChange i j x (e.symm v))`).

Its API is definitional — `bundleMapEquiv_baseSet`, `bundleMapEquiv_indexAt`, `bundleMapEquiv_coordChange`,
`bundleMapEquiv_rank` — so a caller can transport a bundle, and every statement about it, without any
bookkeeping beyond rewriting along those equations.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.TangentClasses

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F F' : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι : Type*}

/-- **The transition function of a bundle conjugated by an equivalence of the fibres**:
`e ∘ Z.coordChange i j x ∘ e.symm`, a continuous linear map `F' → F'`. -/
def bundleMapEquivCoordChange (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (i j : ι) (x : B) : F' →L[ℝ] F' :=
  (e : F →L[ℝ] F').comp (((Z.coordChange i j x) : F →L[ℝ] F).comp (e.symm : F' →L[ℝ] F))

@[simp] theorem bundleMapEquivCoordChange_apply (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (i j : ι)
    (x : B) (v : F') :
    bundleMapEquivCoordChange Z e i j x v = e ((Z.coordChange i j x) (e.symm v)) := rfl

/-- **The transport of a real bundle along a continuous linear equivalence of the fibres**: the same
cover, index map and base sets, with the transition functions conjugated by `e`. -/
def bundleMapEquiv (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') : RealBundle B F' ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange := bundleMapEquivCoordChange Z e
  coordChange_self i x hx v := by
    rw [bundleMapEquivCoordChange_apply, Z.coordChange_self i x hx (e.symm v), e.apply_symm_apply]
  continuousOn_coordChange i j := by
    have h := Z.continuousOn_coordChange i j
    have hconst : ContinuousOn (fun _ : B => (e.symm : F' →L[ℝ] F))
        (Z.baseSet i ∩ Z.baseSet j) := continuousOn_const
    have h1 : ContinuousOn (fun x => ((Z.coordChange i j x) : F →L[ℝ] F).comp
        (e.symm : F' →L[ℝ] F)) (Z.baseSet i ∩ Z.baseSet j) := h.clm_comp hconst
    have hconst' : ContinuousOn (fun _ : B => (e : F →L[ℝ] F'))
        (Z.baseSet i ∩ Z.baseSet j) := continuousOn_const
    have h2 : ContinuousOn (fun x => (e : F →L[ℝ] F').comp
        (((Z.coordChange i j x) : F →L[ℝ] F).comp (e.symm : F' →L[ℝ] F)))
        (Z.baseSet i ∩ Z.baseSet j) := hconst'.clm_comp h1
    refine h2.congr (fun x _ => ?_)
    rw [bundleMapEquivCoordChange]
  coordChange_comp i j l x hx v := by
    rw [bundleMapEquivCoordChange_apply, bundleMapEquivCoordChange_apply, bundleMapEquivCoordChange_apply,
      e.symm_apply_apply, Z.coordChange_comp i j l x hx (e.symm v)]

@[simp] theorem bundleMapEquiv_baseSet (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (i : ι) :
    (bundleMapEquiv Z e).baseSet i = Z.baseSet i := rfl

@[simp] theorem bundleMapEquiv_indexAt (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (x : B) :
    (bundleMapEquiv Z e).indexAt x = Z.indexAt x := rfl

@[simp] theorem bundleMapEquiv_coordChange (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (i j : ι) (x : B) :
    (bundleMapEquiv Z e).coordChange i j x = bundleMapEquivCoordChange Z e i j x := rfl

/-- The transport does not change the rank (the fibre dimension is the dimension of `F'`). -/
theorem bundleMapEquiv_rank (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') :
    (bundleMapEquiv Z e).rank = Module.finrank ℝ F' := rfl

end

end Work.ThomBordism.PontryaginThom
