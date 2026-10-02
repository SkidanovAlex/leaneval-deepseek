import Submission.Work.ThomBordism.PontryaginThom.OrthogonalRange
import Submission.Work.ThomBordism.PontryaginThom.FramesRange
import Submission.Work.TangentClasses.Tangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The frame of an immersion is compatible with the tangent bundle

The splitting `TV ⊕ ν ≅ ε^{8+k}` of the normal bundle of an immersion
(`Splitting.lean`, `nonempty_bundleIso_splitting`) is built from the frames `A i x = frame f i x` of
`im (d f_x)` in the charts `i` of `V`, and needs two compatibility facts relating the frame in an
arbitrary chart to the frame in the *preferred* chart at `x` through the transition function of the
tangent bundle:

* `frame_A_compat` — `coeffMap (A i x) v = coeffMap (A (indexAt x) x) (tCoord Zt i x v)`;
* `frame_Ainv_compat` — `frameCoords (A i x) u = tCoordInv Zt i x (frameCoords (A (indexAt x) x) u)`.

Both reduce to the chain rule.  `coeffMap_frame_compat` is the pointwise statement — the frame in
the chart `i`, expressed in the frame of the chart `j`, is the frame in the chart `j` with the
coordinates transported by the derivative of the chart change — and `tCoord_tangentBundle_eq`
identifies the transition function of the tangent bundle with that derivative (for the self model
`𝓡 8`, where `·.extend (𝓡 8) = ·` and `range (𝓡 8) = univ`).

The inverse-compatibility `frame_Ainv_compat` then follows from `frame_A_compat` and the inverse
transition identity `tCoord_comp_tCoordInv_apply`, together with the chart-independence of the
orthogonal projection (`orthProj_eq_of_range_coeffMap`, `OrthogonalRange.lean`).
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann Work.TangentClasses

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The frame of an immersion in two charts -/

/-- **The frame of an immersion in the coordinates of another chart**: applying the derivative of
the chart change `j ∘ i.symm` to the coordinates of a linear combination of the frame of `i` gives
the coordinates of the same vector in the frame of `j`.  This is the chain rule
(`fderiv_chartRep_eq`), in the form in which the compatibility `A_compat` of the splitting consumes
it. -/
theorem coeffMap_frame_compat (f : V.pt → Euc (8 + k)) (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (i j : atlas (Euc 8) V.pt) {x : V.pt} (hi : x ∈ i.1.source) (hj : x ∈ j.1.source)
    (v : Fin 8 → ℝ) :
    coeffMap (frame f i x) v
      = coeffMap (frame f j x)
          (eucToFun 8 ((fderiv ℝ (fun y => j.1 (i.1.symm y)) (i.1 x)) (funToEuc 8 v))) := by
  have hL : (∑ l, v l • frame f i x l)
      = (fderiv ℝ (chartRep f i) (i.1 x)) (funToEuc 8 v) := by
    rw [show (∑ l, v l • frame f i x l)
        = ∑ l, (fderiv ℝ (chartRep f i) (i.1 x)) (v l • EuclideanSpace.single l 1) from
      Finset.sum_congr rfl fun l _ => by rw [map_smul]; rfl,
      ← map_sum, sum_smul_single_eq_funToEuc]
  set Z : Euc 8 := (fderiv ℝ (fun y => j.1 (i.1.symm y)) (i.1 x)) (funToEuc 8 v) with hZ
  have hY : (fderiv ℝ (chartRep f j) (j.1 x)) Z
      = ∑ m, (eucToFun 8 Z) m • frame f j x m := by
    conv_lhs => rw [show Z = ∑ m, (eucToFun 8 Z) m • EuclideanSpace.single m 1 from by
      rw [sum_smul_single_eq_funToEuc, funToEuc_eucToFun]]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul]; rfl
  have hkey : (∑ l, v l • frame f i x l) = ∑ m, (eucToFun 8 Z) m • frame f j x m := by
    rw [hL, fderiv_chartRep_eq f hf i j hi hj, ContinuousLinearMap.comp_apply]
    exact hY
  rw [coeffMap_eq_sum, coeffMap_eq_sum, hZ]
  exact congrArg (eucToFun (8 + k)) hkey

/-! ## The transition function of the tangent bundle -/

/-- For the self model `𝓡 8`, the extended chart of an atlas element is the atlas element itself. -/
theorem extend_self (i : atlas (Euc 8) V.pt) :
    ⇑(i.1.extend (𝓡 8)) = ⇑i.1 := by
  rw [OpenPartialHomeomorph.extend_coe]
  funext y
  simp

/-- The inverse of the extended chart of an atlas element is the inverse of the atlas element. -/
theorem extend_symm_self (i : atlas (Euc 8) V.pt) :
    ⇑(i.1.extend (𝓡 8)).symm = ⇑i.1.symm := by
  rw [OpenPartialHomeomorph.extend_coe_symm]
  funext y
  simp

/-- **The transition function of the tangent bundle is the derivative of the chart change**: in the
self model, `tCoord` of the tangent bundle between an atlas element and the preferred chart at `x`
is the derivative of `j ∘ i.symm` at `i x`. -/
theorem tCoord_tangentBundle_eq (i : atlas (Euc 8) V.pt) (x : V.pt) (v : Fin 8 → ℝ) :
    tCoord (tangentBundle (𝓡 8) V.pt) i x v
      = eucToFun 8 ((fderiv ℝ (fun y => (achart (Euc 8) x).1 (i.1.symm y)) (i.1 x))
          (funToEuc 8 v)) := by
  have hcoord : (tangentBundle (𝓡 8) V.pt).coordChange i ((tangentBundle (𝓡 8) V.pt).indexAt x) x
      = fderivWithin ℝ ((achart (Euc 8) x).1.extend (𝓡 8) ∘ (i.1.extend (𝓡 8)).symm)
          (Set.range (𝓡 8)) ((i.1.extend (𝓡 8)) x) := by
    rw [show (tangentBundle (𝓡 8) V.pt).indexAt x = achart (Euc 8) x from rfl]
    rfl
  rw [tCoord_apply, hcoord,
    show Set.range (𝓡 8) = Set.univ from ModelWithCorners.range_eq_univ (𝓡 8), fderivWithin_univ,
    extend_self (achart (Euc 8) x), extend_symm_self i, extend_self i]
  rfl

/-! ## The inverse transition identity of the coordinate functions -/

/-- **The two coordinate functions of a bundle are inverse to each other**: the `tCoord` of
`Splitting.lean` composed with its `tCoordInv` is the identity (the mirror of
`tCoordInv_comp_tCoord`). -/
theorem tCoord_comp_tCoordInv_apply {B : Type*} [TopologicalSpace B] {ιT : Type*}
    (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B) (hx : x ∈ Zt.baseSet i) (v : Fin 8 → ℝ) :
    tCoord Zt i x (tCoordInv Zt i x v) = v := by
  show eucToFun 8 (Zt.coordChange i (Zt.indexAt x) x
      (funToEuc 8 (eucToFun 8 (Zt.coordChange (Zt.indexAt x) i x (funToEuc 8 v))))) = v
  rw [funToEuc_eucToFun,
    Zt.coordChange_comp (Zt.indexAt x) i (Zt.indexAt x) x
      ⟨⟨Zt.mem_baseSet_at x, hx⟩, Zt.mem_baseSet_at x⟩,
    Zt.coordChange_self (Zt.indexAt x) x (Zt.mem_baseSet_at x), eucToFun_funToEuc]

/-! ## The compatibility of the frame with the tangent bundle -/

/-- **`A_compat` of the splitting**: the frame of the immersion in the chart `i`, in the coordinates
of the preferred chart at `x`, is the frame of the preferred chart transported by the transition
function of the tangent bundle. -/
theorem frame_A_compat (f : V.pt → Euc (8 + k)) (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) (v : Fin 8 → ℝ) :
    coeffMap (frame f i x) v
      = coeffMap (frame f (achart (Euc 8) x) x)
          (tCoord (tangentBundle (𝓡 8) V.pt) i x v) := by
  rw [tCoord_tangentBundle_eq i x v]
  exact coeffMap_frame_compat f hf i (achart (Euc 8) x) hx (mem_chart_source (Euc 8) x) v

/-- **`Ainv_compat` of the splitting**: the frame coordinates in the chart `i` are the frame
coordinates in the preferred chart at `x`, transported by the inverse transition function. -/
theorem frame_Ainv_compat (f : V.pt → Euc (8 + k)) (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) (u : Fin (8 + k) → ℝ) :
    frameCoords (frame f i x) u
      = tCoordInv (tangentBundle (𝓡 8) V.pt) i x
          (frameCoords (frame f (achart (Euc 8) x) x) u) := by
  have hLIi : LinearIndependent ℝ (frame f i x) := frame_linearIndependent f hf hinj i hx
  have hLIa : LinearIndependent ℝ (frame f (achart (Euc 8) x) x) :=
    frame_linearIndependent f hf hinj (achart (Euc 8) x) (mem_chart_source (Euc 8) x)
  apply coeffMap_injective_of_linearIndependent (frame f i x) hLIi
  rw [coeffMap_frameCoords (frame f i x) hLIi u]
  rw [frame_A_compat f hf i hx
    (tCoordInv (tangentBundle (𝓡 8) V.pt) i x
      (frameCoords (frame f (achart (Euc 8) x) x) u))]
  rw [tCoord_comp_tCoordInv_apply (tangentBundle (𝓡 8) V.pt) i x hx]
  rw [coeffMap_frameCoords (frame f (achart (Euc 8) x) x) hLIa u]
  exact congrArg (fun L => L u)
    (orthProj_eq_of_range_coeffMap (frame f i x) (frame f (achart (Euc 8) x) x) hLIi hLIa
      (range_coeffMap_frame_agree f hf i (achart (Euc 8) x) hx (mem_chart_source (Euc 8) x)))

end

end Work.ThomBordism.PontryaginThom
