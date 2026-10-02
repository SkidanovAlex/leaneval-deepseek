import Mathlib
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.exists_nowhereZero_normalSection
import Submission.Work.PTGeometric.exists_localData_at_boundaryZero
import Submission.Work.PTGeometric.contMDiff_normalProjCLM

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The derivative of the normal coordinate is the orthogonal projection onto the normal space

The tubular neighbourhood theorem gives a *tube chart* `C` of an embedding
`E : V ↪ ℝ^{8+k}` of a closed smooth `8`-manifold (`Work.Tubular.TubeChart`), and with it the
**normal coordinate** `normalCoord E C y = (C.inv y).1.2` (TUBULAR).  Its zero locus is exactly the
image of `V`, and its derivative at a point `E.e x` of the embedded manifold has image exactly the
normal space `ν_x = T_x^⊥` (`Work.Tubular.TubeTransversalityOfChart`).

This file proves the sharper statement that is needed for the *ambient* description of the collapse:
the derivative is not merely *some* map with kernel `T_x` and image `ν_x`, it is precisely the
**orthogonal** projection

  `Work.PTGeometric.tubeNormalProj E C (E.e x)`
  `  = (ν_x).subtypeL ∘ (ν_x).orthogonalProjectionOnto`

onto the normal space at the foot of the point.

The two inputs are the two halves of the projection statement, both already on disk in the TUBULAR
chapter (`Work.Tubular.normalProj := fderiv ℝ (tubeNormal C) (E.e x)`, which is *definitionally*
`fderiv ℝ (normalCoord E C) (E.e x)`):

* `Work.Tubular.range_normalProj`: the range of `normalProj C x` is `ν_x`;
* `Work.Tubular.ker_normalProj`: the kernel of `normalProj C x` is the tangent space `T_x`.

Together with the fact that `normalProj C x` fixes `ν_x` pointwise
(`Work.Tubular.normalProj_apply_of_mem_normal`), these say that `normalProj C x` is the projection
of `ℝ^{8+k}` onto `ν_x` *along* `T_x`: for every vector `q` one has `q = (q - Dq) + Dq` with
`Dq ∈ ν_x` and `q - Dq ∈ T_x = ν_xᗮ`.  A decomposition of `q` as a sum of an element of `ν_x` and an
element of `ν_xᗮ` is unique, so `Dq` *is* the orthogonal projection of `q` onto `ν_x`.

## Main result

* `Work.PTGeometric.fderiv_normalCoord_eq_tubeNormalProj`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Topology InnerProduct
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- The ambient projection of the tube chart, as the orthogonal projection onto the normal space. -/
theorem tubeNormalProj_eq_starProjection {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) :
    Work.PTGeometric.tubeNormalProj E C y
      = (Work.Tubular.normalSpace E (Work.PTGeometric.tubeFoot E C y)).starProjection := rfl

/-- **The derivative of the normal coordinate at a point of the embedded manifold is the orthogonal
projection onto the normal space there.**

This is the ambient form of the transversality of the collapse: `d(normalCoord)_{e x}` decomposes
`ℝ^{8+k} = T_x ⊕ ν_x` orthogonally. -/
theorem fderiv_normalCoord_eq_tubeNormalProj {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    fderiv ℝ (Work.Tubular.normalCoord E C) (E.e x)
      = Work.PTGeometric.tubeNormalProj E C (E.e x) := by
  have hfoot : Work.PTGeometric.tubeFoot E C (E.e x) = x :=
    Work.PTGeometric.tubeFoot_e E C x
  rw [tubeNormalProj_eq_starProjection]
  -- `normalProj` is *definitionally* the derivative of the normal coordinate
  have hL : fderiv ℝ (Work.Tubular.normalCoord E C) (E.e x) = Work.Tubular.normalProj C x := rfl
  rw [hL]
  refine ContinuousLinearMap.ext fun q => ?_
  -- the projection along `T_x` onto `ν_x`, read off from `range` and `ker`
  have hmx : Work.Tubular.normalProj C x q ∈ Work.Tubular.normalSpace E x := by
    rw [Work.Tubular.range_normalProj C x]
    exact ⟨q, rfl⟩
  have hm : Work.Tubular.normalProj C x q
      ∈ Work.Tubular.normalSpace E (Work.PTGeometric.tubeFoot E C (E.e x)) := by
    simpa [hfoot] using hmx
  have hDq : Work.Tubular.normalProj C x (Work.Tubular.normalProj C x q)
      = Work.Tubular.normalProj C x q :=
    Work.Tubular.normalProj_apply_of_mem_normal C hmx
  have hzero : Work.Tubular.normalProj C x (q - Work.Tubular.normalProj C x q) = 0 := by
    rw [map_sub, hDq, sub_self]
  have hsub : q - Work.Tubular.normalProj C x q ∈ Work.Tubular.tangentSpace E x := by
    rw [Work.Tubular.ker_normalProj C x]
    exact LinearMap.mem_ker.mpr hzero
  -- `q = Dq + (q - Dq)` with `Dq ∈ ν_x` and `q - Dq ∈ T_x = ν_xᗮ`, so `Dq` is the orthogonal
  -- projection of `q`
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := Work.Tubular.normalSpace E (Work.PTGeometric.tubeFoot E C (E.e x)))
    (u := q) (v := Work.Tubular.normalProj C x q) hm ?_).symm
  intro w hw
  have hw' : w ∈ Work.Tubular.normalSpace E x := by simpa [hfoot] using hw
  exact (Submodule.mem_orthogonal (Work.Tubular.tangentSpace E x) w).mp
    (by simpa [Work.Tubular.normalSpace] using hw') _ hsub

end

end Work.PTGeometric
