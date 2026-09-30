import Mathlib
import Submission.Work.Cohomology.SubdivisionHomotopyData
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.toChain_boundaryLC

/-!
# The boundary of the homotopy image of a simplex

This file proves `Work.Cohomology.tElem_boundary`, the identity

`∂ (T σ) = Sd σ - σ - T (∂ σ)`

at the level of a single singular simplex `σ`: the `(m+2)`-chain `tElem X (m+1) σ` is obtained by
pushing the primitive `cLC (m+1)` (with `∂ (cLC (m+1)) = sdLC (m+1) - iotaLC (m+1) - Σᵢ (-1)ⁱ
embedLCᵢ (cLC m)`) forward along `σ`, and its boundary is therefore the push-forward of the
right-hand side of `cLC_boundary`.

The two ingredients are

* `toChain_boundaryLC` — the affine chain map `toChain` intertwines `boundaryLC` with the singular
  differential, so that `∂ (toChain (cLC (m+1))) = toChain (boundaryLC (cLC (m+1)))`;
* `chainComplexMap_comm_apply` — the push-forward along `σ` is a chain map, so it commutes with
  `∂` as well.

After these two identifications the statement is linearity of the push-forward together with the
identification of the pushed-forward pieces: the subdivision `sdLC` gives `sdElem`, the identity
simplex `iotaLC` gives the generator `gen`, and the face embeddings `embedLC` give the homotopy
images of the faces `δᵢ σ` (this last one uses `toChain_embedLC` together with the functoriality
of `chainComplexMap` and `faceMap_comp_sdMap`).

## Main results

* `tElem_face` — the push-forward of the face term is `tElem X m (δᵢ σ)`;
* `tElem_boundary_step1` — `∂ (tElem X (m+1) σ)` is the push-forward of `cLCarg m`;
* `tElem_boundary` — the statement of the file.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

/-- The push-forward along `σ` of the face term `toChain (embedLC i (cLC m))` is the homotopy
image `tElem X m (δᵢ σ)` of the `i`-th face of `σ`. -/
lemma tElem_face (X : TopCat) (m : ℕ) (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) (i : Fin (m + 2)) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (m + 1) σ)) (ModuleCat.of ℤ ℤ)).f
        (m + 1)).hom
      (toChain (m + 1) (m + 1) ((embedLC m (m + 1) i) (cLC m))) =
    tElem X m ((TopCat.toSSet.obj X).δ i σ) := by
  rw [toChain_embedLC, chainComplexMap_toSSet_map_comp, faceMap_comp_sdMap]
  rfl

/-- **Step 1**: the differential of `tElem X (m+1) σ` is the push-forward along `σ` of the affine
chain `toChain (cLCarg m)`.  This combines the fact that the push-forward is a chain map with the
computation `∂ (cLC (m+1)) = cLCarg m` of the boundary of the primitive. -/
lemma tElem_boundary_step1 (X : TopCat) (m : ℕ) (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) :
    ((singularChains ℤ X).d (m + 2) (m + 1)).hom (tElem X (m + 1) σ) =
      ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (m + 1) σ)) (ModuleCat.of ℤ ℤ)).f
          (m + 1)).hom
        (toChain (m + 1) (m + 1) (cLCarg m)) := by
  have h1 : ((singularChains ℤ X).d (m + 2) (m + 1)).hom (tElem X (m + 1) σ) =
      ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap (m + 1) σ)) (ModuleCat.of ℤ ℤ)).f
          (m + 1)).hom
        (((TopCat.toSSet.obj (Delta (m + 1))).chainComplex (ModuleCat.of ℤ ℤ)).d (m + 2) (m + 1)
          (toChain (m + 1) (m + 2) (cLC (m + 1)))) := by
    rw [tElem]
    exact chainComplexMap_comm_apply _ (m + 1) _
  rw [h1]
  congr 1
  rw [← toChain_boundaryLC (m + 1) (m + 1) (cLC (m + 1)), cLC_boundary]

open CategoryTheory AlgebraicTopology Simplicial Limits in
open scoped Simplicial in
/-- **The boundary of the homotopy image of a simplex.** For a singular `(m+1)`-simplex `σ`, the
boundary of the `(m+2)`-chain `tElem X (m+1) σ = σ_*(cLC (m+1))` is the subdivided simplex minus
the simplex itself minus the signed sum of the homotopy images of its faces.  This is the identity
`∂(T σ) = Sd σ - σ - T(∂σ)` at the level of a single simplex. -/
theorem tElem_boundary (X : TopCat) (m : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋m + 1⦌) :
    ((singularChains ℤ X).d (m + 2) (m + 1)).hom (tElem X (m + 1) σ) =
      sdElem X (m + 1) σ - gen X (m + 1) σ
        - ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • tElem X m ((TopCat.toSSet.obj X).δ i σ) := by
  rw [tElem_boundary_step1]
  rw [show cLCarg m = sdLC (m + 1) - iotaLC (m + 1)
      - ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC m (m + 1) i (cLC m) from rfl]
  simp only [map_sub, map_sum, map_zsmul]
  rw [sdElem_eq, push_id_simplex]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [tElem_face]

end

end Work.Cohomology
