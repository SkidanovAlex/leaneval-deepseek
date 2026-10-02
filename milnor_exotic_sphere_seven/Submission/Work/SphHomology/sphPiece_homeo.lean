import Mathlib
import Submission.Work.SphHomology.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-!
# The sphere bundle over a trivialising set is a product

For a Euclidean real bundle `Z` over `B`, the piece `SphPiece Z i` of the unit sphere bundle
lying over a trivialising set `Z.baseSet i` is homeomorphic to the product
`↥(Z.baseSet i) × S(F)` of that set with the unit sphere of the model fibre.  This is what makes
the sphere bundle locally a product, and is the input for Mayer–Vietoris / Leray–Hirsch style
arguments bounding the (co)homology of the sphere bundle.

The homeomorphism is the composite

`↥(Z.baseSet i) × S(F) → ↥(Z.baseSet i) × F →  (trivialisation)  Z |_{baseSet i}`

restricted to `‖·‖ = 1`.  The two auxiliary homeomorphisms below are the bookkeeping for the
restrictions: `prodModelSphHomeo` identifies a product-with-sphere with the norm-one part of the
product, and `subtypeSwap` swaps the two ways of nesting subtypes.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.SphHomology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ι : Type*}

/-- The two ways of nesting subtypes of a topological space — `{u : {a // p a} // q u}` and
`{v : {a // q a} // p v}` — are homeomorphic (the identity on the underlying points). -/
def subtypeSwap {α : Type*} [TopologicalSpace α] (p q : α → Prop) :
    {u : {a // p a} // q (u : α)} ≃ₜ {v : {a // q a} // p (v : α)} where
  toFun u := ⟨⟨(u : α), u.2⟩, u.1.2⟩
  invFun v := ⟨⟨(v : α), v.2⟩, v.1.2⟩
  left_inv u := by ext <;> rfl
  right_inv v := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The product `↥s × S(F)` of a subspace with the unit sphere of the model fibre is
homeomorphic to the part of `↥s × F` cut out by the unit-norm condition `‖·‖ = 1`. -/
def prodModelSphHomeo (s : Set B) :
    ↥s × ModelSph F ≃ₜ {y : ↥s × F // ‖y.2‖ = 1} where
  toFun p := ⟨(p.1, (p.2 : F)), by
    simpa [dist_eq_norm] using Metric.mem_sphere.mp p.2.2⟩
  invFun y := (y.1.1, ⟨y.1.2, Metric.mem_sphere.mpr (by simpa [dist_eq_norm] using y.2)⟩)
  left_inv p := by ext <;> rfl
  right_inv y := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The part of the sphere bundle over a trivialising set is a product.**  Reading a point of
the fibre in the trivialisation `Z.localTriv i` identifies `SphPiece Z i` with
`↥(Z.baseSet i) × S(F)`: the composite of the trivialisation `↥(Z.baseSet i) × F ≃ₜ Z|₁`
with the identification of the unit sphere of `F` with the norm-one locus. -/
theorem sphPiece_homeo {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) (i : ι) :
    Nonempty (↥(Z.baseSet i) × Work.SphHomology.ModelSph F ≃ₜ Work.SphHomology.SphPiece Z i) := by
  -- the trivialisation identifies the part of the total space over `baseSet i` with
  -- `baseSet i × F`, and restricted to the unit sphere this reads as `baseSet i × {‖·‖ = 1}`
  have h2 : {z : ↥(Z.proj ⁻¹' Z.baseSet i) // (z : Z.TotalSpace) ∈ Work.Thom.sphereSet Z} ≃ₜ
      {y : ↥(Z.baseSet i) × F // ‖y.2‖ = 1} :=
    ((Z.localTriv i).preimageHomeomorph (s := Z.baseSet i)
      (fun x hx => by show x ∈ Z.baseSet i; exact hx)).subtype (fun z => by
      rw [Bundle.Trivialization.preimageHomeomorph_apply]
      exact Work.Thom.mem_sphereSet_iff hZ i (z : Z.TotalSpace) z.2)
  refine ⟨(prodModelSphHomeo (Z.baseSet i)).trans (h2.symm.trans (subtypeSwap
    (fun p : Z.TotalSpace => p ∈ Work.Thom.sphereSet Z)
    (fun p : Z.TotalSpace => Z.proj p ∈ Z.baseSet i)).symm)⟩

end

end Work.SphHomology
