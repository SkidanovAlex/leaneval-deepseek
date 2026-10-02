import Mathlib
import Submission.Work.SphHomology.sphPiece_homeo
import Submission.Work.SphHomology.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# A product homeomorphism of the sphere piece over a trivialising set, respecting the projection

For a Euclidean real bundle `Z` over `B`, the piece `SphPiece Z i` of the unit sphere bundle lying
over a trivialising set `Z.baseSet i` is homeomorphic to `↥(Z.baseSet i) × S(F)`
(`Work.SphHomology.sphPiece_homeo`).  Here we strengthen that statement: the homeomorphism can be
chosen *fibre-wise*, i.e. it commutes with the projections: the image of `(u, v)` lies over `u`.

The homeomorphism we exhibit is the natural one: read the fibre coordinate of a point over
`baseSet i` in the trivialisation `Z.localTriv i`, and identify the unit sphere of the model fibre
with the norm-one locus.  The projection identity is exactly what turns "the sphere bundle over a
trivialising set is a product" into a statement in the slice over that set, which is the form used
downstream (e.g. when putting a charted-space structure on the piece and comparing it with the
product charted structure).

The proof of the projection identity is by direct computation: the composite of the three standard
homeomorphisms (the product-with-sphere bookkeeping, the trivialisation restricted to the
norm-one locus, and the two ways of nesting the subtypes) has the same underlying point as the
inverse of the trivialisation, so the claim reduces to `proj` of a point in the fibre of the
trivialisation, which is the definition of the trivialisation's inverse.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.Tubular.PuncturedDiscPair

theorem exists_homeo_sphPiece_proj {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (hZ : Work.Thom.IsEuclidean Z) (i : ι) :
    ∃ Φ : ↥(Z.baseSet i) × Work.SphHomology.ModelSph F ≃ₜ Work.SphHomology.SphPiece Z i,
      ∀ (u : ↥(Z.baseSet i)) (v : Work.SphHomology.ModelSph F),
        Z.proj (((Φ (u, v)) : Work.SphHomology.SphPiece Z i) : Z.TotalSpace) = (u : B) := by
  classical
  -- `baseSet i` is contained in the base set of the trivialisation `Z.localTriv i`
  -- (the two sets are in fact definitionally equal).
  have hs : Z.baseSet i ⊆ (Z.localTriv i).baseSet := fun x hx => by
    show x ∈ Z.baseSet i
    exact hx
  -- Reading a point of the total space over `baseSet i` in the trivialisation identifies the part of
  -- the sphere bundle over `baseSet i` with `↥(baseSet i) × {‖·‖ = 1}`.
  let h2 : {z : ↥(Z.proj ⁻¹' Z.baseSet i) // (z : Z.TotalSpace) ∈ Work.Thom.sphereSet Z} ≃ₜ
      {y : ↥(Z.baseSet i) × F // ‖y.2‖ = 1} :=
    ((Z.localTriv i).preimageHomeomorph hs).subtype (fun z => by
      rw [Bundle.Trivialization.preimageHomeomorph_apply]
      exact Work.Thom.mem_sphereSet_iff hZ i (z : Z.TotalSpace) z.2)
  -- The homeomorphism: the product with the sphere, read through the trivialisation, and with the
  -- two nestings of the subtypes swapped.
  let Φ : ↥(Z.baseSet i) × Work.SphHomology.ModelSph F ≃ₜ Work.SphHomology.SphPiece Z i :=
    (Work.SphHomology.prodModelSphHomeo (Z.baseSet i)).trans (h2.symm.trans
      (Work.SphHomology.subtypeSwap
        (fun p : Z.TotalSpace => p ∈ Work.Thom.sphereSet Z)
        (fun p : Z.TotalSpace => Z.proj p ∈ Z.baseSet i)).symm)
  -- The underlying point of `Φ (u, v)` is the inverse image of `(u, v)` under the trivialisation:
  -- every one of the three pieces is the identity on the point, up to the bookkeeping of the
  -- subtypes, so this holds by reflexivity.
  have key : ∀ (u : ↥(Z.baseSet i)) (v : Work.SphHomology.ModelSph F),
      (((Φ (u, v)) : Work.SphHomology.SphPiece Z i) : Z.TotalSpace) =
        (Z.localTriv i).toPartialEquiv.symm ((u : B), (v : F)) := fun u v => rfl
  refine ⟨Φ, fun u v => ?_⟩
  rw [key u v]
  -- the inverse of the trivialisation does not move the base point
  exact (Z.localTriv i).proj_symm_apply' (hs u.2)

end Work.Tubular.PuncturedDiscPair
