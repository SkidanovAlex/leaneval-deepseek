import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk
import Submission.Work.ORLocInd.FKSKernel.Kurosh.edgeRel_general
import Submission.Work.ORLocInd.FKSKernel.Kurosh.EdgeLink
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_inv

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

/-!
# Auxiliary lemmas for the case-1 merge of the shortening step

The Γ-computation of `merge_case1` needs two bookkeeping steps before it becomes pure group
algebra:

* `gEltHom_eq_of_index_eq` moves a vertex-group letter between two *equal* vertex orbits
  (the subgroup membership proof is transported along the equality of orbits);
* `stepGam_orbitEReverse_index` is the linking relator `TreeDatum.linkGamma` of `BSWalk` with
  the two indices `srcE (orbitEReverse E)` and `tgtE (orbitEReverse E)` rewritten to `tgtE E`
  and `srcE E` by `srcE_orbitEReverse` / `tgtE_orbitEReverse`.
-/

section Helpers

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- **Transporting a vertex-group letter along an equality of vertex orbits.**  If `A = B` then
the image in `Γ` of `g ∈ vgroup A` is the image of the corresponding element of `vgroup B`. -/
theorem gEltHom_eq_of_index_eq {d : TreeDatum G V} (D : d.PresData)
    
    {A B : Work.ORBassSerre.orbitV G V} (h : A = B) (g : ↥(d.vgroup A)) :
    d.gEltHom D A g = d.gEltHom D B ⟨(g : G), h ▸ g.2⟩ := by
  subst h
  exact congrArg _ (Subtype.ext rfl)

/-- **The stable letter of the reversed orbit, with indices normalised.**  The linking identity of
`TreeDatum.linkGamma`, with `srcE (orbitEReverse E)` rewritten to `tgtE E` and
`tgtE (orbitEReverse E)` rewritten to `srcE E`. -/
theorem stepGam_orbitEReverse_index {d : TreeDatum G V} (D : d.PresData)
    
    (E : Work.ORBassSerre.orbitE G V) :
    TreeDatum.stepGam D (Work.ORBassSerre.orbitEReverse E) true =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E)
          ⟨(d.linkK E : G), srcE_orbitEReverse (G := G) (V := V) E ▸ (d.linkK E).2⟩ *
        (TreeDatum.stepGam D E true)⁻¹ *
      d.gEltHom D (Work.ORBassSerre.Action.srcE E)
          ⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ := by
  rw [TreeDatum.linkGamma D E,
    show d.gEltHom D (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) (d.linkK E) =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E) _ from
      gEltHom_eq_of_index_eq D (srcE_orbitEReverse (G := G) (V := V) E) (d.linkK E),
    show d.gEltHom D (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) (d.linkH E) =
      d.gEltHom D (Work.ORBassSerre.Action.srcE E) _ from
      gEltHom_eq_of_index_eq D (tgtE_orbitEReverse (G := G) (V := V) E) (d.linkH E)]

end Helpers

/-- **The Γ-computation merging a backtrack, case 1** (`stepB k = true`, `stepB (k+1) = true`, so the
second step runs along the reversed edge orbit `orbitEReverse E` in the forward direction).

This is a piece of the shortening step of the walk proof of the injectivity of
`d.Φ : d.Gamma D →* G`.  In this case the three vertex-group letters `u`, `v`, `w` (living in
`d.vgroup (srcE E)`, `d.vgroup (tgtE E)`, `d.vgroup (srcE E)`) and the two stable letters
`stepGam D E true`, `stepGam D (orbitEReverse E) true` collapse to the single vertex-group letter
whose underlying element of `G` is `u * (eGroupToSrc E c) * (linkH E) * w`, where `c ∈ d.eGroup E`
is an edge-group element with `eGroupToTgt E c = v * linkK E`.

The proof uses `TreeDatum.linkGamma` (in `BSWalk.lean`) to rewrite `stepGam D (orbitEReverse E) true`
as `gEltHom D (srcE (orbitEReverse E)) (linkK E) * (stepGam D E true)⁻¹ *
gEltHom D (tgtE (orbitEReverse E)) (linkH E)`, then
`Work.ORLocInd.FKSKernel.Kurosh.srcE_orbitEReverse` / `tgtE_orbitEReverse` to identify the two
indices with `tgtE E` and `srcE E`, the edge relation of `edgeRel_general`
(`stepGam D E true * gEltHom D (tgtE E) (eGroupToTgt E c) * (stepGam D E true)⁻¹ =
gEltHom D (srcE E) (eGroupToSrc E c)`, valid for tree and non-tree edge orbits alike), and finally
`map_mul` (`gEltHom` is a monoid homomorphism) plus `Subtype.ext` to multiply the vertex-group
letters at the common index `srcE E`. -/
lemma merge_case1 {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (u v w : G)
    (hu : u ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (hv : v ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (hw : w ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (c : ↥(d.eGroup E)) (hc : (d.eGroupToTgt E c : G) = v * (d.linkK E : G)) :
    d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨u, hu⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D E true *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨v, hv⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D
          (Work.ORBassSerre.orbitEReverse E) true *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.srcE E)
        ⟨u * (d.eGroupToSrc E c : G) * (d.linkH E : G) * w, by
          refine mul_mem (mul_mem (mul_mem hu (d.eGroupToSrc E c).2) ?_) hw
          rw [← Work.ORLocInd.FKSKernel.Kurosh.tgtE_orbitEReverse]
          exact (d.linkH E).2⟩ := by
  rw [stepGam_orbitEReverse_index D E]
  let u' : d.Gamma D := d.gEltHom D (srcE E) ⟨u, hu⟩
  let v' : d.Gamma D := d.gEltHom D (tgtE E) ⟨v, hv⟩
  let w' : d.Gamma D := d.gEltHom D (srcE E) ⟨w, hw⟩
  let t : d.Gamma D := TreeDatum.stepGam D E true
  let κ : d.Gamma D :=
    d.gEltHom D (tgtE E) ⟨(d.linkK E : G), srcE_orbitEReverse (G := G) (V := V) E ▸ (d.linkK E).2⟩
  let η : d.Gamma D :=
    d.gEltHom D (srcE E) ⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩
  change u' * t * v' * (κ * t⁻¹ * η) * w' = _
  -- the two vertex-group letters adjacent to the stable letters
  have hVK : v' * κ = d.gEltHom D (tgtE E) (d.eGroupToTgt E c) := by
    change d.gEltHom D (tgtE E) ⟨v, hv⟩ *
        d.gEltHom D (tgtE E)
          ⟨(d.linkK E : G), srcE_orbitEReverse (G := G) (V := V) E ▸ (d.linkK E).2⟩ =
      d.gEltHom D (tgtE E) (d.eGroupToTgt E c)
    rw [← map_mul]
    exact congrArg (d.gEltHom D (tgtE E)) (Subtype.ext hc.symm)
  have hHW : η * w' = d.gEltHom D (srcE E)
      (⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ * ⟨w, hw⟩) := by
    change d.gEltHom D (srcE E)
          ⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ *
        d.gEltHom D (srcE E) ⟨w, hw⟩ =
      d.gEltHom D (srcE E)
        (⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ * ⟨w, hw⟩)
    rw [← map_mul]
  -- the edge relation, in conjugation form
  have hT : t * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) * t⁻¹ =
      d.gEltHom D (srcE E) (d.eGroupToSrc E c) := by
    change TreeDatum.stepGam D E true * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) *
        (TreeDatum.stepGam D E true)⁻¹ = d.gEltHom D (srcE E) (d.eGroupToSrc E c)
    by_cases htree : d.IsTreeEdge E
    · rw [TreeDatum.stepGam, dif_pos htree, one_mul, inv_one, mul_one]
      exact ((edgeRel_general d D E c).1 htree).symm
    · have ht := (edgeRel_general d D E c).2 htree
      have hstep : TreeDatum.stepGam D E true = PresentedGroup.of (Sum.inr ⟨E, htree⟩) := by
        simp only [TreeDatum.stepGam, dif_neg htree, ↓reduceIte]
      rw [hstep, ← ht]
      group
  -- pure group algebra
  rw [show u' * t * v' * (κ * t⁻¹ * η) * w' = (u' * t) * (v' * κ) * t⁻¹ * (η * w') from by
      group,
    hVK, hHW]
  rw [show u' * t * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) * t⁻¹ *
        d.gEltHom D (srcE E)
          (⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ * ⟨w, hw⟩)
      = u' * (t * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) * t⁻¹) *
        d.gEltHom D (srcE E)
          (⟨(d.linkH E : G), tgtE_orbitEReverse (G := G) (V := V) E ▸ (d.linkH E).2⟩ * ⟨w, hw⟩)
      from by group,
    hT, ← map_mul, ← map_mul]
  exact congrArg (d.gEltHom D (srcE E)) (Subtype.ext (by
    show u * (d.eGroupToSrc E c : G) * ((d.linkH E : G) * w) =
      u * (d.eGroupToSrc E c : G) * (d.linkH E : G) * w
    group))

end Work.ORLocInd.FKSKernel.Kurosh
