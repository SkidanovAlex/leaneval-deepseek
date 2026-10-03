import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk
import Submission.Work.ORLocInd.FKSKernel.Kurosh.edgeRel_general
import Submission.Work.ORLocInd.FKSKernel.Kurosh.EdgeLink
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_inv

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- **Reindexing a vertex-group letter along an equality of vertex orbits.**  The element of `Gamma`
attached to a vertex-group element depends only on the orbit and on the underlying element of `G`:
if two vertex-group elements lie in the vertex groups of equal orbits and have the same underlying
element of `G`, then they define the same element of `Gamma`. -/
theorem gEltHom_eq_of_eq_orbit {d : TreeDatum G V}
    
    (D : d.PresData) {A B : Work.ORBassSerre.orbitV G V} (h : A = B)
    (g : ↥(d.vgroup A)) (g' : ↥(d.vgroup B)) (hg : (g : G) = (g' : G)) :
    d.gEltHom D A g = d.gEltHom D B g' := by
  subst h
  exact congrArg (d.gEltHom D A) (Subtype.ext hg)

/-- The stable letter of a step in the backwards direction is the inverse of the stable letter of the
step in the forwards direction. -/
theorem stepGam_false_eq_inv {d : TreeDatum G V}
    
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) :
    TreeDatum.stepGam D E false = (TreeDatum.stepGam D E true)⁻¹ := by
  simpa using (TreeDatum.stepGam_not D E true)

/-- **The edge relation of the Bass--Serre presentation in the form `t⁻¹ ĝ(c) t = ǧ(c)`.**  The
inverse of the stable letter of an edge orbit conjugates the source inclusion of the edge group into
the target inclusion.  For a tree edge orbit the stable letter is `1` and this is the identification
of the two inclusions, for a non-tree edge orbit it is the conjugation relation. -/
theorem stepGam_conj_srcE {d : TreeDatum G V}
    
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (c : ↥(d.eGroup E)) :
    (TreeDatum.stepGam D E true)⁻¹ * d.gEltHom D (srcE E) (d.eGroupToSrc E c) *
      TreeDatum.stepGam D E true = d.gEltHom D (tgtE E) (d.eGroupToTgt E c) := by
  have h : TreeDatum.stepGam D E true * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) *
      (TreeDatum.stepGam D E true)⁻¹ = d.gEltHom D (srcE E) (d.eGroupToSrc E c) := by
    by_cases htree : d.IsTreeEdge E
    · have hs : TreeDatum.stepGam D E true = 1 := by rw [TreeDatum.stepGam, dif_pos htree]
      rw [hs, one_mul, inv_one, mul_one]
      exact ((edgeRel_general d D E c).1 htree).symm
    · have ht := (edgeRel_general d D E c).2 htree
      have hstep : TreeDatum.stepGam D E true = PresentedGroup.of (Sum.inr ⟨E, htree⟩) := by
        simp only [TreeDatum.stepGam, dif_neg htree, ↓reduceIte]
      rw [hstep, ← ht]
      group
  rw [← h]
  group

/-- **The Γ-computation merging a backtrack, case 4** (`stepB k = false`, `stepB (k+1) = false`; the
first step runs along `E` backwards and the second along the reversed edge orbit `orbitEReverse E`
backwards).

This is a piece of the shortening step of the walk proof of the injectivity of
`d.Φ : d.Gamma D →* G`.  In this case the three vertex-group letters `u`, `v`, `w` (living in
`d.vgroup (tgtE E)`, `d.vgroup (srcE E)`, `d.vgroup (tgtE E)`) and the two stable letters
`stepGam D E false`, `stepGam D (orbitEReverse E) false` collapse to the single vertex-group letter
whose underlying element of `G` is `u * (eGroupToTgt E c) * (linkK E)⁻¹ * w`, where `c ∈ d.eGroup E`
is an edge-group element with `eGroupToSrc E c = v * (linkH E)⁻¹`.

The proof uses `TreeDatum.linkGamma` (in `BSWalk.lean`) to rewrite
`stepGam D (orbitEReverse E) true = gEltHom D (srcE (orbitEReverse E)) (linkK E) *
(stepGam D E true)⁻¹ * gEltHom D (tgtE (orbitEReverse E)) (linkH E)`, takes its inverse (so that
`stepGam D (orbitEReverse E) false = (stepGam D (orbitEReverse E) true)⁻¹`), and
`Work.ORLocInd.FKSKernel.Kurosh.srcE_orbitEReverse` / `tgtE_orbitEReverse` to identify the indices
with `tgtE E` and `srcE E`.  Then the hypothesis `hc` identifies `gEltHom D (srcE E) ⟨v, hv⟩ *
gEltHom D (srcE E) ⟨(linkH E : G)⁻¹, ·⟩` with `gEltHom D (srcE E) (eGroupToSrc E c)` (use
`Subtype.ext`), the edge relation of `edgeRel_general` gives
`(stepGam D E true)⁻¹ * gEltHom D (srcE E) (eGroupToSrc E c) * stepGam D E true =
gEltHom D (tgtE E) (eGroupToTgt E c)`, and `map_mul` multiplies everything at the common index
`tgtE E`. -/
lemma merge_case4 {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (u v w : G)
    (hu : u ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (hv : v ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (hw : w ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (c : ↥(d.eGroup E)) (hc : (d.eGroupToSrc E c : G) = v * (d.linkH E : G)⁻¹) :
    d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨u, hu⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D E false *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨v, hv⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D
          (Work.ORBassSerre.orbitEReverse E) false *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E)
        ⟨u * (d.eGroupToTgt E c : G) * (d.linkK E : G)⁻¹ * w, by
          have hlk : (d.linkK E : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E) := by
            rw [← congrArg d.vgroup (Work.ORLocInd.FKSKernel.Kurosh.srcE_orbitEReverse
              (G := G) (V := V) E)]
            exact (d.linkK E).2
          exact mul_mem (mul_mem (mul_mem hu (d.eGroupToTgt E c).2) (inv_mem hlk)) hw⟩ := by
  classical
  -- The link elements `linkK E` and `linkH E` lie in the vertex groups of `tgtE E` and `srcE E`.
  have hK : (d.linkK E : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E) := by
    rw [← congrArg d.vgroup (Work.ORLocInd.FKSKernel.Kurosh.srcE_orbitEReverse
      (G := G) (V := V) E)]
    exact (d.linkK E).2
  have hH : (d.linkH E : G) ∈ d.vgroup (Work.ORBassSerre.Action.srcE E) := by
    rw [← congrArg d.vgroup (Work.ORLocInd.FKSKernel.Kurosh.tgtE_orbitEReverse
      (G := G) (V := V) E)]
    exact (d.linkH E).2
  -- Reindex the two letters of the linking identity to the orbits `tgtE E` and `srcE E`.
  have hA : d.gEltHom D (srcE (Work.ORBassSerre.orbitEReverse E)) (d.linkK E) =
      d.gEltHom D (tgtE E) ⟨(d.linkK E : G), hK⟩ :=
    gEltHom_eq_of_eq_orbit D (srcE_orbitEReverse (G := G) (V := V) E) (d.linkK E)
      ⟨(d.linkK E : G), hK⟩ rfl
  have hB : d.gEltHom D (tgtE (Work.ORBassSerre.orbitEReverse E)) (d.linkH E) =
      d.gEltHom D (srcE E) ⟨(d.linkH E : G), hH⟩ :=
    gEltHom_eq_of_eq_orbit D (tgtE_orbitEReverse (G := G) (V := V) E) (d.linkH E)
      ⟨(d.linkH E : G), hH⟩ rfl
  -- The second stable letter, expanded via the linking relation.
  have hτf : TreeDatum.stepGam D (Work.ORBassSerre.orbitEReverse E) false =
      (d.gEltHom D (srcE E) ⟨(d.linkH E : G), hH⟩)⁻¹ * TreeDatum.stepGam D E true *
        (d.gEltHom D (tgtE E) ⟨(d.linkK E : G), hK⟩)⁻¹ := by
    rw [stepGam_false_eq_inv D (E := Work.ORBassSerre.orbitEReverse E),
      TreeDatum.linkGamma (d := d) D E, hA, hB]
    group
  -- The hypothesis `hc` identifies the letter `v` with `eGroupToSrc E c` followed by `linkH E`.
  have hBv : d.gEltHom D (srcE E) ⟨v, hv⟩ *
      (d.gEltHom D (srcE E) ⟨(d.linkH E : G), hH⟩)⁻¹ =
      d.gEltHom D (srcE E) (d.eGroupToSrc E c) := by
    rw [← map_inv, ← map_mul]
    exact congrArg (d.gEltHom D (srcE E)) (Subtype.ext hc.symm)
  -- The edge relation conjugated by the stable letter of `E`.
  have hconj : (TreeDatum.stepGam D E true)⁻¹ * d.gEltHom D (srcE E) (d.eGroupToSrc E c) *
      TreeDatum.stepGam D E true = d.gEltHom D (tgtE E) (d.eGroupToTgt E c) :=
    stepGam_conj_srcE D E c
  -- Reassociate the word so that the two pairs above become consecutive factors.
  have key : d.gEltHom D (tgtE E) ⟨u, hu⟩ * (TreeDatum.stepGam D E true)⁻¹ *
        d.gEltHom D (srcE E) ⟨v, hv⟩ *
        ((d.gEltHom D (srcE E) ⟨(d.linkH E : G), hH⟩)⁻¹ * TreeDatum.stepGam D E true *
          (d.gEltHom D (tgtE E) ⟨(d.linkK E : G), hK⟩)⁻¹) *
        d.gEltHom D (tgtE E) ⟨w, hw⟩
      = d.gEltHom D (tgtE E) ⟨u, hu⟩ *
        ((TreeDatum.stepGam D E true)⁻¹ *
          (d.gEltHom D (srcE E) ⟨v, hv⟩ * (d.gEltHom D (srcE E) ⟨(d.linkH E : G), hH⟩)⁻¹) *
          TreeDatum.stepGam D E true) *
        (d.gEltHom D (tgtE E) ⟨(d.linkK E : G), hK⟩)⁻¹ *
        d.gEltHom D (tgtE E) ⟨w, hw⟩ := by group
  rw [hτf, stepGam_false_eq_inv D (E := E), key, hBv, hconj]
  -- Collect the remaining vertex-group letters at the common orbit `tgtE E`.
  simp only [← map_mul, ← map_inv]
  refine congrArg (d.gEltHom D (tgtE E)) ?_
  exact Subtype.ext (by simp)

end Work.ORLocInd.FKSKernel.Kurosh
