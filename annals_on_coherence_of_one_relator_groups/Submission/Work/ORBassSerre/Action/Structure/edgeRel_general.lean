import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSPresentation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

variable (d : TreeDatum G V) (D : d.PresData)
variable [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

/-!
# The edge relations of the Bass--Serre presentation, for an arbitrary edge group element

The relators `edgeRel d D E j` of `BSPresentation` only make the two images of the *chosen
generators* `gensE E j` of the edge group agree (for a tree edge orbit), respectively be conjugate
by the stable letter (for a non-tree edge orbit).  In this file we extend these relations to an
arbitrary element `c` of the edge group, using that the chosen generators generate it.

The two generator-level statements `edgeRel_gen_tree` and `edgeRel_gen_nontree` are read off
directly from the corresponding relators, and `eq_of_agree_on_gens` upgrades agreement on the
generating family to equality of homomorphisms.
-/

/-- **Agreement on a generating family implies equality.** Two homomorphisms out of an edge group
`eGroup E` which agree on the chosen generating family `gensE E` agree everywhere: the set on which
two homomorphisms agree is a subgroup, and it contains the generating family, whose closure is
everything by `hgensE`. -/
theorem eq_of_agree_on_gens (E : Work.ORBassSerre.orbitE G V)
    (f g : ↥(d.eGroup E) →* Gamma d D)
    (h : ∀ j, f (D.gensE E j) = g (D.gensE E j)) : f = g := by
  have hT : Subgroup.closure (Set.range (D.gensE E)) ≤
      ({ carrier := {x | f x = g x}
         one_mem' := by simp
         mul_mem' := by
           intro a b ha hb
           change f (a * b) = g (a * b)
           rw [map_mul, map_mul, ha, hb]
         inv_mem' := by
           intro a ha
           change f a⁻¹ = g a⁻¹
           rw [map_inv, map_inv, ha] } : Subgroup ↥(d.eGroup E)) := by
    rw [Subgroup.closure_le]
    rintro x ⟨j, rfl⟩
    exact h j
  ext x
  exact hT (by rw [D.hgensE E]; exact Subgroup.mem_top x)

/-- The tree edge relator, read in `Gamma`: for a tree edge orbit the two images of a chosen
generator of the edge group coincide. -/
theorem edgeRel_gen_tree (E : Work.ORBassSerre.orbitE G V) (htree : d.IsTreeEdge E)
    (j : Fin (D.nE E)) :
    d.gEltHom D (srcE (G := G) (V := V) E) (d.eGroupToSrc E (D.gensE E j)) =
      d.gEltHom D (tgtE (G := G) (V := V) E) (d.eGroupToTgt E (D.gensE E j)) := by
  have h1 : PresentedGroup.mk (rels d D) (edgeRel d D E j) = 1 :=
    PresentedGroup.one_of_mem (edgeRel_mem_rels d D E j)
  rw [edgeRel, dif_pos htree] at h1
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- The non-tree edge relator, read in `Gamma`: the stable letter conjugates the image of a chosen
generator of the edge group in the source vertex group to its image in the target vertex group. -/
theorem edgeRel_gen_nontree (E : Work.ORBassSerre.orbitE G V) (hnt : ¬ d.IsTreeEdge E)
    (j : Fin (D.nE E)) :
    (PresentedGroup.of (Sum.inr ⟨E, hnt⟩))⁻¹ *
        d.gEltHom D (srcE (G := G) (V := V) E) (d.eGroupToSrc E (D.gensE E j)) *
        (PresentedGroup.of (Sum.inr ⟨E, hnt⟩)) =
      d.gEltHom D (tgtE (G := G) (V := V) E) (d.eGroupToTgt E (D.gensE E j)) := by
  have h1 : PresentedGroup.mk (rels d D) (edgeRel d D E j) = 1 :=
    PresentedGroup.one_of_mem (edgeRel_mem_rels d D E j)
  rw [edgeRel, dif_neg hnt] at h1
  rw [map_mul, map_mul, map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

end TreeDatum

/-- **The edge relations for an arbitrary edge group element.** For a tree edge orbit `E` the two
inclusions of the edge group into the neighbouring vertex groups agree after passing to `Gamma`,
and for a non-tree edge orbit the stable letter conjugates the source inclusion into the target
inclusion. -/
theorem edgeRel_general {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum G V) (D : d.PresData)
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    (E : Work.ORBassSerre.orbitE G V) (c : ↥(d.eGroup E)) :
    (d.IsTreeEdge E →
        d.gEltHom D (srcE E) (d.eGroupToSrc E c) =
          d.gEltHom D (tgtE E) (d.eGroupToTgt E c)) ∧
      (∀ (h : ¬ d.IsTreeEdge E),
        (PresentedGroup.of (Sum.inr ⟨E, h⟩))⁻¹ * d.gEltHom D (srcE E) (d.eGroupToSrc E c) *
            (PresentedGroup.of (Sum.inr ⟨E, h⟩))
          = d.gEltHom D (tgtE E) (d.eGroupToTgt E c)) := by
  classical
  constructor
  · intro htree
    have hfg := TreeDatum.eq_of_agree_on_gens d D E
      ((d.gEltHom D (srcE (G := G) (V := V) E)).comp (d.eGroupToSrc E))
      ((d.gEltHom D (tgtE (G := G) (V := V) E)).comp (d.eGroupToTgt E))
      (fun j => TreeDatum.edgeRel_gen_tree d D E htree j)
    simpa using DFunLike.congr_fun hfg c
  · intro hnt
    let t : d.Gamma D := PresentedGroup.of (Sum.inr ⟨E, hnt⟩)
    let f : ↥(d.eGroup E) →* d.Gamma D :=
      (d.gEltHom D (srcE (G := G) (V := V) E)).comp (d.eGroupToSrc E)
    let g : ↥(d.eGroup E) →* d.Gamma D :=
      (d.gEltHom D (tgtE (G := G) (V := V) E)).comp (d.eGroupToTgt E)
    let conj : ↥(d.eGroup E) →* d.Gamma D :=
      { toFun := fun x => t⁻¹ * f x * t
        map_one' := by simp
        map_mul' := by
          intro a b
          rw [map_mul]
          group }
    have hcg : conj = g :=
      TreeDatum.eq_of_agree_on_gens d D E conj g
        (fun j => by simpa [conj, t, f, g] using TreeDatum.edgeRel_gen_nontree d D E hnt j)
    simpa [conj, t, f, g] using DFunLike.congr_fun hcg c

end Work.ORBassSerre.Action.Structure
