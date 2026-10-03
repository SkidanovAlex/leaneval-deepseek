import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum
import Submission.Work.ORLocInd.FKSKernel.Kurosh.EdgeLink

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

open Quiver
open Classical

/-!
# The presentation of the fundamental group of the fundamental domain

Given a `TreeDatum` `d` of a cocompact action of `G` on a tree `V` without inversions, together
with finite presentations of the vertex groups `vgroup A = Stab (vert A)` and finite generating
families of the edge groups `eGroup E = Stab (elift E)`, this file defines the group

`Gamma D = PresentedGroup (rels D)`

presented by

* a generator for each element of the chosen finite generating family of each vertex group;
* a stable letter `t_E` for each edge orbit `E` which is *not* a tree edge orbit;

subject to

* the relations of each vertex group,
* for a tree edge orbit `E` with ends `srcE E` and `tgtE E`: the identification of the two images
  of the edge group,
* for a non-tree edge orbit `E`: the conjugation relation `t_E⁻¹ c t_E = sElt E⁻¹ c sElt E`
  for `c` in a generating family of the edge group.

There is a canonical map `TreeDatum.Φ : Gamma D →* G` and the main theorem is that `Φ` is
injective, so that `Gamma D ≅ G`; since `Gamma D` is finitely presented, this gives that `G` is
finitely presented.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

variable (d : TreeDatum G V)

/-- The data of a finite presentation of each vertex group and a finite generating family of each
edge group. -/
structure PresData where
  /-- the type of generators of the vertex group of each vertex orbit -/
  ιV : Work.ORBassSerre.orbitV G V → Type u
  /-- a surjection from the free group on the chosen generators onto each vertex group -/
  πV : ∀ A, FreeGroup (ιV A) →* ↥(d.vgroup A)
  /-- the surjection is surjective -/
  hπV : ∀ A, Function.Surjective (πV A)
  /-- a set of relators for each vertex group -/
  RV : ∀ A, Set (FreeGroup (ιV A))
  /-- the normal closures of the relator sets are the kernels -/
  hRV : ∀ A, Subgroup.normalClosure (RV A) = (πV A).ker
  /-- the type of chosen generators of the edge group of each edge orbit -/
  ιE : Work.ORBassSerre.orbitE G V → Type u
  /-- a generating family of each edge group -/
  gensE : ∀ E, ιE E → ↥(d.eGroup E)
  /-- the generating families generate -/
  hgensE : ∀ E, Subgroup.closure (Set.range (gensE E)) = ⊤

variable (D : PresData d)

/-- The generators of the presentation: a generator for each element of the chosen finite
generating family of a vertex group, and a stable letter for each edge orbit which is not a tree
edge orbit. -/
abbrev PresGen : Type _ :=
  (Σ A : Work.ORBassSerre.orbitV G V, D.ιV A) ⊕
    {E : Work.ORBassSerre.orbitE G V // ¬ d.IsTreeEdge E}

/-- The image of the chosen generating family of a vertex group in the global generators. -/
noncomputable def blockOf (A : Work.ORBassSerre.orbitV G V) :
    FreeGroup (D.ιV A) →* FreeGroup (PresGen d D) :=
  FreeGroup.lift fun i => FreeGroup.of (Sum.inl ⟨A, i⟩)

theorem blockOf_of (A : Work.ORBassSerre.orbitV G V) (i : D.ιV A) :
    blockOf d D A (FreeGroup.of i) = FreeGroup.of (Sum.inl ⟨A, i⟩) :=
  FreeGroup.lift_apply_of

/-- A chosen word in the free generators of a vertex group representing a given element. -/
noncomputable def wordOf (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    FreeGroup (D.ιV A) :=
  Classical.choose (D.hπV A g)

theorem wordOf_spec (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    D.πV A (wordOf d D A g) = g :=
  Classical.choose_spec (D.hπV A g)

/-- The word in the generators of the presentation representing the stable-letter part of a step
along an edge orbit: `1` for a tree edge orbit, and the stable letter (or its inverse) otherwise.
This is the word-level counterpart of `stepGam` (which lives in `BSWalk`). -/
noncomputable def stepWord (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    FreeGroup (PresGen d D) :=
  if h : d.IsTreeEdge E then 1
  else if b then FreeGroup.of (Sum.inr ⟨E, h⟩) else (FreeGroup.of (Sum.inr ⟨E, h⟩))⁻¹

/-- The relator attached to one element of the generating family of the edge group of `E`. -/
noncomputable def edgeRel (E : Work.ORBassSerre.orbitE G V) (j : D.ιE E) :
    FreeGroup (PresGen d D) :=
  if h : d.IsTreeEdge E then
    blockOf d D (srcE (G := G) (V := V) E)
        (wordOf d D (srcE (G := G) (V := V) E) (d.eGroupToSrc E (D.gensE E j))) *
      (blockOf d D (tgtE (G := G) (V := V) E)
        (wordOf d D (tgtE (G := G) (V := V) E)
          (d.eGroupToTgt E (D.gensE E j))))⁻¹
  else
    (FreeGroup.of (Sum.inr ⟨E, h⟩))⁻¹ *
      blockOf d D (srcE (G := G) (V := V) E)
        (wordOf d D (srcE (G := G) (V := V) E) (d.eGroupToSrc E (D.gensE E j))) *
      FreeGroup.of (Sum.inr ⟨E, h⟩) *
      (blockOf d D (tgtE (G := G) (V := V) E)
        (wordOf d D (tgtE (G := G) (V := V) E)
          (d.eGroupToTgt E (D.gensE E j))))⁻¹

/-- The relator expressing that the stable letter of the reversed edge orbit is the stable letter
of the orbit, conjugated by the vertex group elements of the linking identity (`linkK`, `linkH`). -/
noncomputable def linkRel (E : Work.ORBassSerre.orbitE G V) : FreeGroup (PresGen d D) :=
  (blockOf d D (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))
      (wordOf d D (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) (d.linkK E)) *
    (stepWord d D E true)⁻¹ *
    blockOf d D (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))
      (wordOf d D (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))
        (d.linkH E))) *
  (stepWord d D (Work.ORBassSerre.orbitEReverse E) true)⁻¹


/-- The set of relators of the presentation. -/
noncomputable def rels : Set (FreeGroup (PresGen d D)) :=
  ((⋃ A : Work.ORBassSerre.orbitV G V, blockOf d D A '' (D.RV A)) ∪
    (⋃ E : Work.ORBassSerre.orbitE G V, (Set.univ : Set (D.ιE E)).image (edgeRel d D E))) ∪
  (⋃ E : Work.ORBassSerre.orbitE G V, {linkRel d D E})

theorem block_mem_rels {A : Work.ORBassSerre.orbitV G V} {r : FreeGroup (D.ιV A)}
    (hr : r ∈ D.RV A) : blockOf d D A r ∈ rels d D := by
  rw [rels]
  exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨A, Set.mem_image_of_mem _ hr⟩))

theorem edgeRel_mem_rels (E : Work.ORBassSerre.orbitE G V) (j : D.ιE E) :
    edgeRel d D E j ∈ rels d D := by
  rw [rels]
  exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨E, Set.mem_image_of_mem _ (Set.mem_univ j)⟩))

theorem linkRel_mem_rels (E : Work.ORBassSerre.orbitE G V) : linkRel d D E ∈ rels d D := by
  rw [rels]
  exact Or.inr (Set.mem_iUnion.mpr ⟨E, rfl⟩)

/-! ## The fundamental group and the canonical map to `G` -/

/-- The fundamental group of the fundamental domain: the group presented by the vertex group
generators and the stable letters. -/
noncomputable abbrev Gamma : Type _ := PresentedGroup (rels d D)

/-- The value in `G` of a generator of the presentation. -/
noncomputable def genMap : PresGen d D → G
  | Sum.inl ⟨A, i⟩ => ((D.πV A (FreeGroup.of i) : ↥(d.vgroup A)) : G)
  | Sum.inr ⟨E, _⟩ => d.sElt E

theorem lift_genMap_block (A : Work.ORBassSerre.orbitV G V) (w : FreeGroup (D.ιV A)) :
    FreeGroup.lift (genMap d D) (blockOf d D A w) = ((D.πV A w : ↥(d.vgroup A)) : G) := by
  have h1 : (FreeGroup.lift (genMap d D)).comp (blockOf d D A) =
      (Subgroup.subtype (d.vgroup A)).comp (D.πV A) := by
    apply FreeGroup.ext_hom
    intro i
    simp [blockOf, genMap]
  exact DFunLike.congr_fun h1 w

theorem lift_genMap_stable (E : Work.ORBassSerre.orbitE G V) (h : ¬ d.IsTreeEdge E) :
    FreeGroup.lift (genMap d D) (FreeGroup.of (Sum.inr ⟨E, h⟩)) = d.sElt E := by
  rw [FreeGroup.lift_apply_of]
  rfl

theorem lift_genMap_block_apply (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    FreeGroup.lift (genMap d D) (blockOf d D A (wordOf d D A g)) = (g : G) := by
  rw [lift_genMap_block, wordOf_spec]

/-- The stable-letter word of a step maps to the corresponding element of `G`. -/
theorem lift_genMap_stepWord (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    FreeGroup.lift (genMap d D) (stepWord d D E b) = d.moveElt E b := by
  by_cases h : d.IsTreeEdge E
  · rw [stepWord, dif_pos h, map_one]
    cases b
    · rw [d.moveElt_false, d.sElt_eq_one h, inv_one]
    · rw [d.moveElt_true, d.sElt_eq_one h]
  · rw [stepWord, dif_neg h]
    cases b
    · show FreeGroup.lift (genMap d D) ((FreeGroup.of (Sum.inr ⟨E, h⟩))⁻¹) = (d.sElt E)⁻¹
      rw [map_inv, lift_genMap_stable]
    · show FreeGroup.lift (genMap d D) (FreeGroup.of (Sum.inr ⟨E, h⟩)) = d.sElt E
      rw [lift_genMap_stable]

/-- The linking relator is killed by the generator map. -/
theorem lift_genMap_linkRel (E : Work.ORBassSerre.orbitE G V) :
    FreeGroup.lift (genMap d D) (linkRel d D E) = 1 := by
  rw [linkRel, map_mul, map_inv, map_mul, map_mul, map_inv, lift_genMap_stepWord,
    lift_genMap_stepWord, lift_genMap_block_apply, lift_genMap_block_apply]
  simp only [d.moveElt_true]
  rw [d.sElt_orbitEReverse]
  group

/-- The relators of the presentation are killed by the generator map. -/
theorem rels_lift_eq_one : ∀ r ∈ rels d D, FreeGroup.lift (genMap d D) r = 1 := by
  intro r hr
  rw [rels] at hr
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_image, Set.mem_univ, Set.mem_singleton_iff,
    exists_prop, true_and] at hr
  rcases hr with (⟨A, r', hr', rfl⟩ | ⟨E, j, rfl⟩) | ⟨E, rfl⟩
  · rw [lift_genMap_block]
    have hmem : r' ∈ Subgroup.normalClosure (D.RV A) :=
      Subgroup.subset_normalClosure hr'
    rw [(D.hRV A)] at hmem
    rw [hmem]
    rfl
  · rw [edgeRel]
    split_ifs with htree
    · simp only [map_mul, map_inv, lift_genMap_block, wordOf_spec, d.eGroupToSrc_apply,
        d.eGroupToTgt_apply, d.sElt_eq_one htree, inv_one, one_mul, mul_one]
      group
    · simp only [map_mul, map_inv, lift_genMap_block, wordOf_spec,
        lift_genMap_stable d D E htree, d.eGroupToSrc_apply, d.eGroupToTgt_apply]
      group
  · exact lift_genMap_linkRel d D E

/-- The canonical map from the fundamental group of the fundamental domain to `G`. -/
noncomputable def Φ : Gamma d D →* G :=
  PresentedGroup.toGroup (f := genMap d D) (rels_lift_eq_one d D)

theorem Φ_of_inl (A : Work.ORBassSerre.orbitV G V) (i : D.ιV A) :
    Φ d D (PresentedGroup.of (Sum.inl ⟨A, i⟩)) =
      ((D.πV A (FreeGroup.of i) : ↥(d.vgroup A)) : G) :=
  PresentedGroup.toGroup.of (rels_lift_eq_one d D)

theorem Φ_of_inr (E : Work.ORBassSerre.orbitE G V) (h : ¬ d.IsTreeEdge E) :
    Φ d D (PresentedGroup.of (Sum.inr ⟨E, h⟩)) = d.sElt E :=
  PresentedGroup.toGroup.of (rels_lift_eq_one d D)

theorem Φ_mk (x : FreeGroup (PresGen d D)) :
    Φ d D (PresentedGroup.mk (rels d D) x) = FreeGroup.lift (genMap d D) x :=
  QuotientGroup.lift_mk' (Subgroup.normalClosure (rels d D))
    (PresentedGroup.to_group_eq_one_of_mem_closure (rels_lift_eq_one d D)) x

/-- The image under `Φ` of the element of `Gamma` represented by a word in the generators of a
vertex group. -/
theorem Φ_block (A : Work.ORBassSerre.orbitV G V) (w : FreeGroup (D.ιV A)) :
    Φ d D (PresentedGroup.mk (rels d D) (blockOf d D A w)) =
      ((D.πV A w : ↥(d.vgroup A)) : G) := by
  rw [Φ_mk, lift_genMap_block]

/-- The element of `Gamma` represented by the chosen word of an element of a vertex group. -/
noncomputable def gElt (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) : Gamma d D :=
  PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A g))

theorem Φ_gElt (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    Φ d D (gElt d D A g) = (g : G) := by
  rw [gElt, Φ_mk, lift_genMap_block_apply]

/-- A word in the generators of a vertex group which lies in the kernel of the presentation of that
vertex group represents the trivial element of `Gamma`. -/
theorem mk_block_eq_one {A : Work.ORBassSerre.orbitV G V} {w : FreeGroup (D.ιV A)}
    (hw : w ∈ Subgroup.normalClosure (D.RV A)) :
    PresentedGroup.mk (rels d D) (blockOf d D A w) = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  have hle : Subgroup.normalClosure (D.RV A) ≤
      (Subgroup.normalClosure (rels d D)).comap (blockOf d D A) := by
    apply Subgroup.normalClosure_le_normal
    intro r hr
    exact Subgroup.subset_normalClosure (block_mem_rels d D hr)
  exact hle hw

/-- Two words in the generators of a vertex group with the same image represent the same element of
`Gamma`. -/
theorem mk_block_eq_of_sub_mem {A : Work.ORBassSerre.orbitV G V}
    {w w' : FreeGroup (D.ιV A)} (h : w * w'⁻¹ ∈ Subgroup.normalClosure (D.RV A)) :
    PresentedGroup.mk (rels d D) (blockOf d D A w) =
      PresentedGroup.mk (rels d D) (blockOf d D A w') := by
  have h2 : PresentedGroup.mk (rels d D) (blockOf d D A (w * w'⁻¹)) = 1 :=
    mk_block_eq_one d D h
  rw [map_mul, map_inv, map_mul, map_inv] at h2
  exact mul_inv_eq_one.mp h2

/-- Two words in the generators of a vertex group with the same image represent the same element of
`Gamma` (surjectivity form). -/
theorem mk_block_eq_of_πV_eq {A : Work.ORBassSerre.orbitV G V}
    {w w' : FreeGroup (D.ιV A)} (h : D.πV A w = D.πV A w') :
    PresentedGroup.mk (rels d D) (blockOf d D A w) =
      PresentedGroup.mk (rels d D) (blockOf d D A w') := by
  refine mk_block_eq_of_sub_mem d D ?_
  rw [(D.hRV A), MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

/-- The map `Γ_A : vgroup A → Gamma` sending an element of a vertex group to the element of
`Gamma` represented by its chosen word. -/
noncomputable def gEltHom (A : Work.ORBassSerre.orbitV G V) : ↥(d.vgroup A) →* Gamma d D where
  toFun := gElt d D A
  map_one' := by
    refine mk_block_eq_one d D ?_
    rw [(D.hRV A), MonoidHom.mem_ker]
    exact wordOf_spec d D A 1
  map_mul' a b := by
    show PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A (a * b))) =
      PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A a)) *
        PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A b))
    have h : PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A (a * b))) =
        PresentedGroup.mk (rels d D) (blockOf d D A (wordOf d D A a * wordOf d D A b)) :=
      mk_block_eq_of_πV_eq d D (w := wordOf d D A (a * b))
        (w' := wordOf d D A a * wordOf d D A b) (by
          rw [wordOf_spec, map_mul, wordOf_spec, wordOf_spec])
    rw [h]
    simp only [map_mul]

theorem Φ_gEltHom (A : Work.ORBassSerre.orbitV G V) (g : ↥(d.vgroup A)) :
    Φ d D (gEltHom d D A g) = (g : G) :=
  Φ_gElt d D A g

theorem gElt_eq_of_word {A : Work.ORBassSerre.orbitV G V} (w : FreeGroup (D.ιV A))
    (g : ↥(d.vgroup A)) (h : D.πV A w = g) :
    PresentedGroup.mk (rels d D) (blockOf d D A w) = gEltHom d D A g := by
  refine mk_block_eq_of_πV_eq d D (w := w) (w' := wordOf d D A g) ?_
  rw [wordOf_spec, h]

end TreeDatum

end Work.ORLocInd.FKSKernel.Kurosh
