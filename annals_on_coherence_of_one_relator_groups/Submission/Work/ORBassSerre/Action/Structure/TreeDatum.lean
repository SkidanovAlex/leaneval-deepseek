import Mathlib
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Action.Structure.exists_spanningTree_lift

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# The fundamental-domain (spanning tree) datum of a cocompact `G`-tree

This file packages the spanning-tree data of `exists_spanningTree_lift` into a structure
`TreeDatum`, and derives from it the graph-of-groups data used by the Bass--Serre structure
theorem: for every edge orbit `E` a chosen lift `elift E` whose source is the lifted vertex
`vert (srcE E)` of the source orbit, together with the "stable letter" `sElt E` with
`(elift E).right = sElt E • vert (tgtE E)`, the edge group `eGroup E` (the stabiliser of the
lifted edge) and its inclusions into the two neighbouring vertex groups.

For the edges of the spanning tree the chosen lift is the plumbing arrow `parArrow`, and the
stable letter is `1`.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- **A spanning tree of the quotient graph, lifted to the tree `V`.**

This is the data provided by `Work.ORBassSerre.Action.Structure.exists_spanningTree_lift`: for
every vertex orbit a lift `vert`, a parent map `par` and rank function on the orbits, and for
every non-root orbit a lifting arrow `parArrow` realising the parent edge, with pairwise distinct
edge orbits. -/
structure TreeDatum (G : Type u) (V : Type v) [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V] where
  /-- the chosen root vertex orbit -/
  root : Work.ORBassSerre.orbitV G V
  /-- a lift of every vertex orbit -/
  vert : Work.ORBassSerre.orbitV G V → V
  /-- the parent of a vertex orbit -/
  par : Work.ORBassSerre.orbitV G V → Work.ORBassSerre.orbitV G V
  /-- the rank on the vertex orbits -/
  rank : Work.ORBassSerre.orbitV G V → ℕ
  /-- the lifting arrow of a parent edge -/
  parArrow : (A : Work.ORBassSerre.orbitV G V) → A ≠ root → Quiver.Total V
  vert_mk : ∀ A, Quotient.mk'' (vert A) = A
  rank_root : rank root = 0
  rank_eq_zero : ∀ A, rank A = 0 ↔ A = root
  rank_par_lt : ∀ A (hA : A ≠ root), rank (par A) < rank A
  parArrow_left : ∀ A hA, (parArrow A hA).left = vert (par A)
  parArrow_right : ∀ A hA, (parArrow A hA).right = vert A
  parArrow_ne : ∀ A B hA hB, A ≠ B →
    (Quotient.mk'' (parArrow A hA) : Work.ORBassSerre.orbitE G V) ≠
      Quotient.mk'' (parArrow B hB)

/-- The spanning tree datum exists for a cocompact action on a tree without inversions. -/
theorem nonempty_treeDatum (hT : Work.ORBassSerre.IsTree V)
    (hcc : Work.ORBassSerre.IsCocompact G V) (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (root : Work.ORBassSerre.orbitV G V) : Nonempty (TreeDatum G V) := by
  obtain ⟨vert, par, rank, parArrow, h1, h2, h3, h4, h5, h6⟩ :=
    exists_spanningTree_lift (G := G) (V := V) hT hcc hninv root
  have hdatum : TreeDatum G V :=
    { root := root, vert := vert, par := par, rank := rank, parArrow := parArrow,
      vert_mk := h1, rank_root := h2, rank_eq_zero := h3, rank_par_lt := h4,
      parArrow_left := fun A hA => (h5 A hA).1, parArrow_right := fun A hA => (h5 A hA).2,
      parArrow_ne := h6 }
  exact ⟨hdatum⟩

namespace TreeDatum

variable (d : TreeDatum G V)

/-- An edge orbit is a *tree edge orbit* if it is the orbit of one of the plumbing arrows. -/
abbrev IsTreeEdge (E : Work.ORBassSerre.orbitE G V) : Prop :=
  ∃ p : {A : Work.ORBassSerre.orbitV G V // A ≠ d.root},
    (Quotient.mk'' (d.parArrow p.1 p.2) : Work.ORBassSerre.orbitE G V) = E

theorem isTreeEdge_mk {A : Work.ORBassSerre.orbitV G V} (hA : A ≠ d.root) :
    d.IsTreeEdge (Quotient.mk'' (d.parArrow A hA)) :=
  ⟨⟨A, hA⟩, rfl⟩

/-- Two plumbing arrows with the same edge orbit have the same vertex orbit. -/
theorem eq_of_parArrow_orbit_eq {A B : Work.ORBassSerre.orbitV G V} (hA : A ≠ d.root)
    (hB : B ≠ d.root)
    (h : (Quotient.mk'' (d.parArrow A hA) : Work.ORBassSerre.orbitE G V) =
      Quotient.mk'' (d.parArrow B hB)) :
    A = B := by
  by_contra hne
  exact d.parArrow_ne A B hA hB hne h

/-- The source orbit of the tree edge orbit of the arrow of `A` is `par A`. -/
theorem srcE_parArrow {A : Work.ORBassSerre.orbitV G V} (hA : A ≠ d.root) :
    srcE (G := G) (V := V) (Quotient.mk'' (d.parArrow A hA)) = d.par A := by
  have h := mk_left_eq_of_mk_eq (G := G) (V := V)
    (u := d.parArrow A hA) (w := orbitRepE (G := G) (V := V)
      (Quotient.mk'' (d.parArrow A hA))) (orbitRepE_mk _).symm
  show Quotient.mk'' (orbitRepE _).left = d.par A
  rw [← h]
  show Quotient.mk'' ((d.parArrow A hA).left) = d.par A
  rw [d.parArrow_left A hA]
  exact d.vert_mk (d.par A)

/-- The target orbit of the tree edge orbit of the arrow of `A` is `A`. -/
theorem tgtE_parArrow {A : Work.ORBassSerre.orbitV G V} (hA : A ≠ d.root) :
    tgtE (G := G) (V := V) (Quotient.mk'' (d.parArrow A hA)) = A := by
  have h := mk_right_eq_of_mk_eq (G := G) (V := V)
    (u := d.parArrow A hA) (w := orbitRepE (G := G) (V := V)
      (Quotient.mk'' (d.parArrow A hA))) (orbitRepE_mk _).symm
  show Quotient.mk'' (orbitRepE _).right = A
  rw [← h]
  show Quotient.mk'' ((d.parArrow A hA).right) = A
  rw [d.parArrow_right A hA]
  exact d.vert_mk A

/-- There is a lift of every edge orbit whose source is the lifted vertex of the source orbit; for
tree edge orbits it is one of the plumbing arrows. -/
theorem exists_lift (E : Work.ORBassSerre.orbitE G V) :
    ∃ u : Quiver.Total V, (Quotient.mk'' u : Work.ORBassSerre.orbitE G V) = E ∧
      u.left = d.vert (srcE (G := G) (V := V) E) ∧
      (d.IsTreeEdge E → ∃ (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root),
        u = d.parArrow A hA) := by
  classical
  by_cases htree : d.IsTreeEdge E
  · obtain ⟨p, hp⟩ := htree
    refine ⟨d.parArrow p.1 p.2, hp, ?_, fun _ => ⟨p.1, p.2, rfl⟩⟩
    rw [d.parArrow_left p.1 p.2, ← d.srcE_parArrow p.2, hp]
  · set u₀ : Quiver.Total V := orbitRepE (G := G) (V := V) E with hu₀
    have hsrc : (Quotient.mk'' u₀.left : Work.ORBassSerre.orbitV G V) =
        Quotient.mk'' (d.vert (srcE (G := G) (V := V) E)) := by
      rw [show (Quotient.mk'' u₀.left : Work.ORBassSerre.orbitV G V) =
        srcE (G := G) (V := V) E from rfl, d.vert_mk]
    obtain ⟨g, hg⟩ := exists_smul_of_mk_eq (G := G) (V := V) (x := u₀.left)
      (y := d.vert (srcE (G := G) (V := V) E)) hsrc
    refine ⟨g • u₀, ?_, ?_, fun hh => absurd hh htree⟩
    · show (Quotient.mk'' (g • u₀) : Work.ORBassSerre.orbitE G V) = E
      rw [show (Quotient.mk'' (g • u₀) : Work.ORBassSerre.orbitE G V) = Quotient.mk'' u₀ from
        Quotient.sound ⟨g, rfl⟩]
      show (Quotient.mk'' u₀ : Work.ORBassSerre.orbitE G V) = E
      rw [hu₀]; exact orbitRepE_mk E
    · show (g • u₀).left = d.vert (srcE (G := G) (V := V) E)
      rw [Work.ORBassSerre.Action.smul_left_total, hg]

/-- **The chosen lift of an edge orbit**: a lift whose source is the lifted vertex of the source
orbit.  For the edges of the spanning tree this is the plumbing arrow. -/
noncomputable def elift (E : Work.ORBassSerre.orbitE G V) : Quiver.Total V :=
  Classical.choose (d.exists_lift E)

theorem elift_orbit (E : Work.ORBassSerre.orbitE G V) :
    (Quotient.mk'' (d.elift E) : Work.ORBassSerre.orbitE G V) = E :=
  (Classical.choose_spec (d.exists_lift E)).1

theorem elift_left (E : Work.ORBassSerre.orbitE G V) :
    (d.elift E).left = d.vert (srcE (G := G) (V := V) E) :=
  (Classical.choose_spec (d.exists_lift E)).2.1

theorem elift_tree {E : Work.ORBassSerre.orbitE G V} (h : d.IsTreeEdge E) :
    ∃ (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ d.root), d.elift E = d.parArrow A hA :=
  (Classical.choose_spec (d.exists_lift E)).2.2 h

theorem elift_eq_parArrow {A : Work.ORBassSerre.orbitV G V} (hA : A ≠ d.root) :
    d.elift (Quotient.mk'' (d.parArrow A hA)) = d.parArrow A hA := by
  obtain ⟨A', hA', hpar⟩ := d.elift_tree (d.isTreeEdge_mk hA)
  have horbit : (Quotient.mk'' (d.parArrow A' hA') : Work.ORBassSerre.orbitE G V) =
      Quotient.mk'' (d.parArrow A hA) := by
    rw [← hpar]; exact d.elift_orbit _
  have hAA : A' = A := d.eq_of_parArrow_orbit_eq hA' hA horbit
  subst hAA
  exact hpar

/-- There is a group element carrying the lifted vertex of the target orbit to the target of the
chosen lift; for tree edge orbits it can be taken to be `1`. -/
theorem exists_sElt (E : Work.ORBassSerre.orbitE G V) :
    ∃ s : G, (d.elift E).right = s • d.vert (tgtE (G := G) (V := V) E) ∧
      (d.IsTreeEdge E → s = 1) := by
  classical
  by_cases htree : d.IsTreeEdge E
  · obtain ⟨A, hA, hpar⟩ := d.elift_tree htree
    have htgt : tgtE (G := G) (V := V) E = A := by
      have h1 : (Quotient.mk'' (d.parArrow A hA) : Work.ORBassSerre.orbitE G V) =
          Quotient.mk'' (orbitRepE (G := G) (V := V) E) := by
        rw [orbitRepE_mk, ← hpar, d.elift_orbit E]
      have h2 : (Quotient.mk'' (d.parArrow A hA).right : Work.ORBassSerre.orbitV G V) =
          Quotient.mk'' (orbitRepE (G := G) (V := V) E).right :=
        mk_right_eq_of_mk_eq (G := G) (V := V) h1
      show Quotient.mk'' (orbitRepE (G := G) (V := V) E).right = A
      rw [← h2, d.parArrow_right A hA, d.vert_mk]
    refine ⟨1, ?_, fun _ => rfl⟩
    rw [hpar, d.parArrow_right A hA, htgt, one_smul]
  · have h : (Quotient.mk'' (d.elift E).right : Work.ORBassSerre.orbitV G V) =
        Quotient.mk'' (d.vert (tgtE (G := G) (V := V) E)) := by
      have h1 : (Quotient.mk'' (d.elift E) : Work.ORBassSerre.orbitE G V) =
          Quotient.mk'' (orbitRepE (G := G) (V := V) E) := by
        rw [d.elift_orbit E, orbitRepE_mk]
      have h2 : (Quotient.mk'' (d.elift E).right : Work.ORBassSerre.orbitV G V) =
          Quotient.mk'' (orbitRepE (G := G) (V := V) E).right :=
        mk_right_eq_of_mk_eq (G := G) (V := V) h1
      have h3 : (Quotient.mk'' (orbitRepE (G := G) (V := V) E).right :
          Work.ORBassSerre.orbitV G V) = tgtE (G := G) (V := V) E := rfl
      rw [h2, h3, d.vert_mk]
    obtain ⟨g, hg⟩ := exists_smul_of_mk_eq (G := G) (V := V) (x := (d.elift E).right)
      (y := d.vert (tgtE (G := G) (V := V) E)) h
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul], fun hh => absurd hh htree⟩

/-- **The stable letter of an edge orbit**: the group element with
`(elift E).right = sElt E • vert (tgtE E)`.  For tree edge orbits it is `1`. -/
noncomputable def sElt (E : Work.ORBassSerre.orbitE G V) : G :=
  Classical.choose (d.exists_sElt E)

theorem sElt_eq_one {E : Work.ORBassSerre.orbitE G V} (h : d.IsTreeEdge E) : d.sElt E = 1 :=
  (Classical.choose_spec (d.exists_sElt E)).2 h

theorem elift_right (E : Work.ORBassSerre.orbitE G V) :
    (d.elift E).right = d.sElt E • d.vert (tgtE (G := G) (V := V) E) :=
  (Classical.choose_spec (d.exists_sElt E)).1

/-! ## The two directed moves along an edge orbit -/

/-- The source vertex orbit of the move along `E` in direction `b`
(`true` = from the source end of the edge orbit to the target end). -/
noncomputable def moveSrc (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    Work.ORBassSerre.orbitV G V :=
  if b then srcE (G := G) (V := V) E else tgtE (G := G) (V := V) E

/-- The target vertex orbit of the move along `E` in direction `b`. -/
noncomputable def moveTgt (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    Work.ORBassSerre.orbitV G V :=
  if b then tgtE (G := G) (V := V) E else srcE (G := G) (V := V) E

/-- The group element realising the move along `E` in direction `b`. -/
noncomputable def moveElt (E : Work.ORBassSerre.orbitE G V) (b : Bool) : G :=
  if b then d.sElt E else (d.sElt E)⁻¹

/-- The *move* along the edge orbit `E` in direction `b`: an arrow from the lifted vertex of the
source orbit to the translate by `moveElt E b` of the lifted vertex of the target orbit. -/
noncomputable def move (E : Work.ORBassSerre.orbitE G V) (b : Bool) : Quiver.Total V :=
  if b then d.elift E else ((d.sElt E)⁻¹ • d.elift E).reverse

theorem moveSrc_true (E : Work.ORBassSerre.orbitE G V) :
    moveSrc E true = srcE (G := G) (V := V) E := rfl

theorem moveSrc_false (E : Work.ORBassSerre.orbitE G V) :
    moveSrc E false = tgtE (G := G) (V := V) E := rfl

theorem moveTgt_true (E : Work.ORBassSerre.orbitE G V) :
    moveTgt E true = tgtE (G := G) (V := V) E := rfl

theorem moveTgt_false (E : Work.ORBassSerre.orbitE G V) :
    moveTgt E false = srcE (G := G) (V := V) E := rfl

theorem moveElt_true (E : Work.ORBassSerre.orbitE G V) : d.moveElt E true = d.sElt E := rfl

theorem moveElt_false (E : Work.ORBassSerre.orbitE G V) :
    d.moveElt E false = (d.sElt E)⁻¹ := rfl

theorem move_left (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    (d.move E b).left = d.vert (moveSrc E b) := by
  cases b
  · show (((d.sElt E)⁻¹ • d.elift E).reverse).left = d.vert (tgtE (G := G) (V := V) E)
    rw [Quiver.Total.reverse_left, Work.ORBassSerre.Action.smul_right_total, d.elift_right,
      ← mul_smul, inv_mul_cancel, one_smul]
  · show (d.elift E).left = d.vert (srcE (G := G) (V := V) E)
    rw [d.elift_left]

theorem move_right (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    (d.move E b).right = d.moveElt E b • d.vert (moveTgt E b) := by
  cases b
  · show (((d.sElt E)⁻¹ • d.elift E).reverse).right =
      (d.sElt E)⁻¹ • d.vert (srcE (G := G) (V := V) E)
    rw [Quiver.Total.reverse_right, Work.ORBassSerre.Action.smul_left_total, d.elift_left]
  · show (d.elift E).right = d.sElt E • d.vert (tgtE (G := G) (V := V) E)
    rw [d.elift_right]

/-- The move of a *tree* edge orbit does not move the lifted vertex of the target orbit. -/
theorem move_tree_target {E : Work.ORBassSerre.orbitE G V} (h : d.IsTreeEdge E) (b : Bool) :
    d.moveElt E b • d.vert (moveTgt E b) = d.vert (moveTgt E b) := by
  have hs : d.sElt E = 1 := d.sElt_eq_one h
  cases b
  · show (d.sElt E)⁻¹ • d.vert (srcE (G := G) (V := V) E) = d.vert (srcE (G := G) (V := V) E)
    rw [hs, inv_one, one_smul]
  · show d.sElt E • d.vert (tgtE (G := G) (V := V) E) = d.vert (tgtE (G := G) (V := V) E)
    rw [hs, one_smul]

/-! ## The vertex and edge groups -/

/-- The vertex group of a vertex orbit: the stabiliser of its lifted representative. -/
noncomputable abbrev vgroup (A : Work.ORBassSerre.orbitV G V) : Subgroup G :=
  MulAction.stabilizer G (d.vert A)

/-- The edge group of an edge orbit: the stabiliser of the chosen lift. -/
noncomputable abbrev eGroup (E : Work.ORBassSerre.orbitE G V) : Subgroup G :=
  MulAction.stabilizer G (d.elift E)

theorem eGroup_le_vgroup_src (E : Work.ORBassSerre.orbitE G V) :
    d.eGroup E ≤ d.vgroup (srcE (G := G) (V := V) E) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← d.elift_left E]
  calc g • (d.elift E).left = (g • d.elift E).left :=
        (Work.ORBassSerre.Action.smul_left_total g (d.elift E)).symm
    _ = (d.elift E).left := congrArg Quiver.Total.left hg

theorem eGroup_le_conj (E : Work.ORBassSerre.orbitE G V) :
    d.eGroup E ≤ (d.vgroup (tgtE (G := G) (V := V) E)).map
      (MulEquiv.toMonoidHom (MulAut.conj (d.sElt E))) := by
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj (d.sElt E)
    (d.vert (tgtE (G := G) (V := V) E))]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← d.elift_right E]
  calc g • (d.elift E).right = (g • d.elift E).right :=
        (Work.ORBassSerre.Action.smul_right_total g (d.elift E)).symm
    _ = (d.elift E).right := congrArg Quiver.Total.right hg

/-- The inclusion of the edge group of `E` into the vertex group of the source orbit. -/
noncomputable def eGroupToSrc (E : Work.ORBassSerre.orbitE G V) :
    d.eGroup E →* d.vgroup (srcE (G := G) (V := V) E) :=
  Subgroup.inclusion (d.eGroup_le_vgroup_src E)

/-- The map from the edge group of `E` into the vertex group of the target orbit, given by
conjugation by the inverse of the stable letter. -/
noncomputable def eGroupToTgt (E : Work.ORBassSerre.orbitE G V) :
    d.eGroup E →* d.vgroup (tgtE (G := G) (V := V) E) where
  toFun g := ⟨(d.sElt E)⁻¹ * (g : G) * d.sElt E, by
    rw [MulAction.mem_stabilizer_iff]
    have hg : g • (d.elift E) = d.elift E := g.2
    calc ((d.sElt E)⁻¹ * (g : G) * d.sElt E) • d.vert (tgtE (G := G) (V := V) E)
        = ((d.sElt E)⁻¹ * (g : G)) • (d.sElt E • d.vert (tgtE (G := G) (V := V) E)) := by
          rw [mul_smul]
      _ = ((d.sElt E)⁻¹ * (g : G)) • (d.elift E).right := by rw [d.elift_right]
      _ = (d.sElt E)⁻¹ • ((g : G) • (d.elift E).right) := by rw [mul_smul]
      _ = (d.sElt E)⁻¹ • (d.elift E).right := by
          rw [show (g : G) • (d.elift E).right = (g • d.elift E).right from
            (Work.ORBassSerre.Action.smul_right_total (g : G) (d.elift E)).symm, hg]
      _ = (d.sElt E)⁻¹ • (d.sElt E • d.vert (tgtE (G := G) (V := V) E)) := by
          rw [d.elift_right]
      _ = d.vert (tgtE (G := G) (V := V) E) := by rw [← mul_smul, inv_mul_cancel, one_smul]⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp [mul_assoc]

theorem eGroupToSrc_apply (E : Work.ORBassSerre.orbitE G V) (g : d.eGroup E) :
    ((d.eGroupToSrc E g : d.vgroup (srcE (G := G) (V := V) E)) : G) = (g : G) := rfl

theorem eGroupToTgt_apply (E : Work.ORBassSerre.orbitE G V) (g : d.eGroup E) :
    ((d.eGroupToTgt E g : d.vgroup (tgtE (G := G) (V := V) E)) : G) =
      (d.sElt E)⁻¹ * (g : G) * d.sElt E := rfl

theorem eGroupToTgt_mem (E : Work.ORBassSerre.orbitE G V) (g : d.eGroup E) :
    (d.sElt E)⁻¹ * (g : G) * d.sElt E ∈ d.vgroup (tgtE (G := G) (V := V) E) :=
  (d.eGroupToTgt E g).2

end TreeDatum

end Work.ORBassSerre.Action.Structure
