import Mathlib
import Submission.Work.ORHughesFree.Tree

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-! # `1 * x = x` for finite rooted trees

`Tree` is the quotient of `MTree` (raw rooted trees) by the isomorphism relation
`Iso`, whose children relation `PermRel` is a mutual inductive with `Iso`.
The tree operations `mul`, `one` etc. are defined through `Quotient.out`, so the
proof below has to relate the (opaque) representative `Quotient.out (1 : Tree)`
to the explicit tree `MTree.node [Quotient.out (0 : Tree)]` and reason about the
resulting lists of children.
-/

/-- A custom induction principle for `PermRel`, whose built-in recursor is
mutually recursive with `Iso` (and hence is not usable with `induction`). -/
private theorem permRel_ind {motive : (l l' : List MTree) → PermRel l l' → Prop}
    (nil : motive [] [] PermRel.nil)
    (cons : ∀ {x y : MTree} {l l' : List MTree} (hx : Iso x y) (hl : PermRel l l'),
      motive l l' hl → motive (x :: l) (y :: l') (PermRel.cons hx hl))
    (swap : ∀ (x y : MTree) (l : List MTree),
      motive (x :: y :: l) (y :: x :: l) (PermRel.swap x y l))
    (refl : ∀ l : List MTree, motive l l (PermRel.refl l))
    (symm : ∀ {l l' : List MTree} (h : PermRel l l'), motive l l' h → motive l' l (PermRel.symm h))
    (trans : ∀ {l l' l'' : List MTree} (h : PermRel l l') (h' : PermRel l' l''),
      motive l l' h → motive l' l'' h' → motive l l'' (PermRel.trans h h')) :
    ∀ {l l' : List MTree} (h : PermRel l l'), motive l l' h :=
  PermRel.rec (motive_1 := fun _ _ _ => True) (motive_2 := motive)
    (fun _ _ => trivial) nil (fun hx hl _ ih => cons hx hl ih) swap refl symm trans

/-- Two representatives with equal image in `Tree` are isomorphic. -/
private lemma iso_of_mk_eq {a b : MTree} (h : (Quotient.mk'' a : Tree) = Quotient.mk'' b) :
    Iso a b :=
  Quotient.exact h

/-- Isomorphic representatives have equal image in `Tree`. -/
private lemma mk_eq_of_iso {a b : MTree} (h : Iso a b) :
    (Quotient.mk'' a : Tree) = Quotient.mk'' b :=
  Quotient.sound h

/-- `PermRel` preserves emptiness of the second list. -/
private lemma permRel_nil_iff {l l' : List MTree} (h : PermRel l l') : l = [] ↔ l' = [] := by
  induction h using permRel_ind with
  | nil => simp
  | cons hx hl ih => simp
  | swap x y l => simp
  | refl l => simp
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- The map `MTree → Tree` carries `PermRel` to permutations of lists. -/
private lemma permRel_map_mk_perm {l l' : List MTree} (h : PermRel l l') :
    (l.map (fun t : MTree => (Quotient.mk'' t : Tree))).Perm
      (l'.map (fun t : MTree => (Quotient.mk'' t : Tree))) := by
  induction h using permRel_ind with
  | nil => exact List.Perm.nil
  | cons hx hl ih =>
      simp only [List.map_cons]
      rw [mk_eq_of_iso hx]
      exact List.Perm.cons _ ih
  | swap x y l =>
      simp only [List.map_cons]
      exact List.Perm.swap _ _ _
  | refl l => exact List.Perm.refl _
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- A list which is `PermRel`-equivalent to a singleton is a singleton. -/
private lemma permRel_singleton_right {l : List MTree} {a₀ : MTree} (h : PermRel l [a₀]) :
    ∃ a, l = [a] ∧ Iso a a₀ := by
  have hp := permRel_map_mk_perm h
  have hlen : l.length = 1 := by
    have := hp.length_eq
    simpa using this
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨a, rfl, ?_⟩
  have hmem : (Quotient.mk'' a : Tree) ∈ [Quotient.mk'' a₀] := (List.Perm.mem_iff hp).mp (by simp)
  exact iso_of_mk_eq (by simpa using hmem)

/-- Every list of raw trees is `PermRel`-equivalent to the list of its nodes. -/
private lemma permRel_map_node_children (l : List MTree) :
    PermRel (l.map (fun b => MTree.node (MTree.children b))) l := by
  induction l with
  | nil => exact PermRel.nil
  | cons b l ih =>
      cases b with
      | node m => exact PermRel.cons (Iso.node (PermRel.refl m)) ih

/-- Every raw tree is isomorphic to the node on its list of children. -/
private lemma mk_node_children (t : MTree) :
    (Quotient.mk'' (MTree.node (MTree.children t)) : Tree) = Quotient.mk'' t := by
  cases t with
  | node l => rfl

theorem one_mul (x : Tree) : 1 * x = x := by
  -- The representative of `1` is a node with the single child `Quotient.out 0`, ...
  have hiso1 : Iso (Quotient.out (1 : Tree)) (MTree.node [Quotient.out (0 : Tree)]) :=
    iso_of_mk_eq ((Quotient.out_eq (1 : Tree)).trans rfl)
  -- ... and the representative of `0` is a node with no children.
  have h0iso : Iso (Quotient.out (0 : Tree)) (MTree.node []) :=
    iso_of_mk_eq ((Quotient.out_eq (0 : Tree)).trans rfl)
  -- Hence `Quotient.out 1` has exactly one child `t`, and `t` has no children.
  obtain ⟨t, ht, htis⟩ := permRel_singleton_right (PermRel.of_iso_children hiso1)
  have hc0 : MTree.children (Quotient.out (0 : Tree)) = [] :=
    (permRel_nil_iff (PermRel.of_iso_children h0iso)).mpr rfl
  have hct : MTree.children t = [] := by
    have h1 : PermRel (MTree.children t) (MTree.children (Quotient.out (0 : Tree))) :=
      PermRel.of_iso_children htis
    rw [hc0] at h1
    exact (permRel_nil_iff h1).mpr rfl
  -- The defining sum over the children of `1` therefore has a single term.
  have hflat : (MTree.children (Quotient.out (1 : Tree))).flatMap (fun a =>
      (MTree.children (Quotient.out x)).map (fun b =>
        MTree.node (MTree.children a ++ MTree.children b)))
      = (MTree.children (Quotient.out x)).map (fun b => MTree.node (MTree.children b)) := by
    rw [ht]
    simp [hct]
  have hmul : (1 : Tree) * x =
      Quotient.mk'' (MTree.node
        ((MTree.children (Quotient.out x)).map (fun b => MTree.node (MTree.children b)))) := by
    show Work.ORHughesFree.Tree.mul 1 x = _
    unfold Work.ORHughesFree.Tree.mul
    rw [hflat]
  -- And the node on the nodes on the children of `Quotient.out x` is `x` itself.
  rw [hmul]
  have hstep1 : Iso (MTree.node ((MTree.children (Quotient.out x)).map
        (fun b => MTree.node (MTree.children b))))
      (MTree.node (MTree.children (Quotient.out x))) :=
    Iso.node (permRel_map_node_children _)
  have hstep2 : Iso (MTree.node (MTree.children (Quotient.out x))) (Quotient.out x) :=
    iso_of_mk_eq (mk_node_children (Quotient.out x))
  exact (mk_eq_of_iso (Iso.trans hstep1 hstep2)).trans (Quotient.out_eq x)

end Work.ORHughesFree.Tree
