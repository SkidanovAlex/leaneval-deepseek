import Mathlib
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.Quotient.qpath_exists_lift

namespace Work.ORLocInd.CohenLyndon.Span

open Quiver
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## The quotient graph of a tree is connected

Every vertex orbit is reachable from any other by a path in the quotient graph `V/G`; this is the
only consequence of `V` being a tree that is used below. -/

theorem orbitV_nonempty_path' (hT : Work.ORBassSerre.IsTree V)
    (A B : Work.ORBassSerre.orbitV G V) : Nonempty (Quiver.Path A B) := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep A
  obtain ⟨b, rfl⟩ := Quotient.exists_rep B
  obtain ⟨p⟩ := hT.1 a b
  exact ⟨(Work.ORBassSerre.orbitPrefunctor (G := G) (V := V)).mapPath p⟩

/-! ## The BFS distance and a shortest path

`rank A` is the distance from the root orbit `root` to `A` in the quotient graph. -/

/-- The possible lengths of paths from `rt` to `A` in the quotient graph. -/
def pathLen (rt A : Work.ORBassSerre.orbitV G V) : ℕ → Prop :=
  fun n => ∃ p : Quiver.Path rt A, p.length = n

theorem exists_path_len (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    ∃ n, pathLen (G := G) (V := V) rt A n := by
  obtain ⟨p⟩ := orbitV_nonempty_path' (G := G) (V := V) hT rt A
  exact ⟨p.length, p, rfl⟩

/-- The distance from the root orbit `rt` to `A` in the quotient graph. -/
noncomputable def rank (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) : ℕ :=
  Nat.find (p := pathLen (G := G) (V := V) rt A) (exists_path_len (G := G) (V := V) hT rt A)

theorem rank_le_length (hT : Work.ORBassSerre.IsTree V) (rt : Work.ORBassSerre.orbitV G V)
    {A : Work.ORBassSerre.orbitV G V} (p : Quiver.Path rt A) :
    rank hT rt A ≤ p.length := by
  unfold rank
  exact Nat.find_min' _ (show pathLen (G := G) (V := V) rt A p.length from ⟨p, rfl⟩)

theorem exists_length_rank (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    ∃ p : Quiver.Path rt A, p.length = rank hT rt A := by
  unfold rank
  exact Nat.find_spec (p := pathLen (G := G) (V := V) rt A)
    (exists_path_len (G := G) (V := V) hT rt A)

/-- A path from the root orbit to `A` of minimal length. -/
noncomputable def shortestPath (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    Quiver.Path rt A :=
  Classical.choose (exists_length_rank (G := G) (V := V) hT rt A)

theorem shortestPath_length (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    (shortestPath hT rt A).length = rank hT rt A :=
  Classical.choose_spec (exists_length_rank (G := G) (V := V) hT rt A)

theorem exists_cons_of_length_pos {a b : V} {p : Quiver.Path a b} (h : 0 < p.length) :
    ∃ (c : V) (q : Quiver.Path a c) (e : c ⟶ b), p = q.cons e := by
  cases p with
  | nil => simp at h
  | cons q e => exact ⟨_, q, e, rfl⟩

theorem rank_root (hT : Work.ORBassSerre.IsTree V) (rt : Work.ORBassSerre.orbitV G V) :
    rank hT rt rt = 0 := by
  have h := rank_le_length hT rt (Quiver.Path.nil : Quiver.Path rt rt)
  simp only [Quiver.Path.length_nil] at h
  omega

theorem rank_eq_zero_iff (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    rank hT rt A = 0 ↔ A = rt := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_length_rank (G := G) (V := V) hT rt A
    cases p with
    | nil => rfl
    | cons q e => simp only [Quiver.Path.length_cons] at hp; omega
  · intro h
    rw [h]
    exact rank_root hT rt

/-! ## The parent map

For every orbit `A ≠ rt` we choose a *parent* `par A` of smaller rank together with the arrow of
the quotient graph joining them.  Iterating `par` strictly decreases `rank`, so it eventually
reaches the unique orbit of rank zero, i.e. the root. -/

/-- The chosen parent of an orbit `A ≠ rt`: an orbit of strictly smaller rank together with an
arrow of the quotient graph from the parent to `A`. -/
structure Parent (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) where
  src : Work.ORBassSerre.orbitV G V
  edge : src ⟶ A
  rank_lt : rank hT rt src < rank hT rt A

theorem exists_parent (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : Nonempty (Parent hT rt A) := by
  have hlen : (shortestPath hT rt A).length = rank hT rt A := shortestPath_length hT rt A
  have hpos : 0 < (shortestPath hT rt A).length := by
    rw [hlen]
    exact Nat.pos_of_ne_zero (fun h0 => hA ((rank_eq_zero_iff hT rt A).mp h0))
  obtain ⟨B, q, e, hq⟩ := exists_cons_of_length_pos hpos
  refine ⟨⟨B, e, ?_⟩⟩
  calc rank hT rt B ≤ q.length := rank_le_length hT rt q
    _ < rank hT rt A := by
        rw [← hlen, hq]
        simp [Quiver.Path.length_cons]

/-- The parent map of the spanning tree of the quotient graph: the previous vertex on a shortest
path from the root orbit.  It is the root itself on the root. -/
noncomputable def par (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    Work.ORBassSerre.orbitV G V :=
  if h : A = rt then rt else (Classical.choice (exists_parent hT rt A h)).src

theorem par_eq (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : par hT rt A = (Classical.choice (exists_parent hT rt A hA)).src := by
  rw [par, dif_neg hA]

theorem rank_par_lt (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : rank hT rt (par hT rt A) < rank hT rt A := by
  rw [par_eq hT rt A hA]
  exact (Classical.choice (exists_parent hT rt A hA)).rank_lt

/-- The edge of the quotient graph joining an orbit to its parent. -/
noncomputable def parentHom (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : par hT rt A ⟶ A :=
  (par_eq hT rt A hA).symm ▸ (Classical.choice (exists_parent hT rt A hA)).edge

/-! ## Lifting the parent edges to `V`

Given a prescribed source vertex in the orbit of the source of an arrow of the quotient graph,
there is an arrow of `V` with that source in the corresponding edge orbit. -/

theorem smul_left_total (g : G) (u : Quiver.Total V) : (g • u).left = g • u.left :=
  Work.ORBassSerre.GraphAction.smul_left g u

theorem smul_right_total (g : G) (u : Quiver.Total V) : (g • u).right = g • u.right :=
  Work.ORBassSerre.GraphAction.smul_right g u

theorem orbit_mk_left_eq {u w : Quiver.Total V}
    (h : (Quotient.mk'' u : Work.ORBassSerre.orbitE G V) = Quotient.mk'' w) :
    (Quotient.mk'' u.left : Work.ORBassSerre.orbitV G V) = Quotient.mk'' w.left := by
  have h' : u ∈ MulAction.orbit G w := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h'
  rw [← hg, smul_left_total]
  exact Quotient.sound ⟨g, rfl⟩

theorem orbit_mk_right_eq {u w : Quiver.Total V}
    (h : (Quotient.mk'' u : Work.ORBassSerre.orbitE G V) = Quotient.mk'' w) :
    (Quotient.mk'' u.right : Work.ORBassSerre.orbitV G V) = Quotient.mk'' w.right := by
  have h' : u ∈ MulAction.orbit G w := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h'
  rw [← hg, smul_right_total]
  exact Quotient.sound ⟨g, rfl⟩

theorem exists_smul_eq_of_mk_eq {x : V} {u : Quiver.Total V}
    (h : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = Quotient.mk'' u.left) :
    ∃ g : G, g • u.left = x :=
  MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))

/-- A translate of `u` whose source is the prescribed vertex `x`. -/
noncomputable def translateToSource (u : Quiver.Total V) (x : V)
    (h : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = Quotient.mk'' u.left) :
    Quiver.Total V :=
  Classical.choose (exists_smul_eq_of_mk_eq (G := G) (V := V) h) • u

theorem translateToSource_left (u : Quiver.Total V) (x : V)
    (h : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = Quotient.mk'' u.left) :
    (translateToSource u x h).left = x := by
  rw [translateToSource, smul_left_total]
  exact Classical.choose_spec (exists_smul_eq_of_mk_eq (G := G) (V := V) h)

theorem translateToSource_right_orbit (u : Quiver.Total V) (x : V)
    (h : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = Quotient.mk'' u.left) :
    (Quotient.mk'' (translateToSource u x h).right : Work.ORBassSerre.orbitV G V) =
      Quotient.mk'' u.right := by
  rw [translateToSource, smul_right_total]
  exact Quotient.sound ⟨Classical.choose (exists_smul_eq_of_mk_eq (G := G) (V := V) h), rfl⟩

/-- A representative arrow of an arrow orbit of the quotient graph. -/
noncomputable def reprTotal {A B : Work.ORBassSerre.orbitV G V} (e : A ⟶ B) : Quiver.Total V :=
  Quotient.out e.1

theorem mk_reprTotal {A B : Work.ORBassSerre.orbitV G V} (e : A ⟶ B) :
    (Quotient.mk'' (reprTotal e) : Work.ORBassSerre.orbitE G V) = e.1 :=
  Quotient.out_eq e.1

theorem mk_reprTotal_left {A B : Work.ORBassSerre.orbitV G V} (e : A ⟶ B) :
    (Quotient.mk'' (reprTotal e).left : Work.ORBassSerre.orbitV G V) = A := by
  obtain ⟨u, hu, hl, _⟩ := e.2
  exact (orbit_mk_left_eq ((mk_reprTotal e).trans hu.symm)).trans hl

theorem mk_reprTotal_right {A B : Work.ORBassSerre.orbitV G V} (e : A ⟶ B) :
    (Quotient.mk'' (reprTotal e).right : Work.ORBassSerre.orbitV G V) = B := by
  obtain ⟨u, hu, _, hr⟩ := e.2
  exact (orbit_mk_right_eq ((mk_reprTotal e).trans hu.symm)).trans hr

/-! ## The lifted spanning tree

`vertAux A` is a vertex of `V` lying in the orbit `A`, chosen so that the parent edge of `A` is
realised by an actual arrow of `V` joining `vert (par A)` to `vert A`.  This is a recursion along
the rank: the parent has strictly smaller rank. -/

/-- The lift of the parent edge of `A`, with prescribed source vertex `x`. -/
noncomputable def parentArrowAt (hT : Work.ORBassSerre.IsTree V) (rt : Work.ORBassSerre.orbitV G V)
    (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ rt) (x : V)
    (hx : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = par hT rt A) : Quiver.Total V :=
  translateToSource (reprTotal (parentHom hT rt A hA)) x
    (hx.trans (mk_reprTotal_left (parentHom hT rt A hA)).symm)

theorem parentArrowAt_left (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) (x : V) (hx : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = par hT rt A) :
    (parentArrowAt hT rt A hA x hx).left = x :=
  translateToSource_left _ _ _

theorem parentArrowAt_right_orbit (hT : Work.ORBassSerre.IsTree V)
    (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) (x : V) (hx : (Quotient.mk'' x : Work.ORBassSerre.orbitV G V) = par hT rt A) :
    (Quotient.mk'' (parentArrowAt hT rt A hA x hx).right : Work.ORBassSerre.orbitV G V) = A := by
  rw [parentArrowAt, translateToSource_right_orbit, mk_reprTotal_right]

/-- A vertex of `V` in the orbit `A`, obtained by lifting the tree of shortest paths from the root
orbit. -/
noncomputable def vertAux (hT : Work.ORBassSerre.IsTree V) (rt : Work.ORBassSerre.orbitV G V) :
    (A : Work.ORBassSerre.orbitV G V) → {v : V // Quotient.mk'' v = A}
  | A =>
    if h : A = rt then ⟨Quotient.out rt, (Quotient.out_eq rt).trans h.symm⟩
    else
      ⟨(parentArrowAt hT rt A h (vertAux hT rt (par hT rt A)).1
          (vertAux hT rt (par hT rt A)).2).right,
        parentArrowAt_right_orbit hT rt A h _ _⟩
  termination_by A => rank hT rt A
  decreasing_by exact rank_par_lt hT rt A h

theorem vertAux_eq_of_ne (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) :
    (vertAux hT rt A).1 =
      (parentArrowAt hT rt A hA (vertAux hT rt (par hT rt A)).1
        (vertAux hT rt (par hT rt A)).2).right := by
  conv_lhs => rw [vertAux]
  rw [dif_neg hA]

/-- The chosen lift of the vertex orbits by the spanning tree. -/
noncomputable def vert (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) : V :=
  (vertAux hT rt A).1

theorem vert_mk (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V) :
    Quotient.mk'' (vert hT rt A) = A :=
  (vertAux hT rt A).2

/-- The lift of the parent edge of `A` to an arrow of `V` from `vert (par A)` to `vert A`. -/
noncomputable def parArrow (hT : Work.ORBassSerre.IsTree V) (rt : Work.ORBassSerre.orbitV G V)
    (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ rt) : Quiver.Total V :=
  parentArrowAt hT rt A hA (vert hT rt (par hT rt A)) (vert_mk hT rt (par hT rt A))

theorem parArrow_left (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : (parArrow hT rt A hA).left = vert hT rt (par hT rt A) :=
  parentArrowAt_left hT rt A hA _ _

theorem parArrow_right (hT : Work.ORBassSerre.IsTree V) (rt A : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) : (parArrow hT rt A hA).right = vert hT rt A := by
  show (parentArrowAt hT rt A hA (vertAux hT rt (par hT rt A)).1
      (vertAux hT rt (par hT rt A)).2).right = (vertAux hT rt A).1
  exact (vertAux_eq_of_ne hT rt A hA).symm

/-- The edge orbits of the lifting arrows are pairwise distinct: two arrows of `V` in the same
orbit have targets in the same vertex orbit. -/
theorem parArrow_orbit_ne (hT : Work.ORBassSerre.IsTree V) (rt A B : Work.ORBassSerre.orbitV G V)
    (hA : A ≠ rt) (hB : B ≠ rt) (hAB : A ≠ B) :
    (Quotient.mk'' (parArrow hT rt A hA) : Work.ORBassSerre.orbitE G V) ≠
      Quotient.mk'' (parArrow hT rt B hB) := by
  intro h
  refine hAB ?_
  have h1 := orbit_mk_right_eq (G := G) (V := V) h
  rw [parArrow_right hT rt A hA, parArrow_right hT rt B hB, vert_mk hT rt A,
    vert_mk hT rt B] at h1
  exact h1

/-- **A spanning tree of the quotient graph, lifted to the tree `V`.**
Let `G` act without inversions on a tree `V` with finitely many orbits of vertices and of arrows.
Then there are lifts of the vertex orbits together with a "parent map" on the orbits whose
iterates reach the chosen root orbit, lifting arrows realising the parent edges, and a rank
function decreasing along the parent map; the edge orbits of the lifting arrows are pairwise
distinct.  Thus the chosen arrows form a spanning tree of the quotient graph `V/G`, lifted to a
subtree of `V` containing exactly one vertex from each vertex orbit. -/
theorem exists_spanningTree_lift {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (root : Work.ORBassSerre.orbitV G V) :
    ∃ (vert : Work.ORBassSerre.orbitV G V → V)
      (par : Work.ORBassSerre.orbitV G V → Work.ORBassSerre.orbitV G V)
      (rank : Work.ORBassSerre.orbitV G V → ℕ)
      (parArrow : (A : Work.ORBassSerre.orbitV G V) → A ≠ root → Quiver.Total V),
      (∀ A, Quotient.mk'' (vert A) = A) ∧
      (rank root = 0) ∧
      (∀ A, rank A = 0 ↔ A = root) ∧
      (∀ A, A ≠ root → rank (par A) < rank A) ∧
      (∀ (A : Work.ORBassSerre.orbitV G V) (hA : A ≠ root),
        (parArrow A hA).left = vert (par A) ∧ (parArrow A hA).right = vert A) ∧
      (∀ (A B : Work.ORBassSerre.orbitV G V) (hA : A ≠ root) (hB : B ≠ root), A ≠ B →
        (Quotient.mk'' (parArrow A hA) : Work.ORBassSerre.orbitE G V) ≠
          Quotient.mk'' (parArrow B hB)) := by
  exact ⟨vert hT root, par hT root, rank hT root, fun A hA => parArrow hT root A hA,
    vert_mk hT root, rank_root hT root, rank_eq_zero_iff hT root, rank_par_lt hT root,
    fun A hA => ⟨parArrow_left hT root A hA, parArrow_right hT root A hA⟩,
    fun A B hA hB hAB => parArrow_orbit_ne hT root A B hA hB hAB⟩

end Work.ORLocInd.CohenLyndon.Span
