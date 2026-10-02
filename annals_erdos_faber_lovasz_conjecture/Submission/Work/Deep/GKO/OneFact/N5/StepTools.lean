import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFactDefs

/-!
# Tools for the elementary N5 route: mates, alternating paths and their flips

This module is the vocabulary of the node N5b (`Work.Deep.GKO.OneFact.N5.completeInsideMatching`,
`EFL_N5_LEAD.md` §2).  The completion of a near-perfect *inside* matching `N` proceeds by walking
alternating paths `u -K- a -N- b -K- c -N- d -K- w` whose interior avoids the forbidden set `F`
and the "already used" set `W`, and then flipping them.

Contents:

* `nmate` — the unique `N`-neighbour of a vertex (`N` a matching), and its properties;
* `pairEq` — the unordered pair `{p,q}` as a binary relation;
* `StepPath` — the data of one such path together with the avoidance conditions;
* `StepPath.mate` — the mate function the flip induces (the path's new matching);
* `StepPath.flip` — the graph obtained from `M` by dropping the two `N`-edges of the path and
  adding the three `K`-edges;
* the basic lemmas about `flip`: adjacency, agreement with `M` away from the path, monotonicity,
  the matching property, and the effect on the uncovered set.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO.OneFact.N5

open Classical

noncomputable section

variable {n : ℕ}

/-! ## The mate of a matching -/

/-- The unique neighbour in `N` of a vertex, if it has one; the vertex itself otherwise. -/
noncomputable def nmate (N : SimpleGraph (Fin n)) (v : Fin n) : Fin n :=
  if h : ∃ w, N.Adj v w then Classical.choose h else v

theorem nmate_spec {N : SimpleGraph (Fin n)} {v : Fin n} (h : ∃ w, N.Adj v w) :
    N.Adj v (nmate N v) := by
  rw [nmate]; simp only [dif_pos h]; exact Classical.choose_spec h

theorem nmate_eq_self {N : SimpleGraph (Fin n)} {v : Fin n} (h : ∀ w, ¬ N.Adj v w) :
    nmate N v = v := by
  have h' : ¬ ∃ w, N.Adj v w := fun hh => hh.elim (fun w hw => h w hw)
  rw [nmate]; exact dif_neg h'

/-- If `N` is a matching, the mate of `v` is the unique `N`-neighbour of `v`. -/
theorem nmate_eq_of {N : SimpleGraph (Fin n)} (hN : Work.Deep.GKO.IsMatching' N) {v w : Fin n}
    (h : N.Adj v w) : nmate N v = w := by
  have h' := nmate_spec (N := N) ⟨w, h⟩
  exact hN v (nmate N v) w h' h

theorem nmate_invol {N : SimpleGraph (Fin n)} (hN : Work.Deep.GKO.IsMatching' N) {v : Fin n}
    (h : ∃ w, N.Adj v w) : nmate N (nmate N v) = v := by
  have h1 : N.Adj v (nmate N v) := nmate_spec h
  have h2 : N.Adj (nmate N v) v := (N.adj_comm v (nmate N v)).mp h1
  exact nmate_eq_of hN h2

theorem nmate_ne_self {N : SimpleGraph (Fin n)} {v : Fin n} (h : N.Adj v (nmate N v)) :
    nmate N v ≠ v := fun hh => N.loopless.1 v (by simpa [hh] using h)

theorem nmate_congr {N : SimpleGraph (Fin n)} (hN : Work.Deep.GKO.IsMatching' N) {v : Fin n}
    (h : ∃ w, N.Adj v w) : N.Adj (nmate N v) v :=
  (N.adj_comm v (nmate N v)).mp (nmate_spec h)

/-! ## The uncovered set -/

theorem mem_uncov_iff (M : SimpleGraph (Fin n)) (v : Fin n) :
    v ∈ uncov M ↔ ∀ w, ¬ M.Adj v w := by
  simp [uncov]

theorem not_mem_uncov_iff (M : SimpleGraph (Fin n)) (v : Fin n) :
    v ∉ uncov M ↔ ∃ w, M.Adj v w := by
  simp [mem_uncov_iff]

/-! ## The unordered pair as a relation -/

/-- `pairEq p q x y` means that `{x,y} = {p,q}`. -/
def pairEq (p q x y : Fin n) : Prop := (x = p ∧ y = q) ∨ (x = q ∧ y = p)

theorem pairEq_comm {p q x y : Fin n} (h : pairEq p q x y) : pairEq p q y x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

theorem not_pairEq_self {p q x : Fin n} (h : p ≠ q) : ¬ pairEq p q x x := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact h (h1.symm.trans h2)
  · exact h (h2.symm.trans h1)

/-! ## The step path -/

/-- The data of one step of the completion: six vertices `v 0, …, v 5` with
`v 0 -K- v 1 -N- v 2 -K- v 3 -N- v 4 -K- v 5`, pairwise distinct, the interior vertices
`v 1, …, v 4` avoiding `F`, `U'` and the "used" set `W`. -/
structure StepPath (N K : SimpleGraph (Fin n)) (F U' W : Finset (Fin n)) (u w : Fin n) where
  vert : Fin 6 → Fin n
  zero : vert 0 = u
  five : vert 5 = w
  inj : Function.Injective vert
  K01 : K.Adj (vert 0) (vert 1)
  N12 : N.Adj (vert 1) (vert 2)
  K23 : K.Adj (vert 2) (vert 3)
  N34 : N.Adj (vert 3) (vert 4)
  K45 : K.Adj (vert 4) (vert 5)
  avoid1 : vert 1 ∉ F ∧ vert 1 ∉ U' ∧ vert 1 ∉ W
  avoid2 : vert 2 ∉ F ∧ vert 2 ∉ U' ∧ vert 2 ∉ W
  avoid3 : vert 3 ∉ F ∧ vert 3 ∉ U' ∧ vert 3 ∉ W
  avoid4 : vert 4 ∉ F ∧ vert 4 ∉ U' ∧ vert 4 ∉ W

namespace StepPath

variable {N K : SimpleGraph (Fin n)} {F U' W : Finset (Fin n)} {u w : Fin n}

@[simp] theorem vert_eq_iff (P : StepPath N K F U' W u w) {i j : Fin 6} :
    P.vert i = P.vert j ↔ i = j := ⟨fun h => P.inj h, fun h => by rw [h]⟩

theorem vert_ne (P : StepPath N K F U' W u w) {i j : Fin 6} (h : i ≠ j) :
    P.vert i ≠ P.vert j := fun hh => h (P.inj hh)

/-- The six vertices of the path. -/
def sverts (P : StepPath N K F U' W u w) : Finset (Fin n) :=
  {P.vert 0, P.vert 1, P.vert 2, P.vert 3, P.vert 4, P.vert 5}

theorem vert_mem_sverts (P : StepPath N K F U' W u w) (i : Fin 6) : P.vert i ∈ P.sverts := by
  fin_cases i <;> simp [sverts]

theorem mem_sverts (P : StepPath N K F U' W u w) {x : Fin n} :
    x ∈ P.sverts ↔ x = P.vert 0 ∨ x = P.vert 1 ∨ x = P.vert 2 ∨ x = P.vert 3
      ∨ x = P.vert 4 ∨ x = P.vert 5 := by
  simp [sverts]

theorem notMem_sverts (P : StepPath N K F U' W u w) {x : Fin n} (hx : x ∉ P.sverts)
    {i : Fin 6} : x ≠ P.vert i := fun h => hx (h ▸ P.vert_mem_sverts i)

theorem pairEq_vert_iff (P : StepPath N K F U' W u w) {i j k : Fin 6} {y : Fin n} :
    pairEq (P.vert i) (P.vert j) (P.vert k) y ↔
      (k = i ∧ y = P.vert j) ∨ (k = j ∧ y = P.vert i) := by
  simp [pairEq, vert_eq_iff]

theorem pairEq_vert_false (P : StepPath N K F U' W u w) {i j k : Fin 6} {y : Fin n}
    (hik : i ≠ k) (hjk : j ≠ k) : ¬ pairEq (P.vert i) (P.vert j) (P.vert k) y := by
  rw [P.pairEq_vert_iff]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact hik h.symm
  · exact hjk h.symm

theorem pairEq_vert_self_left (P : StepPath N K F U' W u w) {i j : Fin 6} {y : Fin n}
    (h : pairEq (P.vert i) (P.vert j) (P.vert i) y) : y = P.vert j := by
  rw [P.pairEq_vert_iff] at h
  rcases h with ⟨-, h⟩ | ⟨hji, h⟩
  · exact h
  · rw [h, hji]

theorem pairEq_vert_self_right (P : StepPath N K F U' W u w) {i j : Fin 6} {y : Fin n}
    (h : pairEq (P.vert i) (P.vert j) (P.vert j) y) : y = P.vert i := by
  rw [P.pairEq_vert_iff] at h
  rcases h with ⟨hij, h⟩ | ⟨-, h⟩
  · rw [h, hij]
  · exact h

theorem not_pairEq_of_notMem_sverts (P : StepPath N K F U' W u w) {x y : Fin n}
    (hx : x ∉ P.sverts) {p q : Fin n} (hp : p ∈ P.sverts) (hq : q ∈ P.sverts) :
    ¬ pairEq p q x y := by
  rintro (⟨h1, -⟩ | ⟨h1, -⟩)
  · exact hx (by rw [h1]; exact hp)
  · exact hx (by rw [h1]; exact hq)

/-! ## The mate function induced by the flip -/

/-- The mate function of the flip: inside the path the pairs `(v0,v1)`, `(v2,v3)`, `(v4,v5)`
become matched, and everything else keeps its `M`-mate. -/
noncomputable def mate (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w)
    (x : Fin n) : Fin n :=
  if x = P.vert 0 then P.vert 1
  else if x = P.vert 1 then P.vert 0
  else if x = P.vert 2 then P.vert 3
  else if x = P.vert 3 then P.vert 2
  else if x = P.vert 4 then P.vert 5
  else if x = P.vert 5 then P.vert 4
  else nmate M x

theorem mate_vert0 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 0) = P.vert 1 := by simp [mate]

theorem mate_vert1 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 1) = P.vert 0 := by simp [mate]

theorem mate_vert2 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 2) = P.vert 3 := by simp [mate]

theorem mate_vert3 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 3) = P.vert 2 := by simp [mate]

theorem mate_vert4 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 4) = P.vert 5 := by simp [mate]

theorem mate_vert5 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    P.mate M (P.vert 5) = P.vert 4 := by simp [mate]

theorem mate_of_notMem {M : SimpleGraph (Fin n)} (P : StepPath N K F U' W u w) {x : Fin n}
    (hx : x ∉ P.sverts) : P.mate M x = nmate M x := by
  simp only [mate]
  rw [if_neg (P.notMem_sverts hx (i := 0)), if_neg (P.notMem_sverts hx (i := 1)),
      if_neg (P.notMem_sverts hx (i := 2)), if_neg (P.notMem_sverts hx (i := 3)),
      if_neg (P.notMem_sverts hx (i := 4)), if_neg (P.notMem_sverts hx (i := 5))]

/-! ## The flip -/

/-- The graph obtained from `M` by replacing the two `N`-edges of the path by the three `K`-edges. -/
noncomputable def flip (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    SimpleGraph (Fin n) where
  Adj x y := (M.Adj x y ∧ ¬ pairEq (P.vert 1) (P.vert 2) x y
      ∧ ¬ pairEq (P.vert 3) (P.vert 4) x y)
    ∨ pairEq (P.vert 0) (P.vert 1) x y ∨ pairEq (P.vert 2) (P.vert 3) x y
    ∨ pairEq (P.vert 4) (P.vert 5) x y
  symm := Std.Symm.mk (fun x y h => by
    rcases h with ⟨hM, h1, h2⟩ | h | h | h
    · exact Or.inl ⟨(M.adj_comm x y).mp hM, fun hh => h1 (pairEq_comm hh),
        fun hh => h2 (pairEq_comm hh)⟩
    · exact Or.inr (Or.inl (pairEq_comm h))
    · exact Or.inr (Or.inr (Or.inl (pairEq_comm h)))
    · exact Or.inr (Or.inr (Or.inr (pairEq_comm h))))
  loopless := Std.Irrefl.mk (fun x h => by
    rcases h with ⟨hM, -, -⟩ | h | h | h
    · exact M.loopless.1 x hM
    · exact (P.vert_ne (by decide : (0 : Fin 6) ≠ 1))
        (by rcases h with ⟨a, b⟩ | ⟨a, b⟩; exacts [a.symm.trans b, b.symm.trans a])
    · exact (P.vert_ne (by decide : (2 : Fin 6) ≠ 3))
        (by rcases h with ⟨a, b⟩ | ⟨a, b⟩; exacts [a.symm.trans b, b.symm.trans a])
    · exact (P.vert_ne (by decide : (4 : Fin 6) ≠ 5))
        (by rcases h with ⟨a, b⟩ | ⟨a, b⟩; exacts [a.symm.trans b, b.symm.trans a]))

theorem flip_adj (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) {x y : Fin n} :
    (P.flip M).Adj x y ↔ (M.Adj x y ∧ ¬ pairEq (P.vert 1) (P.vert 2) x y
        ∧ ¬ pairEq (P.vert 3) (P.vert 4) x y)
      ∨ pairEq (P.vert 0) (P.vert 1) x y ∨ pairEq (P.vert 2) (P.vert 3) x y
      ∨ pairEq (P.vert 4) (P.vert 5) x y := Iff.rfl

theorem flip_adj_01 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 0) (P.vert 1) := Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))

theorem flip_adj_10 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 1) (P.vert 0) := Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))

theorem flip_adj_23 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 2) (P.vert 3) := Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))

theorem flip_adj_32 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 3) (P.vert 2) := Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩)))

theorem flip_adj_45 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 4) (P.vert 5) := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem flip_adj_54 (M : SimpleGraph (Fin n)) (P : StepPath N K F U' W u w) :
    (P.flip M).Adj (P.vert 5) (P.vert 4) := Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- The flip stays inside the ambient graph `N ⊔ K`. -/
theorem flip_le {M : SimpleGraph (Fin n)} (hM : M ≤ N ⊔ K)
    (P : StepPath N K F U' W u w) : P.flip M ≤ N ⊔ K := by
  intro x y h
  rw [flip_adj] at h
  rcases h with ⟨h1, -, -⟩ | hk | hk | hk
  · exact hM h1
  · rw [pairEq] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr P.K01)
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr ((K.adj_comm _ _).mp P.K01))
  · rw [pairEq] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr P.K23)
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr ((K.adj_comm _ _).mp P.K23))
  · rw [pairEq] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr P.K45)
    · rw [h1, h2]; exact (SimpleGraph.sup_adj N K _ _).mpr (Or.inr ((K.adj_comm _ _).mp P.K45))

/-- Away from the six vertices of the path, the flip agrees with `M`. -/
theorem flip_agree {M : SimpleGraph (Fin n)} (P : StepPath N K F U' W u w) {x : Fin n}
    (hx : x ∉ P.sverts) (y : Fin n) : (P.flip M).Adj x y ↔ M.Adj x y := by
  rw [flip_adj]
  constructor
  · rintro (⟨h1, -, -⟩ | hk | hk | hk)
    · exact h1
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 0)
        (P.vert_mem_sverts 1))
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 2)
        (P.vert_mem_sverts 3))
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 4)
        (P.vert_mem_sverts 5))
  · intro h1
    exact Or.inl ⟨h1, P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 1)
      (P.vert_mem_sverts 2), P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 3)
      (P.vert_mem_sverts 4)⟩

/-- Every neighbour of `x` in the flip is its `mate`.  This is the crux of the matching property:
the two interior `M`-edges are dropped, the three `K`-edges are added, and the endpoints `v0`, `v5`
had no `M`-edge. -/
theorem flip_adj_eq_mate {M : SimpleGraph (Fin n)} (P : StepPath N K F U' W u w)
    (hM : Work.Deep.GKO.IsMatching' M) (h12 : M.Adj (P.vert 1) (P.vert 2))
    (h34 : M.Adj (P.vert 3) (P.vert 4)) (h0 : ∀ y, ¬ M.Adj (P.vert 0) y)
    (h5 : ∀ y, ¬ M.Adj (P.vert 5) y) {x y : Fin n} (h : (P.flip M).Adj x y) :
    y = P.mate M x := by
  rw [flip_adj] at h
  by_cases hx : x ∈ P.sverts
  · rcases P.mem_sverts.mp hx with h0x | h1x | h2x | h3x | h4x | h5x
    · subst h0x
      rw [P.mate_vert0]
      rcases h with ⟨h1, -, -⟩ | hk | hk | hk
      · exact absurd h1 (h0 y)
      · exact P.pairEq_vert_self_left hk
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
    · subst h1x
      rw [P.mate_vert1]
      rcases h with ⟨h1, hd1, -⟩ | hk | hk | hk
      · have hy : y = P.vert 2 := hM (P.vert 1) y (P.vert 2) h1 h12
        rw [hy] at hd1
        exact absurd (Or.inl ⟨rfl, rfl⟩ :
          pairEq (P.vert 1) (P.vert 2) (P.vert 1) (P.vert 2)) hd1
      · exact P.pairEq_vert_self_right hk
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
    · subst h2x
      rw [P.mate_vert2]
      rcases h with ⟨h1, hd1, -⟩ | hk | hk | hk
      · have hy : y = P.vert 1 := hM (P.vert 2) y (P.vert 1) h1
          ((M.adj_comm (P.vert 1) (P.vert 2)).mp h12)
        rw [hy] at hd1
        exact absurd (Or.inr ⟨rfl, rfl⟩ :
          pairEq (P.vert 1) (P.vert 2) (P.vert 2) (P.vert 1)) hd1
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact P.pairEq_vert_self_left hk
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
    · subst h3x
      rw [P.mate_vert3]
      rcases h with ⟨h1, -, hd2⟩ | hk | hk | hk
      · have hy : y = P.vert 4 := hM (P.vert 3) y (P.vert 4) h1 h34
        rw [hy] at hd2
        exact absurd (Or.inl ⟨rfl, rfl⟩ :
          pairEq (P.vert 3) (P.vert 4) (P.vert 3) (P.vert 4)) hd2
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact P.pairEq_vert_self_right hk
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
    · subst h4x
      rw [P.mate_vert4]
      rcases h with ⟨h1, -, hd2⟩ | hk | hk | hk
      · have hy : y = P.vert 3 := hM (P.vert 4) y (P.vert 3) h1
          ((M.adj_comm (P.vert 3) (P.vert 4)).mp h34)
        rw [hy] at hd2
        exact absurd (Or.inr ⟨rfl, rfl⟩ :
          pairEq (P.vert 3) (P.vert 4) (P.vert 4) (P.vert 3)) hd2
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact P.pairEq_vert_self_left hk
    · subst h5x
      rw [P.mate_vert5]
      rcases h with ⟨h1, -, -⟩ | hk | hk | hk
      · exact absurd h1 (h5 y)
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact absurd hk (P.pairEq_vert_false (by decide) (by decide))
      · exact P.pairEq_vert_self_right hk
  · rw [P.mate_of_notMem hx]
    rcases h with ⟨h1, -, -⟩ | hk | hk | hk
    · exact (nmate_eq_of hM h1).symm
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 0)
        (P.vert_mem_sverts 1))
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 2)
        (P.vert_mem_sverts 3))
    · exact absurd hk (P.not_pairEq_of_notMem_sverts (y := y) hx (P.vert_mem_sverts 4)
        (P.vert_mem_sverts 5))

/-- The flip of a matching is a matching. -/
theorem flip_matching {M : SimpleGraph (Fin n)} (P : StepPath N K F U' W u w)
    (hM : Work.Deep.GKO.IsMatching' M) (h12 : M.Adj (P.vert 1) (P.vert 2))
    (h34 : M.Adj (P.vert 3) (P.vert 4)) (h0 : ∀ y, ¬ M.Adj (P.vert 0) y)
    (h5 : ∀ y, ¬ M.Adj (P.vert 5) y) : Work.Deep.GKO.IsMatching' (P.flip M) := by
  intro x y y' h1 h2
  rw [P.flip_adj_eq_mate hM h12 h34 h0 h5 h1,
    P.flip_adj_eq_mate hM h12 h34 h0 h5 h2]

/-- The uncovered set of the flip: only the two endpoints of the path are covered by it. -/
theorem mem_uncov_flip {M : SimpleGraph (Fin n)} (P : StepPath N K F U' W u w) {x : Fin n} :
    x ∈ uncov (P.flip M) ↔ x ∈ uncov M ∧ x ∉ P.sverts := by
  constructor
  · intro hx
    have hxs : x ∉ P.sverts := by
      intro hmem
      obtain ⟨y, hy⟩ : ∃ y, (P.flip M).Adj x y := by
        rcases P.mem_sverts.mp hmem with h | h | h | h | h | h
        · exact ⟨P.vert 1, by rw [h]; exact P.flip_adj_01 M⟩
        · exact ⟨P.vert 0, by rw [h]; exact P.flip_adj_10 M⟩
        · exact ⟨P.vert 3, by rw [h]; exact P.flip_adj_23 M⟩
        · exact ⟨P.vert 2, by rw [h]; exact P.flip_adj_32 M⟩
        · exact ⟨P.vert 5, by rw [h]; exact P.flip_adj_45 M⟩
        · exact ⟨P.vert 4, by rw [h]; exact P.flip_adj_54 M⟩
      exact (mem_uncov_iff (P.flip M) x).mp hx y hy
    refine ⟨?_, hxs⟩
    rw [mem_uncov_iff]
    intro y hy
    exact (mem_uncov_iff (P.flip M) x).mp hx y ((P.flip_agree hxs y).mpr hy)
  · rintro ⟨hx, hxs⟩
    rw [mem_uncov_iff] at hx ⊢
    intro y hy
    exact hx y ((P.flip_agree hxs y).mp hy)

end StepPath

/-! ## Families of step paths -/

/-- `γ i` is a valid alternating path from `φ i` to `ψ i` with interior avoiding `F` and `U'`. -/
structure Good (N K : SimpleGraph (Fin n)) (F U' : Finset (Fin n)) {a : ℕ}
    (φ ψ : Fin a → Fin n) (γ : Fin a → Fin 6 → Fin n) (i : Fin a) : Prop where
  inj : Function.Injective (γ i)
  zero : γ i 0 = φ i
  five : γ i 5 = ψ i
  K01 : K.Adj (γ i 0) (γ i 1)
  N12 : N.Adj (γ i 1) (γ i 2)
  K23 : K.Adj (γ i 2) (γ i 3)
  N34 : N.Adj (γ i 3) (γ i 4)
  K45 : K.Adj (γ i 4) (γ i 5)
  avoid : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → γ i j ∉ F ∧ γ i j ∉ U'

/-- The first `k` paths of a family are good and have pairwise disjoint interiors. -/
structure PathFam (N K : SimpleGraph (Fin n)) (F U' : Finset (Fin n)) {a : ℕ}
    (φ ψ : Fin a → Fin n) (k : ℕ) (γ : Fin a → Fin 6 → Fin n) : Prop where
  good : ∀ i, i.val < k → Good N K F U' φ ψ γ i
  disj : ∀ i i' j j', i.val < k → i'.val < k → j ≠ 0 → j ≠ 5 → j' ≠ 0 → j' ≠ 5 →
    γ i j = γ i' j' → i = i'

/-- The six vertices of a raw path. -/
def vset {a : ℕ} (γ : Fin a → Fin 6 → Fin n) (i : Fin a) : Finset (Fin n) :=
  {γ i 0, γ i 1, γ i 2, γ i 3, γ i 4, γ i 5}

/-- The union of the interiors of the first `k` paths. -/
def usedW {a : ℕ} (γ : Fin a → Fin 6 → Fin n) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin a => i.val < k)).biUnion
    fun i => ({γ i 1, γ i 2, γ i 3, γ i 4} : Finset (Fin n))

/-- The union of all vertices of the first `k` paths. -/
def usedV {a : ℕ} (γ : Fin a → Fin 6 → Fin n) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin a => i.val < k)).biUnion fun i => vset γ i

/-- The endpoints of the first `k` paths. -/
def pairsAbove {a : ℕ} (φ ψ : Fin a → Fin n) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin a => i.val < k)).biUnion fun i => ({φ i, ψ i} : Finset (Fin n))

theorem mem_usedW {a : ℕ} {γ : Fin a → Fin 6 → Fin n} {k : ℕ} {x : Fin n} :
    x ∈ usedW γ k ↔ ∃ i : Fin a, i.val < k ∧ (x = γ i 1 ∨ x = γ i 2 ∨ x = γ i 3 ∨ x = γ i 4) := by
  simp [usedW, or_assoc]

theorem mem_usedV {a : ℕ} {γ : Fin a → Fin 6 → Fin n} {k : ℕ} {x : Fin n} :
    x ∈ usedV γ k ↔ ∃ i : Fin a, i.val < k ∧ x ∈ vset γ i := by
  simp [usedV]

theorem mem_vset {a : ℕ} {γ : Fin a → Fin 6 → Fin n} {i : Fin a} {x : Fin n} :
    x ∈ vset γ i ↔ x = γ i 0 ∨ x = γ i 1 ∨ x = γ i 2 ∨ x = γ i 3 ∨ x = γ i 4 ∨ x = γ i 5 := by
  simp [vset]

theorem mem_pairsAbove {a : ℕ} {φ ψ : Fin a → Fin n} {k : ℕ} {x : Fin n} :
    x ∈ pairsAbove φ ψ k ↔ ∃ i : Fin a, i.val < k ∧ (x = φ i ∨ x = ψ i) := by
  simp [pairsAbove]

/-- The interiors of `k` paths use at most `4k` vertices. -/
theorem usedW_card {a : ℕ} (γ : Fin a → Fin 6 → Fin n) (k : ℕ) : (usedW γ k).card ≤ 4 * k := by
  have hsum : (usedW γ k).card
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin a => i.val < k),
          ({γ i 1, γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card :=
    Finset.card_biUnion_le
  have hfib : ∀ i : Fin a, ({γ i 1, γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card ≤ 4 := by
    intro i
    have h1 : ({γ i 1, γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card
        ≤ ({γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card
        ≤ ({γ i 3, γ i 4} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
    have h3 : ({γ i 3, γ i 4} : Finset (Fin n)).card
        ≤ ({γ i 4} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
    simp only [Finset.card_singleton] at h3
    omega
  have hfilter : (Finset.univ.filter (fun i : Fin a => i.val < k)).card ≤ k := by
    have h := Finset.card_le_card (s := (Finset.univ.filter (fun i : Fin a => i.val < k)).image Fin.val)
      (t := Finset.range k) (by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Finset.mem_range]
        exact hi)
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h
    simpa using h
  calc (usedW γ k).card
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin a => i.val < k),
          ({γ i 1, γ i 2, γ i 3, γ i 4} : Finset (Fin n)).card := hsum
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin a => i.val < k), 4 :=
        Finset.sum_le_sum fun i _ => hfib i
    _ = 4 * (Finset.univ.filter (fun i : Fin a => i.val < k)).card := by
        rw [Finset.sum_const, smul_eq_mul]; ring
    _ ≤ 4 * k := Nat.mul_le_mul_left 4 hfilter

/-- A good path can be viewed as a `StepPath` with empty forbidden set. -/
def Good.toStepPath {N K : SimpleGraph (Fin n)} {F U' : Finset (Fin n)} {a : ℕ}
    {φ ψ : Fin a → Fin n} {γ : Fin a → Fin 6 → Fin n} {i : Fin a}
    (h : Good N K F U' φ ψ γ i) : StepPath N K F U' ∅ (φ i) (ψ i) where
  vert := γ i
  zero := h.zero
  five := h.five
  inj := h.inj
  K01 := h.K01
  N12 := h.N12
  K23 := h.K23
  N34 := h.N34
  K45 := h.K45
  avoid1 := ⟨(h.avoid 1 (by decide) (by decide)).1, (h.avoid 1 (by decide) (by decide)).2, by simp⟩
  avoid2 := ⟨(h.avoid 2 (by decide) (by decide)).1, (h.avoid 2 (by decide) (by decide)).2, by simp⟩
  avoid3 := ⟨(h.avoid 3 (by decide) (by decide)).1, (h.avoid 3 (by decide) (by decide)).2, by simp⟩
  avoid4 := ⟨(h.avoid 4 (by decide) (by decide)).1, (h.avoid 4 (by decide) (by decide)).2, by simp⟩

end

end Work.Deep.GKO.OneFact.N5
