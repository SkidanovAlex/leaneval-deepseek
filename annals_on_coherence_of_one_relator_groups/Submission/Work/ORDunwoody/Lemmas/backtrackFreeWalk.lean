/-
Copyright: work of the ORDunwoody subproject (node N13).

# Closed walks without immediate backtracking in an acyclic graph

A walk `w` of a graph is *backtrack free* (`SimpleGraph.Walk.BacktrackFree`) if no two
consecutive darts of `w` are reverses of one another.  The main result of this file is
`walk_eq_nil_of_backtrackFree_of_isAcyclic`: in an acyclic graph every closed backtrack free
walk is trivial.

The proof is by minimality.  Let `w : Walk a a` be a shortest non-trivial closed backtrack
free walk.  Then no proper closed subwalk of `w` is non-trivial, so the vertices
`w.getVert 1, …, w.getVert w.length` are pairwise distinct.  The first edge of `w` and the
"long way round" `(w.drop 1).reverse` are then two distinct paths from `w.getVert 0` to
`w.getVert 1`, contradicting acyclicity (which says that any two paths with the same
endpoints are equal).
-/
import Mathlib
import Submission.Work.ORDunwoody.Lemmas.GraphQuiver

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type u}

/-- A chain property is inherited by contiguous sublists. -/
theorem List.IsChain.of_isInfix {α : Type*} {R : α → α → Prop} {l l' : List α}
    (h : l.IsChain R) (hinf : l' <:+: l) : l'.IsChain R := by
  obtain ⟨l₁, l₂, rfl⟩ := hinf
  exact (List.isChain_append.mp (List.isChain_append.mp h).1).2.1

/-- `BacktrackFree` is inherited by contiguous subwalks. -/
theorem SimpleGraph.Walk.BacktrackFree.of_isSubwalk {G : SimpleGraph V} {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} (h : p.IsSubwalk q) (hq : q.BacktrackFree) :
    p.BacktrackFree :=
  List.IsChain.of_isInfix hq h.darts_isInfix

/-- A list of the form `l₁ ++ x :: s x :: l₂` is not a chain for `fun a b => b ≠ s a`. -/
theorem List.not_isChain_cons_invol {α : Type*} (s : α → α) (l₁ l₂ : List α) (x : α) :
    ¬ (l₁ ++ x :: s x :: l₂).IsChain (fun a b => b ≠ s a) := by
  intro h
  obtain ⟨-, h2, -⟩ := List.isChain_append.mp h
  have h3 := (List.isChain_cons.mp h2).1
  have h4 : s x ∈ (s x :: l₂).head? := by simp
  exact h3 (s x) h4 rfl

/-- A walk whose dart list is `l₁ ++ d :: d.symm :: l₂` is not backtrack free. -/
theorem SimpleGraph.Walk.not_backtrackFree_of_darts {G : SimpleGraph V} {a b : V}
    {w : G.Walk a b} {l₁ l₂ : List G.Dart} {d : G.Dart}
    (h : w.darts = l₁ ++ d :: d.symm :: l₂) : ¬ w.BacktrackFree := by
  rw [SimpleGraph.Walk.BacktrackFree, h]
  exact List.not_isChain_cons_invol Dart.symm l₁ l₂ d

/-- A walk containing a two-step `u → v → u` is not backtrack free. -/
theorem SimpleGraph.Walk.not_backtrackFree_of_append_toWalk_symm {G : SimpleGraph V}
    {a b u v : V} (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk u b) :
    ¬ (A.append (h.toWalk.append (h.symm.toWalk.append B))).BacktrackFree := by
  intro hbf
  rw [SimpleGraph.Walk.BacktrackFree] at hbf
  have h1 : (A.append (h.toWalk.append (h.symm.toWalk.append B))).darts
      = A.darts ++ (⟨(u, v), h⟩ : G.Dart) :: (⟨(u, v), h⟩ : G.Dart).symm :: B.darts := by
    simp [SimpleGraph.Walk.darts_append, SimpleGraph.Adj.darts_toWalk, SimpleGraph.Dart.symm_mk]
  rw [h1] at hbf
  exact List.not_isChain_cons_invol Dart.symm A.darts B.darts (⟨(u, v), h⟩ : G.Dart) hbf

/-- A single-edge walk is a path. -/
theorem SimpleGraph.Walk.toWalk_isPath {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    h.toWalk.IsPath :=
  SimpleGraph.Walk.IsPath.mk' (by
    rw [SimpleGraph.Adj.support_toWalk]
    simp [h.ne])

/-- A list is `Nodup` if equal entries have equal indices. -/
theorem List.nodup_of_getElem_inj {α : Type*} {l : List α}
    (h : ∀ i j (_ : i < l.length) (_ : j < l.length), l[i] = l[j] → i = j) : l.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  exact Fin.ext (h i.1 j.1 i.2 j.2 (by simpa [List.get_eq_getElem] using hij))

/-- In an acyclic graph, a closed backtrack free walk is trivial. -/
theorem walk_eq_nil_of_backtrackFree_of_isAcyclic {G : SimpleGraph V} {a : V}
    (w : G.Walk a a) (hG : G.IsAcyclic) (hw : w.BacktrackFree) : w = SimpleGraph.Walk.nil := by
  suffices h : ∀ n, ∀ {a : V} (w : G.Walk a a), w.length ≤ n → w.BacktrackFree →
      w = SimpleGraph.Walk.nil from h w.length w le_rfl hw
  intro n
  induction n with
  | zero =>
    intro a w hlen _
    exact SimpleGraph.Walk.eq_nil_iff_nil.mpr
      (SimpleGraph.Walk.length_eq_zero_iff.mp (Nat.le_zero.mp hlen))
  | succ n ih =>
    intro a w hlen hw
    rcases Nat.lt_or_eq_of_le hlen with hlt | heq
    · exact ih w (Nat.lt_succ_iff.mp hlt) hw
    · by_contra hne
      have hL1 : w.length ≠ 1 := fun h1 =>
        G.irrefl (SimpleGraph.Walk.adj_of_length_eq_one h1)
      have hL2 : w.length ≠ 2 := by
        intro h2
        match w with
        | .cons h p =>
          have hp : p.length = 1 := by
            simp only [SimpleGraph.Walk.length_cons] at h2 ⊢
            omega
          match p with
          | .nil => exact absurd hp (by simp)
          | .cons h' p' =>
            have hp' : p'.length = 0 := by
              simp only [SimpleGraph.Walk.length_cons] at hp ⊢
              omega
            have hv : _ = _ := SimpleGraph.Walk.eq_of_length_eq_zero hp'
            subst hv
            have hd : (⟨(_, _), h'⟩ : G.Dart) = (⟨(_, _), h⟩ : G.Dart).symm :=
              SimpleGraph.Dart.ext _ _ (by simp [SimpleGraph.Dart.symm_mk])
            exact absurd hw (SimpleGraph.Walk.not_backtrackFree_of_darts (l₁ := [])
              (l₂ := p'.darts) (d := (⟨(_, _), h⟩ : G.Dart)) (by
                simp only [SimpleGraph.Walk.darts_cons, hd, List.nil_append, List.cons_append]))
      have h3 : 3 ≤ w.length := by omega
      -- any closed backtrack free walk shorter than `w` is trivial
      have key : ∀ {c : V} (z : G.Walk c c), z.length ≤ n → z.BacktrackFree →
          z = SimpleGraph.Walk.nil := fun z hz hzb => ih z hz hzb
      have hsuplen : (w.drop 1).support.length = w.length := by
        rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.drop_length]
        omega
      -- the vertices `w.getVert 1, …, w.getVert w.length` are pairwise distinct
      have hnodup : (w.drop 1).support.Nodup := by
        refine List.nodup_of_getElem_inj ?_
        intro i j hi hj hij
        by_contra hne_ij
        have hiLen : i ≤ (w.drop 1).length := by
          rw [SimpleGraph.Walk.length_support] at hi
          exact Nat.lt_succ_iff.mp hi
        have hjLen : j ≤ (w.drop 1).length := by
          rw [SimpleGraph.Walk.length_support] at hj
          exact Nat.lt_succ_iff.mp hj
        have hEq : w.getVert (i + 1) = w.getVert (j + 1) := by
          have h1 : (w.drop 1).getVert i = (w.drop 1).getVert j := by
            rw [SimpleGraph.Walk.getVert_eq_support_getElem _ hiLen,
              SimpleGraph.Walk.getVert_eq_support_getElem _ hjLen]
            exact hij
          rw [SimpleGraph.Walk.drop_getVert, SimpleGraph.Walk.drop_getVert] at h1
          simpa [Nat.add_comm] using h1
        have aux : ∀ p q : ℕ, 1 ≤ p → p < q → q ≤ w.length → w.getVert p = w.getVert q → False := by
          intro p q hp1 hpq hq hpqeq
          have hclosed : ((w.drop p).take (q - p)).length = q - p := by
            rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, min_eq_left]
            omega
          have hzbf : ((w.drop p).take (q - p)).BacktrackFree :=
            SimpleGraph.Walk.BacktrackFree.of_isSubwalk
              (SimpleGraph.Walk.IsSubwalk.trans (SimpleGraph.Walk.isSubwalk_take _ _)
                (SimpleGraph.Walk.isSubwalk_drop _ _)) hw
          have hzEq : (w.drop p).getVert (q - p) = w.getVert p := by
            rw [SimpleGraph.Walk.drop_getVert]
            have hpq' : p + (q - p) = q := by omega
            rw [hpq', hpqeq]
          have hzKey : (((w.drop p).take (q - p)).copy rfl hzEq) = SimpleGraph.Walk.nil :=
            key _ (by rw [SimpleGraph.Walk.length_copy, hclosed]; omega) (by
              rw [SimpleGraph.Walk.BacktrackFree, SimpleGraph.Walk.darts_copy]
              exact hzbf)
          have h0 : ((w.drop p).take (q - p)).length = 0 := by
            have hh := congrArg SimpleGraph.Walk.length hzKey
            rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_nil] at hh
            exact hh
          have : q - p = 0 := by rw [← hclosed]; exact h0
          omega
        rcases lt_or_gt_of_ne hne_ij with hlt | hgt
        · exact aux (i + 1) (j + 1) (by omega) (by omega) (by omega) hEq
        · exact aux (j + 1) (i + 1) (by omega) (by omega) (by omega) hEq.symm
      -- the first edge and the long way round are two paths with the same endpoints
      have hpos : 0 < w.length := by omega
      have hP1 : ((w.adj_getVert_succ hpos).toWalk).IsPath :=
        SimpleGraph.Walk.toWalk_isPath _
      have hP2 : (((w.drop 1).reverse).copy (w.getVert_zero).symm rfl).IsPath := by
        rw [SimpleGraph.Walk.isPath_copy]
        exact (SimpleGraph.Walk.IsPath.mk' hnodup).reverse
      have hq : (⟨(w.adj_getVert_succ hpos).toWalk, hP1⟩ : G.Path (w.getVert 0) (w.getVert 1))
          = ⟨((w.drop 1).reverse).copy (w.getVert_zero).symm rfl, hP2⟩ :=
        (hG.subsingleton_path (w.getVert 0) (w.getVert 1)).elim _ _
      have hlen : ((w.adj_getVert_succ hpos).toWalk).length
          = (((w.drop 1).reverse).copy (w.getVert_zero).symm rfl).length :=
        congrArg (fun p : G.Path (w.getVert 0) (w.getVert 1) => p.1.length) hq
      have h1 : ((w.adj_getVert_succ hpos).toWalk).length = 1 := SimpleGraph.Adj.length_toWalk _
      have h2 : (((w.drop 1).reverse).copy (w.getVert_zero).symm rfl).length = w.length - 1 := by
        rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
          SimpleGraph.Walk.drop_length]
      rw [h1, h2] at hlen
      omega

end Work.ORDunwoody.Lemmas
