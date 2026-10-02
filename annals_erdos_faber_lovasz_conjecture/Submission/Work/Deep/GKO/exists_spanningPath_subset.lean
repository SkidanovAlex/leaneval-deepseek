import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.spanningDefs
import Submission.Work.Deep.GKO.subsetDefs
import Submission.Work.Deep.GKO.card_lt_of_independent

/-!
# A spanning path inside a lower-regular vertex set

This file proves `Work.Deep.GKO.exists_spanningPath_subset`: if `G` is lower `(p,ε)`-regular
inside `U`, every vertex of `U` has at least `α|U|` neighbours in `U`, and `ε ≪ α ≪ p` with
`1 ≤ ε|U|`, then any two distinct `a, b ∈ U` are joined by a path of `G` with vertex set
exactly `U` (a Hamiltonian path of `G[U]` with prescribed endpoints).

The proof is the Chvátal–Erdős style argument: `κ(G[U]) ≥ (α-ε)|U| > 2ε|U| + 1 ≥ α(G[U])`,
and a longest `a`–`b`-path `P = v₀…v_k` can be extended using a component `D` of `G[U ∖ V(P)]`
and its neighbourhood `T` on `P` (inserting a `D`-path into `P` between consecutive vertices,
or reversing a middle segment of `P` via a chord).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO

noncomputable section

open Classical

open compFinsetLemmas

variable {n : ℕ}

/-! ## Basic facts about `PathListIn` -/

lemma PathListIn.head_eq {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {l : List (Fin n)} (h : PathListIn G U a b l) (hne : l ≠ []) : l.head hne = a := by
  obtain ⟨ys, hy⟩ := List.head?_eq_some_iff.mp h.head?_eq
  subst hy
  rfl

lemma PathListIn.getLast_eq {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {l : List (Fin n)} (h : PathListIn G U a b l) (hne : l ≠ []) : l.getLast hne = b := by
  obtain ⟨ys, hy⟩ := List.getLast?_eq_some_iff.mp h.getLast?_eq
  subst hy
  exact List.getLast_concat

lemma PathListIn.last_getElem {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {l : List (Fin n)} (h : PathListIn G U a b l) (hpos : 0 < l.length) :
    l[l.length - 1] = b := by
  have h1 : l[l.length - 1]? = some b := by
    rw [← List.getLast?_eq_getElem?]
    exact h.getLast?_eq
  exact (List.getElem?_eq_some_iff.mp h1).2

/-! ## Paths inside a connected component -/

/-- Two vertices of the same component are joined inside that component by a path list. -/
lemma compFinset_exists_pathList {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)} {z x y : Fin n}
    (hx : x ∈ compFinset G Z z) (hy : y ∈ compFinset G Z z) :
    ∃ l : List (Fin n), PathListIn G (compFinset G Z z) x y l := by
  have hxr : ReachIn G Z z x := mem_compFinset.mp hx
  have hyr : ReachIn G Z z y := mem_compFinset.mp hy
  obtain ⟨l, hl⟩ := (ReachIn.trans (ReachIn.symm hxr) hyr).exists_pathList
  exact ⟨l, hl.nodup, hl.isChain, hl.head?_eq, hl.getLast?_eq,
    fun v hv => list_forall_mem_of_closed
      (fun a ha b hb hab => compFinset_closed ha hb hab) hl.isChain
      (fun x hx => hl.mem_U hx) hx hl.head?_eq hv⟩

/-! ## Lower regularity produces edges between large sets -/

lemma exists_adj_of_lowerReg {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε : ℝ}
    (hlr : LowerRegOn G U p ε) (hεp : ε < p) (hεN : 0 < ε * (U.card : ℝ))
    {A B : Finset (Fin n)} (hAU : A ⊆ U) (hBU : B ⊆ U) (hd : Disjoint A B)
    (hAc : ε * (U.card : ℝ) ≤ (A.card : ℝ)) (hBc : ε * (U.card : ℝ) ≤ (B.card : ℝ)) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  have hkey := hlr A B hAU hBU hd hAc hBc
  have hcross : 0 < crossEdges G A B := by
    by_contra hcon
    rw [Nat.not_lt] at hcon
    have hcon' : (crossEdges G A B : ℝ) ≤ 0 := by exact_mod_cast hcon
    have hApos : 0 < (A.card : ℝ) := lt_of_lt_of_le hεN hAc
    have hBpos : 0 < (B.card : ℝ) := lt_of_lt_of_le hεN hBc
    have hpos : 0 < (p - ε) * (A.card : ℝ) * (B.card : ℝ) :=
      mul_pos (mul_pos (by linarith) hApos) hBpos
    linarith
  unfold crossEdges at hcross
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hcross
  rw [Finset.mem_filter] at hq
  obtain ⟨hqmem, hqadj⟩ := hq
  obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp hqmem
  exact ⟨q.1, hqA, q.2, hqB, hqadj⟩

/-- `nbrIn` is the cardinality of the filtered neighbourhood. -/
lemma nbrIn_eq_filter_card (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) :
    nbrIn G U v = (U.filter (fun w => G.Adj v w)).card := by
  have h : ((U.filter (fun w => G.Adj v w) : Finset (Fin n)) : Set (Fin n))
      = G.neighborSet v ∩ (U : Set (Fin n)) := by
    ext w
    simp [Finset.mem_filter, SimpleGraph.mem_neighborSet, and_comm]
  rw [nbrIn, ← h, Set.ncard_coe_finset]

/-! ## Connectivity after deleting few vertices -/

lemma reachIn_after_delete_aux {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε α : ℝ}
    (h : SpanHyp G U p ε α) {S : Finset (Fin n)} (hSU : S ⊆ U)
    (hS : (S.card : ℝ) < α * (U.card : ℝ) - ε * (U.card : ℝ))
    {x y : Fin n} (hx : x ∈ U) (hxs : x ∉ S) (hy : y ∈ U) (hys : y ∉ S) :
    ReachIn G (U \ S) x y := by
  set Z : Finset (Fin n) := U \ S with hZdef
  have hxZ : x ∈ Z := Finset.mem_sdiff.mpr ⟨hx, hxs⟩
  have hyZ : y ∈ Z := Finset.mem_sdiff.mpr ⟨hy, hys⟩
  by_contra hcon
  have hy_notin : y ∉ compFinset G Z x := fun hc => hcon (mem_compFinset.mp hc)
  have hdisj : Disjoint (compFinset G Z x) (compFinset G Z y) :=
    compFinset_disjoint (G := G) (Z := Z) hy_notin
  have hnotadj : ∀ a ∈ compFinset G Z x, ∀ b ∈ compFinset G Z y, ¬ G.Adj a b :=
    fun a ha b hb => compFinset_not_adj (G := G) (Z := Z) hy_notin ha hb
  -- every component of `Z` has more than `ε|U|` vertices
  have size_ge : ∀ z' : Fin n, z' ∈ Z → ε * (U.card : ℝ) ≤ ((compFinset G Z z').card : ℝ) := by
    intro z' hz'
    obtain ⟨v, hv⟩ := compFinset_nonempty hz'
    have hvU : v ∈ U := (Finset.mem_sdiff.mp (compFinset_subset hv)).1
    have hdeg : α * (U.card : ℝ) ≤ (nbrIn G U v : ℝ) := h.minDeg v hvU
    have hbound : nbrIn G U v ≤ (compFinset G Z z').card + S.card := by
      rw [nbrIn_eq_filter_card]
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro w hw
      obtain ⟨hwU, hwadj⟩ := Finset.mem_filter.mp hw
      by_cases hwS : w ∈ S
      · exact Finset.mem_union_right _ hwS
      · exact Finset.mem_union_left _ (compFinset_closed hv (Finset.mem_sdiff.mpr ⟨hwU, hwS⟩) hwadj)
    have hbound' : (nbrIn G U v : ℝ) ≤ ((compFinset G Z z').card : ℝ) + (S.card : ℝ) := by
      exact_mod_cast hbound
    linarith [hS]
  have hAU : compFinset G Z x ⊆ U :=
    fun v hv => (Finset.mem_sdiff.mp (compFinset_subset hv)).1
  have hBU : compFinset G Z y ⊆ U :=
    fun v hv => (Finset.mem_sdiff.mp (compFinset_subset hv)).1
  obtain ⟨a, ha, b, hb, hab⟩ := exists_adj_of_lowerReg h.lr h.eps_lt_p h.epsN_pos
    hAU hBU hdisj (size_ge x hxZ) (size_ge y hyZ)
  exact hnotadj a ha b hb hab




lemma head?_eq_some_head {α : Type*} {l : List α} (h : l ≠ []) : l.head? = some (l.head h) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

lemma getLast?_eq_some_getLast {α : Type*} {l : List α} (h : l ≠ []) :
    l.getLast? = some (l.getLast h) := by
  rw [List.getLast?_eq_getElem?, List.getLast_eq_getElem h,
    List.getElem?_eq_getElem (by have := List.length_pos_iff.mpr h; omega)]

lemma take_getLast? {P : List (Fin n)} {k : ℕ} (hk : k + 1 < P.length) :
    (P.take (k+1)).getLast? = some (P.get ⟨k, by omega⟩) := by
  rw [List.getLast?_take, if_neg (by omega : ¬ (k+1 = 0)), Nat.add_sub_cancel,
    List.getElem?_eq_getElem (by omega)]
  rfl

lemma drop_head? {P : List (Fin n)} {k : ℕ} (hk : k + 1 < P.length) :
    (P.drop (k+1)).head? = some (P.get ⟨k+1, by omega⟩) := by
  rw [List.head?_drop, List.getElem?_eq_getElem (by omega)]
  rfl

lemma take_drop_disjoint (P : List (Fin n)) (hP : P.Nodup) (k : ℕ) :
    ∀ x ∈ P.take k, x ∉ P.drop k := by
  intro x hx hx'
  have hPn : (P.take k ++ P.drop k).Nodup := by rw [List.take_append_drop]; exact hP
  exact (List.nodup_append.mp hPn).2.2 x hx x hx' rfl

-- the first surgery: insert D between positions i and i+1
lemma insert_pathList_aux {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {P D : List (Fin n)} {i : ℕ}
    (hP : PathListIn G U a b P) (hi : i + 1 < P.length)
    (hDne : D ≠ []) (hDnod : D.Nodup) (hDch : D.IsChain G.Adj)
    (hDU : ∀ v ∈ D, v ∈ U) (hDdisj : ∀ v ∈ D, v ∉ P)
    (h1 : G.Adj (P.get ⟨i, by omega⟩) (D.head hDne))
    (h2 : G.Adj (D.getLast hDne) (P.get ⟨i + 1, by omega⟩)) :
    PathListIn G U a b (P.take (i + 1) ++ D ++ P.drop (i + 1)) ∧
      P.length < (P.take (i + 1) ++ D ++ P.drop (i + 1)).length := by
  set A := P.take (i+1) with hAdef
  set B := P.drop (i+1) with hBdef
  have hA_sub : A ⊆ P := by rw [hAdef]; exact List.take_subset _ _
  have hB_sub : B ⊆ P := by rw [hBdef]; exact List.drop_subset _ _
  have htd : ∀ x ∈ A, x ∉ B := hAdef ▸ hBdef ▸ take_drop_disjoint P hP.nodup (i+1)
  have hDnotP : ∀ v ∈ D, v ∉ P := hDdisj
  -- nodup
  have hAD : (A ++ D).Nodup := List.Nodup.append
    ((List.take_sublist (i+1) P).nodup hP.nodup) hDnod
    (by rw [List.disjoint_left]; intro x hx hy; exact hDnotP x hy (hA_sub hx))
  have hADB : (A ++ D ++ B).Nodup := List.Nodup.append hAD
    ((List.drop_sublist (i+1) P).nodup hP.nodup)
    (by rw [List.disjoint_left]; intro x hx hy
        rcases List.mem_append.mp hx with hx | hx
        · exact htd x hx hy
        · exact hDnotP x hx (hB_sub hy))
  -- chain
  have hAch : A.IsChain G.Adj := by rw [hAdef]; exact hP.isChain.take (i+1)
  have hBch : B.IsChain G.Adj := by rw [hBdef]; exact hP.isChain.drop (i+1)
  have hA_last : A.getLast? = some (P.get ⟨i, by omega⟩) := by
    rw [hAdef]; exact take_getLast? hi
  have hB_head : B.head? = some (P.get ⟨i+1, by omega⟩) := by
    rw [hBdef]; exact drop_head? hi
  have hAD_last : (A ++ D).getLast? = some (D.getLast hDne) := by
    rw [List.getLast?_append, getLast?_eq_some_getLast hDne]
    rfl
  have hchain : (A ++ D ++ B).IsChain G.Adj := by
    refine List.IsChain.append (List.IsChain.append hAch hDch ?_) hBch ?_
    · intro x hx y hy
      rw [hA_last] at hx
      rw [Option.mem_some_iff] at hx
      rw [head?_eq_some_head hDne] at hy
      rw [Option.mem_some_iff] at hy
      rw [← hx, ← hy]
      exact h1
    · intro x hx y hy
      rw [hAD_last] at hx
      rw [Option.mem_some_iff] at hx
      rw [hB_head] at hy
      rw [Option.mem_some_iff] at hy
      rw [← hx, ← hy]
      exact h2
  -- endpoints
  have hhead : (A ++ D ++ B).head? = some a := by
    rw [hAdef, hBdef] at *
    rw [List.head?_append, List.head?_append, List.head?_take,
      if_neg (by omega : ¬ (i+1 = 0)), hP.head?_eq]
    rfl
  have hlast : (A ++ D ++ B).getLast? = some b := by
    rw [hAdef, hBdef] at *
    rw [List.getLast?_append, List.getLast?_drop,
      if_neg (by omega : ¬ P.length ≤ i+1), hP.getLast?_eq]
    rfl
  have hU : ∀ v ∈ A ++ D ++ B, v ∈ U := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · exact hP.mem_U (hA_sub hv)
      · exact hDU v hv
    · exact hP.mem_U (hB_sub hv)
  have hlen : P.length < (A ++ D ++ B).length := by
    have hDpos : 0 < D.length := List.length_pos_iff.mpr hDne
    rw [List.length_append, List.length_append, List.length_take, List.length_drop]
    have hmin : min (i + 1) P.length = i + 1 := min_eq_left (by omega)
    rw [hmin]
    omega
  exact ⟨⟨hADB, hchain, hhead, hlast, hU⟩, hlen⟩


lemma drop_mono (P : List (Fin n)) {i j : ℕ} (hij : i ≤ j) : P.drop j ⊆ P.drop i := by
  intro x hx
  have h : P.drop j = (P.drop i).drop (j - i) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [h] at hx
  exact List.drop_subset _ _ hx

lemma insertRev_pathList_aux {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {P D : List (Fin n)} {i j : ℕ}
    (hP : PathListIn G U a b P) (hij : i < j) (hj : j + 1 < P.length)
    (hDne : D ≠ []) (hDnod : D.Nodup) (hDch : D.IsChain G.Adj)
    (hDU : ∀ v ∈ D, v ∈ U) (hDdisj : ∀ v ∈ D, v ∉ P)
    (h1 : G.Adj (P.get ⟨i, by omega⟩) (D.head hDne))
    (h2 : G.Adj (D.getLast hDne) (P.get ⟨j, by omega⟩))
    (h3 : G.Adj (P.get ⟨i + 1, by omega⟩) (P.get ⟨j + 1, by omega⟩)) :
    PathListIn G U a b
      (P.take (i + 1) ++ D ++ ((P.take (j + 1)).drop (i + 1)).reverse ++ P.drop (j + 1)) ∧
      P.length < (P.take (i + 1) ++ D ++ ((P.take (j + 1)).drop (i + 1)).reverse
        ++ P.drop (j + 1)).length := by
  have hi : i + 1 < P.length := by omega
  set A := P.take (i+1) with hAdef
  set B := P.drop (j+1) with hBdef
  have hA_sub : A ⊆ P := by rw [hAdef]; exact List.take_subset _ _
  have hB_sub : B ⊆ P := by rw [hBdef]; exact List.drop_subset _ _
  have hM_sub_drop : (P.take (j+1)).drop (i+1) ⊆ P.drop (i+1) := by
    rw [List.drop_take]; exact List.take_subset _ _
  have hM_sub_take : (P.take (j+1)).drop (i+1) ⊆ P.take (j+1) := List.drop_subset _ _
  have hAM : ∀ x ∈ A, x ∉ (P.take (j+1)).drop (i+1) := by
    intro x hxA hxM
    exact take_drop_disjoint P hP.nodup (i+1) x hxA (hM_sub_drop hxM)
  have hMB : ∀ x ∈ (P.take (j+1)).drop (i+1), x ∉ B := by
    intro x hxM hxB
    exact take_drop_disjoint P hP.nodup (j+1) x (hM_sub_take hxM) hxB
  have hAB : ∀ x ∈ A, x ∉ B := by
    intro x hxA hxB
    have hxB' : x ∈ P.drop (i+1) := by
      rw [hBdef] at hxB
      exact drop_mono P (by omega) hxB
    exact take_drop_disjoint P hP.nodup (i+1) x hxA hxB'
  have hAMr : ∀ x ∈ A, x ∉ ((P.take (j+1)).drop (i+1)).reverse := by
    intro x hxA hx
    exact hAM x hxA (List.mem_reverse.mp hx)
  have hMrB : ∀ x ∈ ((P.take (j+1)).drop (i+1)).reverse, x ∉ B := by
    intro x hx hxB
    exact hMB x (List.mem_reverse.mp hx) hxB
  have hDnotP : ∀ v ∈ D, v ∉ P := hDdisj
  -- nodup
  have hAD : (A ++ D).Nodup := List.Nodup.append
    ((List.take_sublist (i+1) P).nodup hP.nodup) hDnod
    (by rw [List.disjoint_left]; intro x hx hy; exact hDnotP x hy (hA_sub hx))
  have hMr_nod : ((P.take (j+1)).drop (i+1)).reverse.Nodup := by
    rw [List.nodup_reverse]
    exact ((List.drop_sublist (i+1) (P.take (j+1))).trans (List.take_sublist (j+1) P)).nodup hP.nodup
  have hADMr : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse).Nodup := List.Nodup.append hAD hMr_nod
    (by rw [List.disjoint_left]; intro x hx hy
        rcases List.mem_append.mp hx with hx | hx
        · exact hAMr x hx hy
        · have hy' : x ∈ (P.take (j+1)).drop (i+1) := by
            rw [List.mem_reverse] at hy
            exact hy
          exact hDnotP x hx (List.take_subset (j+1) P (hM_sub_take hy')))
  have hnod : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B).Nodup := List.Nodup.append hADMr
    ((List.drop_sublist (j+1) P).nodup hP.nodup)
    (by rw [List.disjoint_left]; intro x hx hy
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact hAB x hx hy
          · exact hDnotP x hx (hB_sub hy)
        · exact hMrB x hx hy)
  -- endpoints
  have hA_last : A.getLast? = some (P.get ⟨i, by omega⟩) := by
    rw [hAdef]; exact take_getLast? hi
  have hA_head : A.head? = some a := by
    rw [hAdef, List.head?_take, if_neg (by omega : ¬ (i+1 = 0)), hP.head?_eq]
  have hM_head : ((P.take (j+1)).drop (i+1)).head? = some (P.get ⟨i+1, by omega⟩) := by
    rw [List.head?_drop, List.getElem?_take, if_pos (by omega : i + 1 < j + 1),
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hMtakelen : (P.take (j+1)).length = j + 1 := by
    rw [List.length_take]; exact min_eq_left (by omega)
  have hM_last : ((P.take (j+1)).drop (i+1)).getLast? = some (P.get ⟨j, by omega⟩) := by
    rw [List.getLast?_drop, hMtakelen, if_neg (by omega : ¬ j + 1 ≤ i + 1)]
    exact take_getLast? hj
  have hB_head : B.head? = some (P.get ⟨j+1, by omega⟩) := by
    rw [hBdef]; exact drop_head? hj
  have hB_last : B.getLast? = some b := by
    rw [hBdef, List.getLast?_drop, if_neg (by omega : ¬ P.length ≤ j+1), hP.getLast?_eq]
  have hAD_last : (A ++ D).getLast? = some (D.getLast hDne) := by
    rw [List.getLast?_append, getLast?_eq_some_getLast hDne]
    rfl
  have hMr_head : ((P.take (j+1)).drop (i+1)).reverse.head? = some (P.get ⟨j, by omega⟩) := by
    rw [List.head?_reverse]; exact hM_last
  have hMr_last : ((P.take (j+1)).drop (i+1)).reverse.getLast? = some (P.get ⟨i+1, by omega⟩) := by
    rw [List.getLast?_reverse]; exact hM_head
  have hADMr_last : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse).getLast?
      = some (P.get ⟨i+1, by omega⟩) := by
    rw [List.getLast?_append, hMr_last]
    rfl
  -- chain
  have hAch : A.IsChain G.Adj := by rw [hAdef]; exact hP.isChain.take (i+1)
  have hBch : B.IsChain G.Adj := by rw [hBdef]; exact hP.isChain.drop (j+1)
  have hMch : ((P.take (j+1)).drop (i+1)).IsChain G.Adj :=
    (hP.isChain.take (j+1)).drop (i+1)
  have hMrch : ((P.take (j+1)).drop (i+1)).reverse.IsChain G.Adj := by
    rw [List.isChain_reverse]; exact hMch.imp (fun {a b} h => h.symm)
  have hADch : (A ++ D).IsChain G.Adj := List.IsChain.append hAch hDch (by
    intro x hx y hy
    rw [hA_last] at hx
    rw [Option.mem_some_iff] at hx
    rw [head?_eq_some_head hDne] at hy
    rw [Option.mem_some_iff] at hy
    rw [← hx, ← hy]
    exact h1)
  have hADMrch : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse).IsChain G.Adj :=
    List.IsChain.append hADch hMrch (by
    intro x hx y hy
    rw [hAD_last] at hx
    rw [Option.mem_some_iff] at hx
    rw [hMr_head] at hy
    rw [Option.mem_some_iff] at hy
    rw [← hx, ← hy]
    exact h2)
  have hchain : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B).IsChain G.Adj :=
    List.IsChain.append hADMrch hBch (by
    intro x hx y hy
    rw [hADMr_last] at hx
    rw [Option.mem_some_iff] at hx
    rw [hB_head] at hy
    rw [Option.mem_some_iff] at hy
    rw [← hx, ← hy]
    exact h3)
  -- endpoints of the whole
  have hhead : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B).head? = some a := by
    rw [List.head?_append, List.head?_append, List.head?_append, hA_head]
    rfl
  have hlast : (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B).getLast? = some b := by
    rw [List.getLast?_append, hB_last]
    rfl
  have hU : ∀ v ∈ A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B, v ∈ U := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · exact hP.mem_U (hA_sub hv)
        · exact hDU v hv
      · exact hP.mem_U (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_reverse.mp hv)))
    · exact hP.mem_U (hB_sub hv)
  have hMlen : ((P.take (j+1)).drop (i+1)).length = j - i := by
    rw [List.length_drop, hMtakelen]
    omega
  have hlen : P.length < (A ++ D ++ ((P.take (j+1)).drop (i+1)).reverse ++ B).length := by
    have hDpos : 0 < D.length := List.length_pos_iff.mpr hDne
    have hAlen : A.length = i + 1 := by
      rw [hAdef, List.length_take]; exact min_eq_left (by omega)
    have hMrlen : ((P.take (j+1)).drop (i+1)).reverse.length = j - i := by
      rw [List.length_reverse, hMlen]
    have hBlen : B.length = P.length - (j + 1) := by rw [hBdef, List.length_drop]
    rw [List.length_append, List.length_append, List.length_append, hAlen, hMrlen, hBlen]
    omega
  exact ⟨⟨hnod, hchain, hhead, hlast, hU⟩, hlen⟩



/-! ## The main theorem -/

lemma getLast?_cons_of_ne_nil {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  rw [List.getLast?_cons]
  cases hl : l.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff] at hl
      exact absurd hl h
  | some z => rfl

lemma exists_walk_of_chain {G : SimpleGraph (Fin n)} {b : Fin n} :
    ∀ {l : List (Fin n)} {a : Fin n}, l.head? = some a → l.getLast? = some b →
      l.IsChain G.Adj → ∃ w : G.Walk a b, w.support = l := by
  intro l
  induction l with
  | nil => intro a h1 _ _; simp at h1
  | cons x t ih =>
      intro a hhead hlast hch
      cases t with
      | nil =>
          have hax : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          rw [← hax, ← hxb]
          exact ⟨SimpleGraph.Walk.nil, by simp [SimpleGraph.Walk.support_nil]⟩
      | cons y t' =>
          have hax : x = a := by simpa using hhead
          have hch' : G.Adj x y ∧ (y :: t').IsChain G.Adj := by
            rw [List.isChain_cons_iff] at hch
            rcases hch with h | ⟨c, l', hxy, hch2, heq⟩
            · simp at h
            · obtain ⟨hyc, ht'l'⟩ := (List.cons.injEq y t' c l').mp heq
              subst hyc
              subst ht'l'
              exact ⟨hxy, hch2⟩
          have hlast' : (y :: t').getLast? = some b := by
            rw [getLast?_cons_of_ne_nil (by simp)] at hlast
            exact hlast
          obtain ⟨w', hw'⟩ := ih (a := y) rfl hlast' hch'.2
          rw [← hax]
          exact ⟨SimpleGraph.Walk.cons hch'.1 w', by
            rw [SimpleGraph.Walk.support_cons, hw']⟩

lemma pathList_exists_walk_aux {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    {l : List (Fin n)} (h : PathListIn G U a b l) :
    ∃ w : G.Walk a b, w.IsPath ∧ w.support = l := by
  obtain ⟨w, hw⟩ := exists_walk_of_chain (G := G) (b := b) (a := a) h.head?_eq h.getLast?_eq h.isChain
  exact ⟨w, (SimpleGraph.Walk.isPath_def w).mpr (hw ▸ h.nodup), hw⟩

lemma exists_max_PathListIn_aux {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {a b : Fin n}
    (hex : ∃ l : List (Fin n), PathListIn G U a b l) :
    ∃ P : List (Fin n), PathListIn G U a b P ∧
      ∀ l : List (Fin n), PathListIn G U a b l → l.length ≤ P.length := by
  classical
  obtain ⟨l₀, hl₀⟩ := hex
  let Q : ℕ → Prop := fun k => ∃ l : List (Fin n), PathListIn G U a b l ∧ l.length = k
  have hQ : ∃ k ≤ U.card, Q k := ⟨l₀.length, hl₀.length_le_card, l₀, hl₀, rfl⟩
  obtain ⟨k, hkle, hkQ⟩ := hQ
  obtain ⟨l, hl, hlQ⟩ := Nat.findGreatest_spec (P := Q) hkle hkQ
  refine ⟨l, hl, fun l' hl' => ?_⟩
  have hle : l'.length ≤ U.card := hl'.length_le_card
  have hspec := Nat.le_findGreatest (P := Q) hle ⟨l', hl', rfl⟩
  omega

/-- The vertex following `v` on the list `P` (defaulting to `a` when there is none). -/
def succOf (P : List (Fin n)) (a : Fin n) (v : Fin n) : Fin n :=
  (P[P.idxOf v + 1]?).getD a

lemma succOf_of_lt {P : List (Fin n)} {a v : Fin n} (h : P.idxOf v + 1 < P.length) :
    succOf P a v = P.get ⟨P.idxOf v + 1, h⟩ := by
  simp only [succOf, List.getElem?_eq_getElem h]
  rfl

/-- **Spanning path in a graph that is lower-regular inside a vertex set.** -/
theorem exists_spanningPath_subset {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {p ε α : ℝ} (hlr : LowerRegOn G U p ε)
    (hεp : ε < p) (hε : 0 < ε) (hε1 : 1 ≤ ε * (U.card : ℝ)) (hεα : 8 * ε ≤ α)
    (hdeg : MinDegOn G U α)
    (a b : Fin n) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
    SpansPath G U a b := by
  classical
  have hH : SpanHyp G U p ε α := ⟨hlr, hεp, hε, hε1, hεα, hdeg⟩
  -- Step 1: some `a`–`b` path inside `U` exists (connectivity).
  have hconn : ∃ l : List (Fin n), PathListIn G U a b l := by
    have hreach : ReachIn G U a b := by
      have h0 := reachIn_after_delete_aux hH (S := (∅ : Finset (Fin n))) (by simp)
        (by simpa using hH.kappa_pos) ha (by simp) hb (by simp)
      simpa using h0
    exact hreach.exists_pathList
  -- Step 2: a longest one.
  obtain ⟨P, hP, hPmax⟩ := exists_max_PathListIn_aux hconn
  have hPpos : 0 < P.length := List.length_pos_iff.mpr hP.ne_nil
  have hPlen2 : 2 ≤ P.length := hP.two_le_length hab
  -- Step 3: it covers `U`.
  have hcover : U ⊆ P.toFinset := by
    by_contra hcon
    rw [Finset.not_subset] at hcon
    obtain ⟨z0, hz0U, hz0P⟩ := hcon
    set Z : Finset (Fin n) := U \ P.toFinset with hZdef
    have hz0Z : z0 ∈ Z := Finset.mem_sdiff.mpr ⟨hz0U, hz0P⟩
    set D : Finset (Fin n) := compFinset G Z z0 with hDdef
    have hz0D : z0 ∈ D := mem_compFinset.mpr (ReachIn.refl hz0Z)
    have hDZ : D ⊆ Z := compFinset_subset
    have hDU : D ⊆ U := fun x hx => (Finset.mem_sdiff.mp (hDZ hx)).1
    have hDclosed : ∀ v ∈ D, ∀ w ∈ Z, G.Adj v w → w ∈ D :=
      fun v hv w hw hadj => compFinset_closed hv hw hadj
    set Tv : Finset (Fin n) := P.toFinset.filter (fun v => ∃ d ∈ D, G.Adj v d) with hTvdef
    have hTv_sub : Tv ⊆ P.toFinset := Finset.filter_subset _ _
    have hTvU : Tv ⊆ U := hTv_sub.trans hP.toFinset_subset
    have hTv_entry : ∀ v, v ∈ Tv ↔ v ∈ P.toFinset ∧ ∃ d ∈ D, G.Adj v d :=
      fun v => Finset.mem_filter
    by_cases hcase : Tv = P.toFinset
    · -- Case 1: every vertex of `P` has a neighbour in `D`: insert a `D`-path.
      have hv0 : P.get ⟨0, by omega⟩ ∈ Tv := by
        rw [hcase]; exact List.mem_toFinset.mpr (List.getElem_mem (by omega))
      have hv1 : P.get ⟨1, by omega⟩ ∈ Tv := by
        rw [hcase]; exact List.mem_toFinset.mpr (List.getElem_mem (by omega))
      obtain ⟨d0, hd0D, hd0adj⟩ := (hTv_entry _).mp hv0 |>.2
      obtain ⟨d1, hd1D, hd1adj⟩ := (hTv_entry _).mp hv1 |>.2
      obtain ⟨Dl, hDl⟩ := compFinset_exists_pathList (G := G) (Z := Z) (z := z0) hd0D hd1D
      have hDlne : Dl ≠ [] := hDl.ne_nil
      have h1' : G.Adj (P.get ⟨0, by omega⟩) (Dl.head hDlne) := by
        rw [hDl.head_eq hDlne]; exact hd0adj
      have h2' : G.Adj (Dl.getLast hDlne) (P.get ⟨0 + 1, by omega⟩) := by
        rw [hDl.getLast_eq hDlne]; exact hd1adj.symm
      have hres := insert_pathList_aux (G := G) (U := U) (a := a) (b := b) (i := 0)
        hP (by omega) hDlne hDl.nodup hDl.isChain
        (fun w hw => hDU (hDl.mem_U hw))
        (fun w hw hwP => (Finset.mem_sdiff.mp (hDZ (hDl.mem_U hw))).2 (List.mem_toFinset.mpr hwP))
        h1' h2'
      have hle := hPmax _ hres.1
      omega
    · -- Case 2: some vertex of `P` is not adjacent to `D`.
      have hex_sub : ∃ y ∈ P.toFinset, y ∉ Tv := by
        by_contra h
        rw [not_exists] at h
        refine hcase (Finset.Subset.antisymm hTv_sub fun y hy => ?_)
        by_contra hyTv
        exact h y ⟨hy, hyTv⟩
      obtain ⟨y, hyP, hyTv⟩ := hex_sub
      have hyU : y ∈ U := hP.toFinset_subset hyP
      have hyD : y ∉ D := fun h => (Finset.mem_sdiff.mp (hDZ h)).2 hyP
      have hclosed' : ∀ v ∈ D, ∀ w ∈ U \ Tv, G.Adj v w → w ∈ D := by
        intro v hv w hw hadj
        obtain ⟨hwU, hwTv⟩ := Finset.mem_sdiff.mp hw
        by_cases hwP : w ∈ P.toFinset
        · exact absurd ((hTv_entry w).mpr ⟨hwP, v, hv, hadj.symm⟩) hwTv
        · exact hDclosed v hv w (Finset.mem_sdiff.mpr ⟨hwU, hwP⟩) hadj
      have hnotreach : ¬ ReachIn G (U \ Tv) z0 y := not_reachIn_of_closed hclosed' hz0D hyD
      have hTvbig : α * (U.card : ℝ) - ε * (U.card : ℝ) ≤ (Tv.card : ℝ) := by
        by_contra hlt
        rw [not_le] at hlt
        exact hnotreach (reachIn_after_delete_aux hH (S := Tv) hTvU hlt hz0U
          (fun h => hz0P (hTv_sub h)) hyU hyTv)
      -- the successor map along `P`
      have hidxbound : ∀ v ∈ Tv, P.idxOf v < P.length := fun v hv =>
        List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp (hTv_sub hv))
      have hget_idx : ∀ (v : Fin n) (hv : P.idxOf v < P.length),
          P.get ⟨P.idxOf v, hv⟩ = v := fun v hv => List.getElem_idxOf hv
      have hlast_elem : P.get ⟨P.length - 1, by omega⟩ = b := hP.last_getElem hPpos
      have hidx_lt : ∀ v ∈ Tv, v ≠ b → P.idxOf v < P.length - 1 := by
        intro v hv hvb
        have h1 : P.idxOf v < P.length := hidxbound v hv
        rcases Nat.lt_or_ge (P.idxOf v) (P.length - 1) with h | h
        · exact h
        · have h2 : P.idxOf v = P.length - 1 := by omega
          have h3 : P.get ⟨P.idxOf v, h1⟩ = v := hget_idx v h1
          have h4 : P.get ⟨P.idxOf v, h1⟩ = b := by
            rw [show (⟨P.idxOf v, h1⟩ : Fin P.length) = ⟨P.length - 1, by omega⟩ from Fin.ext h2]
            exact hlast_elem
          exact absurd (h3.symm.trans h4) hvb
      have hsucc_val : ∀ (v : Fin n) (hv : v ∈ Tv) (hvb : v ≠ b),
          succOf P a v = P.get ⟨P.idxOf v + 1, by have := hidx_lt v hv hvb; omega⟩ := by
        intro v hv hvb
        exact succOf_of_lt (by have := hidx_lt v hv hvb; omega)
      set Tp : Finset (Fin n) := (Tv.erase b).image (succOf P a) with hTpdef
      have hsucc_inj : Set.InjOn (succOf P a) ↑(Tv.erase b) := by
        intro v hv v' hv' heq
        rw [Finset.mem_coe, Finset.mem_erase] at hv hv'
        obtain ⟨hvb, hvTv⟩ := hv
        obtain ⟨hv'b, hv'Tv⟩ := hv'
        have hltv : P.idxOf v + 1 < P.length := by have := hidx_lt v hvTv hvb; omega
        have hltv' : P.idxOf v' + 1 < P.length := by have := hidx_lt v' hv'Tv hv'b; omega
        have e1 : succOf P a v = P.get ⟨P.idxOf v + 1, hltv⟩ := succOf_of_lt hltv
        have e2 : succOf P a v' = P.get ⟨P.idxOf v' + 1, hltv'⟩ := succOf_of_lt hltv'
        have hidxe : P.idxOf v + 1 = P.idxOf v' + 1 := by
          have hgoal : P.get ⟨P.idxOf v + 1, hltv⟩ = P.get ⟨P.idxOf v' + 1, hltv'⟩ := by
            rw [← e1, ← e2]
            exact heq
          exact (List.Nodup.getElem_inj_iff hP.nodup (hi := hltv) (hj := hltv')).mp hgoal
        have heqidx : P.idxOf v = P.idxOf v' := by omega
        have h1 : P.get ⟨P.idxOf v, hidxbound v hvTv⟩ = v := hget_idx v (hidxbound v hvTv)
        have h2 : P.get ⟨P.idxOf v', hidxbound v' hv'Tv⟩ = v' := hget_idx v' (hidxbound v' hv'Tv)
        have hfin : (⟨P.idxOf v, hidxbound v hvTv⟩ : Fin P.length)
            = ⟨P.idxOf v', hidxbound v' hv'Tv⟩ := Fin.ext heqidx
        have h4 : P.get ⟨P.idxOf v, hidxbound v hvTv⟩
            = P.get ⟨P.idxOf v', hidxbound v' hv'Tv⟩ := by rw [hfin]
        exact h1.symm.trans (h4.trans h2)
      have hTp_card : Tv.card ≤ Tp.card + 1 := by
        have himg : Tp.card = (Tv.erase b).card := Finset.card_image_of_injOn hsucc_inj
        by_cases hbTv : b ∈ Tv
        · have h1 : (Tv.erase b).card + 1 = Tv.card := Finset.card_erase_add_one hbTv
          rw [← h1, himg]
        · have herase : Tv.erase b = Tv := Finset.erase_eq_of_notMem hbTv
          rw [himg, herase]
          exact Nat.le_succ _
      have hTp_sub_P : Tp ⊆ P.toFinset := by
        intro x hx
        obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_erase] at hv
        obtain ⟨hvb, hvTv⟩ := hv
        have hltv : P.idxOf v + 1 < P.length := by have := hidx_lt v hvTv hvb; omega
        rw [← hvu, succOf_of_lt hltv]
        exact List.mem_toFinset.mpr (List.getElem_mem hltv)
      have hz0_notin_Tp : z0 ∉ Tp := fun h => hz0P (hTp_sub_P h)
      -- independence of `Tp ∪ {z0}`
      have hno_adj_z : ∀ x ∈ Tp, ¬ G.Adj x z0 := by
        intro x hx hadj
        obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_erase] at hv
        obtain ⟨hvb, hvTv⟩ := hv
        have hltv : P.idxOf v + 1 < P.length := by have := hidx_lt v hvTv hvb; omega
        have hval : succOf P a v = P.get ⟨P.idxOf v + 1, hltv⟩ := succOf_of_lt hltv
        have hvidx : P.get ⟨P.idxOf v, hidxbound v hvTv⟩ = v := hget_idx v (hidxbound v hvTv)
        obtain ⟨d, hdD, hdadj⟩ := (hTv_entry v).mp hvTv |>.2
        obtain ⟨Dl, hDl⟩ := compFinset_exists_pathList (G := G) (Z := Z) (z := z0) hdD hz0D
        have hDlne : Dl ≠ [] := hDl.ne_nil
        have h1' : G.Adj (P.get ⟨P.idxOf v, hidxbound v hvTv⟩) (Dl.head hDlne) := by
          rw [hDl.head_eq hDlne, hvidx]
          exact hdadj
        have h2' : G.Adj (Dl.getLast hDlne) (P.get ⟨P.idxOf v + 1, hltv⟩) := by
          rw [hDl.getLast_eq hDlne, ← hval, hvu]
          exact hadj.symm
        have hres := insert_pathList_aux (G := G) (U := U) (a := a) (b := b)
          (P := P) (D := Dl) (i := P.idxOf v) hP (by omega) hDlne hDl.nodup hDl.isChain
          (fun w hw => hDU (hDl.mem_U hw))
          (fun w hw hwP => (Finset.mem_sdiff.mp (hDZ (hDl.mem_U hw))).2 (List.mem_toFinset.mpr hwP))
          h1' h2'
        have hle := hPmax _ hres.1
        omega
      have hno_adj2 : ∀ x ∈ Tp, ∀ y ∈ Tp, ¬ G.Adj x y := by
        intro x hx y hy hadj
        obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_erase] at hv
        obtain ⟨hvb, hvTv⟩ := hv
        obtain ⟨v', hv', hv'u⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase] at hv'
        obtain ⟨hv'b, hv'Tv⟩ := hv'
        have key : ∀ (u u' X Y : Fin n), u ∈ Tv → u ≠ b → u' ∈ Tv → u' ≠ b →
            P.idxOf u < P.idxOf u' → succOf P a u = X → succOf P a u' = Y →
              G.Adj X Y → False := by
          intro u u' X Y huTv hub hu'Tv hu'b hlt hsu hsu' hadj'
          have hltu : P.idxOf u + 1 < P.length := by have := hidx_lt u huTv hub; omega
          have hltu' : P.idxOf u' + 1 < P.length := by have := hidx_lt u' hu'Tv hu'b; omega
          have hvalu : succOf P a u = P.get ⟨P.idxOf u + 1, hltu⟩ := succOf_of_lt hltu
          have hvalu' : succOf P a u' = P.get ⟨P.idxOf u' + 1, hltu'⟩ := succOf_of_lt hltu'
          have huidx : P.get ⟨P.idxOf u, hidxbound u huTv⟩ = u := hget_idx u (hidxbound u huTv)
          have hu'idx : P.get ⟨P.idxOf u', hidxbound u' hu'Tv⟩ = u' := hget_idx u' (hidxbound u' hu'Tv)
          obtain ⟨d, hdD, hdadj⟩ := (hTv_entry u).mp huTv |>.2
          obtain ⟨d', hd'D, hd'adj⟩ := (hTv_entry u').mp hu'Tv |>.2
          obtain ⟨Dl, hDl⟩ := compFinset_exists_pathList (G := G) (Z := Z) (z := z0) hdD hd'D
          have hDlne : Dl ≠ [] := hDl.ne_nil
          have h1' : G.Adj (P.get ⟨P.idxOf u, hidxbound u huTv⟩) (Dl.head hDlne) := by
            rw [hDl.head_eq hDlne, huidx]
            exact hdadj
          have h2' : G.Adj (Dl.getLast hDlne) (P.get ⟨P.idxOf u', hidxbound u' hu'Tv⟩) := by
            rw [hDl.getLast_eq hDlne, hu'idx]
            exact hd'adj.symm
          have h3' : G.Adj (P.get ⟨P.idxOf u + 1, hltu⟩) (P.get ⟨P.idxOf u' + 1, hltu'⟩) := by
            rw [← hvalu, ← hvalu', hsu, hsu']
            exact hadj'
          have hres := insertRev_pathList_aux (G := G) (U := U) (a := a) (b := b)
            (P := P) (D := Dl) (i := P.idxOf u) (j := P.idxOf u') hP hlt hltu' hDlne
            hDl.nodup hDl.isChain
            (fun w hw => hDU (hDl.mem_U hw))
            (fun w hw hwP => (Finset.mem_sdiff.mp (hDZ (hDl.mem_U hw))).2 (List.mem_toFinset.mpr hwP))
            h1' h2' h3'
          have hle := hPmax _ hres.1
          omega
        by_cases hidxeq : P.idxOf v = P.idxOf v'
        · have hxy : x = y := by
            have hltv : P.idxOf v + 1 < P.length := by have := hidx_lt v hvTv hvb; omega
            have hltv' : P.idxOf v' + 1 < P.length := by have := hidx_lt v' hv'Tv hv'b; omega
            have e1 : succOf P a v = P.get ⟨P.idxOf v + 1, hltv⟩ := succOf_of_lt hltv
            have e2 : succOf P a v' = P.get ⟨P.idxOf v' + 1, hltv'⟩ := succOf_of_lt hltv'
            have hfin : (⟨P.idxOf v + 1, hltv⟩ : Fin P.length) = ⟨P.idxOf v' + 1, hltv'⟩ :=
              Fin.ext (by show P.idxOf v + 1 = P.idxOf v' + 1; rw [hidxeq])
            calc x = succOf P a v := hvu.symm
              _ = P.get ⟨P.idxOf v + 1, hltv⟩ := e1
              _ = P.get ⟨P.idxOf v' + 1, hltv'⟩ := by rw [hfin]
              _ = succOf P a v' := e2.symm
              _ = y := hv'u
          exact (G.loopless.irrefl x) (hxy ▸ hadj)
        · rcases Nat.lt_or_gt_of_ne hidxeq with hij | hji
          · exact key v v' x y hvTv hvb hv'Tv hv'b hij hvu hv'u hadj
          · exact key v' v y x hv'Tv hv'b hvTv hvb hji hv'u hvu hadj.symm
      have hind : ∀ x ∈ Tp ∪ {z0}, ∀ y ∈ Tp ∪ {z0}, ¬ G.Adj x y := by
        intro x hx y hy hadj
        rcases Finset.mem_union.mp hx with hxTp | hxz
        · rcases Finset.mem_union.mp hy with hyTp | hyz
          · exact hno_adj2 x hxTp y hyTp hadj
          · rw [Finset.mem_singleton] at hyz
            exact hno_adj_z x hxTp (hyz ▸ hadj)
        · rw [Finset.mem_singleton] at hxz
          rcases Finset.mem_union.mp hy with hyTp | hyz
          · exact hno_adj_z y hyTp (hxz ▸ hadj.symm)
          · rw [Finset.mem_singleton] at hyz
            exact (G.loopless.irrefl z0) (by rw [hxz, hyz] at hadj; exact hadj)
      have hsub : Tp ∪ {z0} ⊆ U := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hP.toFinset_subset (hTp_sub_P hv)
        · rw [Finset.mem_singleton] at hv
          subst hv
          exact hz0U
      have hcontr := card_lt_of_independent hlr hεp hε1 hsub hind
      have hbig : 2 * (ε * (U.card : ℝ)) + 1 ≤ ((Tp ∪ {z0}).card : ℝ) := by
        have h1 : (Tv.card : ℝ) ≤ (Tp.card : ℝ) + 1 := by exact_mod_cast hTp_card
        have h2 : ((Tp ∪ {z0}).card : ℝ) = (Tp.card : ℝ) + 1 := by
          rw [Finset.union_singleton, Finset.card_insert_of_notMem hz0_notin_Tp]
          simp
        linarith [hH.two_mul_epsN_add_one_le_kappa, hTvbig, h1, h2]
      linarith
  -- Step 4: assemble.
  have hPtube : P.toFinset = U := Finset.Subset.antisymm hP.toFinset_subset hcover
  obtain ⟨w, hwpath, hwsupp⟩ := pathList_exists_walk_aux hP
  refine ⟨ha, hb, hab, w, hwpath, fun v => ?_⟩
  rw [hwsupp, ← hPtube]
  exact List.mem_toFinset.symm

end

end Work.Deep.GKO
