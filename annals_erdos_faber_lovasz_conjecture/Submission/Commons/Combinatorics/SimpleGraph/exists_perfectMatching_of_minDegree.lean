import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Tactic.NormNum.Eq

namespace Commons.Combinatorics.SimpleGraph

open _root_.SimpleGraph

private lemma sum_supp_ncard_eq_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∑ c : H.ConnectedComponent, c.supp.ncard = Fintype.card W := by
  have key : ∀ c : H.ConnectedComponent, c.supp.ncard = Fintype.card c.supp := by
    intro c
    rw [← Nat.card_coe_set_eq (c.supp), Nat.card_eq_fintype_card]
  simp_rw [key]
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  refine
  { toFun := fun x => x.2.1
    invFun := fun w => ⟨H.connectedComponentMk w, ⟨w, rfl⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨c, ⟨v, hv⟩⟩
    simp only
    have hv' : H.connectedComponentMk v = c := hv
    subst hv'
    rfl
  · intro w; rfl

private lemma sum_oddComponents_supp_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ∑ c ∈ H.oddComponents.toFinset, c.supp.ncard ≤ Fintype.card W := by
  calc ∑ c ∈ H.oddComponents.toFinset, c.supp.ncard
      ≤ ∑ c : H.ConnectedComponent, c.supp.ncard :=
        Finset.sum_le_univ_sum_of_nonneg (fun c => Nat.zero_le _)
    _ = Fintype.card W := sum_supp_ncard_eq_card H

private lemma coe_deleteVerts_adj_iff {V : Type*} (G : SimpleGraph V) (u : Set V)
    (a b : ((⊤ : G.Subgraph).deleteVerts u).verts) :
    (((⊤ : G.Subgraph).deleteVerts u).coe).Adj a b ↔ G.Adj a.1 b.1 := by
  rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
  simp only [Subgraph.top_adj]
  constructor
  · rintro ⟨-, -, -, -, h⟩; exact h
  · rintro h; exact ⟨a.2.1, a.2.2, b.2.1, b.2.2, h⟩

private lemma component_supp_ncard_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : Set V)
    (hdeg : ∀ v : V, Fintype.card V - 3 ≤ G.degree v)
    (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    Fintype.card V - 2 - u.ncard ≤ c.supp.ncard := by
  classical
  by_cases hu : u.ncard ≤ Fintype.card V - 2
  · obtain ⟨v, hv⟩ := c.nonempty_supp
    have hv_notin : v.1 ∉ G.neighborSet v.1 := fun h => G.irrefl h
    have hsub : insert v.1 (G.neighborSet v.1) ⊆
        u ∪ (Subtype.val '' (c.supp : Set ↥((⊤ : G.Subgraph).deleteVerts u).verts)) := by
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inr ⟨v, hv, rfl⟩
      · rw [mem_neighborSet] at hw
        by_cases hwu : w ∈ u
        · exact Or.inl hwu
        · right
          let w' : ↥((⊤ : G.Subgraph).deleteVerts u).verts := ⟨w, ⟨trivial, hwu⟩⟩
          have hadj : (((⊤ : G.Subgraph).deleteVerts u).coe).Adj v w' := by
            rw [coe_deleteVerts_adj_iff]; exact hw
          have hw'c : w' ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hadj
          exact ⟨w', hw'c, rfl⟩
    have hdeg_eq : (G.neighborSet v.1).ncard = G.degree v.1 := by
      rw [Set.ncard_eq_toFinset_card', ← neighborFinset_def,
          card_neighborFinset_eq_degree]
    have key : (G.neighborSet v.1).ncard + 1 ≤ u.ncard + c.supp.ncard := by
      calc (G.neighborSet v.1).ncard + 1
          = (insert v.1 (G.neighborSet v.1)).ncard :=
              (Set.ncard_insert_of_notMem hv_notin).symm
        _ ≤ (u ∪ (Subtype.val '' (c.supp : Set ↥((⊤ : G.Subgraph).deleteVerts u).verts))).ncard :=
              Set.ncard_le_ncard hsub
        _ ≤ u.ncard + (Subtype.val '' (c.supp : Set ↥((⊤ : G.Subgraph).deleteVerts u).verts)).ncard :=
              Set.ncard_union_le _ _
        _ = u.ncard + c.supp.ncard := by
              rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    have hd := hdeg v.1
    rw [← hdeg_eq] at hd
    omega
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hu)]
    exact Nat.zero_le _

theorem exists_perfectMatching_of_minDegree (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : 4 < Fintype.card V)
    (heven : Even (Fintype.card V)) (hdeg : ∀ v : V, Fintype.card V - 3 ≤ G.degree v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  refine tutte.mpr ?_
  intro u hu
  let H : SimpleGraph ↥((⊤ : G.Subgraph).deleteVerts u).verts := ((⊤ : G.Subgraph).deleteVerts u).coe
  change u.ncard < H.oddComponents.ncard at hu
  have hcardW : Fintype.card ↥((⊤ : G.Subgraph).deleteVerts u).verts = Fintype.card V - u.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Subgraph.deleteVerts_verts,
        Subgraph.verts_top, Set.ncard_sdiff (Set.subset_univ u), Set.ncard_univ,
        Nat.card_eq_fintype_card]
  have hn6 : 6 ≤ Fintype.card V := by
    obtain ⟨m, hm⟩ := heven
    omega
  have hsle : u.ncard ≤ Fintype.card V := by
    have h : u.ncard ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard (Set.subset_univ u)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  have hn2 : Fintype.card V % 2 = 0 := Nat.even_iff.mp heven
  have hodd : Odd H.oddComponents.ncard ↔ Odd u.ncard := by
    have h1 : Odd H.oddComponents.ncard ↔ Odd (Fintype.card V - u.ncard) := by
      rw [odd_ncard_oddComponents, Nat.card_eq_fintype_card, hcardW]
    have h2 : Odd (Fintype.card V - u.ncard) ↔ Odd u.ncard := by
      rw [Nat.odd_sub hsle, Nat.odd_iff, Nat.even_iff, hn2, Nat.odd_iff]
      constructor
      · intro h
        have hs0' : u.ncard % 2 ≠ 0 := fun hz => absurd (h.mpr hz) (by norm_num)
        omega
      · intro h
        exact iff_of_false (by norm_num) (by omega)
    exact h1.trans h2
  have heven_ks : Even H.oddComponents.ncard ↔ Even u.ncard := by
    rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even]
    exact not_congr hodd
  have hk_ge : u.ncard + 2 ≤ H.oddComponents.ncard := by
    have hdvd : Even (H.oddComponents.ncard - u.ncard) :=
      (Nat.even_sub (le_of_lt hu)).mpr heven_ks
    obtain ⟨j, hj⟩ := hdvd
    have hpos : 0 < H.oddComponents.ncard - u.ncard := Nat.sub_pos_of_lt hu
    omega
  have hsum_le : ∑ c ∈ H.oddComponents.toFinset, c.supp.ncard ≤ Fintype.card V - u.ncard := by
    have h := sum_oddComponents_supp_le H
    rwa [hcardW] at h
  have hone : ∀ c ∈ H.oddComponents.toFinset, (1:ℕ) ≤ c.supp.ncard := by
    intro c _
    have := c.nonempty_supp.ncard_pos
    omega
  have hk_le : H.oddComponents.ncard ≤ Fintype.card V - u.ncard := by
    have h1 : H.oddComponents.toFinset.card ≤ ∑ c ∈ H.oddComponents.toFinset, c.supp.ncard := by
      have := Finset.card_nsmul_le_sum H.oddComponents.toFinset (fun c => c.supp.ncard) (1:ℕ) hone
      simpa using this
    rw [Set.ncard_eq_toFinset_card']
    exact le_trans h1 hsum_le
  have ht2 : 2 ≤ Fintype.card V - 2 - u.ncard := by omega
  have hcomp : ∀ c ∈ H.oddComponents.toFinset,
      Fintype.card V - 2 - u.ncard ≤ c.supp.ncard := by
    intro c _
    exact component_supp_ncard_ge G u hdeg c
  have hkt : H.oddComponents.ncard * (Fintype.card V - 2 - u.ncard) ≤ Fintype.card V - u.ncard := by
    have h := Finset.card_nsmul_le_sum H.oddComponents.toFinset (fun c => c.supp.ncard)
        (Fintype.card V - 2 - u.ncard) hcomp
    have h' : H.oddComponents.toFinset.card * (Fintype.card V - 2 - u.ncard) ≤
        ∑ c ∈ H.oddComponents.toFinset, c.supp.ncard := by simpa using h
    rw [Set.ncard_eq_toFinset_card']
    exact le_trans h' hsum_le
  have hfinal : (u.ncard + 1) * (Fintype.card V - 2 - u.ncard) ≤ 2 := by
    have h1 : (u.ncard + 2) * (Fintype.card V - 2 - u.ncard) ≤
        H.oddComponents.ncard * (Fintype.card V - 2 - u.ncard) :=
      Nat.mul_le_mul_right _ hk_ge
    have h2 : (u.ncard + 2) * (Fintype.card V - 2 - u.ncard) ≤ Fintype.card V - u.ncard :=
      le_trans h1 hkt
    have h3 : Fintype.card V - u.ncard = (Fintype.card V - 2 - u.ncard) + 2 := by omega
    have h4 : (u.ncard + 1) * (Fintype.card V - 2 - u.ncard) + (Fintype.card V - 2 - u.ncard) ≤
        2 + (Fintype.card V - 2 - u.ncard) := by
      have heq : (u.ncard + 1) * (Fintype.card V - 2 - u.ncard) + (Fintype.card V - 2 - u.ncard)
          = (u.ncard + 2) * (Fintype.card V - 2 - u.ncard) := by ring
      calc (u.ncard + 1) * (Fintype.card V - 2 - u.ncard) + (Fintype.card V - 2 - u.ncard)
          = (u.ncard + 2) * (Fintype.card V - 2 - u.ncard) := heq
        _ ≤ Fintype.card V - u.ncard := h2
        _ = (Fintype.card V - 2 - u.ncard) + 2 := h3
        _ = 2 + (Fintype.card V - 2 - u.ncard) := by ring
    exact Nat.add_le_add_iff_right.mp h4
  have hs0 : u.ncard = 0 := by
    have h2t : 2 * (u.ncard + 1) ≤ 2 := by
      calc 2 * (u.ncard + 1) = (u.ncard + 1) * 2 := by ring
        _ ≤ (u.ncard + 1) * (Fintype.card V - 2 - u.ncard) := Nat.mul_le_mul_left _ ht2
        _ ≤ 2 := hfinal
    omega
  have ht_le : Fintype.card V - 2 - u.ncard ≤ 2 := by
    simpa [hs0] using hfinal
  omega

end Commons.Combinatorics.SimpleGraph