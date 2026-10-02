import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring

namespace Commons.Combinatorics.SimpleGraph

open Finset

/-- Two 0/1 indicators of the form `[a = x]` add up to the indicator of `[a = x ∨ a = y]`
when `x ≠ y`. -/
private lemma indicator_or {α : Type*} [DecidableEq α] {a x y : α} (hne : x ≠ y) :
    (if a = x ∨ a = y then (1:ℤ) else 0) =
      (if x = a then 1 else 0) + (if y = a then 1 else 0) := by
  by_cases hx : x = a
  · have hy : ¬ (y = a) := fun hy => hne (hx.trans hy.symm)
    rw [if_pos (Or.inl hx.symm), if_pos hx, if_neg hy]; norm_num
  · by_cases hy : y = a
    · have hxl : ¬ (a = x) := fun h => hx h.symm
      rw [if_pos (Or.inr hy.symm), if_neg hx, if_pos hy]; norm_num
    · have hxl : ¬ (a = x) := fun h => hx h.symm
      have hyl : ¬ (a = y) := fun h => hy h.symm
      rw [if_neg (fun h => h.elim hxl hyl), if_neg hx, if_neg hy]; norm_num

/-- Telescoping alternating sum. -/
private lemma sum_range_alt_telescope (g : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (g i + g (i + 1)) = g 0 - (-1 : ℤ) ^ n * g n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- The alternating sum of the indicator of the positions at which a walk visits a fixed
vertex telescopes to the endpoint contributions. -/
private lemma alt_walk_index_sum {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {n : ℕ} (w : Fin (n+1) → V) (hadj : ∀ i : Fin n, G.Adj (w i.castSucc) (w i.succ)) (a : V) :
    (∑ i : Fin n, (if a = w i.castSucc ∨ a = w i.succ then (-1 : ℤ) ^ (i : ℕ) else 0))
      = (if a = w 0 then 1 else 0) - (-1 : ℤ) ^ n * (if a = w (Fin.last n) then 1 else 0) := by
  set g : ℕ → ℤ := fun j => if h : j < n + 1 then (if w ⟨j, h⟩ = a then 1 else 0) else 0 with hg
  have hg1 : ∀ i : Fin n, g (i : ℕ) = (if w i.castSucc = a then 1 else 0) := by
    intro i
    rw [hg]
    simp only [dif_pos (show (i:ℕ) < n+1 by omega)]
    rfl
  have hg2 : ∀ i : Fin n, g ((i : ℕ) + 1) = (if w i.succ = a then 1 else 0) := by
    intro i
    rw [hg]
    simp only [dif_pos (show (i:ℕ) + 1 < n+1 by omega)]
    rfl
  have hstep1 : ∀ i : Fin n,
      (if a = w i.castSucc ∨ a = w i.succ then (-1 : ℤ) ^ (i : ℕ) else 0)
        = (-1 : ℤ) ^ (i : ℕ) * (g (i : ℕ) + g ((i : ℕ) + 1)) := by
    intro i
    rw [hg1 i, hg2 i, ← indicator_or (a := a) (x := w i.castSucc) (y := w i.succ) (hadj i).ne]
    by_cases h : a = w i.castSucc ∨ a = w i.succ <;> simp [h]
  have hzero : w (⟨0, Nat.succ_pos n⟩ : Fin (n+1)) = w 0 := rfl
  have hg0 : g 0 = (if a = w 0 then 1 else 0) := by
    rw [hg]
    simp only [dif_pos (Nat.succ_pos n)]
    rw [hzero]
    by_cases h : a = w 0
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  have hlast : w (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)) = w (Fin.last n) := rfl
  have hgn : g n = (if a = w (Fin.last n) then 1 else 0) := by
    rw [hg]
    simp only [dif_pos (Nat.lt_succ_self n)]
    rw [hlast]
    by_cases h : a = w (Fin.last n)
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  rw [Finset.sum_congr rfl (fun i _ => hstep1 i),
    Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ j * (g j + g (j + 1))) n,
    sum_range_alt_telescope g n, hg0, hgn]

/-- **Flipping the edges of an edge-simple alternating walk.**

Let `R ≤ G` be a spanning-or-not subgraph of `G`, and let `w : Fin (n+1) → V` be a walk whose
consecutive pairs are `G`-adjacent, whose edges `s(w i.castSucc, w i.succ)` (`i : Fin n`) are
pairwise distinct, and which is *alternating*: the `i`-th edge of `w` lies in `R` iff `i` is odd.

Then toggling the `R`-membership of exactly the edges of `w` (removing the `R`-edges of the walk,
adding the non-`R` ones) produces a spanning subgraph `R'` of `G` whose degrees are

  `deg_{R'}(a) = deg_R(a) + [a = w 0] − (−1)^n · [a = w (Fin.last n)]`.

(Note that no hypothesis `w 0 ≠ w (Fin.last n)` is needed: a closed alternating walk of odd
length toggles *two* edges at its common endpoint, which is exactly what the formula records.) -/
theorem alt_walk_flip_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : G.Subgraph) {n : ℕ} (w : Fin (n+1) → V)
    (hadj : ∀ i : Fin n, G.Adj (w i.castSucc) (w i.succ))
    (hinj : Function.Injective (fun i : Fin n => s(w i.castSucc, w i.succ)))
    (halt : ∀ i : Fin n, R.Adj (w i.castSucc) (w i.succ) ↔ Odd i.val) :
    ∃ R' : G.Subgraph, R'.IsSpanning ∧ ∀ a : V,
      (Nat.card {b : V // R'.Adj a b} : ℤ)
        = (Nat.card {b : V // R.Adj a b} : ℤ)
          + (if a = w 0 then 1 else 0)
          - (if a = w (Fin.last n) then ((-1 : ℤ) ^ n) else 0) := by
  classical
  let Ew : Finset (Sym2 V) := Finset.univ.image (fun i : Fin n => s(w i.castSucc, w i.succ))
  have hmem : ∀ z : Sym2 V, z ∈ Ew ↔ ∃ i : Fin n, s(w i.castSucc, w i.succ) = z := by
    intro z
    simp only [Ew, Finset.mem_image, Finset.mem_univ, true_and]
  have hEw_adj : ∀ {v u : V}, (s(v, u) : Sym2 V) ∈ Ew → G.Adj v u := by
    intro v u h
    obtain ⟨i, hi⟩ := (hmem _).mp h
    have hrel : (w i.castSucc = v ∧ w i.succ = u) ∨ (w i.castSucc = u ∧ w i.succ = v) :=
      Sym2.eq_iff.mp hi
    rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hadj i
    · rw [← h1, ← h2]; exact (hadj i).symm
  let R' : G.Subgraph :=
    { verts := Set.univ
      Adj := fun v u =>
        (R.Adj v u ∧ (s(v,u) : Sym2 V) ∉ Ew) ∨ ((s(v,u) : Sym2 V) ∈ Ew ∧ ¬ R.Adj v u)
      adj_sub := by
        intro v u h
        rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact R.adj_sub h1
        · exact hEw_adj h1
      edge_vert := by intro v u _; exact Set.mem_univ v
      symm := ⟨fun v u h => by
        have hset : ((s(u,v) : Sym2 V) ∈ Ew) ↔ ((s(v,u) : Sym2 V) ∈ Ew) := by rw [Sym2.eq_swap]
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨(R.adj_comm v u).mp h1, fun hh => h2 (hset.mp hh)⟩
        · exact Or.inr ⟨hset.mpr h1, fun hh => h2 ((R.adj_comm v u).mpr hh)⟩⟩ }
  refine ⟨R', fun v => Set.mem_univ v, fun a => ?_⟩
  let Na : Finset V := Finset.univ.filter (fun b => R.Adj a b)
  let Wa : Finset V := Finset.univ.filter (fun b => (s(a,b) : Sym2 V) ∈ Ew)
  let Na' : Finset V := Finset.univ.filter (fun b => R'.Adj a b)
  let J : Finset (Fin n) := Finset.univ.filter (fun i => a = w i.castSucc ∨ a = w i.succ)
  let ψ : Fin n → V := fun i => if a = w i.castSucc then w i.succ else w i.castSucc
  have hψ : ∀ i : Fin n, ((s(a, ψ i) : Sym2 V) = s(w i.castSucc, w i.succ)) ↔
      (a = w i.castSucc ∨ a = w i.succ) := by
    intro i
    constructor
    · intro h
      have h1 : a ∈ s(w i.castSucc, w i.succ) := by rw [← h]; exact Sym2.mem_mk_left a (ψ i)
      rwa [Sym2.mem_iff] at h1
    · intro h
      by_cases ha : a = w i.castSucc
      · have hψi : ψ i = w i.succ := by simp only [ψ, if_pos ha]
        rw [hψi, ha]
      · have hψi : ψ i = w i.castSucc := by simp only [ψ, if_neg ha]
        have hb : a = w i.succ := h.resolve_left ha
        rw [hψi, hb, Sym2.eq_swap]
  have hcardR' : (Nat.card {b : V // R'.Adj a b}) = Na'.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardR : (Nat.card {b : V // R.Adj a b}) = Na.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hNa' : Na' = (Na \ Wa) ∪ (Wa \ Na) := by
    ext b
    simp only [Na', Na, Wa, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff, R']
  have hdisj : Disjoint (Na \ Wa) (Wa \ Na) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_sdiff] at hb1 hb2
    exact hb1.2 hb2.1
  have hcardNa' : Na'.card = (Na \ Wa).card + (Wa \ Na).card := by
    rw [hNa', Finset.card_union_of_disjoint hdisj]
  have hNs : (Na \ Wa).card = Na.card - (Na ∩ Wa).card := by
    rw [Finset.card_sdiff, Finset.inter_comm]
  have hWs : (Wa \ Na).card = Wa.card - (Na ∩ Wa).card := by
    rw [Finset.card_sdiff]
  have hka : (Na'.card : ℤ) = (Na.card : ℤ) + (Wa.card : ℤ) - 2 * ((Na ∩ Wa).card : ℤ) := by
    have hI1 : (Na ∩ Wa).card ≤ Na.card := Finset.card_le_card Finset.inter_subset_left
    have hI2 : (Na ∩ Wa).card ≤ Wa.card := Finset.card_le_card Finset.inter_subset_right
    have e1 : ((Na \ Wa).card : ℤ) = (Na.card : ℤ) - ((Na ∩ Wa).card : ℤ) := by
      rw [hNs, Nat.cast_sub hI1]
    have e2 : ((Wa \ Na).card : ℤ) = (Wa.card : ℤ) - ((Na ∩ Wa).card : ℤ) := by
      rw [hWs, Nat.cast_sub hI2]
    rw [hcardNa', Nat.cast_add, e1, e2]
    ring
  have hNW : Wa.filter (fun b => R.Adj a b) = Na ∩ Wa := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_inter, Na, Wa, Finset.mem_univ, true_and]
    tauto
  have hsumWa' : (∑ i ∈ J, (if R.Adj (w i.castSucc) (w i.succ) then (-1:ℤ) else 1))
      = ∑ b ∈ Wa, (if R.Adj a b then (-1:ℤ) else 1) := by
    refine Finset.sum_bij (fun (i : Fin n) (_ : i ∈ J) => ψ i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : (s(a, ψ i) : Sym2 V) = s(w i.castSucc, w i.succ) := (hψ i).mpr hi.2
      rw [h1]
      exact (hmem _).mpr ⟨i, rfl⟩
    · intro i1 hi1 i2 hi2 heq
      rw [Finset.mem_filter] at hi1 hi2
      have h1 : (s(a, ψ i1) : Sym2 V) = s(w i1.castSucc, w i1.succ) := (hψ i1).mpr hi1.2
      have h2 : (s(a, ψ i2) : Sym2 V) = s(w i2.castSucc, w i2.succ) := (hψ i2).mpr hi2.2
      exact hinj (by
        show s(w i1.castSucc, w i1.succ) = s(w i2.castSucc, w i2.succ)
        rw [← h1, ← h2, heq])
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨i, hi⟩ := (hmem _).mp hb.2
      have hJ : a = w i.castSucc ∨ a = w i.succ := by
        have hmem' : a ∈ s(w i.castSucc, w i.succ) := by rw [hi]; exact Sym2.mem_mk_left a b
        rwa [Sym2.mem_iff] at hmem'
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hJ⟩
      · have h1 : (s(a, ψ i) : Sym2 V) = s(w i.castSucc, w i.succ) := (hψ i).mpr hJ
        exact Sym2.congr_right.mp (by rw [h1, hi])
    · intro i hi
      rw [Finset.mem_filter] at hi
      have h1 : (s(a, ψ i) : Sym2 V) = s(w i.castSucc, w i.succ) := (hψ i).mpr hi.2
      have hiff : R.Adj a (ψ i) ↔ R.Adj (w i.castSucc) (w i.succ) :=
        _root_.SimpleGraph.Subgraph.adj_congr_of_sym2 (H := R) h1
      by_cases h : R.Adj (w i.castSucc) (w i.succ)
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]
  have hLHSWa : (∑ b ∈ Wa, (if R.Adj a b then (-1:ℤ) else 1))
      = (Wa.card : ℤ) - 2 * ((Na ∩ Wa).card : ℤ) := by
    have hpt : ∀ b, (if R.Adj a b then (-1:ℤ) else 1) = 1 - 2 * (if R.Adj a b then (1:ℤ) else 0) := by
      intro b; by_cases h : R.Adj a b <;> simp [h]
    calc (∑ b ∈ Wa, (if R.Adj a b then (-1:ℤ) else 1))
        = ∑ b ∈ Wa, (1 - 2 * (if R.Adj a b then (1:ℤ) else 0)) := by
            apply Finset.sum_congr rfl; intro b _; exact hpt b
      _ = (∑ b ∈ Wa, (1:ℤ)) - ∑ b ∈ Wa, 2 * (if R.Adj a b then (1:ℤ) else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (Wa.card : ℤ) - 2 * ((Na ∩ Wa).card : ℤ) := by
            congr 1
            · simp
            · rw [← Finset.mul_sum, Finset.sum_boole, hNW]
  have hRHSJ : (∑ i ∈ J, (if R.Adj (w i.castSucc) (w i.succ) then (-1:ℤ) else 1))
      = ∑ i ∈ J, (-1:ℤ)^(i:ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [halt i]
    by_cases h : Odd i.val
    · rw [if_pos h, h.neg_one_pow]
    · rw [if_neg h, Even.neg_one_pow (Nat.not_odd_iff_even.mp h)]
  have hsumJ : (∑ i ∈ J, (-1:ℤ)^(i:ℕ))
      = (if a = w 0 then 1 else 0) - (-1:ℤ)^n * (if a = w (Fin.last n) then 1 else 0) := by
    have hJ : J = Finset.univ.filter (fun i : Fin n => a = w i.castSucc ∨ a = w i.succ) := rfl
    rw [hJ, Finset.sum_filter]
    exact alt_walk_index_sum w hadj a
  have hdelta : (Wa.card : ℤ) - 2 * ((Na ∩ Wa).card : ℤ)
      = (if a = w 0 then 1 else 0) - (-1:ℤ)^n * (if a = w (Fin.last n) then 1 else 0) := by
    rw [← hLHSWa, ← hsumWa', hRHSJ, hsumJ]
  rw [hcardR', hcardR, hka]
  have hB : (if a = w (Fin.last n) then (-1:ℤ)^n else 0)
      = (-1:ℤ)^n * (if a = w (Fin.last n) then 1 else 0) := by
    by_cases h : a = w (Fin.last n) <;> simp [h]
  linarith [hdelta, hB]

end Commons.Combinatorics.SimpleGraph
