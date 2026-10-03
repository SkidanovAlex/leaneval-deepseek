import Mathlib
import Submission.Work.PlanarSC.RunDefs

set_option linter.style.haveILetI false

namespace Work.PlanarSC

/-- A graph in which every closed walk of length `≥ 3` with pairwise distinct vertices
(coded as a map `ZMod n → V` with consecutive vertices adjacent) is acyclic.  This is the
`ZMod`-indexed form of `SimpleGraph.IsAcyclic`:  any `Mathlib` cycle of length `n` yields
such a map by reading off its vertices in order. -/
lemma isAcyclic_of_no_zmod_cycle {V : Type*} (G : SimpleGraph V)
    (h : ∀ (n : ℕ) (c : ZMod n → V), 3 ≤ n → Function.Injective c →
      (∀ i, G.Adj (c i) (c (i + 1))) → False) : G.IsAcyclic := by
  intro v p hp
  have hn3 : 3 ≤ p.length := hp.three_le_length
  haveI : NeZero p.length := ⟨by omega⟩
  refine h p.length (fun i => p.getVert i.val) hn3 ?_ ?_
  · intro i j hij
    have hvi : i.val ≤ p.length - 1 := by have := ZMod.val_lt i; omega
    have hvj : j.val ≤ p.length - 1 := by have := ZMod.val_lt j; omega
    exact ZMod.val_injective _ (hp.getVert_injOn' hvi hvj hij)
  · intro i
    have hlt : i.val < p.length := ZMod.val_lt i
    have key : (i + 1 : ZMod p.length).val = (i.val + 1) % p.length := by
      rw [show (i + 1 : ZMod p.length) = i + (1 : ZMod p.length) from rfl, ZMod.val_add,
        ZMod.val_one'' (by omega)]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with h1 | h1
    · rw [key, Nat.mod_eq_of_lt h1]
      exact p.adj_getVert_succ hlt
    · have h2 : i.val + 1 = p.length := h1
      rw [key, h2, Nat.mod_self]
      simpa [h2, p.getVert_zero, p.getVert_length] using p.adj_getVert_succ hlt

/-- Graph theory: a finite loopless symmetric graph (`T : Finset α`, `adj`) which is connected and
acyclic, and has at least two vertices, has a leaf: a vertex whose only neighbour in `T` is a single
vertex `x₀`.

Suggested route: take a longest chain `x₀, x₁, …, x_k` of pairwise adjacent distinct elements of `T`
(so every neighbour in `T` of `x_k` lies on the chain, else the chain would extend).  Acyclicity
forbids the chord `x_j — x_k` for `j ≤ k - 2`, so `x_{k-1}` is the only chain neighbour; the
hypotheses `hconn`/`hcard` give `x_k` at least one neighbour. -/
theorem exists_leaf_of_connected_acyclic {α : Type*} [DecidableEq α] (T : Finset α)
    (adj : α → α → Prop) (hsymm : ∀ a b, adj a b → adj b a) (hirr : ∀ a, ¬ adj a a)
    (hconn : ∀ a b : ↥T, Relation.ReflTransGen (fun x y : ↥T => adj (x : α) (y : α)) a b)
    (hacyc : ∀ (n : ℕ) (c : ZMod n → ↥T), 3 ≤ n → Function.Injective c →
      (∀ i, adj (c i : α) (c (i + 1) : α)) → False)
    (hcard : 2 ≤ T.card) :
    ∃ x ∈ T, ∃ x₀ ∈ T, adj x x₀ ∧ ∀ y ∈ T, adj x y → y = x₀ := by
  classical
  -- `T` has at least two elements, so its subtype is nonempty and nontrivial.
  haveI : Nonempty ↥T := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    exact ⟨⟨w, hw⟩⟩
  haveI : Nontrivial ↥T := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]; omega
  -- Turn `adj` on `↥T` into a `SimpleGraph`; it is a tree by `hconn` and `hacyc`.
  let G : SimpleGraph ↥T := SimpleGraph.mk (fun a b => adj (a : α) (b : α))
    ⟨fun (a b : ↥T) h => hsymm (a : α) (b : α) h⟩ ⟨fun (a : ↥T) h => hirr (a : α) h⟩
  have hconnG : G.Connected :=
    ⟨fun a b => (SimpleGraph.reachable_iff_reflTransGen a b).mpr (hconn a b)⟩
  have hacycG : G.IsAcyclic :=
    isAcyclic_of_no_zmod_cycle G (fun n c hn hinj hadj => hacyc n c hn hinj hadj)
  have hG : G.IsTree := ⟨hconnG, hacycG⟩
  -- A nontrivial tree has a vertex of degree one, i.e. with a unique neighbour.
  obtain ⟨v, hvdeg⟩ := hG.exists_vert_degree_one_of_nontrivial
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hvdeg
  obtain ⟨w, hvw, hwuniq⟩ := hvdeg
  exact ⟨(v : α), v.2, (w : α), w.2, hvw,
    fun y hy hadj => congrArg Subtype.val (hwuniq ⟨y, hy⟩ hadj)⟩

end Work.PlanarSC
