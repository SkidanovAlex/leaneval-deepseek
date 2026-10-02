import Submission.EFL.Comm.InternalEdgesUpperRegAvg
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

/-!
# A port of `Commons.Combinatorics.SimpleGraph.upper_regular_exists_perfectMatching_general`

The paper's Proposition `internal-matching-prop`: an upper `(ρ,ξ)`-regular
graph on an even number of vertices with minimum degree at least `3ρm/4` has a
perfect matching.  This is the shared-commons lemma of the same name,
re-elaborated against *minimal* Mathlib imports so that it can be imported by
the `Submission` library (the commons file starts with the whole of Mathlib,
which exports `_root_.Hypergraph` and would make the fixed `Solution.lean`
ambiguous).
-/


open Finset
namespace Commons.Combinatorics.SimpleGraph
open SimpleGraph
set_option maxHeartbeats 32000000

section Classic

attribute [local instance 100] Classical.propDecidable

/-- Row decomposition of the number of adjacent ordered pairs inside a product. -/
private lemma card_filter_prod {α : Type*} (s t : Finset α) (r : α → α → Prop) [DecidableRel r] :
    ((s.product t).filter (fun p => r p.1 p.2)).card = ∑ x ∈ s, (t.filter (r x)).card := by
  classical
  rw [Finset.card_filter]
  rw [show (∑ i ∈ s.product t, (if r i.1 i.2 then (1 : ℕ) else 0))
        = ∑ x ∈ s, ∑ y ∈ t, (if r x y then 1 else 0) from Finset.sum_product s t _]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

/-- The sizes of the connected components of a finite graph sum to the number of vertices. -/
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

/-- The total size of the odd components of a finite graph is at most the number of vertices. -/
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
  rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj]
  simp only [SimpleGraph.Subgraph.top_adj]
  constructor
  · rintro ⟨-, -, -, -, h⟩; exact h
  · rintro h; exact ⟨a.2.1, a.2.2, b.2.1, b.2.2, h⟩

/-- The support of a connected component of `G - u`, viewed as a finset of `V`. -/
noncomputable def compFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u : Set V) (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) : Finset V :=
  (c.supp.toFinset).image Subtype.val

private lemma compFinset_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u : Set V) (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    (compFinset G u c).card = c.supp.ncard := by
  rw [compFinset, Finset.card_image_of_injective _ Subtype.val_injective, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

private lemma compFinset_nonempty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u : Set V) (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    (compFinset G u c).Nonempty := by
  obtain ⟨y, hy⟩ := c.nonempty_supp
  rw [compFinset]
  exact ⟨y.1, Finset.mem_image.mpr ⟨y, Set.mem_toFinset.mpr hy, rfl⟩⟩

private lemma compFinset_disjoint {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u : Set V) (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    Disjoint (compFinset G u c) u.toFinset := by
  rw [Finset.disjoint_left]
  intro x hx hxu
  rw [compFinset, Finset.mem_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [Set.mem_toFinset] at hxu
  rw [← hyx] at hxu
  have hyu : y.1 ∉ u := by
    have h := y.2
    simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_sdiff, Set.mem_univ, true_and] at h
    exact h
  exact hyu hxu

private lemma compFinset_closed {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u : Set V) (c : (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent) :
    ∀ v, v ∈ compFinset G u c → ∀ z, G.Adj v z → z ∈ compFinset G u c ∪ u.toFinset := by
  intro v hv z hz
  rw [compFinset, Finset.mem_image] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [← hyv] at hz
  by_cases hzu : z ∈ u
  · exact Finset.mem_union_right _ (by rw [Set.mem_toFinset]; exact hzu)
  · have hzv : z ∈ ((⊤ : G.Subgraph).deleteVerts u).verts := by
      simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
        Set.mem_sdiff, Set.mem_univ, true_and]; exact hzu
    refine Finset.mem_union_left _ ?_
    rw [compFinset, Finset.mem_image]
    exact ⟨⟨z, hzv⟩, Set.mem_toFinset.mpr
      (c.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hy)
        ((coe_deleteVerts_adj_iff G u y ⟨z, hzv⟩).mpr hz)), rfl⟩

private lemma sum_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u S : Finset V) (hdisj : Disjoint S u)
    (hcls : ∀ v ∈ S, ∀ z, G.Adj v z → z ∈ S ∪ u) :
    (∑ v ∈ S, (G.degree v : ℝ)) =
      (((S.product S).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
      (((S.product u).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
  classical
  have hrow : ∑ v ∈ S, (G.neighborFinset v).card =
      ((S.product (S ∪ u)).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [card_filter_prod S (S ∪ u) G.Adj]
    apply Finset.sum_congr rfl
    intro v hv
    have heq : G.neighborFinset v = (S ∪ u).filter (G.Adj v) := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
      exact ⟨fun h => ⟨hcls v hv w h, h⟩, fun h => h.2⟩
    rw [heq]
  have hsplit : ((S.product (S ∪ u)).filter (fun p => G.Adj p.1 p.2)).card =
      ((S.product S).filter (fun p => G.Adj p.1 p.2)).card +
      ((S.product u).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [Finset.product_eq_sprod, Finset.product_eq_sprod (s := S) (t := S), Finset.product_eq_sprod (s := S) (t := u),
      Finset.product_union, Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inr hdisj)))]
  have hdeg : ∀ v, (G.degree v : ℝ) = ((G.neighborFinset v).card : ℝ) := by
    intro v; rw [SimpleGraph.card_neighborFinset_eq_degree]
  calc (∑ v ∈ S, (G.degree v : ℝ))
      = (∑ v ∈ S, ((G.neighborFinset v).card : ℝ)) := by simp_rw [hdeg]
    _ = ((∑ v ∈ S, (G.neighborFinset v).card : ℕ) : ℝ) := by push_cast; rfl
    _ = (((S.product (S ∪ u)).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by rw [hrow]
    _ = (((S.product S).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
        (((S.product u).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
          rw [hsplit]; push_cast; ring

/-- Averaging-based lower bound for the size of a "closed" set of vertices, only using the
trivial bound for edges towards `u`. -/
private lemma component_size_lower_avg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ)
    (hdeg : ∀ v : V, 3 * ρ * (Fintype.card V : ℝ) / 4 ≤ (G.degree v : ℝ))
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ))
    (u S : Finset V) (hdisj : Disjoint S u) (hne : S.Nonempty)
    (hcls : ∀ v ∈ S, ∀ z, G.Adj v z → z ∈ S ∪ u)
    (hcard : 2 * Nat.ceil (ξ * (Fintype.card V : ℝ)) ≤ S.card) :
    (3 * ρ * (Fintype.card V : ℝ) / 4 - (u.card : ℝ)) / (ρ + ξ) ≤ (S.card : ℝ) := by
  classical
  have hsum := sum_degree_eq G u S hdisj hcls
  have hcardpos : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hlow : (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4) ≤
      ∑ v ∈ S, (G.degree v : ℝ) := by
    have h : ∑ v ∈ S, (3 * ρ * (Fintype.card V : ℝ) / 4) ≤ ∑ v ∈ S, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun v _ => hdeg v)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h2e : (((S.product S).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (S.card : ℝ) ^ 2 := by
    have h := internal_edges_upper_reg_avg G (le_of_lt hρ) hξ hreg S hcard
    simpa only [Finset.product_eq_sprod] using h
  have heu : (((S.product u).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (S.card : ℝ) * (u.card : ℝ) := by
    have hsub : (S.product u).filter (fun p => G.Adj p.1 p.2) ⊆ S.product u :=
      Finset.filter_subset _ _
    have hnat := Finset.card_le_card hsub
    rw [Finset.product_eq_sprod (s := S) (t := u), Finset.card_product] at hnat
    exact_mod_cast hnat
  have hmain : (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4) ≤
      (S.card : ℝ) * ((ρ + ξ) * (S.card : ℝ) + (u.card : ℝ)) := by
    calc (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4)
        ≤ ∑ v ∈ S, (G.degree v : ℝ) := hlow
      _ = _ + _ := hsum
      _ ≤ (ρ + ξ) * (S.card : ℝ) ^ 2 + (S.card : ℝ) * (u.card : ℝ) := by linarith [h2e, heu]
      _ = (S.card : ℝ) * ((ρ + ξ) * (S.card : ℝ) + (u.card : ℝ)) := by ring
  have hρξ : 0 < ρ + ξ := by linarith
  have h1 := (mul_le_mul_iff_of_pos_left hcardpos).mp hmain
  rw [div_le_iff₀ hρξ]
  linarith

/-- Averaging + regularity based lower bound for the size of a "closed" set of vertices. -/
private lemma component_size_lower_reg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ)
    (hdeg : ∀ v : V, 3 * ρ * (Fintype.card V : ℝ) / 4 ≤ (G.degree v : ℝ))
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ))
    (u S : Finset V) (hdisj : Disjoint S u) (hne : S.Nonempty)
    (hcls : ∀ v ∈ S, ∀ z, G.Adj v z → z ∈ S ∪ u)
    (hcard : 2 * Nat.ceil (ξ * (Fintype.card V : ℝ)) ≤ S.card)
    (hS : ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ))
    (hu : ξ * (Fintype.card V : ℝ) ≤ (u.card : ℝ)) :
    3 * ρ * (Fintype.card V : ℝ) / (4 * (ρ + ξ)) - (u.card : ℝ) ≤ (S.card : ℝ) := by
  classical
  have hsum := sum_degree_eq G u S hdisj hcls
  have hcardpos : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hlow : (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4) ≤
      ∑ v ∈ S, (G.degree v : ℝ) := by
    have h : ∑ v ∈ S, (3 * ρ * (Fintype.card V : ℝ) / 4) ≤ ∑ v ∈ S, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun v _ => hdeg v)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h2e : (((S.product S).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (S.card : ℝ) ^ 2 := by
    have h := internal_edges_upper_reg_avg G (le_of_lt hρ) hξ hreg S hcard
    simpa only [Finset.product_eq_sprod] using h
  have heu : (((S.product u).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (S.card : ℝ) * (u.card : ℝ) := hreg S u hdisj hS hu
  have hmain : (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4) ≤
      (S.card : ℝ) * ((ρ + ξ) * ((S.card : ℝ) + (u.card : ℝ))) := by
    calc (S.card : ℝ) * (3 * ρ * (Fintype.card V : ℝ) / 4)
        ≤ ∑ v ∈ S, (G.degree v : ℝ) := hlow
      _ = _ + _ := hsum
      _ ≤ (ρ + ξ) * (S.card : ℝ) ^ 2 + (ρ + ξ) * (S.card : ℝ) * (u.card : ℝ) := by
            linarith [h2e, heu]
      _ = (S.card : ℝ) * ((ρ + ξ) * ((S.card : ℝ) + (u.card : ℝ))) := by ring
  have hρξ : 0 < ρ + ξ := by linarith
  have h1 := (mul_le_mul_iff_of_pos_left hcardpos).mp hmain
  have h2 : 3 * ρ * (Fintype.card V : ℝ) / (4 * (ρ + ξ)) ≤
      (S.card : ℝ) + (u.card : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (ρ + ξ))]
    linarith
  linarith





/-- If all components in `sm` are small (size `< K2 = 2⌈ξm⌉`) and `ξm ≤ s < m/2`, then their
total size is less than `ξm`. -/
private lemma small_union_lt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ)
    (u : Set V) (s : ℕ) (hs : s = u.ncard) (m : ℕ) (hm : m = Fintype.card V)
    (hξm1 : 1 < ξ * (m : ℝ))
    (hdeg : ∀ v : V, 3 * ρ * (Fintype.card V : ℝ) / 4 ≤ (G.degree v : ℝ))
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ))
    (hsge : ξ * (m : ℝ) ≤ (s : ℝ)) (hslt : (s : ℝ) < (m : ℝ) / 2)
    (K2 : ℕ) (hK2 : K2 = 2 * Nat.ceil (ξ * (m : ℝ)))
    (sm : Finset (((⊤ : G.Subgraph).deleteVerts u).coe).ConnectedComponent)
    (hsm_small : ∀ c ∈ sm, c.supp.ncard < K2) :
    (∑ c ∈ sm, (c.supp.ncard : ℝ)) < ξ * (m : ℝ) := by
  have hmR : (m : ℝ) = (Fintype.card V : ℝ) := by rw [hm]
  have hut : ((u.toFinset.card : ℕ) : ℝ) = (s : ℝ) := by
    rw [← Set.ncard_eq_toFinset_card' u, ← hs]
  by_contra hcon0
  have hcon : ξ * (m : ℝ) ≤ (∑ c ∈ sm, (c.supp.ncard : ℝ)) := not_lt.mp hcon0
  have hsf_disj : ∀ c ∈ sm, ∀ c' ∈ sm, c ≠ c' →
      Disjoint (compFinset G u c) (compFinset G u c') := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [compFinset, Finset.mem_image, Set.mem_toFinset] at hx hx'
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨y', hy', hy'x⟩ := hx'
    have hyy : y = y' := Subtype.val_injective (by rw [hyx, hy'x])
    have hy1 : y ∈ c.supp := hy
    have hy2' : y' ∈ c'.supp := hy'
    have hy2 : y ∈ c'.supp := by rw [hyy]; exact hy2'
    exact hne (_root_.SimpleGraph.ConnectedComponent.eq_of_common_vertex hy1 hy2)
  set Zf : Finset V := sm.biUnion (fun c => compFinset G u c) with hZfE
  have hZf_card : Zf.card = ∑ c ∈ sm, c.supp.ncard := by
    rw [hZfE, Finset.card_biUnion (fun a ha b hb hne => hsf_disj a ha b hb hne)]
    exact Finset.sum_congr rfl (fun c _ => compFinset_card G u c)
  have hZf_ge : ξ * (m : ℝ) ≤ (Zf.card : ℝ) := by
    have h1 : ((∑ c ∈ sm, c.supp.ncard : ℕ) : ℝ) = ∑ c ∈ sm, (c.supp.ncard : ℝ) := by
      push_cast; rfl
    rw [hZf_card, h1]
    exact hcon
  have hZf_pos : 0 < Zf.card := by
    have : (0 : ℝ) < (Zf.card : ℝ) := lt_of_lt_of_le (by positivity) hZf_ge
    exact_mod_cast this
  have hmemZ : ∀ v ∈ Zf, ∃ c ∈ sm, v ∈ compFinset G u c ∧ c.supp.ncard < K2 := by
    intro v hv
    rw [hZfE, Finset.mem_biUnion] at hv
    obtain ⟨c, hc, hvc⟩ := hv
    exact ⟨c, hc, hvc, hsm_small c hc⟩
  have hclsZ : ∀ v ∈ Zf, ∀ z, G.Adj v z → z ∈ Zf ∪ u.toFinset := by
    intro v hv z hz
    obtain ⟨c, hc, hvc, _⟩ := hmemZ v hv
    have h2 : z ∈ compFinset G u c ∪ u.toFinset := compFinset_closed G u c v hvc z hz
    rcases Finset.mem_union.mp h2 with h3 | h3
    · exact Finset.mem_union_left _ (by
        rw [hZfE]; exact Finset.mem_biUnion.mpr ⟨c, hc, h3⟩)
    · exact Finset.mem_union_right _ h3
  have hdisjZ : Disjoint Zf u.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hxu
    obtain ⟨c, hc, hxc, _⟩ := hmemZ x hx
    exact (Finset.disjoint_left.mp (compFinset_disjoint G u c)) hxc hxu
  have hdegsum := sum_degree_eq G u.toFinset Zf hdisjZ hclsZ
  have hint : (((Zf.product Zf).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (Zf.card : ℝ) * ((K2 : ℝ) - 2) := by
    rw [card_filter_prod Zf Zf G.Adj]
    have hterm : ∀ v ∈ Zf, (Zf.filter (G.Adj v)).card ≤ K2 - 2 := by
      intro v hv
      obtain ⟨c, hc, hvc, hcomp⟩ := hmemZ v hv
      have hsub : Zf.filter (G.Adj v) ⊆ (compFinset G u c).erase v := by
        intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨hzZ, hzv⟩ := hz
        obtain ⟨c', hc', hzc', _⟩ := hmemZ z hzZ
        simp only [compFinset, Finset.mem_image, Set.mem_toFinset] at hvc hzc'
        obtain ⟨y, hy, hyv⟩ := hvc
        obtain ⟨y', hy', hy'z⟩ := hzc'
        rw [← hyv, ← hy'z] at hzv
        have hsu : y' ∈ c.supp :=
          c.mem_supp_of_adj_mem_supp hy ((coe_deleteVerts_adj_iff G u y y').mpr hzv)
        have hin : y' ∈ c'.supp := hy'
        have hcc' : c' = c :=
          _root_.SimpleGraph.ConnectedComponent.eq_of_common_vertex hin hsu
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro h
          rw [← hyv, ← hy'z] at h
          exact G.irrefl (h ▸ hzv)
        · rw [← hcc', ← hy'z]
          simp only [compFinset, Finset.mem_image, Set.mem_toFinset]
          exact ⟨y', hy', rfl⟩
      calc (Zf.filter (G.Adj v)).card ≤ ((compFinset G u c).erase v).card :=
            Finset.card_le_card hsub
        _ = (compFinset G u c).card - 1 := Finset.card_erase_of_mem hvc
        _ = c.supp.ncard - 1 := by rw [compFinset_card]
        _ ≤ K2 - 2 := by omega
    have hsum_le : (∑ v ∈ Zf, (Zf.filter (G.Adj v)).card) ≤ Zf.card * (K2 - 2) := by
      calc (∑ v ∈ Zf, (Zf.filter (G.Adj v)).card) ≤ ∑ v ∈ Zf, (K2 - 2) :=
            Finset.sum_le_sum (fun v hv => hterm v hv)
        _ = Zf.card * (K2 - 2) := by rw [Finset.sum_const, smul_eq_mul]
    have hK2ge2 : 2 ≤ K2 := by
      rw [hK2]
      have hc1 : (1 : ℝ) < (Nat.ceil (ξ * (m : ℝ)) : ℝ) :=
        lt_of_lt_of_le hξm1 (Nat.le_ceil _)
      have : 1 < Nat.ceil (ξ * (m : ℝ)) := by exact_mod_cast hc1
      omega
    have hcast : ((∑ v ∈ Zf, (Zf.filter (G.Adj v)).card : ℕ) : ℝ) ≤
        ((Zf.card * (K2 - 2) : ℕ) : ℝ) := Nat.cast_le.mpr hsum_le
    have hcast2 : ((Zf.card * (K2 - 2) : ℕ) : ℝ) = (Zf.card : ℝ) * ((K2 : ℝ) - 2) := by
      rw [Nat.cast_mul, Nat.cast_sub hK2ge2, Nat.cast_ofNat]
    linarith [hcast, hcast2.ge, hcast2.le]
  have heu : (((Zf.product u.toFinset).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
      (ρ + ξ) * (Zf.card : ℝ) * (s : ℝ) := by
    have h := hreg Zf u.toFinset hdisjZ (by rw [← hmR]; exact hZf_ge)
      (by rw [hut, ← hmR]; exact hsge)
    rwa [hut] at h
  have hlow : (Zf.card : ℝ) * (3 * ρ * (m : ℝ) / 4) ≤ ∑ v ∈ Zf, (G.degree v : ℝ) := by
    have h : ∑ v ∈ Zf, (3 * ρ * (m : ℝ) / 4) ≤ ∑ v ∈ Zf, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun v _ => by rw [hmR]; exact hdeg v)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hbig3 : 3 * ρ * (m : ℝ) / 4 ≤ ((K2 : ℝ) - 2) + (ρ + ξ) * (s : ℝ) := by
    have hmul : (Zf.card : ℝ) * (3 * ρ * (m : ℝ) / 4) ≤
        (Zf.card : ℝ) * (((K2 : ℝ) - 2) + (ρ + ξ) * (s : ℝ)) := by
      calc (Zf.card : ℝ) * (3 * ρ * (m : ℝ) / 4) ≤ ∑ v ∈ Zf, (G.degree v : ℝ) := hlow
        _ = _ + _ := hdegsum
        _ ≤ (Zf.card : ℝ) * ((K2 : ℝ) - 2) + (ρ + ξ) * (Zf.card : ℝ) * (s : ℝ) := by
              linarith [hint, heu]
        _ = (Zf.card : ℝ) * (((K2 : ℝ) - 2) + (ρ + ξ) * (s : ℝ)) := by ring
    have hZfR : (0 : ℝ) < (Zf.card : ℝ) := by exact_mod_cast hZf_pos
    exact (mul_le_mul_iff_of_pos_left hZfR).mp hmul
  have hK2le : ((K2 : ℝ) - 2) ≤ 2 * ξ * (m : ℝ) := by
    have hceil : (Nat.ceil (ξ * (m : ℝ)) : ℝ) ≤ ξ * (m : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ ξ * (m : ℝ) := by positivity
      have := Nat.ceil_lt_add_one h0
      linarith
    rw [hK2]; push_cast; linarith
  have hξle : 2 * ξ * (m : ℝ) ≤ ρ * (m : ℝ) / 5 := by
    nlinarith [hξρ, Nat.cast_nonneg (α := ℝ) m]
  have hs_lt2 : (ρ + ξ) * (s : ℝ) < 11 * ρ * (m : ℝ) / 20 := by
    have hρξ11 : ρ + ξ ≤ 11 * ρ / 10 := by linarith
    have h1 : (ρ + ξ) * (s : ℝ) < (ρ + ξ) * ((m : ℝ) / 2) := by
      apply mul_lt_mul_of_pos_left hslt; linarith
    have h2 : (ρ + ξ) * ((m : ℝ) / 2) ≤ (11 * ρ / 10) * ((m : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_right hρξ11 (by linarith)
    linarith
  linarith [hbig3, hK2le, hξle, hs_lt2]

end Classic

/-- Positivity of the "averaging + regularity" lower bound. -/
private lemma Fb_aux_pos {m s : ℕ} {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ)
    (hmpos : (0 : ℝ) < (m : ℝ)) (hslt : (s : ℝ) < (m : ℝ) / 2) :
    0 < 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ) := by
  by_contra hcon
  have h1 : 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) ≤ (s : ℝ) := by
    have h := not_lt.mp hcon
    linarith
  have h3 : 3 * ρ / (4 * (ρ + ξ)) < (1 : ℝ) / 2 := by
    have hmul : 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) < (m : ℝ) / 2 := by linarith [h1, hslt]
    have hmul2 : (m : ℝ) / 2 = ((1 : ℝ) / 2) * (m : ℝ) := by ring
    have hmul3 : 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) = (3 * ρ / (4 * (ρ + ξ))) * (m : ℝ) := by
      ring
    rw [hmul3, hmul2] at hmul
    exact (mul_lt_mul_iff_of_pos_right hmpos).mp hmul
  have h4 : 3 * ρ < 2 * (ρ + ξ) := by
    have hρξpos : (0 : ℝ) < 4 * (ρ + ξ) := by linarith
    have := (div_lt_iff₀ hρξpos).mp h3
    linarith
  nlinarith [h4, hξρ, hρ, hξ]

/-- Arithmetic core of Case I (`ξm ≤ 1`). -/
private lemma arith_caseI {m s : ℕ} {ρ : ℝ} (hρge : (10 : ℝ) / 11 ≤ ρ) (hmnn : (0 : ℝ) ≤ (m : ℝ))
    (hslt : (s : ℝ) < (m : ℝ) / 2)
    (hkey : ((s : ℝ) + 2) * (3 * ρ * (m : ℝ) / 4 + 1 - (s : ℝ)) ≤ (m : ℝ) - (s : ℝ)) : False := by
  have hge : (15 : ℝ) * (m : ℝ) / 22 ≤ 3 * ρ * (m : ℝ) / 4 := by nlinarith [hρge, hmnn]
  have hstep2 : ((s : ℝ) + 2) * (15 * (m : ℝ) / 22 + 1 - (s : ℝ)) ≤ (m : ℝ) - (s : ℝ) := by
    have h6 : ((s : ℝ) + 2) * (15 * (m : ℝ) / 22 + 1 - (s : ℝ)) ≤
        ((s : ℝ) + 2) * (3 * ρ * (m : ℝ) / 4 + 1 - (s : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hfac : 0 ≤ (s : ℝ) * (15 * (m : ℝ) / 22 - (s : ℝ)) := by
    apply mul_nonneg (Nat.cast_nonneg s)
    nlinarith [hslt, hmnn]
  have hexp : (s : ℝ) * (15 * (m : ℝ) / 22 - (s : ℝ)) + 4 * (m : ℝ) / 11 + 2 ≤ 0 := by
    nlinarith [hstep2]
  nlinarith [hexp, hfac, hmnn]

/-- Arithmetic core of Case B (`s < ξm`). -/
private lemma arith_caseB {m s : ℕ} {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ)
    (hmpos : (0 : ℝ) < (m : ℝ)) (hsm : (s : ℝ) < ξ * (m : ℝ))
    (hkey : ((s : ℝ) + 2) * ((3 * ρ * (m : ℝ) / 4 - (s : ℝ)) / (ρ + ξ)) ≤ (m : ℝ) - (s : ℝ)) :
    False := by
  have hF1g : (13 : ℝ) * (m : ℝ) / 22 < (3 * ρ * (m : ℝ) / 4 - (s : ℝ)) / (ρ + ξ) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < ρ + ξ)]
    nlinarith [hsm, hξρ, hξ, hρ, hmpos]
  have hms : (m : ℝ) - (s : ℝ) ≤ (m : ℝ) / 2 * ((s : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) s, hmpos]
  have hspos : (0 : ℝ) < (s : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  have hstep : ((s : ℝ) + 2) * (13 * (m : ℝ) / 22) < (m : ℝ) / 2 * ((s : ℝ) + 2) := by
    have h2 := mul_lt_mul_of_pos_left hF1g hspos
    linarith [h2, hkey, hms]
  nlinarith [hstep, hspos, hmpos]

/-- Arithmetic core of Case A (`ξm ≤ s`). -/
private lemma arith_caseA {m s : ℕ} {ρ ξ : ℝ} (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hmpos : (0 : ℝ) < (m : ℝ)) (hξm1 : 1 < ξ * (m : ℝ))
    (hsge : ξ * (m : ℝ) ≤ (s : ℝ)) (hslt : (s : ℝ) < (m : ℝ) / 2)
    (hkey : ((s : ℝ) + 2 - ξ * (m : ℝ)) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) <
      (m : ℝ) - (s : ℝ)) : False := by
  have hFb_pos : 0 < 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ) :=
    Fb_aux_pos hρ hξ hξρ hmpos hslt
  have hξ10 : ξ ≤ 1 / 10 := by nlinarith [hξρ, hρ1]
  have h2Fb : 2 * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) < (m : ℝ) - (s : ℝ) := by
    have h1 : (2 : ℝ) ≤ (s : ℝ) + 2 - ξ * (m : ℝ) := by linarith
    have h2 : (2 : ℝ) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) ≤
        ((s : ℝ) + 2 - ξ * (m : ℝ)) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hFb_pos)
    linarith [hkey, h2]
  set g : ℝ := 3 * ρ / (4 * (ρ + ξ)) with hg
  set w : ℝ := (s : ℝ) / (m : ℝ) with hw
  have hw_eq : (s : ℝ) = w * (m : ℝ) := by rw [hw]; field_simp
  have hFb_eq : 3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ) = (g - w) * (m : ℝ) := by
    rw [hg, hw]
    field_simp
    try ring
  have hgeq : (15 : ℝ) / 22 ≤ g := by
    rw [hg, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (ρ + ξ))]
    nlinarith [hξρ, hρ, hξ]
  have hw_le : w < 1 / 2 := by rw [hw, div_lt_iff₀ hmpos]; linarith
  have hwe : ξ ≤ w := by rw [hw, le_div_iff₀ hmpos]; linarith
  have hw_gt : 2 * g - 1 < w := by
    rw [hFb_eq, hw_eq] at h2Fb
    have h1 : 2 * (g - w) < 1 - w := by
      have h3 : (2 * (g - w)) * (m : ℝ) < (1 - w) * (m : ℝ) := by nlinarith [h2Fb]
      exact (mul_lt_mul_iff_of_pos_right hmpos).mp h3
    linarith
  have hky : (w - ξ) * (g - w) * (m : ℝ) < 1 + w - 2 * g := by
    rw [hFb_eq, hw_eq] at hkey
    have h2 : (((w - ξ) * (m : ℝ) + 2) * (g - w)) * (m : ℝ) < (1 - w) * (m : ℝ) := by
      nlinarith [hkey]
    have h1 : ((w - ξ) * (m : ℝ) + 2) * (g - w) < 1 - w :=
      (mul_lt_mul_iff_of_pos_right hmpos).mp h2
    nlinarith [h1]
  have hA : (29 : ℝ) / 110 < w - ξ := by linarith [hwe, hw_gt, hgeq, hξ10]
  have hB : (2 : ℝ) / 11 < g - w := by linarith [hw_le, hgeq]
  have hC : 1 + w - 2 * g < 3 / 22 := by linarith [hw_le, hgeq]
  nlinarith [hky, hA, hB, hC, hmpos, hξm1, hξ10]



theorem upper_regular_exists_perfectMatching_general {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℕ} {ρ ξ : ℝ}
    (hρ : 0 < ρ) (hξ : 0 ≤ ξ) (hξρ : 10 * ξ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hB : (B : ℝ) ≤ ρ ^ 2 * (Fintype.card V : ℝ)) (heven : Even (Fintype.card V))
    (hdeg : ∀ v : V, 3 * ρ * (Fintype.card V : ℝ) / 4 ≤ (G.degree v : ℝ))
    (hreg : ∀ S T : Finset V, Disjoint S T → ξ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) →
      ξ * (Fintype.card V : ℝ) ≤ (T.card : ℝ) →
      (((S.product T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≤
        (ρ + ξ) * (S.card : ℝ) * (T.card : ℝ)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  rw [SimpleGraph.tutte]
  intro u hu
  set m : ℕ := Fintype.card V with hm
  have hmR : (m : ℝ) = (Fintype.card V : ℝ) := by rw [hm]
  let TT := (⊤ : G.Subgraph).deleteVerts u
  let H : SimpleGraph ↥TT.verts := TT.coe
  haveI hAdj : DecidableRel H.Adj := inferInstance
  have hcardW : Fintype.card ↥TT.verts = m - u.ncard := by
    rw [hm, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, SimpleGraph.Subgraph.deleteVerts_verts,
        SimpleGraph.Subgraph.verts_top, Set.ncard_sdiff (Set.subset_univ u), Set.ncard_univ,
        Nat.card_eq_fintype_card]
  set s : ℕ := u.ncard with hs
  set oc : Finset H.ConnectedComponent := H.oddComponents.toFinset with hocC
  set t : ℕ := oc.card with ht
  have ht_gt : s < t := by
    have h1 : H.oddComponents.ncard = oc.card := by rw [hocC, Set.ncard_eq_toFinset_card']
    rw [hs, ht, ← h1]
    exact hu
  -- ## Basic numerical facts about the Tutte violator
  have hsle : s ≤ m := by
    rw [hs, hm]
    calc u.ncard ≤ (Set.univ : Set V).ncard := Set.ncard_le_ncard (Set.subset_univ u)
      _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hut : ((u.toFinset.card : ℕ) : ℝ) = (s : ℝ) := by
    rw [← Set.ncard_eq_toFinset_card' u, ← hs]
  have hsum_odd : (∑ c ∈ oc, c.supp.ncard) ≤ m - s := by
    rw [hocC, hs, ← hcardW]
    exact sum_oddComponents_supp_le H
  have hone : ∀ c ∈ oc, 1 ≤ c.supp.ncard := by
    intro c _
    have h := Set.ncard_pos (s := c.supp)
    exact h.mpr c.nonempty_supp
  have ht_le_sum : t ≤ ∑ c ∈ oc, c.supp.ncard := by
    calc oc.card = ∑ c ∈ oc, 1 := Finset.card_eq_sum_ones oc
      _ ≤ ∑ c ∈ oc, c.supp.ncard := Finset.sum_le_sum (fun c hc => hone c hc)
  have hpar : Odd t ↔ Odd s := by
    have h1 : Odd t ↔ Odd (m - s) := by
      have h2 : H.oddComponents.ncard = t := by rw [ht, hocC, Set.ncard_eq_toFinset_card']
      have h3 : Nat.card ↥TT.verts = m - s := by
        rw [Nat.card_eq_fintype_card, hcardW, hs]
      rw [← h2, _root_.SimpleGraph.odd_ncard_oddComponents, h3]
    rw [h1]
    have hev : Even (m - s) ↔ Even s := by
      have hsub : m - s + s = m := Nat.sub_add_cancel hsle
      have h1 : Even (m - s + s) := by rw [hsub]; exact heven
      exact Nat.even_add.mp h1
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd]
    exact not_congr hev
  have ht2 : s + 2 ≤ t := by
    have hmod : t % 2 = s % 2 := by
      rw [Nat.odd_iff, Nat.odd_iff] at hpar
      omega
    omega
  have h2s : 2 * s < m := by omega
  have hslt : (s : ℝ) < (m : ℝ) / 2 := by
    have h : (2 : ℝ) * (s : ℝ) < (m : ℝ) := by exact_mod_cast h2s
    linarith
  -- ## Every odd component has size at least `3ρm/4 + 1 - s`
  have hsz3_le : ∀ c ∈ oc, (3 * ρ * (m : ℝ) / 4 + 1 - (s : ℝ)) ≤ (c.supp.ncard : ℝ) := by
    intro c hc
    obtain ⟨v, hv⟩ := c.nonempty_supp
    have hv' : (v : ↥TT.verts) ∈ c.supp := hv
    have hsub : insert v.1 (G.neighborSet v.1) ⊆
        u ∪ (Subtype.val '' (c.supp : Set ↥TT.verts)) := by
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inr ⟨v, hv', rfl⟩
      · rw [SimpleGraph.mem_neighborSet] at hw
        by_cases hwu : w ∈ u
        · exact Or.inl hwu
        · right
          let w' : ↥TT.verts := ⟨w, by
            simp only [TT, SimpleGraph.Subgraph.deleteVerts_verts,
              SimpleGraph.Subgraph.verts_top, Set.mem_diff, Set.mem_univ, true_and]; exact hwu⟩
          have hadj : H.Adj v w' := (coe_deleteVerts_adj_iff G u v w').mpr hw
          exact ⟨w', c.mem_supp_of_adj_mem_supp hv' hadj, rfl⟩
    have hkey : (G.neighborSet v.1).ncard + 1 ≤ u.ncard + c.supp.ncard := by
      calc (G.neighborSet v.1).ncard + 1
          = (insert v.1 (G.neighborSet v.1)).ncard :=
              (Set.ncard_insert_of_notMem (fun h => G.irrefl h)).symm
        _ ≤ (u ∪ (Subtype.val '' (c.supp : Set ↥TT.verts))).ncard := Set.ncard_le_ncard hsub
        _ ≤ u.ncard + (Subtype.val '' (c.supp : Set ↥TT.verts)).ncard := Set.ncard_union_le u _
        _ = u.ncard + c.supp.ncard := by rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    have hdv := hdeg v.1
    have hdegv : (G.neighborSet v.1).ncard = G.degree v.1 := by
      rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def,
        SimpleGraph.card_neighborFinset_eq_degree]
    rw [← hdegv, ← hmR] at hdv
    have hkeyR : ((G.neighborSet v.1).ncard : ℝ) + 1 ≤ (u.ncard : ℝ) + (c.supp.ncard : ℝ) := by
      exact_mod_cast hkey
    rw [hs]
    push_cast
    linarith
  -- ## Splitting the sum over the odd components at `K2 = 2⌈ξm⌉`
  let K2 : ℕ := 2 * Nat.ceil (ξ * (m : ℝ))
  have hK2val : K2 = 2 * Nat.ceil (ξ * (m : ℝ)) := rfl
  let sm : Finset H.ConnectedComponent := oc.filter (fun c => c.supp.ncard < K2)
  have hsm_def : sm = oc.filter (fun c => c.supp.ncard < K2) := rfl
  let bg : Finset H.ConnectedComponent := oc.filter (fun c => K2 ≤ c.supp.ncard)
  have hbg_def : bg = oc.filter (fun c => K2 ≤ c.supp.ncard) := rfl
  have hsm_card : sm.card + bg.card = t := by
    have hbg2 : bg = oc.filter (fun c => ¬ (c.supp.ncard < K2)) := by
      rw [hbg_def]
      apply Finset.filter_congr
      intro c _
      omega
    rw [ht, hsm_def, hbg2]
    exact Finset.card_filter_add_card_filter_not (s := oc) (p := fun c => c.supp.ncard < K2)
  by_cases hξm1 : ξ * (m : ℝ) ≤ 1
  · -- ## Case I: `ξm ≤ 1`
    have hVne : Nonempty V := by
      have h1 : 0 < t := by omega
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (by rw [← ht]; exact h1)
      obtain ⟨y, _⟩ := c.nonempty_supp
      exact ⟨y.1⟩
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hVne
      rw [hm]; exact_mod_cast this
    obtain ⟨v0⟩ := hVne
    have hdegpos : 0 < (G.degree v0 : ℝ) := by
      have h := hdeg v0
      rw [← hmR] at h
      have : 0 < 3 * ρ * (m : ℝ) / 4 := by positivity
      linarith
    have hneigh : (G.neighborFinset v0).Nonempty := by
      rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast hdegpos
    obtain ⟨w0, hw0⟩ := hneigh
    have hadj : G.Adj v0 w0 := by rwa [SimpleGraph.mem_neighborFinset] at hw0
    have hdisj1 : Disjoint ({v0} : Finset V) ({w0} : Finset V) := by
      rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
      intro h
      exact G.irrefl (h ▸ hadj)
    have hsing : ξ * (m : ℝ) ≤ (({v0} : Finset V).card : ℝ) := by
      simp only [Finset.card_singleton, Nat.cast_one]; linarith
    have hr := hreg {v0} {w0} hdisj1 hsing hsing
    have hmem : (v0, w0) ∈ (({v0} : Finset V) ×ˢ ({w0} : Finset V)).filter
        (fun p => G.Adj p.1 p.2) := by
      simp [hadj]
    have hcard1 : (1 : ℝ) ≤ (((({v0} : Finset V) ×ˢ ({w0} : Finset V)).filter
        (fun p => G.Adj p.1 p.2)).card : ℝ) := by
      have h := Finset.card_pos.mpr ⟨(v0, w0), hmem⟩
      exact_mod_cast h
    have hρξ1 : 1 ≤ ρ + ξ := by
      have hr' := hr
      rw [Finset.product_eq_sprod] at hr'
      simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hr'
      linarith [hr', hcard1]
    have hρge : (10 : ℝ) / 11 ≤ ρ := by
      have : 11 * ρ ≥ 10 := by nlinarith [hρξ1, hξρ]
      linarith
    have hstep : ((s : ℝ) + 2) * (3 * ρ * (m : ℝ) / 4 + 1 - s) ≤ (m : ℝ) - s := by
      have h2R : ((s : ℝ) + 2) ≤ (t : ℝ) := by exact_mod_cast ht2
      have hge : (15 : ℝ) * (m : ℝ) / 22 ≤ 3 * ρ * (m : ℝ) / 4 := by nlinarith [hρge, hmnn]
      have hC3pos : 0 < 3 * ρ * (m : ℝ) / 4 + 1 - s := by linarith [hge, hslt]
      have h3 : (∑ c ∈ oc, (3 * ρ * (m : ℝ) / 4 + 1 - s)) ≤
          (∑ c ∈ oc, (c.supp.ncard : ℝ)) := Finset.sum_le_sum (fun c hc => hsz3_le c hc)
      rw [Finset.sum_const, ← ht, nsmul_eq_mul] at h3
      have h4 : (∑ c ∈ oc, (c.supp.ncard : ℝ)) ≤ (m : ℝ) - s := by
        have h4' : ((∑ c ∈ oc, c.supp.ncard : ℕ) : ℝ) ≤ ((m - s : ℕ) : ℝ) := by
          exact_mod_cast hsum_odd
        rw [Nat.cast_sub hsle] at h4'
        push_cast at h4' ⊢
        linarith
      have h5 : ((s : ℝ) + 2) * (3 * ρ * (m : ℝ) / 4 + 1 - s) ≤
          (t : ℝ) * (3 * ρ * (m : ℝ) / 4 + 1 - s) :=
        mul_le_mul_of_nonneg_right h2R (le_of_lt hC3pos)
      linarith
    exact arith_caseI hρge hmnn hslt hstep
  · have hξm1lt : 1 < ξ * (m : ℝ) := not_le.mp hξm1
    have hξ10 : ξ ≤ 1 / 10 := by nlinarith [hξρ, hρ1]
    have hmpos : (0 : ℝ) < (m : ℝ) := by nlinarith [hξm1lt, hξ10, hξ]
    by_cases hsm_ge : ξ * (m : ℝ) ≤ s
    · -- ## Case A: `ξm ≤ s`
      have hFb : ∀ c ∈ oc, K2 ≤ c.supp.ncard →
          3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ) ≤ (c.supp.ncard : ℝ) := by
        intro c hc hbig
        have hSc : ((compFinset G u c).card : ℝ) =
            (c.supp.ncard : ℝ) := by exact_mod_cast compFinset_card G u c
        have hS : ξ * (Fintype.card V : ℝ) ≤
            ((compFinset G u c).card : ℝ) := by
          rw [hSc, ← hmR]
          calc ξ * (m : ℝ) ≤ 2 * (ξ * (m : ℝ)) := by linarith [hξ, hmnn]
            _ ≤ 2 * (Nat.ceil (ξ * (m : ℝ)) : ℝ) := by
                have := Nat.le_ceil (ξ * (m : ℝ)); linarith
            _ = ((K2 : ℕ) : ℝ) := by rw [hK2val]; push_cast; ring
            _ ≤ (c.supp.ncard : ℝ) := by exact_mod_cast hbig
        have hu2 : ξ * (Fintype.card V : ℝ) ≤ (u.toFinset.card : ℝ) := by
          rw [hut, ← hmR]; exact hsm_ge
        have hcard2 := component_size_lower_reg G hρ hξ hdeg hreg u.toFinset
          (compFinset G u c)
          (compFinset_disjoint G u c) (compFinset_nonempty G u c) (compFinset_closed G u c)
          (by rw [compFinset_card G u c]; exact hbig) hS hu2
        rw [hut, ← hmR] at hcard2
        rw [hSc, ← hmR] at hcard2
        exact hcard2
      have hsmall : (∑ c ∈ sm, (c.supp.ncard : ℝ)) < ξ * (m : ℝ) := by
        refine small_union_lt G hρ hξ hξρ u s hs m hm hξm1lt hdeg hreg hsm_ge hslt K2 hK2val sm ?_
        intro c hc
        rw [hsm_def] at hc
        exact (Finset.mem_filter.mp hc).2
      have hj_lt : (sm.card : ℝ) < ξ * (m : ℝ) := by
        have h1 : ∀ c ∈ sm, 1 ≤ c.supp.ncard := by
          intro c hc
          have h2 : c ∈ oc := (Finset.mem_filter.mp (hsm_def ▸ hc)).1
          exact hone c h2
        have h2 : (sm.card : ℝ) ≤ ∑ c ∈ sm, (c.supp.ncard : ℝ) := by
          have h : (∑ c ∈ sm, (1 : ℕ)) ≤ ∑ c ∈ sm, c.supp.ncard := Finset.sum_le_sum h1
          rw [Finset.sum_const, smul_eq_mul, mul_one] at h
          exact_mod_cast h
        linarith [hsmall]
      have hbgFb : (bg.card : ℝ) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) ≤
          ∑ c ∈ bg, (c.supp.ncard : ℝ) := by
        have h : (∑ c ∈ bg, (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ))) ≤
            ∑ c ∈ bg, (c.supp.ncard : ℝ) := by
          apply Finset.sum_le_sum
          intro c hc
          have hc' : c ∈ oc.filter (fun c => K2 ≤ c.supp.ncard) := by rw [← hbg_def]; exact hc
          exact hFb c (Finset.mem_filter.mp hc').1 (Finset.mem_filter.mp hc').2
        rw [Finset.sum_const, nsmul_eq_mul] at h
        exact h
      have hsum_bg : (∑ c ∈ bg, (c.supp.ncard : ℝ)) ≤ (m : ℝ) - s := by
        have h2 : (∑ c ∈ bg, c.supp.ncard) ≤ ∑ c ∈ oc, c.supp.ncard :=
          Finset.sum_le_sum_of_subset_of_nonneg (by rw [hbg_def]; exact Finset.filter_subset _ _)
            (fun c _ _ => Nat.zero_le _)
        have h3 : ((∑ c ∈ bg, c.supp.ncard : ℕ) : ℝ) ≤ ((m - s : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 hsum_odd
        rw [Nat.cast_sub hsle] at h3
        push_cast at h3 ⊢
        linarith
      have hcard_bg : (bg.card : ℝ) = (t : ℝ) - (sm.card : ℝ) := by
        have h1 : bg.card = t - sm.card := by omega
        rw [h1, Nat.cast_sub (by omega : sm.card ≤ t)]
      have hFb_le : ((s : ℝ) + 2 - ξ * (m : ℝ)) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) <
          (m : ℝ) - s := by
        have h1 : (s : ℝ) + 2 - ξ * (m : ℝ) < (bg.card : ℝ) := by
          rw [hcard_bg]
          have h2 : (t : ℝ) ≥ (s : ℝ) + 2 := by exact_mod_cast ht2
          linarith [hj_lt]
        have h3 : (bg.card : ℝ) * (3 * ρ * (m : ℝ) / (4 * (ρ + ξ)) - (s : ℝ)) ≤ (m : ℝ) - s :=
          le_trans hbgFb hsum_bg
        have h4 := mul_lt_mul_of_pos_right h1 (Fb_aux_pos hρ hξ hξρ hmpos hslt)
        linarith
      exact arith_caseA hρ hξ hξρ hρ1 hmpos hξm1lt hsm_ge hslt hFb_le
    · -- ## Case B: `s < ξm`
      have hsm_lt : s < ξ * (m : ℝ) := not_le.mp hsm_ge
      have hK2 : ∀ c ∈ oc, K2 ≤ c.supp.ncard := by
        intro c hc
        by_contra hcon
        have hcon : c.supp.ncard < K2 := not_le.mp hcon
        have h1 : 3 * ρ * (m : ℝ) / 4 + 1 - s ≤ (c.supp.ncard : ℝ) := hsz3_le c hc
        have h2 : (c.supp.ncard : ℝ) < 2 * (ξ * (m : ℝ)) + 2 := by
          have hceil : (Nat.ceil (ξ * (m : ℝ)) : ℝ) ≤ ξ * (m : ℝ) + 1 := by
            have h0 : (0 : ℝ) ≤ ξ * (m : ℝ) := by positivity
            have := Nat.ceil_lt_add_one h0
            linarith
          have h3 : (c.supp.ncard : ℝ) < 2 * (Nat.ceil (ξ * (m : ℝ)) : ℝ) := by
            have h4 : c.supp.ncard < 2 * Nat.ceil (ξ * (m : ℝ)) := by
              rw [← hK2val]; exact hcon
            exact_mod_cast h4
          linarith
        nlinarith [h1, h2, hsm_lt, hξρ, hξm1lt, hξ, hmpos, hρ]
      have hF1 : ∀ c ∈ oc, (3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ) ≤ (c.supp.ncard : ℝ) := by
        intro c hc
        have hcard2 := component_size_lower_avg G hρ hξ hdeg hreg u.toFinset
          (compFinset G u c)
          (compFinset_disjoint G u c) (compFinset_nonempty G u c) (compFinset_closed G u c)
          (by rw [compFinset_card G u c]; exact hK2 c hc)
        rw [hut, ← hmR] at hcard2
        have hSc : ((compFinset G u c).card : ℝ) =
            (c.supp.ncard : ℝ) := by exact_mod_cast compFinset_card G u c
        rw [hSc, ← hmR] at hcard2
        exact hcard2
      have hF1_le : ((s : ℝ) + 2) * ((3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ)) ≤ (m : ℝ) - s := by
        have h2R : ((s : ℝ) + 2) ≤ (t : ℝ) := by exact_mod_cast ht2
        have h3 : (∑ c ∈ oc, (3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ)) ≤
            (∑ c ∈ oc, (c.supp.ncard : ℝ)) := Finset.sum_le_sum (fun c hc => hF1 c hc)
        rw [Finset.sum_const, ← ht, nsmul_eq_mul] at h3
        have h4 : (∑ c ∈ oc, (c.supp.ncard : ℝ)) ≤ (m : ℝ) - s := by
          have h4' : ((∑ c ∈ oc, c.supp.ncard : ℕ) : ℝ) ≤ ((m - s : ℕ) : ℝ) := by
            exact_mod_cast hsum_odd
          rw [Nat.cast_sub hsle] at h4'
          push_cast at h4' ⊢
          linarith
        have hF1nn : 0 ≤ (3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ) := by
          apply div_nonneg _ (by linarith)
          nlinarith [hsm_lt, hξρ, hξ, hmnn]
        have h5 : ((s : ℝ) + 2) * ((3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ)) ≤
            (t : ℝ) * ((3 * ρ * (m : ℝ) / 4 - s) / (ρ + ξ)) :=
          mul_le_mul_of_nonneg_right h2R hF1nn
        linarith
      exact arith_caseB hρ hξ hξρ hmpos hsm_lt hF1_le

end Commons.Combinatorics.SimpleGraph
