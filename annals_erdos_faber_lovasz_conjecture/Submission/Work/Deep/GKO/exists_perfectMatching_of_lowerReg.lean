import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# A perfect matching in a lower-regular graph of even order

We prove `Work.Deep.GKO.exists_perfectMatching_of_lowerReg`: a lower `(p,ε)`-regular graph
on `n` vertices whose minimum degree is at least `αn` (with `α ≫ ε > 0`) has a perfect
matching, provided `n` is even.

The proof is the one from the paper (Theorem 10.8 of Kang--Kelly--Kühn--Methuku--Osthus,
via Glock--Kühn--Osthus): we verify Tutte's condition using `SimpleGraph.tutte`.  For
`u : Set (Fin n)` we must bound the number of odd components of `G - u` by `|u|`.

Write `K = εn` and let `C_1, …, C_t` be the components of `G - u`.

* (i) at most one component has `≥ K` vertices, since two disjoint vertex sets with no
  edges between them violate lower regularity;
* (ii) if some component `C` has `< K` vertices then every `v ∈ C` has all its neighbours
  in `C ∪ u`, so `αn ≤ d(v) < |C| + |u| < K + |u|`, i.e. `(α - ε)n < |u|`;
* (iii) counting: if a large component exists then the union of the others has `< K`
  vertices, so `t < 1 + K ≤ (α-ε)n < |u|` (using `1 ≤ (α - 2ε)n`); if all components are
  small then either `|G - u| < K`, or a greedy union of components of size in `[K, 2K)`
  has a complement of size `< K`, whence `|G - u| < 3K ≤ (α - ε)n < |u|`; always
  `t ≤ |G - u|`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open SimpleGraph

noncomputable section

variable {n : ℕ}

attribute [local instance 100] Classical.propDecidable

/-! ## The components of `G - u` -/

/-- The graph `G - u`, the subgraph of `G` induced on the complement of `u`; the ambient
graph of Tutte's theorem. -/
abbrev delGraph (G : SimpleGraph (Fin n)) (u : Set (Fin n)) :
    SimpleGraph ↥((⊤ : G.Subgraph).deleteVerts u).verts :=
  ((⊤ : G.Subgraph).deleteVerts u).coe

/-- The connected component `c` of `G - u`, viewed as a finset of vertices of `G`. -/
def compSet (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    (c : (delGraph G u).ConnectedComponent) : Finset (Fin n) :=
  (c.supp.toFinset).image Subtype.val

lemma compSet_card (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    (c : (delGraph G u).ConnectedComponent) :
    (compSet G u c).card = c.supp.ncard := by
  rw [compSet, Finset.card_image_of_injective _ Subtype.val_injective, Set.toFinset_card,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

lemma compSet_nonempty (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    (c : (delGraph G u).ConnectedComponent) : (compSet G u c).Nonempty := by
  obtain ⟨y, hy⟩ := c.nonempty_supp
  exact ⟨y.1, Finset.mem_image.mpr ⟨y, Set.mem_toFinset.mpr hy, rfl⟩⟩

lemma compSet_mem_verts (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {c : (delGraph G u).ConnectedComponent} {v : Fin n} (hv : v ∈ compSet G u c) :
    v ∈ ((⊤ : G.Subgraph).deleteVerts u).verts := by
  rw [compSet, Finset.mem_image] at hv
  obtain ⟨y, -, rfl⟩ := hv
  exact y.2

lemma compSet_notMem_u (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {c : (delGraph G u).ConnectedComponent} {v : Fin n} (hv : v ∈ compSet G u c) :
    v ∉ u := by
  have h := compSet_mem_verts G u hv
  simpa [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_univ] using h

lemma delGraph_adj_iff (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {a b : ↥((⊤ : G.Subgraph).deleteVerts u).verts} :
    (delGraph G u).Adj a b ↔ G.Adj a.1 b.1 := by
  show (((⊤ : G.Subgraph).deleteVerts u).coe).Adj a b ↔ G.Adj a.1 b.1
  rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj]
  simp only [SimpleGraph.Subgraph.top_adj]
  exact ⟨fun h => h.2.2.2.2, fun h => ⟨a.2.1, a.2.2, b.2.1, b.2.2, h⟩⟩

/-- All neighbours of a vertex of a component of `G - u` lie in that component or in `u`. -/
lemma compSet_closed (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {c : (delGraph G u).ConnectedComponent} {v z : Fin n} (hv : v ∈ compSet G u c)
    (hz : G.Adj v z) : z ∈ compSet G u c ∪ u.toFinset := by
  rw [compSet, Finset.mem_image] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [← hyv] at hz
  by_cases hzu : z ∈ u
  · exact Finset.mem_union_right _ (Set.mem_toFinset.mpr hzu)
  · have hzv : z ∈ ((⊤ : G.Subgraph).deleteVerts u).verts := by
      simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
        Set.mem_sdiff, Set.mem_univ, true_and]
      exact hzu
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨z, hzv⟩, Set.mem_toFinset.mpr ?_, rfl⟩)
    exact c.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hy) ((delGraph_adj_iff G u).mpr hz)

lemma compSet_pairwise_disjoint (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {c c' : (delGraph G u).ConnectedComponent} (hne : c ≠ c') :
    Disjoint (compSet G u c) (compSet G u c') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [compSet, Finset.mem_image, Set.mem_toFinset] at hx hx'
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨y', hy', hy'x⟩ := hx'
  have hyy : y = y' := Subtype.val_injective (by rw [hyx, hy'x])
  have h2 : y ∈ c'.supp := by rw [hyy]; exact hy'
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy h2)

lemma biUnion_disjoint_of_disjoint (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {X Y : Finset (delGraph G u).ConnectedComponent} (hXY : Disjoint X Y) :
    Disjoint (X.biUnion (compSet G u)) (Y.biUnion (compSet G u)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Finset.mem_biUnion] at ha hb
  obtain ⟨c, hc, hac⟩ := ha
  obtain ⟨c', hc', hac'⟩ := hb
  have hne : c ≠ c' := by
    intro h; rw [h] at hc; exact Finset.disjoint_left.mp hXY hc hc'
  exact Finset.disjoint_left.mp (compSet_pairwise_disjoint G u hne) hac hac'

lemma no_adj_between_components (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {c c' : (delGraph G u).ConnectedComponent} (hne : c ≠ c') {a b : Fin n}
    (ha : a ∈ compSet G u c) (hb : b ∈ compSet G u c') : ¬ G.Adj a b := by
  intro hab
  rw [compSet, Finset.mem_image] at ha hb
  obtain ⟨y, hy, hya⟩ := ha
  obtain ⟨y', hy', hy'b⟩ := hb
  rw [← hya, ← hy'b] at hab
  have h1 : y' ∈ c.supp :=
    c.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hy) ((delGraph_adj_iff G u).mpr hab)
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex h1 (Set.mem_toFinset.mp hy'))

lemma no_adj_between_unions (G : SimpleGraph (Fin n)) (u : Set (Fin n))
    {X Y : Finset (delGraph G u).ConnectedComponent} (hXY : Disjoint X Y) :
    ∀ a ∈ X.biUnion (compSet G u), ∀ b ∈ Y.biUnion (compSet G u), ¬ G.Adj a b := by
  intro a ha b hb hab
  rw [Finset.mem_biUnion] at ha hb
  obtain ⟨c, hc, hac⟩ := ha
  obtain ⟨c', hc', hbc⟩ := hb
  have hne : c ≠ c' := by
    intro h; rw [h] at hc; exact Finset.disjoint_left.mp hXY hc hc'
  exact no_adj_between_components G u hne hac hbc hab

lemma crossEdges_eq_zero_of_no_adj (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (h : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : crossEdges G A B = 0 := by
  unfold crossEdges
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product] at hp
  exact h p.1 hp.1.1 p.2 hp.1.2 hp.2

/-- Lower regularity forbids two disjoint vertex sets of size at least `εn` between which
there is no edge. -/
lemma false_of_two_large_sets (G : SimpleGraph (Fin n)) {p ε : ℝ}
    (hlr : LowerReg G p ε) (hε : 0 < ε) (hεp : ε < p) (hn : 0 < n)
    {A B : Finset (Fin n)} (hAB : Disjoint A B) (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hA : ε * (n : ℝ) ≤ (A.card : ℝ)) (hB : ε * (n : ℝ) ≤ (B.card : ℝ)) : False := by
  have hzero : crossEdges G A B = 0 := crossEdges_eq_zero_of_no_adj G A B hno
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKpos : 0 < ε * (n : ℝ) := mul_pos hε hnR
  have hAn : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hKpos hA
  have hBn : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le hKpos hB
  have hpe : (0 : ℝ) < p - ε := by linarith
  have hreg := hlr A B hAB hA hB
  rw [hzero, Nat.cast_zero] at hreg
  have hpos : (0 : ℝ) < (p - ε) * (A.card : ℝ) * (B.card : ℝ) := mul_pos (mul_pos hpe hAn) hBn
  linarith

/-- The same statement for two disjoint unions of components of `G - u`. -/
lemma false_of_two_large_unions (G : SimpleGraph (Fin n)) (u : Set (Fin n)) {p ε : ℝ}
    (hlr : LowerReg G p ε) (hε : 0 < ε) (hεp : ε < p) (hn : 0 < n)
    {X Y : Finset (delGraph G u).ConnectedComponent} (hXY : Disjoint X Y)
    (hX : ε * (n : ℝ) ≤ ((X.biUnion (compSet G u)).card : ℝ))
    (hY : ε * (n : ℝ) ≤ ((Y.biUnion (compSet G u)).card : ℝ)) : False :=
  false_of_two_large_sets G hlr hε hεp hn (biUnion_disjoint_of_disjoint G u hXY)
    (no_adj_between_unions G u hXY) hX hY

/-- A component of `G - u` with fewer than `εn` vertices forces `|u| > (α - ε)n`. -/
lemma lt_ncard_of_small_comp (G : SimpleGraph (Fin n)) (u : Set (Fin n)) {α ε : ℝ}
    (hdeg : ∀ v : Fin n, α * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ))
    {c : (delGraph G u).ConnectedComponent} (hc : ((compSet G u c).card : ℝ) < ε * (n : ℝ)) :
    (α - ε) * (n : ℝ) < (u.ncard : ℝ) := by
  obtain ⟨v, hv⟩ := compSet_nonempty G u c
  have hsub : G.neighborSet v ⊆ ((u.toFinset ∪ compSet G u c : Finset (Fin n)) : Set (Fin n)) := by
    intro z hz
    rw [SimpleGraph.mem_neighborSet] at hz
    rcases Finset.mem_union.mp (compSet_closed G u hv hz) with h | h
    · exact Finset.mem_coe.mpr (Finset.mem_union_right _ h)
    · exact Finset.mem_coe.mpr (Finset.mem_union_left _ h)
  have h1 : Nat.card (G.neighborSet v) ≤ (u.toFinset ∪ compSet G u c).card := by
    calc Nat.card (G.neighborSet v) = (G.neighborSet v).ncard := rfl
      _ ≤ ((u.toFinset ∪ compSet G u c : Finset (Fin n)) : Set (Fin n)).ncard :=
            Set.ncard_le_ncard hsub
      _ = (u.toFinset ∪ compSet G u c).card := Set.ncard_coe_finset _
  have h2 : ((u.toFinset ∪ compSet G u c).card : ℝ) ≤ (u.ncard : ℝ) + (compSet G u c).card := by
    have h3 := Finset.card_union_le u.toFinset (compSet G u c)
    have hu : (u.toFinset.card : ℝ) = (u.ncard : ℝ) := by
      rw [← Set.ncard_eq_toFinset_card' u]
    calc ((u.toFinset ∪ compSet G u c).card : ℝ)
        ≤ ((u.toFinset.card + (compSet G u c).card : ℕ) : ℝ) := by exact_mod_cast h3
      _ = (u.ncard : ℝ) + (compSet G u c).card := by rw [Nat.cast_add, hu]
  have h4 : α * (n : ℝ) ≤ ((u.toFinset ∪ compSet G u c).card : ℝ) := by
    calc α * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := hdeg v
      _ ≤ ((u.toFinset ∪ compSet G u c).card : ℝ) := by exact_mod_cast h1
  linarith

/-! ## Sizes of components, and a window lemma -/

/-- The sizes of the connected components of a finite graph sum to the number of vertices. -/
lemma sum_supp_ncard_eq_card {W : Type*} [Fintype W] [DecidableEq W]
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

/-- The number of vertices of `G - u` is `n - |u|`. -/
lemma card_verts_del (G : SimpleGraph (Fin n)) (u : Set (Fin n)) :
    Fintype.card ↥((⊤ : G.Subgraph).deleteVerts u).verts = n - u.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, SimpleGraph.Subgraph.deleteVerts_verts,
    SimpleGraph.Subgraph.verts_top, Set.ncard_sdiff (Set.subset_univ u), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The sizes of the components of `G - u` sum to `n - |u|`. -/
lemma sum_compSet_card (G : SimpleGraph (Fin n)) (u : Set (Fin n)) :
    ∑ c : (delGraph G u).ConnectedComponent, (compSet G u c).card = n - u.ncard :=
  calc ∑ c : (delGraph G u).ConnectedComponent, (compSet G u c).card
      = ∑ c : (delGraph G u).ConnectedComponent, c.supp.ncard :=
        Finset.sum_congr rfl (fun c _ => compSet_card G u c)
    _ = Fintype.card ↥((⊤ : G.Subgraph).deleteVerts u).verts :=
        sum_supp_ncard_eq_card (delGraph G u)
    _ = n - u.ncard := card_verts_del G u

/-- If a family of real numbers, each of them `< K`, has total sum at least `K`, then some
subfamily has sum in `[K, 2K)`. -/
lemma family_window {ι : Type*} [DecidableEq ι] (K : ℝ) (hK : 0 < K) (f : ι → ℝ)
    (C : Finset ι) (hf : ∀ c ∈ C, f c < K) (hsum : K ≤ ∑ c ∈ C, f c) :
    ∃ X : Finset ι, X ⊆ C ∧ K ≤ ∑ c ∈ X, f c ∧ ∑ c ∈ X, f c < 2 * K := by
  induction C using Finset.induction with
  | empty => simp at hsum; linarith
  | insert c C hc ih =>
      by_cases h : K ≤ ∑ x ∈ C, f x
      · obtain ⟨X, hXC, hX1, hX2⟩ := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) h
        exact ⟨X, fun x hx => Finset.mem_insert_of_mem (hXC hx), hX1, hX2⟩
      · push_neg at h
        refine ⟨insert c C, Finset.Subset.refl _, hsum, ?_⟩
        rw [Finset.sum_insert hc]
        linarith [hf c (Finset.mem_insert_self c C)]

/-! ## Tutte's condition -/

/-- **Tutte's condition.**  A lower `(p,ε)`-regular graph on `n` vertices of minimum degree
at least `αn` with `α ≥ 4ε`, `ε < p` and `1 ≤ (α - 2ε)n` satisfies `o(G - u) ≤ |u|` for
every `u`. -/
theorem oddComponents_ncard_le_of_lowerReg {G : SimpleGraph (Fin n)} {p ε α : ℝ}
    (hn : Even n) (hlr : LowerReg G p ε) (hε : 0 < ε) (hεp : ε < p) (hεα : 4 * ε ≤ α)
    (hdeg : ∀ v : Fin n, α * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ))
    (hbig : 1 ≤ (α - 2 * ε) * (n : ℝ)) :
    ∀ u : Set (Fin n), (delGraph G u).oddComponents.ncard ≤ u.ncard := by
  intro u
  have hn1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn0 : (n : ℝ) = 0 := by simp [Nat.le_zero.mp h]
    rw [hn0] at hbig
    norm_num at hbig
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  set K : ℝ := ε * (n : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; exact mul_pos hε hnR
  by_contra hcon
  have hviol : u.ncard < (delGraph G u).oddComponents.ncard := not_le.mp hcon
  set t : ℕ := Fintype.card (delGraph G u).ConnectedComponent with ht
  have hodd_le_t : (delGraph G u).oddComponents.ncard ≤ t := by
    have h1 : (delGraph G u).oddComponents.toFinset.card ≤
        (Finset.univ : Finset (delGraph G u).ConnectedComponent).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Set.ncard_eq_toFinset_card', ht]
    simpa [Finset.card_univ] using h1
  by_cases hbigcomp : ∃ c : (delGraph G u).ConnectedComponent, K ≤ ((compSet G u c).card : ℝ)
  · -- (1) some component has at least `K` vertices
    obtain ⟨c₀, hc₀⟩ := hbigcomp
    have huniq : ∀ c : (delGraph G u).ConnectedComponent, c ≠ c₀ →
        ((compSet G u c).card : ℝ) < K := by
      intro c hc
      by_contra hlt
      refine false_of_two_large_unions G u hlr hε hεp hn1 (X := {c}) (Y := {c₀}) ?_ ?_ ?_
      · rw [Finset.disjoint_singleton_right, Finset.mem_singleton]
        exact fun h => hc h.symm
      · simpa using (not_lt.mp hlt)
      · simpa using hc₀
    by_cases ht1 : t = 1
    · -- `t = 1`: parity of `n` rules out an odd component
      have hodd1 : (delGraph G u).oddComponents.ncard = 1 := by omega
      have hu0 : u.ncard = 0 := by omega
      have hb0 : Odd (delGraph G u).oddComponents.ncard := by
        rw [hodd1]; exact ⟨0, by norm_num⟩
      have hOddNat : Odd (Nat.card ↥((⊤ : G.Subgraph).deleteVerts u).verts) :=
        (SimpleGraph.odd_ncard_oddComponents (delGraph G u)).mp hb0
      have hcard : Nat.card ↥((⊤ : G.Subgraph).deleteVerts u).verts = n := by
        rw [Nat.card_eq_fintype_card, card_verts_del G u, hu0, Nat.sub_zero]
      exact (Nat.not_odd_iff_even.mpr hn) (hcard ▸ hOddNat)
    · -- `t ≥ 2`: a small component exists and the other components are few
      have ht2 : 2 ≤ t := by omega
      obtain ⟨c₁, hc₁⟩ : ∃ c : (delGraph G u).ConnectedComponent, c ≠ c₀ := by
        by_contra h
        push_neg at h
        have h1 : (Finset.univ : Finset (delGraph G u).ConnectedComponent).card ≤ 1 :=
          Finset.card_le_one.mpr (fun a _ b _ => by rw [h a, h b])
        rw [Finset.card_univ] at h1
        omega
      have hsmall₁ : ((compSet G u c₁).card : ℝ) < K := huniq c₁ hc₁
      have hsn : (α - ε) * (n : ℝ) < (u.ncard : ℝ) :=
        lt_ncard_of_small_comp G u hdeg hsmall₁
      have hsumErase : ∑ c ∈ (Finset.univ.erase c₀ : Finset (delGraph G u).ConnectedComponent),
          ((compSet G u c).card : ℝ) < K := by
        by_contra hlt
        have hge : K ≤ ∑ c ∈ Finset.univ.erase c₀, ((compSet G u c).card : ℝ) := not_lt.mp hlt
        refine false_of_two_large_unions G u hlr hε hεp hn1 (X := {c₀})
          (Y := Finset.univ.erase c₀) ?_ ?_ ?_
        · rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase c₀ _
        · simpa using hc₀
        · rw [Finset.card_biUnion (fun a _ b _ hne => compSet_pairwise_disjoint G u hne)]
          push_cast
          exact hge
      have hEraseCard :
          (((Finset.univ.erase c₀ : Finset (delGraph G u).ConnectedComponent)).card : ℝ) < K := by
        have hone : ∀ c ∈ (Finset.univ.erase c₀ : Finset (delGraph G u).ConnectedComponent),
            (1 : ℝ) ≤ ((compSet G u c).card : ℝ) := by
          intro c _
          have h := (compSet_nonempty G u c).card_pos
          exact_mod_cast h
        have h2 : (((Finset.univ.erase c₀ :
              Finset (delGraph G u).ConnectedComponent)).card : ℝ) ≤
            ∑ c ∈ Finset.univ.erase c₀, ((compSet G u c).card : ℝ) := by
          have hcard := Finset.card_nsmul_le_sum
            (Finset.univ.erase c₀) (fun c => ((compSet G u c).card : ℝ)) 1 hone
          simpa [nsmul_eq_mul] using hcard
        linarith
      have htval : (t : ℝ) =
          (((Finset.univ.erase c₀ : Finset (delGraph G u).ConnectedComponent)).card : ℝ) + 1 := by
        have h := Finset.card_erase_add_one
          (s := (Finset.univ : Finset (delGraph G u).ConnectedComponent)) (a := c₀) (Finset.mem_univ c₀)
        rw [ht, ← Finset.card_univ, ← h]
        push_cast
        ring
      have h1K : 1 + K ≤ (α - ε) * (n : ℝ) := by rw [hK]; nlinarith [hbig]
      have ht_lt : (t : ℝ) < (u.ncard : ℝ) := by
        rw [htval]
        linarith
      have hlt : t < u.ncard := Nat.cast_lt.mp ht_lt
      omega
  · -- (2) every component has fewer than `K` vertices
    push_neg at hbigcomp
    have hsmall : ∀ c : (delGraph G u).ConnectedComponent, ((compSet G u c).card : ℝ) < K :=
      fun c => hbigcomp c
    have htpos : 0 < t := by
      have h : 0 < (delGraph G u).oddComponents.ncard := by omega
      omega
    have ht_le_W : t ≤ n - u.ncard := by
      have hone : ∀ c : (delGraph G u).ConnectedComponent, (1 : ℕ) ≤ (compSet G u c).card := by
        intro c
        have h := (compSet_nonempty G u c).card_pos
        omega
      have h1 : (Finset.univ : Finset (delGraph G u).ConnectedComponent).card ≤
          ∑ c : (delGraph G u).ConnectedComponent, (compSet G u c).card := by
        have hcard := Finset.card_nsmul_le_sum
          (Finset.univ : Finset (delGraph G u).ConnectedComponent)
          (fun c => (compSet G u c).card) 1 (fun c _ => hone c)
        simpa using hcard
      calc t = (Finset.univ : Finset (delGraph G u).ConnectedComponent).card := by
              rw [ht, Finset.card_univ]
        _ ≤ _ := h1
        _ = n - u.ncard := sum_compSet_card G u
    have hsn : (α - ε) * (n : ℝ) < (u.ncard : ℝ) := by
      obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by rw [← ht]; exact htpos :
        0 < Fintype.card (delGraph G u).ConnectedComponent)
      exact lt_ncard_of_small_comp G u hdeg (hsmall c)
    have h3K : 3 * K ≤ (α - ε) * (n : ℝ) := by rw [hK]; nlinarith [hεα, hnR]
    by_cases hWbig : K ≤ ((n - u.ncard : ℕ) : ℝ)
    · -- a union of components of size in `[K, 2K)` has a small complement
      have hWsump : K ≤ ∑ c : (delGraph G u).ConnectedComponent, ((compSet G u c).card : ℝ) := by
        have hcast : ((∑ c : (delGraph G u).ConnectedComponent, (compSet G u c).card : ℕ) : ℝ) =
            ∑ c : (delGraph G u).ConnectedComponent, ((compSet G u c).card : ℝ) := by
          push_cast; rfl
        rw [← hcast, sum_compSet_card G u]
        exact hWbig
      obtain ⟨X, -, hXge, hXlt⟩ :=
        family_window K hKpos (fun c : (delGraph G u).ConnectedComponent => ((compSet G u c).card : ℝ))
          Finset.univ (fun c _ => hsmall c) (by simpa using hWsump)
      set Y : Finset (delGraph G u).ConnectedComponent := Finset.univ \ X with hYdef
      have hYsum : ∑ c ∈ Y, ((compSet G u c).card : ℝ) < K := by
        by_contra hlt
        have hge : K ≤ ∑ c ∈ Y, ((compSet G u c).card : ℝ) := not_lt.mp hlt
        refine false_of_two_large_unions G u hlr hε hεp hn1 (X := X) (Y := Y) ?_ ?_ ?_
        · rw [hYdef]; exact Finset.disjoint_sdiff
        · rw [Finset.card_biUnion (fun a _ b _ hne => compSet_pairwise_disjoint G u hne)]
          push_cast
          exact hXge
        · rw [hYdef, Finset.card_biUnion (fun a _ b _ hne => compSet_pairwise_disjoint G u hne)]
          push_cast
          exact hge
      have hsumUniv : ∑ c ∈ (Finset.univ : Finset (delGraph G u).ConnectedComponent),
          ((compSet G u c).card : ℝ) = ((n - u.ncard : ℕ) : ℝ) := by
        have hcast : ((∑ c : (delGraph G u).ConnectedComponent, (compSet G u c).card : ℕ) : ℝ) =
            ∑ c : (delGraph G u).ConnectedComponent, ((compSet G u c).card : ℝ) := by
          push_cast; rfl
        rw [← hcast, sum_compSet_card G u]
      have hWsum : ((n - u.ncard : ℕ) : ℝ) =
          ∑ c ∈ Y, ((compSet G u c).card : ℝ) + ∑ c ∈ X, ((compSet G u c).card : ℝ) := by
        rw [hYdef, ← hsumUniv, ← Finset.sum_sdiff (s₁ := X)
          (s₂ := (Finset.univ : Finset (delGraph G u).ConnectedComponent))
          (f := fun c => ((compSet G u c).card : ℝ)) (Finset.subset_univ X)]
      have hWlt : ((n - u.ncard : ℕ) : ℝ) < 3 * K := by
        rw [hWsum]; linarith
      have hlt : t < u.ncard := by
        have h1 : (t : ℝ) ≤ ((n - u.ncard : ℕ) : ℝ) := by exact_mod_cast ht_le_W
        have : (t : ℝ) < (u.ncard : ℝ) := by linarith
        exact Nat.cast_lt.mp this
      omega
    · -- `|G - u| < K`
      push_neg at hWbig
      have hlt : t < u.ncard := by
        have h1 : (t : ℝ) ≤ ((n - u.ncard : ℕ) : ℝ) := by exact_mod_cast ht_le_W
        have : (t : ℝ) < (u.ncard : ℝ) := by linarith
        exact Nat.cast_lt.mp this
      omega

/-! ## The main theorem -/

/-- A lower `(p,ε)`-regular graph of even order with minimum degree at least `αn` has a perfect matching (`α ≫ ε > 0`).

Proof sketch via `SimpleGraph.tutte`: let `S ⊆ V` and let `C_1, …` be the components of `G - S`; one shows that the number of odd components of `G - S` is at most `|S|`.  (i) At most one component has `εn` vertices or more, since two such components span no edge, contradicting lower regularity.  (ii) If some component `C` has `|C| < εn`, then any `v ∈ C` has all its neighbours in `C ∪ S`, so `|S| > (α-ε)n`.  (iii) Counting components: if the largest component has `≥ εn` then the union of the others has `< εn` (otherwise (i) with the two unions), so the number `t` of components is at most `⌈εn⌉ ≤ (α-ε)n < |S|`; if all components are smaller than `εn`, either `|G-S| < εn` (then `t ≤ |G-S| < εn ≤ n - εn < |S|`), or the greedy union of components reaching size `εn` has size `< 2εn` and its complement has size `< εn` (again by (i) applied to unions), so `|G-S| < 3εn` and `t ≤ |G-S| < 3εn ≤ n - 3εn < |S|` (as `6ε ≤ 1`). -/
theorem exists_perfectMatching_of_lowerReg {n : ℕ} (G : SimpleGraph (Fin n)) {p ε α : ℝ}
    (hn : Even n) (hlr : Work.Deep.GKO.LowerReg G p ε) (hε : 0 < ε) (hα : 0 < α)
    (hεα : 4 * ε ≤ α) (hε6 : 6 * ε ≤ 1) (hεp : ε < p)
    (hdeg : α * (n : ℝ) ≤ (Work.Deep.GKO.minDeg G : ℝ)) (hbig : 1 ≤ (α - 2 * ε) * (n : ℝ)) :
    ∃ M : SimpleGraph (Fin n), Work.Deep.GKO.IsPerfectMatching' G M := by
  classical
  have hdegv : ∀ v : Fin n, α * (n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
    intro v
    have h2 : minDeg G ≤ Nat.card (G.neighborSet v) :=
      Nat.sInf_le (Set.mem_range_self v)
    have h1 : (minDeg G : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by exact_mod_cast h2
    linarith
  have hperf : ∃ M : G.Subgraph, M.IsPerfectMatching := by
    rw [SimpleGraph.tutte]
    intro u
    rw [SimpleGraph.IsTutteViolator, not_lt]
    exact oddComponents_ncard_le_of_lowerReg hn hlr hε hεp hεα hdegv hbig u
  obtain ⟨M, hM⟩ := hperf
  exact ⟨M.spanningCoe, M.spanningCoe_le,
    fun v => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) v⟩

end

end Work.Deep.GKO
