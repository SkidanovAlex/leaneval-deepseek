import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.deficiencyDefs

/-!
# The deficiency step: realising a degree sequence by matchings

A degree sequence `d : Fin n → ℕ` that satisfies Hakimi's multigraph criterion
(`∑ d` even and `d v ≤ ∑_{u ≠ v} d u` for every `v`) is the sum of the incidence
vectors of at most `2D` matchings, where `D` bounds all degrees.

The proof is by strong induction on `∑ d`, and simultaneously constructs the
matchings and performs the greedy edge colouring of a multigraph with degree
sequence `d`.  At each step of the induction one takes a vertex `u` of maximum
degree and a second vertex `w` of positive degree, and colours the edge `uw` with
a colour which is not yet used at either endpoint; the induction hypothesis
(applied to the degree sequence `decrementTwo d u w`, in which the degrees of `u`
and of `w` are lowered by one) supplies all the other edges.  Because each degree
is at most `D`, at most `2D - 1` colours are ever used, which we absorb into the
fixed palette `Fin (2 * D)` by padding with empty graphs.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.GKO

/-! ## Adding a single edge to a graph -/

/-- The graph obtained from `G` by adding the single edge `uw`.  (The extra disjuncts
carry an `x ≠ y` guard, so the result is loopless even when `u = w`.) -/
private def addEdge {n : ℕ} (G : SimpleGraph (Fin n)) (u w : Fin n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∨ (x ≠ y ∧ x = u ∧ y = w) ∨ (x ≠ y ∧ x = w ∧ y = u)
  symm := Std.Symm.mk (fun x y h => by
    rcases h with h | ⟨hne, h1, h2⟩ | ⟨hne, h1, h2⟩
    · exact Or.inl (G.adj_symm h)
    · exact Or.inr (Or.inr ⟨hne.symm, h2, h1⟩)
    · exact Or.inr (Or.inl ⟨hne.symm, h2, h1⟩))
  loopless := Std.Irrefl.mk (fun x h => by
    rcases h with h | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact G.irrefl h
    · exact hne rfl
    · exact hne rfl)

@[simp] private lemma addEdge_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u w x y : Fin n) :
    (addEdge G u w).Adj x y ↔
      G.Adj x y ∨ (x ≠ y ∧ x = u ∧ y = w) ∨ (x ≠ y ∧ x = w ∧ y = u) := Iff.rfl

/-- The neighbourhood of an isolated vertex `u` in `addEdge G u w` is exactly `{w}`. -/
private lemma addEdge_adj_u {n : ℕ} {G : SimpleGraph (Fin n)} {u w y : Fin n}
    (hu : ∀ x, ¬ G.Adj u x) (hwu : u ≠ w) :
    (addEdge G u w).Adj u y ↔ y = w := by
  rw [addEdge_adj]
  constructor
  · rintro (h | ⟨-, -, h2⟩ | ⟨hne, h1, -⟩)
    · exact absurd h (hu y)
    · exact h2
    · exact absurd h1 hwu
  · intro hy; subst hy; exact Or.inr (Or.inl ⟨hwu, rfl, rfl⟩)

/-- The neighbourhood of an isolated vertex `w` in `addEdge G u w` is exactly `{u}`. -/
private lemma addEdge_adj_w {n : ℕ} {G : SimpleGraph (Fin n)} {u w y : Fin n}
    (hw : ∀ x, ¬ G.Adj w x) (hwu : u ≠ w) :
    (addEdge G u w).Adj w y ↔ y = u := by
  rw [addEdge_adj]
  constructor
  · rintro (h | ⟨-, h1, -⟩ | ⟨-, -, h2⟩)
    · exact absurd h (hw y)
    · exact absurd h1 (Ne.symm hwu)
    · exact h2
  · intro hy; subst hy; exact Or.inr (Or.inr ⟨hwu.symm, rfl, rfl⟩)

/-- Away from the two endpoints, `addEdge G u w` is unchanged. -/
private lemma addEdge_adj_of_ne {n : ℕ} {G : SimpleGraph (Fin n)} {u w v y : Fin n}
    (hvu : v ≠ u) (hvw : v ≠ w) :
    (addEdge G u w).Adj v y ↔ G.Adj v y := by
  rw [addEdge_adj]
  constructor
  · rintro (h | ⟨-, h1, -⟩ | ⟨-, h1, -⟩)
    · exact h
    · exact absurd h1 hvu
    · exact absurd h1 hvw
  · exact Or.inl

/-- The existential form of `addEdge_adj_of_ne`, for rewriting under a binder. -/
private lemma exists_addEdge_iff {n : ℕ} {G : SimpleGraph (Fin n)} {u w v : Fin n}
    (hvu : v ≠ u) (hvw : v ≠ w) :
    (∃ x, (addEdge G u w).Adj v x) ↔ ∃ x, G.Adj v x :=
  exists_congr (fun _ => addEdge_adj_of_ne hvu hvw)

private lemma addEdge_self_left {n : ℕ} {G : SimpleGraph (Fin n)} {u w : Fin n} (huw : u ≠ w) :
    (addEdge G u w).Adj u w := by
  rw [addEdge_adj]
  exact Or.inr (Or.inl ⟨huw, rfl, rfl⟩)

private lemma addEdge_self_right {n : ℕ} {G : SimpleGraph (Fin n)} {u w : Fin n} (huw : u ≠ w) :
    (addEdge G u w).Adj w u := by
  rw [addEdge_adj]
  exact Or.inr (Or.inr ⟨huw.symm, rfl, rfl⟩)

/-- Adding an edge between two vertices that are isolated in a matching gives a matching. -/
private lemma isMatching_addEdge {n : ℕ} {G : SimpleGraph (Fin n)} {u w : Fin n}
    (huw : u ≠ w) (hG : IsMatching' G)
    (hu : ∀ x, ¬ G.Adj u x) (hw : ∀ x, ¬ G.Adj w x) :
    IsMatching' (addEdge G u w) := by
  intro v a b hva hvb
  rcases eq_or_ne v u with rfl | hvu
  · rw [addEdge_adj_u hu huw] at hva hvb; rw [hva, hvb]
  · rcases eq_or_ne v w with rfl | hvw
    · rw [addEdge_adj_w hw huw] at hva hvb; rw [hva, hvb]
    · rw [addEdge_adj_of_ne hvu hvw] at hva hvb
      exact hG v a b hva hvb

/-! ## Two counting lemmas -/

/-- `Nat.card` of a subtype of a finite type is the cardinality of the corresponding
filtered `Finset`. -/
private lemma natCard_filter {k : ℕ} (p : Fin k → Prop) [DecidablePred p] :
    Nat.card {i : Fin k // p i} = (Finset.univ.filter p).card := by
  have H : ∀ i : Fin k, i ∈ Finset.univ.filter p ↔ p i := fun i => by simp
  exact (@Nat.card_eq_fintype_card _ (Fintype.subtype (Finset.univ.filter p) H)).trans
    (Fintype.subtype_card (Finset.univ.filter p) H)

/-- If the two colour sets determined by `p` and by `q` have fewer than `k` elements in
total, then some colour lies in neither of them. -/
private lemma exists_not_and_not {k : ℕ} (p q : Fin k → Prop) [DecidablePred p] [DecidablePred q]
    (h : (Finset.univ.filter p).card + (Finset.univ.filter q).card < k) :
    ∃ i : Fin k, ¬ p i ∧ ¬ q i := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ (Finset.univ.filter p) ∪ (Finset.univ.filter q) := by
    intro i _
    by_cases hp : p i
    · exact Finset.mem_union_left _ (by simp [hp])
    · exact Finset.mem_union_right _ (by simp [hcon i hp])
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter p) (Finset.univ.filter q)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-! ## The Hakimi step -/

/-- Lowering the degrees of `u` and of `w` by one preserves Hakimi's criterion. -/
private theorem hakimi_step' {n : ℕ} (d : Fin n → ℕ) (u w : Fin n) (hwu : w ≠ u)
    (humax : ∀ x : Fin n, d x ≤ d u) (hdu : 0 < d u) (hdw : 0 < d w)
    (heven : Even (∑ x, d x)) (h2 : ∀ v : Fin n, 2 * d v ≤ ∑ x, d x) :
    (∑ x, decrementTwo d u w x) + 2 = ∑ x, d x ∧
    ∀ v : Fin n, 2 * decrementTwo d u w v ≤ ∑ x, decrementTwo d u w x := by
  classical
  have huw : u ≠ w := hwu.symm
  have hpoint : ∀ v : Fin n, decrementTwo d u w v + (if v = u ∨ v = w then 1 else 0) = d v := by
    intro v
    by_cases hv : v = u ∨ v = w
    · rw [if_pos hv]
      rcases hv with h | h
      · rw [h, decrementTwo_eq_left]; omega
      · rw [h, decrementTwo_eq_right]; omega
    · rw [if_neg hv]
      have hvu : v ≠ u := fun h => hv (Or.inl h)
      have hvw : v ≠ w := fun h => hv (Or.inr h)
      rw [decrementTwo_of_ne d hvu hvw]
      simp
  have hsplit : (∑ v, decrementTwo d u w v) + (∑ v : Fin n, (if v = u ∨ v = w then 1 else 0))
      = ∑ v, d v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => hpoint v)
  have htwice : (∑ v : Fin n, (if v = u ∨ v = w then 1 else 0)) = 2 := by
    rw [Finset.sum_boole]
    have hfilter : (Finset.univ.filter (fun v : Fin n => v = u ∨ v = w)) = {u, w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
    rw [hfilter, Finset.card_insert_of_notMem (by simpa using huw), Finset.card_singleton]
    omega
  have hsum' : (∑ x, decrementTwo d u w x) = ∑ x, d x - 2 := by omega
  constructor
  · omega
  · intro v
    by_cases hv : v = u ∨ v = w
    · rw [hsum']
      have h2v := h2 v
      rcases hv with h | h
      · rw [h] at h2v ⊢
        rw [decrementTwo_eq_left]
        omega
      · rw [h] at h2v ⊢
        rw [decrementTwo_eq_right]
        omega
    · have hvu : v ≠ u := fun h => hv (Or.inl h)
      have hvw : v ≠ w := fun h => hv (Or.inr h)
      rw [hsum', decrementTwo_of_ne d hvu hvw]
      have humaxv := humax v
      have hthree : d u + d v + d w ≤ ∑ x, d x := by
        have hle := Finset.sum_le_sum_of_subset (f := d)
          (Finset.subset_univ ({u, v, w} : Finset (Fin n)))
        have hu3 : u ∉ ({v, w} : Finset (Fin n)) := by
          rw [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact hvu h.symm
          · exact huw h
        have hv3 : v ∉ ({w} : Finset (Fin n)) := by
          rw [Finset.mem_singleton]
          exact hvw
        have hsum3 : (∑ x ∈ ({u, v, w} : Finset (Fin n)), d x) = d u + d v + d w := by
          rw [Finset.sum_insert hu3, Finset.sum_insert hv3, Finset.sum_singleton]
          omega
        rwa [hsum3] at hle
      have hstrict : 2 * d v + 1 ≤ ∑ x, d x := by omega
      obtain ⟨t, ht⟩ := heven
      omega

/-! ## The main induction -/

/-- Strong induction on `∑ d`: the degree sequence `d` with `∑ d = 2 * m` is realised by
`2 * D` matchings (padded by empty graphs), each vertex `v` seeing exactly `d v` of them. -/
private theorem main (n D : ℕ) : ∀ m : ℕ, ∀ (d : Fin n → ℕ),
    (∑ v, d v) = 2 * m → (∀ v : Fin n, 2 * d v ≤ ∑ v, d v) → (∀ v : Fin n, d v ≤ D) →
    ∃ M : Fin (2 * D) → SimpleGraph (Fin n),
      (∀ i, IsMatching' (M i)) ∧
      (∀ v : Fin n, Nat.card {i : Fin (2 * D) // ∃ w, (M i).Adj v w} = d v) := by
  intro m
  induction m with
  | zero =>
      intro d hsum h2 hD
      classical
      have hd0 : ∀ v : Fin n, d v = 0 := by
        intro v
        have h : ∀ i ∈ (Finset.univ : Finset (Fin n)), d i = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (d i))).1 (by simpa using hsum)
        exact h v (Finset.mem_univ v)
      refine ⟨fun _ => ⊥, ?_, ?_⟩
      · intro i v a b hva _
        exact absurd hva (by simp)
      · intro v
        rw [hd0 v, natCard_filter]
        simp
  | succ m IH =>
      intro d hsum h2 hD
      classical
      -- some vertex has positive degree
      obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin n, 0 < d v₀ := by
        by_contra hc
        push Not at hc
        have hz : ∑ v, d v = 0 := Finset.sum_eq_zero (fun v _ => le_antisymm (hc v) (Nat.zero_le _))
        rw [hsum] at hz
        omega
      -- a vertex `u` of maximum degree
      obtain ⟨u, humax, hdu⟩ : ∃ u : Fin n, (∀ x : Fin n, d x ≤ d u) ∧ 0 < d u := by
        have hne : (Finset.univ.image d).Nonempty :=
          ⟨d v₀, Finset.mem_image_of_mem d (Finset.mem_univ v₀)⟩
        obtain ⟨u, -, hu⟩ := Finset.mem_image.1 (Finset.max'_mem (Finset.univ.image d) hne)
        refine ⟨u, ?_, ?_⟩
        · intro x
          rw [hu]
          exact Finset.le_max' _ (d x) (Finset.mem_image_of_mem d (Finset.mem_univ x))
        · rw [hu]
          exact lt_of_lt_of_le hv₀
            (Finset.le_max' _ (d v₀) (Finset.mem_image_of_mem d (Finset.mem_univ v₀)))
      -- a second vertex `w ≠ u` of positive degree
      have hsum_erase : ∑ x ∈ Finset.univ.erase u, d x = ∑ x, d x - d u := by
        have hkey : (∑ x, d x) = d u + ∑ x ∈ Finset.univ.erase u, d x := by
          have h := Finset.sum_insert (s := Finset.univ.erase u) (a := u) (f := d)
            (Finset.notMem_erase u Finset.univ)
          rwa [Finset.insert_erase (Finset.mem_univ u)] at h
        omega
      obtain ⟨w, hw_mem, hdw⟩ : ∃ w : Fin n, w ∈ Finset.univ.erase u ∧ 0 < d w := by
        by_contra hc
        push Not at hc
        have hz : ∑ x ∈ Finset.univ.erase u, d x = 0 :=
          Finset.sum_eq_zero (fun x hx => le_antisymm (hc x hx) (Nat.zero_le _))
        have hu2 := h2 u
        omega
      have hwu : w ≠ u := (Finset.mem_erase.1 hw_mem).1
      have huw : u ≠ w := hwu.symm
      -- the induction hypothesis applied to the decremented degree sequence
      have hstep : (∑ x, decrementTwo d u w x) + 2 = ∑ x, d x ∧
          (∀ v : Fin n, 2 * decrementTwo d u w v ≤ ∑ x, decrementTwo d u w x) :=
        hakimi_step' d u w hwu humax hdu hdw ⟨m + 1, by omega⟩ h2
      obtain ⟨hs, h2'⟩ := hstep
      have hsum' : ∑ x, decrementTwo d u w x = 2 * m := by omega
      have hD' : ∀ v : Fin n, decrementTwo d u w v ≤ D :=
        fun v => le_trans (decrementTwo_le d u w v) (hD v)
      obtain ⟨M', hmatch', hcount'⟩ := IH (decrementTwo d u w) hsum' h2' hD'
      -- the colour sets at `u` and at `w`
      have hcu : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj u x)).card =
          decrementTwo d u w u := by
        rw [← natCard_filter]
        exact hcount' u
      have hcw : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj w x)).card =
          decrementTwo d u w w := by
        rw [← natCard_filter]
        exact hcount' w
      have hbnd : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj u x)).card +
          (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj w x)).card < 2 * D := by
        rw [hcu, hcw, decrementTwo_eq_left, decrementTwo_eq_right]
        have hDu := hD u
        have hDw := hD w
        omega
      obtain ⟨i0, hi0u, hi0w⟩ := exists_not_and_not
        (fun i : Fin (2 * D) => ∃ x, (M' i).Adj u x)
        (fun i : Fin (2 * D) => ∃ x, (M' i).Adj w x) hbnd
      -- add the edge `uw` in the free colour `i0`
      set M : Fin (2 * D) → SimpleGraph (Fin n) :=
        fun i => if i = i0 then addEdge (M' i0) u w else M' i with hM
      have hM_apply : ∀ i : Fin (2 * D), M i = if i = i0 then addEdge (M' i0) u w else M' i := by
        intro i; rw [hM]
      have hadj_uw : (M i0).Adj u w := by
        rw [hM_apply i0, if_pos rfl]
        exact addEdge_self_left huw
      have hadj_wu : (M i0).Adj w u := by
        rw [hM_apply i0, if_pos rfl]
        exact addEdge_self_right huw
      refine ⟨M, ?_, ?_⟩
      · intro i
        by_cases hi : i = i0
        · rw [hi]
          rw [hM_apply i0, if_pos rfl]
          exact isMatching_addEdge huw (hmatch' i0) (fun x hx => hi0u ⟨x, hx⟩)
            (fun x hx => hi0w ⟨x, hx⟩)
        · rw [hM_apply i, if_neg hi]
          exact hmatch' i
      · intro v
        rw [natCard_filter]
        by_cases hv : v = u ∨ v = w
        · rcases hv with hvu | hvw
          · -- `v = u`: the colour `i0` is newly used at `u`
            rw [hvu]
            have hni : i0 ∉ Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj u x) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hi0u
            have hfil : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M i).Adj u x)) =
                insert i0 (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj u x)) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              by_cases hi : i = i0
              · rw [hi]
                exact ⟨fun _ => Or.inl rfl, fun _ => ⟨w, hadj_uw⟩⟩
              · rw [hM_apply i, if_neg hi]
                simp only [hi, false_or]
            rw [hfil, Finset.card_insert_of_notMem hni, hcu, decrementTwo_eq_left]
            omega
          · -- `v = w`: the colour `i0` is newly used at `w`
            rw [hvw]
            have hni : i0 ∉ Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj w x) := by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hi0w
            have hfil : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M i).Adj w x)) =
                insert i0 (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj w x)) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              by_cases hi : i = i0
              · rw [hi]
                exact ⟨fun _ => Or.inl rfl, fun _ => ⟨u, hadj_wu⟩⟩
              · rw [hM_apply i, if_neg hi]
                simp only [hi, false_or]
            rw [hfil, Finset.card_insert_of_notMem hni, hcw, decrementTwo_eq_right]
            omega
        · -- `v ∉ {u, w}`: nothing changes at `v`
          have hvu : v ≠ u := fun h => hv (Or.inl h)
          have hvw : v ≠ w := fun h => hv (Or.inr h)
          have hfil : (Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M i).Adj v x)) =
              Finset.univ.filter (fun i : Fin (2 * D) => ∃ x, (M' i).Adj v x) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hi : i = i0
            · rw [hi]
              rw [hM_apply i0, if_pos rfl, exists_addEdge_iff hvu hvw]
            · simp only [hM_apply i, if_neg hi]
          rw [hfil, ← natCard_filter, hcount' v]
          exact decrementTwo_of_ne d hvu hvw

/-- Every degree sequence that can be realized by a multigraph (i.e. `Σ d` even and `∀ v, d v ≤ Σ_{u ≠ v} d u`, Hakimi's criterion) is the sum of the incidence vectors of at most `2D` matchings, where `D` bounds the degrees.

This is the "deficiency" step of the reduction: the matchings `M i` are the leaves of the spanning linear forests removed to make the graph regular.  Proof sketch: Hakimi's criterion gives a multigraph `A` on `Fin n` with degree sequence `d` (pair up the `Σ d` tokens greedily, always pairing two vertices of currently largest remaining degree, so that no token is paired with one of its own vertex); then colour the edges of `A` greedily with at most `2D - 1` colours (each edge conflicts with at most `2D - 2` colours at its two ends), and let `M i` be the subgraph of edges of colour `i`.  Each colour class is a matching, and at a vertex `v` the colours appearing are exactly the colours of the `d v` edges at `v`, so `{i // ∃ w, (M i).Adj v w}` has `d v` elements. -/
theorem exists_deficiencyMatchings {n : ℕ} (d : Fin n → ℕ) {D : ℕ}
    (heven : Even (∑ v, d v)) (hmax : ∀ v : Fin n, d v ≤ ∑ u ∈ Finset.univ.erase v, d u)
    (hD : ∀ v : Fin n, d v ≤ D) :
    ∃ (k : ℕ) (M : Fin k → SimpleGraph (Fin n)), k ≤ 2 * D ∧
      (∀ i, Work.Deep.GKO.IsMatching' (M i)) ∧
      (∀ v : Fin n, Nat.card {i : Fin k // ∃ w, (M i).Adj v w} = d v) := by
  classical
  have h2 : ∀ v : Fin n, 2 * d v ≤ ∑ u, d u := by
    intro v
    have hkey : (∑ u, d u) = d v + ∑ u ∈ Finset.univ.erase v, d u := by
      have h := Finset.sum_insert (s := Finset.univ.erase v) (a := v) (f := d)
        (Finset.notMem_erase v Finset.univ)
      rwa [Finset.insert_erase (Finset.mem_univ v)] at h
    have := hmax v
    omega
  obtain ⟨t, ht⟩ := heven
  obtain ⟨M, hmatch, hcount⟩ := main n D t d (by omega) h2 hD
  exact ⟨2 * D, M, le_refl _, hmatch, hcount⟩

end Work.Deep.GKO
