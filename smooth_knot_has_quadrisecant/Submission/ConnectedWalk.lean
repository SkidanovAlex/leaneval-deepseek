import Mathlib

open Set List
open scoped Topology

set_option linter.unnecessarySimpa false

noncomputable section

/-!
# Generic topology for the component-exhaustion ordering: overlap-walks of a
countable connected open cover

Pure point-set topology.  Let `X` be a preconnected space with a countable
open cover `U : ℕ → Set X` by nonempty open sets.  Then:

1. **the overlap graph is connected** (`graph_connected`): any two indices
   are joined by a chain of indices whose consecutive sets overlap
   (membership is `Adj U a b := (U a ∩ U b).Nonempty`, chained as
   `Relation.ReflTransGen`);
2. finite chains are extracted as concrete lists (`Walk`, `walkOf`);
3. **`exists_overlap_walk`**: there is an infinite walk `e : ℕ → ℕ`
   visiting every index, starting at `0`, with consecutive overlap
   `(U (e n) ∩ U (e (n+1))).Nonempty`;
4. **`exists_pathConnected_open_exhaustion`** (combined form): if each
   `U n` is path-connected, an overlap walk `e` together with the partial
   unions `V n = ⋃_{m < n+1} U (e m)` — open, path-connected, increasing,
   exhausting `X` (tied to `e` by the defining equality) — the
   interval-chain-exhaustion input over a connected component of the
   trisecant set (whose chart traces are path-connected, homeomorphic to
   open intervals).

Everything is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

namespace ConnectedWalk

variable {X : Type*} [TopologicalSpace X]

/-- adjacency of two covering sets: they overlap -/
def Adj (U : ℕ → Set X) (a b : ℕ) : Prop := (U a ∩ U b).Nonempty

/-- In a preconnected space the overlap graph of a countable open cover by
nonempty sets is connected. -/
lemma graph_connected [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n) :
    ∀ a b : ℕ, Relation.ReflTransGen (Adj U) a b := by
  have hpre : IsPreconnected (univ : Set X) := isPreconnected_univ
  intro a b
  by_contra hb
  let P : ℕ → Prop := fun n => Relation.ReflTransGen (Adj U) a n
  have haP : P a := by
    dsimp [P]
    exact Relation.ReflTransGen.refl
  let u : Set X := {x : X | ∃ m : {m : ℕ // P m}, x ∈ U (m : ℕ)}
  have hu_open : IsOpen u := by
    rw [show u = ⋃ m : {m : ℕ // P m}, U (m : ℕ) by
      ext x
      simp [u]]
    exact isOpen_iUnion (fun m : {m : ℕ // P m} => hU (m : ℕ))
  let v : Set X := {x : X | ∃ n : {n : ℕ // ¬ P n}, x ∈ U (n : ℕ)}
  have hv_open : IsOpen v := by
    rw [show v = ⋃ n : {n : ℕ // ¬ P n}, U (n : ℕ) by
      ext x
      simp [v]]
    exact isOpen_iUnion (fun n : {n : ℕ // ¬ P n} => hU (n : ℕ))
  have hcov : (Set.univ : Set X) ⊆ u ∪ v := by
    intro x hx
    rcases hcover x with ⟨n, hxn⟩
    by_cases hn : P n
    · exact Or.inl ⟨⟨n, hn⟩, hxn⟩
    · exact Or.inr ⟨⟨n, hn⟩, hxn⟩
  have hu_ne : (univ ∩ u).Nonempty := by
    rcases hUn a with ⟨xa, hxa⟩
    refine ⟨xa, ⟨trivial, ⟨⟨a, haP⟩, hxa⟩⟩⟩
  have hv_ne : (univ ∩ v).Nonempty := by
    have hbP : ¬ P b := by
      intro hbin
      exact hb hbin
    rcases hUn b with ⟨xb, hxb⟩
    refine ⟨xb, ⟨trivial, ⟨⟨b, hbP⟩, hxb⟩⟩⟩
  have hsep : (univ ∩ (u ∩ v)).Nonempty :=
    hpre u v hu_open hv_open hcov hu_ne hv_ne
  rcases hsep with ⟨x, hxmem⟩
  rcases hxmem.2.1 with ⟨m, hxm⟩
  rcases hxmem.2.2 with ⟨n, hxn⟩
  have hadj : Adj U (m : ℕ) (n : ℕ) := ⟨x, hxm, hxn⟩
  have hR : Relation.ReflTransGen (Adj U) a (n : ℕ) :=
    Relation.ReflTransGen.trans (m : {m : ℕ // P m}).2
      (Relation.ReflTransGen.single hadj)
  exact (n : {n : ℕ // ¬ P n}).2 hR

/-- A finite walk from `a` to `b`: a nonempty list whose head is `a`, last
is `b`, consecutive elements related by `R`. -/
structure Walk (R : ℕ → ℕ → Prop) (a b : ℕ) where
  l : List ℕ
  ne : l ≠ []
  chain : l.IsChain R
  head : l.head ne = a
  last : l.getLast ne = b

namespace Walk

/-- The last element of a list does not depend on the nonemptiness proof. -/
private lemma getLast_irrel {l : List ℕ} {h₁ h₂ : l ≠ []} :
    l.getLast h₁ = l.getLast h₂ := by
  congr 1

/-- Append a final step `b —R→ c` at the end of a walk. -/
def append_last {R : ℕ → ℕ → Prop} {a b c : ℕ} (w : Walk R a b) (hbc : R b c) :
    Walk R a c := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  refine ⟨l ++ [c], ?_, ?_, ?_, ?_⟩
  · have hlen : 0 < (l ++ [c]).length := by
      rw [length_append]
      have h0 : 0 < l.length := List.length_pos_of_ne_nil lne
      omega
    exact List.ne_nil_of_length_pos hlen
  · rw [isChain_append]
    constructor
    · exact lchain
    constructor
    · exact List.isChain_singleton c
    · intro x hx y hy
      obtain ⟨hnx, hxeq⟩ := mem_getLast?_eq_getLast hx
      rw [hxeq]
      rw [llast]
      have hyc : c = y := by simpa using hy
      rw [← hyc]
      exact hbc
  · cases l with
    | nil => exfalso; exact lne rfl
    | cons x xs => simpa [lhead]
  · simpa [getLast_irrel] using (getLast_append_singleton l (a := c))

/-- The tail of a nontrivial walk list is nonempty. -/
lemma tail_ne {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b) (hab : a ≠ b) :
    w.l.tail ≠ [] := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  intro ht
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      have hxs : xs = [] := by
        simpa using ht
      subst xs
      have hx : x = a := by simpa using lhead
      have hb : x = b := by simpa using llast
      exact hab (hx.symm.trans hb)

/-- The tail of a walk list ends at the target. -/
lemma tail_last {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b)
    (ht : w.l.tail ≠ []) : w.l.tail.getLast ht = b := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      -- l = x :: xs, w.l.tail = xs
      cases xs with
      | nil => exact (ht rfl).elim
      | cons y ys =>
          -- target: (y :: ys).getLast ht = b; llast: (x :: y :: ys).getLast lne = b
          simpa using llast

/-- The first element of the tail is related to the head. -/
lemma rel_head_tail {R : ℕ → ℕ → Prop} {a b : ℕ} (w : Walk R a b)
    (ht : w.l.tail ≠ []) : R a (w.l.tail.head ht) := by
  rcases w with ⟨l, lne, lchain, lhead, llast⟩
  cases l with
  | nil => exact (lne rfl).elim
  | cons x xs =>
      have hxs : xs ≠ [] := by simpa using ht
      have hc := (isChain_cons.mp lchain).1
      have hmem : xs.head hxs ∈ xs.head? := by
        cases xs with
        | nil => exact (hxs rfl).elim
        | cons y ys => simp
      have hR : R x (xs.head hxs) := hc (xs.head hxs) hmem
      have hx : x = a := by simpa using lhead
      simpa [hx] using hR

end Walk

/-- Equal nonempty lists have equal last elements. -/
private lemma getLast_congr {l l' : List ℕ} (h : l = l') {h₁ : l ≠ []} {h₂ : l' ≠ []} :
    l.getLast h₁ = l'.getLast h₂ := by
  subst l'
  congr 1
/-- An element of the `head?` of a nonempty list equals its head. -/
private lemma head_mem_head_eq {l : List ℕ} (hl : l ≠ []) {y : ℕ} (hy : y ∈ l.head?) :
    y = l.head hl := by
  have h := head_of_mem_head? hy
  rw [← h]


/-- An RTC proof yields a finite walk (existence). -/
lemma exists_walk_of_rtc {R : ℕ → ℕ → Prop} {a b : ℕ}
    (h : Relation.ReflTransGen R a b) : Nonempty (Walk R a b) := by
  induction h with
  | refl =>
      refine ⟨{ l := [a], ne := by simp, chain := by simp, head := rfl, last := rfl }⟩
  | tail hstep hrest ih =>
      rcases ih with ⟨w⟩
      exact ⟨w.append_last hrest⟩

/-- The concrete walk extracted from an RTC proof (choice). -/
noncomputable def walkOf {R : ℕ → ℕ → Prop} {a b : ℕ}
    (h : Relation.ReflTransGen R a b) : Walk R a b :=
  Classical.choice (exists_walk_of_rtc h)

/-- The state of the round construction: the walk list built so far and
the current vertex. -/
structure RoundData where
  list : List ℕ
  cur : ℕ

/-- One round: walk from `r` to `r+1` along the (choice) finite walk of the
connected graph, appending all new vertices of that walk to the list. -/
noncomputable def nextRound (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (s : RoundData) (r : ℕ) :
    RoundData :=
  ⟨s.list ++ (walkOf (allR r (r + 1))).l.tail, r + 1⟩

/-- The rounds: `rounds r` is the walk list that has visited every vertex
`≤ r` (and possibly more), ending at the vertex `r`. -/
noncomputable def rounds (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) : ℕ → RoundData
  | 0 => ⟨[0], 0⟩
  | r + 1 => nextRound R allR (rounds R allR r) r

/-- After round `r` the current vertex is `r`. -/
lemma rounds_cur (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).cur = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [rounds, nextRound]

/-- The joint invariants of the rounds: nonempty list, chain of consecutive
overlaps, ending at `r`, containing every vertex `≤ r`. -/
private lemma rounds_ind (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    ∃ ne : (rounds R allR r).list ≠ [],
      (rounds R allR r).cur = r ∧ (rounds R allR r).list.IsChain R ∧
      (rounds R allR r).list.getLast ne = r ∧
      ∀ k : ℕ, k ≤ r → k ∈ (rounds R allR r).list := by
  induction r with
  | zero =>
      refine ⟨by simp [rounds], ?_, ?_, ?_, ?_⟩
      · rfl
      · exact List.isChain_singleton 0
      · simp [rounds]
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp [rounds]
  | succ r ih =>
      rcases ih with ⟨ne, hcur, hchain, hlast, hmem⟩
      let s : RoundData := rounds R allR r
      let w : Walk R r (r + 1) := walkOf (allR r (r + 1))
      have hne_w : r ≠ r + 1 := by omega
      have htail : w.l.tail ≠ [] := w.tail_ne hne_w
      have hnewlist : (rounds R allR (r + 1)).list = s.list ++ w.l.tail := by
        rfl
      -- nonempty
      have hne' : (rounds R allR (r + 1)).list ≠ [] := by
        rw [hnewlist]
        apply List.ne_nil_of_length_pos
        rw [length_append]
        have h0 : 0 < s.list.length := List.length_pos_of_ne_nil ne
        have h0' : 0 ≤ w.l.tail.length := Nat.zero_le _
        omega
      refine ⟨hne', ?_, ?_, ?_, ?_⟩
      · simp [rounds, nextRound]
      · -- IsChain of s.list ++ w.l.tail
        rw [hnewlist]
        have htailchain : w.l.tail.IsChain R := w.chain.tail
        apply IsChain.append hchain htailchain
        intro x hx y hy
        obtain ⟨hnx, hxeq⟩ := mem_getLast?_eq_getLast hx
        rw [hxeq]
        -- x = getLast s.list ne = r
        have hxr : s.list.getLast ne = r := by
          simpa [s, hcur] using hlast
        rw [hxr]
        -- y is the head of the tail, related to r
        have hyh : y = w.l.tail.head htail := head_mem_head_eq htail hy
        rw [hyh]
        exact w.rel_head_tail htail
      · -- last = r+1
        have hne_app : (s.list ++ w.l.tail) ≠ [] :=
          append_ne_nil_of_right_ne_nil s.list htail
        have hmain : (s.list ++ w.l.tail).getLast hne_app = r + 1 := by
          rw [getLast_append_of_right_ne_nil s.list w.l.tail htail]
          exact w.tail_last htail
        exact (getLast_congr hnewlist (h₁ := hne') (h₂ := hne_app)).trans hmain
      · intro k hk
        rw [hnewlist]
        rw [List.mem_append]
        by_cases hkr : k ≤ r
        · exact Or.inl (hmem k hkr)
        · have hk1 : k = r + 1 := by omega
          subst k
          apply Or.inr
          -- r+1 is the last element of the tail, hence in the tail
          have hlastmem : w.l.tail.getLast htail ∈ w.l.tail := List.getLast_mem htail
          rw [w.tail_last htail] at hlastmem
          exact hlastmem

/-- The rounds list is nonempty. -/
lemma rounds_ne (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list ≠ [] :=
  (rounds_ind R allR r).1

/-- The rounds list is a chain (consecutive vertices overlap-related). -/
lemma rounds_chain (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list.IsChain R :=
  (rounds_ind R allR r).2.2.1

/-- The rounds list ends at the current vertex `r`. -/
lemma rounds_last (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR r).list.getLast (rounds_ne R allR r) = r :=
  (rounds_ind R allR r).2.2.2.1

/-- The rounds list contains every vertex `≤ r`. -/
lemma rounds_mem (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) {k : ℕ} (hk : k ≤ r) :
    k ∈ (rounds R allR r).list :=
  (rounds_ind R allR r).2.2.2.2 k hk

/-- The list after round `r + 1` extends the list after round `r` by the
(possibly trivial) tail of the walk from `r` to `r+1`. -/
lemma rounds_succ_list (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    (rounds R allR (r + 1)).list =
      (rounds R allR r).list ++ (walkOf (allR r (r + 1))).l.tail := by
  rfl

/-- The length of the rounds list is at least `r + 1`. -/
lemma rounds_length_ge (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (r : ℕ) :
    r + 1 ≤ (rounds R allR r).list.length := by
  induction r with
  | zero => simp [rounds]
  | succ r ih =>
      rw [rounds_succ_list]
      rw [length_append]
      have htail : (walkOf (allR r (r + 1))).l.tail ≠ [] :=
        (walkOf (allR r (r + 1))).tail_ne (by omega)
      have h1 : 1 ≤ (walkOf (allR r (r + 1))).l.tail.length :=
        Nat.succ_le_of_lt (List.length_pos_of_ne_nil htail)
      omega



/-- Getting an element of an append inside the left list is the same as
getting it from the left list. -/
private lemma get_append_left (l₁ t : List ℕ) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ t).get ⟨i, by rw [length_append]; omega⟩ = l₁.get ⟨i, hi⟩ := by
  have hpre : l₁ <+: l₁ ++ t := ⟨t, rfl⟩
  simpa using (IsPrefix.getElem hpre hi).symm

/-- Equal lists have equal get-elements at the same index. -/
private lemma get_eq_of_list_eq {l₁ l₂ : List ℕ} (h : l₁ = l₂) (i : ℕ)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁.get ⟨i, h₁⟩ = l₂.get ⟨i, h₂⟩ := by
  subst l₂
  congr 1

/-- The rounds list of round `n` extends the rounds list of round `k` by a
suffix (for `k ≤ n`). -/
private lemma rounds_prefix_tail (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n : ℕ} (h : k ≤ n) :
    ∃ t : List ℕ, (rounds R allR n).list = (rounds R allR k).list ++ t := by
  induction n with
  | zero =>
      refine ⟨[], ?_⟩
      have : k = 0 := by omega
      subst k
      simp [rounds]
  | succ n ih =>
      by_cases hkn : k ≤ n
      · rcases ih hkn with ⟨t, ht⟩
        refine ⟨t ++ (walkOf (allR n (n + 1))).l.tail, ?_⟩
        rw [rounds_succ_list]
        rw [ht]
        simp [List.append_assoc]
      · have hk : k = n + 1 := by omega
        subst k
        refine ⟨[], ?_⟩
        simp [rounds_succ_list]

/-- The walk: `walkPos n` is the vertex visited at time `n` — the element
at position `n` of the `n`-th round list. -/
noncomputable def walkPos (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (n : ℕ) : ℕ :=
  (rounds R allR n).list.get ⟨n,
    Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩

/-- The rounds list of `k` is a prefix of the rounds list of any later
round. -/
private lemma rounds_prefix (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n : ℕ} (h : k ≤ n) :
    (rounds R allR k).list <+: (rounds R allR n).list := by
  rcases rounds_prefix_tail R allR h with ⟨t, ht⟩
  exact ⟨t, ht.symm⟩

/-- Elements of a round list stay fixed in all later rounds. -/
private lemma rounds_fix (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) {k n i : ℕ} (h : k ≤ n)
    (hi : i < (rounds R allR k).list.length)
    (hi2 : i < (rounds R allR n).list.length) :
    (rounds R allR k).list.get ⟨i, hi⟩ = (rounds R allR n).list.get ⟨i, hi2⟩ := by
  rcases rounds_prefix_tail R allR h with ⟨t, ht⟩
  -- ht : (rounds n).list = (rounds k).list ++ t ; first step: left get = append get
  have h1 : (rounds R allR k).list.get ⟨i, hi⟩ =
      ((rounds R allR k).list ++ t).get ⟨i, by rw [length_append]; omega⟩ := by
    have hg := get_append_left (rounds R allR k).list t i hi
    -- hg : append.get⟨i, by omega⟩ = left.get⟨i,hi⟩
    exact hg.symm
  have h2 : ((rounds R allR k).list ++ t).get ⟨i,
      by rw [length_append]; omega⟩ = (rounds R allR n).list.get ⟨i, hi2⟩ :=
    get_eq_of_list_eq ht.symm i (by rw [length_append]; omega) hi2
  exact h1.trans h2

/-- Consecutive walk positions are related: `walkPos` is an overlap walk. -/
lemma walkPos_adjacent (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) (n : ℕ) :
    R (walkPos R allR n) (walkPos R allR (n + 1)) := by
  have hn1 : n < (rounds R allR (n + 1)).list.length := by
    have h := rounds_length_ge R allR (n + 1)
    omega
  have hn2 : n + 1 < (rounds R allR (n + 1)).list.length :=
    Nat.lt_of_succ_le (rounds_length_ge R allR (n + 1))
  have hchain : R ((rounds R allR (n + 1)).list.get ⟨n, hn1⟩)
      ((rounds R allR (n + 1)).list.get ⟨n + 1, hn2⟩) := by
    exact (rounds_chain R allR (n + 1)).getElem n hn2
  have hfix : (rounds R allR n).list.get
      ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩ =
      (rounds R allR (n + 1)).list.get ⟨n, hn1⟩ := by
    exact rounds_fix R allR (k := n) (n := n + 1) (by omega)
      (Nat.lt_of_succ_le (rounds_length_ge R allR n)) hn1
  dsimp [walkPos]
  change R ((rounds R allR n).list.get
      ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩)
    ((rounds R allR (n + 1)).list.get
      ⟨n + 1, Nat.lt_of_succ_le (rounds_length_ge R allR (n + 1))⟩)
  rw [hfix]
  exact hchain

/-- The walk visits every vertex. -/
lemma walkPos_surjective (R : ℕ → ℕ → Prop)
    (allR : ∀ a b : ℕ, Relation.ReflTransGen R a b) :
    Function.Surjective (walkPos R allR) := by
  intro k
  have hk : k ∈ (rounds R allR k).list := rounds_mem R allR k (le_rfl)
  rcases List.mem_iff_get.mp hk with ⟨i, hi⟩
  let n : ℕ := i.1
  have hn_lt : n < (rounds R allR n).list.length :=
    Nat.lt_of_succ_le (rounds_length_ge R allR n)
  refine ⟨n, ?_⟩
  dsimp [walkPos]
  by_cases hkn : k ≤ n
  · have hfix := rounds_fix R allR (k := k) (n := n) hkn i.2 hn_lt
    calc
      (rounds R allR n).list.get ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩
          = (rounds R allR k).list.get ⟨n, i.2⟩ := hfix.symm
      _ = k := hi
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    have hfix := rounds_fix R allR (k := n) (n := k) (le_of_lt hnk) hn_lt i.2
    calc
      (rounds R allR n).list.get ⟨n, Nat.lt_of_succ_le (rounds_length_ge R allR n)⟩
          = (rounds R allR k).list.get ⟨n, i.2⟩ := hfix
      _ = k := hi


/-- **Overlap-walk of a countable connected open cover.**  A preconnected
space with a countable open cover by nonempty open sets admits an infinite
walk `e` visiting every index (starting at `0`) whose consecutive sets
overlap.  This is the enumeration input of the ordering construction
(interval-chain exhaustion) of the component classification. -/
theorem exists_overlap_walk [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n) :
    ∃ e : ℕ → ℕ, e 0 = 0 ∧ (∀ n, (U (e n) ∩ U (e (n + 1))).Nonempty) ∧
      Function.Surjective e := by
  classical
  let allR : ∀ a b : ℕ, Relation.ReflTransGen (Adj U) a b :=
    graph_connected U hU hUn hcover
  refine ⟨walkPos (Adj U) allR, ?_, ?_, ?_⟩
  · dsimp [walkPos]
    simp [rounds]
  · intro n
    exact walkPos_adjacent (Adj U) allR n
  · exact walkPos_surjective (Adj U) allR


/-- Membership in an `Iio`-indexed biUnion. -/
private lemma mem_biUnion_Iio {X : Type*} {U : ℕ → Set X} {x : X} {n : ℕ} :
    (x ∈ ⋃ m ∈ Set.Iio n, U m) ↔ ∃ m, m < n ∧ x ∈ U m := by
  simp

/-- **Path-connected exhaustion from the walk (combined form).**  If the
sets of the cover are path-connected, there is an overlap walk `e`
(consecutive overlaps, surjective, `e 0 = 0`) such that the partial
unions `V n = ⋃_{m < n+1} U (e m)` are an increasing exhaustion of `X` by
open path-connected sets.  This is the interval-chain-exhaustion input
over a connected component of the trisecant set (whose chart traces are
path-connected, homeomorphic to open intervals): the walk and the
exhaustion unions are returned together, tied by the defining equality
`V n = ⋃ m ∈ Iio (n+1), U (e m)`. -/
theorem exists_pathConnected_open_exhaustion [PreconnectedSpace X] (U : ℕ → Set X)
    (hU : ∀ n, IsOpen (U n)) (hUn : ∀ n, (U n).Nonempty)
    (hcover : ∀ x : X, ∃ n, x ∈ U n)
    (hpc : ∀ n, IsPathConnected (U n)) :
    ∃ (e : ℕ → ℕ) (V : ℕ → Set X),
      e 0 = 0 ∧ Function.Surjective e ∧
      (∀ n, (U (e n) ∩ U (e (n + 1))).Nonempty) ∧
      (∀ n, IsOpen (V n)) ∧ (∀ n, IsPathConnected (V n)) ∧
      (∀ n, V n ⊆ V (n + 1)) ∧ (∀ x : X, ∃ n, x ∈ V n) ∧
      (∀ n, V n = ⋃ m ∈ Set.Iio (n + 1), U (e m)) := by
  classical
  rcases exists_overlap_walk U hU hUn hcover with ⟨e, e0, hadj, esurj⟩
  let V : ℕ → Set X := fun n => ⋃ m ∈ Set.Iio (n + 1), U (e m)
  have hVstep : ∀ n, V (n + 1) = V n ∪ U (e (n + 1)) := by
    intro n
    ext x
    change (x ∈ ⋃ m ∈ Set.Iio (n + 2), U (e m) ↔
      x ∈ (⋃ m ∈ Set.Iio (n + 1), U (e m)) ∪ U (e (n + 1)))
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    rw [Set.mem_union]
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    constructor
    · rintro ⟨m, hm, hx⟩
      have hmle : m ≤ n + 1 := by omega
      rcases Nat.lt_or_eq_of_le hmle with hmlt | hmeq
      · exact Or.inl ⟨m, hmlt, hx⟩
      · subst m
        exact Or.inr hx
    · rintro (⟨m, hm, hx⟩ | hx)
      · exact ⟨m, by omega, hx⟩
      · exact ⟨n + 1, by omega, hx⟩
  refine ⟨e, V, e0, esurj, hadj, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [V]
    exact isOpen_biUnion (fun m hm => hU (e m))
  · intro n
    induction n with
    | zero =>
        have hV0 : V 0 = U (e 0) := by
          ext x
          dsimp [V]
          rw [mem_biUnion_Iio (U := fun m => U (e m))]
          simp
        rw [hV0]
        exact hpc (e 0)
    | succ n ih =>
        rw [hVstep n]
        apply IsPathConnected.union ih (hpc (e (n + 1)))
        rcases hadj n with ⟨x, hxmem⟩
        refine ⟨x, ?_, hxmem.2⟩
        dsimp [V]
        rw [mem_biUnion_Iio (U := fun m => U (e m))]
        exact ⟨n, by omega, hxmem.1⟩
  · intro n x hx
    rw [hVstep n]
    exact Or.inl hx
  · intro x
    rcases hcover x with ⟨m, hxm⟩
    rcases esurj m with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    dsimp [V]
    rw [mem_biUnion_Iio (U := fun m => U (e m))]
    refine ⟨p, by omega, ?_⟩
    rw [hp]
    exact hxm
  · intro n
    rfl

end ConnectedWalk
end LeanEval.KnotTheory.Quadrisecant
