import Submission.EFL.Reservoir
import Submission.EFL.StabilityLoop
import Submission.EFL.ColourClassSplitting
import Submission.EFL.ColourClassSplitting

set_option autoImplicit false
open scoped BigOperators
namespace ErdosFaberLovaszConjecture
noncomputable section
variable {n : ℕ}

/-! ## Two-element edges as graphs -/

/-- The "other vertex" of `e` at `v`: the unique element of `e` different from
`v` when it exists, and `v` otherwise. -/
def otherVertex (e : Set (Fin n)) (v : Fin n) : Fin n := by
  classical
  exact if h : ∃ w, w ∈ e ∧ w ≠ v then Classical.choose h else v

theorem otherVertex_mem {e : Set (Fin n)} {v : Fin n} (h : ∃ w, w ∈ e ∧ w ≠ v) :
    otherVertex e v ∈ e := by
  rw [otherVertex, dif_pos h]
  exact (Classical.choose_spec h).1

theorem otherVertex_ne {e : Set (Fin n)} {v : Fin n} (h : ∃ w, w ∈ e ∧ w ≠ v) :
    otherVertex e v ≠ v := by
  rw [otherVertex, dif_pos h]
  exact (Classical.choose_spec h).2

/-- The other vertex of a 2-edge containing `v` is the unique element of `e`
different from `v`. -/
theorem otherVertex_unique {e : Set (Fin n)} {v w : Fin n} (h2 : edgeSize e = 2)
    (hv : v ∈ e) (hw : w ∈ e) (hne : w ≠ v) : w = otherVertex e v := by
  have hex : ∃ x, x ∈ e ∧ x ≠ v := ⟨w, hw, hne⟩
  have h1 : otherVertex e v ∈ e \ {v} :=
    ⟨otherVertex_mem hex, by simp [otherVertex_ne hex]⟩
  have h2' : w ∈ e \ {v} := ⟨hw, by simp [hne]⟩
  have h2n : e.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact h2
  have hcard : (e \ {v}).ncard = 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hv, h2n]
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard
  rw [hx] at h1 h2'
  simp only [Set.mem_singleton_iff] at h1 h2'
  exact h2'.trans h1.symm

/-- A 2-edge containing `v` is `{v, otherVertex e v}`. -/
theorem eq_pair_otherVertex {e : Set (Fin n)} {v : Fin n} (h2 : edgeSize e = 2)
    (hv : v ∈ e) : e = {v, otherVertex e v} := by
  have hex : ∃ x, x ∈ e ∧ x ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hsub : e ⊆ {v} := fun x hx => by simpa using hcon x hx
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h4 : ({v} : Set (Fin n)).ncard = 1 := Set.ncard_singleton v
    rw [h4] at h3
    have h2n : e.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact h2
    omega
  have h2n : e.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact h2
  have h2n : e.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact h2
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    · have := otherVertex_unique h2 hv hx hxv
      simp [this]
  · rw [Set.ncard_pair (Ne.symm (otherVertex_ne hex))]
    omega

/-- The other vertex of the pair `{v,w}` at `v`. -/
theorem otherVertex_pair {v w : Fin n} (h : w ≠ v) :
    otherVertex ({v, w} : Set (Fin n)) v = w := by
  refine (otherVertex_unique ?_ ?_ ?_ h).symm
  · rw [edgeSize_eq_ncard]; exact Set.ncard_pair h.symm
  · simp
  · simp

/-! ## Counting through a vertex -/

/-- In a family of 2-element edges, the number of edges through `v` equals the
number of neighbours of `v`. -/
theorem ncard_nbrs_eq_hypergraphDegree {G : Hypergraph (Fin n)}
    (h2 : ∀ e ∈ G, edgeSize e = 2) (v : Fin n) :
    (nbrs G v).ncard = hypergraphDegree G v := by
  classical
  have hne : ∀ w : Fin n, w ∈ nbrs G v → w ≠ v := by
    intro w hw hwv
    have hsz : edgeSize ({v, w} : Set (Fin n)) = 2 := h2 _ hw
    rw [hwv] at hsz
    have hp : ({v, v} : Set (Fin n)) = ({v} : Set (Fin n)) := by ext x; simp
    rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at hsz
    omega
  have huniv : (Set.univ : Set {e : G // v ∈ (e : Set (Fin n))}).ncard =
      hypergraphDegree G v := by
    rw [hypergraphDegree, Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [← huniv]
  refine Set.ncard_congr
    (fun w hw => (⟨⟨{v, w}, hw⟩, by simp⟩ : {e : G // v ∈ (e : Set (Fin n))})) ?_ ?_ ?_
  · intro w hw; exact Set.mem_univ _
  · intro w w' hw hw' heq
    have h1 : ({v, w} : Set (Fin n)) = {v, w'} :=
      congrArg (fun x : {e : G // v ∈ (e : Set (Fin n))} => (x.1 : Set (Fin n))) heq
    have h2' : w ∈ ({v, w'} : Set (Fin n)) := by rw [← h1]; simp
    rcases h2' with h | h
    · exact absurd h (hne w hw)
    · exact h
  · intro b _
    have hb2 : edgeSize (b.1 : Set (Fin n)) = 2 := h2 _ b.1.2
    have hpair := eq_pair_otherVertex (e := (b.1 : Set (Fin n))) (v := v) hb2 b.2
    have hset : ({v, otherVertex (b.1 : Set (Fin n)) v} : Set (Fin n)) = (b.1 : Set (Fin n)) :=
      hpair.symm
    refine ⟨otherVertex (b.1 : Set (Fin n)) v, ?_, ?_⟩
    · change ({v, otherVertex (b.1 : Set (Fin n)) v} : Set (Fin n)) ∈ G
      rw [hset]; exact b.1.2
    · apply Subtype.ext
      apply Subtype.ext
      exact hpair.symm

/-- In a family of 2-element edges, the number of neighbours of `v` inside `X`
counts the edges through `v` whose other vertex lies in `X`. -/
theorem ncard_inter_nbrs_eq {G : Hypergraph (Fin n)}
    (h2 : ∀ e ∈ G, edgeSize e = 2) (X : Set (Fin n)) (v : Fin n) :
    (X ∩ nbrs G v).ncard = Nat.card {e : G //
      v ∈ (e : Set (Fin n)) ∧ ((e : Set (Fin n)) \ {v}) ⊆ X} := by
  classical
  have hne : ∀ w : Fin n, w ∈ X ∩ nbrs G v → w ≠ v := by
    intro w hw hwv
    have hsz : edgeSize ({v, w} : Set (Fin n)) = 2 := h2 _ hw.2
    rw [hwv] at hsz
    have hp : ({v, v} : Set (Fin n)) = ({v} : Set (Fin n)) := by ext x; simp
    rw [hp, edgeSize_eq_ncard, Set.ncard_singleton] at hsz
    omega
  have huniv : (Set.univ : Set {e : G //
      v ∈ (e : Set (Fin n)) ∧ ((e : Set (Fin n)) \ {v}) ⊆ X}).ncard =
      Nat.card {e : G // v ∈ (e : Set (Fin n)) ∧ ((e : Set (Fin n)) \ {v}) ⊆ X} :=
    Set.ncard_univ _
  rw [← huniv]
  refine Set.ncard_congr
    (fun w hw => (⟨⟨{v, w}, hw.2⟩, ?_, ?_⟩ : {e : G //
      v ∈ (e : Set (Fin n)) ∧ ((e : Set (Fin n)) \ {v}) ⊆ X})) ?_ ?_ ?_
  · simp
  · intro x hx
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hx
    obtain ⟨hxmem, hxne⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
    rcases hxmem with h | h
    · exact absurd h hxne
    · rw [h]; exact hw.1
  · intro w hw; exact Set.mem_univ _
  · intro w w' hw hw' heq
    have h1 : ({v, w} : Set (Fin n)) = {v, w'} :=
      congrArg (fun x : {e : G // v ∈ (e : Set (Fin n)) ∧ ((e : Set (Fin n)) \ {v}) ⊆ X} =>
        (x.1 : Set (Fin n))) heq
    have h2' : w ∈ ({v, w'} : Set (Fin n)) := by rw [← h1]; simp
    rcases h2' with h | h
    · exact absurd h (hne w hw)
    · exact h
  · intro b _
    have hb2 : edgeSize (b.1 : Set (Fin n)) = 2 := h2 _ b.1.2
    have hpair := eq_pair_otherVertex (e := (b.1 : Set (Fin n))) (v := v) hb2 b.2.1
    have hex : ∃ x, x ∈ (b.1 : Set (Fin n)) ∧ x ≠ v := by
      by_contra hcon
      push_neg at hcon
      have hsub : (b.1 : Set (Fin n)) ⊆ {v} := fun x hx => by simpa using hcon x hx
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at h1
      have h2n : (b.1 : Set (Fin n)).ncard = 2 := by rw [← edgeSize_eq_ncard]; exact hb2
      omega
    have hset : ({v, otherVertex (b.1 : Set (Fin n)) v} : Set (Fin n)) = (b.1 : Set (Fin n)) :=
      hpair.symm
    refine ⟨otherVertex (b.1 : Set (Fin n)) v, ⟨?_, ?_⟩, ?_⟩
    · exact b.2.2 ⟨otherVertex_mem hex, by simpa using otherVertex_ne hex⟩
    · change ({v, otherVertex (b.1 : Set (Fin n)) v} : Set (Fin n)) ∈ G
      rw [hset]; exact b.1.2
    · apply Subtype.ext
      apply Subtype.ext
      exact hpair.symm

/-! ## Counting edges between two vertex sets -/

/-- Membership in `s.product t`. -/
theorem mem_product' {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := by
  rw [show s.product t = s ×ˢ t from rfl, Finset.mem_product]

/-- The ordered pairs between `S` and `T` whose edge lies in `R`. -/
noncomputable def edgeCount_pairs (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact (S.product T).filter (fun p => ({p.1, p.2} : Set (Fin n)) ∈ R)

/-- The 2-edges of `R` meeting both `S` and `T`. -/
noncomputable def edgesBetween (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    Finset (Set (Fin n)) := by
  classical
  exact (canonFinset R).filter (fun e => (∃ s ∈ (e : Set (Fin n)), s ∈ (S : Set (Fin n))) ∧
    (∃ t ∈ (e : Set (Fin n)), t ∈ (T : Set (Fin n))))

theorem mem_edgesBetween {R : Hypergraph (Fin n)} {S T : Finset (Fin n)} {e : Set (Fin n)} :
    e ∈ edgesBetween R S T ↔ e ∈ R ∧ (∃ s ∈ e, s ∈ (S : Set (Fin n))) ∧
      (∃ t ∈ e, t ∈ (T : Set (Fin n))) := by
  classical
  unfold edgesBetween canonFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- For a family of 2-element edges and disjoint vertex sets, `edgeCount`
counts exactly the edges between the two sets. -/
theorem edgeCount_eq_edgesBetween {R : Hypergraph (Fin n)}
    (h2 : ∀ e ∈ R, edgeSize e = 2) {S T : Finset (Fin n)} (hd : Disjoint S T) :
    edgeCount R S T = (edgesBetween R S T).card := by
  classical
  have hmap : Set.MapsTo (fun p : Fin n × Fin n => ({p.1, p.2} : Set (Fin n)))
      ↑(edgeCount_pairs R S T) ↑(edgesBetween R S T) := by
    intro p hp
    have hp' : p ∈ edgeCount_pairs R S T := hp
    rw [edgeCount_pairs, Finset.mem_filter, mem_product'] at hp'
    obtain ⟨⟨hpS, hpT⟩, hpR⟩ := hp'
    have hmem : ({p.1, p.2} : Set (Fin n)) ∈ edgesBetween R S T := by
      rw [mem_edgesBetween]
      exact ⟨hpR, ⟨p.1, by simp, hpS⟩, ⟨p.2, by simp, hpT⟩⟩
    simpa using hmem
  have hfiber : ∀ b ∈ edgesBetween R S T,
      ((edgeCount_pairs R S T).filter
        (fun a : Fin n × Fin n => ({a.1, a.2} : Set (Fin n)) = b)).card = 1 := by
    intro b hb
    rw [mem_edgesBetween] at hb
    obtain ⟨hbR, ⟨s, hsb, hsS⟩, ⟨t, htb, htT⟩⟩ := hb
    have hb2 : edgeSize b = 2 := h2 b hbR
    have hbn : b.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact hb2
    have hpair : b = ({s, t} : Set (Fin n)) := by
      obtain ⟨x, y, hxy, hbxy⟩ := Set.ncard_eq_two.mp hbn
      have hsxy : s = x ∨ s = y := by rw [hbxy] at hsb; simpa using hsb
      have htxy : t = x ∨ t = y := by rw [hbxy] at htb; simpa using htb
      rw [hbxy]
      rcases hsxy with h1 | h1 <;> rcases htxy with h2 | h2
      · exact absurd (h1.trans h2.symm) (by intro hst; exact Finset.disjoint_left.mp hd hsS (hst ▸ htT))
      · rw [← h1, ← h2]
      · rw [← h2, ← h1]; exact Set.pair_comm _ _
      · exact absurd (h1.trans h2.symm) (by intro hst; exact Finset.disjoint_left.mp hd hsS (hst ▸ htT))
    have hfib : (edgeCount_pairs R S T).filter
        (fun a : Fin n × Fin n => ({a.1, a.2} : Set (Fin n)) = b) =
        ({((s, t) : Fin n × Fin n)} : Finset (Fin n × Fin n)) := by
      ext a
      unfold edgeCount_pairs
      rw [Finset.mem_filter, Finset.mem_filter, mem_product', Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨haS, haT⟩, haR⟩, haeq⟩
        have h1 : a.1 ∈ ({s, t} : Set (Fin n)) := by rw [← hpair, ← haeq]; simp
        have h2 : a.2 ∈ ({s, t} : Set (Fin n)) := by rw [← hpair, ← haeq]; simp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
        have hcon : a.1 = a.2 → False :=
          fun haa => Finset.disjoint_left.mp hd haS (by rw [haa]; exact haT)
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hcon
        · exact Prod.ext h1 h2
        · exact absurd (h1 ▸ htT) (Finset.disjoint_left.mp hd haS)
        · exact absurd (h1 ▸ htT) (Finset.disjoint_left.mp hd haS)
      · intro ha
        rw [ha]
        refine ⟨⟨⟨hsS, htT⟩, ?_⟩, ?_⟩
        · change ({s, t} : Set (Fin n)) ∈ R
          rw [← hpair]; exact hbR
        · change ({s, t} : Set (Fin n)) = b
          exact hpair.symm
    rw [hfib, Finset.card_singleton]
  have h1 : edgeCount R S T = (edgeCount_pairs R S T).card := rfl
  rw [h1, Finset.card_eq_sum_card_fiberwise hmap, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl (fun b hb => hfiber b hb)

end
end ErdosFaberLovaszConjecture

