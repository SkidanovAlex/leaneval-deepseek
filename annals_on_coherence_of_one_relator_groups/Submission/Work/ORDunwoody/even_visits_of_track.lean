import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.Chord
import Submission.Work.ORDunwoody.even_visits_of_label
import Submission.Work.ORDunwoody.trackOf_eq_of_chord

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

/-!
## The parity of the visits of a face in a fixed track

`even_visits_of_label` shows that a face of `Λ''` visits the cells with a fixed *label* (a fixed
edge of `T`) an even number of times.  Here we prove the same statement for the visits lying in a
fixed **track** (a connected component of the chord graph on the pattern points).

The argument is elementary once the chord structure is unwound.  Fix the face `(r, c)`, its visit
list `l`, and a track `τ`, with `e₀ = τ.label`.  A visit `m` with `trackOf m = τ` has
`m.label = (trackOf m).label = τ.label = e₀` (`Track.label_trackOf`), so all the visits we count
lie in the single fibre `e₀`.

By construction (`Dunwoody.chords`, `Dunwoody.pairUp`), the visits of the fibre `e₀` are paired
consecutively in the order of the walk: the 1st with the 2nd, the 3rd with the 4th, … .  Each such
pair is a **chord** of the face, and the two visits of a chord lie in one track
(`trackOf_eq_of_chord`).  Hence the visits of the fibre `e₀` lying in `τ` are a union of pairs,
so their number is even; and it *is* the number of visits of the face in `τ`.
-/

/-! ## 1. The positions of the entries with a given label -/

/-- The positions, in the list `l`, at which `f` has the value `e`, accumulated from the offset
`i` (the generic form of `Dunwoody.positionsOfLabelAux`). -/
def posAux {α : Type*} {β : Type*} [DecidableEq β] (f : α → β) : List α → β → ℕ → List ℕ
  | [], _, _ => []
  | m :: rest, e, i => (if f m = e then [i] else []) ++ posAux f rest e (i + 1)

/-- The positions, in the list `l`, at which `f` has the value `e`. -/
def posOf {α : Type*} {β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) : List ℕ :=
  posAux f l e 0

@[simp] lemma posAux_nil {α β : Type*} [DecidableEq β] (f : α → β) (e : β) (i : ℕ) :
    posAux f ([] : List α) e i = [] := rfl

@[simp] lemma posAux_cons {α β : Type*} [DecidableEq β] (f : α → β) (m : α) (rest : List α)
    (e : β) (i : ℕ) :
    posAux f (m :: rest) e i = (if f m = e then [i] else []) ++ posAux f rest e (i + 1) := rfl

/-- Shifting the offset shifts all the positions by the same amount. -/
lemma posAux_shift {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) (i k : ℕ) :
    posAux f l e (i + k) = (posAux f l e i).map (fun p => p + k) := by
  induction l generalizing i with
  | nil => rfl
  | cons m rest ih =>
      simp only [posAux_cons, List.map_append]
      rw [show i + k + 1 = (i + 1) + k from by omega, ih (i + 1)]
      by_cases h : f m = e <;> simp [h]

/-- The labelled positions are positions of the list. -/
lemma posAux_lt {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) (i p : ℕ)
    (h : p ∈ posAux f l e i) : p < i + l.length := by
  induction l generalizing i with
  | nil => exact absurd h List.not_mem_nil
  | cons m rest ih =>
      rw [posAux_cons] at h
      by_cases hfm : f m = e
      · rw [if_pos hfm, List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · subst h
          simp
        · have := ih (i + 1) h
          simp only [List.length_cons] at this ⊢
          omega
      · rw [if_neg hfm, List.nil_append] at h
        have := ih (i + 1) h
        simp only [List.length_cons] at this ⊢
        omega

/-- A position occurs in `posAux f l e i` exactly when it is `i` plus a position of `l` at which
`f` has value `e`. -/
lemma posAux_mem_iff {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) (i p : ℕ) :
    p ∈ posAux f l e i ↔ ∃ (k : ℕ) (hk : k < l.length), p = i + k ∧ f (l[k]) = e := by
  induction l generalizing i with
  | nil =>
      constructor
      · intro h; exact absurd h List.not_mem_nil
      · rintro ⟨k, hk, _⟩; exact absurd hk (by simp)
  | cons m rest ih =>
      by_cases hfm : f m = e
      · rw [posAux_cons, if_pos hfm, List.mem_append, List.mem_singleton, ih (i + 1)]
        constructor
        · rintro (hp | ⟨k, hk, hp, hf⟩)
          · subst hp
            exact ⟨0, by simp, by simp, hfm⟩
          · exact ⟨k + 1, by simpa using hk, by omega, by rwa [List.getElem_cons_succ]⟩
        · rintro ⟨k, hk, hp, hf⟩
          match k with
          | 0 => exact Or.inl (by omega)
          | k' + 1 =>
              exact Or.inr ⟨k', by simpa using hk, by omega,
                by rwa [List.getElem_cons_succ] at hf⟩
      · rw [posAux_cons, if_neg hfm, List.nil_append, ih (i + 1)]
        constructor
        · rintro ⟨k, hk, hp, hf⟩
          exact ⟨k + 1, by simpa using hk, by omega, by rwa [List.getElem_cons_succ]⟩
        · rintro ⟨k, hk, hp, hf⟩
          match k with
          | 0 => exact absurd (by rwa [List.getElem_cons_zero] at hf) hfm
          | k' + 1 =>
              exact ⟨k', by simpa using hk, by omega, by rwa [List.getElem_cons_succ] at hf⟩

/-- The number of labelled positions is the length of the filtered list. -/
lemma posAux_length {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) (i : ℕ) :
    (posAux f l e i).length = (l.filter (fun x => decide (f x = e))).length := by
  induction l generalizing i with
  | nil => simp
  | cons m rest ih =>
      rw [posAux_cons, List.length_append, ih (i + 1)]
      by_cases h : f m = e
      · rw [if_pos h, List.filter_cons_of_pos (by simp [h])]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [if_neg h, List.filter_cons_of_neg (by simp [h])]
        simp

/-! ## 2. Pairing the entries of a list -/

/-- The ordered pair of entries of `l` at a pair of positions, if both positions are in range. -/
def pairOpt {α : Type*} (l : List α) (pr : ℕ × ℕ) : Option (α × α) :=
  match l[pr.1]?, l[pr.2]? with
  | some x, some y => some (x, y)
  | _, _ => none

lemma pairOpt_eq_some_iff {α : Type*} {l : List α} {pr : ℕ × ℕ} {z : α × α} :
    pairOpt l pr = some z ↔ l[pr.1]? = some z.1 ∧ l[pr.2]? = some z.2 := by
  obtain ⟨p, q⟩ := pr
  obtain ⟨x, y⟩ := z
  simp only [pairOpt]
  cases hp : l[p]? with
  | none => simp
  | some a =>
      cases hq : l[q]? with
      | none => simp
      | some b => simp

lemma pairOpt_apply {α : Type*} (l : List α) (p q : ℕ) (x y : α) (hx : l[p]? = some x)
    (hy : l[q]? = some y) : pairOpt l (p, q) = some (x, y) := by
  rw [pairOpt_eq_some_iff]
  exact ⟨hx, hy⟩

/-- `Even (n + 2)` gives `Even n`. -/
lemma even_of_even_add_two {n : ℕ} (h : Even (n + 2)) : Even n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k - 1, by omega⟩

/-- **The pairing lemma.**  If a list is the concatenation of the two entries of each element of
a list `Z` of pairs, and the two entries of every pair of `Z` have the same `g`-value, then it
meets every value of `g` an even number of times. -/
lemma even_filter_flatMap_pairs {α γ : Type*} [DecidableEq γ] (Z : List (α × α)) (g : α → γ)
    (c : γ) (h : ∀ pr ∈ Z, g pr.1 = g pr.2) :
    Even ((Z.flatMap (fun pr => [pr.1, pr.2])).filter (fun x => decide (g x = c))).length := by
  induction Z with
  | nil => exact ⟨0, rfl⟩
  | cons pr rest ih =>
      have hpr : g pr.1 = g pr.2 := h pr (by simp)
      have hrest : ∀ q ∈ rest, g q.1 = g q.2 := fun q hq => h q (by simp [hq])
      have hih := ih hrest
      rw [List.flatMap_cons, List.filter_append, List.length_append]
      by_cases hc : g pr.1 = c
      · have hc2 : g pr.2 = c := by rw [← hpr]; exact hc
        rw [List.filter_cons_of_pos (by simp [hc]), List.filter_cons_of_pos (by simp [hc2])]
        simp only [List.length_cons]
        exact Even.add ⟨1, rfl⟩ hih
      · have hc2 : ¬ (g pr.2 = c) := by intro h2; exact hc (by rw [hpr]; exact h2)
        rw [List.filter_cons_of_neg (by simp [hc]), List.filter_cons_of_neg (by simp [hc2])]
        simp only [List.filter_nil, List.length_nil, Nat.zero_add]
        exact hih

/-- Flattening the consecutive pairs of a list of even length returns the list. -/
theorem pairUp_flatMap : ∀ (P : List ℕ), Even P.length →
    (pairUp P).flatMap (fun pr => [pr.1, pr.2]) = P
  | [], _ => rfl
  | [_], h => absurd h Nat.not_even_one
  | a :: b :: rest, h => by
      have he' : Even rest.length := even_of_even_add_two (by simpa using h)
      rw [pairUp_cons_cons, List.flatMap_cons, pairUp_flatMap rest he']
      exact List.singleton_append

/-! ## 3. The fibre list as the entries at the labelled positions -/

/-- The list of the entries of `l` sitting at the positions where `f` takes the value `e`. -/
theorem filter_eq_filterMap_posOf {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (e : β) :
    l.filter (fun x => decide (f x = e)) = (posOf f l e).filterMap (fun p => l[p]?) := by
  induction l with
  | nil => rfl
  | cons m t ih =>
      have hshift : posAux f t e (0 + 1) = (posOf f t e).map (fun p => p + 1) := by
        rw [posOf]; exact posAux_shift f t e 0 1
      rw [posOf, posAux_cons, hshift, List.filterMap_append, List.filterMap_map]
      simp only [Function.comp_apply, List.getElem?_cons_succ]
      rw [← ih]
      by_cases h : f m = e
      · rw [if_pos h,
          List.filterMap_cons_some (f := fun p => (m :: t)[p]?)
            (List.getElem?_cons_zero (a := m) (l := t))]
        simp [h]
      · rw [if_neg h]
        simp [h]

/-- The same, for the consecutive pairs of the labelled positions: the entries at the labelled
positions are the concatenation of the pairs of entries at consecutive pairs of positions. -/
theorem chunk_filterMap {α : Type*} : ∀ (l : List α) (P : List ℕ), (∀ p ∈ P, p < l.length) →
    Even P.length →
    P.filterMap (fun p => l[p]?) =
      ((pairUp P).filterMap (pairOpt l)).flatMap (fun pr => [pr.1, pr.2])
  | l, [], _, _ => rfl
  | l, [u], _, he => absurd he Nat.not_even_one
  | l, u :: v :: rest, hlt, he => by
      have hu : u < l.length := hlt u (by simp)
      have hv : v < l.length := hlt v (by simp)
      have hlt' : ∀ p ∈ rest, p < l.length := fun p hp => hlt p (by simp [hp])
      have he' : Even rest.length := even_of_even_add_two (by simpa using he)
      rw [List.filterMap_cons_some (List.getElem?_eq_getElem hu),
          List.filterMap_cons_some (List.getElem?_eq_getElem hv),
          pairUp_cons_cons,
          List.filterMap_cons_some (pairOpt_apply l u v _ _
            (List.getElem?_eq_getElem hu) (List.getElem?_eq_getElem hv)),
          List.flatMap_cons, ← chunk_filterMap l rest hlt' he']
      exact List.singleton_append

/-! ## 4. The specialisation to the pattern points of a face -/

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-- `posAux` with the label of a pattern point is `Dunwoody.positionsOfLabelAux`. -/
lemma posAux_eq_positionsOfLabelAux (l : List (MidV D)) (e : Sym2 V) (i : ℕ) :
    posAux (MidV.label (D := D)) l e i = positionsOfLabelAux l e i := by
  induction l generalizing i with
  | nil => rfl
  | cons m rest ih =>
      simp only [posAux_cons, positionsOfLabelAux, ih]

/-- The positions of the visits with a fixed label are positions of the visit list. -/
lemma positionsOfLabel_lt {l : List (MidV D)} {e : Sym2 V} {p : ℕ}
    (h : p ∈ positionsOfLabel l e) : p < l.length := by
  have h' : p ∈ posAux (MidV.label (D := D)) l e 0 := by
    rw [posAux_eq_positionsOfLabelAux]; exact h
  have := posAux_lt _ l e 0 p h'
  simpa using this

/-- The number of visits of a fibre is the length of the filtered visit list. -/
lemma positionsOfLabel_length (l : List (MidV D)) (e : Sym2 V) :
    (positionsOfLabel l e).length = (l.filter (fun m => decide (MidV.label m = e))).length := by
  show (positionsOfLabelAux l e 0).length = _
  rw [← posAux_eq_positionsOfLabelAux, posAux_length]

/-- `posOf` with the label of a pattern point is `positionsOfLabel`. -/
lemma posOf_label_eq (l : List (MidV D)) (e : Sym2 V) :
    posOf (MidV.label (D := D)) l e = positionsOfLabel l e := by
  show posAux (MidV.label (D := D)) l e 0 = positionsOfLabelAux l e 0
  rw [posAux_eq_positionsOfLabelAux]

/-- A visit listed at a position of the label `e` has label `e`. -/
lemma map_label_getElem?_of_mem_positionsOfLabel {l : List (MidV D)} {e : Sym2 V} {p : ℕ}
    (h : p ∈ positionsOfLabel l e) : (l[p]?).map (MidV.label (D := D)) = some e := by
  have h' : p ∈ posAux (MidV.label (D := D)) l e 0 := by
    rw [posAux_eq_positionsOfLabelAux]; exact h
  obtain ⟨k, hk, hpk, hfk⟩ := (posAux_mem_iff _ l e 0 p).mp h'
  have hpk' : p = k := by omega
  rw [hpk', List.getElem?_eq_getElem hk]
  simp [hfk]

/-- A visit listed at a position of the label `e` has label `e`. -/
lemma label_of_mem_positionsOfLabel {l : List (MidV D)} {e : Sym2 V} {p : ℕ}
    (h : p ∈ positionsOfLabel l e) (hp : p < l.length) :
    MidV.label (l[p]'hp) = e := by
  have h' := map_label_getElem?_of_mem_positionsOfLabel (D := D) h
  rw [List.getElem?_eq_getElem hp] at h'
  simpa using h'

/-- A pairing of two consecutive positions of the label `e₀` is a chord of the visit list. -/
lemma mem_chords_of_mem_pairUp {l : List (MidV D)} {e₀ : Sym2 V} {pr : ℕ × ℕ}
    (h : pr ∈ pairUp (positionsOfLabel l e₀)) : pr ∈ chords l := by
  by_cases hne : positionsOfLabel l e₀ = []
  · rw [hne] at h
    simp at h
  · obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
    have hult : u < l.length := positionsOfLabel_lt hu
    have hmem : e₀ ∈ labelSet l := by
      show e₀ ∈ (l.map (MidV.label (D := D))).dedup
      rw [List.mem_dedup, List.mem_map]
      exact ⟨l[u]'hult, List.getElem_mem hult, label_of_mem_positionsOfLabel hu hult⟩
    show pr ∈ (labelSet l).flatMap (fun e => pairUp (positionsOfLabel l e))
    exact List.mem_flatMap.mpr ⟨e₀, hmem, h⟩

/-! ## 5. The theorem -/

theorem even_visits_of_track {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    [DecidableEq (Work.ORDunwoody.Dunwoody.Track D)]
    (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G)
    (τ : Work.ORDunwoody.Dunwoody.Track D) :
    Even ((Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1)).filter
      (fun m => Work.ORDunwoody.Dunwoody.trackOf m = τ)).length := by
  set l : List (MidV D) := faceVisits D c (FreeGroup.toWord r.1) with hl
  set e₀ : Sym2 V := τ.label with he₀
  set Ppos : List ℕ := positionsOfLabel l e₀ with hP
  set Z : List (MidV D × MidV D) := (pairUp Ppos).filterMap (pairOpt l) with hZ
  -- the visits of the fibre `e₀` come in pairs
  have hlen : Even Ppos.length := by
    have h1 : Ppos.length = (l.filter (fun m => decide (MidV.label m = e₀))).length := by
      rw [hP, positionsOfLabel_length]
    rw [h1]
    exact even_visits_of_label r c e₀
  have hlt : ∀ p ∈ Ppos, p < l.length := fun p hp => by
    rw [hP] at hp
    exact positionsOfLabel_lt hp
  -- the fibre list is the concatenation of the pairs of `Z`
  have hQ : l.filter (fun m => decide (MidV.label m = e₀)) =
      Z.flatMap (fun pr => [pr.1, pr.2]) := by
    rw [filter_eq_filterMap_posOf (MidV.label) l e₀, posOf_label_eq, ← hP,
      chunk_filterMap l Ppos hlt hlen, ← hZ]
  -- every pair of `Z` lies in one track
  have hZpair : ∀ pr ∈ Z, trackOf pr.1 = trackOf pr.2 := by
    intro pr hpr
    rw [hZ] at hpr
    obtain ⟨pr', hpr', hpr'eq⟩ := List.mem_filterMap.mp hpr
    obtain ⟨p, q⟩ := pr'
    obtain ⟨h1, h2⟩ := pairOpt_eq_some_iff.mp hpr'eq
    exact trackOf_eq_of_chord r c (mem_chords_of_mem_pairUp hpr') h1 h2
  -- hence the fibre meets each track an even number of times
  have hpar := even_filter_flatMap_pairs Z (trackOf (D := D)) τ hZpair
  -- and the visits of the face in `τ` are exactly the visits of the fibre `e₀` in `τ`
  have hgoal : (l.filter (fun m => decide (trackOf m = τ))).length =
      ((Z.flatMap (fun pr => [pr.1, pr.2])).filter
        (fun x => decide (trackOf x = τ))).length := by
    rw [← hQ]
    congr 1
    rw [List.filter_filter]
    exact (List.filter_congr (fun x _ => by
      by_cases hxτ : trackOf x = τ
      · have hlab : MidV.label x = e₀ := by
          have h := Track.label_trackOf x
          rw [hxτ] at h
          exact h.symm.trans he₀.symm
        simp [hxτ, hlab]
      · simp [hxτ])).symm
  rw [hgoal]
  exact hpar

end Work.ORDunwoody
