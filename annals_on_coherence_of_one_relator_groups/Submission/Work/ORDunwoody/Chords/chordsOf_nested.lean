import Mathlib
import Submission.Work.ORDunwoody.Chords.Basic
import Submission.Work.ORDunwoody.Tracks.even_edges_count

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open scoped Sym2

namespace Work.ORDunwoody.Chords

variable {α : Type u}

/-! ## Combinatorics of `pairUp` -/

theorem pairUp_append_of_even : ∀ (L M : List ℕ), Even L.length →
    pairUp (L ++ M) = pairUp L ++ pairUp M
  | [], _, _ => by simp
  | [_], _, h => by
      obtain ⟨k, hk⟩ := h
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk
      omega
  | a :: b :: L, M, h => by
      simp only [List.cons_append, pairUp_cons_cons]
      have h' : Even L.length := by
        obtain ⟨k, hk⟩ := h
        simp only [List.length_cons] at hk
        exact ⟨k - 1, by omega⟩
      rw [pairUp_append_of_even L M h']

theorem pairUp_map_add : ∀ (L : List ℕ) (k : ℕ),
    pairUp (L.map (· + k)) = (pairUp L).map (fun p => (p.1 + k, p.2 + k))
  | [], k => by simp
  | [_], k => by simp
  | a :: b :: L, k => by
      simp only [List.map_cons, pairUp_cons_cons]
      rw [pairUp_map_add L k]

theorem pairUp_even_all_matched : ∀ (L : List ℕ) (h : Even L.length), ∀ t ∈ L,
    ∃ t' ∈ L, (t, t') ∈ pairUp L ∨ (t', t) ∈ pairUp L
  | [], _, t, ht => by simp at ht
  | [_], h, t, ht => by
      obtain ⟨k, hk⟩ := h
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hk
      omega
  | a :: b :: L, h, t, ht => by
      have h' : Even L.length := by
        obtain ⟨k, hk⟩ := h
        simp only [List.length_cons] at hk
        exact ⟨k - 1, by omega⟩
      simp only [List.mem_cons] at ht
      rw [pairUp_cons_cons]
      rcases ht with rfl | rfl | ht
      · exact ⟨b, by simp, Or.inl (by simp)⟩
      · exact ⟨a, by simp, Or.inr (by simp)⟩
      · obtain ⟨t', ht', hh⟩ := pairUp_even_all_matched L h' t ht
        refine ⟨t', by simp [ht'], ?_⟩
        rcases hh with hh | hh
        · exact Or.inl (by simp only [List.mem_cons]; exact Or.inr hh)
        · exact Or.inr (by simp only [List.mem_cons]; exact Or.inr hh)

theorem pairUp_fst_mem : ∀ (L : List ℕ) {p q : ℕ}, (p, q) ∈ pairUp L → p ∈ L
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: L, p, q, h => by
      simp only [pairUp_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [List.mem_cons]; exact Or.inl (congrArg Prod.fst h)
      · rw [List.mem_cons, List.mem_cons]; exact Or.inr (Or.inr (pairUp_fst_mem L h))

theorem pairUp_snd_mem : ∀ (L : List ℕ) {p q : ℕ}, (p, q) ∈ pairUp L → q ∈ L
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: L, p, q, h => by
      simp only [pairUp_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [List.mem_cons, List.mem_cons]; exact Or.inr (Or.inl (congrArg Prod.snd h))
      · rw [List.mem_cons, List.mem_cons]; exact Or.inr (Or.inr (pairUp_snd_mem L h))

theorem pairUp_eq_nil_of_length_le_one : ∀ (L : List ℕ), L.length ≤ 1 → pairUp L = []
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-! ## Combinatorics of `posOf` -/

variable [DecidableEq α]

theorem posOfAux_add_shift (l : List α) (e : α) (i k : ℕ) :
    posOfAux l e (i + k) = (posOfAux l e i).map (· + k) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    simp only [posOfAux_cons]
    rw [show i + k + 1 = (i + 1) + k by omega, ih, List.map_append]
    congr 1
    by_cases h : a = e <;> simp [h]

theorem posOfAux_append (A B : List α) (e : α) (i : ℕ) :
    posOfAux (A ++ B) e i = posOfAux A e i ++ posOfAux B e (i + A.length) := by
  induction A generalizing i with
  | nil => simp
  | cons a A ih =>
    simp only [List.cons_append, posOfAux_cons]
    rw [ih (i + 1)]
    rw [show i + (a :: A).length = (i + 1) + A.length by
      simp only [List.length_cons]; omega]
    rw [List.append_assoc]

theorem posOf_append (A B : List α) (e : α) :
    posOf (A ++ B) e = posOf A e ++ (posOf B e).map (· + A.length) := by
  unfold posOf
  rw [posOfAux_append, posOfAux_add_shift]

theorem posOfAux_length (l : List α) (e : α) (i : ℕ) :
    (posOfAux l e i).length = l.count e := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rw [posOfAux_cons, List.length_append, ih]
    by_cases h : a = e
    · rw [h, if_pos rfl, List.length_cons, List.length_nil, Nat.zero_add, List.count_cons_self]
      omega
    · rw [if_neg h, List.length_nil, Nat.zero_add, List.count_cons_of_ne h]

theorem posOf_length (l : List α) (e : α) : (posOf l e).length = l.count e :=
  posOfAux_length l e 0

theorem posOf_cons (a : α) (l : List α) (f : α) :
    posOf (a :: l) f = (if a = f then [0] else []) ++ (posOf l f).map (· + 1) := by
  unfold posOf
  rw [posOfAux_cons, posOfAux_add_shift]

theorem mem_posOfAux (l : List α) (e : α) (i j : ℕ) :
    j ∈ posOfAux l e i ↔ ∃ t, j = i + t ∧ l[t]? = some e := by
  induction l generalizing i with
  | nil => simp [posOfAux]
  | cons a l ih =>
    rw [posOfAux_cons]
    by_cases ha : a = e
    · rw [if_pos ha, List.singleton_append, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact ⟨0, by simp, by rw [List.getElem?_cons_zero, ha]⟩
        · obtain ⟨t, hj, hl⟩ := (ih (i + 1)).mp h
          exact ⟨t + 1, by omega, by rw [List.getElem?_cons_succ]; exact hl⟩
      · rintro ⟨t, hj, hl⟩
        cases t with
        | zero => left; omega
        | succ t' =>
          right
          rw [List.getElem?_cons_succ] at hl
          exact (ih (i + 1)).mpr ⟨t', by omega, hl⟩
    · rw [if_neg ha, List.nil_append]
      constructor
      · intro h
        obtain ⟨t, hj, hl⟩ := (ih (i + 1)).mp h
        exact ⟨t + 1, by omega, by rw [List.getElem?_cons_succ]; exact hl⟩
      · rintro ⟨t, hj, hl⟩
        cases t with
        | zero =>
          rw [List.getElem?_cons_zero] at hl
          exact absurd (Option.some.inj hl) ha
        | succ t' =>
          rw [List.getElem?_cons_succ] at hl
          exact (ih (i + 1)).mpr ⟨t', by omega, hl⟩

theorem mem_posOf (l : List α) (e : α) (j : ℕ) :
    j ∈ posOf l e ↔ j < l.length ∧ l[j]? = some e := by
  unfold posOf
  rw [mem_posOfAux]
  constructor
  · rintro ⟨t, hj, hl⟩
    rw [Nat.zero_add] at hj
    rw [hj]
    exact ⟨(List.getElem?_eq_some_iff.mp hl).1, hl⟩
  · rintro ⟨hj, hl⟩
    exact ⟨j, by simp, hl⟩

theorem posOf_lt {l : List α} {e : α} {j : ℕ} (h : j ∈ posOf l e) : j < l.length :=
  ((mem_posOf l e j).mp h).1

theorem posOf_eq_nil_of_notMem (l : List α) (e : α) (h : e ∉ l) : posOf l e = [] := by
  rw [← List.length_eq_zero_iff, posOf_length]
  exact List.count_eq_zero.mpr h

/-! ## `chordsOf` -/

theorem mem_chordsOf_iff (l : List α) (p q : ℕ) :
    (p, q) ∈ chordsOf l ↔ ∃ e, (p, q) ∈ pairUp (posOf l e) := by
  rw [chordsOf, List.mem_flatMap]
  constructor
  · rintro ⟨e, _, he⟩; exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    have hel : e ∈ l := by
      by_contra hnot
      rw [posOf_eq_nil_of_notMem l e hnot, pairUp_nil] at he
      exact List.not_mem_nil he
    exact ⟨e, List.mem_dedup.mpr hel, he⟩

theorem chordsOf_eq_nil_of_length_le_one (l : List α) (h : l.length ≤ 1) : chordsOf l = [] := by
  rw [chordsOf]
  cases hd : l.dedup with
  | nil => simp
  | cons e t =>
    have ht : t = [] := by
      have h1 : (e :: t).length ≤ 1 := by
        rw [← hd]
        exact le_trans (List.Sublist.length_le (List.dedup_sublist l)) h
      simp only [List.length_cons] at h1
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact pairUp_eq_nil_of_length_le_one (posOf l e)
      (by rw [posOf_length]; exact le_trans List.count_le_length h)

theorem mem_chordsOf_lt {l : List α} {p q : ℕ} (h : (p, q) ∈ chordsOf l) : p < l.length := by
  obtain ⟨e, he⟩ := (mem_chordsOf_iff l p q).mp h
  exact posOf_lt (pairUp_fst_mem (posOf l e) he)

theorem mem_chordsOf_snd {l : List α} {p q : ℕ} (h : (p, q) ∈ chordsOf l) : q < l.length := by
  obtain ⟨e, he⟩ := (mem_chordsOf_iff l p q).mp h
  exact posOf_lt (pairUp_snd_mem (posOf l e) he)

theorem posOf_cons_cons_self (l : List α) (e : α) (he : e ∉ l) :
    posOf (e :: (l ++ [e])) e = [0, l.length + 1] := by
  have h1 : posOf [e] e = [0] := by simp [posOf_cons]
  rw [posOf_cons, posOf_append, posOf_eq_nil_of_notMem l e he, h1]
  simp

theorem posOf_cons_cons_of_ne (l : List α) (e f : α) (hf : f ≠ e) :
    posOf (e :: (l ++ [e])) f = (posOf l f).map (· + 1) := by
  have hfe : e ≠ f := fun h => hf h.symm
  have h1 : posOf [e] f = [] := by simp [posOf_cons, hfe]
  rw [posOf_cons, posOf_append, h1]
  simp only [if_neg hfe, List.nil_append, List.append_nil, List.map_nil]

theorem mem_chordsOf_append (A B : List α) (hA : ∀ e, Even (A.count e)) (p q : ℕ) :
    (p, q) ∈ chordsOf (A ++ B) ↔
      (p, q) ∈ chordsOf A ∨ (∃ i j, p = i + A.length ∧ q = j + A.length ∧ (i, j) ∈ chordsOf B) := by
  rw [mem_chordsOf_iff, mem_chordsOf_iff]
  constructor
  · rintro ⟨e, he⟩
    rw [posOf_append, pairUp_append_of_even _ _ (by rw [posOf_length]; exact hA e), List.mem_append,
      pairUp_map_add, List.mem_map] at he
    rcases he with he | ⟨⟨i, j⟩, hij, hpq⟩
    · exact Or.inl ⟨e, he⟩
    · exact Or.inr ⟨i, j, (congrArg Prod.fst hpq).symm, (congrArg Prod.snd hpq).symm,
        (mem_chordsOf_iff B i j).mpr ⟨e, hij⟩⟩
  · rintro (⟨e, he⟩ | ⟨i, j, hp, hq, hc⟩)
    · refine ⟨e, ?_⟩
      rw [posOf_append, pairUp_append_of_even _ _ (by rw [posOf_length]; exact hA e), List.mem_append]
      exact Or.inl he
    · obtain ⟨e, he⟩ := (mem_chordsOf_iff B i j).mp hc
      refine ⟨e, ?_⟩
      rw [posOf_append, pairUp_append_of_even _ _ (by rw [posOf_length]; exact hA e), List.mem_append,
        pairUp_map_add, List.mem_map]
      exact Or.inr ⟨(i, j), he, by simp [hp, hq]⟩

theorem mem_chordsOf_bracket (e : α) (D : List α) (he : e ∉ D) (p q : ℕ) :
    (p, q) ∈ chordsOf (e :: (D ++ [e])) ↔
      (p, q) = (0, D.length + 1) ∨ (∃ i j, p = i + 1 ∧ q = j + 1 ∧ (i, j) ∈ chordsOf D) := by
  rw [mem_chordsOf_iff]
  constructor
  · rintro ⟨f, hf⟩
    by_cases hfe : f = e
    · rw [hfe] at hf
      rw [posOf_cons_cons_self D e he] at hf
      left
      simpa using hf
    · rw [posOf_cons_cons_of_ne D e f hfe, pairUp_map_add, List.mem_map] at hf
      rcases hf with ⟨⟨i, j⟩, hij, hpq⟩
      exact Or.inr ⟨i, j, (congrArg Prod.fst hpq).symm, (congrArg Prod.snd hpq).symm,
        (mem_chordsOf_iff D i j).mpr ⟨f, hij⟩⟩
  · rintro (h | ⟨i, j, hp, hq, hc⟩)
    · refine ⟨e, ?_⟩
      rw [h, posOf_cons_cons_self D e he]
      simp
    · obtain ⟨f, hf⟩ := (mem_chordsOf_iff D i j).mp hc
      have hfe : f ≠ e := by
        intro hfe'
        rw [hfe'] at hf
        rw [posOf_eq_nil_of_notMem D e he, pairUp_nil] at hf
        exact List.not_mem_nil hf
      refine ⟨f, ?_⟩
      rw [posOf_cons_cons_of_ne D e f hfe, pairUp_map_add, List.mem_map]
      exact ⟨(i, j), hf, by simp [hp, hq]⟩

theorem chordsOf_complete (l : List α) (h : ∀ e, Even (l.count e)) (i : ℕ) (hi : i < l.length) :
    ∃ j, IsChordOf l i j := by
  have hmem : i ∈ posOf l (l[i]) := by
    rw [mem_posOf]
    exact ⟨hi, List.getElem?_eq_getElem hi⟩
  have heven : Even (posOf l (l[i])).length := by
    rw [posOf_length]; exact h (l[i])
  obtain ⟨t', ht', hh⟩ := pairUp_even_all_matched (posOf l (l[i])) heven i hmem
  rcases hh with hh | hh
  · exact ⟨t', Or.inl ((mem_chordsOf_iff l i t').mpr ⟨l[i], hh⟩)⟩
  · exact ⟨t', Or.inr ((mem_chordsOf_iff l t' i).mpr ⟨l[i], hh⟩)⟩

/-! ## Walk lemmas -/

theorem edges_getElem_opt {V : Type u} {Ξ : SimpleGraph V} :
    ∀ {a b : V} (γ : Ξ.Walk a b) (i : ℕ), i < γ.length →
      γ.edges[i]? = some (Sym2.mk (γ.getVert i) (γ.getVert (i + 1)))
  | _, _, .nil, i, h => by simp at h
  | _, _, .cons hab γ', 0, _ => by
      rw [SimpleGraph.Walk.edges_cons, List.getElem?_cons_zero]
      simp only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
  | _, _, .cons hab γ', i + 1, h => by
      rw [SimpleGraph.Walk.edges_cons, List.getElem?_cons_succ]
      simp only [SimpleGraph.Walk.getVert_cons_succ]
      exact edges_getElem_opt γ' i (by simpa using h)

theorem edges_getElem {V : Type u} {Ξ : SimpleGraph V} {a b : V} (γ : Ξ.Walk a b) (i : ℕ)
    (h : i < γ.length) :
    γ.edges[i]'(by rwa [SimpleGraph.Walk.length_edges]) =
      Sym2.mk (γ.getVert i) (γ.getVert (i + 1)) := by
  have h1 := edges_getElem_opt γ i h
  have h2 : γ.edges[i]? = some (γ.edges[i]'(by rwa [SimpleGraph.Walk.length_edges])) :=
    List.getElem?_eq_getElem (by rwa [SimpleGraph.Walk.length_edges])
  rw [h2] at h1
  exact Option.some.inj h1

/-! ## List helpers -/

theorem take_one_eq_getElem_zero {β : Type u} (l : List β) (h : 0 < l.length) :
    l.take 1 = [l[0]] := by
  have hlt : (l.take 1).length = 1 := by rw [List.length_take]; omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlt
  have hx0 : x = l[0] := by
    have h1 : (l.take 1)[0] = l[0] := List.getElem_take (xs := l) (j := 1) (i := 0)
    simpa [hx] using h1
  rw [hx, hx0]

theorem drop_len_sub_one_eq_getElem {β : Type u} (l : List β) (h : 0 < l.length) :
    l.drop (l.length - 1) = [l[l.length - 1]] := by
  rw [List.drop_eq_getElem_cons (show l.length - 1 < l.length by omega)]
  congr 1
  rw [show l.length - 1 + 1 = l.length by omega, List.drop_length]

theorem count_eq_zero_of_getElem_ne {β : Type u} [DecidableEq β] {l : List β} {a : β}
    (h : ∀ j (hj : j < l.length), l[j] ≠ a) : l.count a = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
  exact h j hj hje

/-! ## The structure of a walk with no intermediate return to its base point -/

theorem excursion_structure {V : Type u} [DecidableEq V] {Ξ : SimpleGraph V} (hΞ : Ξ.IsAcyclic)
    {a : V} (γ : Ξ.Walk a a) (h2 : 2 ≤ γ.length)
    (hni : ∀ i, 0 < i → i < γ.length → γ.getVert i ≠ a) :
    γ.getVert (γ.length - 1) = γ.getVert 1 ∧
    γ.edges = Sym2.mk a (γ.getVert 1) ::
      (((γ.drop 1).take (γ.length - 2)).edges ++ [Sym2.mk a (γ.getVert 1)]) ∧
    Sym2.mk a (γ.getVert 1) ∉ ((γ.drop 1).take (γ.length - 2)).edges := by
  have hlen : γ.edges.length = γ.length := SimpleGraph.Walk.length_edges γ
  have hn2 : 2 ≤ γ.length := h2
  have hge0 : γ.edges[0] = Sym2.mk a (γ.getVert 1) := by
    rw [edges_getElem γ 0 (by omega), SimpleGraph.Walk.getVert_zero]
  have hLl : ((γ.edges.drop 1).take (γ.length - 2)).length = γ.length - 2 := by
    rw [List.length_take, List.length_drop, hlen,
      Nat.min_eq_left (show γ.length - 2 ≤ γ.length - 1 by omega)]
  have hmid_ne : ∀ j (hj : j < ((γ.edges.drop 1).take (γ.length - 2)).length),
      ((γ.edges.drop 1).take (γ.length - 2))[j] ≠ Sym2.mk a (γ.getVert 1) := by
    intro j hj hcontra
    rw [List.getElem_take (xs := γ.edges.drop 1)] at hcontra
    rw [List.getElem_drop] at hcontra
    have hj' : 1 + j < γ.length := by omega
    have hge := edges_getElem γ (1 + j) hj'
    rw [hge, Sym2.eq_iff] at hcontra
    rcases hcontra with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hni (1 + j) (by omega) (by omega) h1
    · exact hni (1 + j + 1) (by omega) (by omega) h2
  have hmid_zero : ((γ.edges.drop 1).take (γ.length - 2)).count (Sym2.mk a (γ.getVert 1)) = 0 :=
    count_eq_zero_of_getElem_ne (fun j hj => hmid_ne j hj)
  have hcnt1 : (γ.edges.take (γ.length - 1)).count (Sym2.mk a (γ.getVert 1)) = 1 := by
    have htake : γ.edges.take (γ.length - 1) =
        γ.edges.take 1 ++ (γ.edges.drop 1).take (γ.length - 2) := by
      rw [show γ.length - 1 = 1 + (γ.length - 2) by omega, List.take_add]
    rw [htake, List.count_append, hmid_zero, Nat.add_zero]
    have h1 : γ.edges.take 1 = [Sym2.mk a (γ.getVert 1)] := by
      rw [take_one_eq_getElem_zero γ.edges (by rw [hlen]; omega), hge0]
    rw [h1]; simp
  have hdrop_eq : γ.edges.drop (γ.length - 1) = [γ.edges[γ.length - 1]] := by
    have h := drop_len_sub_one_eq_getElem γ.edges (by rw [hlen]; omega)
    simp only [hlen] at h
    exact h
  have hlast_occ : γ.edges[γ.length - 1] = Sym2.mk a (γ.getVert 1) := by
    by_contra hne
    have hcnt_total : γ.edges.count (Sym2.mk a (γ.getVert 1)) =
        1 + (γ.edges.drop (γ.length - 1)).count (Sym2.mk a (γ.getVert 1)) := by
      conv_lhs => rw [← List.take_append_drop (γ.length - 1) γ.edges]
      rw [List.count_append, hcnt1]
    have hzero : (γ.edges.drop (γ.length - 1)).count (Sym2.mk a (γ.getVert 1)) = 0 := by
      rw [hdrop_eq]; simp [hne]
    rw [hzero, Nat.add_zero] at hcnt_total
    have hev := Tracks.even_edges_count Ξ hΞ γ (Sym2.mk a (γ.getVert 1))
    rw [hcnt_total] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- last vertex equals first
    have hge := edges_getElem γ (γ.length - 1) (by omega)
    rw [hlast_occ, show γ.length - 1 + 1 = γ.length by omega, SimpleGraph.Walk.getVert_length,
      Sym2.eq_iff] at hge
    rcases hge with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1.symm (hni (γ.length - 1) (by omega) (by omega))
    · exact h2.symm
  · -- the edge list
    have hDmem : ((γ.drop 1).take (γ.length - 2)).edges = (γ.edges.drop 1).take (γ.length - 2) := by
      rw [SimpleGraph.Walk.edges_take, SimpleGraph.Walk.edges_drop]
    have h1 : γ.edges = γ.edges.take 1 ++ γ.edges.drop 1 :=
      (List.take_append_drop 1 γ.edges).symm
    have h2a : (γ.edges.drop 1).drop (γ.length - 2) = γ.edges.drop (γ.length - 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    have h2 : γ.edges.drop 1 =
        (γ.edges.drop 1).take (γ.length - 2) ++ γ.edges.drop (γ.length - 1) := by
      rw [← h2a, List.take_append_drop]
    have h3 : γ.edges.take 1 = [Sym2.mk a (γ.getVert 1)] := by
      rw [take_one_eq_getElem_zero γ.edges (by rw [hlen]; omega), hge0]
    have h4 : γ.edges.drop (γ.length - 1) = [Sym2.mk a (γ.getVert 1)] := by
      rw [hdrop_eq, hlast_occ]
    rw [h1, h2, h3, h4, hDmem]
    simp
  · -- the middle edges avoid the end edge
    rw [show ((γ.drop 1).take (γ.length - 2)).edges = (γ.edges.drop 1).take (γ.length - 2) from
      (by rw [SimpleGraph.Walk.edges_take, SimpleGraph.Walk.edges_drop])]
    rw [← List.count_eq_zero]
    exact hmid_zero

/-- The induction step: a closed walk of length `n` in a forest has a nested chord matching. -/
theorem chordsOf_nested_aux : ∀ n : ℕ, ∀ {V : Type u} [DecidableEq V] {Ξ : SimpleGraph V},
    Ξ.IsAcyclic → ∀ {a : V} (γ : Ξ.Walk a a), γ.length = n →
    ∀ {p q : ℕ}, (p, q) ∈ chordsOf γ.edges → p < q →
    ∀ {t : ℕ}, p < t → t < q → ∃ t', p < t' ∧ t' < q ∧ IsChordOf γ.edges t t' := by
  intro n
  refine Nat.strongRecOn (motive := fun k => ∀ {V : Type u} [DecidableEq V] {Ξ : SimpleGraph V},
      Ξ.IsAcyclic → ∀ {a : V} (γ : Ξ.Walk a a), γ.length = k →
      ∀ {p q : ℕ}, (p, q) ∈ chordsOf γ.edges → p < q →
      ∀ {t : ℕ}, p < t → t < q → ∃ t', p < t' ∧ t' < q ∧ IsChordOf γ.edges t t') n ?_
  intro n ih V inst Ξ hΞ a γ hn p q h hpq t hpt htq
  have hqn : q < n := by
    have hh := mem_chordsOf_snd h
    rwa [SimpleGraph.Walk.length_edges, hn] at hh
  by_cases h2 : 2 ≤ n
  · by_cases hret : ∃ i, 0 < i ∧ i < n ∧ γ.getVert i = a
    · -- there is an intermediate return: split the walk
      obtain ⟨s, hs0, hsn, hsa⟩ := hret
      have hAtake : (γ.take s).edges.length = s := by
        rw [SimpleGraph.Walk.length_edges, SimpleGraph.Walk.take_length]
        exact Nat.min_eq_left (by omega)
      have hTakeLen : (γ.take s).length = s := by
        rw [← SimpleGraph.Walk.length_edges, hAtake]
      have hsplit : γ.edges = (γ.take s).edges ++ (γ.drop s).edges := by
        rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.append_take_drop_eq]
      have hAeven : ∀ e, Even ((γ.take s).edges.count e) := by
        intro e
        have hc := Tracks.even_edges_count Ξ hΞ ((γ.take s).copy rfl hsa) e
        rwa [SimpleGraph.Walk.edges_copy] at hc
      have hlift : ∀ {x y : ℕ}, (x, y) ∈ chordsOf ((γ.drop s).edges) →
          ((x + s), (y + s)) ∈ chordsOf ((γ.take s).edges ++ (γ.drop s).edges) := by
        intro x y hxy
        refine (mem_chordsOf_append _ _ hAeven (x + s) (y + s)).mpr (Or.inr ⟨x, y, ?_, ?_, hxy⟩)
        · rw [hAtake]
        · rw [hAtake]
      rcases (mem_chordsOf_append (γ.take s).edges (γ.drop s).edges hAeven p q).mp
        (hsplit ▸ h) with hch | ⟨i, j, hp, hq, hc⟩
      · obtain ⟨t', ht1, ht2, hch2⟩ :=
          ih s hsn hΞ ((γ.take s).copy rfl hsa)
            (by rw [SimpleGraph.Walk.length_copy, hTakeLen])
            (by rwa [SimpleGraph.Walk.edges_copy]) hpq hpt htq
        refine ⟨t', ht1, ht2, ?_⟩
        have hch3 : IsChordOf ((γ.take s).edges) t t' := by
          rwa [SimpleGraph.Walk.edges_copy] at hch2
        rcases hch3 with hh | hh
        · rw [hsplit]
          exact Or.inl ((mem_chordsOf_append _ _ hAeven t t').mpr (Or.inl hh))
        · rw [hsplit]
          exact Or.inr ((mem_chordsOf_append _ _ hAeven t' t).mpr (Or.inl hh))
      · have hlt_drop : ((γ.drop s).copy hsa rfl).length < n := by
          rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length, hn]; omega
        have hc' : (i, j) ∈ chordsOf ((γ.drop s).copy hsa rfl).edges := by
          rwa [SimpleGraph.Walk.edges_copy]
        have hp' : p = i + s := by rw [hp, hAtake]
        have hq' : q = j + s := by rw [hq, hAtake]
        have hit : i < t - s := by omega
        have htj : t - s < j := by omega
        have hij : i < j := by omega
        obtain ⟨t'', ht1, ht2, hch2⟩ :=
          ih (n - s) (by omega)
            hΞ ((γ.drop s).copy hsa rfl)
            (by rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length, hn])
            hc' hij hit htj
        refine ⟨t'' + s, by omega, by omega, ?_⟩
        have hch3 : IsChordOf ((γ.drop s).edges) (t - s) t'' := by
          rwa [SimpleGraph.Walk.edges_copy] at hch2
        rcases hch3 with hh | hh
        · rw [hsplit]
          refine Or.inl ?_
          have := hlift hh
          rwa [show t - s + s = t by omega] at this
        · rw [hsplit]
          refine Or.inr ?_
          have := hlift hh
          rwa [show t - s + s = t by omega] at this
    · -- no intermediate return: the walk is a single excursion
      have hni : ∀ i, 0 < i → i < γ.length → γ.getVert i ≠ a := by
        intro i hi0 hin hia
        exact hret ⟨i, hi0, by rwa [hn] at hin, hia⟩
      obtain ⟨hlast, hE, hDne⟩ := excursion_structure hΞ γ (by rw [hn]; exact h2) hni
      set D : List (Sym2 V) := ((γ.drop 1).take (γ.length - 2)).edges with hD
      set e0 : Sym2 V := Sym2.mk a (γ.getVert 1) with he0
      have hE' : γ.edges = e0 :: (D ++ [e0]) := by
        simpa only [← he0, ← hD] using hE
      have hDne' : e0 ∉ D := by
        simpa only [← he0, ← hD] using hDne
      have h1v : (γ.drop 1).getVert 0 = γ.getVert 1 := by
        rw [SimpleGraph.Walk.drop_getVert]
      have h2v : (γ.drop 1).getVert (γ.length - 2) = γ.getVert 1 := by
        rw [SimpleGraph.Walk.drop_getVert,
          show 1 + (γ.length - 2) = γ.length - 1 by omega, hlast]
      have hDeven : ∀ f, Even (D.count f) := by
        intro f
        have hc := Tracks.even_edges_count Ξ hΞ (((γ.drop 1).take (γ.length - 2)).copy rfl h2v) f
        rw [SimpleGraph.Walk.edges_copy, ← hD] at hc
        exact hc
      have hδlen : ((γ.drop 1).take (γ.length - 2)).length = γ.length - 2 := by
        rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
          Nat.min_eq_left (show γ.length - 2 ≤ γ.length - 1 by omega)]
      rcases (mem_chordsOf_bracket e0 D hDne' p q).mp (hE' ▸ h) with hpq_eq | ⟨i, j, hp, hq, hc⟩
      · have hp0 : p = 0 := congrArg Prod.fst hpq_eq
        have hq0 : q = D.length + 1 := congrArg Prod.snd hpq_eq
        obtain ⟨j', hj'⟩ := chordsOf_complete D hDeven (t - 1) (by omega)
        have hj'lt : j' < D.length := by
          rcases hj' with hh | hh
          · exact mem_chordsOf_snd hh
          · exact mem_chordsOf_lt hh
        refine ⟨j' + 1, by omega, by omega, ?_⟩
        rcases hj' with hh | hh
        · refine Or.inl ?_
          rw [hE']
          exact (mem_chordsOf_bracket e0 D hDne' t (j' + 1)).mpr
            (Or.inr ⟨t - 1, j', by omega, rfl, hh⟩)
        · refine Or.inr ?_
          rw [hE']
          exact (mem_chordsOf_bracket e0 D hDne' (j' + 1) t).mpr
            (Or.inr ⟨j', t - 1, rfl, by omega, hh⟩)
      · have hij : i < j := by omega
        have hEdges : (((γ.drop 1).take (γ.length - 2)).copy rfl h2v).edges = D := by
          rw [SimpleGraph.Walk.edges_copy, ← hD]
        have hc' : (i, j) ∈ chordsOf (((γ.drop 1).take (γ.length - 2)).copy rfl h2v).edges := by
          rwa [hEdges]
        have hit : i < t - 1 := by omega
        have htj : t - 1 < j := by omega
        obtain ⟨t'', ht1, ht2, hch2⟩ :=
          ih (γ.length - 2) (by omega) hΞ (((γ.drop 1).take (γ.length - 2)).copy rfl h2v)
            (by rw [SimpleGraph.Walk.length_copy, hδlen]) hc' hij hit htj
        refine ⟨t'' + 1, by omega, by omega, ?_⟩
        have hch3 : IsChordOf D (t - 1) t'' := by
          rwa [hEdges] at hch2
        rcases hch3 with hh | hh
        · refine Or.inl ?_
          rw [hE']
          exact (mem_chordsOf_bracket e0 D hDne' t (t'' + 1)).mpr
            (Or.inr ⟨t - 1, t'', by omega, rfl, hh⟩)
        · refine Or.inr ?_
          rw [hE']
          exact (mem_chordsOf_bracket e0 D hDne' (t'' + 1) t).mpr
            (Or.inr ⟨t'', t - 1, rfl, by omega, hh⟩)
  · -- length at most one
    exact absurd hqn (by omega)

theorem chordsOf_nested {V : Type u} [DecidableEq V] {Ξ : SimpleGraph V} (hΞ : Ξ.IsAcyclic)
    {a : V} (γ : Ξ.Walk a a) {p q : ℕ} (h : (p, q) ∈ Work.ORDunwoody.Chords.chordsOf γ.edges)
    (hpq : p < q) {t : ℕ} (hpt : p < t) (htq : t < q) :
    ∃ t', p < t' ∧ t' < q ∧ Work.ORDunwoody.Chords.IsChordOf γ.edges t t' :=
  chordsOf_nested_aux γ.length hΞ γ rfl h hpq hpt htq

end Work.ORDunwoody.Chords
