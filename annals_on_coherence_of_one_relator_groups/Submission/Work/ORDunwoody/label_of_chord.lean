/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Two pattern points joined by a chord have the same label

`Dunwoody/Chord.lean` pairs, inside every fibre of the visits of a face (i.e. among the visits
with a common label `Sym2 V`), the 1st visit with the 2nd, the 3rd with the 4th, and so on.  The
resulting pairs are the *chords* of the face.  This file proves the basic consequence used to
define the *tracks* (`Dunwoody/Track.lean`): the two endpoints of a chord have the same label.

The work is elementary but the definitions are stated with an *offset* (`positionsOfLabelAux l e k`
records the positions at which `l` has the label `e`, shifted by `k`, so that the tail of a
cons-list can be processed without re-indexing), so the proof needs the two bookkeeping facts

* `positionsOfLabelAux_le` — every position produced with offset `k` is `≥ k`;
* `label_of_mem_positionsOfLabelAux` — a position produced with offset `k` is the index `j - k` of
  a visit whose label is `e`.

Since `chords` is a `flatMap` of `pairUp` over the fibres, `pairUp_mem` extracts the fibre from a
membership in a chord list.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

namespace Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- The two entries of a pair produced by `pairUp` are entries of the original list. -/
private theorem pairUp_mem : ∀ (L : List ℕ) (p q : ℕ), (p, q) ∈ pairUp L → p ∈ L ∧ q ∈ L
  | [], _, _, h => by simp at h
  | [x], _, _, h => by simp at h
  | x :: y :: rest, p, q, h => by
      rw [pairUp_cons_cons] at h
      rcases List.mem_cons.mp h with h | h
      · rw [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, by simp⟩
      · obtain ⟨hp, hq⟩ := pairUp_mem rest p q h
        exact ⟨by simp [hp], by simp [hq]⟩

/-- Every position recorded by `positionsOfLabelAux` with offset `k` is at least `k`. -/
private lemma positionsOfLabelAux_le {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (h : j ∈ positionsOfLabelAux l e k) : k ≤ j := by
  induction l generalizing k j with
  | nil => simp only [positionsOfLabelAux, List.not_mem_nil] at h
  | cons a rest ih =>
    simp only [positionsOfLabelAux] at h
    by_cases he : a.label = e
    · rw [if_pos he] at h
      rcases List.mem_append.mp h with h1 | h2
      · have hjk : j = k := by simpa using h1
        omega
      · exact le_trans (Nat.le_succ k) (ih h2)
    · rw [if_neg he] at h
      simp only [List.nil_append] at h
      exact le_trans (Nat.le_succ k) (ih h)

/-- A position recorded by `positionsOfLabelAux l e k` is the index `j - k` of a visit whose label
is `e`. -/
private lemma label_of_mem_positionsOfLabelAux {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (h : j ∈ positionsOfLabelAux l e k) {m : MidV D} (hm : l[j - k]? = some m) :
    m.label = e := by
  induction l generalizing k j with
  | nil => simp only [positionsOfLabelAux, List.not_mem_nil] at h
  | cons a rest ih =>
    have tail : ∀ (j : ℕ), j ∈ positionsOfLabelAux rest e (k + 1) →
        (a :: rest)[j - k]? = some m → m.label = e := by
      intro j h2 hm
      have hle : k + 1 ≤ j := positionsOfLabelAux_le h2
      have hsub : j - k = (j - (k + 1)) + 1 := by omega
      have hsplit : (a :: rest)[j - k]? = rest[j - (k + 1)]? := by
        rw [hsub, List.getElem?_cons_succ]
      rw [hsplit] at hm
      exact ih h2 hm
    simp only [positionsOfLabelAux] at h
    by_cases he : a.label = e
    · rw [if_pos he] at h
      rcases List.mem_append.mp h with h1 | h2
      · have hjk : j = k := by simpa using h1
        have hm0 : (a :: rest)[j - k]? = some a := by rw [hjk, Nat.sub_self]; rfl
        rw [hm0] at hm
        have ham : a = m := Option.some.inj hm
        rw [← ham]
        exact he
      · exact tail j h2 hm
    · rw [if_neg he] at h
      simp only [List.nil_append] at h
      exact tail j h hm

end Dunwoody

open Work.ORDunwoody.Dunwoody

theorem label_of_chord {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} {l : List (Work.ORDunwoody.Dunwoody.MidV D)}
    {p q : ℕ} (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords l)
    {m m' : Work.ORDunwoody.Dunwoody.MidV D} (hm : l[p]? = some m) (hm' : l[q]? = some m') :
    m.label = m'.label := by
  rw [Dunwoody.chords] at h
  rcases List.mem_flatMap.mp h with ⟨e, -, hpq⟩
  obtain ⟨hp, hq⟩ := Dunwoody.pairUp_mem _ p q hpq
  have hm1 : m.label = e := Dunwoody.label_of_mem_positionsOfLabelAux hp (by simpa using hm)
  have hm2 : m'.label = e := Dunwoody.label_of_mem_positionsOfLabelAux hq (by simpa using hm')
  rw [hm1, hm2]

end Work.ORDunwoody
