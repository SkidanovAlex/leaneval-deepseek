import Mathlib
import Submission.Work.ORDunwoody.ChordWalk.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.ChordWalk

open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## Bookkeeping for `positionsOfLabelAux` -/

theorem cwc_aux_positionsOfLabelAux_nil (e : Sym2 V) (k : ℕ) :
    positionsOfLabelAux ([] : List (MidV D)) e k = [] := rfl

theorem cwc_aux_positionsOfLabelAux_cons (a : MidV D) (rest : List (MidV D)) (e : Sym2 V)
    (k : ℕ) :
    positionsOfLabelAux (a :: rest) e k =
      (if a.label = e then [k] else []) ++ positionsOfLabelAux rest e (k + 1) := rfl

theorem cwc_aux_positionsOfLabelAux_bounds {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (h : j ∈ positionsOfLabelAux l e k) : k ≤ j ∧ j < k + l.length := by
  induction l generalizing k j with
  | nil =>
    rw [cwc_aux_positionsOfLabelAux_nil] at h
    exact absurd h (List.not_mem_nil)
  | cons a rest ih =>
    rw [cwc_aux_positionsOfLabelAux_cons] at h
    simp only [List.length_cons]
    by_cases he : a.label = e
    · rw [if_pos he, List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_singleton] at h
        subst h
        omega
      · obtain ⟨h1, h2⟩ := ih h
        omega
    · rw [if_neg he, List.nil_append] at h
      obtain ⟨h1, h2⟩ := ih h
      omega

theorem cwc_aux_label_of_mem_positionsOfLabelAux {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (h : j ∈ positionsOfLabelAux l e k) :
    (l[j - k]?).map (MidV.label (D := D)) = some e := by
  induction l generalizing k j with
  | nil =>
    rw [cwc_aux_positionsOfLabelAux_nil] at h
    exact absurd h (List.not_mem_nil)
  | cons a rest ih =>
    rw [cwc_aux_positionsOfLabelAux_cons] at h
    by_cases he : a.label = e
    · rw [if_pos he, List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_singleton] at h
        subst h
        simp [he]
      · have hle := (cwc_aux_positionsOfLabelAux_bounds h).1
        have hsub : j - k = (j - (k + 1)) + 1 := by omega
        rw [hsub, List.getElem?_cons_succ]
        exact ih h
    · rw [if_neg he, List.nil_append] at h
      have hle := (cwc_aux_positionsOfLabelAux_bounds h).1
      have hsub : j - k = (j - (k + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ]
      exact ih h

theorem cwc_aux_mem_positionsOfLabelAux_of_label {l : List (MidV D)} {e : Sym2 V} {k j : ℕ}
    (hk : k ≤ j) (hj : j < k + l.length)
    (hlabel : (l[j - k]?).map (MidV.label (D := D)) = some e) :
    j ∈ positionsOfLabelAux l e k := by
  induction l generalizing k j with
  | nil =>
    rw [cwc_aux_positionsOfLabelAux_nil]
    simp only [List.length_nil, add_zero] at hj
    have hjk : j = k := by omega
    rw [hjk, Nat.sub_self] at hlabel
    simp at hlabel
  | cons a rest ih =>
    rw [cwc_aux_positionsOfLabelAux_cons]
    simp only [List.length_cons] at hj
    rcases lt_or_ge k j with hlt | hge
    · have hsub : j - k = (j - (k + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ] at hlabel
      have hj' : j < k + 1 + rest.length := by omega
      have hk' : k + 1 ≤ j := by omega
      exact List.mem_append_right _ (ih hk' hj' hlabel)
    · have hjk : j = k := by omega
      have h0 : j - k = 0 := by omega
      rw [h0, List.getElem?_cons_zero, Option.map_some] at hlabel
      have he : a.label = e := Option.some.inj hlabel
      rw [if_pos he]
      exact List.mem_append_left _ (List.mem_singleton.mpr hjk)

/-! ## The main statement -/

theorem cwc_mem_positionsOfLabel_iff {G : Type _} {V : Type _} [Group G] [MulAction G V] [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} {l : List (Work.ORDunwoody.Dunwoody.MidV D)} {e : Sym2 V} {j : ℕ} : j ∈ Work.ORDunwoody.Dunwoody.positionsOfLabel l e ↔ j < l.length ∧ (l[j]?).map (Work.ORDunwoody.Dunwoody.MidV.label (D := D)) = some e := by
  constructor
  · intro h
    have h1 := (cwc_aux_positionsOfLabelAux_bounds h).2
    have h2 := cwc_aux_label_of_mem_positionsOfLabelAux h
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨hj, hlabel⟩
    exact cwc_aux_mem_positionsOfLabelAux_of_label (k := 0) (by omega) (by simpa using hj)
      (by simpa using hlabel)

end Work.ORDunwoody.ChordWalk
