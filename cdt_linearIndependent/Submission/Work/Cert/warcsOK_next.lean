import Mathlib
import Submission.Work.Cert.WindDefs

namespace Work.Cert

theorem warcsOK_next (L : List WArc) (Fx Fy : Int) (h : warcsOK Fx Fy L = true) :
    ∀ i : ℕ, ∀ hi : i < L.length,
      warcOK (L.get ⟨i, hi⟩)
        (if h' : i + 1 < L.length then (L.get ⟨i + 1, h'⟩).Ex else Fx)
        (if h' : i + 1 < L.length then (L.get ⟨i + 1, h'⟩).Ey else Fy) = true := by
  suffices key : ∀ L : List WArc, ∀ Fx Fy, warcsOK Fx Fy L = true →
      ∀ i : ℕ, ∀ hi : i < L.length,
        warcOK (L.get ⟨i, hi⟩)
          (if h' : i + 1 < L.length then (L.get ⟨i + 1, h'⟩).Ex else Fx)
          (if h' : i + 1 < L.length then (L.get ⟨i + 1, h'⟩).Ey else Fy) = true by
    exact key L Fx Fy h
  intro L
  induction L with
  | nil => intro Fx Fy h i hi; simp at hi
  | cons a t ih =>
    intro Fx Fy h
    cases t with
    | nil =>
      have h0 : warcOK a Fx Fy = true := by
        have := h; rw [warcsOK] at this; exact this
      intro i hi
      have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
      subst hi0
      simpa using h0
    | cons b rest =>
      have h1 : warcOK a b.Ex b.Ey = true := by
        have := h; rw [warcsOK] at this
        simp only [Bool.and_eq_true] at this
        exact this.1.1
      have h2 : warcsOK Fx Fy (b :: rest) = true := by
        have := h; rw [warcsOK] at this
        simp only [Bool.and_eq_true] at this
        exact this.2
      intro i hi
      cases i with
      | zero => simp [h1]
      | succ k =>
        have hk : k < (b :: rest).length := by simpa using hi
        simpa only [List.length_cons, List.get_cons_succ, Nat.add_lt_add_iff_right]
          using ih Fx Fy h2 k hk

end Work.Cert
