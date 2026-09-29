import Mathlib
import Submission.Work.Cert.WindDefs

namespace Work.Cert

/-- Concatenation lemma for `warcsOK`, stated for an arbitrary first list so that the induction
goes through: the chains of `L₁` and `L₂` glue at the junction given by `hpt`/`hj`. -/
theorem warcsOK_append_aux (L₁ : List WArc) :
    ∀ (L₂ : List WArc) (Fx Fy Gx Gy : Int),
    warcsOK Fx Fy L₁ = true → warcsOK Gx Gy L₂ = true → L₂ ≠ [] →
    (Fx, Fy) = (L₂.head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) →
    (L₁.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
      (L₂.head?.map (fun a : WArc => a.j)).getD 0 →
    warcsOK Gx Gy (L₁ ++ L₂) = true := by
  induction L₁ with
  | nil =>
    intro L₂ Fx Fy Gx Gy _ h₂ _ _ _
    simpa using h₂
  | cons a t ih =>
    intro L₂ Fx Fy Gx Gy h₁ h₂ hne hpt hj
    cases t with
    | nil =>
      cases L₂ with
      | nil => exact absurd rfl hne
      | cons b t₂ =>
        rw [List.getLast?_singleton, Option.map_some, Option.getD_some] at hj
        rw [List.head?_cons, Option.map_some, Option.getD_some] at hj hpt
        obtain ⟨rfl, rfl⟩ := hpt
        show warcsOK Gx Gy (a :: b :: t₂) = true
        rw [warcsOK]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h₁, hj⟩, h₂⟩
    | cons b rest =>
      have h₁' : warcsOK Fx Fy (b :: rest) = true := by
        have := h₁; rw [warcsOK] at this
        simp only [Bool.and_eq_true] at this
        exact this.2
      have ha : warcOK a b.Ex b.Ey = true := by
        have := h₁; rw [warcsOK] at this
        simp only [Bool.and_eq_true] at this
        exact this.1.1
      have hja : a.j + 1 = b.j := by
        have := h₁; rw [warcsOK] at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.2
      rw [List.getLast?_cons_cons] at hj
      have hrec := ih L₂ Fx Fy Gx Gy h₁' h₂ hne hpt hj
      show warcsOK Gx Gy (a :: b :: (rest ++ L₂)) = true
      rw [warcsOK]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨ha, hja⟩, hrec⟩

theorem warcsOK_append (L₁ L₂ : List WArc) (Fx Fy Gx Gy : Int)
    (h₁ : warcsOK Fx Fy L₁ = true) (h₂ : warcsOK Gx Gy L₂ = true) (hne : L₂ ≠ [])
    (hpt : (Fx, Fy) = (L₂.head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0))
    (hj : (L₁.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
      (L₂.head?.map (fun a : WArc => a.j)).getD 0) :
    warcsOK Gx Gy (L₁ ++ L₂) = true :=
  warcsOK_append_aux L₁ L₂ Fx Fy Gx Gy h₁ h₂ hne hpt hj

end Work.Cert
