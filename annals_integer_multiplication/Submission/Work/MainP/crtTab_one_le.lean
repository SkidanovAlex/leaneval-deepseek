import Mathlib
import Submission.Work.MainP.crtDefs

namespace Work.MainP

/-- A product of a list all of whose entries are `≥ 1` is `≥ 1`. -/
theorem one_le_prod_of_forall_one_le {ss : List ℕ} (h : ∀ s ∈ ss, 1 ≤ s) : 1 ≤ ss.prod := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      rw [List.prod_cons]
      exact one_le_mul (h s (by simp)) (ih fun t ht => h t (by simp [ht]))

theorem crtTab_one_le (ss : List ℕ) (hpos : ∀ s ∈ ss, 1 ≤ s) :
    ∀ sp ∈ Work.MainP.crtTab ss, 1 ≤ sp.1 ∧ 1 ≤ sp.2 := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      intro sp hsp
      rw [crtTab_cons, List.mem_cons] at hsp
      rcases hsp with rfl | hsp
      · exact ⟨hpos s (by simp), one_le_prod_of_forall_one_le fun t ht => hpos t (by simp [ht])⟩
      · exact ih (fun t ht => hpos t (by simp [ht])) sp hsp

end Work.MainP
