import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite

namespace Work.WilLibTS.TS.PolynomialSignSet

lemma forall_finset {X ι α : Type*} {c : X → ι → ℝ} (s : Finset α) (P : α → X → Prop)
    (hP : ∀ a ∈ s, Work.WilLibTS.TS.PolynomialSignSet c {x | P a x}) :
    Work.WilLibTS.TS.PolynomialSignSet c {x | ∀ a ∈ s, P a x} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (Work.WilLibTS.TS.PolynomialSignSet.univ (c := c))
  | @insert a s ha ih =>
    have he : {x | ∀ b ∈ insert a s, P b x}
        = {x | P a x} ∩ {x | ∀ b ∈ s, P b x} := by
      ext x
      constructor
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
      · rintro ⟨ha', hrest⟩ b hb
        rcases Finset.mem_insert.mp hb with rfl | hbs
        · exact ha'
        · exact hrest b hbs
    rw [he]
    exact (hP a (Finset.mem_insert_self a s)).inter
      (ih (fun b hb => hP b (Finset.mem_insert_of_mem hb)))

end Work.WilLibTS.TS.PolynomialSignSet
