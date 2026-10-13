import Mathlib
import Submission.Work.WilLibTS.TS.SemialgebraicOnAlgebra

namespace Work.WilLibTS.TS.SemialgebraicOn

lemma finset_prod {α ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)}
    (hB : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ) B)
    (s : Finset α) (f : α → (ι → ℝ) → (κ → ℝ))
    (hf : ∀ a ∈ s, Work.WilLibTS.TS.SemialgebraicOn B (f a)) :
    Work.WilLibTS.TS.SemialgebraicOn B (fun x => ∏ a ∈ s, f a x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine (SemialgebraicOn.constant hB (fun _ : κ => (1 : ℝ))).congr ?_
    intro x _
    funext i
    simp
  | @insert a s ha ih =>
    have hmul := (hf a (Finset.mem_insert_self a s)).mul
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    refine hmul.congr ?_
    intro x _
    funext i
    simp [Finset.prod_insert ha]

end Work.WilLibTS.TS.SemialgebraicOn
