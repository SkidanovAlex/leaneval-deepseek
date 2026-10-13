import Mathlib
import Submission.Work.WilLibTS.TS.SemialgebraicOnAlgebra

namespace Work.WilLibTS.TS.SemialgebraicOn

lemma finset_sum {α ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)}
    (hB : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ) B)
    (s : Finset α) (f : α → (ι → ℝ) → (κ → ℝ))
    (hf : ∀ a ∈ s, Work.WilLibTS.TS.SemialgebraicOn B (f a)) :
    Work.WilLibTS.TS.SemialgebraicOn B (fun x => ∑ a ∈ s, f a x) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    exact (Work.WilLibTS.TS.SemialgebraicOn.constant (κ := κ) hB (0 : κ → ℝ)).congr
      (fun x _ => by simp)
  · intro a s ha ih hf
    have h1 : Work.WilLibTS.TS.SemialgebraicOn B (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : Work.WilLibTS.TS.SemialgebraicOn B (fun x => ∑ b ∈ s, f b x) :=
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    exact (h1.add h2).congr (fun x _ => by simp [Finset.sum_insert ha])

end Work.WilLibTS.TS.SemialgebraicOn
