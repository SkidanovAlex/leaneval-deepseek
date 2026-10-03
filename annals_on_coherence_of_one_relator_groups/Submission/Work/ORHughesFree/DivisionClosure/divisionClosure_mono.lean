import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure

namespace Work.ORHughesFree.DivisionClosure

open Work.ORHughesFree

theorem divisionClosure_mono {S : Type*} [Ring S] {R T : Set S} (h : R ⊆ T) :
    (divisionClosure R : Set S) ⊆ (divisionClosure T : Set S) := by
  have hchain : ∀ n : ℕ, divisionClosureChain R n ≤ divisionClosureChain T n := by
    intro n
    induction n with
    | zero =>
      exact Subring.closure_mono h
    | succ n ih =>
      apply Subring.closure_mono
      intro x hx
      rcases hx with hx | ⟨z, hz, h1, h2⟩
      · exact Or.inl (ih hx)
      · exact Or.inr ⟨z, ih hz, h1, h2⟩
  have : divisionClosure R ≤ divisionClosure T :=
    iSup_le (fun n => le_trans (hchain n) (le_iSup (divisionClosureChain T) n))
  exact fun x hx => this hx

end Work.ORHughesFree.DivisionClosure
