import Mathlib
import Submission.Work.Peluse.SwapC.concatCore

namespace Work.Peluse.SwapC

/-- The zero element of `Fin s → Bool` is the constant `false` function: a sign pattern all of
whose entries are `false` is the zero pattern. -/
lemma eq_zero_of_forall_apply_eq_false {s : ℕ} {ε : Fin s → Bool}
    (h : ∀ j, ε j = false) : ε = 0 := by
  funext j
  simp only [h j, Pi.zero_apply]
  exact Bool.zero_eq_false.symm

theorem cUBZeroCases (s : ℕ) (f : ℤ → ℂ) (dH0 dH1 : ℤ) :
    (cUB s f dH0 dH1 0 0 = fun z => star (f (z + dH0)) * f (z + dH1))
    ∧ (∀ ε : Fin s → Bool, ε ≠ 0 →
        cUB s f dH0 dH1 ε 0 = fun z => f z * star (f (z + dH0)))
    ∧ (∀ ε' : Fin s → Bool, ε' ≠ 0 →
        cUB s f dH0 dH1 0 ε' = fun z => star (f z) * f (z + dH1))
    ∧ (∀ ε ε' : Fin s → Bool, ε ≠ 0 → ε' ≠ 0 →
        cUB s f dH0 dH1 ε ε' = fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- both halves of the sign pattern vanish: the `ω = 0` corner
    unfold cUB
    split_ifs with h1 h2
    · rfl
    · exact absurd ⟨fun j => Bool.zero_eq_false, h2⟩ h1
    · exact absurd (fun j => Bool.zero_eq_false) h2
  · -- first half nontrivial, second half zero
    intro ε hε
    unfold cUB
    split_ifs with h1 h2 h3
    · exact absurd (eq_zero_of_forall_apply_eq_false h1.1) hε
    · rfl
    · exact absurd (eq_zero_of_forall_apply_eq_false h3) hε
    · exact absurd (fun j => Bool.zero_eq_false) h2
  · -- first half zero, second half nontrivial
    intro ε' hε
    unfold cUB
    split_ifs with h1 h2 h3
    · exact absurd (eq_zero_of_forall_apply_eq_false h1.2) hε
    · exact absurd (eq_zero_of_forall_apply_eq_false h2) hε
    · rfl
    · exact absurd (fun j => Bool.zero_eq_false) h3
  · -- both halves nontrivial: the constant corner
    intro ε ε' hε hε'
    unfold cUB
    split_ifs with h1 h2 h3
    · exact absurd (eq_zero_of_forall_apply_eq_false h1.1) hε
    · exact absurd (eq_zero_of_forall_apply_eq_false h2) hε'
    · exact absurd (eq_zero_of_forall_apply_eq_false h3) hε
    · rfl

end Work.Peluse.SwapC
