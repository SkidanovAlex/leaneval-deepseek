import Mathlib

namespace Work.LT

/-- Well-founded descent on `ℕ`: if from every `P`-point that is not `Q` one can
strictly decrease `f : X → ℕ` while staying in `P`, then some `P`-point must be `Q`. -/
lemma exists_of_no_descent {X : Type*} (f : X → ℕ) (P Q : X → Prop) (x0 : X) (h0 : P x0)
    (hstep : ∀ x, P x → ¬ Q x → ∃ y, P y ∧ f y < f x) : ∃ x, P x ∧ Q x := by
  by_contra h
  -- `h : ¬ ∃ x, P x ∧ Q x`, i.e. every `P`-point fails `Q`.
  have key : ∀ n, ∀ x, f x = n → ¬ P x := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih x hx hPx
    obtain ⟨y, hPy, hyx⟩ := hstep x hPx (fun hQx => h ⟨x, hPx, hQx⟩)
    exact ih (f y) (hx ▸ hyx) y rfl hPy
  exact key (f x0) x0 rfl h0

end Work.LT
