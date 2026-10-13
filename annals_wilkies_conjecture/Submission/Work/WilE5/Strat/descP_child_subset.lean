import Mathlib
import Submission.Work.WilE5.Strat.DescP
import Submission.Work.WilE5.Strat.cover

namespace Work.WilE5.Strat

theorem descP_child_subset {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Ml : ℕ → ℕ)
    (NΦ : ℕ) (σ τ : Work.WilE5.St p q X.r)
    (h : τ ∈ Work.WilE5.childrenP X.c Ml NΦ σ) (k : ℕ) :
    ∀ ρ ∈ Work.WilE5.Strat.descP X Ml NΦ τ k, ρ ∈ Work.WilE5.Strat.descP X Ml NΦ σ (k + 1) := by
  induction k with
  | zero =>
    intro ρ hρ
    rw [descP_zero, List.mem_singleton] at hρ
    subst hρ
    rw [descP_succ, descP_zero, List.flatMap_singleton]
    exact h
  | succ k ih =>
    intro ρ hρ
    rw [descP_succ, List.mem_flatMap] at hρ
    obtain ⟨ρ', hρ', hρρ'⟩ := hρ
    rw [descP_succ, List.mem_flatMap]
    exact ⟨ρ', ih ρ' hρ', hρρ'⟩

end Work.WilE5.Strat
