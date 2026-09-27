import Mathlib
import Submission.Work.EKLC6Route.L7Aux

namespace Work.EKLC6Route

open scoped ENNReal

/-- Reindexing an `ℝ≥0∞`-valued sum along an injection, when the summand vanishes off the range
of the injection. -/
theorem tsum_eq_tsum_of_support {α β : Type*} (e : α → β) (he : Function.Injective e)
    (f : β → ℝ≥0∞) (hf : ∀ b, b ∉ Set.range e → f b = 0) :
    (∑' b : β, f b) = ∑' a : α, f (e a) := by
  have h1 : (∑' b : β, f b) = ∑' b : Set.range e, f (b : β) := by
    rw [tsum_subtype (Set.range e) f]
    refine tsum_congr fun b => ?_
    by_cases hb : b ∈ Set.range e
    · rw [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hb, hf b hb]
  have h2 : (∑' b : Set.range e, f (b : β)) = ∑' a : α, f (e a) := by
    rw [← Equiv.tsum_eq (Equiv.ofInjective e he) (fun b : Set.range e => f (b : β))]
    exact tsum_congr fun a => rfl
  exact h1.trans h2

theorem tsum_S_eq_tsum_piece {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) (g : Set Work.EKLContract.X3 → ENNReal) (hg : g ∅ = 0) :
    (∑' n : ℕ, g (w.S n)) = ∑' p : Work.EKLC6Route.Window.PIdx, g (w.piece p) := by
  have hf : ∀ n : ℕ, n ∉ Set.range encw → g (w.S n) = 0 := by
    intro n hn
    have hS : w.S n = ∅ := by
      rw [S_eq_match w n]
      cases h : decw n with
      | none => rfl
      | some p => exact absurd ⟨p, decw_eq_some.mp h⟩ hn
    rw [hS, hg]
  rw [tsum_eq_tsum_of_support encw encw_injective (fun n => g (w.S n)) hf]
  refine tsum_congr fun p => ?_
  rw [S_eq_match w (encw p), decw_encw]

end Work.EKLC6Route
