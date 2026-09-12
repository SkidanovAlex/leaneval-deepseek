import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Commons.Analysis.Interval

theorem translate_filter_card {Q : ℤ → Prop} [DecidablePred Q] {c d s : ℤ} :
    (((Finset.Icc c d).filter (fun x : ℤ => Q (s + x))).card) =
      ((Finset.Icc (s + c) (s + d)).filter (fun y : ℤ => Q y)).card := by
  apply Finset.card_bij (fun x _ => s + x)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    rw [Finset.mem_Icc] at hx ⊢
    constructor
    · constructor <;> omega
    · exact hx.2
  · intro a _ b _ h
    omega
  · intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_Icc] at hy
    refine ⟨y - s, ?_, ?_⟩
    · rw [Finset.mem_filter]
      rw [Finset.mem_Icc]
      constructor
      · constructor <;> omega
      · have heq : s + (y - s) = y := by omega
        rw [heq]
        exact hy.2
    · omega

end Commons.Analysis.Interval