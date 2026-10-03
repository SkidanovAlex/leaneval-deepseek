import Mathlib

namespace Work.Parab.coordData

theorem iterate_sub_translate_bound {g : ℂ → ℂ} {N K : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hstep : ∀ v : ℂ, N < ‖v‖ → ‖g v - (v + 1)‖ ≤ K / ‖v‖) (ζ : ℂ) :
    ∀ j : ℕ, (∀ i < j, N < ‖(g^[i]) ζ‖) →
      ‖(g^[j]) ζ - ζ - (j : ℂ)‖ ≤ ∑ i ∈ Finset.range j, K / ‖(g^[i]) ζ‖ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have hprev : ∀ i < j, N < ‖(g^[i]) ζ‖ := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hjN : N < ‖(g^[j]) ζ‖ := hj j (Nat.lt_succ_self j)
    have hstepj : ‖g ((g^[j]) ζ) - ((g^[j]) ζ + 1)‖ ≤ K / ‖(g^[j]) ζ‖ := hstep _ hjN
    have hih : ‖(g^[j]) ζ - ζ - (j : ℂ)‖ ≤ ∑ i ∈ Finset.range j, K / ‖(g^[i]) ζ‖ := ih hprev
    have hsplit : (g^[j+1]) ζ - ζ - ((j + 1 : ℕ) : ℂ)
        = (g ((g^[j]) ζ) - ((g^[j]) ζ + 1)) + ((g^[j]) ζ - ζ - (j : ℂ)) := by
      rw [Function.iterate_succ_apply']
      push_cast
      ring
    rw [hsplit]
    calc ‖(g ((g^[j]) ζ) - ((g^[j]) ζ + 1)) + ((g^[j]) ζ - ζ - (j : ℂ))‖
        ≤ ‖g ((g^[j]) ζ) - ((g^[j]) ζ + 1)‖ + ‖(g^[j]) ζ - ζ - (j : ℂ)‖ := norm_add_le _ _
      _ ≤ K / ‖(g^[j]) ζ‖ + ∑ i ∈ Finset.range j, K / ‖(g^[i]) ζ‖ := add_le_add hstepj hih
      _ = ∑ i ∈ Finset.range (j + 1), K / ‖(g^[i]) ζ‖ := by
            rw [Finset.sum_range_succ]
            exact add_comm (K / ‖(g^[j]) ζ‖) (∑ i ∈ Finset.range j, K / ‖(g^[i]) ζ‖)

end Work.Parab.coordData
