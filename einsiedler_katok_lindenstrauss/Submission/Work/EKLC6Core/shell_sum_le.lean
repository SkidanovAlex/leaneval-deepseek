import Mathlib

set_option linter.unusedVariables false

namespace Work.EKLC6Core

/-- Sum of the increments `f (U b) - f (L b)` over a family of pairwise disjoint
intervals `[L b, U b]`, all lying inside `[d, R]`, is at most `f R - f d` for a
monotone `f`. -/
theorem shell_sum_le {ι : Type*} (f : ℝ → ℝ) (hf : Monotone f) (hfnn : ∀ t : ℝ, 0 ≤ f t)
    (u : Finset ι) (L U : ι → ℝ) (d R : ℝ) (hdR : d ≤ R)
    (hLU : ∀ b ∈ u, L b < U b) (hdL : ∀ b ∈ u, d ≤ L b)
    (hdisj : ∀ b ∈ u, ∀ b' ∈ u, b ≠ b' → U b ≤ L b' ∨ U b' ≤ L b)
    (hUR : ∀ b ∈ u, U b ≤ R) :
    ∑ b ∈ u, (f (U b) - f (L b)) ≤ f R - f d := by
  classical
  -- Strong induction on the cardinality of `u`, peeling off a left-most interval.
  suffices key : ∀ n : ℕ, (∀ (u : Finset ι) (L U : ι → ℝ) (d R : ℝ), u.card = n →
      (∀ b ∈ u, L b < U b) → (∀ b ∈ u, d ≤ L b) →
      (∀ b ∈ u, ∀ b' ∈ u, b ≠ b' → U b ≤ L b' ∨ U b' ≤ L b) →
      (∀ b ∈ u, U b ≤ R) → d ≤ R →
      ∑ b ∈ u, (f (U b) - f (L b)) ≤ f R - f d) by
    exact key u.card u L U d R rfl hLU hdL hdisj hUR hdR
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u L U d R hcard hLU hdL hdisj hUR hdR
    rcases u.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.sum_empty]
      exact sub_nonneg.mpr (hf hdR)
    · -- pick an element `b0` whose left endpoint is minimal
      obtain ⟨b0, hb0, hmin⟩ := Finset.exists_min_image u L hne
      have hpos : 0 < n := hcard ▸ hne.card_pos
      have hcardS : (u.erase b0).card < n := by
        rw [Finset.card_erase_of_mem hb0, hcard]
        omega
      have hLU' : ∀ b ∈ u.erase b0, L b < U b := fun b hb => hLU b (Finset.mem_of_mem_erase hb)
      have hUR' : ∀ b ∈ u.erase b0, U b ≤ R := fun b hb => hUR b (Finset.mem_of_mem_erase hb)
      -- minimality plus disjointness: the remaining intervals all start after `U b0`
      have hdL' : ∀ b ∈ u.erase b0, U b0 ≤ L b := by
        intro b hb
        have hb' : b ∈ u := Finset.mem_of_mem_erase hb
        have hne' : b ≠ b0 := Finset.ne_of_mem_erase hb
        rcases hdisj b0 hb0 b hb' (Ne.symm hne') with h | h
        · exact h
        · exfalso
          have h1 := hLU b hb'
          have h2 := hmin b hb'
          linarith
      have hdisj' : ∀ b ∈ u.erase b0, ∀ b' ∈ u.erase b0, b ≠ b' → U b ≤ L b' ∨ U b' ≤ L b :=
        fun b hb b' hb' h => hdisj b (Finset.mem_of_mem_erase hb) b' (Finset.mem_of_mem_erase hb') h
      -- induction hypothesis applied to `u.erase b0` with lower bound `U b0`
      have ihS := ih (u.erase b0).card hcardS (u.erase b0) L U (U b0) R rfl
        hLU' hdL' hdisj' hUR' (hUR b0 hb0)
      have hsum_eq : ∑ b ∈ u, (f (U b) - f (L b))
          = (f (U b0) - f (L b0)) + ∑ b ∈ u.erase b0, (f (U b) - f (L b)) := by
        have h := Finset.sum_erase_add u (fun b => f (U b) - f (L b)) hb0
        rw [← h]; ring
      calc ∑ b ∈ u, (f (U b) - f (L b))
          = (f (U b0) - f (L b0)) + ∑ b ∈ u.erase b0, (f (U b) - f (L b)) := hsum_eq
        _ ≤ (f (U b0) - f (L b0)) + (f R - f (U b0)) := by
              exact add_le_add_right ihS _
        _ = f R - f (L b0) := by ring
        _ ≤ f R - f d := sub_le_sub_left (hf (hdL b0 hb0)) (f R)

end Work.EKLC6Core
