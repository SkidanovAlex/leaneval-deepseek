import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- A `Finset` version of `Finset.card_filter`, cast to `ℝ`. -/
private lemma card_filter_cast {α : Type} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ a ∈ s, (if P a then (1 : ℝ) else 0) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h]

/-- Double counting: the sum over an `r`-separated set `Ω` of the number of points of `D`
lying in each ball of radius `R` around the points of `Ω` is at most `M` times the size of `D`.
Balls of radius `R ≤ 5r/2` around an `r`-separated set contain at most `M` points of `Ω`,
which is what `hdoub` guarantees. -/
theorem sum_ball_card {ι Z : Type} [DecidableEq ι] [DecidableEq Z]
    (d : Z → Z → ℝ) (r M R : ℝ) (hr : 0 < r) (hR : R ≤ 5 * r / 2)
    (hd_sym : ∀ a b, d a b = d b a)
    (hdoub : ∀ z : Z, ∀ s : Finset Z, (∀ w ∈ s, d w z ≤ 5 * r / 2) →
      (∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → r / 2 ≤ d w w') → (s.card : ℝ) ≤ M)
    (Ω : Finset Z) (hsep : ∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → r ≤ d z w)
    (D : Finset (ι × Z)) :
    (∑ z₀ ∈ Ω, ((D.filter (fun q => d q.2 z₀ ≤ R)).card : ℝ)) ≤ M * (D.card : ℝ) := by
  classical
  -- Every `z` has at most `M` points of `Ω` within distance `R`.
  have hkey : ∀ z : Z, ((Ω.filter (fun z₀ => d z z₀ ≤ R)).card : ℝ) ≤ M := by
    intro z
    refine hdoub z (Ω.filter fun z₀ => d z z₀ ≤ R) ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter] at hw
      have h2 : d w z = d z w := hd_sym w z
      linarith
    · intro w hw w' hw' hne
      simp only [Finset.mem_filter] at hw hw'
      have h2 := hsep w hw.1 w' hw'.1 hne
      linarith
  -- Swap the order of summation, then bound each inner sum by `M`.
  calc ∑ z₀ ∈ Ω, ((D.filter (fun q => d q.2 z₀ ≤ R)).card : ℝ)
      = ∑ z₀ ∈ Ω, ∑ q ∈ D, (if d q.2 z₀ ≤ R then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun z₀ _ => ?_
        exact card_filter_cast D _
    _ = ∑ q ∈ D, ∑ z₀ ∈ Ω, (if d q.2 z₀ ≤ R then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ q ∈ D, ((Ω.filter (fun z₀ => d q.2 z₀ ≤ R)).card : ℝ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        exact (card_filter_cast Ω (fun z₀ => d q.2 z₀ ≤ R)).symm
    _ ≤ ∑ _q ∈ D, M := Finset.sum_le_sum fun q _ => hkey q.2
    _ = M * (D.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Work.N8
