import Mathlib

namespace Work.ZeroDensity.Zeta.balAux

open Finset

/-- The `m`-th harmonic number as a real number, written as a sum over `range`. -/
noncomputable def Hr (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (1 : ℝ) / ((i + 1 : ℕ) : ℝ)

private lemma Hr_mono : Monotone Hr := by
  intro a b hab
  simp only [Hr]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab) ?_
  intro i _ _
  positivity

private lemma Hr_eq_harmonic (m : ℕ) : Hr m = (harmonic m : ℝ) := by
  simp only [Hr, harmonic]
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [one_div]

private lemma Hr_add (N n : ℕ) :
    Hr (N + n) = Hr N + ∑ k ∈ Finset.range n, (1 : ℝ) / (((k + N + 1 : ℕ)) : ℝ) := by
  simp only [Hr]
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Nat.add_comm N k]

theorem harmTailTelescope (N n : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range n, (2 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + N + 1 : ℕ) : ℝ)))
      ≤ 2 * (harmonic N : ℝ) / (N : ℝ) := by
  have hterm : ∀ k ∈ Finset.range n,
      (2 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((k + N + 1 : ℕ) : ℝ))
        = (2 / (N : ℝ)) *
            ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) - (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ)) := by
    intro k _
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have h1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  calc ∑ k ∈ Finset.range n, (2 : ℝ) / (((k + 1 : ℕ) : ℝ) * ((k + N + 1 : ℕ) : ℝ))
      = ∑ k ∈ Finset.range n, (2 / (N : ℝ)) *
          ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) - (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = (2 / (N : ℝ)) * ∑ k ∈ Finset.range n,
          ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) - (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ = (2 / (N : ℝ)) * ((∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
          - ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_sub_distrib]
    _ = (2 / (N : ℝ)) * (Hr n - (Hr (N + n) - Hr N)) := by
        rw [Hr_add N n]
        simp only [Hr]
        ring
    _ ≤ (2 / (N : ℝ)) * Hr N := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := Hr_mono (Nat.le_add_left n N)
        linarith
    _ = 2 * (harmonic N : ℝ) / (N : ℝ) := by
        rw [← Hr_eq_harmonic N]
        ring

end Work.ZeroDensity.Zeta.balAux
