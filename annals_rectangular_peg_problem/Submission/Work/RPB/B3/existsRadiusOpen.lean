import Mathlib

namespace Work.RPB.B3

open Set Metric

/-- The membership in `S` is invariant under shifting the second coordinate by an integer
multiple of `2π`, provided it is invariant under a single shift by `2π`.

This is the iterated form of the periodicity hypothesis `hper`; the `↔` in `hper` supplies
both the forward and the backward iteration. -/
lemma periodShiftInt (S : Set (ℝ × ℝ × ℝ))
    (hper : ∀ τ t r, (τ, t + 2 * Real.pi, r) ∈ S ↔ (τ, t, r) ∈ S)
    (τ t r : ℝ) : ∀ n : ℤ, (τ, t + (n : ℝ) * (2 * Real.pi), r) ∈ S ↔ (τ, t, r) ∈ S := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
      rw [show (((i : ℤ) + 1 : ℤ) : ℝ) * (2 * Real.pi)
            = (i : ℝ) * (2 * Real.pi) + 2 * Real.pi by push_cast; ring]
      rw [← add_assoc, hper τ (t + (i : ℝ) * (2 * Real.pi)) r]
      simpa using ih
  | pred i ih =>
      rw [show ((-(i : ℤ) - 1 : ℤ) : ℝ) * (2 * Real.pi)
            = -((i : ℝ) * (2 * Real.pi)) - 2 * Real.pi by push_cast; ring]
      rw [show t + (-((i : ℝ) * (2 * Real.pi)) - 2 * Real.pi)
            = (t + -((i : ℝ) * (2 * Real.pi))) - 2 * Real.pi by ring]
      rw [← hper τ ((t + -((i : ℝ) * (2 * Real.pi))) - 2 * Real.pi) r]
      rw [show (t + -((i : ℝ) * (2 * Real.pi)) - 2 * Real.pi) + 2 * Real.pi
            = t + -((i : ℝ) * (2 * Real.pi)) by ring]
      simpa using ih

/-- Every real number `t` can be written as `t0 + n · 2π` with `t0 ∈ [0, 2π]` (in fact
`t0 ∈ [0, 2π)`) and `n : ℤ`. -/
lemma existsAngleReduce (t : ℝ) :
    ∃ n : ℤ, ∃ t0 ∈ Set.Icc (0 : ℝ) (2 * Real.pi), t = t0 + (n : ℝ) * (2 * Real.pi) := by
  refine ⟨⌊t / (2 * Real.pi)⌋, t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have h := Int.floor_le (t / (2 * Real.pi))
      have hp : (0 : ℝ) < 2 * Real.pi := by positivity
      have h2 : (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ t := (le_div_iff₀ hp).mp h
      linarith
    · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
      have hp : (0 : ℝ) < 2 * Real.pi := by positivity
      have h2 : t < (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        have h3 := (div_lt_iff₀ hp).mp h
        convert h3 using 1
        ring
      linarith
  · ring

/-- If `S ⊆ ℝ × ℝ × ℝ` is open, invariant under shifting the second coordinate by `2π`, and
contains the whole slice `{r = 0}` over `τ ∈ [0,1]` and all `t`, then it contains a strip
`|r| < R` over `τ ∈ [0,1]` and all `t`, uniformly in `τ` and `t`.

The `τ`-direction is compact and the `t`-direction is reduced to the compact fundamental
interval `[0, 2π]` by periodicity; compactness of `[0,1] × [0,2π] × {0}` inside the open set
`S` then yields a uniform radius. -/
theorem existsRadiusOpen (S : Set (ℝ × ℝ × ℝ))
    (hS : IsOpen S)
    (hper : ∀ τ t r, (τ, t + 2 * Real.pi, r) ∈ S ↔ (τ, t, r) ∈ S)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, (τ, t, 0) ∈ S) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < R → (τ, t, r) ∈ S := by
  classical
  -- The compact fundamental piece `[0,1] × [0,2π] × {0}`.
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc 0 (2 * Real.pi) ×ˢ ({0} : Set ℝ)) with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)
  have hKS : K ⊆ S := by
    intro p hp
    rw [hKdef] at hp
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hthis : (p.1, p.2.1, (0 : ℝ)) ∈ S := h0 p.1 h1 p.2.1
    have hpe : p = (p.1, p.2.1, (0 : ℝ)) := by
      ext <;> simp [h3]
    rw [hpe]
    exact hthis
  -- Compactness inside the open set gives a uniform thickening.
  obtain ⟨δ, hδpos, hδsub⟩ := hKc.exists_cthickening_subset_open hS hKS
  refine ⟨δ, hδpos, ?_⟩
  intro τ hτ t r hr
  -- Reduce `t` into the fundamental interval.
  obtain ⟨n, t0, ht0, ht⟩ := existsAngleReduce t
  have hKmem : (τ, t0, (0 : ℝ)) ∈ K := by
    rw [hKdef]
    exact ⟨hτ, ht0, by simp⟩
  have hdist : dist ((τ, t0, r) : ℝ × ℝ × ℝ) (τ, t0, (0 : ℝ)) = |r| := by
    simp [Prod.dist_eq]
  have hmem : (τ, t0, r) ∈ S :=
    hδsub (Metric.mem_cthickening_of_dist_le (τ, t0, r) (τ, t0, (0 : ℝ)) δ K hKmem
      (by rw [hdist]; exact le_of_lt hr))
  -- Periodicity transports the statement back to `t`.
  rw [ht]
  exact (periodShiftInt S hper τ t0 r n).mpr hmem

end Work.RPB.B3
