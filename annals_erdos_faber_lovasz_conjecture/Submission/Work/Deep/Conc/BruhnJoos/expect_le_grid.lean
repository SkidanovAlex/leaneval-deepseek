import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic

namespace Work.Deep.Conc.BruhnJoos

open scoped BigOperators

/-- Auxiliary "layer-cake" bound.  If `0 ≤ y < n * δ` with `δ > 0`, and
`v : ℕ → ℝ` is nonnegative and equals `1` at every level `k` with `k * δ ≤ y`,
then `y ≤ δ * ∑ k ∈ Finset.range n, v k`.

Indeed, if `j` is maximal with `j * δ ≤ y` then all levels `0, …, j` contribute
`1`, so the sum is at least `j + 1 > y / δ`. -/
lemma le_mul_sum_aux {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {y : ℝ} (hy0 : 0 ≤ y)
    (hyn : y < (n : ℝ) * δ) (v : ℕ → ℝ) (hv0 : ∀ k : ℕ, 0 ≤ v k)
    (hv1 : ∀ k : ℕ, (k : ℝ) * δ ≤ y → v k = 1) :
    y ≤ δ * ∑ k ∈ Finset.range n, v k := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul] at hyn
    linarith
  | succ n ih =>
    rcases lt_or_ge y ((n : ℝ) * δ) with h | h
    · -- `y` is still below the previous level: use the induction hypothesis.
      have hle : y ≤ δ * ∑ k ∈ Finset.range n, v k := ih h
      have hmono : (∑ k ∈ Finset.range n, v k) ≤ (∑ k ∈ Finset.range (n + 1), v k) := by
        rw [Finset.sum_range_succ]
        linarith [hv0 n]
      calc y ≤ δ * ∑ k ∈ Finset.range n, v k := hle
        _ ≤ δ * ∑ k ∈ Finset.range (n + 1), v k :=
            mul_le_mul_of_nonneg_left hmono (le_of_lt hδ)
    · -- `n * δ ≤ y < (n + 1) * δ`: every level `k ≤ n` contributes `1`.
      have hall : ∀ k ∈ Finset.range (n + 1), v k = 1 := by
        intro k hk
        refine hv1 k ?_
        have hk' : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Finset.mem_range_succ_iff.mp hk)
        exact (mul_le_mul_of_nonneg_right hk' (le_of_lt hδ)).trans h
      have hsum : ∑ k ∈ Finset.range (n + 1), v k = ((n : ℝ) + 1) := by
        have h2 : ∑ k ∈ Finset.range (n + 1), v k = ∑ k ∈ Finset.range (n + 1), 1 :=
          Finset.sum_congr rfl fun k hk => hall k hk
        rw [h2]
        simp
      rw [hsum, mul_comm δ ((n : ℝ) + 1)]
      simp only [Nat.cast_succ] at hyn
      exact le_of_lt hyn

theorem expect_le_grid {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Y : Ω → ℝ) {L δ : ℝ}
    {n : ℕ} (hδ : 0 < δ) (hL : 0 < L) (hY0 : ∀ ω, 0 ≤ Y ω) (hYL : ∀ ω, Y ω ≤ L)
    (hn : L < (n : ℝ) * δ) :
    Work.Deep.Conc.expect Y ≤ δ * ∑ k ∈ Finset.range n,
      Work.Deep.Conc.prob {ω | (k : ℝ) * δ ≤ Y ω} := by
  -- Pointwise grid bound: `Y ω ≤ δ * (number of grid points below `Y ω`)`.
  have hpt : ∀ ω, Y ω ≤ δ * ∑ k ∈ Finset.range n,
      ({ω' | (k : ℝ) * δ ≤ Y ω'} : Set Ω).indicator (fun _ => (1:ℝ)) ω := by
    intro ω
    refine le_mul_sum_aux hδ (hY0 ω) (lt_of_le_of_lt (hYL ω) hn)
      (fun k => ({ω' | (k : ℝ) * δ ≤ Y ω'} : Set Ω).indicator (fun _ => (1:ℝ)) ω) ?_ ?_
    · intro k
      exact Work.Deep.Conc.indicator_one_nonneg _ ω
    · intro k hk
      have hmem : ω ∈ {ω' : Ω | (k : ℝ) * δ ≤ Y ω'} := hk
      exact Set.indicator_of_mem hmem (fun _ => (1:ℝ))
  -- Take expectations of the pointwise bound.
  have h1 := Work.Deep.Conc.expect_mono' (f := Y)
    (g := fun ω => δ * ∑ k ∈ Finset.range n,
      ({ω' | (k : ℝ) * δ ≤ Y ω'} : Set Ω).indicator (fun _ => (1:ℝ)) ω) hpt
  rw [Work.Deep.Conc.expect_const_mul, Work.Deep.Conc.expect_sum] at h1
  exact h1

end Work.Deep.Conc.BruhnJoos
