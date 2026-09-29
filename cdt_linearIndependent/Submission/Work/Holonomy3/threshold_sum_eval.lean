import Mathlib

set_option linter.unusedVariables false

namespace Work.Holonomy3

/-- The sum of `0, 1, …, n-1` viewed in `ℝ` equals `n(n-1)/2`. -/
lemma sum_range_cast_real (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of the indices `j : Fin d` whose grid point `j/d` lies strictly below a threshold `t`
equals `K(K-1)/2` with `K = ⌈t d⌉`. -/
lemma threshold_sum_eval (d : ℕ) (hd : 0 < d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < t), (j : ℝ))
      = (Nat.ceil (t * (d : ℝ)) : ℝ) * ((Nat.ceil (t * (d : ℝ)) : ℝ) - 1) / 2 := by
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- `K` is the number of grid points strictly below `t`.
  set K : ℕ := Nat.ceil (t * (d : ℝ)) with hK
  -- `K ≤ d` because `t ≤ 1`.
  have hKd : K ≤ d := by
    have h : t * (d : ℝ) ≤ (d : ℝ) := by nlinarith [ht1, hd']
    rw [hK]
    exact (Nat.ceil_le).mpr h
  -- the membership condition `j/d < t` is exactly `j < K`.
  have hcond : ∀ j : Fin d, ((j : ℝ) / (d : ℝ) < t ↔ (j : ℕ) < K) := by
    intro j
    rw [div_lt_iff₀ hd', hK]
    exact Iff.symm Nat.lt_ceil
  have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < t), (j : ℝ))
      = ∑ i ∈ Finset.range K, (i : ℝ) := by
    have hf : Finset.univ.filter (fun j : Fin d => (j : ℝ) / (d : ℝ) < t)
        = Finset.univ.filter (fun j : Fin d => (j : ℕ) < K) :=
      Finset.filter_congr (fun j _ => hcond j)
    rw [hf, Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < K then (i:ℝ) else 0) d]
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hsum, sum_range_cast_real]

end Work.Holonomy3
