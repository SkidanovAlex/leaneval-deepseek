import Mathlib

set_option linter.unusedVariables false

namespace Work.Peluse.LadderP

/-- Pointwise (per-index) step of `p2jensen`: if `a ≤ x`, `a ≥ 0`, `w ≥ 0`, then
`a^k * (w * x) ≤ w * x^(k+1)` (note `x^k ≥ a^k`, so `a^k * w * x ≤ w * x^k * x`). -/
private lemma pow_mul_le_mul_pow {a x w : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hw : 0 ≤ w) (k : ℕ) :
    a ^ k * (w * x) ≤ w * x ^ (k + 1) := by
  calc a ^ k * (w * x) ≤ x ^ k * (w * x) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hax k)
          (mul_nonneg hw (le_trans ha hax))
    _ = w * x ^ (k + 1) := by rw [pow_succ]; ring

/-- Jensen-type extraction: if `w i ≥ 0` sums to `1`, `u i ≥ 0`, and the weighted mean
`∑ w i * u i` is at least `γ ≥ 0`, then the `Θ`-th powers of the large values `u i ≥ γ/2`
(weighted by `w`) dominate `(γ/2)^Θ`.  Equivalently: the mass of the set where `u` is small
costs at most `γ/2` of the mean budget, so at least `γ/2` of the budget is carried by the
set where `u i ≥ γ/2`, on which `u i^Θ ≥ (γ/2)^(Θ-1) * u i`. -/
theorem p2jensen {ι : Type} [Fintype ι] (w u : ι → ℝ) (γ : ℝ) (Θ : ℕ) (hΘ : 1 ≤ Θ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hγ : 0 ≤ γ) (hsum : γ ≤ ∑ i, w i * u i) :
    (γ / 2) ^ Θ
      ≤ ∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * (u i) ^ Θ := by
  classical
  -- Write `Θ = k + 1` (using `hΘ : 1 ≤ Θ`) so that `pow_succ` applies.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Θ ≠ 0)
  have ha0 : 0 ≤ γ / 2 := by linarith
  -- The complement of the "large" set: there `u i < γ/2`, so its contribution to the mean
  -- is at most `(γ/2) * ∑_{i ∉ S} w i ≤ γ/2`.
  have hcomp : ∑ i ∈ Finset.univ.filter (fun i => ¬ (γ / 2 ≤ u i)), w i * u i ≤ γ / 2 := by
    calc ∑ i ∈ Finset.univ.filter (fun i => ¬ (γ / 2 ≤ u i)), w i * u i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ (γ / 2 ≤ u i)), w i * (γ / 2) := by
          apply Finset.sum_le_sum
          intro i hi
          have hlt : ¬ (γ / 2 ≤ u i) := (Finset.mem_filter.mp hi).2
          exact mul_le_mul_of_nonneg_left (lt_of_not_ge hlt).le (hw i)
      _ = (∑ i ∈ Finset.univ.filter (fun i => ¬ (γ / 2 ≤ u i)), w i) * (γ / 2) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (γ / 2) := by
          apply mul_le_mul_of_nonneg_right _ ha0
          calc ∑ i ∈ Finset.univ.filter (fun i => ¬ (γ / 2 ≤ u i)), w i
              ≤ ∑ i : ι, w i := Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.filter_subset _ _) (fun i _ _ => hw i)
            _ = 1 := hws
      _ = γ / 2 := one_mul _
  -- Hence the "large" set carries at least `γ - γ/2 = γ/2` of the mean.
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i => γ / 2 ≤ u i) (f := fun i => w i * u i)
  have hS : γ / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * u i := by
    linarith [hsplit, hcomp]
  -- On the large set, `(γ/2)^k * (w i * u i) ≤ w i * u i^(k+1)` pointwise.
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i),
      (γ / 2) ^ k * (w i * u i) ≤ w i * u i ^ (k + 1) := by
    intro i hi
    have hui : γ / 2 ≤ u i := (Finset.mem_filter.mp hi).2
    exact pow_mul_le_mul_pow ha0 hui (hw i) k
  have key : (γ / 2) ^ k * (∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * u i)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * u i ^ (k + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  calc (γ / 2) ^ (k + 1) = (γ / 2) ^ k * (γ / 2) := by rw [pow_succ]
    _ ≤ (γ / 2) ^ k * (∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * u i) :=
        mul_le_mul_of_nonneg_left hS (pow_nonneg ha0 k)
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => γ / 2 ≤ u i), w i * u i ^ (k + 1) := key

end Work.Peluse.LadderP
