import Mathlib

namespace Work.TMC7Core.Scale

theorem rtlExpGeomSum (cκ B₀ : ℝ) (Q : ℕ → ℕ) (k : ℕ) (hcκ : 0 < cκ) (hB₀ : 0 ≤ B₀)
    (hmono : ∀ j < k, Q j < Q (j + 1)) :
    (∑ i ∈ Finset.range k, B₀ * Real.exp (-(cκ * (Q i : ℝ) / 2)))
      ≤ B₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * (1 - Real.exp (-(cκ / 2)))⁻¹ := by
  set r : ℝ := Real.exp (-(cκ / 2)) with hrdef
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  -- `Q` strictly increases, hence `Q i ≥ Q 0 + i` on `[0, k]`.
  have hQmono : ∀ i, i ≤ k → Q 0 + i ≤ Q i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have h1 : Q n < Q (n + 1) := hmono n (by omega)
        have h2 : Q 0 + n ≤ Q n := ih (by omega)
        omega
  -- The geometric series is summable and dominated by its total sum.
  have hsummable : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  have hgeo : (∑ i ∈ Finset.range k, r ^ i) ≤ (1 - r)⁻¹ := by
    have h := Summable.sum_le_tsum (Finset.range k) (fun i _ => pow_nonneg hr0 i) hsummable
    rwa [tsum_geometric_of_lt_one hr0 hr1] at h
  -- Pointwise geometric domination.
  have hpoint : ∀ i ∈ Finset.range k,
      B₀ * Real.exp (-(cκ * (Q i : ℝ) / 2))
        ≤ B₀ * (Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * r ^ i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hle : (Q 0 : ℝ) + i ≤ (Q i : ℝ) := by
      have := hQmono i (le_of_lt hik)
      exact_mod_cast this
    have harg : -(cκ * (Q i : ℝ) / 2) ≤ -(cκ * ((Q 0 : ℝ) + i) / 2) := by
      nlinarith [hle, hcκ]
    have hexp : Real.exp (-(cκ * (Q i : ℝ) / 2))
        ≤ Real.exp (-(cκ * ((Q 0 : ℝ) + i) / 2)) := Real.exp_le_exp.mpr harg
    have hsplit : Real.exp (-(cκ * ((Q 0 : ℝ) + i) / 2))
        = Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * r ^ i := by
      rw [hrdef]
      rw [show -(cκ * ((Q 0 : ℝ) + i) / 2)
            = -(cκ * (Q 0 : ℝ) / 2) + (i : ℝ) * (-(cκ / 2)) by ring]
      rw [Real.exp_add, Real.exp_nat_mul]
    rw [hsplit] at hexp
    exact mul_le_mul_of_nonneg_left hexp hB₀
  calc ∑ i ∈ Finset.range k, B₀ * Real.exp (-(cκ * (Q i : ℝ) / 2))
      ≤ ∑ i ∈ Finset.range k, B₀ * (Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * r ^ i) :=
        Finset.sum_le_sum hpoint
    _ = B₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * (∑ i ∈ Finset.range k, r ^ i) := by
        rw [Finset.mul_sum (Finset.range k) (fun i => r ^ i)
              (B₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)))]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ B₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * (1 - r)⁻¹ := by
        apply mul_le_mul_of_nonneg_left hgeo
        positivity
    _ = B₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) * (1 - Real.exp (-(cκ / 2)))⁻¹ := by
        rw [hrdef]

end Work.TMC7Core.Scale
