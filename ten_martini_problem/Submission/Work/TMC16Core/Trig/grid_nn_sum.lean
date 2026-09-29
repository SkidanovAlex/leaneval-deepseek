import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.gridW
import Submission.Work.TMC16Core.Trig.sum_emod_coprime
import Submission.Work.TMC16Core.Trig.nn_grid_min_transfer
import Submission.Work.TMC16Core.Trig.nn_mul_div_emod
import Submission.Work.TMC16Core.Trig.gridW_inv_sum_le
import Submission.Work.TMC16Core.Trig.q_mul_nn_eq_gridW

/-!
# The grid sum estimate `grid_nn_sum`

For `q > 0`, `p` coprime to `q` and a real phase `x`, the numbers
`nn (2 * x + k * (p/q))`, `k = 1, …, q`, form (after the change of index
`k ↦ (k * p) mod q`) the distances of the grid `j/q`, `j = 0, …, q - 1`, shifted by the
fractional part of `2x`, to the nearest integer.  If `k₁` minimises these distances then the
reciprocals of the remaining `q - 1` values obey the harmonic-type bound
`∑_{k ≠ k₁} 1 / nn (2x + k p/q) ≤ 4 q (1 + log q)`.

The proof splits into

* the arithmetic reduction `nn (2x + k p/q) = nn (2x + ((k p) mod q)/q)` together with the
  re-indexing of the sum over `k ∈ [1,q]` as a sum over the residues `j ∈ [0,q)`
  (this is where coprimality of `p` and `q` is used), and
* the purely real estimate `gridW_inv_sum_le` for the grid distances `gridW`.
-/

noncomputable section

namespace Work.TMC16Core.Trig

open Work.TMC16Core.Basic

/-! ## Glue lemmas -/

/-- The erased-sum re-indexing, derived from `sum_emod_coprime`. -/
theorem sum_erase_emod_coprime {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q) (F : ℕ → ℝ) :
    ∑ k ∈ (Finset.Icc 1 q).erase k₁, F ((((k : ℤ) * p) % q).toNat)
      = ∑ j ∈ (Finset.range q).erase ((((k₁ : ℤ) * p) % q).toNat), F j := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hjlt : ((((k₁ : ℤ) * p) % q).toNat) < q := by
    have h1 : 0 ≤ ((k₁ : ℤ) * p) % q := Int.emod_nonneg _ hqZ
    have h2 : ((k₁ : ℤ) * p) % q < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have h3 : ((((k₁ : ℤ) * p) % q).toNat : ℤ) < (q : ℤ) := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  have hmain := sum_emod_coprime hq hcop (F := fun z : ℤ => F z.toNat)
  simp only [Int.toNat_natCast] at hmain
  rw [Finset.sum_erase_eq_sub hk₁, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hjlt),
    hmain]

/-- `nn (2x + w) = nn (s + w)` where `s` is the fractional part of `2x`. -/
theorem nn_two_mul_add_frac (x w : ℝ) :
    nn (2 * x + w) = nn (Int.fract (2 * x) + w) := by
  have h : 2 * x + w = (Int.fract (2 * x) + w) + ((⌊2 * x⌋ : ℤ) : ℝ) := by
    have hfloor := Int.floor_add_fract (2 * x)
    linarith
  rw [h, nn_add_intCast]

/-- `c * (c * w)⁻¹ = w⁻¹` for `c ≠ 0`. -/
theorem mul_inv_mul (c w : ℝ) (hc : c ≠ 0) : c * (c * w)⁻¹ = w⁻¹ := by
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- `((z.toNat : ℕ) : ℝ) = ((z : ℤ) : ℝ)` for `0 ≤ z`. -/
theorem cast_toNat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : (((z.toNat : ℕ)) : ℝ) = ((z : ℤ) : ℝ) := by
  exact_mod_cast (Int.toNat_of_nonneg hz : ((z.toNat : ℕ) : ℤ) = z)

theorem grid_nn_sum {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≥
        Work.TMC16Core.Basic.nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))) :
    ∑ k ∈ (Finset.Icc 1 q).erase k₁,
        (Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
      ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  let j₁ : ℕ := ((((k₁ : ℤ) * p) % q).toNat)
  have hj₁lt : j₁ < q := by
    have h1 : 0 ≤ ((k₁ : ℤ) * p) % q := Int.emod_nonneg _ hqZ
    have h2 : ((k₁ : ℤ) * p) % q < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have h3 : ((j₁ : ℕ) : ℤ) < (q : ℤ) := by
      dsimp only [j₁]
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  -- the minimality hypothesis transfers to the grid index `j₁`
  have hminj : ∀ j < q, nn (2 * x + (j : ℝ) / (q : ℝ)) ≥
      nn (2 * x + (j₁ : ℝ) / (q : ℝ)) := by
    intro j hj
    have h := nn_grid_min_transfer hq hcop x hk₁ hmin j hj
    simpa only [j₁] using h
  -- fractional part of the phase
  set s : ℝ := Int.fract (2 * x) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Int.fract_nonneg (2 * x)
  have hs1 : s < 1 := by rw [hsdef]; exact Int.fract_lt_one (2 * x)
  have hminj_s : ∀ j < q, nn (s + (j : ℝ) / (q : ℝ)) ≥ nn (s + (j₁ : ℝ) / (q : ℝ)) := by
    intro j hj
    have h := hminj j hj
    have e1 : nn (2 * x + (j : ℝ) / (q : ℝ)) = nn (s + (j : ℝ) / (q : ℝ)) := by
      simpa [hsdef] using nn_two_mul_add_frac x ((j : ℝ) / (q : ℝ))
    have e2 : nn (2 * x + (j₁ : ℝ) / (q : ℝ)) = nn (s + (j₁ : ℝ) / (q : ℝ)) := by
      simpa [hsdef] using nn_two_mul_add_frac x ((j₁ : ℝ) / (q : ℝ))
    rwa [e1, e2] at h
  -- re-index the sum along the residue bijection `k ↦ (k * p) mod q`
  have hreindex : ∑ k ∈ (Finset.Icc 1 q).erase k₁,
        (nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
      = ∑ j ∈ (Finset.range q).erase j₁, (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹ := by
    have hA : ∑ k ∈ (Finset.Icc 1 q).erase k₁,
          (nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
        = ∑ k ∈ (Finset.Icc 1 q).erase k₁,
          (nn (2 * x + ((((k : ℤ) * p) % q).toNat : ℝ) / (q : ℝ)))⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro k _
      have hz : 0 ≤ ((k : ℤ) * p) % q := Int.emod_nonneg _ hqZ
      congr 1
      rw [cast_toNat_of_nonneg hz, ← nn_mul_div_emod hq p x k]
    have h1 := sum_erase_emod_coprime hq hcop hk₁
      (F := fun j : ℕ => (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹)
    rw [hA]
    simpa only [j₁] using h1
  -- the real grid estimate
  have hminW : ∀ j < q, gridW q ((q : ℝ) * s) j₁ ≤ gridW q ((q : ℝ) * s) j := by
    intro j hj
    have h1 : (q : ℝ) * nn (s + (j₁ : ℝ) / (q : ℝ)) = gridW q ((q : ℝ) * s) j₁ :=
      q_mul_nn_eq_gridW hq hs0 hs1 hj₁lt
    have h2 : (q : ℝ) * nn (s + (j : ℝ) / (q : ℝ)) = gridW q ((q : ℝ) * s) j :=
      q_mul_nn_eq_gridW hq hs0 hs1 hj
    rw [← h1, ← h2]
    exact mul_le_mul_of_nonneg_left (hminj_s j hj) (le_of_lt hpos)
  have hA0 : 0 ≤ (q : ℝ) * s := mul_nonneg (le_of_lt hpos) hs0
  have hAq : (q : ℝ) * s < (q : ℝ) := by nlinarith [hpos, hs0, hs1]
  have hcore := gridW_inv_sum_le hq hA0 hAq hj₁lt hminW
  -- normalise `gridW q (q*s) j = q * nn (s + j/q)` and multiply through by `q`
  have hnorm : ∑ j ∈ (Finset.range q).erase j₁, (gridW q ((q : ℝ) * s) j)⁻¹
      = (q : ℝ)⁻¹ * ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjq : j < q := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    rw [← q_mul_nn_eq_gridW hq hs0 hs1 hjq, mul_inv]
  have hfinal : ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹
      ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
    rw [hnorm] at hcore
    have hmul := mul_le_mul_of_nonneg_left hcore (le_of_lt hpos)
    have hleft : (q : ℝ) * ((q : ℝ)⁻¹ *
        ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹)
        = ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rw [hleft] at hmul
    calc ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹
        ≤ (q : ℝ) * (4 * (1 + Real.log (q : ℝ))) := hmul
      _ = 4 * (q : ℝ) * (1 + Real.log q) := by ring
  have hsum_s : ∑ j ∈ (Finset.range q).erase j₁, (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹
      = ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    simpa [hsdef] using nn_two_mul_add_frac x ((j : ℝ) / (q : ℝ))
  rw [hreindex, hsum_s]
  exact hfinal

end Work.TMC16Core.Trig
