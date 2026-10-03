import Mathlib
import Submission.Work.KMTAreas.Khintchine.sum_enorm_rpow
import Submission.Work.KMTAreas.Khintchine.ofReal_rpow_le_inv_mul_inv_mul
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

namespace Work.KMTAreas.A7

open Finset

/-- **Khintchine on the `ℓ²`-size of a finite complex vector, in `ℝ≥0∞` form.**

For every `q ≥ 1` there is `c > 0` such that for every `N` and every `v : Fin N → ℂ`

`(∑ i, ‖v i‖ₑ ^ 2) ^ (q/2) ≤ (c^q)^{-1} (2^N)^{-1} ∑ ε, ‖∑ i, ε_i v i‖ₑ ^ q`,

where `ε` runs over the `2^N` sign choices `Fin N → Bool`.

This is the lower half of Khintchine's inequality
(`Commons.Analysis.Walsh.exists_khintchine_hilbert`, applied with the Hilbert space `ℂ`),
which gives `c (∑ i, ‖v i‖^2)^{1/2} ≤ (2^{-N} ∑ ε, ‖∑ i, ε_i v i‖^q)^{1/q}`;
the `ℝ≥0∞`-valued statement is then pure bookkeeping: `sum_enorm_rpow` converts the two
`ℝ≥0∞` sums into `ofReal` of the corresponding real sums, and
`ofReal_rpow_le_inv_mul_inv_mul` performs the algebraic rearrangement
`A^q ≤ c^{-q} 2^{-N} S` of the Khintchine inequality. -/
theorem khintchine_sqSum_pointwise (q : ℝ) (hq : 1 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (v : Fin N → ℂ),
      (∑ i : Fin N, ‖v i‖ₑ ^ (2 : ℝ)) ^ (q / 2)
        ≤ (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            ∑ ε : Fin N → Bool,
              ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * v i‖ₑ ^ q := by
  obtain ⟨c, C, hc, hC, hKh⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert q hq
  refine ⟨c, hc, ?_⟩
  intro N v
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  -- the real `ℓ²`-square of `v` and the real sign-averaged `q`-moment of the signed sums
  set B : ℝ := ∑ i : Fin N, ‖v i‖ ^ (2 : ℕ) with hBdef
  set T : ℝ := ∑ e : Fin N → Bool, ‖∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i‖ ^ q
    with hTdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact Finset.sum_nonneg fun i _ => by positivity
  have hTnn : 0 ≤ T := by
    rw [hTdef]; exact Finset.sum_nonneg fun i _ => by positivity
  -- Khintchine's inequality for `H = ℂ`
  have hkh := (hKh (H := ℂ) N v).1
  have hkh' : c * B ^ ((1 : ℝ) / 2) ≤ (T / (2 : ℝ) ^ N) ^ (1 / q) := by
    rw [hBdef, hTdef]
    simpa [smul_eq_mul] using hkh
  -- rearrange to `ofReal (B ^ (q/2)) ≤ c^{-q} 2^{-N} ofReal T`
  have hmain := Work.KMTAreas.Khintchine.ofReal_rpow_le_inv_mul_inv_mul (p := q) (c := c)
    (A := B ^ ((1 : ℝ) / 2)) (S := T) (n := N) hc hq0 (Real.rpow_nonneg hBnn _) hTnn hkh'
  have hAq : (B ^ ((1 : ℝ) / 2)) ^ q = B ^ (q / 2) := by
    rw [← Real.rpow_mul hBnn]; congr 1; ring
  have hmain' : ENNReal.ofReal (B ^ (q / 2)) ≤
      (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ENNReal.ofReal T := by
    simpa only [hAq] using hmain
  -- identify the two `ℝ≥0∞` sums with `ofReal B` and `ofReal T`
  have hLHS : (∑ i : Fin N, ‖v i‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal B := by
    rw [Work.KMTAreas.Khintchine.sum_enorm_rpow v (by norm_num : (0 : ℝ) < 2), hBdef]
    simp
  have hRHS : (∑ e : Fin N → Bool, ‖∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i‖ₑ ^ q)
      = ENNReal.ofReal T := by
    rw [Work.KMTAreas.Khintchine.sum_enorm_rpow (fun e : Fin N → Bool =>
      ∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i) hq0, hTdef]
  rw [hLHS, hRHS, ENNReal.ofReal_rpow_of_nonneg hBnn (by positivity : (0 : ℝ) ≤ q / 2)]
  exact hmain'

end Work.KMTAreas.A7
