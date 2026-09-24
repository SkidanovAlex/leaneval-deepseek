import Mathlib
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- A window (tail) of `corrExt` starting after `N` equals the difference of the two
partial sums over `range (m+1)` and `range (N+1)`, for `N ≤ m`. -/
private lemma partial_window_eq_sum_Icc (N m : ℕ) (hNm : N ≤ m) :
    (∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)
      = ∑ k ∈ Finset.Icc (N + 1) m, corrExt k := by
  have hsub : Finset.range (N + 1) ⊆ Finset.range (m + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega : N + 1 ≤ m + 1))
  have hsum := Finset.sum_sdiff (s₁ := Finset.range (N + 1)) (s₂ := Finset.range (m + 1))
    (f := corrExt) hsub
  have hset : Finset.range (m + 1) \ Finset.range (N + 1) = Finset.Icc (N + 1) m := by
    ext x
    simp
    omega
  -- hsum : (∑ range(m+1)\range(N+1)) + (∑ range(N+1)) = ∑ range(m+1)
  calc
    (∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)
        = (∑ k ∈ Finset.range (m + 1) \ Finset.range (N + 1), corrExt k) := by
            rw [← hsum]
            ring
    _ = ∑ k ∈ Finset.Icc (N + 1) m, corrExt k := by
            rw [hset]

/-- Finite-window tail bound for the correction terms: for `N ≤ m`,
`|(Σ_{k ≤ m} corrExt k) − (Σ_{k ≤ N} corrExt k)| ≤ 4 / (N+1)`. -/
private lemma partial_window_bound (N m : ℕ) (hNm : N ≤ m) :
    |(∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)|
      ≤ (4 : ℝ) / ((N : ℝ) + 1) := by
  have hIccIoo : Finset.Icc (N + 1) m = Finset.Ioo N (m + 1) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ioo]
  calc
    |(∑ k ∈ Finset.range (m + 1), corrExt k) - (∑ k ∈ Finset.range (N + 1), corrExt k)|
        = |∑ k ∈ Finset.Icc (N + 1) m, corrExt k| := by
            rw [partial_window_eq_sum_Icc N m hNm]
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) m, |corrExt k| :=
            Finset.abs_sum_le_sum_abs corrExt (Finset.Icc (N + 1) m)
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) m, (2 : ℝ) / (k : ℝ) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro k hk
            simpa [Real.norm_eq_abs] using corrExt_bound k
    _ = ∑ k ∈ Finset.Icc (N + 1) m, (2 : ℝ) * (((k : ℝ) ^ 2)⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [div_eq_mul_inv]
    _ = (2 : ℝ) * ∑ k ∈ Finset.Icc (N + 1) m, (((k : ℝ) ^ 2)⁻¹) := by
            rw [Finset.mul_sum]
    _ = (2 : ℝ) * ∑ k ∈ Finset.Ioo N (m + 1), (((k : ℝ) ^ 2)⁻¹) := by
            rw [hIccIoo]
    _ ≤ (2 : ℝ) * (2 / ((N : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) N (m + 1)) (by norm_num)
    _ = (4 : ℝ) / ((N : ℝ) + 1) := by ring

/-- The correction term series is summable with tail decaying like `O(1/N)`:
there is `C > 0` with `|Σ' corrExt − Σ_{k ≤ N} corrExt| ≤ C / N` for every `N ≥ 1`. -/
theorem corr_sum_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑' n : ℕ, Commons.NumberTheory.Mertens.corrExt n) -
        (∑ k ∈ Finset.range (N + 1), Commons.NumberTheory.Mertens.corrExt k)| ≤
        C / (N : ℝ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro N hN
  let S : ℕ → ℝ := fun m => ∑ k ∈ Finset.range (m + 1), corrExt k
  let T : ℝ := ∑' n : ℕ, corrExt n
  have hS : Tendsto S atTop (nhds T) := by
    dsimp [S, T]
    exact tendsto_partial_range_add_one
  have hwin : ∀ m : ℕ, N ≤ m → |S m - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := by
    intro m hm
    dsimp [S]
    exact partial_window_bound N m hm
  have hev : ∀ᶠ m : ℕ in atTop, |S m - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with m hm
    exact hwin m hm
  have hsub : Tendsto (fun m : ℕ => S m - S N) atTop (nhds (T - S N)) := by
    exact hS.sub tendsto_const_nhds
  have hlim : Tendsto (fun m : ℕ => |S m - S N|) atTop (nhds (|T - S N|)) := by
    change Tendsto (abs ∘ (fun m : ℕ => S m - S N)) atTop (nhds (abs (T - S N)))
    exact (continuous_abs.tendsto (T - S N)).comp hsub
  have hb : |T - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := le_of_tendsto hlim hev
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hden_le : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hfinal : |T - S N| ≤ (4 : ℝ) / (N : ℝ) := by
    calc
      |T - S N| ≤ (4 : ℝ) / ((N : ℝ) + 1) := hb
      _ ≤ (4 : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hNpos hden_le
  simpa [S, T] using hfinal

end

end Commons.NumberTheory.Mertens
