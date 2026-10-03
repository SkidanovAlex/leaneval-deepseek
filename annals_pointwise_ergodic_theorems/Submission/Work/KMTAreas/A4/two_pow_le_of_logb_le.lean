import Mathlib
import Submission.Work.KMTAreas.A4.two_pow_logN_le

/-!
# The scale comparison of §5 (Krause--Mirek--Tao)

This module proves the elementary scale bookkeeping used in §5 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

namely: if the fixed constant `C₀ > 0` is small enough on the logarithmic scale, i.e.
`2 log₂ (4 C₀) ≤ l`, then the two "height" conditions `2^{Lᵢ} ≤ C₀ 2^{l/2}` and
`2^{kᵢ} ≤ C₀ 2^{l/2} / N` force `Lᵢ ≤ l` and `kᵢ ≤ l - Log N - 1`.  This is what makes the
truncation height `l` dominate the running scale and what produces the `N⁻¹` (equivalently
`2^{-Log N}`) gain on the second summand.
-/

namespace Work.KMTAreas.A4

/-- From the logarithmic smallness of `4 C₀` and the two height bounds at scale `l/2`, the
natural height `Li` is at most `l`, and the integer height `ki` is at most
`l - Log N - 1` with `Log N = log₂ max(N,2)`. -/
theorem two_pow_le_of_logb_le {C₀ : ℝ} (hC₀ : 0 < C₀) {N l Li : ℕ} {ki : ℤ} (hN : 1 ≤ N) (hlog : 2 * Real.logb 2 (4 * C₀) ≤ (l : ℝ)) (hli : (2 : ℝ) ^ Li ≤ C₀ * (2 : ℝ) ^ ((l : ℝ) / 2)) (hki : (2 : ℝ) ^ ki ≤ C₀ * (2 : ℝ) ^ ((l : ℝ) / 2) / (N : ℝ)) : Li ≤ l ∧ ki ≤ (l : ℤ) - Work.Analysis.EndVar.logN N - 1 := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- Rewrite the logarithmic hypothesis: `log₂ (4 C₀) = 2 + log₂ C₀`.
  have hlogb4 : Real.logb 2 (4 * C₀) = 2 + Real.logb 2 C₀ := by
    rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hC₀),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one h2]
    norm_num
  -- Hence `log₂ C₀ ≤ l/2 - 2`.
  have hL : Real.logb 2 C₀ ≤ (l : ℝ) / 2 - 2 := by
    have := hlog
    rw [hlogb4] at this
    linarith
  -- Exponentials: `4 C₀ ≤ 2^{l/2}`, equivalently `C₀ ≤ 2^{l/2 - 2}`.
  have h4C0 : 4 * C₀ ≤ (2 : ℝ) ^ ((l : ℝ) / 2) :=
    (Real.logb_le_iff_le_rpow h2 (by positivity : (0 : ℝ) < 4 * C₀)).mp (by linarith)
  have hC0pow : C₀ ≤ (2 : ℝ) ^ ((l : ℝ) / 2 - 2) := by
    have hsub : (2 : ℝ) ^ ((l : ℝ) / 2 - 2) = (2 : ℝ) ^ ((l : ℝ) / 2) / 4 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hsub]; linarith
  refine ⟨?_, ?_⟩
  · -- `Li ≤ l`: compare `2^{Li}` with `2^{l-2}`.
    have hLi : (2 : ℝ) ^ (Li : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ) - 2) := by
      rw [Real.rpow_natCast]
      calc (2 : ℝ) ^ Li ≤ C₀ * (2 : ℝ) ^ ((l : ℝ) / 2) := hli
        _ ≤ (2 : ℝ) ^ ((l : ℝ) / 2 - 2) * (2 : ℝ) ^ ((l : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hC0pow (by positivity)
        _ = (2 : ℝ) ^ ((l : ℝ) - 2) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1
            ring
    have h := (Real.rpow_le_rpow_left_iff h2).mp hLi
    exact_mod_cast (show (Li : ℝ) ≤ (l : ℝ) by linarith)
  · -- `Log N ≤ log₂ N + 1`, from `2^{Log N} ≤ 2N`.
    have hlogN_le : (Work.Analysis.EndVar.logN N : ℝ) ≤ Real.logb 2 (N : ℝ) + 1 := by
      have h := two_pow_logN_le (N := N) hN
      rw [← Real.rpow_intCast] at h
      have hmono := (Real.logb_le_logb h2 (by positivity) (by positivity)).mpr h
      rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hmono
      rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hNpos),
          Real.logb_self_eq_one h2] at hmono
      linarith
    -- Logarithm of the second height bound.
    have hki' : (ki : ℝ) ≤ (l : ℝ) - 2 - Real.logb 2 (N : ℝ) := by
      have h1 := (Real.logb_le_logb h2 (by positivity : (0 : ℝ) < (2 : ℝ) ^ ki)
        (by positivity : (0 : ℝ) < C₀ * (2 : ℝ) ^ ((l : ℝ) / 2) / (N : ℝ))).mpr hki
      rw [← Real.rpow_intCast (2 : ℝ) ki] at h1
      rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h1
      rw [Real.logb_div (by positivity : C₀ * (2 : ℝ) ^ ((l : ℝ) / 2) ≠ 0)
            (by positivity : (N : ℝ) ≠ 0),
          Real.logb_mul (ne_of_gt hC₀) (by positivity : (2 : ℝ) ^ ((l : ℝ) / 2) ≠ 0),
          Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h1
      linarith
    have hki_real : (ki : ℝ) ≤ (l : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) - 1 := by linarith
    have hcast : (((l : ℤ) - Work.Analysis.EndVar.logN N - 1 : ℤ) : ℝ)
        = (l : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) - 1 := by push_cast; ring
    have : (ki : ℝ) ≤ ((l : ℤ) - Work.Analysis.EndVar.logN N - 1 : ℤ) := by
      rw [hcast]; exact hki_real
    exact_mod_cast this

end Work.KMTAreas.A4
