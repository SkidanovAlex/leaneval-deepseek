import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width

/-!
# Classical (de la Vallée Poussin) zero-free region for `ζ`, single `log`

There is `c > 0` such that `ζ(σ + i t) ≠ 0` whenever `|t| ≥ 2` and
`σ ≥ 1 - c / log(|t|+2)`.

This is assembled from two ingredients that live in the shared commons:

* `Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight` — the
  de la Vallée Poussin region `σ ≥ 1 - c₀/log(|t|+3)` for all sufficiently large
  `|t| ≥ T₀` (proved via the logarithmic derivative of `ζ` and the Hadamard
  partial fraction of `ζ'/ζ`);
* `Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width` — a fixed gap
  `σ ≥ 1 - ε` free of zeros in the compact rectangle `|Im s| ≤ T`, `σ ≤ 2`,
  obtained from the discreteness of the zero set.

The two are glued by choosing
`c := min (c₀/2) (ε · log 4)`:  for `|t| ≥ T` the large-height region applies
(because `log(|t|+3) ≤ 2 log(|t|+2)`), while for `2 ≤ |t| ≤ T` the compact gap
applies (because `log(|t|+2) ≥ log 4`).
-/

namespace Commons.NumberTheory.LSeries

open Complex

/-- Elementary comparison of logarithms: `log(|t|+3) ≤ 2 log(|t|+2)` for every real `t`
(since `|t|+3 ≤ (|t|+2)²`). -/
private lemma log_plus_three_le_two_log_plus_two (t : ℝ) :
    Real.log (|t| + 3) ≤ 2 * Real.log (|t| + 2) := by
  have h1 : |t| + 3 ≤ (|t| + 2) ^ 2 := by nlinarith [abs_nonneg t]
  have h2 : Real.log (|t| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
    Real.log_le_log (by positivity) h1
  have h3 : Real.log ((|t| + 2) ^ 2) = 2 * Real.log (|t| + 2) := by
    rw [Real.log_pow]; norm_num
  rwa [h3] at h2

theorem exists_zero_free_region_riemannZeta_log :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₀, T₀, hc₀, _hT₀, hlarge⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
  set T : ℝ := max T₀ 4 with hTdef
  have hT4 : (4 : ℝ) ≤ T := le_max_right T₀ 4
  have hT0T : T₀ ≤ T := le_max_left T₀ 4
  obtain ⟨ε, hεpos, hbox⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width T hT4
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨min (c₀ / 2) (ε * Real.log 4),
    lt_min (half_pos hc₀) (mul_pos hεpos hlog4pos), ?_⟩
  intro σ t ht hσ
  have hlogpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have hlog4le : Real.log 4 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by
    ring
  rcases le_or_gt T |t| with hTt | htT
  · -- large height: use the de la Vallée Poussin region
    rw [harg]
    refine hlarge t (le_trans hT0T hTt) σ ?_
    have hcle : min (c₀ / 2) (ε * Real.log 4) / Real.log (|t| + 2)
        ≤ c₀ / Real.log (|t| + 3) := by
      have h1 : min (c₀ / 2) (ε * Real.log 4) ≤ c₀ / 2 := min_le_left _ _
      have h2 : (c₀ / 2) / Real.log (|t| + 2) ≤ c₀ / Real.log (|t| + 3) := by
        rw [div_le_div_iff₀ hlogpos (Real.log_pos (by linarith [abs_nonneg t]))]
        nlinarith [log_plus_three_le_two_log_plus_two t, hc₀]
      exact le_trans (div_le_div_of_nonneg_right h1 (le_of_lt hlogpos)) h2
    linarith
  · rcases le_or_gt 1 σ with hσ1 | hσ1
    · -- to the right of the line: non-vanishing from the Euler product
      intro hz
      exact (riemannZeta_ne_zero_of_one_le_re
        (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ1)) hz
    · -- bounded height and `σ < 1`: use the compact gap
      rw [harg]
      refine hbox t σ (le_of_lt htT) ?_ (by linarith)
      have hcle : min (c₀ / 2) (ε * Real.log 4) / Real.log (|t| + 2) ≤ ε := by
        have h1 : min (c₀ / 2) (ε * Real.log 4) ≤ ε * Real.log 4 := min_le_right _ _
        have h2 : (ε * Real.log 4) / Real.log (|t| + 2) ≤ ε := by
          rw [div_le_iff₀ hlogpos]
          nlinarith [hlog4le, hεpos]
        exact le_trans (div_le_div_of_nonneg_right h1 (le_of_lt hlogpos)) h2
      linarith

end Commons.NumberTheory.LSeries
