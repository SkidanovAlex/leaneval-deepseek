import Mathlib
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log_pow

open Complex Metric
open scoped Topology

namespace Commons.NumberTheory.LSeries

/-- There is a fixed gap between `1` and the real parts of all zeros of `ζ` whose imaginary
part is bounded by `2`.  This is what lets us extend a quantitative zero-free region (valid only
for `|Im s| ≥ 2`) down to all imaginary parts.

The proof: the zeros lying in the compact set `K = {s | |re s| ≤ 2 ∧ |im s| ≤ 2}` are finite;
taking `M` to be the maximum of their real parts (or `-2` if there are none) works, because every
zero has `re < 1`, and a zero with `|im s| ≤ 2` and `|re s| > 2` has `re < -2 ≤ M`. -/
private lemma exists_lt_one_bound_zeros_low_im :
    ∃ M : ℝ, M < 1 ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≤ 2 → ρ.re ≤ M := by
  set K : Set ℂ := {s | |s.re| ≤ 2 ∧ |s.im| ≤ 2} with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    apply (isCompact_closedBall (0:ℂ) 4).of_isClosed_subset ?_ ?_
    · rw [show {s : ℂ | |s.re| ≤ 2 ∧ |s.im| ≤ 2}
          = (fun s : ℂ => |s.re|) ⁻¹' Set.Iic 2 ∩ (fun s : ℂ => |s.im|) ⁻¹' Set.Iic 2 by
        ext s; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]]
      exact (isClosed_Iic.preimage (continuous_abs.comp continuous_re)).inter
        (isClosed_Iic.preimage (continuous_abs.comp continuous_im))
    · intro s hs
      simp only [Set.mem_ofPred_eq] at hs
      simp only [Metric.mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 2 + 2 := add_le_add hs.1 hs.2
        _ = 4 := by norm_num
  have hfin : (K ∩ riemannZetaZeros).Finite := hKc.inter_riemannZetaZeros_finite
  set F : Finset ℂ := hfin.toFinset with hFdef
  have hFmem : ∀ z : ℂ, z ∈ F ↔ (|z.re| ≤ 2 ∧ |z.im| ≤ 2) ∧ riemannZeta z = 0 := by
    intro z
    rw [hFdef, hfin.mem_toFinset, Set.mem_inter_iff, mem_riemannZetaZeros, hKdef]
    simp
  by_cases hne : F.Nonempty
  · refine ⟨F.sup' hne (fun z => z.re), ?_, ?_⟩
    · obtain ⟨z0, hz0F, hz0eq⟩ := Finset.exists_mem_eq_sup' hne (fun z => z.re)
      have hz0z : riemannZeta z0 = 0 := ((hFmem z0).mp hz0F).2
      have : z0.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz0z)
      rwa [hz0eq]
    · have hMge : -2 ≤ F.sup' hne (fun z => z.re) := by
        obtain ⟨z0, hz0F, hz0eq⟩ := Finset.exists_mem_eq_sup' hne (fun z => z.re)
        have h := ((hFmem z0).mp hz0F).1.1
        have h' : -2 ≤ z0.re := (abs_le.mp h).1
        rwa [hz0eq]
      intro ρ hρ0 hρim
      by_cases hre : |ρ.re| ≤ 2
      · exact Finset.le_sup' (fun z => z.re) ((hFmem ρ).mpr ⟨⟨hre, hρim⟩, hρ0⟩)
      · have h2 : 2 < |ρ.re| := lt_of_not_ge hre
        have hneg : ρ.re < -2 := by
          rcases lt_or_ge 0 ρ.re with h | h
          · rw [abs_of_nonneg (le_of_lt h)] at h2; exfalso
            exact riemannZeta_ne_zero_of_one_le_re (by linarith) hρ0
          · rw [abs_of_nonpos h] at h2; linarith
        linarith
  · refine ⟨-2, by norm_num, ?_⟩
    have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    intro ρ hρ0 hρim
    by_cases hre : |ρ.re| ≤ 2
    · have hmem : ρ ∈ F := (hFmem ρ).mpr ⟨⟨hre, hρim⟩, hρ0⟩
      rw [hFempty] at hmem
      exact absurd hmem (Finset.notMem_empty ρ)
    · have h2 : 2 < |ρ.re| := lt_of_not_ge hre
      rcases lt_or_ge 0 ρ.re with h | h
      · rw [abs_of_nonneg (le_of_lt h)] at h2; exfalso
        exact riemannZeta_ne_zero_of_one_le_re (by linarith) hρ0
      · rw [abs_of_nonpos h] at h2; linarith

/-- **Quantitative zero-free region for `ζ`, with no restriction on `Im s`.**

There is `c > 0` such that `ζ(σ + it) ≠ 0` whenever `σ ≥ 1 - c/(log(|t|+2))⁹` — with **no**
lower bound on `|t|`.

PROOF PLAN.  Write `Z := {s : ℂ | riemannZeta s = 0}` (`riemannZetaZeros`).
1. For `|t| ≥ 2` use `Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log_pow`.
2. For `|t| < 2` we only need a *fixed* gap: show that there is `ε > 0` such that every zero with
   `|Im ρ| ≤ 2` satisfies `Re ρ ≤ 1 - ε`.  Indeed:
   * every zero satisfies `Re ρ < 1`, because `riemannZeta_ne_zero_of_one_le_re`
     (Mathlib, `NumberTheory/LSeries/Nonvanishing.lean`);
   * the zeros in the compact set `K := {s | |re s| ≤ 2 ∧ |im s| ≤ 2}` are **finitely many**
     (`IsCompact.inter_riemannZetaZeros_finite`, Mathlib
     `NumberTheory/LSeries/ZetaZeros.lean`);  if that finite set is empty any `ε > 0` works,
     otherwise take `1 - ε` to be the maximum of `re ρ` over it (`Finset.sup'` / `Finset.max'`),
     which is `< 1`;
   * every zero with `|Im ρ| ≤ 2` and `|Re ρ| > 2` satisfies `Re ρ < -2 < 1 - ε` trivially.
3. Combine: take `c := min c₁ (ε · (log 2)⁹)` (note `log(|t|+2)⁹ ≥ (log 2)⁹` when `|t| < 2`, and
   `log(|t|+2) ≥ log 4 > 1` when `|t| ≥ 2`). -/
theorem exists_zero_free_region_riemannZeta_all_t :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ,
      1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := exists_zero_free_region_riemannZeta_log_pow
  obtain ⟨M, hM1, hM⟩ := exists_lt_one_bound_zeros_low_im
  have hεpos : 0 < (1 - M) / 2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min c₁ ((1 - M) / 2 * (Real.log 2) ^ 9),
    lt_min hc₁pos (mul_pos hεpos (pow_pos hlog2 9)), ?_⟩
  intro σ t hσ hz
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rcases le_or_gt 2 |t| with ht | ht
  · -- large `|t|`: reduce to the zero-free region with `|t| ≥ 2`
    have hden : 0 < (Real.log (|t| + 2)) ^ 9 := by
      have : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      positivity
    have hle : 1 - c₁ / (Real.log (|t| + 2)) ^ 9 ≤ σ := by
      have hdiv : min c₁ ((1 - M) / 2 * (Real.log 2) ^ 9) / (Real.log (|t| + 2)) ^ 9
          ≤ c₁ / (Real.log (|t| + 2)) ^ 9 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hden)
      linarith
    exact hc₁ σ t ht hle hz
  · -- small `|t|`: use the fixed gap `M`
    have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have hlogge : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) ht2
    have hlog9ge : (Real.log 2) ^ 9 ≤ (Real.log (|t| + 2)) ^ 9 :=
      pow_le_pow_left₀ (le_of_lt hlog2) hlogge 9
    have hden : 0 < (Real.log (|t| + 2)) ^ 9 := pow_pos (lt_of_lt_of_le hlog2 hlogge) 9
    have hdiv : min c₁ ((1 - M) / 2 * (Real.log 2) ^ 9) / (Real.log (|t| + 2)) ^ 9
        ≤ (1 - M) / 2 := by
      calc min c₁ ((1 - M) / 2 * (Real.log 2) ^ 9) / (Real.log (|t| + 2)) ^ 9
          ≤ ((1 - M) / 2 * (Real.log 2) ^ 9) / (Real.log (|t| + 2)) ^ 9 :=
            div_le_div_of_nonneg_right (min_le_right _ _) (le_of_lt hden)
        _ ≤ (1 - M) / 2 := by
            rw [div_le_iff₀ hden]
            exact mul_le_mul_of_nonneg_left hlog9ge (le_of_lt hεpos)
    have hσge : (1 + M) / 2 ≤ σ := by linarith
    have hσle : σ ≤ M := by
      have h := hM ((σ : ℂ) + (t : ℂ) * Complex.I) hz (by rw [him]; exact le_of_lt ht)
      rwa [hre] at h
    linarith

end Commons.NumberTheory.LSeries
