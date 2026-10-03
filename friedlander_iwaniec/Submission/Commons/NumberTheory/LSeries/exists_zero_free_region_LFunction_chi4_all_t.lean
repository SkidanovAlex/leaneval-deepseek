import Mathlib
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_log_pow

open Complex Metric Filter
open scoped Topology
open Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.LSeries

/-- A function which is analytic on all of `ℂ` and is not identically zero has only
finitely many zeros in any compact subset of `ℂ`. -/
lemma finite_inter_zeroSet_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {x : ℂ} (hx : f x ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ f ⁻¹' {0}).Finite := by
  rw [← Set.not_infinite]
  intro hInf
  obtain ⟨y, -, hacc⟩ := hInf.exists_accPt_of_subset_isCompact hK Set.inter_subset_left
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ z in 𝓝[≠] y, f z = 0 := hacc.mono fun z hz => show f z = 0 from hz.2
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hf
    isPreconnected_univ (Set.mem_univ y) hfreq
  exact hx (by simpa using hzero (Set.mem_univ x))

/-- The zeros of `L(·,χ₄)` inside a compact subset of `ℂ` are finite. -/
lemma isCompact_inter_LFunction_chi4_zeros_finite {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z : ℂ | DirichletCharacter.LFunction chi4 z = 0}).Finite := by
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi4) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact DirichletCharacter.differentiable_LFunction chi4_ne_one
  have hx : DirichletCharacter.LFunction chi4 (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4 (Or.inl chi4_ne_one) (by norm_num)
  have h := finite_inter_zeroSet_of_analyticOnNhd hf hx hK
  simpa [Set.preimage, Set.mem_singleton_iff] using h

/-- There is a fixed gap between `1` and the real parts of all zeros of `L(·,χ₄)` whose
imaginary part is bounded by `2`. -/
lemma exists_lt_one_bound_zeros_LFunction_chi4_low_im :
    ∃ M : ℝ, M < 1 ∧ ∀ ρ : ℂ, DirichletCharacter.LFunction chi4 ρ = 0 → |ρ.im| ≤ 2 → ρ.re ≤ M := by
  classical
  set K : Set ℂ := {s | |s.re| ≤ 2 ∧ |s.im| ≤ 2} with hKdef
  have hKc : IsCompact K := by
    have hclosed : IsClosed K := by
      rw [hKdef]
      exact (isClosed_Iic.preimage (continuous_abs.comp continuous_re)).inter
        (isClosed_Iic.preimage (continuous_abs.comp continuous_im))
    refine (isCompact_closedBall (0 : ℂ) 4).of_isClosed_subset hclosed ?_
    intro s hs
    rw [hKdef] at hs
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + 2 := add_le_add hs.1 hs.2
      _ = 4 := by norm_num
  have hfin : (K ∩ {z : ℂ | DirichletCharacter.LFunction chi4 z = 0}).Finite :=
    isCompact_inter_LFunction_chi4_zeros_finite hKc
  set F : Finset ℂ := hfin.toFinset with hFdef
  have hFmem : ∀ z : ℂ,
      z ∈ F ↔ (|z.re| ≤ 2 ∧ |z.im| ≤ 2) ∧ DirichletCharacter.LFunction chi4 z = 0 := by
    intro z
    rw [hFdef, hfin.mem_toFinset, Set.mem_inter_iff, hKdef]
    simp
  by_cases hne : F.Nonempty
  · refine ⟨F.sup' hne (fun z => z.re), ?_, ?_⟩
    · obtain ⟨z0, hz0F, hz0eq⟩ := Finset.exists_mem_eq_sup' hne (fun z => z.re)
      have hz0z : DirichletCharacter.LFunction chi4 z0 = 0 := ((hFmem z0).mp hz0F).2
      have hlt : z0.re < 1 :=
        lt_of_not_ge fun h => DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4
          (Or.inl chi4_ne_one) h hz0z
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
          · rw [abs_of_nonneg (le_of_lt h)] at h2
            exact absurd (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4
              (Or.inl chi4_ne_one) (by linarith) hρ0) (by simp)
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
      · rw [abs_of_nonneg (le_of_lt h)] at h2
        exact absurd (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4
          (Or.inl chi4_ne_one) (by linarith) hρ0) (by simp)
      · rw [abs_of_nonpos h] at h2; linarith

/-- **Quantitative zero-free region for `L(·,χ₄)`, with no restriction on `Im s`.**

There is `c > 0` such that `L(σ + it, χ₄) ≠ 0` whenever `σ ≥ 1 - c/(log(|t|+2))⁹` — with **no**
lower bound on `|t|`, where `χ₄` is `Commons.NumberTheory.DirichletCharacter.chi4`.

PROOF PLAN.  Identical in shape to the corresponding statement for `ζ`
(`Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_all_t`).
1. For `|t| ≥ 2` use `Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_log_pow`.
2. For `|t| < 2` a *fixed* gap suffices: show `∃ ε > 0` with `Re ρ ≤ 1 - ε` for every zero `ρ` of
`L(·,χ₄)` with `|Im ρ| ≤ 2`.  Every such zero has `Re ρ < 1`
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re` : a non-trivial character has no zeros on
`re s ≥ 1`; for `re s = 1` and `s ≠ 1` this is `LFunction_ne_zero_of_re_eq_one`), and the zeros
in the compact set `{s | |re s| ≤ 2 ∧ |im s| ≤ 2}` are finitely many because the zero set of
the entire function `L(·,χ₄)` is discrete and closed; then take `1 - ε` to be the maximum of `re`
over that finite set.
3. Combine, taking `c := min c₁ (ε · (log 2)⁹)`. -/
theorem exists_zero_free_region_LFunction_chi4_all_t :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ,
      1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction Commons.NumberTheory.DirichletCharacter.chi4
        ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := exists_zero_free_region_LFunction_chi4_log_pow
  obtain ⟨M, hM1, hM⟩ := exists_lt_one_bound_zeros_LFunction_chi4_low_im
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
        _ = (1 - M) / 2 * ((Real.log 2) ^ 9 / (Real.log (|t| + 2)) ^ 9) := by ring
        _ ≤ (1 - M) / 2 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hεpos)
            rw [div_le_one hden]
            exact hlog9ge
        _ = (1 - M) / 2 := by ring
    have hσge : (1 + M) / 2 ≤ σ := by linarith
    have hσle : σ ≤ M := by
      have h := hM ((σ : ℂ) + (t : ℂ) * Complex.I) hz (by rw [him]; exact le_of_lt ht)
      rwa [hre] at h
    linarith

end Commons.NumberTheory.LSeries
